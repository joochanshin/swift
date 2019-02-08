//===--- Differentiation.cpp - SIL Automatic Differentiation --*- C++ -*---===//
//
// This source file is part of the Swift.org open source project
//
// Copyright (c) 2014 - 2017 Apple Inc. and the Swift project authors
// Licensed under Apache License v2.0 with Runtime Library Exception
//
// See https://swift.org/LICENSE.txt for license information
// See https://swift.org/CONTRIBUTORS.txt for the list of Swift project authors
//
//===----------------------------------------------------------------------===//
//
// SWIFT_ENABLE_TENSORFLOW
//
// This file implements reverse-mode automatic differentiation.
//
// NOTE: Although the AD feature is developed as part of the Swift for
// TensorFlow project, it is completely independent from TensorFlow support.
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "differentiation"

#include "swift/AST/ASTMangler.h"
#include "swift/AST/ASTPrinter.h"
#include "swift/AST/AutoDiff.h"
#include "swift/AST/Builtins.h"
#include "swift/AST/DeclContext.h"
#include "swift/AST/DiagnosticsSIL.h"
#include "swift/AST/Expr.h"
#include "swift/AST/GenericEnvironment.h"
#include "swift/AST/GenericSignatureBuilder.h"
#include "swift/AST/Module.h"
#include "swift/AST/ParameterList.h"
#include "swift/AST/SubstitutionMap.h"
#include "swift/SIL/FormalLinkage.h"
#include "swift/SIL/InstructionUtils.h"
#include "swift/SIL/LoopInfo.h"
#include "swift/SIL/SILBuilder.h"
#include "swift/SIL/TypeSubstCloner.h"
#include "swift/SILOptimizer/Analysis/DominanceAnalysis.h"
#include "swift/SILOptimizer/Analysis/LoopAnalysis.h"
#include "swift/SILOptimizer/PassManager/Passes.h"
#include "swift/SILOptimizer/PassManager/Transforms.h"
// #include "swift/SILOptimizer/Utils/Generics.h"
#include "swift/SILOptimizer/Utils/Local.h"
#include "swift/SILOptimizer/Utils/LoopUtils.h"
#include "swift/SILOptimizer/Utils/SILOptFunctionBuilder.h"
#include "llvm/ADT/APSInt.h"
#include "llvm/ADT/BreadthFirstIterator.h"
#include "llvm/ADT/DenseSet.h"

using namespace swift;
using llvm::DenseMap;
using llvm::SmallDenseMap;
using llvm::SmallDenseSet;
using llvm::SmallSet;

//===----------------------------------------------------------------------===//
// Helpers
//===----------------------------------------------------------------------===//

/// Prints an "[AD] " prefix to `llvm::dbgs()` and returns the debug stream.
/// This is being used to print short debug messages within the AD pass.
static raw_ostream &getADDebugStream() { return llvm::dbgs() << "[AD] "; }

/// Given a dumpable value, dumps it to `llvm::dbgs()`.
template <typename T> static inline void debugDump(T &v) {
  LLVM_DEBUG(llvm::dbgs() << "\n==== BEGIN DEBUG DUMP ====\n"
                          << v << "\n==== END DEBUG DUMP ====\n");
}

/// Returns true if the module we are compiling is in an LLDB REPL.
static bool isInLLDBREPL(SILModule &module) {
  // TODO(SR-9704): Use a more prinicpled way to do this check.
  return module.getSwiftModule()->getNameStr().startswith("__lldb_expr_");
}

//===----------------------------------------------------------------------===//
// Thunk helpers
//===----------------------------------------------------------------------===//

using namespace Lowering;

#if false
static CanGenericSignature
buildThunkSignature(SILFunctionType* fnType,
                    bool inheritGenericSig,
                    ArchetypeType *openedExistential,
                    GenericEnvironment *&genericEnv,
                    SubstitutionMap &contextSubs,
                    SubstitutionMap &interfaceSubs,
                    ArchetypeType *&newArchetype) {
  // auto *mod = fn->getModule().getSwiftModule();
  // auto &ctx = mod->getASTContext();

  // If there's no opened existential, we just inherit the generic environment
  // from the parent function.
  SILFunctionType *ty;
  // fn->getLowered
  assert(openedExistential == nullptr);
  auto genericSig = fnType->getGenericSignature();
  genericEnv = genericSig->createGenericEnvironment();
  interfaceSubs = genericEnv->getForwardingSubstitutionMap();
  contextSubs = interfaceSubs;
  return genericSig;
}

/// Build the type of a function transformation thunk.
static CanSILFunctionType buildThunkType(SILModule &module,
                                         CanSILFunctionType &sourceType,
                                         CanSILFunctionType &expectedType,
                                         /*
                                          CanType &inputfromType,
                                          CanType &outputfromType,
                                          */
                                         CanType inputfromType,
                                         CanType outputfromType,
                                         GenericEnvironment *&genericEnv,
                                         SubstitutionMap &interfaceSubs,
                                         bool withoutActuallyEscaping = false) {
  assert(!expectedType->isPolymorphic());
  assert(!sourceType->isPolymorphic());

  auto origType = sourceType;

  // Can't build a thunk without context, so we require ownership semantics
  // on the result type.
  assert(expectedType->getExtInfo().hasContext());

  // This may inherit @noescape from the expectedType. The @noescape attribute
  // is only stripped when using this type to materialize a new decl.
  auto extInfo = expectedType->getExtInfo()
  .withRepresentation(SILFunctionType::Representation::Thin);

  if (withoutActuallyEscaping)
    extInfo = extInfo.withNoEscape(false);

  // Does the thunk type involve archetypes other than opened existentials?
  bool hasArchetypes = false;
  // Does the thunk type involve an open existential type?
  CanArchetypeType openedExistential;
  auto archetypeVisitor = [&](CanType t) {
    if (auto archetypeTy = dyn_cast<ArchetypeType>(t)) {
      if (archetypeTy->getOpenedExistentialType()) {
        assert((openedExistential == CanArchetypeType() ||
                openedExistential == archetypeTy) &&
               "one too many open existentials");
        openedExistential = archetypeTy;
      } else
        hasArchetypes = true;
    }
  };

  // Use the generic signature from the context if the thunk involves
  // generic parameters.
  CanGenericSignature genericSig;
  SubstitutionMap contextSubs;
  ArchetypeType *newArchetype = nullptr;

  if (expectedType->hasArchetype() || sourceType->hasArchetype()) {
    expectedType.visit(archetypeVisitor);
    sourceType.visit(archetypeVisitor);

    genericSig = buildThunkSignature(origType,
                                     hasArchetypes,
                                     openedExistential,
                                     genericEnv,
                                     contextSubs,
                                     interfaceSubs,
                                     newArchetype);
  }

  // Utility function to apply contextSubs, and also replace the
  // opened existential with the new archetype.
  auto substIntoThunkContext = [&](CanType t) -> CanType {
    return t.subst(
                   [&](SubstitutableType *type) -> Type {
                     if (CanType(type) == openedExistential)
                       return newArchetype;
                     return Type(type).subst(contextSubs);
                   },
                   LookUpConformanceInSubstitutionMap(contextSubs),
                   SubstFlags::AllowLoweredTypes)
    ->getCanonicalType();
  };

  sourceType = cast<SILFunctionType>(substIntoThunkContext(sourceType));
  expectedType = cast<SILFunctionType>(substIntoThunkContext(expectedType));

  /*
   if (inputfromType) {
   inputfromType = cast<AnyFunctionType>(substIntoThunkContext(inputfromType));
   }

   if (outputfromType) {
   outputfromType = cast<AnyFunctionType>(substIntoThunkContext(outputfromType));
   }
   */

  // If our parent function was pseudogeneric, this thunk must also be
  // pseudogeneric, since we have no way to pass generic parameters.
  if (genericSig)
    if (origType->isPseudogeneric())
      extInfo = extInfo.withIsPseudogeneric();

  // Add the function type as the parameter.
  auto contextConvention =
  SILType::getPrimitiveObjectType(sourceType).isTrivial(module)
  ? ParameterConvention::Direct_Unowned
  : ParameterConvention::Direct_Guaranteed;
  SmallVector<SILParameterInfo, 4> params;
  params.append(expectedType->getParameters().begin(),
                expectedType->getParameters().end());
  params.push_back({sourceType,
    sourceType->getExtInfo().hasContext()
    ? contextConvention
    : ParameterConvention::Direct_Unowned});

  // Map the parameter and expected types out of context to get the interface
  // type of the thunk.
  SmallVector<SILParameterInfo, 4> interfaceParams;
  interfaceParams.reserve(params.size());
  for (auto &param : params) {
    auto paramIfaceTy = param.getType()->mapTypeOutOfContext();
    interfaceParams.push_back(
                              SILParameterInfo(paramIfaceTy->getCanonicalType(genericSig),
                                               param.getConvention()));
  }

  SmallVector<SILYieldInfo, 4> interfaceYields;
  for (auto &yield : expectedType->getYields()) {
    auto yieldIfaceTy = yield.getType()->mapTypeOutOfContext();
    auto interfaceYield =
    yield.getWithType(yieldIfaceTy->getCanonicalType(genericSig));
    interfaceYields.push_back(interfaceYield);
  }

  SmallVector<SILResultInfo, 4> interfaceResults;
  for (auto &result : expectedType->getResults()) {
    auto resultIfaceTy = result.getType()->mapTypeOutOfContext();
    auto interfaceResult =
    result.getWithType(resultIfaceTy->getCanonicalType(genericSig));
    interfaceResults.push_back(interfaceResult);
  }

  Optional<SILResultInfo> interfaceErrorResult;
  if (expectedType->hasErrorResult()) {
    auto errorResult = expectedType->getErrorResult();
    auto errorIfaceTy = errorResult.getType()->mapTypeOutOfContext();
    interfaceErrorResult = SILResultInfo(
                                         errorIfaceTy->getCanonicalType(genericSig),
                                         expectedType->getErrorResult().getConvention());
  }

  // The type of the thunk function.
  return SILFunctionType::get(genericSig, extInfo,
                              expectedType->getCoroutineKind(),
                              ParameterConvention::Direct_Unowned,
                              interfaceParams, interfaceYields,
                              interfaceResults, interfaceErrorResult,
                              module.getASTContext());
}

static SILValue createThunk(SILModule &module,
                            SILFunctionBuilder &builder,
                            SILLocation loc,
                            SILValue fn,
                            AbstractionPattern inputOrigType,
                            CanAnyFunctionType inputfromType,
                            AbstractionPattern outputOrigType,
                            CanAnyFunctionType outputfromType,
                            const TypeLowering &expectedTL) {
  auto sourceType = fn->getType().castTo<SILFunctionType>();
  auto expectedType = expectedTL.getLoweredType().castTo<SILFunctionType>();

  // SWIFT_ENABLE_TENSORFLOW
  /*
  assert(sourceType->isDifferentiable() == expectedType->isDifferentiable() &&
         "thunks can't change differentiability");
  if (sourceType->isDifferentiable()) {
    return createAutoDiffThunk(SGF, loc, fn, inputOrigType, inputfromType,
                               outputOrigType, outputfromType);
  }
   */

  // We can't do bridging here.
  assert(expectedType->getLanguage() ==
         fn->getType().castTo<SILFunctionType>()->getLanguage() &&
         "bridging in re-abstraction thunk?");

  // Declare the thunk.
  SubstitutionMap interfaceSubs;
  GenericEnvironment *genericEnv = nullptr;
  auto toType = expectedType->getWithExtInfo(
      expectedType->getExtInfo().withNoEscape(false));
  auto thunkType = buildThunkType(module, sourceType, toType,
                                  inputfromType,
                                  outputfromType,
                                  genericEnv,
                                  interfaceSubs);
  
  auto thunk = SGF.SGM.getOrCreateReabstractionThunk(
                                                     thunkType,
                                                     sourceType,
                                                     toType,
                                                     SGF.F.isSerialized());

  // Build it if necessary.
  if (thunk->empty()) {
    thunk->setGenericEnvironment(genericEnv);
    /*
    SILGenFunction thunkSGF(SGF.SGM, *thunk, SGF.FunctionDC);
    auto loc = RegularLocation::getAutoGeneratedLocation();
    buildThunkBody(thunkSGF, loc,
                   inputOrigType,
                   inputfromType,
                   outputOrigType,
                   outputfromType);
     */
  }
  llvm::errs() << "CREATING A REABSTRACTION THUNK!\n";
  thunkType->dump();
  thunk->dump();
  llvm::errs() << "TYPE DUMP\n";
  sourceType->dump();
  toType->dump();
  outputfromType->dump();

  CanSILFunctionType substFnType = thunkType;

  if (thunkType->getGenericSignature()) {
    substFnType = thunkType->substGenericArgs(SGF.F.getModule(),
                                              interfaceSubs);
  }

  // Create it in our current function.
  auto thunkValue = SGF.B.createFunctionRefFor(loc, thunk);
  ManagedValue thunkedFn =
  SGF.B.createPartialApply(loc, thunkValue,
                           SILType::getPrimitiveObjectType(substFnType),
                           interfaceSubs, fn.ensurePlusOne(SGF, loc),
                           SILType::getPrimitiveObjectType(toType));

  if (!expectedType->isNoEscape()) {
    return thunkedFn;
  }

  // Handle the escaping to noescape conversion.
  assert(expectedType->isNoEscape());
  return SGF.B.createConvertEscapeToNoEscape(
      loc, thunkedFn, SILType::getPrimitiveObjectType(expectedType), false);
}
#endif

/// Creates arguments in the entry block based on the function type.
static void createEntryArguments(SILFunction *f) {
  auto *entry = f->getEntryBlock();
  auto conv = f->getConventions();
  auto &ctx = f->getASTContext();
  auto moduleDecl = f->getModule().getSwiftModule();
  assert((entry->getNumArguments() == 0 || conv.getNumSILArguments() == 0) &&
         "Entry already has arguments?!");
  // Create a dummy argument declaration.
  // Necessary to prevent crash during argument explosion optimization.
  auto createDummyParamDecl = [&] {
    return new (ctx)
        ParamDecl(VarDecl::Specifier::Default, SourceLoc(), SourceLoc(),
                  Identifier(), SourceLoc(), Identifier(), moduleDecl);
  };
  for (auto indResultTy : conv.getIndirectSILResultTypes())
    entry->createFunctionArgument(
        f->mapTypeIntoContext(indResultTy).getAddressType(),
        createDummyParamDecl());
  for (auto paramTy : conv.getParameterSILTypes()) {
    auto *decl = createDummyParamDecl();
    auto ty = f->mapTypeIntoContext(paramTy);
    decl->setType(ty.getASTType());
    entry->createFunctionArgument(ty, decl);
  }
}

/// Computes the correct linkage for functions generated by the AD pass
/// associated with a function with linkage `originalLinkage`.
static SILLinkage getAutoDiffFunctionLinkage(SILLinkage originalLinkage) {
  // If the original is defined externally, then the AD pass is just generating
  // associated functions for use in the current module and therefore these
  // associated functions should not be visible outside the module.
  if (isAvailableExternally(originalLinkage))
    return SILLinkage::Hidden;

  // If the original is public, then external modules may need to link the
  // associated function. Make the associated function public.
  if (originalLinkage == SILLinkage::Public ||
      originalLinkage == SILLinkage::PublicNonABI)
    return originalLinkage;

  // Otherwise, the original function is defined and used only in the current
  // module, so external modules will never try to access the associated
  // function. Make the associated function hidden.
  return SILLinkage::Hidden;
}

/// Given a function, gather all of its formal results (both direct and
/// indirect) in an order defined by its result type. Note that "formal results"
/// refer to result values in the body of the function, not at call sites.
static void
collectAllFormalResultsInTypeOrder(SILFunction &function,
                                   SmallVectorImpl<SILValue> &results) {
  SILFunctionConventions convs(function.getLoweredFunctionType(),
                               function.getModule());
  auto indResults = function.getIndirectResults();
  auto *retInst = cast<ReturnInst>(function.findReturnBB()->getTerminator());
  auto retVal = retInst->getOperand();
  SmallVector<SILValue, 8> dirResults;
  if (auto *tupleInst =
          dyn_cast_or_null<TupleInst>(retVal->getDefiningInstruction()))
    dirResults.append(tupleInst->getElements().begin(),
                      tupleInst->getElements().end());
  else
    dirResults.push_back(retVal);
  unsigned indResIdx = 0, dirResIdx = 0;
  for (auto &resInfo : convs.getResults())
    results.push_back(resInfo.isFormalDirect() ? dirResults[dirResIdx++]
                                               : indResults[indResIdx++]);
}

/// Given a function call site, gather all of its actual results (both direct
/// and indirect) in an order defined by its result type.
template <typename IndResRange>
static void collectAllActualResultsInTypeOrder(
    ApplyInst *ai, ArrayRef<SILValue> extractedDirectResults,
    IndResRange &&indirectResults, SmallVectorImpl<SILValue> &results) {
  auto callee = ai->getCallee();
  SILFunctionConventions calleeConvs(
      callee->getType().castTo<SILFunctionType>(), ai->getModule());
  unsigned indResIdx = 0, dirResIdx = 0;
  llvm::errs() << "LEMME CHECK RES INFO\n";
  for (auto &resInfo : calleeConvs.getResults())
    resInfo.dump();
  llvm::errs() << "DE\n";
  for (auto &resInfo : calleeConvs.getResults()) {
    results.push_back(resInfo.isFormalDirect()
                          ? extractedDirectResults[dirResIdx++]
                          : indirectResults[indResIdx++]);
  }
}

/// Given a range of types, joins these into a single type. If there's exactly
/// one element type, returns that element type. Otherwise, creates a tuple type
/// of all element types.
template <typename TypeRange>
static CanType joinElementTypes(TypeRange &&range, const ASTContext &ctx) {
  if (range.size() == 1)
    return range.front();
  auto typeElts =
      map<SmallVector<TupleTypeElt, 8>>(range, [&](Type type) { return type; });
  return TupleType::get(typeElts, ctx);
}

/// Given a range of SIL values, retrieves the canonical types of these values,
/// and joins these types into a single type.
template <typename SILValueRange>
static CanType joinElementTypesFromValues(SILValueRange &&range,
                                          const ASTContext &ctx) {
  if (range.size() == 1)
    return range.front()->getType().getASTType();
  SmallVector<TupleTypeElt, 8> elts;
  transform(range, elts.begin(),
            [&](SILValue val) { return val->getType().getASTType(); });
  return TupleType::get(elts, ctx)->getCanonicalType();
}

/// Given an operator name, such as '+', and a protocol, returns the '+'
/// operator. If the operator does not exist in the protocol, returns null.
static FuncDecl *findOperatorDeclInProtocol(DeclName operatorName,
                                            ProtocolDecl *protocol) {
  assert(operatorName.isOperator());
  // Find the operator requirement in the `VectorNumeric` protocol
  // declaration and cache it.
  auto opLookUp = protocol->lookupDirect(operatorName);
  // Find the `+` with type siguature `(Self, Self) -> Self`.
  for (auto *decl : opLookUp) {
    auto *fd = dyn_cast<FuncDecl>(decl);
    if (!fd || !fd->isStatic() || !fd->isOperator())
      continue;
    return fd;
  }
  // Not found.
  return nullptr;
}

/// Assuming the buffer is for indirect passing, returns the store ownership
/// qualifier for creating a `store` instruction into the buffer.
static StoreOwnershipQualifier getBufferSOQ(Type type, SILFunction &fn) {
  if (fn.hasQualifiedOwnership())
    return fn.getModule().Types.getTypeLowering(type).isTrivial()
               ? StoreOwnershipQualifier::Trivial
               : StoreOwnershipQualifier::Init;
  return StoreOwnershipQualifier::Unqualified;
}

/// Assuming the buffer is for indirect passing, returns the load ownership
/// qualified for creating a `load` instruction from the buffer.
static LoadOwnershipQualifier getBufferLOQ(Type type, SILFunction &fn) {
  if (fn.hasQualifiedOwnership())
    return fn.getModule().Types.getTypeLowering(type).isTrivial()
               ? LoadOwnershipQualifier::Trivial
               : LoadOwnershipQualifier::Take;
  return LoadOwnershipQualifier::Unqualified;
}

/// Assuming the given type conforms to `Differentiable`, returns the associated
/// cotangent space type.
static SILType getCotangentType(CanType type, SILModule &mod) {
  return SILType::getPrimitiveObjectType(
      type->getAutoDiffAssociatedVectorSpace(
          AutoDiffAssociatedVectorSpaceKind::Cotangent,
          LookUpConformanceInModule(mod.getSwiftModule()))->getCanonicalType());
}

/// Assuming the given type conforms to `Differentiable`, returns the associated
/// cotangent space type.
static SILType getCotangentType(SILType type, SILModule &mod) {
  return getCotangentType(type.getASTType(), mod).copyCategory(type);
}

// Return the expected generic signature for autodiff associated functions given
// a SILDifferentiableAttr. The expected generic signature is built from the
// original generic signature and the attribute's requirements.
static CanGenericSignature
getAssociatedFunctionGenericSignature(SILDifferentiableAttr *attr,
                                      SILFunction *original) {
  auto originalGenSig =
      original->getLoweredFunctionType()->getGenericSignature();
  if (!originalGenSig)
    return nullptr;
  GenericSignatureBuilder builder(original->getASTContext());
  // Add original generic signature.
  builder.addGenericSignature(originalGenSig);
  // Add where clause requirements.
  auto source =
      GenericSignatureBuilder::FloatingRequirementSource::forAbstract();
  for (auto &req : attr->getRequirements())
    builder.addRequirement(req, source, original->getModule().getSwiftModule());
  return std::move(builder)
      .computeGenericSignature(SourceLoc(), /*allowConcreteGenericParams=*/true)
      ->getCanonicalSignature();
}

// Clone the generic parameters of the given generic signature and return a new
// `GenericParamList`.
static GenericParamList *cloneGenericParameters(ASTContext &ctx,
                                                DeclContext *dc,
                                                CanGenericSignature sig) {
  SmallVector<GenericTypeParamDecl *, 2> clonedParams;
  for (auto paramType : sig->getGenericParams()) {
    auto clonedParam = new (ctx) GenericTypeParamDecl(dc, paramType->getName(),
                                                      SourceLoc(),
                                                      paramType->getDepth(),
                                                      paramType->getIndex());
    clonedParam->setDeclContext(dc);
    clonedParam->setImplicit(true);
    clonedParams.push_back(clonedParam);
  }
  return GenericParamList::create(ctx, SourceLoc(), clonedParams, SourceLoc());
}

static ReturnInst *getSingleReturn(SILFunction *f) {
  return cast<ReturnInst>(f->findReturnBB()->getTerminator());
}

//===----------------------------------------------------------------------===//
// Auxiliary data structures
//===----------------------------------------------------------------------===//

namespace {
class ADContext;
class DifferentiationTask;

/// The invoker of a differentiation task. It can be some user syntax, e.g.
/// `AutoDiffFunctionExpr` expression, the differentiation pass, or nothing at
/// all. This will be used to emit informative diagnostics.
struct DifferentiationInvoker {
public:
  /// The kind of the invoker of a differentiation task.
  enum class Kind {
    // No known invoker. This is the case when the differentiation is requested
    // from SIL source via a `autodiff_function` instruction **without** being
    // linked to a Swift AST node.
    AutoDiffFunctionInst,

    // Invoked by the indirect application of differentiation. This case has an
    // associated differentiation task reference.
    IndirectDifferentiation,

    // Invoked by function conversion from a non-differentiable function to a
    // differentiable one. The corresponding AST node is an
    // `AutoDiffFunctionExpr`.
    FunctionConversion,

    // Invoked by a `@differentiable` attribute in the Swift source. This case
    // has an associated `@differentiable` attribute.
    DifferentiableAttribute,

    // Invoker by a `[differentiable]` attribute in SIL **without** being linked
    // to a Swift AST attribute. This case has an associated `[differentiable]`
    // attribute.
    SILDifferentiableAttribute
  };

private:
  Kind kind;
  union Value {
    /// The instruction associated with the `AutoDiffFunctionInst` case.
    AutoDiffFunctionInst *adFuncInst;
    Value(AutoDiffFunctionInst *inst) : adFuncInst(inst) {}

    /// The parent differentiation task associated with the
    /// `IndirectDifferentiation` case.
    std::pair<ApplyInst *, DifferentiationTask *> indirectDifferentiation;
    Value(ApplyInst *applyInst, DifferentiationTask *parentTask)
        : indirectDifferentiation({applyInst, parentTask}) {}

    /// The conversion expression associated with the `FunctionConversion` case.
    AutoDiffFunctionExpr *functionConversion;
    Value(AutoDiffFunctionExpr *expr) : functionConversion(expr) {}

    /// The `@differentiable` attribute associated with the
    /// `DifferentiableAttribute` case.
    std::pair<DifferentiableAttr *, FuncDecl *> differentiableAttribute;
    Value(DifferentiableAttr *attr, FuncDecl *fd)
        : differentiableAttribute({attr, fd}) {}

    /// The `[differentiable]` attribute associated with the
    /// `SILDifferentiableAttribute` case.
    std::pair<SILDifferentiableAttr *, SILFunction *>
        silDifferentiableAttribute;
    Value(SILDifferentiableAttr *attr, SILFunction *f)
        : silDifferentiableAttribute({attr, f}) {}
  } value;

  /*implicit*/
  DifferentiationInvoker(Kind kind, Value value) : kind(kind), value(value) {}

public:
  DifferentiationInvoker(AutoDiffFunctionInst *inst)
      : kind(Kind::AutoDiffFunctionInst), value(inst) {}
  DifferentiationInvoker(ApplyInst *applyInst, DifferentiationTask *task)
      : kind(Kind::IndirectDifferentiation), value(applyInst, task) {}
  DifferentiationInvoker(AutoDiffFunctionExpr *expr)
      : kind(Kind::FunctionConversion), value(expr) {}
  DifferentiationInvoker(DifferentiableAttr *attr, FuncDecl *fd)
      : kind(Kind::DifferentiableAttribute), value(attr, fd) {}
  DifferentiationInvoker(SILDifferentiableAttr *attr, SILFunction *f)
      : kind(Kind::SILDifferentiableAttribute), value(attr, f) {}

  Kind getKind() const { return kind; }

  AutoDiffFunctionInst *getAutoDiffFunctionInst() const {
    assert(kind == Kind::AutoDiffFunctionInst);
    return value.adFuncInst;
  }

  std::pair<ApplyInst *, DifferentiationTask *>
  getIndirectDifferentiation() const {
    assert(kind == Kind::IndirectDifferentiation);
    return value.indirectDifferentiation;
  }

  AutoDiffFunctionExpr *getFunctionConversion() const {
    assert(kind == Kind::FunctionConversion);
    return value.functionConversion;
  }

  std::pair<DifferentiableAttr *, FuncDecl *>
  getDifferentiableAttribute() const {
    assert(kind == Kind::DifferentiableAttribute);
    return value.differentiableAttribute;
  }

  std::pair<SILDifferentiableAttr *, SILFunction *>
  getSILDifferentiableAttribute() const {
    assert(kind == Kind::SILDifferentiableAttribute);
    return value.silDifferentiableAttribute;
  }

  SourceLoc getLocation() const {
    switch (kind) {
    case Kind::AutoDiffFunctionInst:
      return getAutoDiffFunctionInst()->getLoc().getSourceLoc();
    case Kind::IndirectDifferentiation:
      return getIndirectDifferentiation().first->getLoc().getSourceLoc();
    case Kind::FunctionConversion:
      return getFunctionConversion()->getLoc();
    case Kind::DifferentiableAttribute:
      return getDifferentiableAttribute().first->getLocation();
    case Kind::SILDifferentiableAttribute:
      return getSILDifferentiableAttribute().second
          ->getLocation().getSourceLoc();
    }
  }

  void print(llvm::raw_ostream &os) const;
};

/// Information about the primal function produced by PrimalGen, e.g.
/// mappings from the original values to their corresponding ones in the primal
/// value struct produced by the primal function.
///
/// A primal value struct is an aggregate value containing intermediate values
/// checkpointed during the primal computation. During PrimalGen, such a struct
/// will be generated for each function being differentiated, and each primal
/// function will return such a struct value for the adjoint function to
/// consume.
class PrimalInfo {
private:
  /// The primal value struct declaration.
  StructDecl *primalValueStruct = nullptr;

  /// Mapping from `apply` and `struct_extract` instructions in the original
  /// function to the corresponding pullback decl in the primal struct.
  DenseMap<SILInstruction *, VarDecl *> pullbackValueMap;

private:
  VarDecl *addVarDecl(StringRef name, Type type) {
    auto &ctx = primalValueStruct->getASTContext();
    auto id = ctx.getIdentifier(name);
    auto *varDecl = new (ctx) VarDecl(
        /*IsStatic*/ false, VarDecl::Specifier::Var,
        /*IsCaptureList*/ false, SourceLoc(), id, primalValueStruct);
    varDecl->setAccess(primalValueStruct->getEffectiveAccess());
    if (type->hasArchetype())
      varDecl->setInterfaceType(type->mapTypeOutOfContext());
    else
      varDecl->setInterfaceType(type);
    primalValueStruct->addMember(varDecl);
    return varDecl;
  }

public:
  PrimalInfo(const PrimalInfo &) = delete;
  PrimalInfo &operator=(const PrimalInfo &) = delete;

  explicit PrimalInfo(StructDecl *primalValueStruct)
      : primalValueStruct(&*primalValueStruct) {}

  /// Returns the primal value struct that the primal info is established
  /// around.
  StructDecl *getPrimalValueStruct() const { return primalValueStruct; }

  /// Add a pullback to the primal value struct.
  // VarDecl *addPullbackDecl(SILInstruction *inst, Type pullbackType) {
  VarDecl *addPullbackDecl(SILInstruction *inst, SILType pullbackType) {
    // IRGen requires decls to have AST types (not `SILFunctionType`), so we
    // convert the `SILFunctionType` of the pullback to a `FunctionType` with
    // the same parameters and results.
    auto silFnTy = pullbackType.castTo<SILFunctionType>();
    SmallVector<AnyFunctionType::Param, 8> params;
    for (auto &param : silFnTy->getParameters())
      params.push_back(AnyFunctionType::Param(param.getType()));
    Type astFnTy = FunctionType::get(
        params, silFnTy->getAllResultsType().getASTType());

    // Why not the line below?
    // astFnTy = pullbackType.getASTType();

    if (pullbackType.getASTType() != astFnTy->getCanonicalType()) {
      // assert(false);
    }

    auto *decl = addVarDecl("pullback_" + llvm::itostr(pullbackValueMap.size()),
                            astFnTy);
    pullbackValueMap.insert({inst, decl});
    return decl;
  }

  /// Finds the pullback decl in the primal value struct for an `apply` or
  /// `struct_extract` in the original function.
  VarDecl *lookUpPullbackDecl(SILInstruction *inst) {
    auto lookup = pullbackValueMap.find(inst);
    return lookup == pullbackValueMap.end() ? nullptr
                                            : lookup->getSecond();
  }
};

/// Tracks the progress of primal/adjoint synthesis for a task.
enum class FunctionSynthesisState {
  /// We do not need to synthesize this function.
  NotNeeded,

  /// We need to synthesize this function.
  Needed,

  /// The function has been added to the PrimalGen/AdjointGen worklist, but not
  /// yet synthesized.
  Pending,

  /// Synthesis is done: either the function has been synthesized, or an error
  /// occurred durng synthesis.
  Done
};

/// Stores activity information about `apply` instructions that `PrimalGen`
/// calculates.
struct NestedApplyActivity {
  /// The differentiation indices that are used to differentiate this apply.
  SILAutoDiffIndices indices;
};

/// Specifies how we should differentiate a `struct_extract` instruction.
enum class StructExtractDifferentiationStrategy {
  // The `struct_extract` is not active, so do not differentiate it.
  Inactive,

  // The `struct_extract` is extracting a field from a Differentiable struct
  // with @_fieldwiseProductSpace cotangent space. Therefore, differentiate the
  // `struct_extract` by setting the adjoint to a vector in the cotangent space
  // that is zero except along the direction of the corresponding field.
  //
  // Fields correspond by matching name.
  Fieldwise,

  // Differentiate the `struct_extract` by looking up the corresponding getter
  // and using its VJP.
  Getter
};

/// A differentiation task, specifying the original function and the
/// `[differentiable]` attribute on the function. PrimalGen and AdjointGen
/// will synthesize the primal and the adjoint for this task, filling the primal
/// and adjoint fields in the attribute.
///
/// NOTE: A task instance manages a `[differentiable]` SIL attribute and shall
/// be the only one that modifies this attribute.
class DifferentiationTask {
  friend llvm::DenseMapInfo<DifferentiationTask>;
  friend class ADContext;

private:
  ADContext &context;

  /// The original function to be differentiated.
  SILFunction *original;

  /// The `[differentiable]` attribute on the original function. Since
  /// attribute synthesis is part of differentiation, a `[differentiable]`
  /// attribute must be available when a `DifferentiationTask` is created. The
  /// AD configuration resides within the attribute. This is guaranteed to be
  /// non-null.
  SILDifferentiableAttr *attr;

  /// The invoker of this differentiation task.
  DifferentiationInvoker invoker;

  /// Primal info. If this is `nullptr`, then there is no primal values between
  /// the primal and the adjoint.
  std::unique_ptr<PrimalInfo> primalInfo = nullptr;

  /// Mapping from original `apply` instructions to their corresponding
  /// `NestedApplyActivity`s.
  DenseMap<ApplyInst *, NestedApplyActivity> nestedApplyActivities;

  /// Mapping from original `struct_extract` instructions to their strategies.
  DenseMap<StructExtractInst *, StructExtractDifferentiationStrategy>
      structExtractDifferentiationStrategies;

  /// Cache for associated functions.
  SILFunction *primal = nullptr;
  SILFunction *adjoint = nullptr;
  SILFunction *jvp = nullptr;
  SILFunction *vjp = nullptr;

  /// Tracks the progress of primal synthesis for this task.
  FunctionSynthesisState primalSynthesisState;

  /// Tracks the progress of adjoint synthesis for this task.
  FunctionSynthesisState adjointSynthesisState;

  /// Asserts that a transition from one state to another is valid.
  void validateTransition(FunctionSynthesisState from,
                          FunctionSynthesisState to) {
    switch (from) {
    case FunctionSynthesisState::NotNeeded:
      llvm_unreachable("should not change state from NotNeeded");
    case FunctionSynthesisState::Needed:
      assert(to == FunctionSynthesisState::Pending &&
             "Needed must transition to Pending");
      break;
    case FunctionSynthesisState::Pending:
      assert(to == FunctionSynthesisState::Done &&
             "Pending must transition to Done");
      break;
    case FunctionSynthesisState::Done:
      llvm_unreachable("should not change state from Done");
    }
  }

  /// Creates an empty primal for this task.
  void createEmptyPrimal();
  /// Creates an empty adjoint for this task.
  void createEmptyAdjoint();

  /// Creates a JVP for this task.
  /// Currently, the JVP simply returns undef.
  void createJVP();

  /// Creates a VJP for this task. Primal and adjoint (possibly empty) must
  /// exist.
  void createVJP();

protected:
  /// Create a differentiation task.
  ///
  /// Creates empty primal and adjoint functions, if this task needs to
  /// synthesize them. Creates fully-synthesized VJP if this task needs to
  /// synthesize it.
  ///
  /// @param context The ADContext where differentiation happens.
  /// @param original The original function to be differentiated.
  /// @param attr The [differentiable] attribute to take control of.
  /// @param invoker The invoker of this differentiation task.
  explicit DifferentiationTask(ADContext &context,
                               SILFunction *original,
                               SILDifferentiableAttr *&&attr,
                               DifferentiationInvoker invoker);

public:
  DifferentiationTask(const DifferentiationTask &) = delete;
  DifferentiationTask &operator=(const DifferentiationTask &) = delete;

  SILFunction *getOriginal() const { return original; }
  SILDifferentiableAttr *getAttribute() const { return attr; }
  DifferentiationInvoker getInvoker() const { return invoker; }

  PrimalInfo *getPrimalInfo() const { return primalInfo.get(); }

  const SILAutoDiffIndices &getIndices() const {
    return attr->getIndices();
  }

  FunctionSynthesisState getPrimalSynthesisState() const {
    return primalSynthesisState;
  }
  void setPrimalSynthesisState(FunctionSynthesisState newState) {
    validateTransition(primalSynthesisState, newState);
    primalSynthesisState = newState;
  }
  FunctionSynthesisState getAdjointSynthesisState() const {
    return adjointSynthesisState;
  }
  void setAdjointSynthesisState(FunctionSynthesisState newState) {
    validateTransition(adjointSynthesisState, newState);
    adjointSynthesisState = newState;
  }

  SILFunction *getPrimal() const { return primal; }
  SILFunction *getAdjoint() const { return adjoint; }
  SILFunction *getJVP() const { return jvp; }
  SILFunction *getVJP() const { return vjp; }

  SILFunction *getAssociatedFunction(AutoDiffAssociatedFunctionKind kind) {
    switch (kind) {
    case AutoDiffAssociatedFunctionKind::JVP:
      return jvp;
    case AutoDiffAssociatedFunctionKind::VJP:
      return vjp;
    }
  }

  DenseMap<ApplyInst *, NestedApplyActivity> &getNestedApplyActivities() {
    return nestedApplyActivities;
  }

  DenseMap<StructExtractInst *, StructExtractDifferentiationStrategy> &
  getStructExtractDifferentiationStrategies() {
    return structExtractDifferentiationStrategies;
  }

  bool isEqual(const DifferentiationTask &other) const {
    return original == other.original && attr == other.attr;
  }

  void print(llvm::raw_ostream &os) const;
};

static inline llvm::raw_ostream &operator<<(llvm::raw_ostream &os,
                                            DifferentiationInvoker invoker) {
  invoker.print(os);
  return os;
}

void DifferentiationInvoker::print(llvm::raw_ostream &os) const {
  os << "(differentiation_invoker ";
  switch (kind) {
  case Kind::AutoDiffFunctionInst:
    os << "autodiff_function_inst=(" << *getAutoDiffFunctionInst() << ")";
    break;
  case Kind::IndirectDifferentiation: {
    auto indDiff = getIndirectDifferentiation();
    os << "indirect_differentiation=(apply_inst=(" << *indDiff.first
       << ") task=" << indDiff.second << ')';
    break;
  }
  case Kind::FunctionConversion: {
    StreamPrinter printer(os);
    PrintOptions options;
    os << "differential_operator=(";
    getFunctionConversion()->print(printer, options);
    os << ')';
    break;
  }
  case Kind::DifferentiableAttribute: {
    auto diffAttr = getDifferentiableAttribute();
    os << "differentiable_attribute=(attr=(";
    diffAttr.first->print(os);
    os << ") func_decl=" << diffAttr.second->getFullName();
    break;
  }
  case Kind::SILDifferentiableAttribute: {
    auto diffAttr = getSILDifferentiableAttribute();
    os << "sil_differentiable_attribute=(attr=(";
    diffAttr.first->print(os);
    os << ") function=" << diffAttr.second->getName();
    break;
  }
  }
  os << ')';
}

void DifferentiationTask::print(llvm::raw_ostream &os) const {
  os << "(differentiation_task original=@" << original->getName()
     << " attribute=";
  attr->print(os);
  os << " invoker=" << invoker << ")";
}

/// A task specifies the empty primal/adjoint function to be filled in, and what
/// its corresponding original function and differentiation indices are.
struct FunctionSynthesisItem {
  /// The original function that the new function will be cloned and synthesized
  /// based on.
  SILFunction *original;

  /// The function to be synthesized.
  SILFunction *target;

  /// The indices of reverse automatic differentiation.
  SILAutoDiffIndices indices;

  /// The parent differentiation task. This will be used for diagnostics.
  DifferentiationTask *task;
};

//===----------------------------------------------------------------------===//
// ADContext - Per-module contextual information for the Differentiation pass.
//===----------------------------------------------------------------------===//

class ADContext {
private:
  /// Reference to the main transform.
  SILModuleTransform &transform;

  /// The module where Differentiation is performed on.
  SILModule &module;

  /// AST context.
  ASTContext &astCtx = module.getASTContext();

  /// Shared pass manager.
  SILPassManager &passManager;

  /// Queue of differentiation tasks.
  SmallVector<std::unique_ptr<DifferentiationTask>, 32> differentiationTasks;
  /// Mapping from enqueued differentiation tasks to their indices in
  /// `differentiationTasks`.
  SmallDenseMap<std::pair<SILFunction *, SILAutoDiffIndices>, unsigned>
      enqueuedTaskIndices;

  /// The VectorNumeric protocol in the standard library.
  ProtocolDecl *vectorNumericProtocol =
      astCtx.getProtocol(KnownProtocolKind::VectorNumeric);
  /// The Numeric protocol in the standard library.
  ProtocolDecl *numericProtocol =
      astCtx.getProtocol(KnownProtocolKind::Numeric);
  /// The AdditiveArithmetic protocol in the standard library.
  ProtocolDecl *additiveArithmeticProtocol =
    astCtx.getProtocol(KnownProtocolKind::AdditiveArithmetic);
  /// The FloatingPoint protocol in the stanard library.
  ProtocolDecl *floatingPointProtocol =
      astCtx.getProtocol(KnownProtocolKind::FloatingPoint);

  /// `AdditiveArithmetic.+` declaration.
  mutable FuncDecl *cachedPlusFn = nullptr;
  /// `AdditiveArithmetic.+=` declaration.
  mutable FuncDecl *cachedPlusEqualFn = nullptr;

public:
  /// Construct an ADContext for the given module.
  explicit ADContext(SILModuleTransform &transform);

  SILModuleTransform &getTransform() const { return transform; }
  SILModule &getModule() const { return module; }
  ASTContext &getASTContext() const { return module.getASTContext(); }
  SILPassManager &getPassManager() const { return passManager; }
  Lowering::TypeConverter &getTypeConverter() { return module.Types; }

  ArrayRef<std::unique_ptr<DifferentiationTask>>
  getDifferentiationTasks() const {
    return differentiationTasks;
  }

  ProtocolDecl *getVectorNumericProtocol() const {
    return vectorNumericProtocol;
  }

  ProtocolDecl *getNumericProtocol() const {
    return numericProtocol;
  }

  ProtocolDecl *getAdditiveArithmeticProtocol() const {
    return additiveArithmeticProtocol;
  }

  ProtocolDecl *getFloatingPointProtocol() const {
    return floatingPointProtocol;
  }

  FuncDecl *getPlusDecl() const {
    if (!cachedPlusFn) {
      cachedPlusFn = findOperatorDeclInProtocol(
          astCtx.getIdentifier("+"), additiveArithmeticProtocol);
      assert(cachedPlusFn && "AdditiveArithmetic.+ not found");
    }
    return cachedPlusFn;
  }

  FuncDecl *getPlusEqualDecl() const {
    if (!cachedPlusEqualFn) {
      cachedPlusEqualFn = findOperatorDeclInProtocol(
          astCtx.getIdentifier("+="), additiveArithmeticProtocol);
      assert(cachedPlusEqualFn && "AdditiveArithmetic.+= not found");
    }
    return cachedPlusEqualFn;
  }

  void clearTask(DifferentiationTask *task) {
    LLVM_DEBUG(getADDebugStream() << "Clearing differentiation task for "
               << task->original->getName() << '\n');
    if (task->primal) {
      transform.notifyWillDeleteFunction(task->primal);
      module.eraseFunction(task->primal);
    }
    if (task->adjoint) {
      transform.notifyWillDeleteFunction(task->adjoint);
      module.eraseFunction(task->adjoint);
    }
    transform.notifyWillDeleteFunction(task->jvp);
    module.eraseFunction(task->jvp);
    transform.notifyWillDeleteFunction(task->vjp);
    module.eraseFunction(task->vjp);
    task->original->removeDifferentiableAttr(task->attr);
  }

  /// Retrieves the file unit that contains implicit declarations in the
  /// current Swift module. If it does not exist, create one.
  ///
  // FIXME: Currently it defaults to the file containing `origFn`, if it can be
  // determined. Otherwise, it defaults to any file unit in the module. To
  // handle this more properly, we should make a DerivedFileUnit class to
  // contain all synthesized implicit type declarations.
  SourceFile &getPrimalValueDeclContainer(SILFunction *origFn) {
    if (origFn->hasLocation())
      if (auto *declContext = origFn->getLocation().getAsDeclContext())
        if (auto *parentSourceFile = declContext->getParentSourceFile())
          return *parentSourceFile;
    for (auto *file : module.getSwiftModule()->getFiles())
      if (auto *src = dyn_cast<SourceFile>(file))
        return *src;
    llvm_unreachable("No files?");
  }

  /// Creates a struct declaration (without contents) for storing primal values
  /// of a function. The newly created struct will have the same generic
  /// signature as the given primal generic signature.
  StructDecl *createPrimalValueStruct(const DifferentiationTask *task,
                                      CanGenericSignature primalGenericSig);

  /// Finds the `[differentiable]` attribute on the specified original function
  /// corresponding to the specified parameter indices. Returns nullptr if it
  /// does not exist.
  ///
  /// TODO: Currently we are doing a O(n) lookup. This could be improved by
  /// hashing on SILFunction's side or maintaining a dictionary in ADContext.
  /// In any case, this is not performance-critical.
  SILDifferentiableAttr *lookUpDifferentiableAttr(
      SILFunction *original, const SILAutoDiffIndices &indices) const {
    for (auto *attr : original->getDifferentiableAttrs())
      if (attr->getIndices() == indices)
        return attr;
    return nullptr;
  }

  SILDifferentiableAttr *createDifferentiableAttr(
      SILFunction *original, const SILAutoDiffIndices &indices) const {
    assert(!lookUpDifferentiableAttr(original, indices));
    auto *attr = SILDifferentiableAttr::create(getModule(), indices);
    original->addDifferentiableAttr(attr);
    return attr;
  }

  /// Finds or creates a `[differentiable]` attribute on the specified
  /// original function corresponding to the specified parameter indices.
  SILDifferentiableAttr *getOrCreateDifferentiableAttr(
      SILFunction *original, const SILAutoDiffIndices &indices) {
    if (auto *attr = lookUpDifferentiableAttr(original, indices))
      return attr;
    assert(original->isDefinition());
    return createDifferentiableAttr(original, indices);
  }

  /// Finds a differentiation task on a function such that the task produces
  /// adjoints for the specified indices.
  DifferentiationTask *
  lookUpDifferentiationTask(SILFunction *original,
                            const SILAutoDiffIndices &indices) {
    auto existing = enqueuedTaskIndices.find({original, indices});
    if (existing == enqueuedTaskIndices.end())
      return nullptr;
    return differentiationTasks[existing->getSecond()].get();
  }

  /// Finds a differentiation task on a function such that the task produces
  /// adjoints for the specified indices or, if such a task is not present,
  /// for the task with the least number of parameters that is a superset of
  /// the parameter indices in `indices`, and which corresponds to a
  /// primitive adjoint function.
  DifferentiationTask *
  lookUpMinimalDifferentiationTask(SILFunction *original,
                                   const SILAutoDiffIndices &indices) {
    auto supersetParamIndices = llvm::SmallBitVector();
    const auto &indexSet = indices.parameters;
    if (auto *existingTask = lookUpDifferentiationTask(original, indices))
      return existingTask;
    for (auto *rda : original->getDifferentiableAttrs()) {
      const auto &rdaIndexSet = rda->getIndices().parameters;
      // If all indices in indexSet are in rdaIndexSet, and it has fewer
      // indices than our current candidate and a primitive adjoint, rda is our
      // new candidate.
      if (!indexSet.test(rdaIndexSet) && // all indexSet indices in rdaIndexSet
          (supersetParamIndices.empty() || // fewer parameters than before
           rdaIndexSet.count() < supersetParamIndices.count()))
        supersetParamIndices = rda->getIndices().parameters;
    }
    auto existing = enqueuedTaskIndices.find(
        {original, {indices.source, supersetParamIndices}});
    if (existing == enqueuedTaskIndices.end())
      return nullptr;
    return differentiationTasks[existing->getSecond()].get();
  }

public:
  /// Register a differentiation task in the global worklist. This will ensure
  /// that a `[differentiable]` attribute will be generated for the specified
  /// indices, and that primal/adjoint synthesis will be run in the
  /// Differentiation pass.
  ///
  /// The function must either be a definition or be serialized.
  DifferentiationTask *
  registerDifferentiationTask(SILFunction *original,
                              const SILAutoDiffIndices &indices,
                              DifferentiationInvoker invoker) {
    // Make sure this pair of original and indices is unique.
    assert(!lookUpDifferentiationTask(original, indices));
    auto *attr = getOrCreateDifferentiableAttr(original, indices);
    std::unique_ptr<DifferentiationTask> task(
        new DifferentiationTask(*this, original, std::move(attr), invoker));
    differentiationTasks.push_back(std::move(task));
    enqueuedTaskIndices.insert(
        {{original, indices}, differentiationTasks.size() - 1});
    return differentiationTasks.back().get();
  }

  /// Declare an external reference to an associated function of `original`,
  /// given a `[differentiable]` attribute of `original` and the associated
  /// function kind.
  SILFunction *
  declareExternalAssociatedFunction(SILFunction *original,
                                    SILDifferentiableAttr *attr, StringRef name,
                                    AutoDiffAssociatedFunctionKind kind);

  template <typename... T, typename... U>
  InFlightDiagnostic diagnose(SourceLoc loc, Diag<T...> diag,
                              U &&... args) const {
    return getASTContext().Diags.diagnose(loc, diag, std::forward<U>(args)...);
  }

  /// Emit a "not differentiable" error based on the given differentiation task
  /// and diagnostic.
  void emitNondifferentiabilityError(const DifferentiationTask *task,
                                     Diag<> diag);

  /// Given an instruction and a differentiation task associated with the
  /// parent function, emits a "not differentiable" error based on the task. If
  /// the task is indirect, emits notes all the way up to the outermost task,
  /// and emits an error at the outer task. Otherwise, emits an error directly.
  void emitNondifferentiabilityError(SILInstruction *inst,
                                     const DifferentiationTask *task,
                                     Optional<Diag<>> diag = None);

  /// Given a value and a differentiation task associated with the parent
  /// function, emits a "not differentiable" error based on the task. If the
  /// task is indirect, emits notes all the way up to the outermost task, and
  /// emits an error at the outer task. Otherwise, emits an error directly.
  void emitNondifferentiabilityError(SILValue value,
                                     const DifferentiationTask *task,
                                     Optional<Diag<>> diag = None);
};
} // end anonymous namespace

ADContext::ADContext(SILModuleTransform &transform)
    : transform(transform), module(*transform.getModule()),
      passManager(*transform.getPassManager()) {}

void ADContext::emitNondifferentiabilityError(const DifferentiationTask *task,
                                              Diag<> diag) {
  auto invoker = task->getInvoker();
  diagnose(invoker.getLocation(), diag);
  diagnose(invoker.getLocation(), diag::autodiff_function_not_differentiable);
}

void ADContext::emitNondifferentiabilityError(SILValue value,
                                              const DifferentiationTask *task,
                                              Optional<Diag<>> diag) {
  auto *inst = value->getDefiningInstruction();
  if (!inst) {
    diagnose(value.getLoc().getSourceLoc(),
             diag.getValueOr(diag::autodiff_expression_is_not_differentiable));
    return;
  }
  emitNondifferentiabilityError(inst, task, diag);
}

void ADContext::emitNondifferentiabilityError(SILInstruction *inst,
                                              const DifferentiationTask *task,
                                              Optional<Diag<>> diag) {
  // Location of the instruction.
  auto opLoc = inst->getLoc().getSourceLoc();
  if (!task) {
    diagnose(opLoc,
             diag.getValueOr(diag::autodiff_expression_is_not_differentiable));
    return;
  }
  auto invoker = task->getInvoker();
  LLVM_DEBUG({
    auto &s = getADDebugStream()
        << "Diagnosing non-differentiability for inst \n\t" << *inst
        << "\nwhile performing differentiation task\n\t";
    task->print(s);
    s << '\n';
  });
  switch (invoker.getKind()) {
  // For a `autodiff_function` instruction or a `[differentiable]` attribute
  // that is not associated with any source location, we emit a diagnostic at
  // the instruction source location.
  case DifferentiationInvoker::Kind::AutoDiffFunctionInst:
    // FIXME: This will not report an error to the user.
    diagnose(opLoc,
             diag.getValueOr(diag::autodiff_expression_is_not_differentiable));
    break;
  case DifferentiationInvoker::Kind::SILDifferentiableAttribute: {
    auto attr = invoker.getSILDifferentiableAttribute();
    bool foundAttr = false;
    if (auto *declContext = attr.second->getDeclContext()) {
      if (auto *fnDecl = declContext->getInnermostDeclarationDeclContext()) {
        if (auto *diffAttr =
                fnDecl->getAttrs().getAttribute<DifferentiableAttr>()) {
          diagnose(diffAttr->getLocation(),
                   diag::autodiff_function_not_differentiable)
              .highlight(diffAttr->getRangeWithAt());
          diagnose(attr.second->getLocation().getSourceLoc(),
                   diag::autodiff_when_differentiating_function_definition);
          foundAttr = true;
        }
      }
    }
    if (!foundAttr) {
      // Fallback if we cannot find the expected attribute.
      diagnose(attr.second->getLocation().getSourceLoc(),
               diag::autodiff_function_not_differentiable);
    }
    diagnose(opLoc,
             diag.getValueOr(diag::autodiff_expression_is_not_differentiable));
    break;
  }

  // For indirect differentiation, emit a "not differentiable" note on the
  // expression first. Then emit an error at the source invoker of
  // differentiation, and a "when differentiating this"  note at each indirect
  // invoker.
  case DifferentiationInvoker::Kind::IndirectDifferentiation: {
    std::tie(inst, task) = task->getInvoker().getIndirectDifferentiation();
    emitNondifferentiabilityError(inst, task, None);
    diagnose(opLoc, diag.getValueOr(
                        diag::autodiff_when_differentiating_function_call));
    break;
  }

  // For a function conversion, emit a "not differentiable" error on the
  // attribute first and a note on the non-differentiable operation.
  case DifferentiationInvoker::Kind::FunctionConversion: {
    auto *expr = invoker.getFunctionConversion();
    diagnose(expr->getLoc(), diag::autodiff_function_not_differentiable)
        .highlight(expr->getSubExpr()->getSourceRange());
    diagnose(opLoc,
             diag.getValueOr(diag::autodiff_expression_is_not_differentiable));
    break;
  }

  // For a `@differentiable` attribute, emit a "not differentiable" error on the
  // attribute first and a note on the non-differentiable operation.
  case DifferentiationInvoker::Kind::DifferentiableAttribute: {
    auto diffAttr = invoker.getDifferentiableAttribute();
    diagnose(diffAttr.first->getLocation(),
             diag::autodiff_function_not_differentiable)
        .highlight(diffAttr.second->getNameLoc());
    diagnose(opLoc,
             diag.getValueOr(diag::autodiff_expression_is_not_differentiable));
    break;
  }
  }
}

//===----------------------------------------------------------------------===//
// Activity Analysis
//===----------------------------------------------------------------------===//

namespace {
class DifferentiableActivityInfo;

/// In many real situations, the end-users of AD need only the derivatives of
/// some selected outputs of `P` with respect to some selected inputs of `P`.
/// Whatever the differentiation mode (tangent, reverse,...), these restrictions
/// allow the AD tool to produce a much more efficient differentiated program.
/// Essentially, fixing some inputs and neglecting some outputs allows AD to
/// just forget about several intermediate differentiated variables.
///
/// Activity analysis is the specific analysis that detects these situations,
/// therefore allowing for a better differentiated code. Activity analysis is
/// present in all transformation-based AD tools.
///
/// To begin with, the end-user specifies that only some output variables (the
/// “dependent”) must be differentiated with respect to only some input
/// variables (the “independent”). We say that variable `y` depends on `x` when
/// the derivative of `y` with respect to `x` is not trivially null. We say that
/// a variable is “varied” if it depends on at least one independent. Conversely
/// we say that a variable is “useful” if at least one dependent depends on it.
/// Finally, we say that a variable is “active” if it is at the same time varied
/// and useful. In the special case of the tangent mode, it is easy to check
/// that when variable `v` is not varied at some place in the program, then its
/// derivative `v̇` at this place is certainly null. Conversely when variable `v`
/// is not useful, then whatever the value of `v̇`, this value does not matter
/// for the final result. Symmetric reasoning applies for the reverse mode of
/// AD: observing that differentiated variables go upstream, we see that a
/// useless variable has a null derivative, in other words the partial
/// derivative of the output with respect to this variable is null. Conversely
/// when variable `v` is not varied, then whatever the value of `v`, this value
/// does not matter for the final result.
///
/// Reference:
/// Laurent Hascoët. Automatic Differentiation by Program Transformation. 2007.
class DifferentiableActivityAnalysis
    : public FunctionAnalysisBase<DifferentiableActivityInfo> {
private:
  DominanceAnalysis *dominanceAnalysis = nullptr;
  PostDominanceAnalysis *postDominanceAnalysis = nullptr;

public:
  explicit DifferentiableActivityAnalysis()
      : FunctionAnalysisBase(SILAnalysisKind::DifferentiableActivity) {}

  static bool classof(const SILAnalysis *s) {
    return s->getKind() == SILAnalysisKind::DifferentiableActivity;
  }

  virtual bool shouldInvalidate(SILAnalysis::InvalidationKind k) override {
    return k & InvalidationKind::Everything;
  }

  virtual std::unique_ptr<DifferentiableActivityInfo>
  newFunctionAnalysis(SILFunction *f) override;

  virtual void initialize(SILPassManager *pm) override;
};
} // end anonymous namespace

namespace {
/// Represents the differentiation activity associated with a SIL value.
enum class ActivityFlags : unsigned {
  /// The value depends on a function parameter.
  Varied = 1 << 1,
  /// The value contributes to a result.
  Useful = 1 << 2,
  /// The value is both varied and useful.
  Active = Varied | Useful,
};

using Activity = OptionSet<ActivityFlags>;

/// Result of activity analysis on a function. Accepts queries for whether a
/// value is "varied", "useful" or "active" against certain differentiation
/// indices.
class DifferentiableActivityInfo {
private:
  SILFunction &function;

  /// Input values, i.e. parameters (both direct and indirect).
  SmallVector<SILValue, 4> inputValues;
  /// Output values, i.e. individual values (not the final tuple) being returned
  /// by the `return` instruction.
  SmallVector<SILValue, 4> outputValues;

  /// The set of useful variables, indexed by the corresponding dependent value
  /// (output) index.
  SmallVector<SmallDenseSet<SILValue>, 4> usefulValueSets;
  /// The set of useful variables, indexed by the corresponding independent
  /// value (input) index.
  SmallVector<SmallDenseSet<SILValue>, 4> variedValueSets;

  /// Perform analysis and populate sets.
  void analyze(DominanceInfo *di, PostDominanceInfo *pdi);

  bool setVariedIfDifferentiable(SILValue value,
                                 unsigned independentVariableIndex);
  bool setUsefulIfDifferentiable(SILValue value,
                                 unsigned dependentVariableIndex);
  void recursivelySetVariedIfDifferentiable(SILValue value,
                                            unsigned independentVariableIndex);
  void propagateUsefulThroughBuffer(SILValue value,
                                    unsigned dependentVariableIndex);

public:
  explicit DifferentiableActivityInfo(SILFunction &f,
                                      DominanceInfo *di,
                                      PostDominanceInfo *pdi);

  bool isVaried(SILValue value, unsigned independentVariableIndex) const;
  bool isUseful(SILValue value, unsigned dependentVariableIndex) const;
  bool isVaried(SILValue value,
                const llvm::SmallBitVector &parameterIndices) const;
  bool isActive(SILValue value, const SILAutoDiffIndices &indices) const;

  Activity getActivity(SILValue value,
                       const SILAutoDiffIndices &indices) const;
  Activity getActivity(SILInstruction *inst,
                       const SILAutoDiffIndices &indices) const;
};
} // end anonymous namespace

std::unique_ptr<DifferentiableActivityInfo>
DifferentiableActivityAnalysis::newFunctionAnalysis(SILFunction *f) {
  assert(dominanceAnalysis && "Expect a valid dominance anaysis");
  assert(postDominanceAnalysis && "Expect a valid post-dominance anaysis");
  return llvm::make_unique<DifferentiableActivityInfo>(
      *f, dominanceAnalysis->get(f), postDominanceAnalysis->get(f));
}

void DifferentiableActivityAnalysis::initialize(SILPassManager *pm) {
  dominanceAnalysis = pm->getAnalysis<DominanceAnalysis>();
  postDominanceAnalysis = pm->getAnalysis<PostDominanceAnalysis>();
}

SILAnalysis *swift::createDifferentiableActivityAnalysis(SILModule *m) {
  return new DifferentiableActivityAnalysis();
}

DifferentiableActivityInfo::DifferentiableActivityInfo(SILFunction &f,
                                                       DominanceInfo *di,
                                                       PostDominanceInfo *pdi)
    : function(f) {
  analyze(di, pdi);
}

void DifferentiableActivityInfo::analyze(DominanceInfo *di,
                                         PostDominanceInfo *pdi) {
  LLVM_DEBUG(getADDebugStream()
             << "Running activity analysis on @" << function.getName() << '\n');
  // Inputs are just function's arguments, count `n`.
  auto paramArgs = function.getArgumentsWithoutIndirectResults();
  for (auto value : paramArgs)
    inputValues.push_back(value);
  LLVM_DEBUG({
    auto &s = getADDebugStream();
    s << "Inputs in @" << function.getName() << ":\n";
    for (auto val : inputValues)
      s << val << '\n';
  });
  // Outputs are indirect result buffers and return values, count `m`.
  collectAllFormalResultsInTypeOrder(function, outputValues);
  LLVM_DEBUG({
    auto &s = getADDebugStream();
    s << "Outputs in @" << function.getName() << ":\n";
    for (auto val : outputValues)
      s << val << '\n';
  });

  auto &module = function.getModule();
  // Mark inputs as varied.
  assert(variedValueSets.empty());
  for (auto input : inputValues) {
    variedValueSets.push_back({});
    if (input->getType().isDifferentiable(module))
      variedValueSets.back().insert(input);
  }
  // Propagate varied-ness through the function in dominance order.
  DominanceOrder domOrder(function.getEntryBlock(), di);
  while (auto *block = domOrder.getNext()) {
    for (auto &inst : *block) {
      for (auto i : indices(inputValues)) {
        // Handle `apply`.
        if (auto *ai = dyn_cast<ApplyInst>(&inst)) {
          for (auto arg : ai->getArgumentsWithoutIndirectResults()) {
            if (isVaried(arg, i)) {
              for (auto indRes : ai->getIndirectSILResults())
                setVariedIfDifferentiable(indRes, i);
              for (auto dirRes : ai->getResults())
                setVariedIfDifferentiable(dirRes, i);
            }
          }
        }
        // Handle `store`.
        else if (auto *si = dyn_cast<StoreInst>(&inst)) {
          if (isVaried(si->getSrc(), i))
            recursivelySetVariedIfDifferentiable(si->getDest(), i);
        }
        // Handle `copy_addr`.
        else if (auto *cai = dyn_cast<CopyAddrInst>(&inst)) {
          if (isVaried(cai->getSrc(), i))
            recursivelySetVariedIfDifferentiable(cai->getDest(), i);
        }
        // Handle `struct_extract`.
        else if (auto *sei = dyn_cast<StructExtractInst>(&inst)) {
          if (isVaried(sei->getOperand(), i)) {
            // If `@noDerivative` exists on the field while the struct is
            // `@_fieldwiseDifferentiable`, this field is not in the set of
            // differentiable variables that we want to track the variedness of.
            auto hasNoDeriv = sei->getField()->getAttrs()
                .hasAttribute<NoDerivativeAttr>();
            auto structIsFieldwiseDiffable = sei->getStructDecl()->getAttrs()
                .hasAttribute<FieldwiseDifferentiableAttr>();
            if (!(hasNoDeriv && structIsFieldwiseDiffable))
              for (auto result: inst.getResults())
                setVariedIfDifferentiable(result, i);
          }
        }
        // Handle everything else.
        else {
          for (auto &op : inst.getAllOperands())
            if (isVaried(op.get(), i))
              for (auto result : inst.getResults())
                setVariedIfDifferentiable(result, i);
        }
      }
    }
    domOrder.pushChildren(block);
  }

  // Mark differentiable outputs as useful.
  assert(usefulValueSets.empty());
  for (auto output : outputValues) {
    usefulValueSets.push_back({});
    if (output->getType().isDifferentiable(module))
      usefulValueSets.back().insert(output);
  }
  // Propagate usefulness through the function in post-dominance order.
  PostDominanceOrder postDomOrder(&*function.findReturnBB(), pdi);
  while (auto *block = postDomOrder.getNext()) {
    for (auto &inst : reversed(*block)) {
      for (auto i : indices(outputValues)) {
        // Handle indirect results in `apply`.
        if (auto *ai = dyn_cast<ApplyInst>(&inst)) {
          auto checkAndSetUseful = [&](SILValue res) {
            if (isUseful(res, i))
              for (auto arg : ai->getArgumentsWithoutIndirectResults())
                setUsefulIfDifferentiable(arg, i);
          };
          for (auto dirRes : ai->getResults())
            checkAndSetUseful(dirRes);
          for (auto indRes : ai->getIndirectSILResults())
            checkAndSetUseful(indRes);
        }
        // Handle `store`.
        else if (auto *si = dyn_cast<StoreInst>(&inst)) {
          if (isUseful(si->getDest(), i))
            setUsefulIfDifferentiable(si->getSrc(), i);
        }
        // Handle reads.
        else if (inst.mayReadFromMemory()) {
          if (llvm::any_of(inst.getResults(),
                           [&](SILValue res) { return isUseful(res, i); }))
            for (auto &op : inst.getAllOperands())
              if (op.get()->getType().isAddress())
                propagateUsefulThroughBuffer(op.get(), i);
        }
        // Handle everything else.
        else {
          for (auto result : inst.getResults())
            if (isUseful(result, i))
              for (auto &op : inst.getAllOperands())
                setUsefulIfDifferentiable(op.get(), i);
        }
      }
    }
    postDomOrder.pushChildren(block);
  }
}

bool DifferentiableActivityInfo::setVariedIfDifferentiable(
    SILValue value, unsigned independentVariableIndex) {
  if (!value->getType().isDifferentiable(function.getModule()))
    return false;
  variedValueSets[independentVariableIndex].insert(value);
  return true;
}

bool DifferentiableActivityInfo::setUsefulIfDifferentiable(
    SILValue value, unsigned dependentVariableIndex) {
  if (!value->getType().isDifferentiable(function.getModule()))
    return false;
  usefulValueSets[dependentVariableIndex].insert(value);
  return true;
}

void DifferentiableActivityInfo::recursivelySetVariedIfDifferentiable(
    SILValue value, unsigned independentVariableIndex) {
  if (!setVariedIfDifferentiable(value, independentVariableIndex))
    return;
  if (auto *inst = value->getDefiningInstruction())
    for (auto &op : inst->getAllOperands())
      recursivelySetVariedIfDifferentiable(op.get(), independentVariableIndex);
}

void DifferentiableActivityInfo::propagateUsefulThroughBuffer(
    SILValue value, unsigned dependentVariableIndex) {
  assert(value->getType().isAddress());
  if (!setUsefulIfDifferentiable(value, dependentVariableIndex))
    return;
  if (auto *inst = value->getDefiningInstruction())
    for (auto &operand : inst->getAllOperands())
      if (operand.get()->getType().isAddress())
        propagateUsefulThroughBuffer(operand.get(), dependentVariableIndex);
  auto isProjectingMemory = [](SILInstruction *inst) -> bool {
    bool hasAddrResults = llvm::any_of(inst->getResults(),
        [&](SILValue res) { return res->getType().isAddress(); });
    bool hasAddrOperands = llvm::any_of(inst->getAllOperands(),
        [&](Operand &op) { return op.get()->getType().isAddress(); });
    return hasAddrResults && hasAddrOperands;
  };
  for (auto use : value->getUses())
    if (isProjectingMemory(use->getUser()))
      for (auto res : use->getUser()->getResults())
        if (res->getType().isAddress())
          setUsefulIfDifferentiable(res, dependentVariableIndex);
}

bool DifferentiableActivityInfo::isVaried(
    SILValue value, unsigned independentVariableIndex) const {
  auto &set = variedValueSets[independentVariableIndex];
  return set.count(value);
}

bool DifferentiableActivityInfo::isVaried(
    SILValue value, const llvm::SmallBitVector &parameterIndices) const {
  for (auto paramIdx : parameterIndices.set_bits())
    if (isVaried(value, paramIdx))
      return true;
  return false;
}

bool DifferentiableActivityInfo::isUseful(
    SILValue value, unsigned dependentVariableIndex) const {
  auto &set = usefulValueSets[dependentVariableIndex];
  return set.count(value);
}

bool DifferentiableActivityInfo::isActive(
    SILValue value, const SILAutoDiffIndices &indices) const {
  return isVaried(value, indices.parameters) && isUseful(value, indices.source);
}

Activity DifferentiableActivityInfo::getActivity(
    SILValue value, const SILAutoDiffIndices &indices) const {
  Activity activity;
  if (isVaried(value, indices.parameters))
    activity |= ActivityFlags::Varied;
  if (isUseful(value, indices.source))
    activity |= ActivityFlags::Useful;
  return activity;
}

Activity DifferentiableActivityInfo::getActivity(
    SILInstruction *inst, const SILAutoDiffIndices &indices) const {
  Activity activity;
  for (auto result : inst->getResults())
    activity |= getActivity(result, indices);
  return activity;
}

static void dumpActivityInfo(SILValue value,
                             const SILAutoDiffIndices &indices,
                             const DifferentiableActivityInfo &activityInfo,
                             llvm::raw_ostream &s = llvm::dbgs()) {
  s << '[';
  auto activity = activityInfo.getActivity(value, indices);
  switch (activity.toRaw()) {
  case 0: s << "NONE"; break;
  case (unsigned)ActivityFlags::Varied: s << "VARIED"; break;
  case (unsigned)ActivityFlags::Useful: s << "USEFUL"; break;
  case (unsigned)ActivityFlags::Active: s << "ACTIVE"; break;
  }
  s << "] " << value;
}

static void dumpActivityInfo(SILFunction &fn,
                             const SILAutoDiffIndices &indices,
                             DifferentiableActivityInfo &activityInfo,
                             llvm::raw_ostream &s = llvm::dbgs()) {
  s << "Activity info for " << fn.getName() << " at " << indices << '\n';
  for (auto &bb : fn) {
    for (auto *arg : bb.getArguments())
      dumpActivityInfo(arg, indices, activityInfo, s);
    for (auto &inst : bb)
      for (auto res : inst.getResults())
        dumpActivityInfo(res, indices, activityInfo, s);
  }
}

/// If the original function in the differentiation task has more than one basic
/// blocks, emit a "control flow unsupported" error at appropriate source
/// locations. Returns true if error is emitted.
static bool diagnoseUnsupportedControlFlow(ADContext &context,
                                           DifferentiationTask *task) {
  if (task->getOriginal()->getBlocks().size() <= 1)
    return false;
  // Find any control flow node and diagnose.
  for (auto &bb : *task->getOriginal()) {
    auto *term = bb.getTerminator();
    if (term->isBranch()) {
      context.emitNondifferentiabilityError(
          term, task, diag::autodiff_control_flow_not_supported);
      return true;
    }
  }
  return false;
}

/// If the original function in the differentiation task has indirect
/// differentiation parameters/result, emit a "unknown parameter or result
/// size" error at appropriate source locations. Returns true if error is
/// emitted.
static bool diagnoseIndirectParametersOrResult(CanSILFunctionType fnType,
                                               ADContext &context,
                                               DifferentiationTask *task) {
  auto indices = task->getIndices();
  // Check whether differentiation result or parameters are indirect.
  bool hasIndirectParamOrResult =
      fnType->getResults()[indices.source].isFormalIndirect();
  for (unsigned i : swift::indices(fnType->getParameters())) {
    if (!indices.isWrtParameter(i))
      continue;
    if (fnType->getParameters()[i].isFormalIndirect()) {
      hasIndirectParamOrResult = true;
      break;
    }
  }
  if (hasIndirectParamOrResult) {
    context.emitNondifferentiabilityError(
        task, diag::autodiff_function_indirect_params_or_result_unsupported);
    return true;
  }
  return false;
}

//===----------------------------------------------------------------------===//
// Code emission utilities
//===----------------------------------------------------------------------===//

/// Given a value, extracts all elements to `result` from this value if it's a
/// tuple. Otherwise, add this value directly to `result`.
static void extractAllElements(SILValue val, SILBuilder &builder,
                               SmallVectorImpl<SILValue> &result) {
  if (auto tupleType = val->getType().getAs<TupleType>())
    for (auto i : range(tupleType->getNumElements()))
      result.push_back(builder.createTupleExtract(val.getLoc(), val, i));
  else
    result.push_back(val);
}

/// Given a range of elements, joins these into a single value. If there's
/// exactly one element, returns that element. Otherwise, creates a tuple using
/// a `tuple` instruction.
static SILValue joinElements(ArrayRef<SILValue> elements, SILBuilder &builder,
                             SILLocation loc) {
  if (elements.size() == 1)
    return elements.front();
  return builder.createTuple(loc, elements);
}

/// When a function value is used in an instruction (usually `apply`), there's
/// some conversion instruction in between, e.g. `thin_to_thick_function`. Given
/// a new function value and an old function value, this helper function
/// recursively converts the new function just like how the old function is
/// converted. If the new function's generic signature is specified, it is used
/// to create substitution maps for reapplied `partial_apply` instructions.
static SILValue
reapplyFunctionConversion(SILValue newFunc, SILValue oldFunc,
                          SILValue oldConvertedFunc, SILBuilder &builder,
                          SILLocation loc,
                          GenericSignature* newFuncGenSig = nullptr,
                          std::function<SILValue(SILValue)> substituteOperand =
                              [](SILValue v) { return v; }) {
  // If the old func is the new func, then there's no conversion.
  if (oldFunc == oldConvertedFunc)
    return newFunc;
  // Handle a few instruction cases.
  // thin_to_thick_function
  if (auto *tttfi = dyn_cast<ThinToThickFunctionInst>(oldConvertedFunc)) {
    auto innerNewFunc = reapplyFunctionConversion(
        newFunc, oldFunc, tttfi->getOperand(), builder, loc, newFuncGenSig,
        substituteOperand);
    auto operandFnTy = innerNewFunc->getType().castTo<SILFunctionType>();
    auto thickTy = operandFnTy->getWithRepresentation(
        SILFunctionTypeRepresentation::Thick);
    auto silTy = SILType::getPrimitiveObjectType(thickTy);

    return builder.createThinToThickFunction(loc, innerNewFunc, silTy);
  }
  // partial_apply
  if (auto *pai = dyn_cast<PartialApplyInst>(oldConvertedFunc)) {
    SmallVector<SILValue, 8> newArgs;
    newArgs.reserve(pai->getNumArguments());
    for (auto arg : pai->getArguments())
      newArgs.push_back(substituteOperand(arg));
    auto innerNewFunc = reapplyFunctionConversion(
        newFunc, oldFunc, pai->getCallee(), builder, loc, newFuncGenSig,
        substituteOperand);
    // If new function's generic signature is specified, use it to create
    // substitution map for reapplied `partial_apply` instruction.
    auto substMap = !newFuncGenSig
        ? pai->getSubstitutionMap()
        : SubstitutionMap::get(
              newFuncGenSig, QuerySubstitutionMap{pai->getSubstitutionMap()},
              LookUpConformanceInModule(builder.getModule().getSwiftModule()));
    return builder.createPartialApply(loc, innerNewFunc, substMap, newArgs,
                                      ParameterConvention::Direct_Guaranteed);
  }
  // convert_escape_to_noescape
  if (auto *cetn = dyn_cast<ConvertEscapeToNoEscapeInst>(oldConvertedFunc)) {
    auto innerNewFunc = reapplyFunctionConversion(newFunc, oldFunc,
                                                  cetn->getOperand(), builder,
                                                  loc, newFuncGenSig,
                                                  substituteOperand);
    auto operandFnTy = innerNewFunc->getType().castTo<SILFunctionType>();
    auto noEscapeType = operandFnTy->getWithExtInfo(
        operandFnTy->getExtInfo().withNoEscape());
    auto silTy = SILType::getPrimitiveObjectType(noEscapeType);
    return builder.createConvertEscapeToNoEscape(
        loc, innerNewFunc, silTy, cetn->isEscapedByUser(),
        cetn->isLifetimeGuaranteed());
  }
  // convert_function
  if (auto *cfi = dyn_cast<ConvertFunctionInst>(oldConvertedFunc)) {
    // `convert_function` does not have a fixed typing rule because it can
    // convert between function types as long as they are ABI-compatible. Here
    // we match specific patterns.
    auto origTargetFnTy = cfi->getType().castTo<SILFunctionType>();
    auto origSourceFnTy =
        cfi->getOperand()->getType().castTo<SILFunctionType>();
    auto innerNewFunc = reapplyFunctionConversion(newFunc, oldFunc,
                                                  cfi->getOperand(), builder,
                                                  loc, newFuncGenSig,
                                                  substituteOperand);
    // Match a conversion from escaping to `@noescape`
    CanSILFunctionType targetType;
    if (!origSourceFnTy->isNoEscape() && origTargetFnTy->isNoEscape() &&
        origSourceFnTy == origTargetFnTy->getWithExtInfo(
            origTargetFnTy->getExtInfo().withNoEscape(false))) {
      auto operandFnTy = innerNewFunc->getType().castTo<SILFunctionType>();
      targetType = operandFnTy->getWithExtInfo(
          operandFnTy->getExtInfo().withNoEscape(true));
    }
    assert(targetType && "Unhandled convert_function pattern");
    auto silTy = SILType::getPrimitiveObjectType(targetType);
    return builder.createConvertFunction(loc, innerNewFunc, silTy,
                                         cfi->withoutActuallyEscaping());
  }
  llvm_unreachable("Unhandled function convertion instruction");
}

template<class Inst>
static Inst *peerThroughFunctionConversions(SILValue value) {
  if (auto *inst = dyn_cast<Inst>(value))
    return inst;
  if (auto *thinToThick = dyn_cast<ThinToThickFunctionInst>(value))
    return peerThroughFunctionConversions<Inst>(thinToThick->getOperand());
  if (auto *convertFn = dyn_cast<ConvertFunctionInst>(value))
    return peerThroughFunctionConversions<Inst>(convertFn->getOperand());
  if (auto *convertFn = dyn_cast<ConvertEscapeToNoEscapeInst>(value))
    return peerThroughFunctionConversions<Inst>(convertFn->getOperand());
  if (auto *partialApply = dyn_cast<PartialApplyInst>(value))
    return peerThroughFunctionConversions<Inst>(partialApply->getCallee());
  return nullptr;
}

/// Emits a reference to an associated function of `original`, differentiated
/// with respect to a superset of `desiredIndices`. Returns the `SILValue` for
/// the associated function and the actual indices that the associated function
/// is with respect to.
///
/// Returns `None` on failure, signifying that a diagnostic has been emitted.
///
/// Creates new differentiation tasks, if necessary, using `invoker` as the
/// invoker. Calls `taskCallback` for all newly-created tasks (but may also call
/// `taskCallback` for already-existing tasks), so that the caller can make sure
/// that the task actually gets executed.
///
/// FIXME: This is too complicated and needs to be rewritten.
static Optional<std::pair<SILValue, SILAutoDiffIndices>>
emitAssociatedFunctionReference(ADContext &context, SILBuilder &builder,
    const DifferentiationTask *parentTask, SILAutoDiffIndices desiredIndices,
    AutoDiffAssociatedFunctionKind kind, SILValue original,
    DifferentiationInvoker invoker,
    std::function<void(DifferentiationTask *)> taskCallback) {

  SILValue functionSource = original;
  /*
  llvm::errs() << "EMIT ASSOC FUNC REF\n";
  original->dumpInContext();
  */

  // If `original` is itself an `AutoDiffFunctionExtractInst` whose kind matches
  // the given kind and desired differentiation parameter indices, simply
  // extract the associated function of its function operand, retain the
  // associated function, and return it.
  if (auto *inst = original->getDefiningInstruction()) {
    if (auto *adfei = dyn_cast<AutoDiffFunctionExtractInst>(inst)) {
      if (adfei->getExtractee() == AutoDiffFunctionExtractee::Original) {
        functionSource = adfei->getFunctionOperand();
      }
    }
  }

  // If functionSource is a @differentiable function, just extract it.
  if (auto autodiffFnType = original->getType().castTo<SILFunctionType>()) {
    if (autodiffFnType->isDifferentiable()) {
      SILValue assocFn = builder.createAutoDiffFunctionExtract(
          original.getLoc(), kind, /*differentiationOrder*/ 1, functionSource);
      if (autodiffFnType->getDifferentiationParameterIndices().test(
              desiredIndices.parameters)) {
        context.emitNondifferentiabilityError(
            original, parentTask,
            diag::autodiff_function_subset_indices_not_differentiable);
        return None;
      }
      SILAutoDiffIndices indices(0, desiredIndices.parameters);
      return std::make_pair(assocFn, indices);
    }
  }

  // Find local function reference.
  if (auto *originalFRI =
          peerThroughFunctionConversions<FunctionRefInst>(original)) {
    auto loc = originalFRI->getLoc();
    auto *originalFn = originalFRI->getReferencedFunction();
    auto *task =
        context.lookUpMinimalDifferentiationTask(originalFn, desiredIndices);
    if (!task) {
      if (originalFn->isExternalDeclaration()) {
        // For LLDB REPL, we should attempt to load the function as
        // this may be defined in a different cell.
        if (isInLLDBREPL(*original->getModule()))
          original->getModule()->loadFunction(originalFn);
        // If we still don't have the definition, generate an error message.
        if (originalFn->isExternalDeclaration()) {
          context.emitNondifferentiabilityError(
              original, parentTask,
              diag::autodiff_external_nondifferentiable_function);
          return None;
        }
      }
      task = context.registerDifferentiationTask(originalFn, desiredIndices,
                                                 invoker);
    }
    assert(task);
    taskCallback(task);
    auto *assocFn = task->getAssociatedFunction(kind);
    auto *ref = builder.createFunctionRef(loc, assocFn);
    if (originalFn->isThunk() == IsReabstractionThunk) {
      llvm::errs() << "FOUND REABS THUNK in `emitAssociatedFunctionReference`\n";
      originalFn->dump();
      auto *pai = cast<PartialApplyInst>(originalFRI->getSingleUse()->getUser());
      llvm::errs() << "ORIGINAL\n";
      original->dumpInContext();
      llvm::errs() << "PAI FOR REABS THUNK\n";
      pai->dumpInContext();
      assert(pai->getNumArguments() == 1);
      // NOTE: Not necessary a function ref inst?
      auto trueOriginalFn = pai->getArgument(0);
      auto *trueOriginalFRI = peerThroughFunctionConversions<FunctionRefInst>(pai->getArgument(0));
      llvm::errs() << "TRUE ORIGINAL FN";
      trueOriginalFn->dumpInContext();
      // auto trueVJP = emitAssociatedFunctionReference(context, builder, parentTask, <#SILAutoDiffIndices desiredIndices#>, kind, trueOriginalFn, invoker, taskCallback);
      // auto trueVJP = emitAssociatedFunctionReference(context, builder, parentTask, SILAutoDiffIndices(0, {0}), kind, trueOriginalFn, invoker, taskCallback);
      auto trueVJP = emitAssociatedFunctionReference(context, builder, parentTask, task->getIndices(), kind, trueOriginalFn, invoker, taskCallback);
      llvm::errs() << "TRUE ORIGINAL " << (kind == AutoDiffAssociatedFunctionKind::JVP ? "JVP" : "VJP") << "\n";
      trueVJP->first->dumpInContext();
      llvm::errs() << "THUNK " << (kind == AutoDiffAssociatedFunctionKind::JVP ? "JVP" : "VJP") << "?\n";
      ref->dumpInContext();
      // auto convertedTrueVJP = reapplyFunctionConversion(trueVJP->first, trueOriginalFRI, trueOriginalFn, builder, loc, assocFn->getLoweredFunctionType()->getGenericSignature());
      // llvm::errs() << "CONVERTED TRUE ORIGINAL " << (kind == AutoDiffAssociatedFunctionKind::JVP ? "JVP" : "VJP") << "\n";
      // convertedTrueVJP->dumpInContext();
      // reapplyFunctionConversion(<#SILValue newFunc#>, <#SILValue oldFunc#>, <#SILValue oldConvertedFunc#>, <#SILBuilder &builder#>, <#SILLocation loc#>)
      auto convertedRef = reapplyFunctionConversion(ref, originalFRI, original, builder, loc,
                                                    assocFn->getLoweredFunctionType()->getGenericSignature(),
                                                    [&](SILValue operand) { return operand; });
      llvm::errs() << "CONVERTED REF " << (kind == AutoDiffAssociatedFunctionKind::JVP ? "JVP" : "VJP") << "\n";
      convertedRef->dumpInContext();
      // TODO: Change application of stuff
      return std::make_pair(convertedRef, task->getIndices());
    }
    auto convertedRef = reapplyFunctionConversion(
        ref, originalFRI, original, builder, loc,
        assocFn->getLoweredFunctionType()->getGenericSignature());
    return std::make_pair(convertedRef, task->getIndices());
  }

  // Find global `let` closure.
  if (auto *load = peerThroughFunctionConversions<LoadInst>(original)) {
    FunctionRefInst *initialFnRef = nullptr;
    SILValue initVal;
    if (auto *globalAddr = dyn_cast<GlobalAddrInst>(load->getOperand())) {
      // Search for the original function used to initialize this `let`
      // constant.
      if (auto *global = globalAddr->getReferencedGlobal()) {
        if (!global->isLet()) {
          context.emitNondifferentiabilityError(original, parentTask,
              diag::autodiff_cannot_differentiate_global_var_closures);
          return None;
        }
        // FIXME: In LLDB REPL, "main" will not be the function we should look
        // for.
        if (auto *mainFn = global->getModule().lookUpFunction("main")) {
          if (mainFn->isDefinition())
            for (auto &inst : mainFn->front())
              if (auto *globalAddrInMain = dyn_cast<GlobalAddrInst>(&inst))
                if (globalAddrInMain->getReferencedGlobal() == global)
                  for (auto *use : globalAddrInMain->getUses())
                    if (auto *store = dyn_cast<StoreInst>(use->getUser()))
                      if (store->getDest() == globalAddrInMain)
                        initialFnRef = peerThroughFunctionConversions
                            <FunctionRefInst>((initVal = store->getSrc()));
        }
      }
    }
    if (initialFnRef) {
      assert(initVal);
      auto *initialFn = initialFnRef->getReferencedFunction();
      auto *task =
          context.lookUpMinimalDifferentiationTask(initialFn, desiredIndices);
      if (!task) {
        if (initialFn->isExternalDeclaration()) {
          if (isInLLDBREPL(*original->getModule()))
            original->getModule()->loadFunction(initialFn);
          if (initialFn->isExternalDeclaration()) {
            context.emitNondifferentiabilityError(original, parentTask,
                diag::autodiff_global_let_closure_not_differentiable);
            return None;
          }
        }
        task = context.registerDifferentiationTask(
            initialFn, desiredIndices, invoker);
      }
      auto loc = original.getLoc();
      auto *assocFn = task->getAssociatedFunction(kind);
      auto assocFnGenSig =
          assocFn->getLoweredFunctionType()->getGenericSignature();
      auto *initialVJPRef = builder.createFunctionRef(loc, assocFn);
      auto converted =
          reapplyFunctionConversion(initialVJPRef, initialFnRef, initVal,
                                    builder, loc, assocFnGenSig);
      converted =
          reapplyFunctionConversion(converted, load, original,
                                    builder, loc, assocFnGenSig);
      SILAutoDiffIndices indices(0, desiredIndices.parameters);
      return std::make_pair(converted, indices);
    }
  }

  // Find witness method retrieval.
  if (auto *witnessMethod =
          peerThroughFunctionConversions<WitnessMethodInst>(original)) {
    auto loc = witnessMethod->getLoc();
    auto requirement = witnessMethod->getMember();
    auto *requirementDecl = requirement.getDecl();
    auto *diffAttr =
        requirementDecl->getAttrs().getAttribute<DifferentiableAttr>();
    if (!diffAttr) {
      context.emitNondifferentiabilityError(original, parentTask,
          diag::autodiff_protocol_member_not_differentiable);
      return None;
    }

    // Check that the requirement indices are the same as the desired indices.
    auto *requirementParameterIndices = diffAttr->getParameterIndices();
    auto loweredRequirementIndices = requirementParameterIndices->getLowered(
        requirementDecl->getInterfaceType()->castTo<AnyFunctionType>());
    SILAutoDiffIndices requirementIndices(/*source*/ 0,
                                          loweredRequirementIndices);

    if (desiredIndices.source != requirementIndices.source ||
        desiredIndices.parameters.test(requirementIndices.parameters)) {
      context.emitNondifferentiabilityError(original, parentTask,
          diag::autodiff_protocol_member_subset_indices_not_differentiable);
      return None;
    }

    auto originalType = witnessMethod->getType().castTo<SILFunctionType>();
    auto assocType = originalType->getAutoDiffAssociatedFunctionType(
        requirementIndices.parameters, requirementIndices.source,
        /*differentiationOrder*/ 1, kind, builder.getModule(),
        LookUpConformanceInModule(builder.getModule().getSwiftModule()));

    // Emit a witness_method instruction pointing at the associated function.
    auto *autoDiffFuncId = AutoDiffAssociatedFunctionIdentifier::get(
        kind, /*differentiationOrder*/ 1, requirementParameterIndices,
        context.getASTContext());
    auto *ref = builder.createWitnessMethod(
        loc, witnessMethod->getLookupType(), witnessMethod->getConformance(),
        requirement.asAutoDiffAssociatedFunction(autoDiffFuncId),
        SILType::getPrimitiveObjectType(assocType));
    auto convertedRef =
        reapplyFunctionConversion(ref, witnessMethod, original, builder, loc);
    return std::make_pair(convertedRef, requirementIndices);
  }

  // Emit the general opaque function error.
  context.emitNondifferentiabilityError(original, parentTask,
      diag::autodiff_opaque_function_not_differentiable);
  return None;
}

//===----------------------------------------------------------------------===//
// PrimalGen - generates primal functions for each differentiation task in
// the SIL module.
//===----------------------------------------------------------------------===//

namespace {
class PrimalGen {
  friend class PrimalGenCloner;

private:
  /// The global AD context.
  ADContext &context;

  /// A worklist of primal synthesis items, each of which specifies a the
  /// original function, the target primal function, AD indices, and the primal
  /// value struct.
  SmallVector<FunctionSynthesisItem, 16> worklist;

  /// Flag indicating there was an error during primal generation.
  bool errorOccurred = false;

public:
  explicit PrimalGen(ADContext &context) : context(context) {}

  /// Performs primal synthesis for all differentiation tasks. Returns true if
  /// any error occurs.
  bool run();

protected:
  /// If the task needs primal synthesis, and if primal synthesis for the task
  /// hasn't been scheduled yet, then schedule primal synthesis.
  void schedulePrimalSynthesisIfNeeded(DifferentiationTask *task);

private:
  /// Processes a synthesis item. Returns true if any error occurs.
  bool performSynthesis(FunctionSynthesisItem task);
};
} // end anonymous namespace

StructDecl *
ADContext::createPrimalValueStruct(const DifferentiationTask *task,
                                   CanGenericSignature primalGenericSig) {
  auto *function = task->getOriginal();
  assert(&function->getModule() == &module &&
         "The function must be in the same module");
  auto &file = getPrimalValueDeclContainer(function);
  // Create a `_<fn_name>__Type` struct.
  std::string pvStructName = "_AD__" + function->getName().str() + "__Type__" +
                             task->getIndices().mangle();
  auto structId = astCtx.getIdentifier(pvStructName);
  SourceLoc loc = function->getLocation().getSourceLoc();
  auto pvStruct =
      new (astCtx) StructDecl(/*StructLoc*/ loc, /*Name*/ structId,
                              /*NameLoc*/ loc, /*Inherited*/ {},
                              /*GenericParams*/ nullptr, // to be set later
                              /*DC*/ &file);
  // Set braces so that `pvStruct` can be dumped.
  pvStruct->setBraces(loc);
  if (primalGenericSig) {
    auto genericParams =
        cloneGenericParameters(astCtx, pvStruct, primalGenericSig);
    pvStruct->setGenericParams(genericParams);
    pvStruct->setGenericEnvironment(
        primalGenericSig->createGenericEnvironment());
  }
  switch (function->getEffectiveSymbolLinkage()) {
  case swift::SILLinkage::Public:
  case swift::SILLinkage::PublicNonABI:
    pvStruct->setAccess(AccessLevel::Internal);
    pvStruct->getAttrs().add(
        new (astCtx) UsableFromInlineAttr(/*Implicit*/ true));
    break;
  case swift::SILLinkage::Hidden:
  case swift::SILLinkage::Shared:
    pvStruct->setAccess(AccessLevel::Internal);
    break;
  case swift::SILLinkage::Private:
    pvStruct->setAccess(AccessLevel::FilePrivate);
    break;
  default:
    // When the original function has external linkage, we create an internal
    // struct for use by our own module. This is neccessary for cross-cell
    // differentiation in Jupyter.
    // TODO: Add a test in the compiler that exercises a similar situation as
    // cross-cell differentiation in Jupyter.
    pvStruct->setAccess(AccessLevel::Internal);
  }
  pvStruct->computeType();
  file.addVisibleDecl(pvStruct);
  LLVM_DEBUG({
    auto &s = getADDebugStream();
    s << "Primal value struct created for function " << function->getName()
      << '\n';
    pvStruct->print(s);
    s << '\n';
  });
  return pvStruct;
}

/// Given an parameter argument (not indirect result) and some differentiation
/// indices, figure out whether the parent function is being differentiated with
/// respect to this parameter, according to the indices.
static bool isDifferentiationParameter(SILArgument *argument,
                                       llvm::SmallBitVector indices) {
  if (!argument) return false;
  auto *function = argument->getFunction();
  auto paramArgs = function->getArgumentsWithoutIndirectResults();
  for (unsigned i : indices.set_bits())
    if (paramArgs[i] == argument)
      return true;
  return false;
}

/// For a nested function call that has results active on the differentiation
/// path, compute the set of minimal indices for differentiating this function
/// as required by the data flow.
static void collectMinimalIndicesForFunctionCall(
    ApplyInst *ai, SmallVectorImpl<SILValue> &results,
    const SILAutoDiffIndices &parentIndices,
    const DifferentiableActivityInfo &activityInfo,
    SmallVectorImpl<unsigned> &paramIndices,
    SmallVectorImpl<unsigned> &resultIndices) {
  // Make sure the function call has active results.
  // assert(activityInfo.isActive(ai, parentIndices));
  // TODO: REVISIT RESULT INDICES + INDIRECT RESULTS?
  assert(llvm::any_of(results, [&](SILValue result) {
    return activityInfo.isActive(result, parentIndices);
  }));
  auto fnTy = ai->getCallee()->getType().castTo<SILFunctionType>();
  SILFunctionConventions convs(fnTy, ai->getModule());
  auto arguments = ai->getArgumentOperands();
  // Parameter indices are indices (in the type signature) of parameter
  // arguments that are varied or are arguments.
  unsigned currentParamIdx = 0;
  for (auto applyArg : ai->getArgumentsWithoutIndirectResults()) {
    if (activityInfo.isVaried(applyArg, parentIndices.parameters) ||
        isDifferentiationParameter(dyn_cast<SILArgument>(applyArg),
                                   parentIndices.parameters))
      paramIndices.push_back(currentParamIdx);
    ++currentParamIdx;
  }
  // Result indices are indices (in the type signature) of results that are
  // useful.
  //
  // If the function returns only one result, then we just see if that is
  // useful.
  if (fnTy->getNumDirectFormalResults() == 1) {
    if (activityInfo.isUseful(ai, parentIndices.source))
      resultIndices.push_back(0);
    return;
  }
  // If the function returns more than 1 results, the return type is a tuple. We
  // need to find all `tuple_extract`s on that tuple, and determine if each
  // found extracted element is useful.
  // Collect direct results being retrieved using `tuple_extract`.
  SmallVector<SILValue, 8> usedDirectResults(convs.getNumDirectSILResults());
  for (auto *use : ai->getUses())
    if (auto *tei = dyn_cast<TupleExtractInst>(use->getUser()))
      usedDirectResults[tei->getFieldNo()] = tei;
  // Add differentiation indices based on activity analysis.
  unsigned dirResIdx = 0;
  unsigned indResIdx = convs.getSILArgIndexOfFirstIndirectResult();
  for (auto &resAndIdx : enumerate(convs.getResults())) {
    auto &res = resAndIdx.value();
    unsigned idx = resAndIdx.index();
    if (res.isFormalDirect()) {
      if (auto dirRes = usedDirectResults[dirResIdx])
        if (dirRes && activityInfo.isUseful(dirRes, parentIndices.source))
          resultIndices.push_back(idx);
      ++dirResIdx;
    } else {
      if (activityInfo.isUseful(arguments[indResIdx].get(),
                                parentIndices.source))
        resultIndices.push_back(idx);
      ++indResIdx;
    }
  }
}


  /*
  static CanGenericSignature
  buildThunkSignature(SILFunction* fn,
                      bool inheritGenericSig,
                      ArchetypeType *openedExistential,
                      GenericEnvironment *&genericEnv,
                      SubstitutionMap &contextSubs,
                      SubstitutionMap &interfaceSubs,
                      ArchetypeType *&newArchetype) {
    // auto *mod = fn->getModule().getSwiftModule();
    // auto &ctx = mod->getASTContext();

    // If there's no opened existential, we just inherit the generic environment
    // from the parent function.
    SILFunctionType *ty;
    // fn->getLowered
    assert(openedExistential == nullptr);
    auto genericSig = fn->getLoweredFunctionType()->getGenericSignature();
    genericEnv = fn->getGenericEnvironment();
    interfaceSubs = fn->getForwardingSubstitutionMap();
    contextSubs = interfaceSubs;
    return genericSig;
  }
  */

  static CanGenericSignature
  buildThunkSignature(SILFunctionType* fnType,
                      bool inheritGenericSig,
                      ArchetypeType *openedExistential,
                      GenericEnvironment *&genericEnv,
                      SubstitutionMap &contextSubs,
                      SubstitutionMap &interfaceSubs,
                      ArchetypeType *&newArchetype) {
    // auto *mod = fn->getModule().getSwiftModule();
    // auto &ctx = mod->getASTContext();

    // If there's no opened existential, we just inherit the generic environment
    // from the parent function.
    SILFunctionType *ty;
    // fn->getLowered
    assert(openedExistential == nullptr);
    auto genericSig = fnType->getGenericSignature();
    genericEnv = genericSig->createGenericEnvironment();
    interfaceSubs = genericEnv->getForwardingSubstitutionMap();
    contextSubs = interfaceSubs;
    return genericSig;
  }

  /// Build the type of a function transformation thunk.
  static CanSILFunctionType buildThunkType(SILModule &module,
                                           CanSILFunctionType &sourceType,
                                           CanSILFunctionType &expectedType,
                                           /*
                                           CanType &inputfromType,
                                           CanType &outputfromType,
                                            */
                                           CanType inputfromType,
                                           CanType outputfromType,
                                           GenericEnvironment *&genericEnv,
                                           SubstitutionMap &interfaceSubs,
                                           bool withoutActuallyEscaping) {
    assert(!expectedType->isPolymorphic());
    assert(!sourceType->isPolymorphic());

    auto origType = sourceType;

    // Can't build a thunk without context, so we require ownership semantics
    // on the result type.
    assert(expectedType->getExtInfo().hasContext());

    // This may inherit @noescape from the expectedType. The @noescape attribute
    // is only stripped when using this type to materialize a new decl.
    auto extInfo = expectedType->getExtInfo()
    .withRepresentation(SILFunctionType::Representation::Thin);

    if (withoutActuallyEscaping)
      extInfo = extInfo.withNoEscape(false);

    // Does the thunk type involve archetypes other than opened existentials?
    bool hasArchetypes = false;
    // Does the thunk type involve an open existential type?
    CanArchetypeType openedExistential;
    auto archetypeVisitor = [&](CanType t) {
      if (auto archetypeTy = dyn_cast<ArchetypeType>(t)) {
        if (archetypeTy->getOpenedExistentialType()) {
          assert((openedExistential == CanArchetypeType() ||
                  openedExistential == archetypeTy) &&
                 "one too many open existentials");
          openedExistential = archetypeTy;
        } else
          hasArchetypes = true;
      }
    };

    // Use the generic signature from the context if the thunk involves
    // generic parameters.
    CanGenericSignature genericSig;
    SubstitutionMap contextSubs;
    ArchetypeType *newArchetype = nullptr;

    if (expectedType->hasArchetype() || sourceType->hasArchetype()) {
      expectedType.visit(archetypeVisitor);
      sourceType.visit(archetypeVisitor);

      genericSig = buildThunkSignature(origType,
                                       hasArchetypes,
                                       openedExistential,
                                       genericEnv,
                                       contextSubs,
                                       interfaceSubs,
                                       newArchetype);
    }

    // Utility function to apply contextSubs, and also replace the
    // opened existential with the new archetype.
    auto substIntoThunkContext = [&](CanType t) -> CanType {
      return t.subst(
                     [&](SubstitutableType *type) -> Type {
                       if (CanType(type) == openedExistential)
                         return newArchetype;
                       return Type(type).subst(contextSubs);
                     },
                     LookUpConformanceInSubstitutionMap(contextSubs),
                     SubstFlags::AllowLoweredTypes)
      ->getCanonicalType();
    };

    sourceType = cast<SILFunctionType>(substIntoThunkContext(sourceType));
    expectedType = cast<SILFunctionType>(substIntoThunkContext(expectedType));

    /*
    if (inputfromType) {
      inputfromType = cast<AnyFunctionType>(substIntoThunkContext(inputfromType));
    }

    if (outputfromType) {
      outputfromType = cast<AnyFunctionType>(substIntoThunkContext(outputfromType));
    }
     */

    // If our parent function was pseudogeneric, this thunk must also be
    // pseudogeneric, since we have no way to pass generic parameters.
    if (genericSig)
      if (origType->isPseudogeneric())
        extInfo = extInfo.withIsPseudogeneric();

    // Add the function type as the parameter.
    auto contextConvention =
        SILType::getPrimitiveObjectType(sourceType).isTrivial(module)
        ? ParameterConvention::Direct_Unowned
        : ParameterConvention::Direct_Guaranteed;
    SmallVector<SILParameterInfo, 4> params;
    params.append(expectedType->getParameters().begin(),
                  expectedType->getParameters().end());
    params.push_back({sourceType,
      sourceType->getExtInfo().hasContext()
      ? contextConvention
      : ParameterConvention::Direct_Unowned});

    // Map the parameter and expected types out of context to get the interface
    // type of the thunk.
    SmallVector<SILParameterInfo, 4> interfaceParams;
    interfaceParams.reserve(params.size());
    for (auto &param : params) {
      auto paramIfaceTy = param.getType()->mapTypeOutOfContext();
      interfaceParams.push_back(
                                SILParameterInfo(paramIfaceTy->getCanonicalType(genericSig),
                                                 param.getConvention()));
    }

    SmallVector<SILYieldInfo, 4> interfaceYields;
    for (auto &yield : expectedType->getYields()) {
      auto yieldIfaceTy = yield.getType()->mapTypeOutOfContext();
      auto interfaceYield =
      yield.getWithType(yieldIfaceTy->getCanonicalType(genericSig));
      interfaceYields.push_back(interfaceYield);
    }

    SmallVector<SILResultInfo, 4> interfaceResults;
    for (auto &result : expectedType->getResults()) {
      auto resultIfaceTy = result.getType()->mapTypeOutOfContext();
      auto interfaceResult =
      result.getWithType(resultIfaceTy->getCanonicalType(genericSig));
      interfaceResults.push_back(interfaceResult);
    }

    Optional<SILResultInfo> interfaceErrorResult;
    if (expectedType->hasErrorResult()) {
      auto errorResult = expectedType->getErrorResult();
      auto errorIfaceTy = errorResult.getType()->mapTypeOutOfContext();
      interfaceErrorResult = SILResultInfo(
                                           errorIfaceTy->getCanonicalType(genericSig),
                                           expectedType->getErrorResult().getConvention());
    }

    // The type of the thunk function.
    return SILFunctionType::get(genericSig, extInfo,
                                expectedType->getCoroutineKind(),
                                ParameterConvention::Direct_Unowned,
                                interfaceParams, interfaceYields,
                                interfaceResults, interfaceErrorResult,
                                module.getASTContext());
  }

namespace {
class PrimalGenCloner final
    : public TypeSubstCloner<PrimalGenCloner, SILOptFunctionBuilder> {
private:
  /// A reference to this function synthesis item.
  const FunctionSynthesisItem &synthesis;

  /// Info from activity analysis on the original function.
  const DifferentiableActivityInfo &activityInfo;

  bool errorOccurred = false;

  /// Global PrimalGen.
  PrimalGen &primalGen;

  /// Global context.
  ADContext &getContext() { return primalGen.context; }

  SmallVector<SILValue, 8> primalValues;

  ASTContext &getASTContext() const {
    return synthesis.target->getASTContext();
  }

  DifferentiationTask *getDifferentiationTask() const { return synthesis.task; }

  SILFunction *getOriginal() const { return synthesis.original; }
  SILFunction *getPrimal() const { return synthesis.target; }

  PrimalInfo &getPrimalInfo() const {
    return *getDifferentiationTask()->getPrimalInfo();
  }

public:
  explicit PrimalGenCloner(const FunctionSynthesisItem &synthesis,
                           const DifferentiableActivityInfo &activityInfo,
                           SubstitutionMap substMap,
                           PrimalGen &primalGen, ADContext &context)
      : TypeSubstCloner(*synthesis.target, *synthesis.original, substMap),
        synthesis(synthesis),
        activityInfo(activityInfo),
        primalGen(primalGen) {}

  void postProcess(SILInstruction *orig, SILInstruction *cloned) {
    if (errorOccurred)
      return;
    SILClonerWithScopes::postProcess(orig, cloned);
  }

  // Run primal generation. Returns true on error.
  bool run() {
    auto *original = getOriginal();
    auto *primal = getPrimal();
    LLVM_DEBUG(getADDebugStream()
               << "Cloning original @" << original->getName()
               << " to primal @" << synthesis.target->getName() << '\n');
    // Create entry BB and arguments.
    auto *entry = primal->createBasicBlock();
    createEntryArguments(primal);
    auto entryArgs = map<SmallVector<SILValue, 4>>(
        entry->getArguments(), [](SILArgument *arg) { return arg; });
    // Clone.
    cloneFunctionBody(original, entry, entryArgs);
    // If errors occurred, back out.
    if (errorOccurred)
      return true;
    auto *origExit = &*original->findReturnBB();
    auto *exit = BBMap.lookup(origExit);
    assert(exit->getParent() == getPrimal());
    // Get the original's return value's corresponding value in the primal.
    auto *origRetInst = cast<ReturnInst>(origExit->getTerminator());
    auto origRetVal = origRetInst->getOperand();
    auto origResInPrimal = getOpValue(origRetVal);
    // Create a primal value struct containing all static primal values and
    // tapes.
    auto loc = getPrimal()->getLocation();
    /*
    auto structTy =
        getPrimalInfo().getPrimalValueStruct()->getDeclaredInterfaceType();
    if (auto primalGenericEnv = getPrimal()->getGenericEnvironment())
      structTy = primalGenericEnv->mapTypeIntoContext(structTy);
     */
    auto structTy = getOpASTType(getPrimalInfo().getPrimalValueStruct()->getDeclaredInterfaceType()->getCanonicalType());
    auto &builder = getBuilder();
    builder.setInsertionPoint(exit);
    auto structLoweredTy =
        getContext().getTypeConverter().getLoweredType(structTy);
    llvm::errs() << "PRIMAL VALUES\n";
    for (auto primalValue : primalValues) {
      primalValue->dump();
      // getPrimalInfo().lookUpPullbackDecl(<#SILInstruction *inst#>)
    }
    llvm::errs() << "DONE PRIMAL VALUES\n";
    auto primValsVal = builder.createStruct(loc, structLoweredTy, primalValues);
    // FIXME: Handle tapes.
    //
    // If the original result was a tuple, return a tuple of all elements in the
    // original result tuple and the primal value struct value.
    auto origResTy = origResInPrimal->getType();
    SILValue retVal;
    if (auto origResTupTy = origResTy.getAs<TupleType>()) {
      auto eltTypes = origResTupTy.getElementTypes();
      auto numElts = eltTypes.size();
      SmallVector<SILValue, 8> elts;
      elts.reserve(numElts + 1);
      elts.push_back(primValsVal);
      for (unsigned i : range(numElts))
        elts.push_back(builder.emitTupleExtract(loc, origResInPrimal, i));
      retVal = joinElements(elts, builder, loc);
    }
    // If the original result was a single value, return a tuple of the primal
    // value struct value and the original result.
    else {
      retVal = builder.createTuple(loc, {primValsVal, origResInPrimal});
    }
    builder.createReturn(loc, retVal);
    LLVM_DEBUG({
      auto &s = getADDebugStream()
                << "Primal values in $"
                << getPrimalInfo().getPrimalValueStruct()->getName() << ":\n";
      for (auto *var : getPrimalInfo().getPrimalValueStruct()->getMembers()) {
        var->dump(s);
        s << '\n';
      }
    });
    LLVM_DEBUG(getADDebugStream() << "Finished PrimalGen for function "
                                  << original->getName() << ":\n"
                                  << *getPrimal());
    debugDump(*getPrimal());
    return errorOccurred;
  }

  /// General visitor for all instruction. If there is any error emitted by
  /// previous visits, bail out.
  void visit(SILInstruction *inst) {
    if (errorOccurred)
      return;
    TypeSubstCloner::visit(inst);
  }

  void visitSILInstruction(SILInstruction *inst) {
    getContext().emitNondifferentiabilityError(inst, getDifferentiationTask(),
        diag::autodiff_expression_is_not_differentiable);
    errorOccurred = true;
  }

  void visitReturnInst(ReturnInst *ri) {
    // The original return is not to be cloned.
    return;
  }

      SILFunction *createThunk(SILLocation loc,
                               // CanSILFunctionType thunkType,
                               CanSILFunctionType fromType,
                               CanSILFunctionType toType) {
        SILOptFunctionBuilder fb(getContext().getTransform());

        // SILFunctionType::get(<#GenericSignature *genericSig#>, <#ExtInfo ext#>, <#SILCoroutineKind coroutineKind#>, <#ParameterConvention calleeConvention#>, <#ArrayRef<SILParameterInfo> interfaceParams#>, <#ArrayRef<SILYieldInfo> interfaceYields#>, <#ArrayRef<SILResultInfo> interfaceResults#>, <#Optional<SILResultInfo> interfaceErrorResult#>, <#const ASTContext &ctx#>)
        SubstitutionMap interfaceSubs;
        GenericEnvironment *genericEnv = nullptr;
        // buildThunkType(<#SILModule &module#>, <#CanSILFunctionType &sourceType#>, <#CanSILFunctionType &expectedType#>, <#CanType &inputfromType#>, <#CanType &outputfromType#>, <#GenericEnvironment *&genericEnv#>, <#SubstitutionMap &interfaceSubs#>, <#bool withoutActuallyEscaping#>)
        // auto thunkType = buildThunkType(getContext().getModule(), fromType, toType, fromType->getCanonicalType(), toType->getCanonicalType(), genericEnv, interfaceSubs, /*withoutActuallyEscaping*/ false);
        auto thunkType = buildThunkType(getContext().getModule(), fromType, toType, fromType->getCanonicalType(), toType->getCanonicalType(), genericEnv, interfaceSubs, /*withoutActuallyEscaping*/ false);
        // auto thunkType = SILFunctionType::get(toType->getGenericSignature(), toType->getExtInfo(),
        //                                       toType->getCoroutineKind(),
        //                                       ParameterConvention::Direct_Unowned,
        //                                       toType->getParameters(), toType->getYields(),
        //                                       toType->getResults(), toType->getOptionalErrorResult(),
        //                                       getASTContext());
        llvm::errs() << "THUNK TYPE\n";
        thunkType->dump();

        auto thunkDeclType =
            thunkType->getWithExtInfo(thunkType->getExtInfo().withNoEscape(false));

        auto fromInterfaceType = fromType->mapTypeOutOfContext()->getCanonicalType();
        auto toInterfaceType = toType->mapTypeOutOfContext()->getCanonicalType();

        Mangle::ASTMangler NewMangler;
        std::string name =
        NewMangler.mangleReabstractionThunkHelper(thunkType, fromInterfaceType, toInterfaceType, getContext().getModule().getSwiftModule());

        auto *thunk = fb.getOrCreateSharedFunction(loc, name, thunkType,
                                                   IsBare, IsTransparent, IsSerialized, ProfileCounter(), IsReabstractionThunk, IsNotDynamic);

        if (thunk->empty()) {
          thunk->setGenericEnvironment(genericEnv);
          // TranslateArguments
          // SILGenFunction thunkSGF(SGF.SGM, *thunk, SGF.FunctionDC);
          // auto loc = RegularLocation::getAutoGeneratedLocation();
          // buildThunkBody(thunkSGF, loc,
          //                inputOrigType,
          //                inputfromType,
          //                outputOrigType,
          //                outputfromType);

          auto *entry = thunk->createBasicBlock();
          SILBuilder builder(entry);
          createEntryArguments(thunk);

#if false
          // CanSILFunctionType toType = SpecializedFunc->getLoweredFunctionType();
          // CanSILFunctionType fromType = ReInfo.getSubstitutedType();
          // CanSILFunctionType toType = toType;
          // CanSILFunctionType fromType = fromType;
          // auto toConv = SpecializedFunc->getConventions();
          auto &module = getContext().getModule();
          SILFunctionConventions toConv(toType, module);
          (void)toConv;
          SILFunctionConventions fromConv(fromType, module);
          SmallVector<SILValue, 4> arguments;

          assert(toConv.useLoweredAddresses());

          // ReInfo.NumIndirectResults corresponds to SubstTy's formal indirect
          // results. SpecTy may have fewer formal indirect results.
          assert(fromType->getNumIndirectFormalResults()
                 >= toType->getNumIndirectFormalResults());

          SILArgument *returnValueAddr = nullptr;
          auto toArgIter = thunk->getArguments().begin();
          auto cloneSpecializedArgument = [&]() {
            // No change to the argument.
            SILArgument *toArg = *toArgIter++;
            // SILArgument *NewArg =
            // entry->createFunctionArgument(toArg->getType(), toArg->getDecl());
            arguments.push_back(toArg);
          };
          // ReInfo.NumIndirectResults corresponds to SubstTy's formal indirect
          // results. SpecTy may have fewer formal indirect results.
          assert(fromType->getNumIndirectFormalResults()
                 >= toType->getNumIndirectFormalResults());
          unsigned resultIdx = 0;
          for (auto substRI : fromType->getIndirectFormalResults()) {
            if (ReInfo.isFormalResultConverted(resultIdx++)) {
              // Convert an originally indirect to direct specialized result.
              // Store the result later.
              // FIXME: This only handles a single result! Partial specialization could
              // induce some combination of direct and indirect results.
              // SILType ResultTy = SpecializedFunc->mapTypeIntoContext(fromConv.getSILType(substRI));
              SILType ResultTy = fromConv.getSILType(substRI);
              assert(ResultTy.isAddress());
              assert(!returnValueAddr);
              returnValueAddr = entry->createFunctionArgument(ResultTy);
              continue;
            }
            // If the specialized result is already indirect, simply clone the indirect
            // result argument.
            assert((*toArgIter)->getType().isAddress());
            cloneSpecializedArgument();
          }
          assert(toArgIter == SpecializedFunc->getArgumentsWithoutIndirectResults().begin());
          unsigned numParams = toType->getNumParameters();
          assert(numParams == fromType->getNumParameters());
          for (unsigned paramIdx = 0; paramIdx < numParams; ++paramIdx) {
            if (ReInfo.isParamConverted(paramIdx)) {
              // Convert an originally indirect to direct specialized parameter.
              assert(!toConv.isSILIndirect(toType->getParameters()[paramIdx]));
              // Instead of passing the address, pass the loaded value.
              SILType ParamTy = SpecializedFunc->mapTypeIntoContext(
                  fromConv.getSILType(fromType->getParameters()[paramIdx]));
              assert(ParamTy.isAddress());
              SILArgument *toArg = *toArgIter++;
              SILArgument *NewArg =
              entry->createFunctionArgument(ParamTy, toArg->getDecl();
              auto *ArgVal =
              Builder.createLoad(loc, NewArg, LoadOwnershipQualifier::Unqualified);
              arguments.push_back(ArgVal);
              continue;
            }
            // Simply clone unconverted direct or indirect parameters.
            cloneSpecializedArgument();
          }
          assert(toArgIter == SpecializedFunc->getArguments().end());
          // return returnValueAddr;
#endif

          assert(thunk->getArguments().size() == 2);
          auto inputArg = thunk->getArgument(0);
          auto fnArg = thunk->getArgument(1);
          SILValue retVal;

          thunk->setUnqualifiedOwnership();
          // assert(inputArg->getType().isAddress());
          // assert(inputArg->getType().isObject());
          // LoadOwnershipQualifier
          if (inputArg->getType().isAddress()) {
            auto load = builder.createLoad(loc, inputArg, LoadOwnershipQualifier::Unqualified);
            auto apply = builder.createApply(loc, fnArg, interfaceSubs, {load}, /*isNonThrowing*/ true);
            auto store = builder.createStore(loc, apply, load, StoreOwnershipQualifier::Unqualified);
            // builder.createReturn(loc, undef);
          } else {
            // auto outArg = builder.createAllocStack(loc, fromType->getParameters()[])
            SILFunctionConventions hi(fromType, getContext().getModule());
            SmallVector<SILValue, 4> args;
            // args.push_back(inputArg);
            // hi.getArguments
            for (unsigned i : range(fromType->getNumParameters())) {
              llvm::errs() << "ARG TYPE\n";
              hi.getSILArgumentType(i).dump();
            }
            SmallVector<SILValue, 4> indirectArgs;
            for (unsigned i = hi.getSILArgIndexOfFirstParam(), n = hi.getNumSILArguments(); i < n; ++i) {
              auto argConv = hi.getSILArgumentConvention(i);
              // TODO: Check if there's a mismatch with the underlying function argument types
              if (argConv.isIndirectConvention()) {
                // indirectArgs.push_back(entry
                llvm::errs() << "FOUND INDIRECT ARG " << i << "\n";
                hi.getSILArgumentType(i).dump();
              }
            }
            for (auto res : hi.getIndirectSILResults()) {
              auto indRes = builder.createAllocStack(loc, res.getSILStorageType());
              llvm::errs() << "IND RES\n";
              indRes->dump();
              args.push_back(indRes);
            }
            // for (auto res : fromType->getCon
            SmallVector<SILValue, 4> applyArgs;
            applyArgs.append(args.begin(), args.end());
            applyArgs.push_back(inputArg);
            builder.createRetainValue(loc, inputArg, builder.getDefaultAtomicity());
            builder.createRetainValue(loc, fnArg, builder.getDefaultAtomicity());
            auto apply = builder.createApply(loc, fnArg, interfaceSubs, applyArgs, /*isNonThrowing*/ false);
            builder.createRetainValue(loc, apply, builder.getDefaultAtomicity());
            SmallVector<SILValue, 4> loads;
            for (auto arg : args) {
              auto load = builder.createLoad(loc, arg, LoadOwnershipQualifier::Unqualified);
              builder.createRetainValue(loc, load, builder.getDefaultAtomicity());
              // auto load = builder.createLoad(loc, arg, LoadOwnershipQualifier::Trivial);
              // auto load = builder.createLoadBorrow(loc, arg);
              loads.push_back(load);
            }
            for (auto arg : args) {
              builder.createDeallocStack(loc, arg);
            }
            SmallVector<SILValue, 4> results;
            results.push_back(apply);
            results.append(loads.begin(), loads.end());
            retVal = joinElements(results, builder, loc);
          }

          // retVal = SILUndef::get(thunkType->getAllResultsType(), getContext().getModule());
          builder.createReturn(loc, retVal);
          // return thu

          // builder.createApply(loc, thunk, <#SubstitutionMap Subs#>, <#ArrayRef<SILValue> Args#>, <#bool isNonThrowing#>)
        }

        llvm::errs() << "THUNK BODY\n";
        thunk->dump();
        /*
        CanSILFunctionType toType = SpecializedFunc->getLoweredFunctionType();
        Lowering::GenericContextScope GenericScope(M.Types,
                                                   toType->getGenericSignature());
         */


        return thunk;
      }

  void visitStructExtractInst(StructExtractInst *sei) {
    auto &strategies =
        getDifferentiationTask()->getStructExtractDifferentiationStrategies();
    // Special handling logic only applies when the `struct_extract` is active.
    // If not, just do standard cloning.
    if (!activityInfo.isActive(sei, synthesis.indices)) {
      LLVM_DEBUG(getADDebugStream() << "Not active:\n" << *sei << '\n');
      strategies.insert(
          {sei, StructExtractDifferentiationStrategy::Inactive});
      SILClonerWithScopes::visitStructExtractInst(sei);
      return;
    }
    // This instruction is active. Determine the appropriate differentiation
    // strategy, and use it.
    auto *structDecl = sei->getStructDecl();
    if (structDecl->getAttrs().hasAttribute<FieldwiseDifferentiableAttr>()) {
      strategies.insert(
          {sei, StructExtractDifferentiationStrategy::Fieldwise});
      SILClonerWithScopes::visitStructExtractInst(sei);
      return;
    }
    // The FieldwiseProductSpace strategy is not appropriate, so use the Getter
    // strategy.
    strategies.insert(
        {sei, StructExtractDifferentiationStrategy::Getter});
    // Find the corresponding getter and its VJP.
    auto *getterDecl = sei->getField()->getGetter();
    assert(getterDecl);
    auto *getterFn = getContext().getModule().lookUpFunction(
        SILDeclRef(getterDecl, SILDeclRef::Kind::Func));
    if (!getterFn) {
      getContext().emitNondifferentiabilityError(
          sei, synthesis.task, diag::autodiff_property_not_differentiable);
      errorOccurred = true;
      return;
    }
    SILAutoDiffIndices indices(/*source*/ 0, /*parameters*/ {0});
    auto *task = getContext().lookUpDifferentiationTask(getterFn, indices);
    if (!task) {
      getContext().emitNondifferentiabilityError(
          sei, synthesis.task, diag::autodiff_property_not_differentiable);
      errorOccurred = true;
      return;
    }
    // Reference and apply the VJP.
    auto loc = sei->getLoc();
    auto *getterVJPRef = getBuilder().createFunctionRef(loc, task->getVJP());
    auto *getterVJPApply = getBuilder().createApply(
        loc, getterVJPRef, /*substitutionMap*/ {},
        /*args*/ {getMappedValue(sei->getOperand())}, /*isNonThrowing*/ false);
    SmallVector<SILValue, 8> vjpDirectResults;
    extractAllElements(getterVJPApply, getBuilder(), vjpDirectResults);
    // Map original results.
    auto originalDirectResults =
        ArrayRef<SILValue>(vjpDirectResults).drop_back(1);
    SILValue originalDirectResult = joinElements(originalDirectResults,
                                                 getBuilder(),
                                                 getterVJPApply->getLoc());
    mapValue(sei, originalDirectResult);
    // Checkpoint the pullback.
    SILValue pullback = vjpDirectResults.back();
    // getPrimalInfo().addPullbackDecl(sei, pullback->getType().getASTType());
    getPrimalInfo().addPullbackDecl(sei, pullback->getType());
    auto loweredType = getContext().getTypeConverter().getLoweredType(pullback->getType().getASTType());
    // auto loweredType2 = getContext().getModule().getTypeLowering(pullback->getType()).getSemanticType();
    // getContext().getModule().getTypeLowering(<#SILType t#>)
    if (loweredType != pullback->getType()) {
      assert(false && "bad pullback type");
    }
    // getContext().getModule().getTypeLowering(pullback->getType().getASTType()).get
    // if (pullback->getType().getASTType()->getAs<AnyFunctionType>())
    //   ;
    primalValues.push_back(pullback);
  }

  // Return the substitution map for the associated function of an `apply`
  // instruction. If the associated derivative has generic requirements that are
  // unfulfilled by the primal function, emit "callee requirements unmet"
  // diagnostics for each unmet requirement and return `None`.
  Optional<SubstitutionMap> getOrDiagnoseAssociatedFunctionSubstitutionMap(
      ApplyInst *ai, CanSILFunctionType assocFnTy) {
    auto &context = getContext();
    auto *swiftModule = context.getModule().getSwiftModule();
    auto origSubstMap = ai->getSubstitutionMap();
    auto assocGenSig = assocFnTy->getGenericSignature();
    // If associated derivative has no generic signature, then short-circuit and
    // return original substitution map.
    if (!assocGenSig)
      return origSubstMap;

    // Get the associated function substitution map.
    auto assocGenEnv = assocGenSig->createGenericEnvironment();
    auto assocSubstMap = assocGenEnv->getForwardingSubstitutionMap();
    // If the primal function has a generic environment, use it to update
    // `origSubstMap` (because the primal substitution map may have more
    // requirements).
    if (auto primalGenEnv = getPrimal()->getGenericEnvironment())
      origSubstMap = SubstitutionMap::get(
          primalGenEnv->getGenericSignature(),
          QuerySubstitutionMap{origSubstMap},
          LookUpConformanceInModule(swiftModule));
    // Get the cloner substitution map.
    auto substMap = SubsMap.empty() ? origSubstMap : SubsMap;

    // Jointly iterate through requirements and conformances of associated
    // function.
    SmallVector<Requirement, 2> unsatisfiedRequirements;
    auto conformances = assocSubstMap.getConformances();
    for (auto req : assocGenSig->getRequirements()) {
      if (req.getKind() != RequirementKind::Conformance)
        continue;
      auto conformance = conformances.front();
      auto *proto = conformance.getAbstract();
      assert(proto && "Expected protocol in generic signature requirement");
      auto reqType = req.getFirstType();
      // Try substituting requirement type using original substutition map. If
      // the result type is known to conform to protocol in the current module,
      // continue.
      // This handles cases where the primal caller is non-generic (specialized
      // with concrete types) but the associated derivative callee is generic.
      if (auto origFirstType = reqType.subst(origSubstMap)) {
        if (!origFirstType->hasError() &&
            swiftModule->lookupConformance(origFirstType, proto)) {
          conformances = conformances.slice(1);
          continue;
        }
      }
      // Otherwise, try to look up conformance in substitution maps.
      auto isConformanceMet =
          origSubstMap.lookupConformance(reqType->getCanonicalType(), proto) ||
          substMap.lookupConformance(reqType->getCanonicalType(), proto);
      if (!isConformanceMet)
        unsatisfiedRequirements.push_back(req);
      conformances = conformances.slice(1);
    }
    // Diagnose unsatisfied requirements.
    if (!unsatisfiedRequirements.empty()) {
      context.emitNondifferentiabilityError(
          ai, getDifferentiationTask(),
          diag::autodiff_function_assoc_func_requirements_unmet);
      return None;
    }

    // If all requirements are satisfied, return target substitution map.
    return SubstitutionMap::get(
        assocSubstMap.getGenericSignature(),
        QuerySubstitutionMap{substMap},
        LookUpConformanceInModule(context.getModule().getSwiftModule()));
  }

  /*
  void visitPartialApplyInst(PartialApplyInst *pai) {
    auto &context = getContext();

    llvm::errs() << "PRIMAL GEN CHECK PAI\n";
    pai->dumpInContext();
    if (auto fn = isPartialApplyOfReabstractionThunk(pai)) {
      llvm::errs() << "WOAH WE FOUND REABSTRACTION THUNK!";
      fn->dump();
    }

    // Special handling logic only applies when `partial_apply` is a
    // reabstraction thunk. If not, just do standard cloning.
    if (!activityInfo.isActive(pai, synthesis.indices)) {
      LLVM_DEBUG(getADDebugStream() << "Not active:\n" << *pai << '\n');
      SILClonerWithScopes::visitPartialApplyInst(pai);
      return;
    }
  }
   */

  void visitApplyInst(ApplyInst *ai) {
    auto &context = getContext();

    if (getOriginal()->isThunk() == IsReabstractionThunk) {
      llvm::errs() << "WOAH WE FOUND REABSTRACTION THUNK!\n";
      auto *origFn = ai->getReferencedFunction();
      ai->dumpInContext();
      // origFn->dump();
    }
    /*
    auto *reabsThunk = ai->getReferencedFunction();
    if (reabsThunk && reabsThunk->isThunk() == IsReabstractionThunk) {
      llvm::errs() << "WOAH WE FOUND REABSTRACTION THUNK!";
      auto *fn = reabsThunk->getArguments().back();
      fn->dump();
    }
     */

    // Special handling logic only applies when `apply` is active. If not, just
    // do standard cloning.
    // if (!activityInfo.isActive(ai, synthesis.indices)) {
    SmallVector<SILValue, 4> dirResults;
    extractAllElements(ai, getBuilder(), dirResults);
    SmallVector<SILValue, 4> allResults;
    collectAllActualResultsInTypeOrder(
        ai, dirResults, ai->getIndirectSILResults(), allResults);
    for (auto r : allResults) {
      llvm::errs() << "IS RESULT ACTIVE?\n";
      r->dump();
      llvm::errs() << activityInfo.isActive(r, synthesis.indices);
    }
    if (llvm::none_of(allResults, [&](SILValue result) {
      return activityInfo.isActive(result, synthesis.indices);
    })) {
      LLVM_DEBUG(getADDebugStream() << "Not active:\n" << *ai << '\n');
      SILClonerWithScopes::visitApplyInst(ai);
      return;
    }

    // This instruction is active. Replace it with a call to the VJP.

    // Get the indices required for differentiating this function.
    LLVM_DEBUG(getADDebugStream() << "Primal-transforming:\n" << *ai << '\n');
    SmallVector<unsigned, 8> activeParamIndices;
    SmallVector<unsigned, 8> activeResultIndices;
    collectMinimalIndicesForFunctionCall(ai, allResults, synthesis.indices,
                                         activityInfo, activeParamIndices,
                                         activeResultIndices);
    assert(!activeParamIndices.empty() && "Parameter indices cannot be empty");
    assert(!activeResultIndices.empty() && "Result indices cannot be empty");
    LLVM_DEBUG(auto &s = getADDebugStream() << "Active indices: params={";
               interleave(activeParamIndices.begin(), activeParamIndices.end(),
                          [&s](unsigned i) { s << i; }, [&s] { s << ", "; });
               s << "}, results={"; interleave(
                   activeResultIndices.begin(), activeResultIndices.end(),
                   [&s](unsigned i) { s << i; }, [&s] { s << ", "; });
               s << "}\n";);

    // FIXME: If there are mutiple active results, we don't support it yet.
    if (activeResultIndices.size() > 1) {
      context.emitNondifferentiabilityError(ai, synthesis.task);
      errorOccurred = true;
      return;
    }

    // Form expected indices by assuming there's only one result.
    SILAutoDiffIndices indices(activeResultIndices.front(), activeParamIndices);

    // Emit the VJP.
    auto vjpAndVJPIndices = emitAssociatedFunctionReference(
        context, getBuilder(), getDifferentiationTask(), indices,
        AutoDiffAssociatedFunctionKind::VJP, getMappedValue(ai->getCallee()),
        /*invoker*/ {ai, synthesis.task}, [&](DifferentiationTask *newTask) {
          primalGen.schedulePrimalSynthesisIfNeeded(newTask);
        });
    if (!vjpAndVJPIndices) {
      context.emitNondifferentiabilityError(ai, synthesis.task);
      errorOccurred = true;
      return;
    }
    auto vjp = vjpAndVJPIndices->first;

    // Emit error if callee type has indirect differentiation parameters/result.
    /*
    if (diagnoseIndirectParametersOrResult(
            vjp->getType().getAs<SILFunctionType>(), getContext(),
            getDifferentiationTask())) {
      errorOccurred = true;
      return;
    }
     */

    // Record the VJP's indices.
    getDifferentiationTask()->getNestedApplyActivities().insert(
        {ai, {vjpAndVJPIndices->second}});

    // Call the VJP using the original parameters.
    SmallVector<SILValue, 8> newArgs;
    auto vjpFnTy = vjp->getType().castTo<SILFunctionType>();
    // auto numVJPParams = vjpFnTy->getNumParameters();
    auto numVJPParams = vjpFnTy->getNumParameters() + vjpFnTy->getNumIndirectFormalResults();
    llvm::errs() << "VFJ FN TYPE, NUM PARAMS: " << numVJPParams << ", NUM FORMAL INDIRECT RESULTS: " << vjpFnTy->getNumIndirectFormalResults() << "\n";
    vjpFnTy->dump();
    llvm::errs() << "WHAT AI IS HERE?\n";
    ai->dumpInContext();
    // assert(vjpFnTy->getNumIndirectFormalResults() == 0 &&
    //        "FIXME: handle vjp with indirect results");
    newArgs.reserve(numVJPParams);
    // Collect indirect results.
    // if (activeResultIndices[0] > vjpFnTy->getNumIndirectFormalResults())
    //   newArgs.push_back(getOpValue(origArg));
    // Collect substituted arguments.
    for (auto origArg : ai->getArguments())
      newArgs.push_back(getOpValue(origArg));
    assert(newArgs.size() == numVJPParams);
    // Get the VJP substitution map and apply the VJP.
    auto substMap = getOrDiagnoseAssociatedFunctionSubstitutionMap(ai, vjpFnTy);
    if (!substMap) {
      errorOccurred = true;
      return;
    }
    auto *vjpCall = getBuilder().createApply(ai->getLoc(), vjp, *substMap,
                                             newArgs, ai->isNonThrowing());
    LLVM_DEBUG(getADDebugStream() << "Applied vjp function\n" << *vjpCall);

    // Get the VJP results (original results and pullback).
    SmallVector<SILValue, 8> vjpDirectResults;
    extractAllElements(vjpCall, getBuilder(), vjpDirectResults);
    ArrayRef<SILValue> originalDirectResults =
        ArrayRef<SILValue>(vjpDirectResults).drop_back(1);
    SILValue originalDirectResult = joinElements(originalDirectResults,
                                                 getBuilder(),
                                                 vjpCall->getLoc());
    SILValue pullback = vjpDirectResults.back();

    // Store the original result to the value map.
    mapValue(ai, originalDirectResult);

    // Checkpoint the pullback.
    // getPrimalInfo().addPullbackDecl(ai, pullback->getType().getASTType());
    auto *pullbackDecl = getPrimalInfo().addPullbackDecl(ai, pullback->getType());
    auto loweredPullbackType = getContext().getTypeConverter().getLoweredType(pullbackDecl->getInterfaceType()->getCanonicalType()).castTo<SILFunctionType>();
    // auto expectedPullbackType = pullbackDecl->getInterfaceType()->getCanonicalType();
    /*
    // auto loweredType2 = getContext().getModule().getTypeLowering(pullback->getType()).getSemanticType();
    llvm::errs() << "PULLBACK TYPE:\n";
    pullback->getType().dump();
    llvm::errs() << "LOWERED PULLBACK ASTTYPE TYPE:\n";
    loweredType.dump();
    // getContext().getModule().getTypeLowering(<#SILType t#>)
    if (loweredType != pullback->getType()) {
      assert(false && "bad pullback type");
    }
     */
    auto actualPullbackType = pullback->getType().getAs<SILFunctionType>();
    if (!loweredPullbackType->isEqual(actualPullbackType)) {
      auto thunk = createThunk(ai->getLoc(), actualPullbackType, loweredPullbackType);
      auto thunkFRI = getBuilder().createFunctionRef(ai->getLoc(), thunk);
      pullback = getBuilder().createPartialApply(ai->getLoc(), thunkFRI, thunk->getForwardingSubstitutionMap(), {pullback}, actualPullbackType->getCalleeConvention());
      llvm::errs() << "BOOYA PARTIAL APPLY\n";
      pullback->dumpInContext();
    }
    primalValues.push_back(pullback);

    // Some instructions that produce the callee may have been cloned.
    // If the original callee did not have any users beyond this `apply`,
    // recursively kill the cloned callee.
    if (auto *origCallee = cast_or_null<SingleValueInstruction>(
            ai->getCallee()->getDefiningInstruction()))
      if (origCallee->hasOneUse())
        recursivelyDeleteTriviallyDeadInstructions(
            getOpValue(origCallee)->getDefiningInstruction());
  }

  /// Primal has qualified ownership. We assign store ownership qualifier while
  /// cloning the `store` instruction.
  void visitStoreInst(StoreInst *si) {
    auto destTy = si->getDest()->getType().getASTType();
    auto loc = remapLocation(si->getLoc());
    auto soq = getBufferSOQ(getOpASTType(destTy), *getPrimal());
    getBuilder().createStore(loc, getOpValue(si->getSrc()),
                             getOpValue(si->getDest()), soq);
  }

  /// Primal has qualified ownership. We assign load ownership qualified while
  /// cloning the `load` instruction.
  void visitLoadInst(LoadInst *li) {
    auto srcTy = li->getOperand()->getType().getASTType();
    auto loc = remapLocation(li->getLoc());
    auto loq = getBufferLOQ(getOpASTType(srcTy), *getPrimal());
    mapValue(
        li, getBuilder().createLoad(loc, getOpValue(li->getOperand()), loq));
  }
};
} // end anonymous namespace

bool PrimalGen::performSynthesis(FunctionSynthesisItem item) {
  LLVM_DEBUG(getADDebugStream() << "Performing primal synthesis for original "
             << item.original->getName() << " and its corresponding primal "
             << item.target->getName() << '\n');
  // FIXME: If the original function has multiple basic blocks, bail out since
  // AD does not support control flow yet.
  // FIXME: If the original function has indirect differentiation
  // parameters/result, bail out since AD does not support function calls with
  // indirect parameters yet.
  /*
  if (diagnoseUnsupportedControlFlow(context, item.task) ||
      diagnoseIndirectParametersOrResult(
          item.original->getLoweredFunctionType(), context, item.task)) {
  */
  if (diagnoseUnsupportedControlFlow(context, item.task)) {
    errorOccurred = true;
    return true;
  }
  // Compute necessary analyses on the original function.
  auto &passManager = context.getPassManager();
  auto *activityAnalysis =
      passManager.getAnalysis<DifferentiableActivityAnalysis>();
  auto &activityInfo = *activityAnalysis->get(item.original);
  // For debugging, dump the original function's activity analysis.
  LLVM_DEBUG(dumpActivityInfo(*item.original, item.task->getIndices(),
                              activityInfo, getADDebugStream()));
  // Synthesize primal.
  auto substMap = item.original->getForwardingSubstitutionMap();
  if (auto primalGenEnv = item.target->getGenericEnvironment())
    substMap = substMap.subst(primalGenEnv->getForwardingSubstitutionMap());
  PrimalGenCloner cloner(item, activityInfo, substMap, *this, context);
  // Run the cloner.
  return cloner.run();
}

void PrimalGen::schedulePrimalSynthesisIfNeeded(DifferentiationTask *task) {
  if (task->getPrimalSynthesisState() == FunctionSynthesisState::Needed) {
    auto *primal = task->getPrimal();
    assert(primal);
    FunctionSynthesisItem synthesis{task->getOriginal(), primal,
                                    task->getIndices(), task};
    worklist.push_back(synthesis);
    task->setPrimalSynthesisState(FunctionSynthesisState::Pending);
  }
}

bool PrimalGen::run() {
  // Push everything to the list of primal synthesis items.
  for (auto &task : context.getDifferentiationTasks())
    schedulePrimalSynthesisIfNeeded(task.get());
  // Process each item until empty.
  while (!worklist.empty()) {
    auto synthesis = worklist.back();
    worklist.pop_back();
    if (performSynthesis(synthesis)) {
      errorOccurred = true;
      continue;
    }
    synthesis.task->setPrimalSynthesisState(FunctionSynthesisState::Done);
  }
  return errorOccurred;
}

//===----------------------------------------------------------------------===//
// AdjointGen - generates an adjoint function for each differentiation task
// in a SIL module.
//===----------------------------------------------------------------------===//

/// The adjoint generator for all differentiation tasks.
namespace {

class AdjointGen {
  friend class AdjointEmitter;

private:
  /// The global AD context.
  ADContext &context;

  /// Work list of synthesis items.
  SmallVector<FunctionSynthesisItem, 16> worklist;

  /// Flag indicating whether an error has occurred.
  bool errorOccurred = false;

public:
  explicit AdjointGen(ADContext &context) : context(context) {}

  /// Performs adjoint generation for all differentiation tasks. Returns true if
  /// any error occurs.
  bool run();

private:
  /// Do the synthesis item. Returns true if any error occurs.
  bool performSynthesis(FunctionSynthesisItem item);
};
} // end anonymous namespace

bool AdjointGen::run() {
  // Push everything to the worklist.
  for (auto &task : context.getDifferentiationTasks()) {
    if (task->getPrimalSynthesisState() != FunctionSynthesisState::Done)
      continue;
    if (task->getAdjointSynthesisState() == FunctionSynthesisState::Needed) {
      FunctionSynthesisItem synthesis{task->getOriginal(), task->getAdjoint(),
                                      task->getIndices(), task.get()};
      worklist.push_back(synthesis);
      task->setAdjointSynthesisState(FunctionSynthesisState::Pending);
    }
  }
  // Iterate over the worklist, look up existing adjoint. If an adjoint exists
  // for the task, do nothing. Otherwise, create a function and process it.
  while (!worklist.empty()) {
    auto synthesis = worklist.back();
    worklist.pop_back();
    if (performSynthesis(synthesis)) {
      errorOccurred = true;
      continue;
    }
    synthesis.task->setAdjointSynthesisState(FunctionSynthesisState::Done);
  }
  return errorOccurred;
}

//===----------------------------------------------------------------------===//
// AdjointValue - a symbolic representation for adjoint values that allows
// for efficient differentiation of aggregates.
//===----------------------------------------------------------------------===//

namespace {
class AdjointEmitter;
class AdjointValue;

class Cleanup {
public:
  using Func = void(*)(SILBuilder &, SILLocation, SILValue);

private:
  SILValue value;
  Func func;
  unsigned numChildren;

  Cleanup **getChildrenData() {
    return reinterpret_cast<Cleanup **>(this + 1);
  }

  Cleanup(SILValue value, Func func, ArrayRef<Cleanup *> children)
      : value(value), func(func), numChildren(children.size()) {
    assert(((func && value) || !func) &&
           "Value must be non-null when the function is non-null");
    assert(llvm::all_of(children, [](Cleanup *c) { return (bool)c; }));
    LLVM_DEBUG(getADDebugStream() << "Creating a cleanup with " << numChildren
               << " children.\n");
    std::uninitialized_copy(children.begin(), children.end(),
                            getChildrenData());
    assert(llvm::all_of(llvm::zip(children, getChildren()),
                        [](std::tuple<Cleanup *, Cleanup *> pair) {
      return std::get<0>(pair) == std::get<1>(pair);
    }));
  }

public:
  Cleanup() = delete;
  Cleanup(Cleanup &) = delete;
  Cleanup &operator=(const Cleanup &) = delete;

  static Cleanup *create(llvm::BumpPtrAllocator &allocator, SILValue value,
                         Func func, ArrayRef<Cleanup *> children) {
    auto *buf = allocator.Allocate(
        sizeof(Cleanup) + sizeof(Cleanup *) * children.size(),
        alignof(Cleanup));
    return new (buf) Cleanup(value, func, children);
  }

  unsigned getNumChildren() const {
    return numChildren;
  }

  ArrayRef<Cleanup *> getChildren() const {
    return {const_cast<Cleanup *>(this)->getChildrenData(), numChildren};
  }

  /// Disable this cleanup and makes its application a no-op.
  void disable() {
    func = nullptr;
  }

  /// Apply and invaliate the cleanup.
  void apply(SILBuilder &builder, SILLocation loc) {
    if (!func) return;
    assert(value);
    LLVM_DEBUG(getADDebugStream() << "Running `Cleanup::apply` for "
               << value << '\n');
    func(builder, loc, value);
    func = nullptr;
  }

  /// Apply the cleanup and its children recursively and invalidate them.
  void applyRecursively(SILBuilder &builder, SILLocation loc) {
    apply(builder, loc);
    for (auto *child : getChildren()) {
      assert(child);
      child->applyRecursively(builder, loc);
    }
  }
};

class ValueWithCleanup {
private:
  SILValue value;
  Cleanup *cleanup;

public:
  explicit ValueWithCleanup(SILValue value, Cleanup *cleanup = nullptr)
      : value(value), cleanup(cleanup) {}

public:
  SILValue getValue() const { return value; }
  operator SILValue() const { return getValue(); }
  void setValue(SILValue value) { this->value = value; }
  Cleanup *getCleanup() const { return cleanup; }
  void setCleanup(Cleanup *cleanup) { this->cleanup = cleanup; }

  SILLocation getLoc() const { return value.getLoc(); }
  SILType getType() const { return value->getType(); }
};

enum AdjointValueKind {
  /// An empty adjoint, i.e. zero. This case exists due to its special
  /// mathematical properties: `0 + x = x`. This is a guaranteed optimization
  /// when we combine a zero adjoint with another (e.g. differentiating a
  /// fanout).
  Zero,

  /// An aggregate of adjoint values.
  Aggregate,

  /// A concrete SIL value.
  Concrete,
};

class AdjointValueBase {
  friend class AdjointValue;

  /// The kind of this adjoint value.
  AdjointValueKind kind;

  /// The type of this value as if it were materialized as a SIL value.
  SILType type;

  /// The underlying value.
  union Value {
    MutableArrayRef<AdjointValue> aggregate;
    ValueWithCleanup concrete;
    Value(MutableArrayRef<AdjointValue> v) : aggregate(v) {}
    Value(ValueWithCleanup v) : concrete(v) {}
    Value() {}
  } value;

  explicit AdjointValueBase(SILType type,
                            MutableArrayRef<AdjointValue> aggregate)
      : kind(AdjointValueKind::Aggregate), type(type), value(aggregate) {}

  explicit AdjointValueBase(ValueWithCleanup v)
      : kind(AdjointValueKind::Concrete), type(v.getType()), value(v) {}

  explicit AdjointValueBase(SILType type)
      : kind(AdjointValueKind::Zero), type(type) {}
};

/// A symbolic adjoint value that is capable of representing zero value 0 and
/// 1, in addition to a materialized SILValue. This is expected to be passed
/// around by value in most cases, as it's two words long.
class AdjointValue final {
  friend class AdjointEmitter;

private:
  /// The kind of this adjoint value.
  AdjointValueBase *base;
  /*implicit*/ AdjointValue(AdjointValueBase *base = nullptr) : base(base) {}

public:
  AdjointValue(const AdjointValue &) = delete;
  AdjointValue &operator=(const AdjointValue &) = delete;
  AdjointValue(AdjointValue &&val) = default;
  AdjointValue &operator=(AdjointValue &&) = default;

  AdjointValueBase *operator->() const { return base; }
  AdjointValueBase &operator*() const { return *base; }

  static AdjointValue createConcrete(llvm::BumpPtrAllocator &allocator,
                                     ValueWithCleanup value) {
    return new (allocator.Allocate<AdjointValueBase>()) AdjointValueBase(value);
  }

  template<typename EltMoveRange>
  static AdjointValue createAggregate(llvm::BumpPtrAllocator &allocator,
                                      SILType type, EltMoveRange &&elements) {
    AdjointValue *buf = reinterpret_cast<AdjointValue *>(allocator.Allocate(
        elements.size() * sizeof(AdjointValue), alignof(AdjointValue)));
    MutableArrayRef<AdjointValue> elementsCopy(buf, elements.size());
    std::move(elements.begin(), elements.end(), elementsCopy.begin());
    return new (allocator.Allocate<AdjointValueBase>())
        AdjointValueBase(type, elementsCopy);
  }

  static AdjointValue createZero(llvm::BumpPtrAllocator &allocator,
                                 SILType type) {
    return new (allocator.Allocate<AdjointValueBase>()) AdjointValueBase(type);
  }

  AdjointValueKind getKind() const { return base->kind; }
  SILType getType() const { return base->type; }
  CanType getSwiftType() const { return getType().getASTType(); }

  NominalTypeDecl *getAnyNominal() const {
    return getSwiftType()->getAnyNominal();
  }

  bool isZero() const { return getKind() == AdjointValueKind::Zero; }
  bool isAggregate() const { return getKind() == AdjointValueKind::Aggregate; }
  bool isConcrete() const { return getKind() == AdjointValueKind::Concrete; }

  unsigned getNumAggregateElements() const {
    assert(isAggregate());
    return base->value.aggregate.size();
  }

  AdjointValue takeAggregateElement(unsigned i) {
    assert(isAggregate());
    return std::move(base->value.aggregate[i]);
  }

  ValueWithCleanup getConcreteValue() const {
    assert(isConcrete());
    return base->value.concrete;
  }

  void print(llvm::raw_ostream &s) const {
    switch (getKind()) {
    case AdjointValueKind::Zero:
      s << "Zero";
      break;
    case AdjointValueKind::Aggregate:
      s << "Aggregate<";
      if (auto *decl =
            getType().getASTType()->getStructOrBoundGenericStruct()) {
        s << "Struct>(";
        interleave(llvm::zip(decl->getStoredProperties(),
                             base->value.aggregate),
                             [&s](std::tuple<VarDecl *,
                                             const AdjointValue &> elt) {
                               s << std::get<0>(elt)->getName() << ": ";
                               std::get<1>(elt).print(s);
                             }, [&s] { s << ", "; });
      } else if (auto tupleType = getType().getAs<TupleType>()) {
        s << "Tuple>(";
        interleave(base->value.aggregate,
                   [&s](const AdjointValue &elt) { elt.print(s); },
                   [&s] { s << ", "; });
      } else {
        llvm_unreachable("Invalid aggregate");
      }
      s << ')';
      break;
    case AdjointValueKind::Concrete:
      s << "Concrete(" << base->value.concrete.getValue() << ')';
      break;
    }
  }
};

inline llvm::raw_ostream &operator<<(llvm::raw_ostream &os,
                                     const AdjointValue &adjVal) {
  adjVal.print(os);
  return os;
}

} // end anonymous namespace

//===----------------------------------------------------------------------===//
// AdjointEmitter - visitors on the original function for adjoint code
// generation
//===----------------------------------------------------------------------===//

namespace {
class AdjointEmitter final : public SILInstructionVisitor<AdjointEmitter> {
private:
  /// A reference to this function synthesis item.
  const FunctionSynthesisItem &synthesis;

  /// Info from activity analysis on the original function.
  const DifferentiableActivityInfo &activityInfo;

  /// Post-dominance info.
  const PostDominanceInfo &postDomInfo;

  /// Global AdjointGen.
  AdjointGen &adjointGen;

  /// Mapping from original values to their corresponding adjoint values.
  DenseMap<SILValue, AdjointValue> valueMap;

  /// Mapping from original buffers to their corresponding adjoint buffers.
  DenseMap<SILValue, ValueWithCleanup> bufferMap;

  /// Mapping from original basic blocks to their corresponding adjoint basic
  /// blocks.
  DenseMap<SILBasicBlock *, SILBasicBlock *> adjointBBMap;

  /// Local stack allocations.
  SmallVector<AllocStackInst *, 8> localAllocations;

  /// The primal value aggregate passed to the adjoint function.
  SILArgument *primalValueAggregateInAdj = nullptr;

  /// The seed argument in the adjoint function.
  SILArgument *seed = nullptr;

  /// The main builder.
  SILBuilder builder;

  llvm::BumpPtrAllocator allocator;

  bool errorOccurred = false;

  ADContext &getContext() const { return adjointGen.context; }

  SILModule &getModule() const { return getContext().getModule(); }

  ASTContext &getASTContext() const {
    return synthesis.target->getASTContext();
  }

  PrimalInfo &getPrimalInfo() const {
    return *getDifferentiationTask()->getPrimalInfo();
  }

  SILFunction &getOriginal() const { return *synthesis.original; }
  SILFunction &getAdjoint() const { return *synthesis.target; }

  DifferentiationTask *getDifferentiationTask() const { return synthesis.task; }

public:
  explicit AdjointEmitter(const FunctionSynthesisItem &item,
                          DifferentiableActivityInfo &activityInfo,
                          PostDominanceInfo &postDomInfo,
                          AdjointGen &adjointGen)
      : synthesis(item), activityInfo(activityInfo), postDomInfo(postDomInfo),
        adjointGen(adjointGen), builder(getAdjoint()) {}

private:
  //--------------------------------------------------------------------------//
  // Managed value factory methods
  //--------------------------------------------------------------------------//

  Cleanup *makeCleanup(SILValue value, Cleanup::Func func,
                       ArrayRef<Cleanup *> children = {});

  Cleanup *makeCleanupFromChildren(ArrayRef<Cleanup *> children);

  AdjointValue makeZeroAdjointValue(SILType type);

  AdjointValue makeConcreteAdjointValue(SILValue value);

  AdjointValue makeConcreteAdjointValue(ValueWithCleanup value);

  template<typename EltMoveRange>
  AdjointValue makeAggregateAdjointValue(SILType type, EltMoveRange &&elements);

  //--------------------------------------------------------------------------//
  // Managed value materializers
  //--------------------------------------------------------------------------//

  /// Materialize an adjoint value. The type of the given adjoint value must be
  /// loadable.
  ValueWithCleanup materializeAdjointDirect(AdjointValue &&val,
                                            SILLocation loc);

  /// Materialize an adjoint value indirectly to a SIL buffer.
  void materializeAdjointIndirect(
      AdjointValue &&val, ValueWithCleanup &destBuffer);

  /// Materialize the given adjoint value indirectly to the specified buffer.
  /// The root address derivation of `seedBufAccess` must be the result of
  /// a `begin_access`.
  void materializeAdjointIndirectHelper(
      AdjointValue &&val, ValueWithCleanup &destBufferAccess);

  //--------------------------------------------------------------------------//
  // Helpers for managed value materializers
  //--------------------------------------------------------------------------//

  /// Emit a zero value by calling `AdditiveArithmetic.zero`. The given type
  /// must conform to `AdditiveArithmetic`.
  void emitZeroIndirect(CanType type, SILValue bufferAccess, SILLocation loc);

  /// Emit a zero value by calling `AdditiveArithmetic.zero`. The given type
  /// must conform to `AdditiveArithmetic` and is loadable in SIL.
  SILValue emitZeroDirect(CanType type, SILLocation loc);

  //--------------------------------------------------------------------------//
  // Accumulator
  //--------------------------------------------------------------------------//

  /// Materialize an adjoint value in the most efficient way.
  ValueWithCleanup materializeAdjoint(AdjointValue &&val, SILLocation loc);

  /// Given two adjoint values, accumulate them.
  AdjointValue accumulateAdjointsDirect(AdjointValue &&lhs, AdjointValue &&rhs);

  /// Given two materialized adjoint values, accumulate them. These two
  /// adjoints must be objects of loadable type.
  SILValue accumulateDirect(SILValue lhs, SILValue rhs);

  /// Given two materialized adjoint values, accumulate them using
  /// `AdditiveArithmetic.+`, depending on the differentiation mode.
  void accumulateIndirect(SILValue resultBufAccess,
                          SILValue lhsBufAccess, SILValue rhsBufAccess);

  /// Given two buffers of an `AdditiveArithmetic` type, accumulate the right
  /// hand side into the left hand side using `+=`.
  void accumulateIndirect(SILValue lhsDestAccess, SILValue rhsAccess);

  //--------------------------------------------------------------------------//
  // Type transformer
  //--------------------------------------------------------------------------//

  /// Remap any archetypes into the current function's context.
  SILType remapType(SILType ty) {
    if (!ty.hasArchetype())
      return ty;
    auto *adjointGenEnv = getAdjoint().getGenericEnvironment();
    if (!adjointGenEnv)
      return ty;
    return ty.subst(getAdjoint().getModule(),
                    adjointGenEnv->getForwardingSubstitutionMap());
  }

  //--------------------------------------------------------------------------//
  // Managed value mapping
  //--------------------------------------------------------------------------//

  /// Returns true if the original value has a corresponding adjoint value.
  bool hasAdjointValue(SILValue originalValue) const {
    assert(originalValue->getType().isObject());
    return valueMap.count(originalValue);
  }

  /// Initializes an original value's corresponding adjoint value. Its adjoint
  /// value must not be present before this function is called.
  void initializeAdjointValue(SILValue originalValue,
                              AdjointValue &&adjointValue) {
    auto insertion =
        valueMap.try_emplace(originalValue, std::move(adjointValue));
    assert(insertion.second && "Adjoint value inserted before");
  }

  /// Get the adjoint for an original value. The given value must be in the
  /// original function.
  ///
  /// This method first tries to find an entry in `adjointMap`. If an adjoint
  /// doesn't exist, create a zero adjoint.
  AdjointValue takeAdjointValue(SILValue originalValue) {
    // assert(originalValue->getType().isObject());
    assert(originalValue->getFunction() == &getOriginal());
    auto insertion = valueMap.try_emplace(
        originalValue, makeZeroAdjointValue(
            getCotangentType(originalValue->getType(), getModule())));
    auto it = insertion.first;
    SWIFT_DEFER { valueMap.erase(it); };
    return std::move(it->getSecond());
  }

  /// Add an adjoint value for the given original value.
  void addAdjointValue(SILValue originalValue, AdjointValue &&newAdjointValue) {
    // assert(originalValue->getType().isObject());
    assert(newAdjointValue.getType().isObject());
    assert(originalValue->getFunction() == &getOriginal());
    LLVM_DEBUG(getADDebugStream() << "Adding adjoint for " << originalValue);
#ifndef NDEBUG
    auto origTy = remapType(originalValue->getType()).getASTType();
    auto cotanSpace = origTy->getAutoDiffAssociatedVectorSpace(
        AutoDiffAssociatedVectorSpaceKind::Cotangent,
        LookUpConformanceInModule(getModule().getSwiftModule()));
    // The adjoint value must be in the cotangent space.
    if (newAdjointValue.getType().getASTType() != cotanSpace->getCanonicalType()) {
      llvm::errs() << "WE ARE DOOMED\n";
      newAdjointValue.getType().getASTType()->dump();
      cotanSpace->getCanonicalType()->dump();
    }
    assert(cotanSpace && newAdjointValue.getType().getASTType() ==
                             cotanSpace->getCanonicalType());
#endif
    auto insertion =
        valueMap.try_emplace(originalValue, std::move(newAdjointValue));
    auto inserted = insertion.second;
    if (inserted)
      return;
    // If adjoint already exists, accumulate the adjoint onto the existing
    // adjoint.
    auto it = insertion.first;
    auto &&existingValue = it->getSecond();
    valueMap.erase(it);
    initializeAdjointValue(originalValue,
        accumulateAdjointsDirect(std::move(existingValue),
                                 std::move(newAdjointValue)));
  }

  //--------------------------------------------------------------------------//
  // Buffer mapping
  //--------------------------------------------------------------------------//

  void setAdjointBuffer(SILValue originalBuffer,
                        ValueWithCleanup adjointBuffer) {
    assert(originalBuffer->getType().isAddress());
    auto insertion = bufferMap.try_emplace(originalBuffer, adjointBuffer);
    assert(insertion.second); (void)insertion;
  }

  ValueWithCleanup getAdjointBuffer(SILValue originalBuffer) {
    assert(originalBuffer->getType().isAddress());
    auto insertion = bufferMap.try_emplace(originalBuffer,
                                           ValueWithCleanup(SILValue()));
    if (!insertion.second) // not inserted
      return insertion.first->getSecond();
    auto *newBuf = builder.createAllocStack(originalBuffer.getLoc(),
        remapType(getCotangentType(originalBuffer->getType(), getModule())));
    auto *access = builder.createBeginAccess(newBuf->getLoc(), newBuf,
                                             SILAccessKind::Init,
                                             SILAccessEnforcement::Static,
                                             /*noNestedConflict*/ true,
                                             /*fromBuiltin*/ false);
    emitZeroIndirect(access->getType().getASTType(), access, access->getLoc());
    builder.createEndAccess(access->getLoc(), access, /*aborted*/ false);
    localAllocations.push_back(newBuf);
    return (insertion.first->getSecond() = ValueWithCleanup(newBuf, nullptr));
  }

  void addToAdjointBuffer(SILValue originalBuffer,
                          SILValue newValueBufferAccess) {
    assert(originalBuffer->getType().isAddress() &&
           newValueBufferAccess->getType().isAddress());
    auto buf = getAdjointBuffer(originalBuffer);
    auto *access = builder.createBeginAccess(
        newValueBufferAccess.getLoc(), buf, SILAccessKind::Modify,
        SILAccessEnforcement::Static, /*noNestedConflict*/ true,
        /*fromBuiltin*/ false);
    accumulateIndirect(access, newValueBufferAccess);
    builder.createEndAccess(access->getLoc(), access, /*aborted*/ false);
  }

  //--------------------------------------------------------------------------//
  // CFG mapping
  //--------------------------------------------------------------------------//

  SILBasicBlock *getAdjointBlock(SILBasicBlock *originalBlock) {
    return adjointBBMap.lookup(originalBlock);
  }

  //--------------------------------------------------------------------------//
  // Other utilities
  //--------------------------------------------------------------------------//
  
  bool shouldBeDifferentiated(SILInstruction *inst,
                              const SILAutoDiffIndices &indices) {
    if (llvm::any_of(inst->getResults(),
            [&](SILValue val) { return activityInfo.isActive(val, indices); }))
      return true;
    if (auto *ai = dyn_cast<ApplyInst>(inst))
      for (auto indRes : ai->getIndirectSILResults())
        if (activityInfo.isActive(indRes, indices))
          return true;
    if (inst->mayWriteToMemory())
      for (auto &op : inst->getAllOperands())
        if (activityInfo.isActive(op.get(), indices))
          return true;
    return false;
  }

  AdjointValue prepareSeedAdjoint() {
    auto *ret = cast<ReturnInst>(getOriginal().findReturnBB()->getTerminator());
    auto origRetLoc = ret->getOperand().getLoc();
    if (seed->getType().isReferenceCounted(getModule())) {
      auto *rvi = builder.createRetainValue(origRetLoc, seed,
                                            builder.getDefaultAtomicity());
      assert(rvi->getParent() == getAdjoint().getEntryBlock());
    }
    auto cleanupFn = [](SILBuilder &b, SILLocation loc, SILValue v) {
      LLVM_DEBUG(getADDebugStream() << "Cleaning up seed " << v << '\n');
      b.createReleaseValue(loc, v, b.getDefaultAtomicity());
    };
    return makeConcreteAdjointValue(
        ValueWithCleanup(seed, makeCleanup(seed, cleanupFn)));
  }

public:
  /// Performs adjoint synthesis on the empty adjoint function. Returns true if
  /// any error occurs.
  bool run() {
    auto &original = getOriginal();
    auto &adjoint = getAdjoint();
    auto adjLoc = getAdjoint().getLocation();
    auto *task = getDifferentiationTask();
    LLVM_DEBUG(getADDebugStream() << "Running AdjointGen on\n" << original);
    auto origTy = original.getLoweredFunctionType();
    // Create entry BB and arguments.
    auto *adjointEntry = adjoint.createBasicBlock();
    createEntryArguments(&adjoint);
    auto *origRet = getSingleReturn(&original);
    auto *origRetBB = origRet->getParent();
    adjointBBMap.insert({origRetBB, adjointEntry});
    SILFunctionConventions origConv(origTy, getModule());
    // The adjoint function has type (seed, pv) -> ([arg0], ..., [argn]).
    auto adjParamArgs = adjoint.getArgumentsWithoutIndirectResults();
    seed = adjParamArgs[0];
    primalValueAggregateInAdj = adjParamArgs[1];
/*
    // OLD: The adjoint function has type (seed, pv) -> ([arg0], ..., [argn]).
    // The adjoint function has type (seed, [indirect_results], pv) -> ([arg0], ..., [argn]).
    auto adjParamArgs = getAdjoint().getArgumentsWithoutIndirectResults();
    seed = adjParamArgs.front();
    // primalValueAggregateInAdj = adjParamArgs[1];
    primalValueAggregateInAdj = adjParamArgs.back();
*/

    // Assign adjoint to the return value.
    //   y = tuple (y0, ..., yn)
    //   return y
    //   adj[y] =
    //     if the source result is direct
    //     then tuple (0, ..., seed, ..., 0) where seed is at the direct
    //          result index corresponding to the source index
    //     else zeros
    SmallVector<SILValue, 8> formalResults;
    collectAllFormalResultsInTypeOrder(original, formalResults);
    auto srcIdx = task->getIndices().source;

    builder.setInsertionPoint(adjointEntry);
    initializeAdjointValue(formalResults[srcIdx], prepareSeedAdjoint());
    LLVM_DEBUG(getADDebugStream()
               << "Assigned seed " << *seed << " as the adjoint of "
               << formalResults[srcIdx]);

    // From the original exit, emit a reverse control flow graph and perform
    // differentiation in each block.
    // NOTE: For now we just assume single basic block.
    for (auto *bb : llvm::breadth_first(origRetBB)) {
      if (errorOccurred)
        break;
      auto indices = getDifferentiationTask()->getIndices();
      // Get the corresponding adjoint basic block.
      auto adjBB = getAdjointBlock(bb);
      builder.setInsertionPoint(adjBB);
      LLVM_DEBUG({
        auto &s = getADDebugStream()
            << "To differentiate or not to differentiate?\n";
        for (auto &inst : reversed(*bb)) {
          s << (shouldBeDifferentiated(&inst, indices) ? "[∂] " : "[ ] ")
            << inst;
        }
      });
      // Visit each instruction in reverse order.
      for (auto &inst : reversed(*bb)) {
        if (!shouldBeDifferentiated(&inst, indices))
          continue;
        // Differentiate instruction.
        visit(&inst);
        if (errorOccurred)
          return true;
      }
    }
    
    // If errors occurred, back out.
    if (errorOccurred)
      return true;

    // Place the builder at the adjoint block corresponding to the original
    // entry. This block is going to be our exit block and we emit a `return`
    // there.
    builder.setInsertionPoint(getAdjointBlock(original.getEntryBlock()));

    // This vector will contain all the materialized return elements.
    SmallVector<SILValue, 8> retElts;
    // auto origParams = original.getArgumentsWithoutIndirectResults();
    auto origParams = original.getArguments();
    auto origNumIndRes = origConv.getNumIndirectSILResults();
    // adjoint.dump();

    // Materializes the return element corresponding to the parameter
    // `parameterIndex` into the `retElts` vector.
    auto addRetElt = [&](unsigned parameterIndex) -> void {
      auto origParam = origParams[origNumIndRes + parameterIndex];
      llvm::errs() << "PARAM INDEX: " << parameterIndex << "\n";
      origParam->dump();
      if (origParam->getType().isObject()) {
        auto adjVal = takeAdjointValue(origParam);
        auto val = materializeAdjointDirect(std::move(adjVal), adjLoc);
        if (auto *cleanup = val.getCleanup()) {
          LLVM_DEBUG(getADDebugStream() << "Disabling cleanup for "
                     << val.getValue() << "for return\n");
          cleanup->disable();
          LLVM_DEBUG(getADDebugStream() << "Applying "
                     << cleanup->getNumChildren() << " child cleanups\n");
          cleanup->applyRecursively(builder, adjLoc);
        }
        retElts.push_back(val);
      }
      else {
        llvm::errs() << "NEED COPY ADDR HERE\n";
        // auto adjVal = getAdjoint
        // setAdjointBuffer
        // llvm_unreachable("Unimplemented: Handle indirect pullback results");
      }
    };
    // The original's self parameter, if present, is the last parameter. But we
    // want its cotangent, if present, to be the first return element.
    auto selfParamIndex = origParams.size() - 1;
    if (origTy->hasSelfParam() &&
        task->getIndices().isWrtParameter(selfParamIndex))
      addRetElt(selfParamIndex);
    // Add the non-self parameters that are differentiated with respect to.
    for (auto i : task->getIndices().parameters.set_bits()) {
      // Do not add the self parameter because we have already added it at the
      // beginning.
      if (origTy->hasSelfParam() && i == selfParamIndex)
        continue;
      addRetElt(i);
    }
    builder.createReturn(adjLoc, joinElements(retElts, builder, adjLoc));

    // For any temporary allocations, emit a deallocation in the right place.
    for (auto *alloc : reversed(localAllocations)) {
      auto useIt = alloc->use_begin();
      assert(useIt != alloc->use_end());
      SILBasicBlock *deallocationPoint = (useIt++)->getUser()->getParent();
      do {
        postDomInfo.findNearestCommonDominator(
            deallocationPoint, (useIt++)->getUser()->getParent());
      } while (useIt != alloc->use_end());
      builder.setInsertionPoint(deallocationPoint->getTerminator());
      builder.createDeallocStack(adjLoc, alloc);
    }

    LLVM_DEBUG(getADDebugStream() << "Generated adjoint\n" << adjoint);
    return errorOccurred;
  }

  void visit(SILInstruction *inst) {
    if (errorOccurred)
      return;

#ifndef NDEBUG
    auto beforeInsertion = std::prev(builder.getInsertionPoint());
#endif
    SILInstructionVisitor::visit(inst);
    LLVM_DEBUG({
      auto &s = getADDebugStream()
          << "AdjointEmitter visited:\n[ORIG]" << *inst;
      s << "[ADJ] Emitted:\n";
      auto afterInsertion = builder.getInsertionPoint();
      for (auto it = ++beforeInsertion; it != afterInsertion; ++it)
        s << *it;
    });
  }

  void visitSILInstruction(SILInstruction *inst) {
    LLVM_DEBUG(getADDebugStream()
               << "Unhandled instruction in adjoint emitter: " << *inst);
    getContext().emitNondifferentiabilityError(inst, getDifferentiationTask(),
        diag::autodiff_expression_is_not_differentiable);
    errorOccurred = true;
  }

  void visitApplyInst(ApplyInst *ai) {
    llvm::errs() << "HELLO VISITING APPLY INST\n";
    ai->dumpInContext();
    // Replace a call to a function with a call to its pullback.
    auto &nestedApplyActivities =
        getDifferentiationTask()->getNestedApplyActivities();
    auto applyInfoLookUp = nestedApplyActivities.find(ai);
    // If no NestedApplyActivity was found, then this task doesn't need to be
    // differentiated.
    if (applyInfoLookUp == nestedApplyActivities.end()) {
      // Must not be active.
      assert(
          !activityInfo.isActive(ai, getDifferentiationTask()->getIndices()));
      return;
    }
    llvm::errs() << "WE MADE IT HERE\n"; // this doesn't print
    auto applyInfo = applyInfoLookUp->getSecond();
    auto origTy = ai->getCallee()->getType().castTo<SILFunctionType>();
    SILFunctionConventions origConvs(origTy, getModule());

    // Get the pullback.
    auto *field = getPrimalInfo().lookUpPullbackDecl(ai);
    assert(field);
    auto loc = ai->getLoc();
    SILValue pullback = builder.createStructExtract(loc,
                                                    primalValueAggregateInAdj,
                                                    field);

    // Construct the pullback arguments.
    SmallVector<SILValue, 8> args;
    // auto av = takeAdjointValue(allResults[applyInfo.indices.source]);
    // auto av = takeAdjointValue(ai);

    // Extract all results from `ai`.
    SmallVector<SILValue, 8> origDirResults;
    extractAllElements(ai, builder, origDirResults);
    // Get all original results in type-defined order.
    SmallVector<SILValue, 8> origAllResults;
    collectAllActualResultsInTypeOrder(
        ai, origDirResults, ai->getIndirectSILResults(),
        origAllResults);
    auto av = takeAdjointValue(origAllResults[applyInfo.indices.source]);
    llvm::errs() << "ORIG ALL RESULTS! SOURCE " << applyInfo.indices.source << "\n";
    for (auto res : origAllResults) {
      res->dump();
    }
    llvm::errs() << "ORIG\n";
    ai->dump();
    ValueWithCleanup seedBuf(builder.createAllocStack(loc, av.getType()),
                             /*cleanup*/ nullptr);
    materializeAdjointIndirect(std::move(av), seedBuf);
    if (av.getType().isAddressOnly(getModule()))
      args.push_back(seedBuf);
    else {
      auto access = builder.createBeginAccess(
          loc, seedBuf, SILAccessKind::Read, SILAccessEnforcement::Static,
          /*noNestedConflict*/ true, /*fromBuiltin*/ false);
      SILValue seedEltAddr;
      if (auto tupleTy = av.getType().getAs<TupleType>())
        seedEltAddr = builder.createTupleElementAddr(
            loc, access, applyInfo.indices.source);
      else
        seedEltAddr = access;
      args.push_back(builder.createLoad(
          loc, seedEltAddr, getBufferLOQ(av.getSwiftType(), getAdjoint())));
      builder.createEndAccess(loc, access, /*aborted*/ false);
    }

    // Call the pullback.
    auto *pullbackCall = builder.createApply(ai->getLoc(), pullback,
                                             SubstitutionMap(), args,
                                             /*isNonThrowing*/ false);
    builder.createDeallocStack(loc, seedBuf);

    // Extract all results from `pullbackCall`.
    SmallVector<SILValue, 8> dirResults;
    extractAllElements(pullbackCall, builder, dirResults);
    // Get all results in type-defined order.
    SmallVector<SILValue, 8> allResults;
    collectAllActualResultsInTypeOrder(
        pullbackCall, dirResults, pullbackCall->getIndirectSILResults(),
        allResults);
    LLVM_DEBUG({
      auto &s = getADDebugStream();
      s << "All direct results of the nested pullback call: \n";
      llvm::for_each(dirResults, [&](SILValue v) { s << v; });
      s << "All indirect results of the nested pullback call: \n";
      llvm::for_each(pullbackCall->getIndirectSILResults(),
                     [&](SILValue v) { s << v; });
      s << "All results of the nested pullback call: \n";
      llvm::for_each(allResults, [&](SILValue v) { s << v; });
    });

    // Set adjoints for all original parameters.
    // auto originalParams = ai->getArgumentsWithoutIndirectResults();
    auto originalParams = ai->getArguments();
    auto origNumIndRes = ai->getNumIndirectResults();
    auto allResultsIt = allResults.begin();

    auto cleanupFn = [](SILBuilder &b, SILLocation l, SILValue v) {
      b.createReleaseValue(l, v, b.getDefaultAtomicity());
    };

    llvm::errs() << "ORIG ARGUMENTS (NUM INDIRECT RESULTS: " << origNumIndRes << ")\n";
    for (auto arg : originalParams) {
      arg->dump();
    }
    llvm::errs() << "PULLBACK RESULTS (NUM INDIRECT RESULTS: " << origNumIndRes << ")\n";
    pullbackCall->dumpInContext();
    for (auto res : allResults) {
      res->dump();
    }
    getAdjoint().dump();
    llvm::errs() << "PARAMETER INDICES:";
    for (unsigned i : applyInfo.indices.parameters.set_bits()) {
      llvm::errs() << " " << i;
    }
    llvm::errs() << "\n";

    // If the applied adjoint returns the adjoint of the original self
    // parameter, then it returns it first. Set the adjoint of the original
    // self parameter.
    // auto selfParamIndex = originalParams.size() - 1;
    // auto selfParamIndex = originalParams.size() - origConvs.getNumIndirectSILResults() - 1;
    auto selfParamIndex = originalParams.size() - origNumIndRes - 1;
    if (ai->hasSelfArgument() &&
        applyInfo.indices.isWrtParameter(selfParamIndex)) {
      auto cotanWrtSelf = *allResultsIt++;
      llvm::errs() << "VISIT APPLY INST, COTAN WRT SELF: \n";
      ai->getArgument(origNumIndRes + selfParamIndex)->dump();
      cotanWrtSelf->dump();
      addAdjointValue(ai->getArgument(origNumIndRes + selfParamIndex),
          makeConcreteAdjointValue(ValueWithCleanup(
              cotanWrtSelf,
              makeCleanup(cotanWrtSelf, cleanupFn, {seedBuf.getCleanup()}))));
    }
    // Set adjoints for the remaining non-self original parameters.
    for (unsigned i : applyInfo.indices.parameters.set_bits()) {
      // Do not set the adjoint of the original self parameter because we
      // already added it at the beginning.
      if (ai->hasSelfArgument() && i == selfParamIndex)
        continue;
      auto cotan = *allResultsIt++;
      llvm::errs() << "VISIT APPLY INST, COTAN: \n";
      ai->getArgument(origNumIndRes + i)->dump();
      cotan->dump();
      // if (ai->getArgument(origNumIndRes + i)->getType().isAddress())
      //   continue;
      addAdjointValue(ai->getArgument(origNumIndRes + i),
          makeConcreteAdjointValue(ValueWithCleanup(
              cotan, makeCleanup(cotan, cleanupFn, {seedBuf.getCleanup()}))));
    }
  }

  /// Handle `struct` instruction.
  ///   y = struct (x0, x1, x2, ...)
  ///   adj[x0] = struct_extract #0, adj[y]
  ///   adj[x1] = struct_extract #1, adj[y]
  ///   adj[x2] = struct_extract #2, adj[y]
  ///   ...
  void visitStructInst(StructInst *si) {
    auto *decl = si->getStructDecl();
    auto av = takeAdjointValue(si);
    switch (av.getKind()) {
    case AdjointValueKind::Zero:
      for (auto *field : decl->getStoredProperties()) {
        auto fv = si->getFieldValue(field);
        addAdjointValue(fv, makeZeroAdjointValue(
            getCotangentType(fv->getType(), getModule())));
      }
      break;
    case AdjointValueKind::Concrete: {
      // FIXME(SR-9602): If `CotangentVector` is not marked
      // `@_fieldwiseProductSpace`, call the VJP of the memberwise initializer.
      // auto adjY = av.getMaterializedValue();
      // for (auto *field : decl->getStoredProperties())
      //   addAdjointValue(si->getFieldValue(field),
      //                   builder.createStructExtract(loc, adjY, field));
      llvm_unreachable("Unhandled. Are you trying to differentiate a "
                       "memberwise initializer?");
    }
    case AdjointValueKind::Aggregate: {
      // FIXME(SR-9602): If `CotangentVector` is not marked
      // `@_fieldwiseProductSpace`, call the VJP of the memberwise initializer.
      // for (auto pair : llvm::zip(si->getElements(), av.getAggregateElements()))
      //   addAdjointValue(std::get<0>(pair), std::get<1>(pair));
      llvm_unreachable("Unhandled. Are you trying to differentiate a "
                       "memberwise initializer?");
    }
    }
  }

  void visitStructExtractInst(StructExtractInst *sei) {
    auto loc = sei->getLoc();
    auto &differentiationStrategies =
        getDifferentiationTask()->getStructExtractDifferentiationStrategies();
    auto strategy = differentiationStrategies.lookup(sei);
    switch (strategy) {
    case StructExtractDifferentiationStrategy::Inactive:
      assert(!activityInfo.isActive(sei, synthesis.indices));
      return;
    case StructExtractDifferentiationStrategy::Fieldwise: {
      // Compute adjoint as follows:
      //   y = struct_extract <key>, x
      //   adj[x] = struct (0, ..., key': adj[y], ..., 0)
      // where `key'` is the field in the cotangent space corresponding to
      // `key`.
      auto structTy = remapType(sei->getOperand()->getType()).getASTType();
      auto cotangentVectorTy = structTy->getAutoDiffAssociatedVectorSpace(
          AutoDiffAssociatedVectorSpaceKind::Cotangent,
          LookUpConformanceInModule(getModule().getSwiftModule()))
              ->getType()->getCanonicalType();
      assert(!getModule().Types.getTypeLowering(cotangentVectorTy)
                 .isAddressOnly());
      auto cotangentVectorSILTy =
          SILType::getPrimitiveObjectType(cotangentVectorTy);
      auto *cotangentVectorDecl =
          cotangentVectorTy->getStructOrBoundGenericStruct();
      assert(cotangentVectorDecl);
      // Find the corresponding field in the cotangent space.
      VarDecl *correspondingField = nullptr;
      // If the cotangent space is the original sapce, then it's the same field.
      if (cotangentVectorDecl == sei->getStructDecl())
        correspondingField = sei->getField();
      // Otherwise we just look it up by name.
      else {
        auto correspondingFieldLookup =
            cotangentVectorDecl->lookupDirect(sei->getField()->getName());
        assert(correspondingFieldLookup.size() == 1);
        correspondingField = cast<VarDecl>(correspondingFieldLookup.front());
      }
      // Compute adjoint.
      auto av = takeAdjointValue(sei);
      switch (av.getKind()) {
      case AdjointValueKind::Zero:
        addAdjointValue(sei->getOperand(),
                        makeZeroAdjointValue(cotangentVectorSILTy));
        break;
      case AdjointValueKind::Concrete:
      case AdjointValueKind::Aggregate: {
        SmallVector<AdjointValue, 8> eltVals;
        for (auto *field : cotangentVectorDecl->getStoredProperties()) {
          if (field == correspondingField)
            eltVals.push_back(av);
          else
            eltVals.push_back(makeZeroAdjointValue(
                SILType::getPrimitiveObjectType(
                    field->getType()->getCanonicalType())));
        }
        addAdjointValue(sei->getOperand(),
            makeAggregateAdjointValue(cotangentVectorSILTy, eltVals));
      }
      }
      return;
    }
    case StructExtractDifferentiationStrategy::Getter: {
      // Get the pullback.
      auto *pullbackField = getPrimalInfo().lookUpPullbackDecl(sei);
      assert(pullbackField);
      SILValue pullback = builder.createStructExtract(loc,
                                                      primalValueAggregateInAdj,
                                                      pullbackField);

      // Construct the pullback arguments.
      SmallVector<SILValue, 8> args;
      auto av = takeAdjointValue(sei);
      assert(av.getType().isObject());
      auto vector = materializeAdjointDirect(std::move(av), loc);
      args.push_back(vector);

      // Call the pullback.
      auto *pullbackCall = builder.createApply(loc, pullback, SubstitutionMap(),
                                               args, /*isNonThrowing*/ false);
      assert(!pullbackCall->hasIndirectResults());

      // Set adjoint for the `struct_extract` operand.
      addAdjointValue(sei->getOperand(),
          makeConcreteAdjointValue(
              ValueWithCleanup(pullbackCall, vector.getCleanup())));
      break;
    }
    }
  }

  /// Handle `tuple` instruction.
  ///   y = tuple (x0, x1, x2, ...)
  ///   adj[x0] = tuple_extract 0, adj[y]
  ///   ...
  void visitTupleInst(TupleInst *ti) {
    auto av = takeAdjointValue(ti);
    switch (av.getKind()) {
    case AdjointValueKind::Zero:
      for (auto eltVal : ti->getElements())
        addAdjointValue(eltVal, makeZeroAdjointValue(
            getCotangentType(eltVal->getType(), getModule())));
      break;
    case AdjointValueKind::Concrete: {
      auto val = av.getConcreteValue();
      for (auto i : range(ti->getNumOperands()))
        addAdjointValue(ti->getOperand(i),
            makeConcreteAdjointValue(ValueWithCleanup(
                builder.createTupleExtract(ti->getLoc(), val, i),
                val.getCleanup())));
      break;
    }
    case AdjointValueKind::Aggregate:
      for (auto i : range(ti->getElements().size()))
        addAdjointValue(ti->getElement(i), av.takeAggregateElement(i));
      break;
    }
  }

  /// Handle `tuple_extract` instruction.
  ///   y = tuple_extract <n>, x
  ///                      |--- n-th element
  ///   adj[x] = tuple (0, 0, ..., adj[y], ..., 0, 0)
  void visitTupleExtractInst(TupleExtractInst *tei) {
    auto *tupleTy = tei->getTupleType();
    auto tupleCotanTy = getCotangentType(tupleTy->getCanonicalType(),
                                         getModule());
    auto av = takeAdjointValue(tei);
    switch (av.getKind()) {
    case AdjointValueKind::Zero:
      addAdjointValue(tei->getOperand(),
                      makeZeroAdjointValue(tupleCotanTy));
      break;
    case AdjointValueKind::Aggregate:
    case AdjointValueKind::Concrete: {
      SmallVector<AdjointValue, 8> elements;
      for (unsigned i : range(tupleTy->getNumElements())) {
        if (tei->getFieldNo() == i)
          elements.push_back(av);
        else
          elements.push_back(makeZeroAdjointValue(
              getCotangentType(tupleTy->getElementType(i)->getCanonicalType(),
                               getModule())));
      }
      addAdjointValue(tei->getOperand(),
          makeAggregateAdjointValue(tupleCotanTy, elements));
      break;
    }
    }
  }

  // Handle `alloc_stack` instruction.
  //   Original: y = alloc_stack $T
  //    Adjoint: dealloc_stack adj[y]
  void visitAllocStackInst(AllocStackInst *asi) {
    auto adjBuf = getAdjointBuffer(asi);
    builder.createDeallocStack(asi->getLoc(), adjBuf);
  }

  // Handle `dealloc_stack` instruction.
  //   Original: dealloc_stack y
  //    Adjoint: adj[y] = alloc_stack $T.CotangentVector
  void visitDeallocStackInst(DeallocStackInst *dsi) {
    auto bufType =
        remapType(getCotangentType(dsi->getOperand()->getType(), getModule()));
    auto *adjBuf = builder.createAllocStack(dsi->getLoc(), bufType);
    auto *access = builder.createBeginAccess(dsi->getLoc(), adjBuf,
                                             SILAccessKind::Init,
                                             SILAccessEnforcement::Static,
                                             /*noNestedConflict*/ true,
                                             /*fromBuiltin*/ false);
    emitZeroIndirect(bufType.getASTType(), access, dsi->getLoc());
    builder.createEndAccess(dsi->getLoc(), access, /*aborted*/ false);
    setAdjointBuffer(dsi->getOperand(),
                     ValueWithCleanup(adjBuf, /*cleanup*/ nullptr));
  }

  // Handle `load` instruction.
  //   Original: y = load x
  //    Adjoint: adj[x] += adj[y]
  void visitLoadInst(LoadInst *li) {
    auto adjVal = materializeAdjointDirect(takeAdjointValue(li), li->getLoc());
    auto *buf = builder.createAllocStack(li->getLoc(), adjVal.getType());
    auto *initAccess = builder.createBeginAccess(
        li->getLoc(), buf, SILAccessKind::Init, SILAccessEnforcement::Static,
        /*noNestedConflict*/ true, /*fromBuiltin*/ false);
    builder.createStore(li->getLoc(), adjVal, initAccess,
        getBufferSOQ(buf->getType().getASTType(), getAdjoint()));
    builder.createEndAccess(li->getLoc(), initAccess, /*aborted*/ false);
    auto *readAccess = builder.createBeginAccess(
        li->getLoc(), buf, SILAccessKind::Read, SILAccessEnforcement::Static,
        /*noNestedConflict*/ true, /*fromBuiltin*/ false);
    addToAdjointBuffer(li->getOperand(), readAccess);
    builder.createEndAccess(li->getLoc(), readAccess, /*aborted*/ false);
    builder.createDeallocStack(li->getLoc(), buf);
  }

  // Handle `store` instruction.
  //   Original: store x to y
  //    Adjoint: adj[x] += load adj[y]; adj[y] = 0
  void visitStoreInst(StoreInst *si) {
    auto adjBuf = getAdjointBuffer(si->getDest());
    auto bufType = remapType(adjBuf.getType());
    auto adjVal = builder.createLoad(si->getLoc(), adjBuf,
        getBufferLOQ(bufType.getASTType(), getAdjoint()));
    addAdjointValue(si->getSrc(), makeConcreteAdjointValue(
        ValueWithCleanup(adjVal, adjBuf.getCleanup())));
    emitZeroIndirect(bufType.getASTType(), adjBuf, si->getLoc());
  }

  // Handle `copy_addr` instruction.
  //   Original: copy_addr x to y
  //    Adjoint: adj[x] += adj[y]; adj[y] = 0
  void visitCopyAddrInst(CopyAddrInst *cai) {
    auto adjDest = getAdjointBuffer(cai->getDest());
    // accumulateIndirect(<#SILValue lhsDestAccess#>, <#SILValue rhsAccess#>)
    // addToAdjointBuffer(<#SILValue originalBuffer#>, <#SILValue newValueBufferAccess#>)
    auto *readAccess = builder.createBeginAccess(
        cai->getLoc(), adjDest, SILAccessKind::Read, SILAccessEnforcement::Static,
        /*noNestedConflict*/ true, /*fromBuiltin*/ false);
    addToAdjointBuffer(cai->getSrc(), readAccess);
    builder.createEndAccess(cai->getLoc(), readAccess, /*aborted*/ false);
    auto destType = remapType(adjDest.getType());
    emitZeroIndirect(destType.getASTType(), adjDest, cai->getLoc());
    // materializeZeroIndirect(destType.getASTType(), adjDest, cai->getLoc());

    // auto bufType = remapType(adjDest->getType());
    // // builder.createLoad(<#SILLocation Loc#>, <#SILValue LV#>, <#LoadOwnershipQualifier Qualifier#>)
    // // auto adjVal = builder.createLoad(cai->getLoc(), adjBuf,
    // //     getBufferLOQ(bufType.getASTType(), getAdjoint()));
    // // addAdjointValue(cai->getSrc(), adjVal);
    // auto loc = cai->getLoc();
    // auto adjSrc = materializeAdjoint(getAdjointValue(cai->getSrc()), cai->getLoc());
    // auto *resultBuf = builder.createAllocStack(loc, bufType);
    // auto *resultBufAccess = builder.createBeginAccess(
    //     loc, resultBuf, SILAccessKind::Init, SILAccessEnforcement::Static,
    //     /*noNestedConflict*/ true, /*fromBuiltin*/ false);
    // auto *lhsBufReadAccess = builder.createBeginAccess(loc, adjDest,
    //     SILAccessKind::Read, SILAccessEnforcement::Static,
    //     /*noNestedConflict*/ true, /*fromBuiltin*/ false);
    // auto *rhsBufReadAccess = builder.createBeginAccess(loc, adjSrc,
    //     SILAccessKind::Read, SILAccessEnforcement::Static,
    //     /*noNestedConflict*/ true, /*fromBuiltin*/ false);
    // accumulateMaterializedAdjointsIndirect(lhsBufReadAccess, rhsBufReadAccess, resultBufAccess);
    // builder.createEndAccess(loc, resultBufAccess, /*aborted*/ false);
    // builder.createEndAccess(loc, rhsBufReadAccess, /*aborted*/ false);
    // builder.createEndAccess(loc, lhsBufReadAccess, /*aborted*/ false);
    // // builder.createCopyAddr(loc, resultBuf, adjDest, IsNotTake, IsNotInitialization);
    // builder.createCopyAddr(loc, resultBuf, adjSrc, IsNotTake, IsNotInitialization);
    // // Deallocate the temporary result buffer.
    // builder.createDeallocStack(loc, resultBuf);
    // materializeZeroIndirect(bufType.getASTType(), adjDest, cai->getLoc());
  }

  // Handle `begin_access` instruction.
  //   Original: y = begin_access x
  //    Adjoint: end_access adj[y]
  void visitBeginAccessInst(BeginAccessInst *bai) {
    // Check for non-differentiable writes.
    if (bai->getAccessKind() == SILAccessKind::Modify) {
      if (auto *gai = dyn_cast<GlobalAddrInst>(bai->getSource())) {
        getContext()
            .emitNondifferentiabilityError(bai, getDifferentiationTask(),
                diag::autodiff_cannot_differentiate_writes_to_global_variables);
        errorOccurred = true;
        return;
      }
      if (auto *pbi = dyn_cast<ProjectBoxInst>(bai->getSource())) {
        getContext()
            .emitNondifferentiabilityError(bai, getDifferentiationTask(),
                diag::autodiff_cannot_differentiate_writes_to_mutable_captures);
        errorOccurred = true;
        return;
      }
    }
    auto accessBuf = getAdjointBuffer(bai);
    builder.createEndAccess(bai->getLoc(), accessBuf, /*aborted*/ false);
  }

  // Handle `end_access` instruction.
  //   Original: end_access y, where y = begin_access x
  //    Adjoint: adj[y] = begin_access inverse(access_kind) adj[x]
  void visitEndAccessInst(EndAccessInst *eai) {
    auto adjBuf = getAdjointBuffer(eai->getSource());
    SILAccessKind kind;
    switch (eai->getBeginAccess()->getAccessKind()) {
    case SILAccessKind::Read: kind = SILAccessKind::Modify; break;
    case SILAccessKind::Modify: kind = SILAccessKind::Read; break;
    case SILAccessKind::Init: kind = SILAccessKind::Deinit; break;
    case SILAccessKind::Deinit: kind = SILAccessKind::Init; break;
    }
    auto adjAccess = builder.createBeginAccess(
        eai->getLoc(), adjBuf, kind, eai->getBeginAccess()->getEnforcement(),
        eai->getBeginAccess()->hasNoNestedConflict(),
        eai->getBeginAccess()->isFromBuiltin());
    setAdjointBuffer(eai->getOperand(),
                     ValueWithCleanup(adjAccess, adjBuf.getCleanup()));
  }

#define NOT_DIFFERENTIABLE(INST, DIAG) \
  void visit##INST##Inst(INST##Inst *inst) { \
    getContext().emitNondifferentiabilityError( \
        inst, getDifferentiationTask(), DIAG); \
    errorOccurred = true; \
    return; \
  }
#undef NOT_DIFFERENTIABLE

#define NO_ADJOINT(INST) \
  void visit##INST##Inst(INST##Inst *inst) {}
  NO_ADJOINT(Return)
  NO_ADJOINT(DebugValue)
  NO_ADJOINT(DebugValueAddr)
  NO_ADJOINT(RetainValue)
  NO_ADJOINT(RetainValueAddr)
  NO_ADJOINT(ReleaseValue)
  NO_ADJOINT(ReleaseValueAddr)
  NO_ADJOINT(StrongRetain)
  NO_ADJOINT(StrongRelease)
  NO_ADJOINT(UnownedRetain)
  NO_ADJOINT(UnownedRelease)
  NO_ADJOINT(StrongRetainUnowned)
  NO_ADJOINT(DestroyValue)
  NO_ADJOINT(DestroyAddr)
#undef NO_DERIVATIVE
};
} // end anonymous namespace

Cleanup *AdjointEmitter::makeCleanup(SILValue value, Cleanup::Func func,
                                     ArrayRef<Cleanup *> children) {
  SmallVector<Cleanup *, 2> nonnullChildren;
  for (auto *c : children)
    if (c) nonnullChildren.push_back(c);
  return Cleanup::create(allocator, value, func, nonnullChildren);
}

Cleanup *AdjointEmitter::makeCleanupFromChildren(ArrayRef<Cleanup *> children) {
  if (children.empty())
    return nullptr;
  if (children.size() == 1)
    return children.front();
  SmallSetVector<Cleanup *, 8> uniqued(children.begin(), children.end());
  return makeCleanup(SILValue(), /*func*/ nullptr, uniqued.getArrayRef());
}

AdjointValue AdjointEmitter::makeZeroAdjointValue(SILType type) {
  return AdjointValue::createZero(allocator, remapType(type));
}

AdjointValue
AdjointEmitter::makeConcreteAdjointValue(ValueWithCleanup value) {
  return AdjointValue::createConcrete(allocator, value);
}

template<typename EltMoveRange>
AdjointValue AdjointEmitter::makeAggregateAdjointValue(
    SILType type, EltMoveRange &&elements) {
  return AdjointValue::createAggregate(
      allocator, remapType(type), std::move(elements));
}

ValueWithCleanup AdjointEmitter::materializeAdjointDirect(
    AdjointValue &&val, SILLocation loc) {
  assert(val.getType().isObject());
  LLVM_DEBUG(getADDebugStream() <<
             "Materializing adjoints for " << val << '\n');
  switch (val.getKind()) {
  case AdjointValueKind::Zero: {
    auto zeroVal = emitZeroDirect(val.getSwiftType(), loc);
    return ValueWithCleanup(zeroVal, nullptr);
  }
  case AdjointValueKind::Aggregate: {
    SmallVector<SILValue, 8> elements;
    SmallVector<Cleanup *, 8> cleanups;
    for (auto i : range(val.getNumAggregateElements())) {
      auto eltVal = materializeAdjointDirect(val.takeAggregateElement(i), loc);
      elements.push_back(eltVal.getValue());
      cleanups.push_back(eltVal.getCleanup());
    }
    if (val.getType().is<TupleType>())
      return ValueWithCleanup(
          builder.createTuple(loc, val.getType(), elements),
                              makeCleanupFromChildren(cleanups));
    else {
      auto *adj = builder.createStruct(loc, val.getType(), elements);
      builder.createRetainValue(loc, adj, builder.getDefaultAtomicity());
      auto cleanupFn = [](SILBuilder &b, SILLocation l, SILValue v) {
        b.createReleaseValue(l, v, b.getDefaultAtomicity());
      };
      return ValueWithCleanup(adj, makeCleanup(adj, cleanupFn, cleanups));
    }
  }
  case AdjointValueKind::Concrete:
    return val.getConcreteValue();
  }
}

void AdjointEmitter::materializeAdjointIndirect(
    AdjointValue &&val, ValueWithCleanup &destBuffer) {
  ValueWithCleanup access(
      builder.createBeginAccess(
          destBuffer.getLoc(), destBuffer, SILAccessKind::Init,
          SILAccessEnforcement::Static, /*noNestedConflict*/ true,
          /*fromBuiltin*/ false),
          /*cleanup*/ nullptr);
  materializeAdjointIndirectHelper(std::move(val), access);
  destBuffer.setCleanup(access.getCleanup());
  builder.createEndAccess(access.getLoc(), access, /*aborted*/ false);
}

ValueWithCleanup AdjointEmitter::materializeAdjoint(AdjointValue &&val,
                                                    SILLocation loc) {
  if (val.isConcrete()) {
    LLVM_DEBUG(getADDebugStream()
        << "Materialzing adjoint: Value is concrete.\n");
    return val.getConcreteValue();
  }
  LLVM_DEBUG(getADDebugStream() <<
      "Materialzing adjoint: Value is non-concrete. Materializing directly.\n");
  return materializeAdjointDirect(std::move(val), loc);
}

void AdjointEmitter::materializeAdjointIndirectHelper(
    AdjointValue &&val, ValueWithCleanup &destBufferAccess) {
  auto loc = destBufferAccess.getLoc();
  /*
  llvm::errs() << "DEBUG LOC\n";
  loc.dump(getModule().getSourceManager());
  llvm::errs() << "\n";
  */
  auto soq = getBufferSOQ(val.getType().getASTType(), builder.getFunction());
  switch (val.getKind()) {
  /// Given a `%buf : *T, emit instructions that produce a zero or an aggregate
  /// of zeros of the expected type. When `T` conforms to
  /// `AdditiveArithmetic`, we emit a call to `AdditiveArithmetic.zero`. When
  /// `T` is a builtin float, we emit a `float_literal` instruction.
  /// Otherwise, we assert that `T` must be an aggregate where each element
  /// conforms to `AdditiveArithmetic` or is a builtin float. We expect to emit
  /// a zero for each element and use the appropriate aggregate constructor
  /// instruction (in this case, `tuple`) to produce a tuple. But currently,
  /// since we need indirect passing for aggregate instruction, we just use
  /// `tuple_element_addr` to get element buffers and write elements to them.
  case AdjointValueKind::Zero:
    if (auto tupleTy = val.getType().getAs<TupleType>()) {
      SmallVector<SILValue, 8> eltVals;
      for (unsigned i : range(tupleTy->getNumElements())) {
        auto eltAddr = builder.createTupleElementAddr(loc, destBufferAccess, i);
        emitZeroIndirect(tupleTy->getElementType(i)->getCanonicalType(),
                         eltAddr, loc);
      }
    } else {
      emitZeroIndirect(val.getSwiftType(), destBufferAccess, loc);
    }
    break;
  /// Given a `%buf : *(T0, T1, T2, ...)` or `%buf : *Struct` recursively emit
  /// instructions to materialize the symbolic tuple or struct, filling the
  /// buffer.
  case AdjointValueKind::Aggregate: {
    if (auto *tupTy = val.getSwiftType()->getAs<TupleType>()) {
      for (auto idx : range(val.getNumAggregateElements())) {
        auto eltTy = SILType::getPrimitiveAddressType(
            tupTy->getElementType(idx)->getCanonicalType());
        ValueWithCleanup eltBuf(
            builder.createTupleElementAddr(loc, destBufferAccess, idx, eltTy),
            /*cleanup*/ nullptr);
        materializeAdjointIndirectHelper(val.takeAggregateElement(idx), eltBuf);
        destBufferAccess.setCleanup(makeCleanupFromChildren(
            {destBufferAccess.getCleanup(), eltBuf.getCleanup()}));
      }
    } else if (auto *structDecl =
                   val.getSwiftType()->getStructOrBoundGenericStruct()) {
      auto fieldIt = structDecl->getStoredProperties().begin();
      for (unsigned i = 0; fieldIt != structDecl->getStoredProperties().end();
           ++fieldIt, ++i) {
        ValueWithCleanup eltBuf(
            builder.createStructElementAddr(loc, destBufferAccess, *fieldIt),
            /*cleanup*/ nullptr);
        materializeAdjointIndirectHelper(val.takeAggregateElement(i), eltBuf);
        destBufferAccess.setCleanup(makeCleanupFromChildren(
            {destBufferAccess.getCleanup(), eltBuf.getCleanup()}));
      }
    } else {
      llvm_unreachable("Not an aggregate type");
    }
    break;
  }
  /// Value is already materialized!
  case AdjointValueKind::Concrete:
    auto concreteVal = val.getConcreteValue();
    builder.createStore(loc, concreteVal, destBufferAccess, soq);
    destBufferAccess.setCleanup(makeCleanupFromChildren(
        {destBufferAccess.getCleanup(), concreteVal.getCleanup()}));
    break;
  }
}

void AdjointEmitter::emitZeroIndirect(CanType type, SILValue bufferAccess,
                                      SILLocation loc) {
  // Lookup `AdditiveArithmetic.zero.getter`.
  auto *additiveArithmeticProto =
      getASTContext().getProtocol(KnownProtocolKind::AdditiveArithmetic);
  auto initDeclLookup =
      additiveArithmeticProto->lookupDirect(getASTContext().Id_zero);
  auto *zeroDecl = cast<VarDecl>(initDeclLookup.front());
  assert(zeroDecl->isProtocolRequirement());
  auto *accessorDecl = zeroDecl->getAccessor(AccessorKind::Get);
  SILDeclRef accessorDeclRef(accessorDecl, SILDeclRef::Kind::Func);
  // auto *nomTypeDecl = type->getAnyNominal();
  // assert(nomTypeDecl);
  auto methodType =
      getContext().getTypeConverter().getConstantType(accessorDeclRef);
  // Lookup conformance to `AdditiveArithmetic`.
  auto *swiftMod = getModule().getSwiftModule();
  auto conf = swiftMod->lookupConformance(type, additiveArithmeticProto);
  assert(conf.hasValue() && "No conformance to AdditiveArithmetic?");
  ProtocolConformanceRef confRef(*conf);
  // %wm = witness_method ...
  auto *getter = builder.createWitnessMethod(loc, type, confRef,
                                             accessorDeclRef, methodType);
  // %metatype = metatype $T
  auto metatypeType = CanMetatypeType::get(type, MetatypeRepresentation::Thick);
  auto metatype = builder.createMetatype(
      loc, SILType::getPrimitiveObjectType(metatypeType));
  auto subMap = SubstitutionMap::getProtocolSubstitutions(
      additiveArithmeticProto, type, confRef);
  builder.createApply(loc, getter, subMap, {bufferAccess, metatype},
                      /*isNonThrowing*/ false);
}

SILValue AdjointEmitter::emitZeroDirect(CanType type, SILLocation loc) {
  auto silType = getModule().Types.getLoweredLoadableType(type);
  auto *buffer = builder.createAllocStack(loc, silType);
  auto *initAccess = builder.createBeginAccess(loc, buffer, SILAccessKind::Init,
                                               SILAccessEnforcement::Static,
                                               /*noNestedConflict*/ true,
                                               /*fromBuiltin*/ false);
  emitZeroIndirect(type, initAccess, loc);
  builder.createEndAccess(loc, initAccess, /*aborted*/ false);
  auto readAccess = builder.createBeginAccess(loc, buffer, SILAccessKind::Read,
                                     SILAccessEnforcement::Static,
                                     /*noNestedConflict*/ true,
                                     /*fromBuiltin*/ false);
  auto *loaded = builder.createLoad(loc, readAccess,
                                    getBufferLOQ(type, getAdjoint()));
  builder.createEndAccess(loc, readAccess, /*aborted*/ false);
  builder.createDeallocStack(loc, buffer);
  return loaded;
}


AdjointValue
AdjointEmitter::accumulateAdjointsDirect(AdjointValue &&lhs,
                                         AdjointValue &&rhs) {
  LLVM_DEBUG(getADDebugStream()
             << "Materializing adjoint directly.\nLHS: " << lhs
             << "\nRHS: " << rhs << '\n');

  switch (lhs.getKind()) {
  // x
  case AdjointValueKind::Concrete: {
    auto lhsVal = lhs.getConcreteValue();
    switch (rhs.getKind()) {
    // x + y
    case AdjointValueKind::Concrete: {
      auto rhsVal = rhs.getConcreteValue();
      return makeConcreteAdjointValue(ValueWithCleanup(
          accumulateDirect(lhsVal, rhsVal),
              makeCleanupFromChildren({lhsVal.getCleanup(),
                                       rhsVal.getCleanup()})));
    }
    // x + 0 => x
    case AdjointValueKind::Zero:
      return std::move(lhs);
    // x + (y, z) => (x.0 + y, x.1 + z)
    case AdjointValueKind::Aggregate:
      SmallVector<AdjointValue, 8> newElements;
      for (auto i : range(rhs.getNumAggregateElements())) {
        auto lhsElt = builder.createTupleExtract(lhsVal.getLoc(), lhsVal, i);
        auto rhsElt = rhs.takeAggregateElement(i);
        newElements.push_back(accumulateAdjointsDirect(
            makeConcreteAdjointValue(
                ValueWithCleanup(lhsElt, lhsVal.getCleanup())),
            std::move(rhsElt)));
      }
      return makeAggregateAdjointValue(lhsVal.getType(), newElements);
    }
  }
  // 0
  case AdjointValueKind::Zero:
    // 0 + x => x
    return std::move(rhs);
  // (x, y)
  case AdjointValueKind::Aggregate:
    switch (rhs.getKind()) {
    // (x, y) + z => (x + z.0, y + z.1)
    case AdjointValueKind::Concrete:
    // x + 0 => x
    case AdjointValueKind::Zero:
      return std::move(lhs);
    // (x, y) + (z, w) => (x + z, y + w)
    case AdjointValueKind::Aggregate: {
      SmallVector<AdjointValue, 8> newElements;
      for (auto i : range(lhs.getNumAggregateElements()))
        newElements.push_back(
            accumulateAdjointsDirect(lhs.takeAggregateElement(i),
                                     rhs.takeAggregateElement(i)));
      return makeAggregateAdjointValue(lhs.getType(), newElements);
    }
    }
  }
}

SILValue AdjointEmitter::accumulateDirect(SILValue lhs, SILValue rhs) {
  // TODO: Optimize for the case when lhs == rhs.
  LLVM_DEBUG(getADDebugStream() <<
             "Emitting adjoint accumulation for lhs: " << lhs <<
             " and rhs: " << rhs << "\n");
  assert(lhs->getType() == rhs->getType() && "Adjoints must have equal types!");
  assert(lhs->getType().isObject() && rhs->getType().isObject() &&
         "Adjoint types must be both object types!");
  auto adjointTy = lhs->getType();
  auto adjointASTTy = adjointTy.getASTType();
  auto loc = lhs.getLoc();
  auto *swiftMod = getModule().getSwiftModule();
  auto cotangentSpace = adjointASTTy->getAutoDiffAssociatedVectorSpace(
      AutoDiffAssociatedVectorSpaceKind::Cotangent,
      LookUpConformanceInModule(swiftMod));
  assert(cotangentSpace && "No tangent space for this type");
  switch (cotangentSpace->getKind()) {
  case VectorSpace::Kind::Vector: {
    // Allocate buffers for inputs and output.
    auto *resultBuf = builder.createAllocStack(loc, adjointTy);
    auto *lhsBuf = builder.createAllocStack(loc, adjointTy);
    auto *rhsBuf = builder.createAllocStack(loc, adjointTy);
    // Initialize input buffers.
    auto *lhsBufInitAccess = builder.createBeginAccess(
        loc, lhsBuf, SILAccessKind::Init, SILAccessEnforcement::Static,
        /*noNestedConflict*/ true, /*fromBuiltin*/ false);
    auto *rhsBufInitAccess = builder.createBeginAccess(
        loc, rhsBuf, SILAccessKind::Init, SILAccessEnforcement::Static,
        /*noNestedConflict*/ true, /*fromBuiltin*/ false);
    builder.createStore(loc, lhs, lhsBufInitAccess,
                        getBufferSOQ(adjointASTTy, getAdjoint()));
    builder.createStore(loc, rhs, rhsBufInitAccess,
                        getBufferSOQ(adjointASTTy, getAdjoint()));
    builder.createEndAccess(loc, lhsBufInitAccess, /*aborted*/ false);
    builder.createEndAccess(loc, rhsBufInitAccess, /*aborted*/ false);
    // Accumulate the adjoints.
    auto *resultBufAccess = builder.createBeginAccess(
        loc, resultBuf, SILAccessKind::Init, SILAccessEnforcement::Static,
        /*noNestedConflict*/ true, /*fromBuiltin*/ false);
    auto *lhsBufReadAccess = builder.createBeginAccess(loc, lhsBuf,
        SILAccessKind::Read, SILAccessEnforcement::Static,
        /*noNestedConflict*/ true, /*fromBuiltin*/ false);
    auto *rhsBufReadAccess = builder.createBeginAccess(loc, rhsBuf,
        SILAccessKind::Read, SILAccessEnforcement::Static,
        /*noNestedConflict*/ true, /*fromBuiltin*/ false);
    accumulateIndirect(resultBufAccess, lhsBufReadAccess, rhsBufReadAccess);
    builder.createEndAccess(loc, resultBufAccess, /*aborted*/ false);
    builder.createEndAccess(loc, rhsBufReadAccess, /*aborted*/ false);
    builder.createEndAccess(loc, lhsBufReadAccess, /*aborted*/ false);
    // Deallocate input buffers.
    builder.createDeallocStack(loc, rhsBuf);
    builder.createDeallocStack(loc, lhsBuf);
    // Load result.
    resultBufAccess = builder.createBeginAccess(loc, resultBuf,
        SILAccessKind::Read, SILAccessEnforcement::Static,
        /*noNestedConflict*/ true, /*fromBuiltin*/ false);
    auto val = builder.createLoad(loc, resultBufAccess,
        getBufferLOQ(lhs->getType().getASTType(), getAdjoint()));
    builder.createEndAccess(loc, resultBufAccess, /*aborted*/ false);
    // Deallocate result buffer.
    builder.createDeallocStack(loc, resultBuf);
    return val;
  }
  case VectorSpace::Kind::Tuple: {
    auto tupleType = cotangentSpace->getTuple();
    SmallVector<SILValue, 8> adjElements;
    for (unsigned i : range(tupleType->getNumElements())) {
      auto *eltLHS = builder.createTupleExtract(loc, lhs, i);
      auto *eltRHS = builder.createTupleExtract(loc, rhs, i);
      adjElements.push_back(accumulateDirect(eltLHS, eltRHS));
    }
    return builder.createTuple(loc, adjointTy, adjElements);
  }
  case VectorSpace::Kind::Function: {
    llvm_unreachable(
      "Unimplemented: Emit thunks for abstracting adjoint accumulation");
  }
  }
}

void AdjointEmitter::accumulateIndirect(
    SILValue resultBufAccess, SILValue lhsBufAccess, SILValue rhsBufAccess) {
  // TODO: Optimize for the case when lhs == rhs.
  assert(lhsBufAccess->getType() == rhsBufAccess->getType()
         && "Adjoints must have equal types!");
  assert(lhsBufAccess->getType().isAddress() &&
         rhsBufAccess->getType().isAddress()
         && "Adjoint types must be both address types!");
  auto loc = resultBufAccess.getLoc();
  auto adjointTy = lhsBufAccess->getType();
  auto adjointASTTy = adjointTy.getASTType();
  auto *swiftMod = getModule().getSwiftModule();
  auto cotangentSpace = adjointASTTy->getAutoDiffAssociatedVectorSpace(
      AutoDiffAssociatedVectorSpaceKind::Cotangent,
      LookUpConformanceInModule(swiftMod));
  assert(cotangentSpace && "No tangent space for this type");
  switch (cotangentSpace->getKind()) {
  case VectorSpace::Kind::Vector: {
    // auto *adjointDecl = cotangentSpace->getNominal();
    auto *proto = getContext().getAdditiveArithmeticProtocol();
    auto *combinerFuncDecl = getContext().getPlusDecl();
    // Call the combiner function and return.
    // auto confRef = *adjointParentModule->lookupConformance(adjointASTTy, proto);
    auto *adjointParentModule = getModule().getSwiftModule();
    auto confRef = *adjointParentModule->lookupConformance(adjointASTTy, proto);
    SILDeclRef declRef(combinerFuncDecl, SILDeclRef::Kind::Func);
    auto silFnTy = getContext().getTypeConverter().getConstantType(declRef);
    // %0 = witness_method @+
    auto witnessMethod = builder.createWitnessMethod(loc, adjointASTTy,
                                                     confRef, declRef, silFnTy);
    auto subMap =
        SubstitutionMap::getProtocolSubstitutions(proto, adjointASTTy, confRef);
    // %1 = metatype $T.Type
    auto metatypeType =
        CanMetatypeType::get(adjointASTTy, MetatypeRepresentation::Thick);
    auto metatypeSILType = SILType::getPrimitiveObjectType(metatypeType);
    auto metatype = builder.createMetatype(loc, metatypeSILType);
    // %2 = apply $0(%result, %new, %old, %1)
    builder.createApply(loc, witnessMethod, subMap,
                        {resultBufAccess, rhsBufAccess, lhsBufAccess, metatype},
                        /*isNonThrowing*/ false);
    return;
  }
  case VectorSpace::Kind::Tuple: {
    auto tupleType = cotangentSpace->getTuple();
    for (unsigned i : range(tupleType->getNumElements())) {
      auto *destAddr = builder.createTupleElementAddr(loc, resultBufAccess, i);
      auto *eltAddrLHS = builder.createTupleElementAddr(loc, lhsBufAccess, i);
      auto *eltAddrRHS = builder.createTupleElementAddr(loc, rhsBufAccess, i);
      accumulateIndirect(destAddr, eltAddrLHS, eltAddrRHS);
    }
    return;
  }
  case VectorSpace::Kind::Function: {
    llvm_unreachable(
        "Unimplemented: Emit thunks for abstracting adjoint accumulation");
  }
  }
}

void AdjointEmitter::accumulateIndirect(SILValue lhsDestAccess,
                                        SILValue rhsAccess) {
  assert(lhsDestAccess->getType().isAddress() &&
         rhsAccess->getType().isAddress());
  auto loc = lhsDestAccess.getLoc();
  auto type = lhsDestAccess->getType();
  auto astType = type.getASTType();
  auto *swiftMod = getModule().getSwiftModule();
  auto cotangentSpace = astType->getAutoDiffAssociatedVectorSpace(
      AutoDiffAssociatedVectorSpaceKind::Cotangent,
      LookUpConformanceInModule(swiftMod));
  assert(cotangentSpace && "No tangent space for this type");
  switch (cotangentSpace->getKind()) {
  case VectorSpace::Kind::Vector: {
    auto *proto = getContext().getAdditiveArithmeticProtocol();
    auto *accumulatorFuncDecl = getContext().getPlusEqualDecl();
    // Call the combiner function and return.
    auto confRef = *swiftMod->lookupConformance(astType, proto);
    SILDeclRef declRef(accumulatorFuncDecl, SILDeclRef::Kind::Func);
    auto silFnTy = getContext().getTypeConverter().getConstantType(declRef);
    // %0 = witness_method @+=
    auto witnessMethod =
        builder.createWitnessMethod(loc, astType, confRef, declRef, silFnTy);
    auto subMap =
        SubstitutionMap::getProtocolSubstitutions(proto, astType, confRef);
    // %1 = metatype $T.Type
    auto metatypeType =
        CanMetatypeType::get(astType, MetatypeRepresentation::Thick);
    auto metatypeSILType = SILType::getPrimitiveObjectType(metatypeType);
    auto metatype = builder.createMetatype(loc, metatypeSILType);
    // %2 = apply $0(%lhs, %rhs, %1)
    builder.createApply(loc, witnessMethod, subMap,
                        {lhsDestAccess, rhsAccess, metatype},
                        /*isNonThrowing*/ false);
    return;
  }
  case VectorSpace::Kind::Tuple: {
    auto tupleType = cotangentSpace->getTuple();
    for (unsigned i : range(tupleType->getNumElements())) {
      auto *destAddr = builder.createTupleElementAddr(loc, lhsDestAccess, i);
      auto *eltAddrRHS = builder.createTupleElementAddr(loc, rhsAccess, i);
      accumulateIndirect(destAddr, eltAddrRHS);
    }
    return;
  }
  case VectorSpace::Kind::Function: {
    llvm_unreachable(
        "Unimplemented: Emit thunks for abstracting adjoint accumulation");
  }
  }
}

bool AdjointGen::performSynthesis(FunctionSynthesisItem item) {
  LLVM_DEBUG(getADDebugStream() << "Performing adjoint synthesis for original "
             << item.original->getName() << " and its corresponding adjoint "
             << item.target->getName() << '\n');
  auto &passManager = context.getPassManager();
  auto *activityAnalysis =
      passManager.getAnalysis<DifferentiableActivityAnalysis>();
  auto *postDomAnalysis =
      passManager.getAnalysis<PostDominanceAnalysis>();
  // Generate primal code.
  AdjointEmitter emitter(item, *activityAnalysis->get(item.original),
                         *postDomAnalysis->get(item.original), *this);
  // Run the adjoint emitter.
  return emitter.run();
}

//===----------------------------------------------------------------------===//
// DifferentiationTask
//===----------------------------------------------------------------------===//

SILFunction *
ADContext::declareExternalAssociatedFunction(
    SILFunction *original, SILDifferentiableAttr *attr, StringRef name,
    AutoDiffAssociatedFunctionKind kind) {
  auto &module = getModule();
  auto &indices = attr->getIndices();
  auto originalTy = original->getLoweredFunctionType();
  auto originalLoc = original->getLocation();
  auto assocGenSig = getAssociatedFunctionGenericSignature(attr, original);
  auto assocFnTy = originalTy->getAutoDiffAssociatedFunctionType(
      indices.parameters, indices.source, /*differentiationOrder*/ 1, kind,
      module, LookUpConformanceInModule(module.getSwiftModule()), assocGenSig);
  SILOptFunctionBuilder fb(getTransform());
  // Create external function declaration.
  auto *assocFn = fb.createFunction(
      SILLinkage::PublicExternal, name, assocFnTy,
      /*genericEnv*/ nullptr, originalLoc, original->isBare(), IsNotTransparent,
      original->isSerialized(), original->isDynamicallyReplaceable());
  // NOTE: Setting debug scope is necessary to prevent crash in TFPartition.
  assocFn->setDebugScope(new (module) SILDebugScope(originalLoc, assocFn));
  return assocFn;
}

DifferentiationTask::DifferentiationTask(ADContext &context,
                                         SILFunction *original,
                                         SILDifferentiableAttr *&&attr,
                                         DifferentiationInvoker invoker)
    : context(context), original(original), attr(attr), invoker(invoker) {
  auto &module = context.getModule();
  // Try to look up JVP only if attribute specifies JVP name or if original
  // function is an external declaration. If JVP function can't be found,
  // create an external JVP reference.
  StringRef jvpName;
  if (attr->hasJVP()) {
    jvpName = attr->getJVPName();
  } else if (original->isExternalDeclaration()) {
    jvpName = original->getASTContext()
                  .getIdentifier("AD__" + original->getName().str() +
				 "__jvp_" + getIndices().mangle())
                  .str();
  }
  if (!jvpName.empty()) {
    jvp = module.lookUpFunction(jvpName);
    if (!jvp)
      jvp = context.declareExternalAssociatedFunction(
          original, attr, jvpName, AutoDiffAssociatedFunctionKind::JVP);
    attr->setJVPName(jvpName);
  }

  // Try to look up VJP only if attribute specifies VJP name or if original
  // function is an external declaration. If VJP function can't be found,
  // create an external VJP reference.
  StringRef vjpName;
  if (attr->hasVJP()) {
    vjpName = attr->getVJPName();
  } else if (original->isExternalDeclaration()) {
    vjpName = original->getASTContext()
                  .getIdentifier("AD__" + original->getName().str() +
				 "__vjp_" + getIndices().mangle())
                  .str();
  }
  if (!vjpName.empty()) {
    vjp = module.lookUpFunction(vjpName);
    if (!vjp)
      vjp = context.declareExternalAssociatedFunction(
          original, attr, vjpName, AutoDiffAssociatedFunctionKind::VJP);
    attr->setVJPName(vjpName);
  }

  if (!jvp)
    createJVP();

  if (vjp) {
    // If the VJP exists, then no synthesis is needed.
    primalSynthesisState = FunctionSynthesisState::NotNeeded;
    adjointSynthesisState = FunctionSynthesisState::NotNeeded;
    return;
  }

  primalSynthesisState = FunctionSynthesisState::Needed;
  adjointSynthesisState = FunctionSynthesisState::Needed;
  createEmptyPrimal();
  createEmptyAdjoint();
  createVJP();
}

void DifferentiationTask::createEmptyPrimal() {
  assert(primalSynthesisState == FunctionSynthesisState::Needed);
  assert(!primalInfo);
  assert(!primal);

  auto indices = getIndices();
  auto *original = getOriginal();
  auto primalName = original->getASTContext()
                        .getIdentifier("AD__" + original->getName().str() +
                                       "__primal_" + indices.mangle())
                        .str();
  auto primalGenericSig = getAssociatedFunctionGenericSignature(attr, original);
  auto *primalGenericEnv = primalGenericSig
      ? primalGenericSig->createGenericEnvironment()
      : nullptr;
  auto *primalValueStructDecl =
      context.createPrimalValueStruct(this, primalGenericSig);
  primalInfo = std::unique_ptr<PrimalInfo>(
      new PrimalInfo(primalValueStructDecl));
  auto pvType =
      primalValueStructDecl->getDeclaredInterfaceType()->getCanonicalType();
  auto origResults = original->getLoweredFunctionType()->getResults();
  SmallVector<SILResultInfo, 8> results;
  results.push_back({pvType, ResultConvention::Owned});
  results.append(origResults.begin(), origResults.end());
  // Create result info for checkpoints.
  auto originalTy = original->getLoweredFunctionType();
  auto primalTy = SILFunctionType::get(
      primalGenericSig, originalTy->getExtInfo(),
      originalTy->getCoroutineKind(), originalTy->getCalleeConvention(),
      originalTy->getParameters(), originalTy->getYields(), results,
      originalTy->getOptionalErrorResult(), context.getASTContext());
  SILOptFunctionBuilder fb(context.getTransform());
  // We set generated primal linkage to Hidden because generated primals are
  // never called cross-module in VJP mode: all cross-module calls to associated
  // functions call the VJP.
  auto linkage = SILLinkage::Hidden;
  primal = fb.createFunction(linkage, primalName, primalTy, primalGenericEnv,
                             original->getLocation(), original->isBare(),
                             IsNotTransparent, original->isSerialized(),
                             original->isDynamicallyReplaceable());
  primal->setUnqualifiedOwnership();
  primal->setDebugScope(new (context.getModule())
                            SILDebugScope(original->getLocation(), primal));
  LLVM_DEBUG(getADDebugStream() << "Primal function created \n"
                                << *primal << '\n');
}

void DifferentiationTask::createEmptyAdjoint() {
  assert(adjointSynthesisState == FunctionSynthesisState::Needed);
  assert(!adjoint);

  auto &module = context.getModule();
  auto *original = getOriginal();
  auto origTy = original->getLoweredFunctionType();
  auto lookupConformance = LookUpConformanceInModule(module.getSwiftModule());

  // RAII that pushes the original function's generic signature to
  // `module.Types` so that the calls `module.Types.getTypeLowering()` below
  // will know the original function's generic parameter types.
  Lowering::GenericContextScope genericContextScope(
      module.Types, origTy->getGenericSignature());

  // Given a type, returns its formal SIL parameter info.
  auto getFormalParameterInfo = [&](CanType type) -> SILParameterInfo {
    auto &typeLowering = module.Types.getTypeLowering(type);
    ParameterConvention conv;
    if (typeLowering.isFormallyPassedIndirectly())
      conv = ParameterConvention::Indirect_In_Guaranteed;
    else if (typeLowering.isTrivial())
      conv = ParameterConvention::Direct_Unowned;
    else
      conv = ParameterConvention::Direct_Guaranteed;
    return {type, conv};
  };
  // Given a type, returns its formal SIL result info.
  auto getFormalResultInfo = [&](CanType type) -> SILResultInfo {
    auto &typeLowering = module.Types.getTypeLowering(type);
    ResultConvention conv;
    if (typeLowering.isFormallyReturnedIndirectly())
      conv = ResultConvention::Indirect;
    else if (typeLowering.isTrivial())
      conv = ResultConvention::Unowned;
    else
      conv = ResultConvention::Owned;
    return {type, conv};
  };

  // Parameters of the adjoint are:
  // - a seed,
  // - a primal value struct,
  // - original results, and
  // - the original parameters.
  // Results of the adjoint are in the cotangent space of the original
  // parameters.
  SmallVector<SILParameterInfo, 8> adjParams;
  SmallVector<SILResultInfo, 8> adjResults;
  auto origParams = origTy->getParameters();

  // Add adjoint parameter for the seed.
  adjParams.push_back(getFormalParameterInfo(
      origTy->getResults()[getIndices().source]
          .getType()
          ->getAutoDiffAssociatedVectorSpace(
              AutoDiffAssociatedVectorSpaceKind::Cotangent, lookupConformance)
          ->getCanonicalType()));

  // Accept a primal value struct in the adjoint parameter list. This is the
  // pullback's closure context.
  auto pvType = getPrimalInfo()->getPrimalValueStruct()
      ->getDeclaredInterfaceType()->getCanonicalType();
  adjParams.push_back({pvType, ParameterConvention::Direct_Guaranteed});

  // Add adjoint result for the wrt self parameter, if it was requested.
  auto selfParamIndex = origParams.size() - 1;
  if (origTy->hasSelfParam() &&
      getIndices().isWrtParameter(selfParamIndex))
    adjResults.push_back(getFormalResultInfo(
        origParams[selfParamIndex]
            .getType()
            ->getAutoDiffAssociatedVectorSpace(
                AutoDiffAssociatedVectorSpaceKind::Cotangent, lookupConformance)
            ->getCanonicalType()));

  // Add adjoint results for the requested non-self wrt parameters.
  for (auto i : getIndices().parameters.set_bits()) {
    if (origTy->hasSelfParam() && i == selfParamIndex)
      continue;
    adjResults.push_back(getFormalResultInfo(
        origParams[i]
            .getType()
            ->getAutoDiffAssociatedVectorSpace(
                AutoDiffAssociatedVectorSpaceKind::Cotangent, lookupConformance)
            ->getCanonicalType()));
  }

  auto adjName = original->getASTContext()
                     .getIdentifier("AD__" + original->getName().str() +
                                    "__adjoint_" + getIndices().mangle())
                     .str();
  auto adjGenericSig = getAssociatedFunctionGenericSignature(attr, original);
  auto *adjGenericEnv = adjGenericSig
      ? adjGenericSig->createGenericEnvironment()
      : nullptr;
  auto adjType = SILFunctionType::get(
      adjGenericSig, origTy->getExtInfo(), origTy->getCoroutineKind(),
      origTy->getCalleeConvention(), adjParams, {}, adjResults, None,
      original->getASTContext());

  SILOptFunctionBuilder fb(context.getTransform());
  // We set generated adjoint linkage to Hidden because generated adjoints are
  // never called cross-module in VJP mode: all cross-module calls to associated
  // functions call the VJP.
  auto linkage = SILLinkage::Hidden;
  adjoint = fb.createFunction(linkage, adjName, adjType, adjGenericEnv,
                              original->getLocation(), original->isBare(),
                              IsNotTransparent, original->isSerialized(),
                              original->isDynamicallyReplaceable());
  adjoint->setUnqualifiedOwnership();
  adjoint->setDebugScope(new (module)
                             SILDebugScope(original->getLocation(), adjoint));
}

void DifferentiationTask::createJVP() {
  auto &module = context.getModule();
  auto originalTy = original->getLoweredFunctionType();

  // RAII that pushes the original function's generic signature to
  // `module.Types` so that the calls `module.Types.getTypeLowering()` below
  // will know the original function's generic parameter types.
  Lowering::GenericContextScope genericContextScope(
      module.Types, originalTy->getGenericSignature());

  // === Create an empty JVP. ===
  auto jvpName = original->getASTContext()
                     .getIdentifier("AD__" + original->getName().str() +
                                    "__jvp_" + getIndices().mangle())
                     .str();
  auto jvpGenericSig = getAssociatedFunctionGenericSignature(attr, original);
  auto *jvpGenericEnv = jvpGenericSig
      ? jvpGenericSig->createGenericEnvironment()
      : nullptr;
  auto jvpType = originalTy->getAutoDiffAssociatedFunctionType(
      getIndices().parameters, getIndices().source, 1,
      AutoDiffAssociatedFunctionKind::JVP, module,
      LookUpConformanceInModule(module.getSwiftModule()),
      jvpGenericSig);

  SILOptFunctionBuilder fb(context.getTransform());
  auto linkage = getAutoDiffFunctionLinkage(original->getLinkage());
  jvp = fb.createFunction(linkage, jvpName, jvpType, jvpGenericEnv,
                          original->getLocation(), original->isBare(),
                          IsNotTransparent, original->isSerialized(),
                          original->isDynamicallyReplaceable());
  jvp->setUnqualifiedOwnership();
  jvp->setDebugScope(new (module) SILDebugScope(original->getLocation(), jvp));
  attr->setJVPName(jvpName);

  // Create JVP entry BB and arguments.
  auto jvpConv = jvp->getConventions();
  auto *entry = jvp->createBasicBlock();
  createEntryArguments(jvp);
  // Return undef.
  SILBuilder builder(entry);
  auto loc = jvp->getLocation();
  builder.createReturn(
      loc, SILUndef::get(jvp->mapTypeIntoContext(jvpConv.getSILResultType()),
                         module));
}

void DifferentiationTask::createVJP() {
  assert(!vjp);
  assert(adjoint);
  assert(primal);

  LLVM_DEBUG(llvm::dbgs() << "Creating VJP:\n"
                          << "  original type: "
                          << original->getLoweredFunctionType() << "\n"
                          << "  primal type: "
                          << primal->getLoweredFunctionType() << "\n"
                          << "  adjoint type: "
                          << adjoint->getLoweredFunctionType() << "\n");

  auto &module = context.getModule();
  auto originalTy = original->getLoweredFunctionType();

  // RAII that pushes the original function's generic signature to
  // `module.Types` so that the calls `module.Types.getTypeLowering()` below
  // will know the original function's generic parameter types.
  Lowering::GenericContextScope genericContextScope(
      module.Types, originalTy->getGenericSignature());

  // === Create an empty VJP. ===
  auto vjpName = original->getASTContext()
                     .getIdentifier("AD__" + original->getName().str() +
                                    "__vjp_" + getIndices().mangle())
                     .str();
  auto vjpGenericSig = getAssociatedFunctionGenericSignature(attr, original);
  auto *vjpGenericEnv = vjpGenericSig
      ? vjpGenericSig->createGenericEnvironment()
      : nullptr;
  auto vjpType = originalTy->getAutoDiffAssociatedFunctionType(
      getIndices().parameters, getIndices().source, 1,
      AutoDiffAssociatedFunctionKind::VJP, module,
      LookUpConformanceInModule(module.getSwiftModule()), vjpGenericSig);

  SILOptFunctionBuilder fb(context.getTransform());
  auto linkage = getAutoDiffFunctionLinkage(original->getLinkage());
  vjp = fb.createFunction(linkage, vjpName, vjpType, vjpGenericEnv,
                          original->getLocation(), original->isBare(),
                          IsNotTransparent, original->isSerialized(),
                          original->isDynamicallyReplaceable());
  vjp->setUnqualifiedOwnership();
  vjp->setDebugScope(new (module) SILDebugScope(original->getLocation(), vjp));
  attr->setVJPName(vjpName);

  LLVM_DEBUG(llvm::dbgs() << "  vjp type: "
                          << vjp->getLoweredFunctionType() << "\n");

  // We'll use these conventions frequently.
  auto originalConv = original->getConventions();
  auto primalConv = primal->getConventions();
  auto vjpConv = vjp->getConventions();

  // Keep track of some stack allocation to clean up.
  SmallVector<SILValue, 2> stackAllocsToCleanUp;

  // Validate signatures.
#ifndef NDEBUG
  auto adjointConv = adjoint->getConventions();

  unsigned numOriginalParameters = originalConv.getNumParameters();
  unsigned numOriginalResults = originalConv.getResults().size();
  unsigned numCheckpoints = primalConv.getResults().size() - numOriginalResults;
  unsigned numSeeds = 1;

  LLVM_DEBUG(llvm::dbgs() << "  numOriginalParameters: "
                          << numOriginalParameters << "\n"
                          << "  numOriginalResults: "
                          << numOriginalResults << "\n"
                          << "  numCheckpoints: "
                          << numCheckpoints << "\n"
                          << "  numSeeds: "
                          << numSeeds << "\n");

  assert(primalConv.getNumParameters() == numOriginalParameters &&
         "unexpected number of primal parameters");
  assert(vjpConv.getNumParameters() == numOriginalParameters &&
         "unexpected number of vjp parameters");
  assert(vjpConv.getResults().size() == numOriginalResults + 1 &&
         "unexpected number of vjp results");
  assert(adjointConv.getResults().size() == getIndices().parameters.count() &&
         "unexpected number of adjoint results");

  // We assume that primal result conventions (for all results but the optional
  // checkpoints struct) match the vjp result conventions (for all results but
  // the pullback), so check that assumption.
  for (unsigned resultIndex : range(numOriginalResults)) {
    auto &primalResultInfo =
        primalConv.getResults()[numCheckpoints + resultIndex];
    auto &vjpResultInfo = vjpConv.getResults()[resultIndex];
    assert(primalResultInfo == vjpResultInfo &&
           "primal result info does not match vjp result info");
  }
#endif

  // Create VJP entry BB and arguments.
  auto *entry = vjp->createBasicBlock();
  createEntryArguments(vjp);

  SILBuilder builder(entry);
  auto loc = vjp->getLocation();

  // Call primal with original arguments.
  SmallVector<SILValue, 8> primalArgs;
  // Allocate space for indirect checkpoint results, and pass the addresses to
  // the primal.
  unsigned remainingIndirectCheckpointResults =
      primalConv.getNumIndirectSILResults() -
      originalConv.getNumIndirectSILResults();
  for (auto silType : primalConv.getIndirectSILResultTypes()) {
    if (remainingIndirectCheckpointResults == 0)
      break;
    auto type = vjp->mapTypeIntoContext(silType.getObjectType());
    auto resultBuf = builder.createAllocStack(loc, type);
    primalArgs.push_back(resultBuf);
    stackAllocsToCleanUp.push_back(resultBuf);
    --remainingIndirectCheckpointResults;
  }
  // Tell the primal to put its indirect results in the vjp indirect result
  // buffers. This assumes that the primal indirect results are exactly the vjp
  // indirect results, an assumption that we check in assertions above.
  for (auto indRes : vjp->getIndirectResults())
    primalArgs.push_back(indRes);
  // Add original parameters.
  for (auto arg : vjp->getArgumentsWithoutIndirectResults())
    primalArgs.push_back(arg);
  // Get and call the primal.
  auto *primalRef = builder.createFunctionRef(loc, primal);
  auto vjpSubstMap = vjpGenericEnv
      ? vjpGenericEnv->getForwardingSubstitutionMap()
      : vjp->getForwardingSubstitutionMap();
  auto *primalApply = builder.createApply(
      loc, primalRef, vjpSubstMap, primalArgs, /*isNonThrowing*/ false);

  // Clean up the stack allocations for primal application.
  for (auto alloc : reversed(stackAllocsToCleanUp))
    builder.createDeallocStack(loc, alloc);

  // Collect the primal's direct results to prepare for creating a pullback
  // and return original values and the pullback.
  SmallVector<SILValue, 8> primalDirectResults;
  extractAllElements(primalApply, builder, primalDirectResults);
  auto originalDirectResults = ArrayRef<SILValue>(primalDirectResults)
      .take_back(originalConv.getNumDirectSILResults());
  // Get and partially apply the adjoint.
  auto *adjointRef = builder.createFunctionRef(loc, adjoint);
  auto *adjointPartialApply = builder.createPartialApply(
      loc, adjointRef, vjpSubstMap, { primalDirectResults[0] },
      ParameterConvention::Direct_Guaranteed);

  // Return the direct results. Note that indirect results have already been
  // filled in by the application of the primal.
  SmallVector<SILValue, 8> directResults;
  directResults.append(originalDirectResults.begin(),
                       originalDirectResults.end());
  directResults.push_back(adjointPartialApply);
  builder.createReturn(loc, joinElements(directResults, builder, loc));

  LLVM_DEBUG(getADDebugStream() << "Generated VJP\n" << *vjp);
}

//===----------------------------------------------------------------------===//
// Differentiation pass implementation
//===----------------------------------------------------------------------===//

/// Given an `autodiff_function` instruction, find the corresponding
/// differential operator used in the AST. If no differential operator is found,
/// return nullptr.
static AutoDiffFunctionExpr *findDifferentialOperator(
    AutoDiffFunctionInst *inst) {
  return inst->getLoc().getAsASTNode<AutoDiffFunctionExpr>();
}

/// The automatic differentiation pass.
namespace {
class Differentiation : public SILModuleTransform {
public:
  Differentiation() : SILModuleTransform() {}
  void run() override;

private:
  bool processAutoDiffFunctionInst(AutoDiffFunctionInst *adfi,
                                   ADContext &context);
};
} // end anonymous namespace

bool Differentiation::processAutoDiffFunctionInst(AutoDiffFunctionInst *adfi,
                                                  ADContext &context) {
  if (adfi->getNumAssociatedFunctions() ==
      autodiff::getNumAutoDiffAssociatedFunctions(
          adfi->getDifferentiationOrder()))
    return false;
  assert(adfi->getNumAssociatedFunctions() == 0 &&
         "some functions are already filled in but not all of them");

  SILFunction *parent = adfi->getFunction();
  auto origFnOperand = adfi->getOriginalFunction();
  SILBuilder builder(adfi);
  auto loc = parent->getLocation();

  /*
  auto *fnRef = peerThroughFunctionConversions<FunctionRefInst>(origFnOperand);
  if (fnRef) {
    llvm::errs() << "FOUND FUNCTION REF!\n";
    fnRef->dumpInContext();
    SILAutoDiffIndices desiredIndices(0, adfi->getParameterIndices());
    auto *fn = fnRef->getReferencedFunction();
    if (fn->isThunk() == IsReabstractionThunk) {
      llvm::errs() << "FOUND THUNK " << (unsigned)fn->isThunk() << ", JACKPOT\n";
      desiredIndices.print(llvm::errs());
      // assert(false && "NO THUNKS PLEASE");
      // fn->dump();

      // TODO: Get the argument to rebastraction thunk, check if it has indirect passing, etc
      // QUESTIONS: What parameter indices to use for thunk input? What other arguments?
      // QUESTION: What are current parameter indices?
      // builder.createAutoDiffFunction(loc, <#const llvm::SmallBitVector &parameterIndices#>, <#unsigned int differentiationOrder#>, <#SILValue original#>)
    }
  }
  */

  SILAutoDiffIndices desiredIndices(0, adfi->getParameterIndices());
  SmallVector<SILValue, 2> assocFns;
  for (auto assocFnKind : {AutoDiffAssociatedFunctionKind::JVP,
                           AutoDiffAssociatedFunctionKind::VJP}) {
    auto getInvoker =
        [&](AutoDiffFunctionInst *inst) -> DifferentiationInvoker {
      if (auto *expr = findDifferentialOperator(inst))
        return expr;
      return inst;
    };
    auto invoker = getInvoker(adfi);
    auto assocFnAndIndices = emitAssociatedFunctionReference(
        context, builder, /*parentTask*/ nullptr, desiredIndices, assocFnKind,
        origFnOperand, invoker, [](DifferentiationTask *newTask) {});
    if (!assocFnAndIndices) {
      // Show an error at the operator, highlight the argument, and show a note
      // at the definition site of the argument.
      auto loc = invoker.getLocation();
      context.diagnose(loc, diag::autodiff_function_not_differentiable)
          .highlight(loc);
      return true;
    }
    assert(assocFnAndIndices->second == desiredIndices &&
           "FIXME: We could emit a thunk that converts the VJP to have the "
           "desired indices.");
    auto assocFn = assocFnAndIndices->first;
    if (assocFn->getType().isReferenceCounted(*getModule()))
      builder.createRetainValue(loc, assocFn, builder.getDefaultAtomicity());
    assocFns.push_back(assocFnAndIndices->first);
  }

  auto *newADFI = builder.createAutoDiffFunction(
      loc, adfi->getParameterIndices(), adfi->getDifferentiationOrder(),
      origFnOperand, assocFns);
  adfi->replaceAllUsesWith(newADFI);
  adfi->eraseFromParent();
  PM->invalidateAnalysis(parent, SILAnalysis::InvalidationKind::FunctionBody);
  return false;
}

/// AD pass entry.
void Differentiation::run() {
  auto &module = *getModule();
  auto &astCtx = module.getASTContext();
  debugDump(module);

  // Collect `[differentiable]` attributes and `autodiff_function` instructions
  // to process.
  SmallVector<std::pair<SILFunction *,
                        SILDifferentiableAttr *>, 8> diffAttrs;
  SmallVector<AutoDiffFunctionInst *, 16> autodiffInsts;
  // Handle all the instructions and attributes in the module that trigger
  // differentiation.
  for (SILFunction &f : module) {
    // If `f` has a `[differentiable]` attribute, it should become a
    // differentiation task.
    for (auto *diffAttr : f.getDifferentiableAttrs()) {
      diffAttrs.push_back({&f, diffAttr});
      continue;
    }
    for (SILBasicBlock &bb : f)
      for (SILInstruction &i : bb)
        if (auto *adfi = dyn_cast<AutoDiffFunctionInst>(&i))
          autodiffInsts.push_back(adfi);
  }

  // If nothing has triggered differentiation, there's nothing to do.
  if (diffAttrs.empty() && autodiffInsts.empty())
    return;

  // AD relies on stdlib (the Swift module). If it's not imported, it's an
  // internal error.
  if (!astCtx.getStdlibModule()) {
    astCtx.Diags.diagnose(SourceLoc(),
                          diag::autodiff_internal_swift_not_imported);
    return;
  }

  // A global differentiation context.
  ADContext context(*this);

  // For every `[differentiable]` attribute, create a differentiation task. If
  // the attribute has a primal and adjoint, this task will not synthesize
  // anything, but it's still needed as a lookup target.
  for (auto &fnAndAttr : diffAttrs) {
    context.registerDifferentiationTask(
        fnAndAttr.first, fnAndAttr.second->getIndices(),
        DifferentiationInvoker(fnAndAttr.second, fnAndAttr.first));
  }

  bool errorProcessingAutoDiffInsts = false;
  for (auto *adfi : autodiffInsts)
    errorProcessingAutoDiffInsts |= processAutoDiffFunctionInst(adfi, context);

  auto cleanUp = [&]() {
    for (auto &task : context.getDifferentiationTasks())
      context.clearTask(task.get());
  };

  // Run primal generation for newly created differentiation tasks. If any error
  // occurs, continue on the tasks that are still good.
  PrimalGen primalGen(context);
  bool primalGenError = primalGen.run();

  // Run adjoint generation for differentiation tasks. If any error occurs, back
  // out.
  AdjointGen adjointGen(context);
  if (adjointGen.run() || primalGenError) {
    cleanUp();
    return;
  }

  // If there was any error that occurred during `autodiff_function` instruction
  // processing, back out.
  if (errorProcessingAutoDiffInsts) {
    cleanUp();
    return;
  }

  LLVM_DEBUG(getADDebugStream() << "All differentiation finished\n");
}

//===----------------------------------------------------------------------===//
// Pass creation
//===----------------------------------------------------------------------===//

SILTransform *swift::createDifferentiation() {
  return new Differentiation;
}
