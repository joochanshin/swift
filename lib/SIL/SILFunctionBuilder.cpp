//===--- SILFunctionBuilder.cpp -------------------------------------------===//
//
// This source file is part of the Swift.org open source project
//
// Copyright (c) 2014 - 2018 Apple Inc. and the Swift project authors
// Licensed under Apache License v2.0 with Runtime Library Exception
//
// See https://swift.org/LICENSE.txt for license information
// See https://swift.org/CONTRIBUTORS.txt for the list of Swift project authors
//
//===----------------------------------------------------------------------===//

#include "swift/SIL/SILFunctionBuilder.h"

using namespace swift;

SILFunction *SILFunctionBuilder::getOrCreateFunction(
    SILLocation loc, StringRef name, SILLinkage linkage,
    CanSILFunctionType type, IsBare_t isBareSILFunction,
    IsTransparent_t isTransparent, IsSerialized_t isSerialized,
    ProfileCounter entryCount, IsThunk_t isThunk, SubclassScope subclassScope) {
  assert(!type->isNoEscape() && "Function decls always have escaping types.");
  if (auto fn = mod.lookUpFunction(name)) {
    assert(fn->getLoweredFunctionType() == type);
    assert(stripExternalFromLinkage(fn->getLinkage()) ==
           stripExternalFromLinkage(linkage));
    return fn;
  }

  auto fn = SILFunction::create(mod, linkage, name, type, nullptr, loc,
                                isBareSILFunction, isTransparent, isSerialized,
                                entryCount, isThunk, subclassScope);
  fn->setDebugScope(new (mod) SILDebugScope(loc, fn));
  return fn;
}

// SWIFT_ENABLE_TENSORFLOW
void
SILFunctionBuilder::addFunctionAttributes(SILFunction *F, SILDeclRef constant,
                                          DeclAttributes &Attrs, SILModule &M) {
  for (auto *A : Attrs.getAttributes<SemanticsAttr>())
    F->addSemanticsAttr(cast<SemanticsAttr>(A)->Value);

  // Propagate @_specialize.
  for (auto *A : Attrs.getAttributes<SpecializeAttr>()) {
    auto *SA = cast<SpecializeAttr>(A);
    auto kind =
        SA->getSpecializationKind() == SpecializeAttr::SpecializationKind::Full
            ? SILSpecializeAttr::SpecializationKind::Full
            : SILSpecializeAttr::SpecializationKind::Partial;
    F->addSpecializeAttr(SILSpecializeAttr::create(M, SA->getRequirements(),
                                                   SA->isExported(), kind));
  }

  if (auto *OA = Attrs.getAttribute<OptimizeAttr>()) {
    F->setOptimizationMode(OA->getMode());
  }

  // @_silgen_name and @_cdecl functions may be called from C code somewhere.
  if (Attrs.hasAttribute<SILGenNameAttr>() || Attrs.hasAttribute<CDeclAttr>())
    F->setHasCReferences(true);

  // SWIFT_ENABLE_TENSORFLOW
  // Don't propagate @differentiable attributes to default arg generator
  // functions.
  auto *decl = constant.getDecl();
  if (constant.kind != SILDeclRef::Kind::DefaultArgGenerator &&
      // !constant.isSetter() &&
      (!isa<AccessorDecl>(decl) || dyn_cast<AccessorDecl>(decl)->isGetter()) &&
      !constant.isThunk() &&
      !constant.autoDiffAssociatedFunctionIdentifier) {
    for (auto *A : Attrs.getAttributes<DifferentiableAttr>()) {
      auto *DA = cast<DifferentiableAttr>(A);
      llvm::errs() << "WOW ADD FUNCTION ATTRIBUTES, KIND " << (unsigned)constant.kind << "\n";
      A->print(llvm::errs());
      constant.dump();
      llvm::errs() << "\n";

      // The declaration (or its storage decl) has a @differentiable attribute, so
      // turn it into a SIL [differentiable] attribute with lowered associated
      // function names and lowered differentiation parameter indices.
      llvm::errs() << "NAME: " << F->getName() << "\n";
      llvm::errs() << "PRIMAL: " << DA->getPrimalFunction() << "\n";
      llvm::errs() << "ADJOINT: " << DA->getAdjointFunction() << "\n";
      llvm::errs() << "JVP: " << DA->getJVPFunction() << "\n";
      llvm::errs() << "VJP: " << DA->getVJPFunction() << "\n";
      // Either only adjoint is specified, or both primal and adjoint are
      // spcified.
      StringRef primName, adjName, jvpName, vjpName;
      bool hasPrimitiveAdjoint = false;
      if (auto *primFn = DA->getPrimalFunction())
        primName = M.allocateCopy(SILDeclRef(primFn).mangle());
        // primName = SILDeclRef(primFn).mangle();
        // primName = Builder.getOrCreateFunction(SILLocation(primFn, LocationKind), <#SILDeclRef constant#>, <#ForDefinition_t forDefinition#>)
        // primName = getOrCreateFunction(SILLocation(primFn), SILDeclRef(primFn), ForDefinition)->getName();
        // primName = M.getFunction(SILDeclRef(primFn), ForDefinition)->getName();
      if (auto *adjFn = DA->getAdjointFunction()) {
        // If the adjoint is specified but the primal is not, then we treat the
        // original as the primal.
        if (primName.empty())
          primName = F->getName();
          // primName = silOriginalFn->getName();
        // adjName = M.getFunction(SILDeclRef(adjointFn), ForDefinition)->getName();
        // adjName = M.lookUpFunction(SILDeclRef(adjointFn))->getName();
        // adjName = getOrCreateFunction(SILLocation(adjFn), SILDeclRef(adjFn), ForDefinition)->getName();
        adjName = M.allocateCopy(SILDeclRef(adjFn).mangle());
        hasPrimitiveAdjoint = true;
      } else {
        assert(primName.empty() && "Primal cannot be present if adjoint is not");
      }
      if (auto *jvpFn = DA->getJVPFunction())
        jvpName = M.allocateCopy(SILDeclRef(jvpFn).mangle());
        // jvpName = getOrCreateFunction(SILLocation(jvpFn), SILDeclRef(jvpFn), ForDefinition)->getName();
        // jvpName = M.lookUpFunction(SILDeclRef(jvpFn))->getName();
        // jvpName = M.getFunction(SILDeclRef(jvpFn), ForDefinition)->getName();
      if (auto *vjpFn = DA->getVJPFunction())
        vjpName = M.allocateCopy(SILDeclRef(vjpFn).mangle());
        // vjpName = getOrCreateFunction(SILLocation(vjpFn), SILDeclRef(vjpFn), ForDefinition)->getName();
        // vjpName = M.lookUpFunction(SILDeclRef(vjpFn))->getName();
        // vjpName = M.getFunction(SILDeclRef(vjpFn), ForDefinition)->getName();
      // Get lowered argument indices.
      // auto AFD = M.lookUpFunction(SILDeclRef(F));
      llvm::errs() << "TRYING TO GET ORIGINAL FUNCTION AST TYPE: " << DA->getParameterIndices() << "\n";
      F->getLoweredType().dump();
      F->getLoweredType().getASTType()->dump();
      decl->getInterfaceType()->castTo<AnyFunctionType>()->dump();
      // DA->getCheckedParameterIndices()->getLowered(<#AnyFunctionType *functionType#>)
      // llvm::errs() << "HELLO PARAM INDICES: " << DA->getCheckedParameterIndices()->getString() << "\n";
      /*
      AutoDiffParameterIndicesBuilder autoDiffParameterIndicesBuilder(decl->getInterfaceType()->castTo<AnyFunctionType>());
      auto uncheckedWrtParams = DA->getParameters();
      auto original = cast<FuncDecl>(decl);
      bool isProperty = isa<AccessorDecl>(original);
      bool isMethod = original->getImplicitSelfDecl() ? true : false;
      auto isInstanceMethod = original->isInstanceMember();

      if (uncheckedWrtParams.empty()) {
        if (isProperty)
          autoDiffParameterIndicesBuilder.setParameter(0);
        else {
          // If 'wrt:' is not specified, the wrt parameters are all the parameters
          // in the main parameter group. Self is intentionally excluded except when
          // it's a property.
          unsigned numNonSelfParameters = autoDiffParameterIndicesBuilder.size() -
          (isMethod ? 1 : 0);
          for (unsigned i : range(numNonSelfParameters))
            autoDiffParameterIndicesBuilder.setParameter(i);
        }
      } else {
        // 'wrt:' is specified. Validate and collect the selected parameters.
        int lastIndex = -1;
        for (size_t i = 0; i < uncheckedWrtParams.size(); i++) {
          auto paramLoc = uncheckedWrtParams[i].getLoc();
          switch (uncheckedWrtParams[i].getKind()) {
            case AutoDiffParameter::Kind::Index: {
              unsigned index = uncheckedWrtParams[i].getIndex();
              if ((int)index <= lastIndex) {
                assert(false);
                return;
              }
              // // Parameter index cannot exceed bounds.
              // if (index >= originalParams.size()) {
              //   assert(false);
              //   return;
              // }
              autoDiffParameterIndicesBuilder.setParameter(index);
              lastIndex = index;
              break;
            }
            case AutoDiffParameter::Kind::Self: {
              // 'self' is only applicable to instance methods.
              if (!isInstanceMethod) {
                assert(false);
                return;
              }
              // 'self' can only be the first in the list.
              if (i > 0) {
                assert(false);
                return;
              }
              autoDiffParameterIndicesBuilder.setParameter(
                                                           autoDiffParameterIndicesBuilder.size() - 1);
              break;
            }
          }
        }
      }
      auto checkedParamIndices = autoDiffParameterIndicesBuilder.build(M.getASTContext());
       */
      auto paramIndices = DA->getParameterIndices();
      auto loweredIndices = paramIndices->getLowered(decl->getInterfaceType()->castTo<AnyFunctionType>());

      // auto paramIndices = DA->getCheckedParameterIndices()->getLowered(
      //     decl->getInterfaceType()->castTo<AnyFunctionType>());
          // F->getLoweredType().getASTType()->getAs<AnyFunctionType>());
          // AFD->getInterfaceType()->castTo<AnyFunctionType>());
      llvm::errs() << "HELLO 2\n";
      SILAutoDiffIndices indices(/*source*/ 0, loweredIndices);
      auto silDiffAttr = SILDifferentiableAttr::create(
          M, indices, DA->getRequirements(), primName, adjName,
          /*primitive*/ hasPrimitiveAdjoint, jvpName, vjpName);
      F->addDifferentiableAttr(silDiffAttr);
    }
  }
}

SILFunction *
SILFunctionBuilder::getOrCreateFunction(SILLocation loc, SILDeclRef constant,
                                        ForDefinition_t forDefinition,
                                        ProfileCounter entryCount) {
  auto nameTmp = constant.mangle();
  auto constantType = mod.Types.getConstantFunctionType(constant);
  SILLinkage linkage = constant.getLinkage(forDefinition);

  if (auto fn = mod.lookUpFunction(nameTmp)) {
    assert(fn->getLoweredFunctionType() == constantType);
    assert(fn->getLinkage() == linkage ||
           (forDefinition == ForDefinition_t::NotForDefinition &&
            fn->getLinkage() ==
                constant.getLinkage(ForDefinition_t::ForDefinition)));
    if (forDefinition) {
      // In all the cases where getConstantLinkage returns something
      // different for ForDefinition, it returns an available-externally
      // linkage.
      if (isAvailableExternally(fn->getLinkage())) {
        fn->setLinkage(constant.getLinkage(ForDefinition));
      }
    }
    return fn;
  }

  IsTransparent_t IsTrans =
      constant.isTransparent() ? IsTransparent : IsNotTransparent;
  IsSerialized_t IsSer = constant.isSerialized();

  EffectsKind EK = constant.hasEffectsAttribute()
                       ? constant.getEffectsAttribute()
                       : EffectsKind::Unspecified;

  Inline_t inlineStrategy = InlineDefault;
  if (constant.isNoinline())
    inlineStrategy = NoInline;
  else if (constant.isAlwaysInline())
    inlineStrategy = AlwaysInline;

  StringRef name = mod.allocateCopy(nameTmp);
  auto *F =
      SILFunction::create(mod, linkage, name, constantType, nullptr, None,
                          IsNotBare, IsTrans, IsSer, entryCount, IsNotThunk,
                          constant.getSubclassScope(), inlineStrategy, EK);
  F->setDebugScope(new (mod) SILDebugScope(loc, F));

  F->setGlobalInit(constant.isGlobal());
  if (constant.hasDecl()) {
    auto decl = constant.getDecl();

    if (constant.isForeign && decl->hasClangNode())
      F->setClangNodeOwner(decl);

    if (decl->isWeakImported(/*fromModule=*/nullptr))
      F->setWeakLinked();

    llvm::errs() << "HELLO DECL!\n";
    decl->dump();
    if (auto *accessor = dyn_cast<AccessorDecl>(decl)) {
      auto *storage = accessor->getStorage();
      // Add attributes for e.g. computed properties.
      llvm::errs() << "HELLO ACCESSOR!\n";
      accessor->dump();
      for (auto a : accessor->getAttrs().getAttributes<DifferentiableAttr>())
        a->print(llvm::errs());
      llvm::errs() << "HELLO STORAGE!\n";
      storage->dump();
      for (auto a : storage->getAttrs().getAttributes<DifferentiableAttr>())
        a->print(llvm::errs());
      addFunctionAttributes(F, constant, storage->getAttrs(), mod);
    }
    addFunctionAttributes(F, constant, decl->getAttrs(), mod);
  }

  return F;
}

SILFunction *SILFunctionBuilder::getOrCreateSharedFunction(
    SILLocation loc, StringRef name, CanSILFunctionType type,
    IsBare_t isBareSILFunction, IsTransparent_t isTransparent,
    IsSerialized_t isSerialized, ProfileCounter entryCount, IsThunk_t isThunk) {
  return getOrCreateFunction(loc, name, SILLinkage::Shared, type,
                             isBareSILFunction, isTransparent, isSerialized,
                             entryCount, isThunk, SubclassScope::NotApplicable);
}

SILFunction *SILFunctionBuilder::createFunction(
    SILLinkage linkage, StringRef name, CanSILFunctionType loweredType,
    GenericEnvironment *genericEnv, Optional<SILLocation> loc,
    IsBare_t isBareSILFunction, IsTransparent_t isTrans,
    IsSerialized_t isSerialized, ProfileCounter entryCount, IsThunk_t isThunk,
    SubclassScope subclassScope, Inline_t inlineStrategy, EffectsKind EK,
    SILFunction *InsertBefore, const SILDebugScope *DebugScope) {
  return SILFunction::create(mod, linkage, name, loweredType, genericEnv, loc,
                             isBareSILFunction, isTrans, isSerialized,
                             entryCount, isThunk, subclassScope, inlineStrategy,
                             EK, InsertBefore, DebugScope);
}
