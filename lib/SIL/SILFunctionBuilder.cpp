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
#include "swift/AST/Decl.h"
#include "swift/AST/Module.h"
using namespace swift;

SILFunction *SILFunctionBuilder::getOrCreateFunction(
    SILLocation loc, StringRef name, SILLinkage linkage,
    CanSILFunctionType type, IsBare_t isBareSILFunction,
    IsTransparent_t isTransparent, IsSerialized_t isSerialized,
    IsDynamicallyReplaceable_t isDynamic, ProfileCounter entryCount,
    IsThunk_t isThunk, SubclassScope subclassScope) {
  assert(!type->isNoEscape() && "Function decls always have escaping types.");
  if (auto fn = mod.lookUpFunction(name)) {
    assert(fn->getLoweredFunctionType() == type);
    assert(stripExternalFromLinkage(fn->getLinkage()) ==
           stripExternalFromLinkage(linkage));
    return fn;
  }

  auto fn = SILFunction::create(mod, linkage, name, type, nullptr, loc,
                                isBareSILFunction, isTransparent, isSerialized,
                                entryCount, isDynamic, isThunk, subclassScope);
  fn->setDebugScope(new (mod) SILDebugScope(loc, fn));
  return fn;
}


// SWIFT_ENABLE_TENSORFLOW
void SILFunctionBuilder::addFunctionAttributes(SILFunction *F,
                                               DeclAttributes &Attrs,
                                               SILModule &M,
                                               SILDeclRef constant,
                                               ForDefinition_t forDefinition) {

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

  // Propagate @_dynamicReplacement(for:).
  if (constant.isNull())
    return;
  auto *decl = constant.getDecl();

  // SWIFT_ENABLE_TENSORFLOW
  // Propagate @differentiable attributes.
  // Don't propagate @differentiable to:
  // - Non-getter accessors (setters, modifiers, etc).
  // - Default argument generator functions.
  // - Thunks. Those are currently handled in SILGenThunk.cpp.
  if ((!isa<AccessorDecl>(decl) || dyn_cast<AccessorDecl>(decl)->isGetter()) &&
      constant.kind != SILDeclRef::Kind::DefaultArgGenerator &&
      !constant.autoDiffFunctionIdentifier &&
      !constant.isThunk()) {
    for (auto *A : Attrs.getAttributes<DifferentiableAttr>()) {
      auto *DA = cast<DifferentiableAttr>(A);
      // bool isSameModule = M.getSwiftModule() == decl->getModuleContext();
      // bool isSameModule = M.getAssociatedContext() == decl->getModuleContext();
      bool isSameSILModule = M.lookUpFunction(constant);
      // bool isSameSILModule = M.lookUpFunction(constant) && !M.lookUpFunction(constant)->isExternalDeclaration();
      llvm::errs() << "CONSTANT: " << constant << ", SILMODULE " << &M << " CAN FIND CONSTANT? " << M.lookUpFunction(constant) << ", CONSTANT FOR DEFINITION? " << (forDefinition == ForDefinition) << "\n";
      DA->print(llvm::errs());
      if (auto origFn = M.lookUpFunction(constant)) {
        llvm::errs() << "FOUND FUNCTION: " << origFn->getName() << ", IS EXTERN DECLARATION? " << origFn->isExternalDeclaration() << "\n";
        if (origFn->getName() == "$s10TensorFlow0A0VAASjRzrlE4mean9alongAxesACyxGs5Int32Vd_tF") {
          llvm::errs() << "WE FOUND MEAN!\n";
          if (forDefinition == NotForDefinition) {
            auto test = rand() % 2;
            llvm::errs() << "Expectations subverted, random: " << test << "\n";
            if (test == 0)
              assert(false && "expected for definition");
            // M.dump();
          }
        }
      }
      // constant.getDecl()->getDeclContext()->dumpContext()
      // constant.dump();
      if (auto src = constant.getDecl()->getSourceFileName())
        llvm::errs() << "CONSTANT SOURCE FILE: " << *src << "\n";

      // M.dump();
      // decl->dump();
      // decl->getModuleContext()->dump();
      llvm::errs() << "IS SAME SIL MODULE? " << isSameSILModule << "\n";
      std::string jvpName, vjpName;
      // Get JVP/VJP names. If the functions aren't specified, use the expected
      // mangled name if . Differentiation pass ensures that JVP and VJP exist.
      if (auto *jvpFn = DA->getJVPFunction())
        jvpName = SILDeclRef(jvpFn).mangle();
      // else if (forDefinition == NotForDefinition)
      // // else if (forDefinition == NotForDefinition && !isSameSILModule)
      // // else if (!isSameSILModule)
      //   jvpName = constant.asAutoDiffAssociatedFunction(
      //       AutoDiffAssociatedFunctionIdentifier::get(
      //           AutoDiffAssociatedFunctionKind::JVP, /*differentiationOrder*/ 1,
      //           DA->getParameterIndices(), F->getASTContext())).mangle();
      if (auto *vjpFn = DA->getVJPFunction())
        vjpName = SILDeclRef(vjpFn).mangle();
      // else if (forDefinition == NotForDefinition && !isSameSILModule)
      // else if (forDefinition == NotForDefinition)
      // // else if (!isSameSILModule)
      //   vjpName = constant.asAutoDiffAssociatedFunction(
      //       AutoDiffAssociatedFunctionIdentifier::get(
      //           AutoDiffAssociatedFunctionKind::VJP, /*differentiationOrder*/ 1,
      //           DA->getParameterIndices(), F->getASTContext())).mangle();
      // Get lowered argument indices.
      auto paramIndices = DA->getParameterIndices();
      auto loweredIndices = paramIndices->getLowered(
          decl->getInterfaceType()->castTo<AnyFunctionType>());
      SILAutoDiffIndices indices(/*source*/ 0, loweredIndices);
      auto silDiffAttr = SILDifferentiableAttr::create(
          M, indices, DA->getRequirements(), M.allocateCopy(jvpName),
          M.allocateCopy(vjpName));
      F->addDifferentiableAttr(silDiffAttr);
    }
  }

  // Only emit replacements for the objc entry point of objc methods.
  if (decl->isObjC() &&
      F->getLoweredFunctionType()->getExtInfo().getRepresentation() !=
          SILFunctionTypeRepresentation::ObjCMethod)
    return;

  auto *replacedFuncAttr = Attrs.getAttribute<DynamicReplacementAttr>();
  if (!replacedFuncAttr)
    return;

  auto *replacedDecl = replacedFuncAttr->getReplacedFunction();
  assert(replacedDecl);

  if (decl->isObjC()) {
    F->setObjCReplacement(replacedDecl);
    return;
  }

  if (constant.isInitializerOrDestroyer())
    return;

  SILDeclRef declRef(replacedDecl, constant.kind, false);
  auto *replacedFunc =
      getOrCreateFunction(replacedDecl, declRef, NotForDefinition);
  assert(replacedFunc->getLoweredFunctionType() == F->getLoweredFunctionType());
  F->setDynamicallyReplacedFunction(replacedFunc);

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
  IsDynamicallyReplaceable_t IsDyn = IsNotDynamic;
  if (constant.isDynamicallyReplaceable()) {
    IsDyn = IsDynamic;
    IsTrans = IsNotTransparent;
  }

  auto *F = SILFunction::create(mod, linkage, name, constantType, nullptr, None,
                                IsNotBare, IsTrans, IsSer, entryCount, IsDyn,
                                IsNotThunk, constant.getSubclassScope(),
                                inlineStrategy, EK);
  F->setDebugScope(new (mod) SILDebugScope(loc, F));

  F->setGlobalInit(constant.isGlobal());
  if (constant.hasDecl()) {
    auto decl = constant.getDecl();

    if (constant.isForeign && decl->hasClangNode())
      F->setClangNodeOwner(decl);

    if (decl->isWeakImported(/*fromModule=*/nullptr))
      F->setWeakLinked();

    if (auto *accessor = dyn_cast<AccessorDecl>(decl)) {
      auto *storage = accessor->getStorage();
      // SWIFT_ENABLE_TENSORFLOW
      addFunctionAttributes(F, storage->getAttrs(), mod, constant,
                            forDefinition);
    }
    // SWIFT_ENABLE_TENSORFLOW
    addFunctionAttributes(F, decl->getAttrs(), mod, constant, forDefinition);
  }

  return F;
}

SILFunction *SILFunctionBuilder::getOrCreateSharedFunction(
    SILLocation loc, StringRef name, CanSILFunctionType type,
    IsBare_t isBareSILFunction, IsTransparent_t isTransparent,
    IsSerialized_t isSerialized, ProfileCounter entryCount, IsThunk_t isThunk,
    IsDynamicallyReplaceable_t isDynamic) {
  return getOrCreateFunction(loc, name, SILLinkage::Shared, type,
                             isBareSILFunction, isTransparent, isSerialized,
                             isDynamic, entryCount, isThunk,
                             SubclassScope::NotApplicable);
}

SILFunction *SILFunctionBuilder::createFunction(
    SILLinkage linkage, StringRef name, CanSILFunctionType loweredType,
    GenericEnvironment *genericEnv, Optional<SILLocation> loc,
    IsBare_t isBareSILFunction, IsTransparent_t isTrans,
    IsSerialized_t isSerialized, IsDynamicallyReplaceable_t isDynamic,
    ProfileCounter entryCount, IsThunk_t isThunk, SubclassScope subclassScope,
    Inline_t inlineStrategy, EffectsKind EK, SILFunction *InsertBefore,
    const SILDebugScope *DebugScope) {
  return SILFunction::create(mod, linkage, name, loweredType, genericEnv, loc,
                             isBareSILFunction, isTrans, isSerialized,
                             entryCount, isDynamic, isThunk, subclassScope,
                             inlineStrategy, EK, InsertBefore, DebugScope);
}
