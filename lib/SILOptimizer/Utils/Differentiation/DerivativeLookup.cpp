//===--- DerivativeLookup.cpp ---------------------------------------------===//
//
// This source file is part of the Swift.org open source project
//
// Copyright (c) 2019 Apple Inc. and the Swift project authors
// Licensed under Apache License v2.0 with Runtime Library Exception
//
// See https://swift.org/LICENSE.txt for license information
// See https://swift.org/CONTRIBUTORS.txt for the list of Swift project authors
//
//===----------------------------------------------------------------------===//
//
// SWIFT_ENABLE_TENSORFLOW
//
// Utilities for looking up derivatives of functions.
//
//===----------------------------------------------------------------------===//

#include "swift/SILOptimizer/Utils/Differentiation/DerivativeLookup.h"

// TODO: REMOVE
#include "swift/AST/GenericSignatureBuilder.h"

namespace swift {

/// Returns the AbstractFunctionDecl corresponding to `F`. If there isn't one,
/// returns `nullptr`.
static AbstractFunctionDecl *findAbstractFunctionDecl(SILFunction *F) {
  auto *DC = F->getDeclContext();
  if (!DC)
    return nullptr;
  auto *D = DC->getAsDecl();
  if (!D)
    return nullptr;
  return dyn_cast<AbstractFunctionDecl>(D);
}

SILDifferentiabilityWitness *
getExactDifferentiabilityWitness(SILModule &module, SILFunction *original,
                                 IndexSubset *parameterIndices,
                                 IndexSubset *resultIndices) {
  for (auto *w : module.lookUpDifferentiabilityWitnessesForFunction(
           original->getName())) {
    if (w->getParameterIndices() == parameterIndices &&
        w->getResultIndices() == resultIndices)
      return w;
  }
  return nullptr;
}

#if 0
// Returns the canonical generic signature for an autodiff derivative function
// given an existing derivative function generic signature. All differentiation
// parameters are constrained to conform to `Differentiable`.
static CanGenericSignature getAutoDiffDerivativeFunctionGenericSignature(
    GenericSignature derivativeFnGenSig, ModuleDecl *module) {
  if (!derivativeFnGenSig)
    return nullptr;
  auto &ctx = module->getASTContext();
  GenericSignatureBuilder builder(ctx);

  // Add derivative function generic signature.
  builder.addGenericSignature(derivativeFnGenSig);
  // Constrain all wrt parameters to conform to `Differentiable`.
  auto source =
      GenericSignatureBuilder::FloatingRequirementSource::forAbstract();
  auto *diffableProto = ctx.getProtocol(KnownProtocolKind::Differentiable);
  for (auto gpType : derivativeFnGenSig->getGenericParams()) {
    Requirement req(RequirementKind::Conformance, gpType,
                    diffableProto->getDeclaredType());
    builder.addRequirement(req, source, module);

    // TODO: Try adding `T == T.TangentVector`?
    Requirement req(RequirementKind::SameType, gpType,
                    diffableProto->getDeclaredType());
    builder.addRequirement(req, source, module);
  }
  return std::move(builder)
      .computeGenericSignature(SourceLoc(), /*allowConcreteGenericParams*/ true)
      ->getCanonicalSignature();
}
#endif

bool findMinimalDerivativeConfiguration(AbstractFunctionDecl *original,
                                        IndexSubset *parameterIndices,
                                        IndexSubset *&minimalASTParameterIndices,
                                        IndexSubset *&minimalSILParameterIndices,
                                        GenericSignature &derivativeGenericSignature) {
#if 0
  auto &ctx = original->getASTContext();
  DeclAttribute *minimalAttr = nullptr;
  minimalParameterIndices = nullptr;
  derivativeGenericSignature = GenericSignature();
  for (auto *attr : original->getAttrs().getAttributes<DifferentiableAttr>()) {
    auto *attrParameterIndices = autodiff::getLoweredParameterIndices(
        attr->getParameterIndices(),
        original->getInterfaceType()->castTo<AnyFunctionType>());
    // If all indices in `parameterIndices` are in `daParameterIndices`, and it
    // has fewer indices than our current candidate and a primitive VJP, then
    // `attr` is our new candidate.
    //
    // NOTE(TF-642): `attr` may come from a un-partial-applied function and
    // have larger capacity than the desired indices. We expect this logic to
    // go away when `partial_apply` supports `@differentiable` callees.
    if (attrParameterIndices->isSupersetOf(parameterIndices->extendingCapacity(
            original->getASTContext(), attrParameterIndices->getCapacity())) &&
        // fewer parameters than before
        (!minimalParameterIndices ||
         attrParameterIndices->getNumIndices() <
             minimalParameterIndices->getNumIndices())) {
      minimalAttr = const_cast<DifferentiableAttr *>(attr);
      minimalParameterIndices = attrParameterIndices;
      derivativeGenericSignature = attr->getDerivativeGenericSignature();
    }
  }
  if (minimalAttr)
    return minimalAttr;
#endif
  // TODO: Need minimal attributes
  auto results = original->getDerivativeFunctionConfigurations();
  llvm::errs() << "results: " << results.size() << "\n";
  // assert(results.size() == 0 && "Negative assertion to detect when things start working");
  for (auto config : results) {
    auto *paramIndices = config.parameterIndices;
    auto derivativeGenSig = config.derivativeGenericSignature;
    auto *silParameterIndices = autodiff::getLoweredParameterIndices(
        paramIndices, original->getInterfaceType()->castTo<AnyFunctionType>());
    // If all indices in `parameterIndices` are in `daParameterIndices`, and
    // it has fewer indices than our current candidate and a primitive VJP,
    // then `attr` is our new candidate.
    //
    // NOTE(TF-642): `attr` may come from a un-partial-applied function and
    // have larger capacity than the desired indices. We expect this logic to
    // go away when `partial_apply` supports `@differentiable` callees.
    if (silParameterIndices->isSupersetOf(
            parameterIndices->extendingCapacity(
                original->getASTContext(),
                silParameterIndices->getCapacity())) &&
        // fewer parameters than before
        (!minimalSILParameterIndices ||
         silParameterIndices->getNumIndices() <
             minimalSILParameterIndices->getNumIndices())) {
      minimalASTParameterIndices = paramIndices;
      minimalSILParameterIndices = silParameterIndices;
      derivativeGenericSignature = derivativeGenSig;
    }
  }

#if 0
  llvm::errs() << "ctx.DerivativeAttrs: " << ctx.DerivativeAttrs.size() << "\n";
  for (auto entry : ctx.DerivativeAttrs) {
    auto *attr = entry.getSecond();
    auto *origDecl = std::get<0>(entry.getFirst());
    llvm::errs() << "@deriv attr for: "
                 << cast<ValueDecl>(origDecl)->getFullName() << "\n";
    if (original == origDecl) {
      llvm::errs() << "WE FOUND ONE!\n";
      auto *attrParameterIndices = autodiff::getLoweredParameterIndices(
          attr->getParameterIndices(),
          original->getInterfaceType()->castTo<AnyFunctionType>());
      // If all indices in `parameterIndices` are in `daParameterIndices`, and
      // it has fewer indices than our current candidate and a primitive VJP,
      // then `attr` is our new candidate.
      //
      // NOTE(TF-642): `attr` may come from a un-partial-applied function and
      // have larger capacity than the desired indices. We expect this logic to
      // go away when `partial_apply` supports `@differentiable` callees.
      if (attrParameterIndices->isSupersetOf(
              parameterIndices->extendingCapacity(
                  original->getASTContext(),
                  attrParameterIndices->getCapacity())) &&
          // fewer parameters than before
          (!minimalParameterIndices ||
           attrParameterIndices->getNumIndices() <
               minimalParameterIndices->getNumIndices())) {
#if 0
        minimalAttr = attr;
        minimalParameterIndices = attrParameterIndices;
#endif
        // TODO: `DerivativeAttrs` is not sufficient, doesn't store derivative
        // generic signature derivativeGenericSignature =
        // attr->getDerivativeGenericSignature(); derivativeGenericSignature =
        // getAutoDiffDerivativeFunctionGenericSignature(original->getGenericSignature(),
        // origDecl->getModuleContext());
      }
    }
  }
#endif
#if 0
  for (auto derivKind : {AutoDiffDerivativeFunctionKind::JVP,
                         AutoDiffDerivativeFunctionKind::VJP}) {
    auto *attr = ctx.DerivativeAttrs.lookup({original, parameterIndices, derivKind});
    if (!attr)
      continue;
    return attr;
  }
#endif
  return minimalASTParameterIndices;
}

SILDifferentiabilityWitness *getOrCreateMinimalASTDifferentiabilityWitness(
    SILModule &module, SILFunction *original, IndexSubset *parameterIndices,
    IndexSubset *resultIndices) {
  // AST differentiability witnesses always have a single result.
  if (resultIndices->getCapacity() != 1 || !resultIndices->contains(0))
    return nullptr;

  // Explicit differentiability witnesses only exist on SILFunctions that come
  // from AST functions.
  auto *originalAFD = findAbstractFunctionDecl(original);
  if (!originalAFD)
    return nullptr;

#if 0
  IndexSubset *minimalParameterIndices = nullptr;
  const auto *minimalAttr = getMinimalASTDifferentiableAttr(
      originalAFD, parameterIndices, minimalParameterIndices);

  // TODO(TF-835): This will also need to search all `@differentiating`
  // attributes after we stop synthesizing `@differentiable` attributes for
  // `@differentiating` attributes.

  if (!minimalAttr)
    return nullptr;

  AutoDiffConfig minimalConfig(minimalParameterIndices, resultIndices,
                               minimalAttr->getDerivativeGenericSignature());
#endif
  IndexSubset *minimalASTParameterIndices = nullptr;
  IndexSubset *minimalSILParameterIndices = nullptr;
  GenericSignature derivativeGenericSignature;
  if (!findMinimalDerivativeConfiguration(
      originalAFD, parameterIndices, minimalASTParameterIndices,
      minimalSILParameterIndices, derivativeGenericSignature)) {
    return nullptr;
  }

  AutoDiffConfig minimalConfig(minimalSILParameterIndices, resultIndices,
                               derivativeGenericSignature);

  auto *existingWitness = module.lookUpDifferentiabilityWitness(
      {original->getName(), minimalConfig});
  if (existingWitness)
    return existingWitness;

  assert(original->isExternalDeclaration() &&
         "SILGen should create differentiability witnesses for all function "
         "definitions with explicit differentiable attributes");

  return SILDifferentiabilityWitness::createDeclaration(
      module, SILLinkage::PublicExternal, original,
      minimalConfig.parameterIndices, minimalConfig.resultIndices,
      minimalConfig.derivativeGenericSignature);
}

} // end namespace swift
