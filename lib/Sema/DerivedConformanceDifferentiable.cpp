//===--- DerivedConformanceDifferentiable.cpp - Derived Differentiable ----===//
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
// This file implements explicit derivation of the Differentiable protocol for
// struct types.
//
//===----------------------------------------------------------------------===//

// TODO:
// - Support synthesis when non-synthesized `TangentVector` or `CotangentVector`
//   struct does not have implicit memberwise initializer. Currently,
//   user-defined memberwise initializers do not work.

#include "CodeSynthesis.h"
#include "TypeChecker.h"
#include "swift/AST/AutoDiff.h"
#include "swift/AST/Decl.h"
#include "swift/AST/Expr.h"
#include "swift/AST/Module.h"
#include "swift/AST/ParameterList.h"
#include "swift/AST/Pattern.h"
#include "swift/AST/ProtocolConformance.h"
#include "swift/AST/Stmt.h"
#include "swift/AST/Types.h"
#include "DerivedConformances.h"

using namespace swift;

// Represents the possible outcomes of checking whether the `TangentVector` or
// `CotangentVector` struct exists.
enum AssocStructTypeStatus {
  Valid,
  Invalid,
  DoesNotExist
};

// Return the "parameter type" corresponding to a ValueDecl.
// If the decl conforms to Parameterized, return the `Parameters` associated
// type. Otherwise, directly return the decl's type.
/*
static Type getAutodiffAssocType(ValueDecl *decl) {
  auto &C = decl->getASTContext();
  auto *module = decl->getModuleContext();
  auto *diffProto = C.getProtocol(KnownProtocolKind::Parameterized);
  auto conf =
      module->lookupConformance(decl->getInterfaceType(), diffProto);
  if (!conf)
    return decl->getInterfaceType();
  Type parametersType = ProtocolConformanceRef::getTypeWitnessByName(
      decl->getInterfaceType(), *conf, C.Id_Parameters, nullptr);
  assert(parametersType && "'Parameters' associated type not found");
  return parametersType;
}
*/

static Identifier getAutoDiffAssocTypeIdentifier(
                                           AutoDiffAssociatedTypeKind kind,
                                           ASTContext &C) {
  switch (kind) {
    case AutoDiffAssociatedTypeKind::TangentVector: return C.Id_TangentVector;
    case AutoDiffAssociatedTypeKind::CotangentVector: return C.Id_CotangentVector;
  }
}

// Return the protocol requirement with the specified name.
static ValueDecl *getProtocolRequirement(ProtocolDecl *proto, Identifier name) {
  auto lookup = proto->lookupDirect(name);
  // Erase declarations that are not protocol requirements.
  // This is important for removing default implementations of the same name.
  lookup.erase(std::remove_if(lookup.begin(), lookup.end(), [](ValueDecl *v) {
    return !isa<ProtocolDecl>(v->getDeclContext()) || !v->isProtocolRequirement();
  }), lookup.end());
  assert(lookup.size() == 1 && "Ambiguous protocol requirement");
  return lookup[0];
}

bool DerivedConformance::canDeriveDifferentiable(NominalTypeDecl *nominal) {
  // Nominal type must be a struct with at least one stored property.
  auto *structDecl = dyn_cast<StructDecl>(nominal);
  if (!structDecl || structDecl->getStoredProperties().empty())
    return false;
  // All stored properties must conform to `Differentiable`.
  auto &C = nominal->getASTContext();
  auto *lazyResolver = C.getLazyResolver();
  auto *diffProto = C.getProtocol(KnownProtocolKind::Differentiable);
  // return llvm::all_of(structDecl->getStoredProperties(), [&](VarDecl *v) {
  auto result = llvm::all_of(structDecl->getStoredProperties(), [&](VarDecl *v) {
    if (!v->hasType())
      lazyResolver->resolveDeclSignature(v);
    if (!v->hasType())
      return false;
    auto conf = TypeChecker::conformsToProtocol(
        v->getType(), diffProto, v->getDeclContext(),
        ConformanceCheckFlags::Used);
    return (bool)conf;
  });
  llvm::errs() << "CAN DERIVE DIFFERENTIABLE? " << result << ", " << nominal->getNameStr() << "\n";
  return result;
}

static Type getDifferentiableAssocType(ValueDecl *decl, AutoDiffAssociatedTypeKind kind) {
  auto &C = decl->getASTContext();
  auto *diffableProto = C.getProtocol(KnownProtocolKind::Differentiable);
  auto declType =
    decl->getDeclContext()->mapTypeIntoContext(decl->getInterfaceType());
  auto conf = TypeChecker::conformsToProtocol(declType, diffableProto,
                                              decl->getDeclContext(),
                                              ConformanceCheckFlags::Used);
  if (!conf)
      return Type();
  auto assocTypeId = getAutoDiffAssocTypeIdentifier(kind, C);
  Type assocType = ProtocolConformanceRef::getTypeWitnessByName(
      decl->getInterfaceType(), *conf, assocTypeId, C.getLazyResolver());
  assert(assocType && "Differentiable protocol associated type not found");
  return assocType;
}

// Return true if `parametersDecl` is a valid `Parameters` struct for a nominal
// type.
static bool isValidParametersStruct(NominalTypeDecl *nominal,
                                    StructDecl *parametersDecl) {
  // Add all stored properties of the `Parameters` struct to a map.
  // Also, check that `Parameters` struct has a memberwise initializer.
  llvm::DenseMap<Identifier, VarDecl *> parameters;
  ConstructorDecl *memberwiseInitDecl = nullptr;
  for (auto member : parametersDecl->getMembers()) {
    // Find memberwise initializer.
    if (!memberwiseInitDecl) {
      auto initDecl = dyn_cast<ConstructorDecl>(member);
      if (initDecl && initDecl->isMemberwiseInitializer())
        memberwiseInitDecl = initDecl;
    }
    // Add `Parameters` struct stored properties to map.
    auto varDecl = dyn_cast<VarDecl>(member);
    if (!varDecl || varDecl->isStatic() || !varDecl->hasStorage())
      continue;
    parameters[varDecl->getName()] = varDecl;
  }
  if (!memberwiseInitDecl)
    return false;

  SmallVector<VarDecl *, 8> tfParamDecls;
  nominal->getAllTFParameters(tfParamDecls);
  // If there's a parameter count mismatch, return false.
  if (tfParamDecls.size() != parameters.size())
    return false;

  // Check that each parameter of the nominal type maps to a stored property in
  // the `Parameters` struct.
  for (auto parameter : tfParamDecls) {
    auto it = parameters.find(parameter->getName());
    if (it == parameters.end() ||
        // !it->second->getType()->isEqual(getParameterType(parameter))) {
        !it->second->getType()->isEqual(parameter->getType())) {
      return false;
    }
  }
  return true;
}

static std::pair<StructDecl *, AssocStructTypeStatus>
getAssocTypeStructDecl(NominalTypeDecl *nominal, AutoDiffAssociatedTypeKind kind) {
  auto &ctx = nominal->getASTContext();
  AssocStructTypeStatus status = DoesNotExist;
  StructDecl *assocTypeStructDecl = nullptr;
  auto assocTypeId = getAutoDiffAssocTypeIdentifier(kind, ctx);

  for (auto memberDecl : nominal->getMembers()) {
    auto structDecl = dyn_cast<StructDecl>(memberDecl);
    if (auto typealiasDecl = dyn_cast<TypeAliasDecl>(memberDecl)) {
      auto underlyingType = typealiasDecl->getUnderlyingTypeLoc().getType();
      underlyingType->dump();
      structDecl = dyn_cast<StructDecl>(underlyingType->getAnyNominal());
      structDecl->getDeclaredInterfaceType()->dump();
    }
    if (!structDecl || structDecl->getName() != assocTypeId)
      continue;
    assocTypeStructDecl = structDecl;
    if (isValidParametersStruct(nominal, structDecl))
      return std::make_pair(assocTypeStructDecl, Valid);
    else
      status = Invalid;
  }
  return std::make_pair(assocTypeStructDecl, status);
}

static ConstructorDecl *getMemberwiseInitializer(NominalTypeDecl *nominal) {
  ConstructorDecl *memberwiseInitDecl = nullptr;
  for (auto member : nominal->getMembers()) {
    // Find memberwise initializer.
    if (!memberwiseInitDecl) {
      auto initDecl = dyn_cast<ConstructorDecl>(member);
      if (!initDecl || !initDecl->isMemberwiseInitializer())
        continue;
      assert(!memberwiseInitDecl && "Memberwise initializer already found");
      memberwiseInitDecl = initDecl;
    }
  }
  return memberwiseInitDecl;
}

// Synthesize body for a `Differentiable` method requirement.
static void deriveBodyDifferentiable_method(AbstractFunctionDecl *funcDecl,
                                            Identifier methodName,
                                            Identifier methodParamLabel,
                                            NominalTypeDecl *returnedNominal) {
  auto *nominal = funcDecl->getDeclContext()->getSelfNominalTypeDecl();
  auto &C = nominal->getASTContext();

  auto *memberwiseInitDecl = getMemberwiseInitializer(returnedNominal);
  auto *initDRE =
    new (C) DeclRefExpr(memberwiseInitDecl, DeclNameLoc(), /*Implicit*/ true);
  initDRE->setFunctionRefKind(FunctionRefKind::SingleApply);

  // auto *retNominalTypeExpr = TypeExpr::createForDecl(SourceLoc(), returnedNominal,
  //                                                    nominal, /*Implicit*/ true);
  // auto *retNominalTypeExpr = TypeExpr::createImplicit(returnedNominal->getDeclaredInterfaceType(), C);
  auto retNominalType = funcDecl->mapTypeIntoContext(returnedNominal->getDeclaredInterfaceType());
  auto *retNominalTypeExpr = TypeExpr::createImplicit(retNominalType, C);
  auto *initExpr = new (C) ConstructorRefCallExpr(initDRE, retNominalTypeExpr);

  auto *diffProto = C.getProtocol(KnownProtocolKind::Differentiable);
  auto *methodReq = getProtocolRequirement(diffProto, methodName);

  auto *selfDecl = funcDecl->getImplicitSelfDecl();
  auto *selfDRE =
    new (C) DeclRefExpr(selfDecl, DeclNameLoc(), /*Implicit*/ true);
  auto *paramDecl = funcDecl->getParameters()->get(0);
  auto *paramDRE =
    new (C) DeclRefExpr(paramDecl, DeclNameLoc(), /*Implicit*/ true);

  auto createMemberCallExpr = [&](VarDecl *member) -> Expr * {
    auto module = nominal->getModuleContext();
    auto confRef = module->lookupConformance(member->getType(), diffProto);
    assert(confRef && "Member does not conform to 'Differentiable'");

    ValueDecl *memberMethodDecl = methodReq;
    // If conformance reference is concrete, then use concrete witness
    // declaration for the operator.
    // FIXME: BUGGED!
    if (confRef->isConcrete())
      memberMethodDecl =
        confRef->getConcrete()->getWitnessDecl(methodReq, nullptr);
    auto memberMethodDRE =
      new (C) DeclRefExpr(memberMethodDecl, DeclNameLoc(), /*Implicit*/ true);
    memberMethodDRE->setFunctionRefKind(FunctionRefKind::SingleApply);

    auto memberExpr = new (C) MemberRefExpr(selfDRE, SourceLoc(), member, DeclNameLoc(),
                                            /*Implicit*/ true);
    auto memberMethodExpr =
      new (C) DotSyntaxCallExpr(memberMethodDRE, SourceLoc(), memberExpr);
    VarDecl *paramMember = nullptr;
    assert(paramDecl->getType()->getAnyNominal() && "param has a nominal type");
    // FIXME: use lookupDirect
    for (auto candidate : paramDecl->getType()->getAnyNominal()->getStoredProperties()) {
      if (candidate->getName() == member->getName() &&
          candidate->getName() == member->getName()) {
        paramMember = candidate;
        break;
      }
    }
    assert(paramMember && "could not find corresponding");
    // auto paramMemberExpr = new (C) MemberRefExpr(paramDRE, SourceLoc(), member, DeclNameLoc(),
    auto paramMemberExpr = new (C) MemberRefExpr(paramDRE, SourceLoc(), paramMember, DeclNameLoc(),
                                                 /*Implicit*/ true);
    return CallExpr::createImplicit(C, memberMethodExpr, {paramMemberExpr}, {methodParamLabel});
  };

  // Create array of member call expressions.
  llvm::SmallVector<Expr *, 2> memberCallExprs;
  llvm::SmallVector<Identifier, 2> memberNames;
  for (auto member : nominal->getStoredProperties()) {
    memberCallExprs.push_back(createMemberCallExpr(member));
    memberNames.push_back(member->getName());
  }
  // Call memberwise initialier with member call expressions.
  auto *callExpr =
      CallExpr::createImplicit(C, initExpr, memberCallExprs, memberNames);
  llvm::errs() << "SYNTHESIZED BODY FOR " << methodName.str() << "\n";
  callExpr->dump();
  ASTNode returnStmt = new (C) ReturnStmt(SourceLoc(), callExpr, true);
  funcDecl->setBody(
      BraceStmt::create(C, SourceLoc(), returnStmt, SourceLoc(), true));
}

// Synthesize body for `moved(along:)`.
static void deriveBodyDifferentiable_moved(AbstractFunctionDecl *funcDecl) {
  auto *nominal = funcDecl->getDeclContext()->getSelfNominalTypeDecl();
  auto &C = nominal->getASTContext();
  deriveBodyDifferentiable_method(funcDecl, C.Id_moved, C.getIdentifier("along"), nominal);
}

// Synthesize body for `tangentVector(from:)`.
static void deriveBodyDifferentiable_tangentVector(AbstractFunctionDecl *funcDecl) {
  auto *nominal = funcDecl->getDeclContext()->getSelfNominalTypeDecl();
  auto &C = nominal->getASTContext();
  auto *tangentDecl = getAssocTypeStructDecl(nominal, AutoDiffAssociatedTypeKind::TangentVector).first;
  assert(tangentDecl && "'TangentVector' struct must exist");
  deriveBodyDifferentiable_method(funcDecl, C.Id_tangentVector, C.getIdentifier("from"), tangentDecl);
}

// Synthesize the `moved(along:)` function declaration.
static ValueDecl *deriveDifferentiable_moved(DerivedConformance &derived) {
  auto nominal = derived.Nominal;
  auto &C = derived.TC.Context;
  auto parentDC = derived.getConformanceContext();
  auto selfInterfaceType = parentDC->getDeclaredInterfaceType();

  /*
  auto module = nominal->getModuleContext();
  auto lookupConformance = LookUpConformanceInModule(module);
  Type tangentType = nominal->getInterfaceType()->getAutoDiffAssociatedType(
      AutoDiffAssociatedTypeKind::TangentVector, lookupConformance);
   */
  Type tangentType = getAssocTypeStructDecl(nominal, AutoDiffAssociatedTypeKind::TangentVector).first->getDeclaredInterfaceType();
  tangentType->dump();

  auto *param = new (C) ParamDecl(VarDecl::Specifier::Default, SourceLoc(),
                                  SourceLoc(), C.getIdentifier("along"),
                                  SourceLoc(), C.getIdentifier("direction"),
                                  parentDC);
  param->setInterfaceType(tangentType);
  ParameterList *params = ParameterList::create(C, {param});

  DeclName declName(C, C.Id_moved, params);
  auto funcDecl =
    FuncDecl::create(C, SourceLoc(),
                     StaticSpellingKind::None,
                     SourceLoc(), declName, SourceLoc(),
                     /*Throws*/ false, SourceLoc(),
                     /*GenericParams=*/nullptr, params,
                     TypeLoc::withoutLoc(selfInterfaceType),
                     parentDC);
  funcDecl->setImplicit();
  funcDecl->setBodySynthesizer(deriveBodyDifferentiable_moved);

  if (auto env = parentDC->getGenericEnvironmentOfContext())
    funcDecl->setGenericEnvironment(env);
  funcDecl->computeType();
  funcDecl->copyFormalAccessFrom(nominal, /*sourceIsParentContext*/ true);
  funcDecl->setValidationToChecked();
  llvm::errs() << "DUMP MOVED FUNC DECL\n";
  funcDecl->dump();

  derived.addMembersToConformanceContext({funcDecl});
  C.addSynthesizedDecl(funcDecl);

  return funcDecl;
}

// Synthesize the `tangentVector(from:)` function declaration.
static ValueDecl *
deriveDifferentiable_tangentVector(DerivedConformance &derived) {
  /*
  auto nominal = derived.Nominal;
  auto &TC = derived.TC;
  auto &C = TC.Context;

  StructDecl *parametersDecl;
  AssocStructTypeStatus status;
  std::tie(parametersDecl, status) = getAssocTypeStructDecl(nominal);
  switch (status) {
  case DoesNotExist:
    TC.diagnose(derived.ConformanceDecl->getLoc(),
                diag::parameterized_no_parameters_struct,
                derived.getProtocolType());
    return nullptr;
  case Invalid:
    TC.diagnose(parametersDecl, diag::parameterized_invalid_parameters_struct,
                derived.getProtocolType());
    return nullptr;
  case Valid:
    break;
  }

  auto returnInterfaceTy = parametersDecl->getDeclaredInterfaceType();
  auto returnTy = nominal->mapTypeIntoContext(returnInterfaceTy);
  */

  auto nominal = derived.Nominal;
  auto &C = derived.TC.Context;
  auto parentDC = derived.getConformanceContext();

  /*
  auto module = nominal->getModuleContext();
  auto lookupConformance = LookUpConformanceInModule(module);
  Type tangentVectorType = nominal->getInterfaceType()->getAutoDiffAssociatedType(
      AutoDiffAssociatedTypeKind::TangentVector, lookupConformance);
  Type cotangentVectorType = nominal->getInterfaceType()->getAutoDiffAssociatedType(
      AutoDiffAssociatedTypeKind::CotangentVector, lookupConformance);
   */
  Type tangentType = getAssocTypeStructDecl(nominal, AutoDiffAssociatedTypeKind::TangentVector).first->getDeclaredInterfaceType();
  Type cotangentType = getAssocTypeStructDecl(nominal, AutoDiffAssociatedTypeKind::CotangentVector).first->getDeclaredInterfaceType();

  auto *param = new (C) ParamDecl(VarDecl::Specifier::Default, SourceLoc(),
                                  SourceLoc(), C.getIdentifier("from"),
                                  SourceLoc(), C.getIdentifier("cotangent"),
                                  parentDC);
  param->setInterfaceType(cotangentType);
  ParameterList *params = ParameterList::create(C, {param});

  DeclName declName(C, C.Id_tangentVector, params);
  auto funcDecl =
    FuncDecl::create(C, SourceLoc(),
                     StaticSpellingKind::None,
                     SourceLoc(), declName, SourceLoc(),
                     /*Throws*/ false, SourceLoc(),
                     /*GenericParams=*/nullptr, params,
                     TypeLoc::withoutLoc(tangentType),
                     parentDC);
  funcDecl->setImplicit();
  funcDecl->setBodySynthesizer(deriveBodyDifferentiable_tangentVector);

  if (auto env = parentDC->getGenericEnvironmentOfContext())
    funcDecl->setGenericEnvironment(env);
  funcDecl->computeType();
  funcDecl->copyFormalAccessFrom(nominal, /*sourceIsParentContext*/ true);
  funcDecl->setValidationToChecked();
  llvm::errs() << "DUMP TANGENTVECTOR FUNC DECL\n";

  derived.addMembersToConformanceContext({funcDecl});
  C.addSynthesizedDecl(funcDecl);

  return funcDecl;
}

static Type deriveDifferentiable_AssocType(DerivedConformance &derived,
                                           AutoDiffAssociatedTypeKind kind) {
  auto &TC = derived.TC;
  auto parentDC = derived.getConformanceContext();
  auto nominal = derived.Nominal;
  auto &C = nominal->getASTContext();

  auto module = nominal->getModuleContext();
  auto lookupConformance = LookUpConformanceInModule(module);

  // Check if all members have associated type equal to `Self`.
  bool allMembersSelfEqualsAssoc = llvm::all_of(nominal->getStoredProperties(), [&](VarDecl *member) {
    // auto memberAssocType =
    //   member->getType()->getAutoDiffAssociatedType(kind, lookupConformance);
    auto memberAssocType = nominal->mapTypeIntoContext(getDifferentiableAssocType(member, kind));
    llvm::errs() << "MEMBER TYPE\n";
    member->getType()->dump();
    // member->getInterfaceType()->dump();
    llvm::errs() << "MEMBER ASSOC TYPE\n";
    memberAssocType->dump();
    llvm::errs() << "EQUAL? " << member->getType()->isEqual(memberAssocType) << "\n";
    // nominal->mapTypeIntoContext(memberAssocType)->dump();
    return member->getType()->isEqual(memberAssocType);
  });
  llvm::errs() << "ALL MEMBERS HAVE SELF = ASSOC TYPE? " << allMembersSelfEqualsAssoc << "\n";
  if (allMembersSelfEqualsAssoc) {
    if (DerivedConformance::canDeriveVectorNumeric(nominal)) {
      auto *addArithProto = C.getProtocol(KnownProtocolKind::AdditiveArithmetic);
      auto addArithType = TypeLoc::withoutLoc(addArithProto->getDeclaredType());
      auto *vectorNumProto = C.getProtocol(KnownProtocolKind::VectorNumeric);
      auto vectorNumType = TypeLoc::withoutLoc(vectorNumProto->getDeclaredType());
      TypeLoc inherited[2] = {addArithType, vectorNumType};
      nominal->setInherited(C.AllocateCopy(inherited));
      // TC.typeCheckDecl(nominal);
      // TC.validateDecl(nominal);
      nominal->dump();
      return nominal->getDeclaredInterfaceType();
    }
    assert(false && "couldn't synthesize `vectornumeric` conformance, need all members to conform to `vectornumeric` then, that should always work");
  }

  /*
  Type sameMemberAssocType;
  for (auto *member : nominal->getStoredProperties()) {
    auto memberAssocType =
      member->getType()->getAutoDiffAssociatedType(kind, lookupConformance);
    if (!sameMemberAssocType) {
      sameMemberAssocType = memberAssocType;
      continue;
    }
    if (!sameMemberAssocType->isEqual(memberAssocType)) {
      sameMemberAssocType = nullptr;
      break;
    }
  }
  llvm::errs() << "DO MEMBERS HAVE SAME ASSOC TYPE? " << !sameMemberAssocType.isNull() << "\n";
  if (!sameMemberAssocType.isNull()) {
    sameMemberAssocType->dump();
    return nominal->getDeclaredInterfaceType();
  }
   */

  // Otherwise, synthesize new aggregate struct.
  auto assocTypeId = getAutoDiffAssocTypeIdentifier(kind, C);
  auto *structDecl =
      new (C) StructDecl(SourceLoc(), assocTypeId, SourceLoc(),
                         /*Inherited*/ {}, /*GenericParams*/ {}, parentDC);
  structDecl->setImplicit();
  structDecl->copyFormalAccessFrom(nominal, /*sourceIsParentContext*/ true);
  structDecl->computeType();
  // TC.validateDecl(structDecl);

  for (auto *member : nominal->getStoredProperties()) {
    auto memberAssocType =
        member->getType()->getAutoDiffAssociatedType(kind, lookupConformance);

    auto newMember =
        new (C) VarDecl(member->isStatic(), member->getSpecifier(),
                        member->isCaptureList(), /*NameLoc*/ SourceLoc(),
                        member->getName(), structDecl);
    // NOTE: `newParameter` is not marked as implicit here, because that affects
    // memberwise initializer synthesis.
    newMember->setInterfaceType(memberAssocType->mapTypeOutOfContext());
    // newMember->setType(memberAssocType);
    structDecl->addMember(newMember);
    newMember->copyFormalAccessFrom(member, /*sourceIsParentContext*/ true);
    newMember->setValidationToChecked();
    newMember->setSetterAccess(member->getFormalAccess());
    C.addSynthesizedDecl(newMember);
  }
  // TEST: Set autodiff associated type to Self.
  /*
  auto typealiasDecl = new (C) TypeAliasDecl(SourceLoc(), SourceLoc(), assocTypeId, SourceLoc(), {}, structDecl);
  typealiasDecl->setUnderlyingType(structDecl->getDeclaredInterfaceType());
  structDecl->addMember(typealiasDecl);
  typealiasDecl->setValidationToChecked();
  C.addSynthesizedDecl(typealiasDecl);
   */
  auto addAssocTypeDecl = [&](Identifier assocTypeId) {
    auto typealiasDecl = new (C) TypeAliasDecl(SourceLoc(), SourceLoc(), assocTypeId, SourceLoc(), {}, structDecl);
    typealiasDecl->setImplicit();
    typealiasDecl->setUnderlyingType(structDecl->getDeclaredInterfaceType());
    structDecl->addMember(typealiasDecl);
    typealiasDecl->setValidationToChecked();
    C.addSynthesizedDecl(typealiasDecl);
  };
  addAssocTypeDecl(C.Id_TangentVector);
  addAssocTypeDecl(C.Id_CotangentVector);

  structDecl->setValidationToChecked();

  // Add conformance to the ParameterGroup protocol, if possible.
  // The ParameterGroup protocol requirements will be derived.
  /*
  if (DerivedConformance::canDeriveParameterGroup(structDecl)) {
    TypeLoc inherited[1] = {paramGroupType};
    structDecl->setInherited(C.AllocateCopy(inherited));
  }
  */
  // assert(DerivedConformance::canDeriveAdditiveArithmetic(structDecl) && "Should be able to derive 'AdditiveArithmetic'");
  // assert(DerivedConformance::canDeriveVectorNumeric(structDecl) && "Should be able to derive 'VectorNumeric'");
  // NOTE: FOLLOWING FAILS
  // assert(DerivedConformance::canDeriveDifferentiable(structDecl) && "Should be able to derive 'Differentiable'");
  auto *vectorNumericProto = C.getProtocol(KnownProtocolKind::VectorNumeric);
  auto vectorNumericType = TypeLoc::withoutLoc(vectorNumericProto->getDeclaredType());
  auto *addArithProto = C.getProtocol(KnownProtocolKind::AdditiveArithmetic);
  auto addArithType = TypeLoc::withoutLoc(addArithProto->getDeclaredType());
  auto *diffableProto = C.getProtocol(KnownProtocolKind::Differentiable);
  auto diffableType = TypeLoc::withoutLoc(diffableProto->getDeclaredType());
  TypeLoc inherited[3] = {addArithType, vectorNumericType, diffableType};
  structDecl->setInherited(C.AllocateCopy(inherited));

  // The implicit memberwise constructor must be explicitly created so that it
  // can called in `VectorNumeric` and `Differentiable` methods. Normally, the
  // memberwise constructor is synthesized during SILGen, which is too late.
  auto *initDecl = createImplicitConstructor(
      TC, structDecl, ImplicitConstructorKind::Memberwise);
  structDecl->addMember(initDecl);
  C.addSynthesizedDecl(initDecl);

  // structDecl->setValidationToChecked();

  // After memberwise initializer is synthesized, mark members as implicit.
  for (auto member : structDecl->getStoredProperties())
    member->setImplicit();

  derived.addMembersToConformanceContext({structDecl});
  C.addSynthesizedDecl(structDecl);

  llvm::errs() << "HERE'S THE STRUCT\n";
  structDecl->dump();

  // auto structType = structDecl->getDeclaredInterfaceType();
  // return derived.getConformanceContext()->mapTypeIntoContext(structType);
  return structDecl->getDeclaredInterfaceType();
}

ValueDecl *DerivedConformance::deriveDifferentiable(ValueDecl *requirement) {
  if (requirement->getBaseName() == TC.Context.Id_moved)
    return deriveDifferentiable_moved(*this);
  if (requirement->getBaseName() == TC.Context.Id_tangentVector)
    return deriveDifferentiable_tangentVector(*this);
  TC.diagnose(requirement->getLoc(), diag::broken_differentiable_requirement);
  return nullptr;
}

Type DerivedConformance::deriveDifferentiable(AssociatedTypeDecl *requirement) {
  if (requirement->getBaseName() == TC.Context.Id_TangentVector) {
    auto rawType = deriveDifferentiable_AssocType(*this, AutoDiffAssociatedTypeKind::TangentVector);
    llvm::errs() << "FINAL TANGENTVECTOR TYPE\n";
    // rawType->dump();
    // return rawType;
    getConformanceContext()->mapTypeIntoContext(rawType)->dump();
    return getConformanceContext()->mapTypeIntoContext(rawType);
    // getConformanceContext()->mapTypeIntoContext(rawType->mapTypeOutOfContext())->dump();
    // return getConformanceContext()->mapTypeIntoContext(rawType->mapTypeOutOfContext());
  }
  if (requirement->getBaseName() == TC.Context.Id_CotangentVector) {
    auto rawType = deriveDifferentiable_AssocType(*this, AutoDiffAssociatedTypeKind::CotangentVector);
    llvm::errs() << "FINAL COTANGENTVECTOR TYPE\n";
    // rawType->dump();
    // return rawType;
    getConformanceContext()->mapTypeIntoContext(rawType)->dump();
    return getConformanceContext()->mapTypeIntoContext(rawType);
    // getConformanceContext()->mapTypeIntoContext(rawType->mapTypeOutOfContext())->dump();
    // return getConformanceContext()->mapTypeIntoContext(rawType->mapTypeOutOfContext());
  }
  TC.diagnose(requirement->getLoc(), diag::broken_differentiable_requirement);
  return nullptr;
}
