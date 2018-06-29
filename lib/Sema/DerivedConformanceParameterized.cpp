//===--- DerivedConformanceParameterized.cpp - Derived Parameterized ------===//
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
// This file implements explicit derivation of the Parameterized protocol for a
// nominal type.
//
//===----------------------------------------------------------------------===//

#include "CodeSynthesis.h"
#include "TypeChecker.h"
#include "swift/AST/Decl.h"
#include "swift/AST/Expr.h"
#include "swift/AST/Module.h"
#include "swift/AST/ParameterList.h"
#include "swift/AST/Pattern.h"
#include "swift/AST/Stmt.h"
#include "swift/AST/Types.h"
#include "swift/AST/ProtocolConformance.h"
#include "DerivedConformances.h"

using namespace swift;

static bool isValidParametersStruct(NominalTypeDecl *nominal,
                                    StructDecl *parameters) {
  llvm::DenseSet<VarDecl *> parameterDecls;
  for (auto member : parameters->getMembers()) {
    auto varDecl = dyn_cast<VarDecl>(member);
    if (!varDecl || varDecl->isStatic() || !varDecl->hasStorage() ||
        !varDecl->getGetter() || !varDecl->getSetter())
      return false;
    parameterDecls.insert(varDecl);
  }

  for (auto parameter : nominal->getAllParameters()) {
    bool foundMatch = false;
    for (auto p : parameterDecls) {
      if (p->getType()->isEqual(parameter->getType()) &&
          p->getName() == parameter->getName()) {
        foundMatch = true;
        break;
      }
    }
    if (!foundMatch) return false;
  }
  return true;
}

static StructDecl *getParametersStructDecl(NominalTypeDecl *nominal) {
  auto &ctx = nominal->getASTContext();
  StructDecl *parametersDecl = nullptr;
  for (auto memberDecl : nominal->getMembers()) {
    auto structDecl = dyn_cast<StructDecl>(memberDecl);
    if (!structDecl || structDecl->getName() != ctx.Id_Parameters) {
      continue;
    }
    // if (isValidParametersStruct(Nominal, structDecl)) {
    //   parametersDecl = structDecl;
    //   break;
    // }
    parametersDecl = structDecl;
    break;
  }
  return parametersDecl;
}

static AccessorDecl *
declareDerivedPropertySetter(DerivedConformance &derived, TypeChecker &tc,
                             VarDecl *property, Type propertyContextType) {
  bool isStatic = property->isStatic();
  bool isFinal = property->isFinal();

  auto &C = tc.Context;
  auto parentDC = property->getDeclContext();
  auto selfDecl =
    ParamDecl::createSelf(SourceLoc(), parentDC, isStatic, /*isInOut*/ true);

  auto propertyInterfaceType = property->getInterfaceType();
  auto propertyParam =
    new (C) ParamDecl(VarDecl::Specifier::Default, SourceLoc(), SourceLoc(),
                      Identifier(), property->getLoc(),
                      C.getIdentifier("newValue"), property->getType(),
                      parentDC);
  propertyParam->setInterfaceType(propertyInterfaceType);

  ParameterList *params[] = {
    ParameterList::createWithoutLoc(selfDecl),
    ParameterList::create(C, propertyParam)
  };

  auto setterDecl = AccessorDecl::create(C,
      /*FuncLoc*/ SourceLoc(), /*AccessorKeywordLoc*/ SourceLoc(),
      AccessorKind::Set, AddressorKind::NotAddressor, property,
      /*StaticLoc*/ SourceLoc(), StaticSpellingKind::None,
      /*Throws*/ false, /*ThrowsLoc*/ SourceLoc(),
      /*GenericParams*/ nullptr, params,
      TypeLoc::withoutLoc(propertyInterfaceType), parentDC);
  setterDecl->setImplicit();
  setterDecl->setStatic(isStatic);
  setterDecl->setSelfAccessKind(SelfAccessKind::Mutating);

  // If this is supposed to be a final method, mark it as such.
  assert(isFinal || !parentDC->getAsClassOrClassExtensionContext());
  if (isFinal && parentDC->getAsClassOrClassExtensionContext() &&
      !setterDecl->isFinal())
    setterDecl->getAttrs().add(new (C) FinalAttr(/*Implicit*/ true));

  // Compute the interface type of the setter.
  Type interfaceType = FunctionType::get(propertyInterfaceType,
                                         TupleType::getEmpty(C));
  auto selfParam = computeSelfParam(setterDecl);
  if (auto sig = parentDC->getGenericSignatureOfContext()) {
    setterDecl->setGenericEnvironment(
        parentDC->getGenericEnvironmentOfContext());
    interfaceType = GenericFunctionType::get(sig, { selfParam },
                                             interfaceType,
                                             FunctionType::ExtInfo());
  } else {
    interfaceType = FunctionType::get({ selfParam }, interfaceType,
                                      FunctionType::ExtInfo());
  }
  setterDecl->setInterfaceType(interfaceType);
  setterDecl->copyFormalAccessFrom(property);
  setterDecl->setValidationStarted();

  tc.Context.addSynthesizedDecl(setterDecl);
  return setterDecl;
}

static void derivedBody_allParametersGetter(AbstractFunctionDecl *getterDecl) {
  auto *nominal = getterDecl->getDeclContext()
    ->getAsNominalTypeOrNominalTypeExtensionContext();
  auto &C = nominal->getASTContext();

  // auto semantics = AccessSemantics::DirectToStorage;
  // auto *selfDecl = getterDecl->getImplicitSelfDecl();
  // Expr *selfDRE =
  //   new (C) DeclRefExpr(selfDecl, DeclNameLoc(), /*Implicit*/ true);

  auto *parametersDecl = getParametersStructDecl(nominal);
  assert(parametersDecl && "'Parameters' struct not found");
  ConstructorDecl *parametersInitDecl = nullptr;
  for (auto member : parametersDecl->getMembers()) {
    auto initDecl = dyn_cast<ConstructorDecl>(member);
    if (!initDecl || !initDecl->isMemberwiseInitializer()) continue;
    // NOTE: This could trigger if user-defined 'Parameters' exists
    assert(!parametersInitDecl && "'Parameters' initializer already found");
    parametersInitDecl = initDecl;
  }
  assert(parametersInitDecl && "'Parameters' implicit initializer not found");

  auto *selfDecl = getterDecl->getImplicitSelfDecl();
  auto *selfDRE =
    new (C) DeclRefExpr(selfDecl, DeclNameLoc(), /*Implicit*/ true);

  auto *initDRE =
    new (C) DeclRefExpr(parametersInitDecl, DeclNameLoc(), /*Implicit*/ true);
  initDRE->setFunctionRefKind(FunctionRefKind::SingleApply);

  auto parametersType = nominal->mapTypeIntoContext(
      parametersDecl->getDeclaredInterfaceType());
  Expr *baseExpr = TypeExpr::createImplicit(parametersType, C);
  auto* initExpr = new (C) ConstructorRefCallExpr(initDRE, baseExpr);
  initExpr->setThrows(false);
  initExpr->setImplicit();

  auto *parameterizedProto =
    C.getProtocol(KnownProtocolKind::Parameterized);
  auto lookup = parameterizedProto->lookupDirect(C.Id_allParameters);
  assert(lookup.size() == 1);
  auto allParametersReq = lookup[0];

  auto getUnderlyingParameter = [&](Expr *expr, VarDecl *param) -> Expr * {
    auto module = nominal->getModuleContext();
    auto confRef = module->lookupConformance(param->getType(),
                                             parameterizedProto);
    if (!confRef) return expr;
    auto conf = confRef->getConcrete();
    auto allParamsDecl = conf->getWitnessDecl(allParametersReq, nullptr);

    // START EXPERIMENT
    // expr->setType(InOutType::get(expr->getType()));
    // auto inout = new (C) InOutExpr(SourceLoc(), expr,
    //                                parametersDecl->getDeclaredInterfaceType(),
    //                                /*Implicit*/ true);
    // auto MRE = new (C) MemberRefExpr(inout, SourceLoc(), allParamsDecl,
    //                                  DeclNameLoc(), /*Implicit*/ true);
    // return MRE;

    // return new (C) UnresolvedDotExpr(expr, SourceLoc(), C.Id_allParameters,
    //                                  DeclNameLoc(), true);
    auto MRE = new (C) MemberRefExpr(expr, SourceLoc(), allParamsDecl,
                                     DeclNameLoc(), /*Implicit*/ true);
    return MRE;
    // return new (C) InOutExpr(SourceLoc(), MRE,
    //                          parametersDecl->getDeclaredInterfaceType(),
    //                          /*Implicit*/ true);
  };

  SmallVector<Expr *, 2> members;
  SmallVector<Identifier, 2> memberNames;
  for (auto param : nominal->getAllParameters()) {
    Expr *member =
      new (C) MemberRefExpr(selfDRE, SourceLoc(), param, DeclNameLoc(),
                            // /*Implicit*/ true, AccessSemantics::DirectToStorage);
                            /*Implicit*/ true);
    member->setType(param->getType());
    member = getUnderlyingParameter(member, param);
    members.push_back(member);
    memberNames.push_back(param->getName());
  }
  Expr* callExpr = CallExpr::createImplicit(C, initExpr, members, memberNames);

  // llvm::errs() << "allParameters getter body\n";
  // callExpr->dump();

  /*
  auto *parameterizedProto =
    C.getProtocol(KnownProtocolKind::Parameterized);

  auto getUnderlyingParameter = [&](Expr *expr, VarDecl *param) -> Expr * {
    auto module = nominal->getModuleContext();
    auto confRef = module->lookupConformance(param->getType(),
                                             parameterizedProto);
    if (!confRef) return expr;
    // auto conf = confRef->getConcrete();
    // auto allParamsDecl = conf->getWitnessDecl(allParametersReq, nullptr);
    return new (C) UnresolvedDotExpr(expr, SourceLoc(), C.Id_allParameters,
                                     DeclNameLoc(), true);
  };

  auto *initExpr = new (C) UnresolvedDeclRefExpr(DeclName(C.Id_Parameters),
                                                 DeclRefKind::Ordinary,
                                                 DeclNameLoc());
  SmallVector<Expr *, 2> members;
  SmallVector<Identifier, 2> memberNames;
  for (auto param : nominal->getAllParameters()) {
    // NOTE: This place in the code needs to be updated
    Expr *member = new (C) UnresolvedDeclRefExpr(DeclName(param->getName()),
                                                 DeclRefKind::Ordinary,
                                                 DeclNameLoc());
    member = getUnderlyingParameter(member, param);
    members.push_back(member);
    memberNames.push_back(param->getName());
  }
  Expr* callExpr = CallExpr::createImplicit(C, initExpr, members, memberNames);
   */

  ASTNode returnStmt = new (C) ReturnStmt(SourceLoc(), callExpr, true);
  getterDecl->setBody(
      BraceStmt::create(C, SourceLoc(), returnStmt, SourceLoc(), true));
}

static void derivedBody_allParametersSetter(AbstractFunctionDecl *setterDecl) {
  auto *nominal = setterDecl->getDeclContext()
    ->getAsNominalTypeOrNominalTypeExtensionContext();
  auto &C = nominal->getASTContext();

  auto *selfDecl = setterDecl->getImplicitSelfDecl();
  Expr *selfDRE =
    new (C) DeclRefExpr(selfDecl, DeclNameLoc(), /*Implicit*/ true);

  auto *parametersDecl = getParametersStructDecl(nominal);
  assert(parametersDecl && "'Parameters' struct not found");
  auto *newValueDecl = setterDecl->getParameterList(1)->get(0);
  Expr *newValueDRE =
    new (C) DeclRefExpr(newValueDecl, DeclNameLoc(), /*Implicit*/ true);

  auto *parameterizedProto =
    C.getProtocol(KnownProtocolKind::Parameterized);
  auto lookup = parameterizedProto->lookupDirect(C.Id_allParameters);
  assert(lookup.size() == 1);
  auto allParametersReq = lookup[0];

  auto getUnderlyingParameter = [&](VarDecl *param) -> ValueDecl * {
    auto module = nominal->getModuleContext();
    auto confRef =
      module->lookupConformance(param->getType(), parameterizedProto);
    if (!confRef) return param;
    auto conf = confRef->getConcrete();
    auto allParamsDecl = conf->getWitnessDecl(allParametersReq, nullptr);
    return allParamsDecl;
  };

  auto getParametersMember = [&](VarDecl *param) -> ValueDecl * {
    for (auto member : parametersDecl->getMembers()) {
      auto *varDecl = dyn_cast<VarDecl>(member);
      if (!varDecl) continue;
      if (varDecl->getName() == param->getName())
        return varDecl;
    }
    assert(false && "Could not find matching 'Parameters' struct member");
    return nullptr;
  };

  SmallVector<ASTNode, 2> assignNodes;
  for (auto param : nominal->getAllParameters()) {
    Expr *lhs;
    auto lhsParam = getUnderlyingParameter(param);
    if (param == lhsParam) {
      lhs = new (C) MemberRefExpr(selfDRE, SourceLoc(), param, DeclNameLoc(),
                                  /*Implicit*/ true);
    } else {
      auto *paramDRE =
        new (C) MemberRefExpr(selfDRE, SourceLoc(), param, DeclNameLoc(),
                              /*Implicit*/ true);
      lhs = new (C) MemberRefExpr(paramDRE, SourceLoc(), lhsParam,
                                  DeclNameLoc(), /*Implicit*/ true);
    }
    auto *rhs = new (C) MemberRefExpr(newValueDRE, SourceLoc(),
                                      getParametersMember(param), DeclNameLoc(),
                                      /*Implicit*/ true);
    auto *assignExpr = new (C) AssignExpr(lhs, SourceLoc(), rhs,
                                          /*Implicit*/ true);
    assignNodes.push_back(assignExpr);
  }

  setterDecl->setBody(
      BraceStmt::create(C, SourceLoc(), assignNodes, SourceLoc(), true));
  // llvm::errs() << "allParameters setter body\n";
  // setterDecl->dump();
}

// SWIFT_ENABLE_TENSORFLOW
static ValueDecl *
deriveParameterized_allParameters(DerivedConformance &derived) {
  auto nominal = derived.Nominal;
  auto &C = derived.TC.Context;

  for (auto memberDecl : nominal->getMembers()) {
    auto varDecl = dyn_cast<VarDecl>(memberDecl);
    if (!varDecl) continue;
    if (varDecl->getName() == C.Id_allParameters) {
      assert(false && "'allParameters' member already exists");
    }
  }
  StructDecl *parametersDecl = nullptr;
  for (auto memberDecl : nominal->getMembers()) {
    auto structDecl = dyn_cast<StructDecl>(memberDecl);
    if (!structDecl || structDecl->getName() != C.Id_Parameters) {
      continue;
    }

    // if (isValidParametersStruct(Nominal, structDecl)) {
    //   parametersDecl = structDecl;
    //   break;
    // }
    parametersDecl = structDecl;
    break;
  }
  assert(parametersDecl && "WE FAILED\n");

  auto returnInterfaceTy = parametersDecl->getDeclaredInterfaceType();
  auto returnTy = nominal->mapTypeIntoContext(returnInterfaceTy);

  VarDecl *propDecl;
  PatternBindingDecl *pbDecl;
  std::tie(propDecl, pbDecl)
    = derived.declareDerivedProperty(C.Id_allParameters, returnInterfaceTy,
                                     returnTy, /*isStatic*/ false,
                                     /*isFinal*/ true);

  auto *getterDecl =
    derived.declareDerivedPropertyGetter(derived.TC, propDecl, returnTy);
  getterDecl->setBodySynthesizer(&derivedBody_allParametersGetter);

  auto *setterDecl =
    declareDerivedPropertySetter(derived, derived.TC, propDecl, returnTy);
  setterDecl->setBodySynthesizer(&derivedBody_allParametersSetter);
  propDecl->setSetterAccess(nominal->getFormalAccess());
  propDecl->setAccessors(VarDecl::Computed, SourceLoc(),
                         { getterDecl, setterDecl }, SourceLoc());

  derived.addMembersToConformanceContext(
      { getterDecl, setterDecl, propDecl, pbDecl });

  return propDecl;
}

ValueDecl *DerivedConformance::deriveParameterized(ValueDecl *requirement) {
  if (requirement->getBaseName() == TC.Context.Id_allParameters)
    return deriveParameterized_allParameters(*this);
  TC.diagnose(requirement->getLoc(), diag::broken_parameterized_requirement);
  return nullptr;
}

static Type deriveParameterized_Parameters(DerivedConformance &derived) {
  auto &TC = derived.TC;
  auto parentDC = derived.getConformanceContext();
  auto nominal = derived.Nominal;
  auto &C = nominal->getASTContext();

  TC.validateDecl(nominal);

  StructDecl *parametersDecl = nullptr;
  for (auto memberDecl : nominal->getMembers()) {
    auto structDecl = dyn_cast<StructDecl>(memberDecl);
    if (!structDecl) continue;
    if (structDecl->getName() == C.Id_Parameters) {
      assert(false && "'Parameters' struct already exists");
    }
  }
  auto *paramAggProto =
    C.getProtocol(KnownProtocolKind::ParameterAggregate);
  auto paramAggType = TypeLoc::withoutLoc(paramAggProto->getDeclaredType());
  TypeLoc inherited[1] = { paramAggType };
  parametersDecl =
    new (C) StructDecl(SourceLoc(), C.Id_Parameters, SourceLoc(),
                       /*Inherited*/ {}, /*GenericParams*/ {}, parentDC);
  parametersDecl->setImplicit();
  parametersDecl->copyFormalAccessFrom(nominal, /*sourceIsParentContext*/ true);
  TC.validateDecl(parametersDecl);

  auto *parameterizedProto =
    C.getProtocol(KnownProtocolKind::Parameterized);
  for (auto parameter : nominal->getAllParameters()) {
    Type newParameterType;
    auto conf =
      TC.conformsToProtocol(parameter->getType(), parameterizedProto, parentDC,
                            ConformanceCheckFlags::InExpression);
    if (conf) {
      newParameterType =
        ProtocolConformanceRef::getTypeWitnessByName(
          parameter->getType(), *conf, C.Id_Parameters, &TC);
    } else {
      newParameterType = parameter->getType();
    }

    auto newParameter =
      new (C) VarDecl(parameter->isStatic(), parameter->getSpecifier(),
                      parameter->isCaptureList(), /*NameLoc*/ SourceLoc(),
                      parameter->getName(), newParameterType, parametersDecl);
    newParameter->setInterfaceType(newParameterType);
    parametersDecl->addMember(newParameter);
    newParameter->copyFormalAccessFrom(parameter,
                                       /*sourceIsParentContext*/ true);
    newParameter->setValidationStarted();
    newParameter->setSetterAccess(parameter->getFormalAccess());
    C.addSynthesizedDecl(newParameter);
  }
  parametersDecl->setValidationStarted();

  // Add conformance to the ParameterAggregate protocol, if possible.
  // The ParameterAggregate protocol requirements will be derived.
  if (DerivedConformance::canDeriveParameterAggregate(TC, parametersDecl))
    parametersDecl->setInherited(C.AllocateCopy(inherited));

  // The implicit memberwise constructor must be explicitly created so that it
  // can used when synthesizing the `allParameters` getter. Normally, the
  // memberwise constructor is synthesized during SILGen, which is too late.
  auto *initDecl =
    createImplicitConstructor(TC, parametersDecl,
                              ImplicitConstructorKind::Memberwise);
  parametersDecl->addMember(initDecl);

  derived.addMembersToConformanceContext({ parametersDecl });
  C.addSynthesizedDecl(parametersDecl);

  auto parametersType = parametersDecl->getDeclaredInterfaceType();
  return derived.getConformanceContext()->mapTypeIntoContext(parametersType);
}

Type DerivedConformance::deriveParameterized(AssociatedTypeDecl *requirement) {
  if (requirement->getBaseName() == TC.Context.Id_Parameters)
    return deriveParameterized_Parameters(*this);
  TC.diagnose(requirement->getLoc(), diag::broken_parameterized_requirement);
  return nullptr;
}
