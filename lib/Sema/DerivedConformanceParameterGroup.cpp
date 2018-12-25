//===--- DerivedConformanceParameterGroup.cpp -----------------------------===//
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
// This file implements explicit derivation of the ParameterGroup protocol
// for a nominal type.
//
//===----------------------------------------------------------------------===//

#include "CodeSynthesis.h"
#include "TypeChecker.h"
#include "swift/AST/Decl.h"
#include "swift/AST/Expr.h"
#include "swift/AST/GenericSignature.h"
#include "swift/AST/Module.h"
#include "swift/AST/ParameterList.h"
#include "swift/AST/Pattern.h"
#include "swift/AST/ProtocolConformance.h"
#include "swift/AST/Stmt.h"
#include "swift/AST/Types.h"
#include "DerivedConformances.h"

using namespace swift;

// Return the "parameter type" corresponding to a ValueDecl.
// If the decl conforms to ParameterGroup, return the `Parameter` associated
// type. Otherwise, directly return the decl's type.
static Type getParameterType(ValueDecl *decl) {
  auto &ctx = decl->getASTContext();
  auto *paramGroupProto = ctx.getProtocol(KnownProtocolKind::ParameterGroup);
  auto conf = TypeChecker::conformsToProtocol(
      decl->getInterfaceType(), paramGroupProto, decl->getDeclContext(),
      ConformanceCheckFlags::InExpression);
  if (!conf)
    return decl->getInterfaceType();
  Type parameterType = ProtocolConformanceRef::getTypeWitnessByName(
      decl->getInterfaceType(), *conf, ctx.Id_Parameter, ctx.getLazyResolver());
  assert(parameterType && "'Parameter' associated type not found");
  return parameterType;
}

static Type deriveParameterGroup_Parameter(NominalTypeDecl *nominal) {
  if (nominal->getStoredProperties().empty())
    return Type();
  // If all stored properties have the same type, return that type.
  // Otherwise, the `Parameter` type cannot be derived.
  Type sameMemberType;
  for (auto member : nominal->getStoredProperties()) {
    auto parameterType = getParameterType(member);
    if (!sameMemberType) {
      sameMemberType = parameterType;
      continue;
    }
    if (!parameterType->isEqual(sameMemberType))
      return Type();
  }
  return sameMemberType;
}

bool DerivedConformance::canDeriveParameterGroup(NominalTypeDecl *nominal) {
  // return bool(deriveParameterGroup_Parameter(nominal));
  // return !nominal->getMembers().empty();

  // There must be at least one stored property.
  // TODO: Could be improved.
  // Can derive if `Parameter` and `update` are defined.
  return !nominal->getStoredProperties().empty();
}

// Add @_fixed_layout attribute to type conforming to `ParameterGroup`, if
// necessary.
void addFixedLayoutAttrIfNeeded(TypeChecker &TC, NominalTypeDecl *nominal) {
  // If nominal already has @_fixed_layout, return.
  if (nominal->getAttrs().hasAttribute<FixedLayoutAttr>())
    return;
  auto access = nominal->getEffectiveAccess();
  // If nominal does not have at least internal access, return.
  if (access < AccessLevel::Internal)
    return;
  // If nominal is internal, it should have the @usableFromInline attribute.
  if (access == AccessLevel::Internal &&
      !nominal->getAttrs().hasAttribute<UsableFromInlineAttr>()) {
    nominal->getAttrs().add(new (TC.Context)
                                UsableFromInlineAttr(/*Implicit*/ true));
  }
  // Add the @_fixed_layout attribute to the nominal.
  nominal->getAttrs().add(new (TC.Context) FixedLayoutAttr(/*Implicit*/ true));
}

static TypeAliasDecl *getParameterTypeAliasDecl(NominalTypeDecl *nominal) {
  auto &ctx = nominal->getASTContext();
  TypeAliasDecl *parameterDecl = nullptr;
  for (auto memberDecl : nominal->getMembers()) {
    auto typealiasDecl = dyn_cast<TypeAliasDecl>(memberDecl);
    if (!typealiasDecl || typealiasDecl->getName() != ctx.Id_Parameter)
      continue;
    parameterDecl = typealiasDecl;
    break;
  }
  return parameterDecl;
}

static void deriveBodyParameterGroup_update(AbstractFunctionDecl *funcDecl) {
  auto *nominal = funcDecl->getDeclContext()->getSelfNominalTypeDecl();
  auto &C = nominal->getASTContext();

  auto *selfDecl = funcDecl->getImplicitSelfDecl();
  Expr *selfDRE =
      new (C) DeclRefExpr(selfDecl, DeclNameLoc(), /*Implicit*/ true);

  auto *gradientsDecl = funcDecl->getParameters()->get(0);
  auto *updaterDecl = funcDecl->getParameters()->get(1);
  Expr *gradientsDRE =
      new (C) DeclRefExpr(gradientsDecl, DeclNameLoc(), /*Implicit*/ true);
  Expr *updaterDRE =
      new (C) DeclRefExpr(updaterDecl, DeclNameLoc(), /*Implicit*/ true);

  // Return the member with the same name as a target VarDecl.
  auto getMatchingMember = [&](VarDecl *target) -> VarDecl * {
    for (auto member : nominal->getStoredProperties()) {
      if (member->getName() == target->getName())
        return member;
    }
    assert(false && "Could not find matching 'ParameterGroup' member");
    return nullptr;
  };

  auto *paramGroupProto = C.getProtocol(KnownProtocolKind::ParameterGroup);
  auto lookup = paramGroupProto->lookupDirect(C.getIdentifier("update"));
  assert(lookup.size() == 1 && "Broken 'ParameterGroup' protocol");
  auto updateRequirement = lookup[0];

  // Return an "update call" expression for a member `x`.
  auto createUpdateCallExpr = [&](VarDecl *member) -> Expr * {
    auto module = nominal->getModuleContext();
    auto confRef =
        module->lookupConformance(member->getType(), paramGroupProto);
    auto *memberExpr = new (C) MemberRefExpr(selfDRE, SourceLoc(), member,
                                             DeclNameLoc(), /*Implicit*/ true);
    auto *gradientsMemberExpr = new (C) MemberRefExpr(
        gradientsDRE, SourceLoc(), getMatchingMember(member), DeclNameLoc(),
        /*Implicit*/ true);

    // If member does not conform to ParameterGroup, apply updater to member
    // directly: `updater(&x, gradients.x)`.
    if (!confRef) {
      auto *inoutExpr = new (C) InOutExpr(SourceLoc(), memberExpr,
                                          member->getType(), /*Implicit*/ true);
      return CallExpr::createImplicit(C, updaterDRE,
                                      {inoutExpr, gradientsMemberExpr}, {});
    }

    // Otherwise, if member does conform to ParameterGroup, call the
    // member's `update` method:
    // `x.update(withGradients: gradients.x, updater)`.
    auto conf = confRef->getConcrete();
    auto paramUpdateDecl = conf->getWitnessDecl(updateRequirement, nullptr);
    auto updateDRE =
        new (C) DeclRefExpr(paramUpdateDecl, DeclNameLoc(), /*Implicit*/ true);
    auto updateCallExpr =
        new (C) DotSyntaxCallExpr(updateDRE, SourceLoc(), memberExpr);
    updateCallExpr->setImplicit();
    return CallExpr::createImplicit(
        C, updateCallExpr, {gradientsMemberExpr, updaterDRE},
        {C.getIdentifier("withGradients"), Identifier()});
  };

  SmallVector<ASTNode, 2> updateCallNodes;
  for (auto member : nominal->getStoredProperties()) {
    auto *call = createUpdateCallExpr(member);
    updateCallNodes.push_back(call);
  }
  funcDecl->setBody(BraceStmt::create(C, SourceLoc(), updateCallNodes,
                                      SourceLoc(),
                                      /*Implicit*/ true));
}

// Synthesize the `update(withGradients:_:)` function declaration.
static ValueDecl *deriveParameterGroup_update(DerivedConformance &derived) {
  auto nominal = derived.Nominal;
  auto parentDC = derived.getConformanceContext();
  auto &C = derived.TC.Context;

  auto parametersType = nominal->getDeclaredTypeInContext();
  auto parametersInterfaceType = nominal->getDeclaredInterfaceType();

  auto parameterDecl = getParameterTypeAliasDecl(nominal);
  auto parameterType = parameterDecl->getDeclaredInterfaceType();
  assert(nominal && parametersType && "'Parameters' decl unresolved");
  assert(parameterDecl && "'Parameter' decl unresolved");

  auto gradientsDecl =
      new (C) ParamDecl(VarDecl::Specifier::Default, SourceLoc(), SourceLoc(),
                        C.getIdentifier("withGradients"), SourceLoc(),
                        C.getIdentifier("gradients"), parentDC);
  gradientsDecl->setInterfaceType(parametersInterfaceType);

  auto inoutFlag = ParameterTypeFlags().withInOut(true);
  auto updaterDecl = new (C) ParamDecl(VarDecl::Specifier::Default, SourceLoc(),
                                       SourceLoc(), Identifier(), SourceLoc(),
                                       C.getIdentifier("updater"), parentDC);
  FunctionType::Param updaterInputTypes[] = {
      FunctionType::Param(parameterType, Identifier(), inoutFlag),
      FunctionType::Param(parameterType)};
  auto updaterType =
      FunctionType::get(updaterInputTypes, TupleType::getEmpty(C),
                        FunctionType::ExtInfo().withNoEscape());
  updaterDecl->setInterfaceType(updaterType);

  ParameterList *params =
      ParameterList::create(C, {gradientsDecl, updaterDecl});

  DeclName updateDeclName(C, C.getIdentifier("update"), params);
  auto updateDecl = FuncDecl::create(
      C, SourceLoc(), StaticSpellingKind::None, SourceLoc(), updateDeclName,
      SourceLoc(), /*Throws*/ false, SourceLoc(), nullptr, params,
      TypeLoc::withoutLoc(TupleType::getEmpty(C)), nominal);
  updateDecl->setImplicit();
  updateDecl->setSelfAccessKind(SelfAccessKind::Mutating);
  updateDecl->setBodySynthesizer(deriveBodyParameterGroup_update);

  if (auto env = parentDC->getGenericEnvironmentOfContext())
    updateDecl->setGenericEnvironment(env);
  updateDecl->computeType();
  updateDecl->copyFormalAccessFrom(nominal, /*sourceIsParentContext*/ true);
  updateDecl->setValidationToChecked();

  derived.addMembersToConformanceContext({updateDecl});
  C.addSynthesizedDecl(updateDecl);

  return updateDecl;
}

// Synthesize body for the `keyPaths(to:)` function declaration.
static void deriveBodyParameterGroup_keyPaths(AbstractFunctionDecl *funcDecl) {
  auto *nominal = funcDecl->getDeclContext()->getSelfNominalTypeDecl();
  auto &C = nominal->getASTContext();

  auto *nominalTypeExpr = TypeExpr::createForDecl(SourceLoc(), nominal,
                                                  funcDecl, /*Implicit*/ true);

  // Get generic parameter <T>.
  auto genericParamType = funcDecl->getGenericSignature()
                              ->getGenericParams()
                              .back()
                              ->getCanonicalType();
  auto *typeExpr = TypeExpr::createImplicit(
      funcDecl->mapTypeIntoContext(genericParamType), C);
  auto typeSelfExpr =
      new (C) DotSelfExpr(typeExpr, SourceLoc(), SourceLoc(), genericParamType);
  typeSelfExpr->setImplicit();

  // Create map from parameter type to parameter key paths.
  llvm::DenseMap<Type, llvm::SmallVector<Expr *, 2>> parameterTypes;
  for (auto member : nominal->getStoredProperties()) {
    auto *dotExpr = new (C)
        UnresolvedDotExpr(nominalTypeExpr, SourceLoc(), member->getFullName(),
                          DeclNameLoc(), /*Implicit*/ true);
    auto *keyPathExpr =
        new (C) KeyPathExpr(SourceLoc(), dotExpr, nullptr, /*Implicit*/ true);
    parameterTypes[member->getType()].push_back(keyPathExpr);
  }

  // Create case statements. Example:
  // `case is Float.self: return [\Parameters.w, \Parameters.b]`
  SmallVector<ASTNode, 2> caseStmts;
  auto resultType =
      funcDecl->mapTypeIntoContext(funcDecl->getMethodInterfaceType()
                                       ->getAs<AnyFunctionType>()
                                       ->getResult());
  auto resultTypeLoc = TypeLoc::withoutLoc(resultType);
  for (auto &pair : parameterTypes) {
    auto parameterType = pair.first;
    auto keyPathExprs = pair.second;
    auto parameterMetatype =
        TypeLoc::withoutLoc(MetatypeType::get(parameterType, C));
    auto *pattern = new (C) IsPattern(SourceLoc(), parameterMetatype, nullptr,
                                      CheckedCastKind::ValueCast);
    auto *arrayExpr =
        ArrayExpr::create(C, SourceLoc(), keyPathExprs, {}, SourceLoc());
    auto *castExpr = new (C) ForcedCheckedCastExpr(arrayExpr, SourceLoc(),
                                                   SourceLoc(), resultTypeLoc);
    auto *returnStmt = new (C) ReturnStmt(SourceLoc(), castExpr);
    auto *body = BraceStmt::create(C, SourceLoc(), {returnStmt}, SourceLoc(),
                                   /*Implicit*/ true);
    auto caseItem = CaseLabelItem(pattern, SourceLoc(), /*guardExpr*/ nullptr);
    auto *caseStmt =
        CaseStmt::create(C, SourceLoc(), {caseItem}, /*HasBoundDecls*/ false,
                         SourceLoc(), SourceLoc(), body, /*Implicit*/ true);
    caseStmts.push_back(caseStmt);
  }

  // Create default case statement:
  // `default: return []`
  auto *returnStmt = new (C) ReturnStmt(
      SourceLoc(), ArrayExpr::create(C, SourceLoc(), {}, {}, SourceLoc()));
  auto *body = BraceStmt::create(C, SourceLoc(), {returnStmt}, SourceLoc(),
                                 /*Implicit*/ true);
  auto caseItem = CaseLabelItem::getDefault(
      new (C) AnyPattern(SourceLoc(), /*Implicit*/ true));
  auto *caseStmt =
      CaseStmt::create(C, SourceLoc(), {caseItem}, /*HasBoundDecls*/ false,
                       SourceLoc(), SourceLoc(), body, /*Implicit*/ true);
  caseStmts.push_back(caseStmt);

  // Create switch statement and set function body.
  auto *switchStmt =
      SwitchStmt::create(LabeledStmtInfo(), SourceLoc(), typeSelfExpr,
                         SourceLoc(), caseStmts, SourceLoc(), C);
  funcDecl->setBody(BraceStmt::create(C, SourceLoc(), {switchStmt}, SourceLoc(),
                                      /*Implicit*/ true));
}

// Synthesize body for the `nestedKeyPaths(to:)` function declaration.
static void
deriveBodyParameterGroup_nestedKeyPaths(AbstractFunctionDecl *funcDecl) {
  auto *nominal = funcDecl->getDeclContext()->getSelfNominalTypeDecl();
  auto &C = nominal->getASTContext();
  auto *nominalTypeExpr = TypeExpr::createForDecl(SourceLoc(), nominal,
                                                  funcDecl, /*Implicit*/ true);
  auto *selfDecl = funcDecl->getImplicitSelfDecl();
  Expr *selfDRE =
      new (C) DeclRefExpr(selfDecl, DeclNameLoc(), /*Implicit*/ true);

  // Get generic parameter <T>.
  auto genericParamType = funcDecl->getGenericSignature()
                              ->getGenericParams()
                              .back()
                              ->getCanonicalType();
  auto *typeExpr = TypeExpr::createImplicit(
      funcDecl->mapTypeIntoContext(genericParamType), C);
  auto typeSelfExpr =
      new (C) DotSelfExpr(typeExpr, SourceLoc(), SourceLoc(), genericParamType);
  typeSelfExpr->setImplicit();

  // Get `ParameterGroup.allKeyPaths(to:)` function declaration.
  auto *paramGroupProto = C.getProtocol(KnownProtocolKind::ParameterGroup);
  auto lookup = paramGroupProto->lookupDirect(C.getIdentifier("allKeyPaths"));
  assert(lookup.size() == 1 && "Broken 'ParameterGroup' protocol");
  auto allKeyPathsDecl = lookup[0];

  // Get `WritableKeyPath<Nominal, T>` type.
  auto *writableKeyPathDecl = cast<ClassDecl>(C.getWritableKeyPathDecl());
  auto resultKeyPathType = BoundGenericClassType::get(
      writableKeyPathDecl, /*parent*/ Type(),
      {nominal->getDeclaredInterfaceType(), genericParamType});

  // Store expressions of the form:
  // `x.allKeyPaths(to: T.self).map { (\Nominal.x).appending(path: $0) }`
  llvm::SmallVector<Expr *, 2> keyPathsExprs;
  unsigned discriminator = 0;
  for (auto member : nominal->getStoredProperties()) {
    auto module = nominal->getModuleContext();
    auto confRef =
        module->lookupConformance(member->getType(), paramGroupProto);
    // If stored property does not conform to `ParameterGroup`, continue.
    if (!confRef)
      continue;

    // `member.allKeyPaths(to: T.self)`
    auto *memberExpr = new (C) MemberRefExpr(selfDRE, SourceLoc(), member,
                                             DeclNameLoc(), /*Implicit*/ true);
    auto allKeyPathsDRE =
        new (C) DeclRefExpr(allKeyPathsDecl, DeclNameLoc(), /*Implicit*/ true);
    auto allKeyPathsExpr =
        new (C) DotSyntaxCallExpr(allKeyPathsDRE, SourceLoc(), memberExpr);
    allKeyPathsExpr->setImplicit();
    auto *allKeyPathsCallExpr =
        CallExpr::createImplicit(C, allKeyPathsExpr, {typeSelfExpr}, {C.Id_to});

    // `{ \Nominal.member.appending(path: $0) }`
    auto closureParamDecl = new (C)
        ParamDecl(VarDecl::Specifier::Default, SourceLoc(), SourceLoc(),
                  Identifier(), SourceLoc(), C.getIdentifier("$0"), funcDecl);
    auto params = ParameterList::create(C, {closureParamDecl});
    auto *closure =
        new (C) ClosureExpr(params, SourceLoc(), SourceLoc(), SourceLoc(),
                            TypeLoc::withoutLoc(resultKeyPathType),
                            /*discriminator*/ discriminator++, funcDecl);
    closure->getCaptureInfo().setGenericParamCaptures(true);
    auto *memberDotExpr = new (C)
        UnresolvedDotExpr(nominalTypeExpr, SourceLoc(), member->getFullName(),
                          DeclNameLoc(), /*Implicit*/ true);
    auto *keyPathExpr = new (C)
        KeyPathExpr(SourceLoc(), memberDotExpr, nullptr, /*Implicit*/ true);
    auto appendingExpr = new (C) UnresolvedDotExpr(
        keyPathExpr, SourceLoc(), DeclName(C.getIdentifier("appending")),
        DeclNameLoc(), /*Implicit*/ true);
    auto closureParamDRE =
        new (C) DeclRefExpr(closureParamDecl, DeclNameLoc(), /*Implicit*/ true);
    auto *callExpr = CallExpr::createImplicit(
        C, appendingExpr, {closureParamDRE}, {C.getIdentifier("path")});
    auto *returnStmt = new (C) ReturnStmt(SourceLoc(), callExpr);
    auto *body = BraceStmt::create(C, SourceLoc(), {returnStmt}, SourceLoc(),
                                   /*Implicit*/ true);
    closure->setBody(body, /*isSingleExpression*/ true);

    // `member.allKeyPaths(to: T.self).map
    //    { (\Nominal.member).appending(path: $0) }`
    auto mapExpr = new (C) UnresolvedDotExpr(allKeyPathsCallExpr, SourceLoc(),
                                             DeclName(C.getIdentifier("map")),
                                             DeclNameLoc(), /*Implicit*/ true);
    auto mapCallExpr =
        CallExpr::createImplicit(C, mapExpr, {closure}, {Identifier()});
    keyPathsExprs.push_back(mapCallExpr);
  }
  // If no result exprs exist, return empty array.
  if (keyPathsExprs.empty()) {
    auto *returnStmt = new (C) ReturnStmt(
        SourceLoc(), ArrayExpr::create(C, SourceLoc(), {}, {}, SourceLoc()));
    auto *body = BraceStmt::create(C, SourceLoc(), {returnStmt}, SourceLoc(),
                                   /*Implicit*/ true);
    funcDecl->setBody(BraceStmt::create(C, SourceLoc(), {body}, SourceLoc(),
                                        /*Implicit*/ true));
    return;
  }
  // Otherwise, concatenate all result exprs and return.
  Expr *resultExpr = keyPathsExprs[0];
  for (auto keyPathsExpr : keyPathsExprs) {
    if (keyPathsExpr == resultExpr)
      continue;
    auto plusFuncExpr = new (C)
        UnresolvedDeclRefExpr(DeclName(C.getIdentifier("+")),
                              DeclRefKind::BinaryOperator, DeclNameLoc());
    auto plusArgs = TupleExpr::create(
        C, SourceLoc(), {resultExpr, keyPathsExpr}, {}, {}, SourceLoc(),
        /*HasTrailingClosure*/ false,
        /*Implicit*/ true);
    auto plusExpr = new (C) BinaryExpr(plusFuncExpr, plusArgs,
                                       /*Implicit*/ true);
    resultExpr = plusExpr;
  }
  auto *returnStmt = new (C) ReturnStmt(SourceLoc(), resultExpr);
  auto *body = BraceStmt::create(C, SourceLoc(), {returnStmt}, SourceLoc(),
                                 /*Implicit*/ true);
  funcDecl->setBody(BraceStmt::create(C, SourceLoc(), {body}, SourceLoc(),
                                      /*Implicit*/ true));
}

// Synthesize the `keyPaths(to:)` or `nestedKeyPaths(to:)` function declaration.
static ValueDecl *deriveParameterGroup_keyPaths(DerivedConformance &derived,
                                                bool isNested) {
  auto nominal = derived.Nominal;
  auto parentDC = derived.getConformanceContext();
  auto &C = derived.TC.Context;

  // Create generic parameter <T>.
  int depth = 0;
  if (auto genSig = nominal->getGenericSignature())
    depth = genSig->getGenericParams().back()->getDepth() + 1;
  auto genericParam = new (C) GenericTypeParamDecl(
      parentDC, C.getIdentifier("T"), SourceLoc(), depth, /*index*/ 0);

  // Create `to: T.Type` parameter.
  auto toParamDecl =
      new (C) ParamDecl(VarDecl::Specifier::Default, SourceLoc(), SourceLoc(),
                        C.Id_to, SourceLoc(), C.Id_to, parentDC);
  toParamDecl->setInterfaceType(genericParam->getInterfaceType());

  auto *genericParams =
      GenericParamList::create(C, SourceLoc(), {genericParam}, SourceLoc());
  ParameterList *params = ParameterList::create(C, {toParamDecl});

  // Create `keyPaths(to:)` function declaration.
  auto keyPathsId = isNested ? C.Id_nestedKeyPaths : C.Id_keyPaths;
  DeclName keyPathsDeclName(C, keyPathsId, params);
  auto *writableKeyPathDecl = cast<ClassDecl>(C.getWritableKeyPathDecl());
  auto writableKeyPathType =
      BoundGenericClassType::get(writableKeyPathDecl, /*parent*/ Type(),
                                 {nominal->getDeclaredInterfaceType(),
                                  genericParam->getDeclaredInterfaceType()});
  auto keyPathsType = ArraySliceType::get(writableKeyPathType);
  auto keyPathsDecl = FuncDecl::create(
      C, SourceLoc(), StaticSpellingKind::None, SourceLoc(), keyPathsDeclName,
      SourceLoc(), /*Throws*/ false, SourceLoc(), genericParams, params,
      TypeLoc::withoutLoc(keyPathsType), nominal);
  keyPathsDecl->setImplicit();
  // Compute function generic signature and type.
  derived.TC.validateGenericFuncSignature(keyPathsDecl);
  if (isNested)
    keyPathsDecl->setBodySynthesizer(deriveBodyParameterGroup_nestedKeyPaths);
  else
    keyPathsDecl->setBodySynthesizer(deriveBodyParameterGroup_keyPaths);
  keyPathsDecl->copyFormalAccessFrom(nominal, /*sourceIsParentContext*/ true);
  keyPathsDecl->setValidationToChecked();

  derived.addMembersToConformanceContext({keyPathsDecl});
  C.addSynthesizedDecl(keyPathsDecl);

  return keyPathsDecl;
}

ValueDecl *DerivedConformance::deriveParameterGroup(ValueDecl *requirement) {
  if (requirement->getBaseName() == TC.Context.getIdentifier("update")) {
    addFixedLayoutAttrIfNeeded(TC, Nominal);
    return deriveParameterGroup_update(*this);
  }
  if (requirement->getBaseName() == TC.Context.Id_keyPaths) {
    addFixedLayoutAttrIfNeeded(TC, Nominal);
    return deriveParameterGroup_keyPaths(*this, /*isNested*/ false);
  }
  if (requirement->getBaseName() == TC.Context.Id_nestedKeyPaths) {
    addFixedLayoutAttrIfNeeded(TC, Nominal);
    return deriveParameterGroup_keyPaths(*this, /*isNested*/ true);
  }
  TC.diagnose(requirement->getLoc(), diag::broken_parameter_group_requirement);
  return nullptr;
}

Type DerivedConformance::deriveParameterGroup(AssociatedTypeDecl *requirement) {
  if (requirement->getBaseName() == TC.Context.Id_Parameter) {
    addFixedLayoutAttrIfNeeded(TC, Nominal);
    return deriveParameterGroup_Parameter(Nominal);
  }
  TC.diagnose(requirement->getLoc(), diag::broken_parameter_group_requirement);
  return nullptr;
}
