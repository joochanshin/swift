//===--- TBDGenVisitor.h - AST Visitor for TBD generation -----------------===//
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
//  This file defines the visitor that finds all symbols in a swift AST.
//
//===----------------------------------------------------------------------===//
#ifndef SWIFT_TBDGEN_TBDGENVISITOR_H
#define SWIFT_TBDGEN_TBDGENVISITOR_H

#include "swift/AST/ASTMangler.h"
#include "swift/AST/ASTVisitor.h"
#include "swift/AST/FileUnit.h"
#include "swift/AST/Module.h"
#include "swift/AST/ParameterList.h"
#include "swift/Basic/LLVM.h"
#include "swift/IRGen/Linking.h"
#include "swift/SIL/FormalLinkage.h"
#include "swift/SIL/SILDeclRef.h"
#include "swift/SIL/SILWitnessTable.h"
#include "swift/SIL/TypeLowering.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/ADT/Triple.h"
#include "llvm/TextAPI/MachO/InterfaceFile.h"

using namespace swift::irgen;
using StringSet = llvm::StringSet<>;

namespace llvm {
class DataLayout;
}

namespace swift {

struct TBDGenOptions;

namespace tbdgen {

class TBDGenVisitor : public ASTVisitor<TBDGenVisitor> {
public:
  llvm::MachO::InterfaceFile &Symbols;
  llvm::MachO::TargetList Targets;
  StringSet *StringSymbols;
  const llvm::DataLayout &DataLayout;

  const UniversalLinkageInfo &UniversalLinkInfo;
  ModuleDecl *SwiftModule;
  const TBDGenOptions &Opts;

private:
  void addSymbol(StringRef name, llvm::MachO::SymbolKind kind =
                                     llvm::MachO::SymbolKind::GlobalSymbol);

  void addSymbol(SILDeclRef declRef);

  void addSymbol(LinkEntity entity);

  void addConformances(DeclContext *DC);

  void addDispatchThunk(SILDeclRef declRef);

  void addMethodDescriptor(SILDeclRef declRef);

  void addProtocolRequirementsBaseDescriptor(ProtocolDecl *proto);
  void addAssociatedTypeDescriptor(AssociatedTypeDecl *assocType);
  void addAssociatedConformanceDescriptor(AssociatedConformance conformance);
  void addBaseConformanceDescriptor(BaseConformance conformance);

  // SWIFT_ENABLE_TENSORFLOW
  /// Adds the symbol for the linear map function of the given kind associated
  /// with the given original function and parameter indices.
  void addAutoDiffLinearMapFunction(AbstractFunctionDecl *original,
                                    IndexSubset *parameterIndices,
                                    AutoDiffLinearMapKind kind);

  /// Adds the symbol for the autodiff function of the given kind associated
  /// with the given original function and parameter indices.
  void addAutoDiffDerivativeFunction(AbstractFunctionDecl *original,
                                     IndexSubset *parameterIndices,
                                     AutoDiffDerivativeFunctionKind kind);

  /// Adds the symbol for the differentiability witness associated with the
  /// given original function and parameter indices.
  void addDifferentiabilityWitness(AbstractFunctionDecl *original,
                                   IndexSubset *parameterIndices,
                                   GenericSignature derivativeGenericSignature);

  /// Adds symbols associated with the given original function and
  /// `@differentiable` attribute.
  void addDifferentiableAttr(AbstractFunctionDecl *original,
                             const DifferentiableAttr *attr);

  /// Adds symbols associated with the given original function and
  /// `@derivative` attribute.
  void addDerivativeAttr(AbstractFunctionDecl *original,
                         const DerivativeAttr *attr);

public:
  TBDGenVisitor(llvm::MachO::InterfaceFile &symbols,
                llvm::MachO::TargetList targets, StringSet *stringSymbols,
                const llvm::DataLayout &dataLayout,
                const UniversalLinkageInfo &universalLinkInfo,
                ModuleDecl *swiftModule, const TBDGenOptions &opts)
      : Symbols(symbols), Targets(targets), StringSymbols(stringSymbols),
        DataLayout(dataLayout), UniversalLinkInfo(universalLinkInfo),
        SwiftModule(swiftModule), Opts(opts) {}

  void addMainIfNecessary(FileUnit *file) {
    // HACK: 'main' is a special symbol that's always emitted in SILGen if
    //       the file has an entry point. Since it doesn't show up in the
    //       module until SILGen, we need to explicitly add it here.
    if (file->hasEntryPoint())
      addSymbol("main");
  }

  /// Adds the global symbols associated with the first file.
  void addFirstFileSymbols();

  void visitDefaultArguments(ValueDecl *VD, ParameterList *PL);

  void visitAbstractFunctionDecl(AbstractFunctionDecl *AFD);

  void visitAccessorDecl(AccessorDecl *AD);

  void visitNominalTypeDecl(NominalTypeDecl *NTD);

  void visitClassDecl(ClassDecl *CD);

  void visitConstructorDecl(ConstructorDecl *CD);

  void visitDestructorDecl(DestructorDecl *DD);

  void visitExtensionDecl(ExtensionDecl *ED);
  
  void visitFuncDecl(FuncDecl *FD);

  void visitProtocolDecl(ProtocolDecl *PD);

  void visitAbstractStorageDecl(AbstractStorageDecl *ASD);

  void visitVarDecl(VarDecl *VD);

  void visitEnumDecl(EnumDecl *ED);

  void visitEnumElementDecl(EnumElementDecl *EED);

  void visitDecl(Decl *D) {}
};
} // end namespace tbdgen
} // end namespace swift

#endif
