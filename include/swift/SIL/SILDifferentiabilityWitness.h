//===--- SILDifferentiabilityWitness.h - Differentiability witnesses ------===//
//
// This source file is part of the Swift.org open source project
//
// Copyright (c) 2014 - 2019 Apple Inc. and the Swift project authors
// Licensed under Apache License v2.0 with Runtime Library Exception
//
// See https://swift.org/LICENSE.txt for license information
// See https://swift.org/CONTRIBUTORS.txt for the list of Swift project authors
//
//===----------------------------------------------------------------------===//
//
// This file defines the SILDifferentiabilityWitness class, which maps an
// original SILFunction and derivative configuration (parameter indices, result
// indices, derivative generic signature) to derivative functions (JVP and VJP).
//
// SIL differentiability witnesses are generated from the `@differentiable`
// and `@differentiating` attributes AST declaration attributes.
// Differentiability witnesses are canonicalized by the differentiation SIL
// transform, which fills in missing derivative functions. Canonical
// differentiability witnesses from other modules can be deserialized to look up
// derivative functions.
//
//===----------------------------------------------------------------------===//

#ifndef SWIFT_SIL_SILDIFFERENTIABILITYWITNESS_H
#define SWIFT_SIL_SILDIFFERENTIABILITYWITNESS_H

#include "swift/AST/Attr.h"
#include "swift/AST/AutoDiff.h"
#include "swift/AST/GenericSignature.h"
#include "swift/SIL/SILAllocated.h"
#include "llvm/ADT/ilist_node.h"
#include "llvm/ADT/ilist.h"

namespace swift {

class SILPrintContext;

class SILDifferentiabilityWitness
    : public llvm::ilist_node<SILDifferentiabilityWitness>,
      public SILAllocated<SILDifferentiabilityWitness>
{
private:
  /// The module which contains the differentiability witness.
  SILModule &module;
  /// The linkage of the differentiability witness.
  SILLinkage linkage;
  /// The original function.
  StringRef originalFunctionName;
  CanSILFunctionType originalFunctionType;
  /// The autodiff configuration: parameter indices, result indices, derivative
  /// generic signature (optional).
  AutoDiffConfig config;
  /// The JVP (Jacobian-vector products) derivative function.
  StringRef jvpFunctionName;
  CanSILFunctionType jvpFunctionType;
  /// The VJP (vector-Jacobian products) derivative function.
  StringRef vjpFunctionName;
  CanSILFunctionType vjpFunctionType;
  /// Whether or not this differentiability witness is serialized, which allows
  /// devirtualization from another module.
  bool serialized;
  /// The AST `@differentiable` or `@differentiating` attribute from which the
  /// differentiability witness is generated. Used for diagnostics.
  /// Null if the differentiability witness is parsed from SIL or if it is
  /// deserialized.
  DeclAttribute *attribute = nullptr;

  SILDifferentiabilityWitness(SILModule &module, SILLinkage linkage,
                              StringRef originalFunctionName,
                              CanSILFunctionType originalFunctionType,
                              IndexSubset *parameterIndices,
                              IndexSubset *resultIndices,
                              GenericSignature *derivativeGenSig,
                              StringRef jvpFunctionName,
                              CanSILFunctionType jvpFunctionType,
                              StringRef vjpFunctionName,
                              CanSILFunctionType vjpFunctionType,
                              bool isSerialized, DeclAttribute *attribute)
    : module(module), linkage(linkage), originalFunctionName(originalFunctionName),
      originalFunctionType(originalFunctionType),
      config(parameterIndices, resultIndices, derivativeGenSig),
      jvpFunctionName(jvpFunctionName), jvpFunctionType(jvpFunctionType),
      vjpFunctionName(vjpFunctionName), vjpFunctionType(vjpFunctionType),
      serialized(isSerialized), attribute(attribute) {}

public:
  static SILDifferentiabilityWitness *create(
      SILModule &module, SILLinkage linkage,
      StringRef originalFunctionName,
      CanSILFunctionType originalFunctionType,
      IndexSubset *parameterIndices, IndexSubset *resultIndices,
      GenericSignature *derivativeGenSig,
      StringRef jvpFunctionName,
      CanSILFunctionType jvpFunctionType,
      StringRef vjpFunctionName,
      CanSILFunctionType vjpFunctionType,
      bool isSerialized, DeclAttribute *attribute = nullptr);

  SILDifferentiabilityWitnessKey getKey() const;
  SILModule &getModule() const { return module; }
  SILLinkage getLinkage() const { return linkage; }
  StringRef getOriginalFunctionName() const { return originalFunctionName; }
  CanSILFunctionType getOriginalFunctionType() const { return originalFunctionType; }
  const AutoDiffConfig &getConfig() const { return config; }
  IndexSubset *getParameterIndices() const {
    return config.parameterIndices;
  }
  IndexSubset *getResultIndices() const {
    return config.resultIndices;
  }
  GenericSignature *getDerivativeGenericSignature() const {
    return config.derivativeGenericSignature;
  }
  StringRef getJVPFunctionName() const { return jvpFunctionName; }
  CanSILFunctionType getJVPFunctionType() const { return jvpFunctionType; }
  StringRef getVJPFunctionName() const { return vjpFunctionName; }
  CanSILFunctionType getVJPFunctionType() const { return vjpFunctionType; }
#if 0
  SILFunction *getDerivative(AutoDiffDerivativeFunctionKind kind) const {
    switch (kind) {
    case AutoDiffDerivativeFunctionKind::JVP: return jvp;
    case AutoDiffDerivativeFunctionKind::VJP: return vjp;
    }
  }
#endif
#if 0
  void setJVP(SILFunction *jvp) { this->jvp = jvp; }
  void setVJP(SILFunction *vjp) { this->vjp = vjp; }
  void setDerivative(AutoDiffDerivativeFunctionKind kind,
                     SILFunction *derivative) {
    switch (kind) {
    case AutoDiffDerivativeFunctionKind::JVP: jvp = derivative; break;
    case AutoDiffDerivativeFunctionKind::VJP: vjp = derivative; break;
    }
  }
#endif
  bool isSerialized() const { return serialized; }
  DeclAttribute *getAttribute() const { return attribute; }

  /// Verify that the differentiability witness is well-formed.
  void verify(const SILModule &module) const;

  void print(llvm::raw_ostream &os, bool verbose = false) const;
  void dump() const;
};

} // end namespace swift

namespace llvm {

//===----------------------------------------------------------------------===//
// ilist_traits for SILDifferentiabilityWitness
//===----------------------------------------------------------------------===//

template <>
struct ilist_traits<::swift::SILDifferentiabilityWitness>
    : public ilist_node_traits<::swift::SILDifferentiabilityWitness> {
  using SILDifferentiabilityWitness = ::swift::SILDifferentiabilityWitness;

public:
  static void deleteNode(SILDifferentiabilityWitness *DW) {
    DW->~SILDifferentiabilityWitness();
  }

private:
  void createNode(const SILDifferentiabilityWitness &);
};

} // namespace llvm

#endif // SWIFT_SIL_SILDIFFERENTIABILITYWITNESS_H
