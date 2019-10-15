//===--- GenProto.cpp - Swift IR Generation for Protocols -----------------===//
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
//  This file implements IR generation for protocols in Swift.
//
//  Protocols serve two masters: generic algorithms and existential
//  types.  In either case, the size and structure of a type is opaque
//  to the code manipulating a value.  Local values of the type must
//  be stored in fixed-size buffers (which can overflow to use heap
//  allocation), and basic operations on the type must be dynamically
//  delegated to a collection of information that "witnesses" the
//  truth that a particular type implements the protocol.
//
//  In the comments throughout this file, three type names are used:
//    'B' is the type of a fixed-size buffer
//    'T' is the type which implements a protocol
//    'W' is the type of a witness to the protocol
//
//===----------------------------------------------------------------------===//

#include "swift/AST/ASTContext.h"
#include "swift/AST/CanTypeVisitor.h"
#include "swift/AST/Types.h"
#include "swift/AST/Decl.h"
#include "swift/AST/GenericEnvironment.h"
#include "swift/AST/LazyResolver.h"
#include "swift/AST/IRGenOptions.h"
#include "swift/AST/PrettyStackTrace.h"
#include "swift/AST/SubstitutionMap.h"
#include "swift/ClangImporter/ClangModule.h"
#include "swift/IRGen/Linking.h"
#include "swift/SIL/SILDeclRef.h"
#include "swift/SIL/SILDefaultWitnessTable.h"
#include "swift/SIL/SILModule.h"
#include "swift/SIL/SILValue.h"
#include "swift/SIL/SILWitnessTable.h"
#include "swift/SIL/SILWitnessVisitor.h"
#include "swift/SIL/TypeLowering.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"

#include "CallEmission.h"
#include "ConformanceDescription.h"
#include "ConstantBuilder.h"
#include "EnumPayload.h"
#include "Explosion.h"
#include "FixedTypeInfo.h"
#include "Fulfillment.h"
#include "GenArchetype.h"
#include "GenCast.h"
#include "GenClass.h"
#include "GenEnum.h"
#include "GenHeap.h"
#include "GenMeta.h"
#include "GenOpaque.h"
#include "GenPoly.h"
#include "GenType.h"
#include "GenericRequirement.h"
#include "IRGenDebugInfo.h"
#include "IRGenFunction.h"
#include "IRGenMangler.h"
#include "IRGenModule.h"
#include "MetadataPath.h"
#include "MetadataRequest.h"
#include "NecessaryBindings.h"
#include "ProtocolInfo.h"
#include "TypeInfo.h"

#include "GenProto.h"

using namespace swift;
using namespace irgen;

// SWIFT_ENABLE_TENSORFLOW
void IRGenModule::emitSILDifferentiabilityWitness(
    SILDifferentiabilityWitness *dw) {
  if (isAvailableExternally(dw->getLinkage()))
    return;

  // Ensure that relatively-referenced symbols for witness thunks are collocated
  // in the same LLVM module.
  IRGen.ensureRelativeSymbolCollocation(*dw);

  auto key = dw->getKey();

  // Build the witness table.
  ConstantInitBuilder builder(*this);
  auto diffWitnessContents = builder.beginStruct();
  auto *origFnAddr = getAddrOfSILFunction(dw->getOriginalFunction(), NotForDefinition);
  auto *jvpFnAddr = getAddrOfSILFunction(dw->getJVP(), NotForDefinition);
  auto *vjpFnAddr = getAddrOfSILFunction(dw->getVJP(), NotForDefinition);
  llvm::errs() << "DIFF WITNESS REFERENCES\n";
  origFnAddr->dump();
  jvpFnAddr->dump();
  vjpFnAddr->dump();
  diffWitnessContents.addRelativeAddress(origFnAddr);
  diffWitnessContents.addRelativeAddress(jvpFnAddr);
  diffWitnessContents.addRelativeAddress(vjpFnAddr);
  auto diffWitnessGlobal =
    diffWitnessContents.finishAndCreateGlobal("differentiability_witness",
                                              getPointerAlignment(),
                                              /*constant*/ true);
  llvm::errs() << "DIFF WITNESS GLOBAL\n";
  diffWitnessGlobal->dump();
  // getAddrOfDifferentiabilityWitness(<#SILFunction *original#>, <#const AutoDiffConfig config#>)
#if 0
  WitnessTableBuilder wtableBuilder(*this, wtableContents, wt);
  wtableBuilder.build();
#endif

#if 0
  SmallVector<llvm::Constant *, 4> resilientWitnesses;
  // Collect the resilient witnesses to go into the conformance descriptor.
  wtableBuilder.collectResilientWitnesses(resilientWitnesses);

  // Produce the initializer value.
  auto initializer = wtableContents.finishAndCreateFuture();

  bool isDependent = isDependentConformance(conf);

  llvm::GlobalVariable *global = nullptr;
  unsigned tableSize;
  if (!isResilientConformance(conf)) {
    global = cast<llvm::GlobalVariable>(
      (isDependent && conf->getDeclContext()->isGenericContext())
        ? getAddrOfWitnessTablePattern(cast<NormalProtocolConformance>(conf),
                                       initializer)
        : getAddrOfWitnessTable(conf, initializer));
    global->setConstant(isConstantWitnessTable(wt));
    global->setAlignment(getWitnessTableAlignment().getValue());
    tableSize = wtableBuilder.getTableSize();
  } else {
    initializer.abandon();
    tableSize = 0;
  }

  // Collect the information that will go into the protocol conformance
  // descriptor.
  ConformanceDescription description(conf, wt, global, tableSize,
                                     wtableBuilder.getTablePrivateSize(),
                                     isDependent);

  // Build the instantiation function, we if need one.
  description.instantiationFn = wtableBuilder.buildInstantiationFunction();
  description.resilientWitnesses = std::move(resilientWitnesses);

  // Record this conformance descriptor.
  addProtocolConformance(std::move(description));

  IRGen.noteUseOfTypeContextDescriptor(conf->getType()->getAnyNominal(),
                                       RequireMetadata);
#endif
}
// SWIFT_ENABLE_TENSORFLOW END
