//===-- Dataset.swift -----------------------------------------*- swift -*-===//
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
// The dataset API.
//
//===----------------------------------------------------------------------===//

/// The default graph seed.
///
/// - Note: See TensorFlow's `python.framework.random_seed.DEFAULT_GRAPH_SEED`.
@usableFromInline let _defaultGraphSeed: Int64 = 87654321

/// Returns the local seeds an operation should use given an op-specific seed.
///
/// Given operation-specific seed, `seed`, this helper function returns two
/// seeds derived from graph-level and op-level seeds. Many random operations
/// internally use the two seeds to allow user to change the seed globally for a
/// graph, or for only specific operations.
///
/// - Note: See TensorFlow's `python.framework.random_seed.get_seed`.
///
// TODO: There's no support for TF's "global seed" yet, so we always use the
// default graph seed as the first seed. Need to investigate the best way to
// model TF's "global seed".
@usableFromInline @inline(__always)
func _tensorSeeds(_ seed: Tensor<Int64>) -> (Tensor<Int64>, Tensor<Int64>) {
  return (Tensor(_defaultGraphSeed), seed)
}

//===----------------------------------------------------------------------===//
// Single value dataset
//===----------------------------------------------------------------------===//

/// Represents a potentially large set of elements.
///
/// A `Dataset` can be used to represent an input pipeline as a
/// collection of element tensors.
@_fixed_layout
public struct Dataset<Element : TensorGroup> {
  @usableFromInline let _handle: VariantHandle

  @usableFromInline @inline(__always)
  internal init(_handle: VariantHandle) {
    self._handle = _handle
  }
}

public extension Dataset {
  @inlinable @inline(__always)
  init(randomSeed: Int64) {
    let (seed1, seed2) = _tensorSeeds(Tensor(randomSeed))
    self.init(
      _handle: #tfop("RandomDataset", seed1, seed2,
                     output_types$dtype: Element._typeList,
                     output_shapes: Element._unknownShapeList)
    )
  }
}

public extension Dataset {
  /// Creates a dataset from a batch of elements as a tensor.
  @inlinable @inline(__always)
  init(elements: Element) {
    // A dataset creation op only runs on TF CPU.
    self.init(
      _handle: #tfop(
        "TensorSliceDataset", [elements],
        Toutput_types$dtype: Element._typeList,
        output_shapes: Element._unknownShapeList
      )
    )
  }
}

extension Dataset : Sequence {
  public typealias Iterator = DatasetIterator<Element>

  /// Returns an iterator over the elements of this dataset.
  @inlinable @inline(__always)
  public func makeIterator() -> DatasetIterator<Element> {
    let resource: ResourceHandle =
      #tfop("AnonymousIterator", output_types$dtype: Element._typeList,
            output_shapes: Element._unknownShapeList)
    #tfop("MakeIterator", _handle, resource) as Void
    return DatasetIterator(_handle: resource)
  }
}

/// FIXME(SR-8684): @convention(tensorflow) types crash SILGen when their
/// parameters or results have generic parameters. This is blocking generic
/// higher-order dataset transformation functions.
public extension Dataset where Element == Tensor<Float> {
  @inlinable @inline(__always)
  func map(
    _ transform: @convention(tensorflow) (Element) -> Element
  ) -> Dataset {
    // FIXME(SR-8570): If we pass an empty Array<TensorHandle<T>> as
    // other_arguments and an empty Array<Any.Type> as Targuments, partitioning
    // won't recognize the attribute:
    //    error: unknown array attribute
    return Dataset(
      _handle: #tfop(
        "MapDataset", _handle, [Tensor<Int32>(0)], f: transform,
        Targuments$dtype: [Int32.tensorFlowDataType],
        output_types$dtype: Element._typeList,
        output_shapes: Element._unknownShapeList
      )
    )
  }

  @inlinable @inline(__always)
  func filter(
    _ isIncluded:
      @convention(tensorflow) (Element) -> Tensor<Bool>
  ) -> Dataset {
    // FIXME(SR-8570): If we pass an empty Array<TensorHandle<T>> as
    // other_arguments and an empty Array<Any.Type> as Targuments, partitioning
    // won't recognize the attribute:
    //    error: unknown array attribute
    return Dataset(
      _handle: #tfop(
        "FilterDataset", _handle, [Tensor<Int32>(0)],
        predicate: isIncluded, Targuments$dtype: [Int32.tensorFlowDataType],
        output_types$dtype: Element._typeList,
        output_shapes: Element._unknownShapeList
      )
    )
  }
}

public extension Dataset {
  @inlinable @inline(__always)
  func shuffled(
    sampleCount: Int64, randomSeed: Int64
  ) -> Dataset {
    let (seed1, seed2) = _tensorSeeds(Tensor(randomSeed))
    return Dataset(
      _handle: #tfop(
        "ShuffleDataset", _handle, Tensor<Int64>(sampleCount), seed1, seed2,
        output_types$dtype: Element._typeList,
        output_shapes: Element._unknownShapeList
      )
    )
  }

  @inlinable @inline(__always)
  func batched(_ batchSize: Int64) -> Dataset {
    return Dataset(
      _handle: #tfop(
        "BatchDataset", _handle, Tensor<Int64>(batchSize),
        output_types$dtype: Element._typeList,
        output_shapes: Element._unknownShapeList
      )
    )
  }
}

/// Represents the state of iterating through a `Dataset`.
@_fixed_layout
public struct DatasetIterator<Element : TensorGroup> {
  @usableFromInline let _handle: ResourceHandle

  @usableFromInline @inline(__always)
  internal init(_handle: ResourceHandle) {
    self._handle = _handle
  }
}

extension DatasetIterator : IteratorProtocol {
  // Advances to the next element and returns it, or nil if no next element
  // exists.
  @inlinable @inline(__always)
  public mutating func next() -> Element? {
    let optional: VariantHandle =
      #tfop("IteratorGetNextAsOptional", _handle,
            output_types$dtype: Element._typeList,
            output_shapes: Element._unknownShapeList)
    guard _TFGetScalarOrDie(#tfop("OptionalHasValue", optional)) else {
      return nil
    }
    return #tfop("OptionalGetValue", optional,
                 output_types$dtype: Element._typeList,
                 output_shapes: Element._unknownShapeList) as Element
  }
}

/// A 2-tuple-like struct that conforms to TensorGroup that represents the 
/// result type of a zip operation between two datasets.
public struct ZippedTensors<T: TensorGroup, U: TensorGroup> : TensorGroup {
  public var first: T
  public var second: U
}

// TODO(SR-9156): This does not work in graph mode.
@inlinable @inline(__always)
public func zip<T : TensorGroup, U : TensorGroup>(
  _ dataset1: Dataset<T>, _ dataset2: Dataset<U>
) -> Dataset<ZippedTensors<T, U>> {
  let handle: VariantHandle = #tfop(
     "ZipDataset", ZippedTensors(dataset1._handle, dataset2._handle),
     output_types$dtype: ZippedTensors<T, U>._typeList,
     output_shapes: ZippedTensors<T, U>._unknownShapeList)
  return Dataset(_handle: handle)
}
