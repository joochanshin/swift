//===-- KeyPathIterable.swift ---------------------------------*- swift -*-===//
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
// This file defines the KeyPathIterable protocol.
//
//===----------------------------------------------------------------------===//

//===----------------------------------------------------------------------===//
// KeyPathIterable
//===----------------------------------------------------------------------===//

/// A type that provides key paths to all of its stored properties.
public protocol KeyPathIterable {
  /// A type that can represent a collection of all key paths of this type.
  associatedtype AllKeyPaths : RangeReplaceableCollection where
    AllKeyPaths.Element == PartialKeyPath<Self>

  /// An array of key paths to the stored properties of this type.
  var keyPaths: AllKeyPaths { get }

  /// An array of key paths to all stored properties of the stored properties of
  /// this type that conform to `KeyPathIterable`.
  var nestedKeyPaths: AllKeyPaths { get }
}

public extension KeyPathIterable {
  /// An array of key paths to all stored properties contained within this type.
  @inlinable
  var allKeyPaths: AllKeyPaths {
    return keyPaths + nestedKeyPaths
  }

  /// Returns an array of key paths to all stored properties contained within
  /// this type, with the specified type.
  @inlinable
  func allKeyPaths<T>(to _: T.Type) -> [KeyPath<Self, T>] {
    return keyPaths(to: T.self) + nestedKeyPaths(to: T.self)
  }

  /// Returns an array of key paths to all mutable stored properties contained
  /// within this type, with the specified type.
  @inlinable
  func allWritableKeyPaths<T>(to _: T.Type) -> [WritableKeyPath<Self, T>] {
    return writableKeyPaths(to: T.self) + writableNestedKeyPaths(to: T.self)
  }

  /// Returns an array of key paths to the stored properties of this type, with
  /// the specified type.
  @inlinable
  func keyPaths<T>(to _: T.Type) -> [KeyPath<Self, T>] {
    return keyPaths.compactMap { $0 as? KeyPath<Self, T> }
  }

  /// Returns an array of key paths to all nested stored properties of this
  /// type, with the specified type.
  @inlinable
  func nestedKeyPaths<T>(to _: T.Type) -> [KeyPath<Self, T>] {
    return nestedKeyPaths.compactMap { $0 as? KeyPath<Self, T> }
  }

  /// Returns an array of key paths to the mutable stored properties of this
  /// type, with the specified type.
  @inlinable
  func writableKeyPaths<T>(to _: T.Type) -> [WritableKeyPath<Self, T>] {
    return keyPaths.compactMap { $0 as? WritableKeyPath<Self, T> }
  }

  /// Returns an array of key paths to all nested, mutable stored properties of
  /// this type, with the specified type.
  @inlinable
  func writableNestedKeyPaths<T>(to _: T.Type) -> [WritableKeyPath<Self, T>] {
    return nestedKeyPaths.compactMap { $0 as? WritableKeyPath<Self, T> }
  }
}

//===----------------------------------------------------------------------===//
// `Array` conformances
//===----------------------------------------------------------------------===//

extension Array : KeyPathIterable where Element : KeyPathIterable {
  public typealias AllKeyPaths = [PartialKeyPath<Array>]

  public var keyPaths: [PartialKeyPath<Array>] {
    return indices.map { \Array.[$0] }
  }

  public var nestedKeyPaths: [PartialKeyPath<Array>] {
    return indices.flatMap { index in
      return self[index].allKeyPaths.map { kp in
        // Note: this code is a long way of writing the following, which doesn't
        // type-check:
        // `(\Array.[index]).appending(path: $0)!`
        let rootFullKeyPath: WritableKeyPath<Array, Element> = \Array.[index]
        let rootKeyPath: PartialKeyPath<Array> = rootFullKeyPath
        return rootKeyPath.appending(path: kp)!
      }
    }
  }
}
