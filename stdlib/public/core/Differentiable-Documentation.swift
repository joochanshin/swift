public protocol Differentiable {
  /// The tangent bundle of this differentiable manifold.
  associatedtype TangentVector : AdditiveArithmetic & Differentiable
    where TangentVector.TangentVector == TangentVector,
          TangentVector.CotangentVector == CotangentVector,
          TangentVector.AllDifferentiableVariables == TangentVector
  /// The cotangent bundle of this differentiable manifold.
  associatedtype CotangentVector : AdditiveArithmetic & Differentiable
    where CotangentVector.TangentVector == CotangentVector,
          CotangentVector.CotangentVector == TangentVector,
          CotangentVector.AllDifferentiableVariables == CotangentVector
  /// The type of all differentiable variables in this type.
  associatedtype AllDifferentiableVariables : Differentiable
    where AllDifferentiableVariables.AllDifferentiableVariables ==
              AllDifferentiableVariables,
          AllDifferentiableVariables.TangentVector == TangentVector,
          AllDifferentiableVariables.CotangentVector == CotangentVector

  /// All differentiable variables in this value.
  var allDifferentiableVariables: AllDifferentiableVariables { get }

  /// Returns `self` moved along the value space towards the given tangent
  /// vector. In Riemannian geometry (mathematics), this represents an
  /// exponential map.
  func moved(along direction: TangentVector) -> Self

  /// Convert a cotangent vector to its corresponding tangent vector.
  func tangentVector(from cotangent: CotangentVector) -> TangentVector
}
