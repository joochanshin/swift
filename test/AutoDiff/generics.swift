// RUN: %target-swift-frontend -emit-sil -verify %s

struct Tensor<T : VectorNumeric> : VectorNumeric, Differentiable {
  var value: Float
  init(_ value: Float) { self.value = value }
}

func genericParameter<T : FloatingPoint & Differentiable>(_ x: Tensor<T>) -> Float {
  return x.value + x.value
}
_ = pullback(at: Tensor<Float>(1), in: genericParameter)

func generic<T : FloatingPoint & Differentiable>(_ x: Tensor<T>) -> Tensor<T> {
  return Tensor(x.value + x.value)
}
_ = pullback(at: Tensor<Float>(1), in: generic)

@differentiable(vjp: vjpUnmetRequirements where T : BinaryInteger)
func unmetRequirements<T : FloatingPoint & Differentiable>(_ x: Tensor<T>) -> Tensor<T> {
  return Tensor(x.value + x.value)
}
func vjpUnmetRequirements<T : FloatingPoint & Differentiable & BinaryInteger>(_ x: Tensor<T>) -> (Tensor<T>, (Tensor<T>) -> Tensor<T>) {
  return (x, { $0 })
}
// _ = pullback(at: Tensor<Float>(1), in: generic)

// TODO: add more tests.
