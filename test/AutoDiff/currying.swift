// RUN: %target-run-simple-swift

import StdlibUnittest

var CurryingAutodiffTests = TestSuite("CurryingAutodiff")

CurryingAutodiffTests.test("StructMember") {
  struct A {
    @differentiable(wrt: (value))
    func v(_ value: Float) -> Float { return value * value }
  }

  let a = A()
  // The line below implicitly constructs a curried function with type
  // `(A) -> (Float) -> Float`, which is applied to `a`:
  let g: @differentiable (Float) -> Float = a.v

  expectEqual(6.0, Float(3.0).gradient(in: g))
}

runAllTests()
