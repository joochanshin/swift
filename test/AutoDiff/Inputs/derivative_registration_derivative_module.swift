import derivative_registration_original_module

@derivative(of: id)
func vjpId(_ x: Float) -> (value: Float, pullback: (Float) -> Float) {
  return (id(x), { $0 })
}
