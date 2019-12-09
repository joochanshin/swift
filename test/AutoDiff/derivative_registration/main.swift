// Verify that cross-file derivative registration works.

// RUN: %empty-directory(%t)
// RUN: %target-swift-frontend -emit-module -primary-file %S/../Inputs/derivative_registration_original_module.swift -emit-module-path %t/derivative_registration_original_module.swiftmodule
// RUN: %target-swift-frontend -I %t -emit-module -primary-file %S/../Inputs/derivative_registration_derivative_module.swift -emit-module-path %t/derivative_registration_derivative_module.swiftmodule
// RUN: %target-swift-emit-sil -I %t -emit-module %s

import derivative_registration_original_module
import derivative_registration_derivative_module

func x(_ x: Float) -> Float {
  return gradient(at: x, in: id)
}
