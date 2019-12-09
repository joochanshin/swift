// Verify that cross-file derivative registration works.

// RUN: %empty-directory(%t)
// RUN: %target-swift-frontend -emit-module -primary-file %S/../Inputs/derivative_registration_original_module.swift -emit-module-path %t/derivative_registration_original_module.swiftmodule
// RUN: %target-swift-frontend -I %t -emit-module -primary-file %S/../Inputs/derivative_registration_derivative_module.swift -emit-module-path %t/derivative_registration_derivative_module.swiftmodule
// RUN: %target-swift-frontend -I %t -emit-module -primary-file %S/../Inputs/derivative_registration_derivative_module2.swift -emit-module-path %t/derivative_registration_derivative_module2.swiftmodule
// RUN: %target-swift-emit-sil -I %t -emit-module %s

import derivative_registration_original_module
import derivative_registration_derivative_module
import derivative_registration_derivative_module2

func x(_ x: Float) -> Float {
  // TODO: Check which derivative for `id` is used:
  // - The one from `derivative_registration_derivative_module`, or
  // - The one from `derivative_registration_derivative_module2`.
  return gradient(at: x, in: id)
}
