#===--- CMakeLists.txt - Build the TensorFlow high-level APIs library -----===#
#
# This source file is part of the Swift.org open source project
#
# Copyright (c) 2014 - 2017 Apple Inc. and the Swift project authors
# Licensed under Apache License v2.0 with Runtime Library Exception
#
# See https://swift.org/LICENSE.txt for license information
# See https://swift.org/CONTRIBUTORS.txt for the list of Swift project authors
#
#===-----------------------------------------------------------------------===#
#
# SWIFT_ENABLE_TENSORFLOW
#
#===-----------------------------------------------------------------------===#

if(NOT SWIFT_ENABLE_TENSORFLOW)
  return()
endif()

# If high-level API directory does not exist, return.
if(NOT TENSORFLOW_SWIFT_APIS)
  return()
endif()

message(STATUS "Building TensorFlow.")

set(CMAKE_BUILD_WITH_INSTALL_RPATH TRUE)

set(SOURCES)

# Copy TensorFlow high-level API sources, if they exists.
message(STATUS "Using TensorFlow high-level APIs? ${TENSORFLOW_SWIFT_APIS}")
file(GLOB_RECURSE TENSORFLOW_SWIFT_API_SOURCES
  "${TENSORFLOW_SWIFT_APIS}/Sources/*.swift")
message(STATUS "Using TensorFlow high-level APIs.")
message(STATUS "HIGH LEVEL API SOURCES: ${TENSORFLOW_SWIFT_API_SOURCES}")
list(APPEND SOURCES "${TENSORFLOW_SWIFT_API_SOURCES}")

# When Python exists, NumpyConversion.swift imports it, so it must be
# available at link time.
set(TENSORFLOW_DEPENDS_PYTHON)
if(SWIFT_PYTHON_EXISTS)
  list(APPEND TENSORFLOW_DEPENDS_PYTHON SWIFT_MODULE_DEPENDS Python)
endif()

# FIXME: Compilation crashes when "-Xfrontend -enable-resilience" is enabled.
# Manually remove these flags for now.
message(STATUS "SWIFT COMPILE FLAGS: ${SWIFT_RUNTIME_SWIFT_COMPILE_FLAGS}")
list(FIND SWIFT_RUNTIME_SWIFT_COMPILE_FLAGS "-enable-resilience" ENABLE_RESILIENCE_FLAG_INDEX)
if(NOT ENABLE_RESILIENCE_FLAG_INDEX EQUAL -1)
  list(REMOVE_AT SWIFT_RUNTIME_SWIFT_COMPILE_FLAGS $ENABLE_RESILIENCE_FLAG_INDEX - 1) # remove "-Xfrontend"
  list(REMOVE_AT SWIFT_RUNTIME_SWIFT_COMPILE_FLAGS $ENABLE_RESILIENCE_FLAG_INDEX)     # remove "-enable-resilience"
endif()
message(STATUS "NEW SWIFT COMPILE FLAGS: ${SWIFT_RUNTIME_SWIFT_COMPILE_FLAGS}")

add_swift_target_library(swiftTensorFlow ${SWIFT_STDLIB_LIBRARY_BUILD_TYPES} IS_STDLIB
  "${SOURCES}"

  INCORPORATE_OBJECT_LIBRARIES swiftCTensorFlow
  TARGET_SDKS OSX LINUX
  SWIFT_MODULE_DEPENDS TensorFlowCore
  # SWIFT_MODULE_DEPENDS SwiftOnoneSupport
  # SWIFT_MODULE_DEPENDS_IOS Darwin
  # SWIFT_MODULE_DEPENDS_OSX Darwin
  # SWIFT_MODULE_DEPENDS_TVOS Darwin
  # SWIFT_MODULE_DEPENDS_WATCHOS Darwin
  # SWIFT_MODULE_DEPENDS_LINUX Glibc
  # SWIFT_MODULE_DEPENDS_FREEBSD Glibc
  # SWIFT_MODULE_DEPENDS_CYGWIN Glibc
  # SWIFT_MODULE_DEPENDS_HAIKU Glibc
  ${TENSORFLOW_DEPENDS_PYTHON}
  SWIFT_COMPILE_FLAGS "${SWIFT_RUNTIME_SWIFT_COMPILE_FLAGS}"
  LINK_FLAGS "${SWIFT_RUNTIME_SWIFT_LINK_FLAGS}"
  INSTALL_IN_COMPONENT stdlib
  EXTRA_RPATHS "${SWIFT_TENSORFLOW_TARGET_LIB_DIR}")
