# Find libelf.

include (FindPackageHandleStandardArgs)

find_path(LIBELF_INCLUDE_DIRS
  NAMES libelf/libelf.h libelf.h
  HINTS ${LIBELF_ROOT}
  PATH_SUFFIXES include libelf/include)

find_library (LIBELF_LIBRARIES
  NAMES elf libelf
  HINTS ${LIBELF_ROOT}
  PATH_SUFFIXES lib libelf/lib)

find_package_handle_standard_args(LibElf DEFAULT_MSG LIBELF_INCLUDE_DIRS LIBELF_LIBRARIES)
mark_as_advanced(LIBELF_INCLUDE_DIRS LIBELF_LIBRARIES)
