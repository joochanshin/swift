# Find libdwarf.

include (FindPackageHandleStandardArgs)

find_path(LIBDWARF_INCLUDE_DIRS
  NAMES libdwarf/libdwarf.h libdwar.h
  HINTS ${LIBDWARF_ROOT}
  PATH_SUFFIXES include libdwarf/include)

find_library (LIBDWARF_LIBRARIES
  NAMES dwarf libdwarf
  HINTS ${LIBDWARF_ROOT}
  PATH_SUFFIXES lib libdwarf/lib)

find_package_handle_standard_args(LibDwarf DEFAULT_MSG LIBDWARF_INCLUDE_DIRS LIBDWARF_LIBRARIES)
mark_as_advanced(LIBDWARF_INCLUDE_DIRS LIBDWARF_LIBRARIES)
