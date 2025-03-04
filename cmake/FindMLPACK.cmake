include(FindPkgConfig)
pkg_check_modules(PC_MLPACK "mlpack")

set(MLPACK_DEFINITIONS ${PC_MLPACK_CFLAGS_OTHER})

find_path(
    MLPACK_INCLUDE_DIR
    NAMES mlpack.hpp
    HINTS ${PC_MLPACK_INCLUDEDIR}
    PATHS ${CMAKE_INSTALL_PREFIX}/include
          /usr/local/include
          /usr/include
)
set(MLPACK_INCLUDE_DIRS ${MLPACK_INCLUDE_DIR})
set(MLPACK_PC_ADD_CFLAGS "-I${MLPACK_INCLUDE_DIR}")

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(MLPACK
  DEFAULT_MSG
  MLPACK_INCLUDE_DIR)
mark_as_advanced(MLPACKXX_LIBRARY MLPACK_LIBRARY MLPACK_INCLUDE_DIR)
