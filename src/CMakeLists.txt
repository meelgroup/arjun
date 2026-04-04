# Copyright (c) 2017, Mate Soos
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
# THE SOFTWARE.

if(NOT WIN32)
    add_cxx_flag_if_supported("-Wno-bitfield-constant-conversion")
    #add_cxx_flag_if_supported("-Wduplicated-cond")
    #add_cxx_flag_if_supported("-Wduplicated-branches")
    add_cxx_flag_if_supported("-Wlogical-op")
    add_cxx_flag_if_supported("-Wrestrict")
    add_cxx_flag_if_supported("-Wnull-dereference")
    add_cxx_flag_if_supported("-Wjump-misses-init")
    add_cxx_flag_if_supported("-Wdouble-promotion")
    add_cxx_flag_if_supported("-Wshadow")
    add_cxx_flag_if_supported("-Wformat=2")
    add_cxx_flag_if_supported("-pedantic")
    #add_cxx_flag_if_supported("-Wdeprecated")
endif()

configure_file("${CMAKE_CURRENT_SOURCE_DIR}/GitSHA1.cpp.in" "${CMAKE_CURRENT_BINARY_DIR}/GitSHA1.cpp" @ONLY)

set(libfiles
    extend.cpp
    backward.cpp
    simplify.cpp
    minimize.cpp
    arjun.cpp
    puura.cpp
    unate_def.cpp
    autarky.cpp
    ccnr/ccnr.cpp
    ${CMAKE_CURRENT_BINARY_DIR}/GitSHA1.cpp
    manthan.cpp
    interpolant.cpp
)

if(EXTRA_SYNTH)
    list(APPEND libfiles manthan_learn.cpp)
endif()

add_library(arjun ${libfiles})

target_include_directories(arjun
  PRIVATE
    ${PROJECT_SOURCE_DIR}
    ${CMAKE_CURRENT_BINARY_DIR}
    ${CMAKE_CURRENT_SOURCE_DIR}
  PUBLIC
    $<BUILD_INTERFACE:${PROJECT_BINARY_DIR}/include>
)

if(EXTRA_SYNTH)
    target_include_directories(arjun
        PRIVATE
            ${ARMADILLO_INCLUDE_DIRS}
            ${MLPACK_INCLUDE_DIR}
    )
    target_link_libraries(arjun PRIVATE EvalMaxSAT)
endif()

target_link_libraries(arjun
  PUBLIC
    PkgConfig::GMP
    PkgConfig::MPFR
    cryptominisat5
    sbva
    cadical
    treedecomp
)

set_target_properties(arjun PROPERTIES
    VERSION ${PROJECT_VERSION_MAJOR}.${PROJECT_VERSION_MINOR}
    SOVERSION ${PROJECT_VERSION_MAJOR}.${PROJECT_VERSION_MINOR}
)

add_executable(arjun-bin main.cpp synth.cpp)
add_executable(arjun-example example.cpp)
add_executable(test-synth test-synth.cpp)

target_link_libraries(arjun-bin PRIVATE arjun)
target_link_libraries(arjun-example PRIVATE arjun)
target_link_libraries(test-synth PRIVATE arjun cadical cryptominisat5)

target_include_directories(arjun-bin PRIVATE
    ${PROJECT_SOURCE_DIR}
    ${CMAKE_CURRENT_SOURCE_DIR}
)
target_include_directories(arjun-example PRIVATE
    ${PROJECT_SOURCE_DIR}
    ${CMAKE_CURRENT_SOURCE_DIR}
)
target_include_directories(test-synth PRIVATE
    ${PROJECT_SOURCE_DIR}
    ${CMAKE_CURRENT_SOURCE_DIR}
)

if(ZLIB_FOUND)
    foreach(tgt arjun-bin arjun-example test-synth)
        target_include_directories(${tgt} PRIVATE ${ZLIB_INCLUDE_DIR})
        target_link_libraries(${tgt} PRIVATE ${ZLIB_LIBRARY})
    endforeach()
endif()

if(CMAKE_SYSTEM_NAME STREQUAL "Emscripten")
    set_target_properties(arjun-bin PROPERTIES
      OUTPUT_NAME arjun
      RUNTIME_OUTPUT_DIRECTORY ${PROJECT_BINARY_DIR}
      INSTALL_RPATH_USE_LINK_PATH TRUE
    )
    target_link_options(arjun-bin PRIVATE
      "SHELL:-s WASM=1"
      "SHELL:-s ALLOW_MEMORY_GROWTH=1"
      "SHELL:-s STACK_SIZE=10MB"
      "SHELL:-s EXPORTED_RUNTIME_METHODS='[\"callMain\", \"ccall\", \"cwrap\", \"FS\", \"print\"]'"
      "SHELL:-s FORCE_FILESYSTEM=1"
    )
else()
    set_target_properties(arjun-bin PROPERTIES
        OUTPUT_NAME arjun
        RUNTIME_OUTPUT_DIRECTORY ${PROJECT_BINARY_DIR}
        INSTALL_RPATH_USE_LINK_PATH TRUE)
endif()

set_target_properties(arjun-example PROPERTIES
    OUTPUT_NAME example
    RUNTIME_OUTPUT_DIRECTORY ${PROJECT_BINARY_DIR}
    INSTALL_RPATH_USE_LINK_PATH TRUE)

set_target_properties(test-synth PROPERTIES
    OUTPUT_NAME test-synth
    RUNTIME_OUTPUT_DIRECTORY ${PROJECT_BINARY_DIR}
    INSTALL_RPATH_USE_LINK_PATH TRUE)

arjun_add_public_header(arjun ${CMAKE_CURRENT_SOURCE_DIR}/arjun.h)

# Ensure headers from sub-builds are copied before we compile against them.
foreach(_dep_copy_target
        CopyPublicHeaders_cryptominisat5
        CopyPublicHeaders_sbva
        CopyPublicHeaders_treedecomp)
    if(TARGET ${_dep_copy_target})
        foreach(_tgt arjun arjun-bin arjun-example test-synth)
            add_dependencies(${_tgt} ${_dep_copy_target})
        endforeach()
    endif()
endforeach()

# Public headers are fully known now; the CopyPublicHeaders target below reads
# this property, so it must be set before that target is created.
get_target_property(arjun_public_headers arjun PUBLIC_HEADER)

# -----------------------------------------------------------------------------
# Copy public headers into build directory include directory.
# The arjunConfig.cmake we generate in the build directory depends on
# this.
# -----------------------------------------------------------------------------
set(HEADER_DEST "${PROJECT_BINARY_DIR}/include/arjun")
add_custom_target(CopyPublicHeaders_arjun ALL)
foreach(public_header ${arjun_public_headers})
    get_filename_component(HEADER_NAME ${public_header} NAME)
    add_custom_command(TARGET CopyPublicHeaders_arjun PRE_BUILD
                       COMMAND ${CMAKE_COMMAND} -E make_directory
                               "${HEADER_DEST}"
                       COMMAND ${CMAKE_COMMAND} -E echo
                       "Copying ${HEADER_NAME} to ${HEADER_DEST}"
                       COMMAND ${CMAKE_COMMAND} -E
                           copy_if_different
                           ${public_header}
                           "${HEADER_DEST}"
                      )
endforeach()

install(TARGETS arjun
    EXPORT ${ARJUN_EXPORT_NAME}
    LIBRARY DESTINATION "${CMAKE_INSTALL_LIBDIR}"
    ARCHIVE DESTINATION "${CMAKE_INSTALL_LIBDIR}"
    RUNTIME DESTINATION "${CMAKE_INSTALL_BINDIR}"
    PUBLIC_HEADER DESTINATION "${CMAKE_INSTALL_INCLUDEDIR}/arjun"
)

install(TARGETS arjun-bin
    EXPORT ${ARJUN_EXPORT_NAME}
    RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR}
)
