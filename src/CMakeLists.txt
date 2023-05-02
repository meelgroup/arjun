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

include_directories(${PROJECT_SOURCE_DIR})
include_directories(${LOUVAIN_COMMUNITIES_INCLUDE_DIRS})
include_directories(${CMAKE_CURRENT_BINARY_DIR})
include_directories(${Boost_INCLUDE_DIRS})
include_directories(${CRYPTOMINISAT5_INCLUDE_DIRS})

if (NOT WIN32)
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
    add_cxx_flag_if_supported("-Wextra-semi")
    add_cxx_flag_if_supported("-pedantic")
    #add_cxx_flag_if_supported("-Wdeprecated")
endif()

configure_file("${CMAKE_CURRENT_SOURCE_DIR}/GitSHA1.cpp.in" "${CMAKE_CURRENT_BINARY_DIR}/GitSHA1.cpp" @ONLY)

add_library(arjun
    backward.cpp
    simplify.cpp
    common.cpp
    arjun.cpp
    ${CMAKE_CURRENT_BINARY_DIR}/GitSHA1.cpp
)

if (louvain_communities_FOUND)
    target_link_libraries(arjun
        LINK_PUBLIC ${LOUVAIN_COMMUNITIES_LIBRARIES}
        LINK_PUBLIC ${CRYPTOMINISAT5_LIBRARIES}
    )
else()
    target_link_libraries(arjun
        LINK_PUBLIC ${CRYPTOMINISAT5_LIBRARIES}
    )
endif()


if (EMSCRIPTEN)
    add_executable(arjun-bin
        main_emscripten.cpp
    )

    set_target_properties(arjun-bin
        PROPERTIES
        OUTPUT_NAME arjun
        LINK_FLAGS "-s WASM=1 -s ALLOW_MEMORY_GROWTH=1 -s EXTRA_EXPORTED_RUNTIME_METHODS='[\"ccall\", \"cwrap\"]'  -s LINKABLE=1 -s EXPORT_ALL=1 --pre-js ${CMAKE_CURRENT_SOURCE_DIR}/pre.js"
    )

    SET_SOURCE_FILES_PROPERTIES(main_emscripten.cpp
        PROPERTIES COMPILE_FLAGS "-s WASM=1 -s ALLOW_MEMORY_GROWTH=1 -s EXTRA_EXPORTED_RUNTIME_METHODS='[\"ccall\", \"cwrap\"]'  -s LINKABLE=1 -s EXPORT_ALL=1"
    )
else()
    add_executable(arjun-bin
        main.cpp
    )

    add_executable(arjun-example
        example.cpp
    )

if (ARJUN_SERIALIZE)
    add_executable(solextend
        solextend.cpp
    )
endif()

    set(arjun_bin_exec_link_libs
        ${Boost_LIBRARIES}
    )
endif()

IF (ZLIB_FOUND)
    SET(arjun_bin_exec_link_libs ${arjun_bin_exec_link_libs} ${ZLIB_LIBRARY})
ENDIF()

set_target_properties(arjun PROPERTIES
    PUBLIC_HEADER "${arjun_public_headers}"
    VERSION ${PROJECT_VERSION_MAJOR}.${PROJECT_VERSION_MINOR}
    SOVERSION ${PROJECT_VERSION_MAJOR}.${PROJECT_VERSION_MINOR}
)

set_target_properties(arjun-bin PROPERTIES
    OUTPUT_NAME arjun
    RUNTIME_OUTPUT_DIRECTORY ${PROJECT_BINARY_DIR}
    INSTALL_RPATH_USE_LINK_PATH TRUE)


target_link_libraries(arjun-bin
    ${arjun_bin_exec_link_libs}
    arjun
)


set_target_properties(arjun-example PROPERTIES
    OUTPUT_NAME example
    RUNTIME_OUTPUT_DIRECTORY ${PROJECT_BINARY_DIR}
    INSTALL_RPATH_USE_LINK_PATH TRUE)


target_link_libraries(arjun-example
    ${arjun_bin_exec_link_libs}
    arjun
)

if (ARJUN_SERIALIZE)
set_target_properties(solextend PROPERTIES
    OUTPUT_NAME solextend
    RUNTIME_OUTPUT_DIRECTORY ${PROJECT_BINARY_DIR}
    INSTALL_RPATH_USE_LINK_PATH TRUE)

target_link_libraries(solextend
    LINK_PUBLIC ${CRYPTOMINISAT5_LIBRARIES}
    ${arjun_bin_exec_link_libs}
    arjun
)
endif()

arjun_add_public_header(
    arjun ${CMAKE_CURRENT_SOURCE_DIR}/arjun.h )

# -----------------------------------------------------------------------------
# Copy public headers into build directory include directory.
# The arjunConfig.cmake we generate in the build directory depends on
# this.
# -----------------------------------------------------------------------------
set(HEADER_DEST "${PROJECT_BINARY_DIR}/include/arjun")
add_custom_target(CopyPublicHeaders ALL)
get_target_property(arjun_public_headers arjun PUBLIC_HEADER)
foreach(public_header ${arjun_public_headers})
    get_filename_component(HEADER_NAME ${public_header} NAME)
    add_custom_command(TARGET CopyPublicHeaders PRE_BUILD
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
