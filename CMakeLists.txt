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

cmake_minimum_required(VERSION 3.12 FATAL_ERROR)

message(STATUS "LIB directory is '${CMAKE_INSTALL_LIBDIR}'")
message(STATUS "BIN directory is '${CMAKE_INSTALL_BINDIR}'")

if(POLICY CMP0022)
    cmake_policy(SET CMP0022 NEW)
endif()

if(POLICY CMP0048)
    cmake_policy(SET CMP0048 NEW)
endif()

if(POLICY CMP0046)
    cmake_policy(SET CMP0046 NEW)
endif()

if(POLICY CMP0026)
    cmake_policy(SET CMP0026 NEW)
endif()

# -----------------------------------------------------------------------------
# Make RelWithDebInfo the default build type if otherwise not set
# -----------------------------------------------------------------------------
set(build_types Debug Release RelWithDebInfo MinSizeRel)
if(NOT CMAKE_BUILD_TYPE)
    message(STATUS "You can choose the type of build, options are:${build_types}")
    set(CMAKE_BUILD_TYPE RelWithDebInfo CACHE STRING
        "Options are ${build_types}"
        FORCE
    )

    # Provide drop down menu options in cmake-gui
    set_property(CACHE CMAKE_BUILD_TYPE PROPERTY STRINGS ${build_types})
endif()
message(STATUS "Doing a ${CMAKE_BUILD_TYPE} build")

# -----------------------------------------------------------------------------
# Option to enable/disable assertions
# -----------------------------------------------------------------------------

# Filter out definition of NDEBUG from the default build configuration flags.
# We will add this ourselves if we want to disable assertions
foreach (build_config ${build_types})
    string(TOUPPER ${build_config} upper_case_build_config)
    foreach (language CXX C)
        set(VAR_TO_MODIFY "CMAKE_${language}_FLAGS_${upper_case_build_config}")
        string(REGEX REPLACE "(^| )[/-]D *NDEBUG($| )"
                             " "
                             replacement
                             "${${VAR_TO_MODIFY}}")
        #message("Original (${VAR_TO_MODIFY}) is ${${VAR_TO_MODIFY}} replacement is ${replacement}")
        set(${VAR_TO_MODIFY} "${replacement}" CACHE STRING "Default flags for ${build_config} configuration" FORCE)
    endforeach()
endforeach()

project (arjun)
set(CMAKE_CXX_EXTENSIONS OFF)
set(CMAKE_C_STANDARD 99)
set(CMAKE_CXX_STANDARD 20)
set(CMAKE_POSITION_INDEPENDENT_CODE ON)
enable_language( CXX )
enable_language( C )
include (GenerateExportHeader)
include (GNUInstallDirs)

# contains some library search cmake scripts
SET(CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/cmake)

# generate JSON file of compile commands -- useful for code extension
set(CMAKE_EXPORT_COMPILE_COMMANDS 1)

# static compilation
option(SYNTH "Also build synthesis" ON)
option(BUILD_SHARED_LIBS "Build the shared library" ON)
option(STATICCOMPILE "Compile to static executable" OFF)
if (STATICCOMPILE)
    set(BUILD_SHARED_LIBS OFF)
endif()

if ((${CMAKE_SYSTEM_NAME} MATCHES "Linux") OR (${CMAKE_SYSTEM_NAME} MATCHES "Darwin"))
    if(NOT BUILD_SHARED_LIBS)
        MESSAGE(STATUS "Compiling statically")
        if (${CMAKE_SYSTEM_NAME} MATCHES "Linux")
            set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -static")
        endif()
        SET(CMAKE_FIND_LIBRARY_SUFFIXES ".a")
    else()
        MESSAGE(STATUS "Compiling for dynamic library use")
    endif()
endif()

set(THREADS_PREFER_PTHREAD_FLAG ON)
find_package (Threads REQUIRED)
find_package (sbva REQUIRED)
message(STATUS "Found SBVA includes at: ${SBVA_INCLUDE_DIRS}")
find_package(GMP REQUIRED)
if (SYNTH)
    add_definitions(-DSYNTH)
    find_package(MLPACK REQUIRED)
    find_library(cadical
        PATHS ${CMAKE_CURRENT_SOURCE_DIR}/../cadical/build/
        NAMES cadical
        REQUIRED)
endif()

macro(add_sanitize_option flagname)
    SET(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${flagname}" )
endmacro()

option(SANITIZE "Use Clang sanitizers. You MUST use clang++ as the compiler for this to work" OFF)
if (SANITIZE)
    MESSAGE(WARNING " --Using clang sanitizers -- you MUST use clang++ or the compile WILL fail")
    add_compile_options("-fsanitize=address")
    add_link_options("-fsanitize=address")
    #    add_compile_options("-fsanitize=integer")
    add_compile_options("-fsanitize=undefined")
    add_compile_options("-fsanitize=null")
    add_compile_options("-fsanitize=alignment")
    #add_compile_options("-fno-sanitize-recover")
    add_compile_options("-fsanitize=return")
    add_compile_options("-fsanitize=bounds")
    # add_compile_options("-fsanitize=float-divide-by-zero")
    # add_compile_options("-fsanitize=integer-divide-by-zero")
    #    add_compile_options("-fsanitize=unsigned-integer-overflow")
    # add_compile_options("-fsanitize=signed-integer-overflow")
    add_compile_options("-fsanitize=bool")
    add_compile_options("-fsanitize=enum")
    add_compile_options("-fsanitize=float-cast-overflow")
    add_compile_options("$<$<CONFIG:RELWITHDEBINFO>:-D_GLIBCXX_ASSERTIONS>")
endif()

include(CheckCXXCompilerFlag)
macro(add_cxx_flag_if_supported flagname)
  check_cxx_compiler_flag("${flagname}" HAVE_FLAG_${flagname})

  if(HAVE_FLAG_${flagname})
    SET(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${flagname}" )
  endif()
endmacro()

option(ENABLE_ASSERTIONS "Build with assertions enabled" ON)
message(STATUS "build type is ${CMAKE_BUILD_TYPE}")
if(CMAKE_BUILD_TYPE STREQUAL "Release")
    set(ENABLE_ASSERTIONS OFF)
endif()

if (ENABLE_ASSERTIONS)
    # NDEBUG was already removed.
else()
    # Note this definition doesn't appear in the cache variables.
    add_definitions(-DNDEBUG)
    add_cxx_flag_if_supported("-fno-stack-protector")
    add_definitions(-D_FORTIFY_SOURCE=0)
endif()

# Note: O3 gives slight speed increase, 1 more solved from SAT Comp'14 @ 3600s
if (NOT MSVC)
    add_compile_options( -g)

    add_compile_options("$<$<CONFIG:RelWithDebInfo>:-O3>")

    add_compile_options("$<$<CONFIG:Release>:-O3>")
    add_compile_options("$<$<CONFIG:Release>:-g0>")
    add_compile_options("$<$<CONFIG:Release>:-DNDEBUG>")

    add_compile_options("$<$<CONFIG:DEBUG>:-O0>")

else()
    # see https://msdn.microsoft.com/en-us/library/fwkeyyhe.aspx for details
    # /ZI = include debug info
    # /Wall = all warnings

    add_compile_options("$<$<CONFIG:RELWITHDEBINFO>:/Ox>")
    add_compile_options("$<$<CONFIG:RELWITHDEBINFO>:/ZI>")

    add_compile_options("$<$<CONFIG:Release>:/Ox>")
    add_compile_options("$<$<CONFIG:Release>:/D>")
    add_compile_options("$<$<CONFIG:Release>:/NDEBUG>")
    add_compile_options("$<$<CONFIG:Release>:/ZI>")

    add_compile_options("$<$<CONFIG:DEBUG>:/Od>")

    if (STATICCOMPILE)
        # We statically link to reduce dependencies
        foreach(flag_var CMAKE_CXX_FLAGS CMAKE_CXX_FLAGS_DEBUG CMAKE_CXX_FLAGS_RELEASE CMAKE_CXX_FLAGS_MINSIZEREL CMAKE_CXX_FLAGS_RELWITHDEBINFO)
            # /MD -- Causes the application to use the multithread-specific and DLL-specific version of the run-time library.
            #        Defines _MT and _DLL and causes the compiler to place the library name MSVCRT.lib into the .obj file.
            if(${flag_var} MATCHES "/MD")
                string(REGEX REPLACE "/MD" "/MT" ${flag_var} "${${flag_var}}")
            endif(${flag_var} MATCHES "/MD")

            # /MDd	-- Defines _DEBUG, _MT, and _DLL and causes the application to use the debug multithread-specific and DLL-specific version of the run-time library.
            #          It also causes the compiler to place the library name MSVCRTD.lib into the .obj file.
            if(${flag_var} MATCHES "/MDd")
                string(REGEX REPLACE "/MDd" "/MTd" ${flag_var} "${${flag_var}}")
            endif(${flag_var} MATCHES "/MDd")
        endforeach(flag_var)

        # Creates a multithreaded executable (static) file using LIBCMT.lib.
        add_compile_options(/MT)
    endif()

    # buffers security check
    add_compile_options(/GS)

    # Proper warning level
    add_compile_options(/W1)

    # Disable STL used in DLL-boundary warning
    add_compile_options(/wd4251)
    add_compile_options(/D_CRT_SECURE_NO_WARNINGS)

    # Wall is MSVC's Weverything, so annoying unless used from the start
    # and with judiciously used warning disables
    # add_compile_options(/Wall)

    # /Za = only ansi C98 & C++11
    # /Za is not recommended for use, not tested, etc.
    # see: http://stackoverflow.com/questions/5489326/za-compiler-directive-does-not-compile-system-headers-in-vs2010
    # add_compile_options(/Za)

    add_compile_options(/fp:precise)

    # exception handling. s = The exception-handling model that catches C++ exceptions only and tells the compiler to assume that functions declared as extern "C" may throw an exception.
    # exception handling. c = If used with s (/EHsc), catches C++ exceptions only and tells the compiler to assume that functions declared as extern "C" never throw a C++ exception.
    add_compile_options(/EHsc)


    set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} /INCREMENTAL:NO")
    set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} /PDBCOMPRESS")
    set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} /STACK:1572864")

    #what does this do?
    set(DEF_INSTALL_CMAKE_DIR CMake)
endif()

option(ENABLE_TESTING "Enable testing" OFF)
option(ARJUN_SERIALIZE OFF)
if (ARJUN_SERIALIZE)
    add_definitions( -DARJUN_SERIALIZE )
endif()

# Use mold/sold linker if available
if(CMAKE_CXX_COMPILER_ID MATCHES "Clang|GNU" AND NOT EMSCRIPTEN)
  message(STATUS "Detected GCC/Clang, checking for mold/sold linker...")

  # Check for mold linker on general systems and ld64.mold on macOS
  if(APPLE)
    find_program(MOLD_LINKER ld64.mold)
  else()
    find_program(MOLD_LINKER mold)
  endif()

  if(MOLD_LINKER)
    message(STATUS "LINKER_TYPE set to ${CMAKE_LINKER_TYPE} for faster builds")
    list(APPEND CMAKE_MESSAGE_INDENT " ")
    message(STATUS "(set -DUSE_MOLD=OFF to disable)")
    list(POP_BACK CMAKE_MESSAGE_INDENT)
    if(APPLE)
      set(CMAKE_LINKER_TYPE SOLD)
    else()
      set(CMAKE_LINKER_TYPE MOLD)
    endif()
  else()
    message(STATUS "  -- No suitable mold linker found. Using default linker.")
  endif()
else()
  message(STATUS "Compiler is neither GCC nor Clang. Skipping mold linker check.")
endif()

if (NOT WIN32)
    add_cxx_flag_if_supported("-Wall")
    add_cxx_flag_if_supported("-Wextra")
    add_cxx_flag_if_supported("-Wunused")
    add_cxx_flag_if_supported("-Wsign-compare")
    add_cxx_flag_if_supported("-march=sandybridge")
    if (NOT CMAKE_BUILD_TYPE STREQUAL "Release")
        add_cxx_flag_if_supported("-fno-omit-frame-pointer")
        add_cxx_flag_if_supported("-g")
        add_cxx_flag_if_supported("-ggdb3")
    endif()
    add_cxx_flag_if_supported("-Wtype-limits")
    add_cxx_flag_if_supported("-Wuninitialized")
    add_cxx_flag_if_supported("-Wno-deprecated")
    add_cxx_flag_if_supported("-Wno-extra-semi")
    add_cxx_flag_if_supported("-Wstrict-aliasing")
    add_cxx_flag_if_supported("-Wpointer-arith")
    add_cxx_flag_if_supported("-Wheader-guard")
    if(NOT ENABLE_TESTING AND ${CMAKE_SYSTEM_NAME} MATCHES "Linux")
        add_cxx_flag_if_supported("-fvisibility=hidden")
    endif()
    add_cxx_flag_if_supported("-Wpointer-arith")
    add_cxx_flag_if_supported("-Wformat-nonliteral")
    add_cxx_flag_if_supported("-Winit-self")
    add_cxx_flag_if_supported("-Wparentheses")
    add_cxx_flag_if_supported("-Wunreachable-code")
    add_cxx_flag_if_supported("-msse4.2")
    add_cxx_flag_if_supported("-mpopcnt")

    # add_cxx_flag_if_supported("-flto") # slow compile and not enough benefits
    #add_cxx_flag_if_supported("-fno-exceptions")
endif()

set(DEF_INSTALL_CMAKE_DIR lib/cmake/arjun)
set(ARJUN_INSTALL_CMAKE_DIR ${DEF_INSTALL_CMAKE_DIR} CACHE PATH
    "Installation directory for arjun CMake files")

# -----------------------------------------------------------------------------
# Add GIT version
# -----------------------------------------------------------------------------
function(SetVersionNumber PREFIX VERSION_MAJOR VERSION_MINOR VERSION_PATCH)
  set(${PREFIX}_VERSION_MAJOR ${VERSION_MAJOR} PARENT_SCOPE)
  set(${PREFIX}_VERSION_MINOR ${VERSION_MINOR} PARENT_SCOPE)
  set(${PREFIX}_VERSION_PATCH ${VERSION_PATCH} PARENT_SCOPE)
  set(${PREFIX}_VERSION
        "${VERSION_MAJOR}.${VERSION_MINOR}.${VERSION_PATCH}"
        PARENT_SCOPE)
endfunction()

find_program (GIT_EXECUTABLE git)
if (GIT_EXECUTABLE)
  include(GetGitRevisionDescription)
  get_git_head_revision(GIT_REFSPEC GIT_SHA1)
  MESSAGE(STATUS "GIT hash found: ${GIT_SHA1}")
else()
  set(GIT_SHA "GIT-hash-notfound")
endif()
set(ARJUN_FULL_VERSION "2.6.1")

string(REPLACE "." ";" ARJUN_FULL_VERSION_LIST ${ARJUN_FULL_VERSION})
SetVersionNumber("PROJECT" ${ARJUN_FULL_VERSION_LIST})
MESSAGE(STATUS "PROJECT_VERSION: ${PROJECT_VERSION}")
MESSAGE(STATUS "PROJECT_VERSION_MAJOR: ${PROJECT_VERSION_MAJOR}")
MESSAGE(STATUS "PROJECT_VERSION_MINOR: ${PROJECT_VERSION_MINOR}")
MESSAGE(STATUS "PROJECT_VERSION_PATCH: ${PROJECT_VERSION_PATCH}")

option(EMSCRIPTEN "Generate only emscripten JS" OFF)
if (EMSCRIPTEN)
    set(BUILD_SHARED_LIBS ON)
    set(NOZLIB ON)
endif()

# ----------
# manpage
# ----------
if (${CMAKE_SYSTEM_NAME} MATCHES "Linux" AND NOT EMSCRIPTEN)
    find_program(HELP2MAN_FOUND help2man)
    if (HELP2MAN_FOUND)
        ADD_CUSTOM_TARGET(man_arjun
            ALL
            DEPENDS arjun-bin
        )

        ADD_CUSTOM_COMMAND(
            POST_BUILD
            TARGET man_arjun
            COMMAND help2man
            ARGS --version-string=${ARJUN_FULL_VERSION} --help-option="-h" $<TARGET_FILE:arjun-bin> -o ${CMAKE_CURRENT_BINARY_DIR}/arjun.1
        )

        INSTALL(
            FILES ${CMAKE_CURRENT_BINARY_DIR}/arjun.1
            DESTINATION ${CMAKE_INSTALL_PREFIX}/man/man1)

        message(STATUS "Manpage will be created and installed")
    else()
        MESSAGE(STATUS "Cannot find help2man, not creating manpage")
    endif()
else()
    MESSAGE(STATUS "Not on Linux, not creating manpage")
endif()

# -----------------------------------------------------------------------------
# Look for ZLIB (For reading zipped CNFs)
# -----------------------------------------------------------------------------
option(NOZLIB "Don't use zlib" OFF)

# cannot currently compile static zlib under Windows
if (NOT NOZLIB AND NOT (STATICCOMPILE AND WIN32))
    find_package(ZLIB)
    IF (ZLIB_FOUND)
        MESSAGE(STATUS "OK, Found ZLIB!")
        include_directories(${ZLIB_INCLUDE_DIR})
        link_directories(${ZLIB_LIB_DIR})
        add_definitions( -DUSE_ZLIB )
    ELSE (ZLIB_FOUND)
        MESSAGE(STATUS "WARNING: Did not find ZLIB, gzipped file support will be disabled")
    ENDIF (ZLIB_FOUND)
endif()

#query definitions
get_directory_property( DirDefs DIRECTORY ${CMAKE_SOURCE_DIR} COMPILE_DEFINITIONS )
set(COMPILE_DEFINES)
foreach( d ${DirDefs} )
    # message( STATUS "Found Define: " ${d} )
    set(COMPILE_DEFINES "${COMPILE_DEFINES} -D${d}")
endforeach()
message(STATUS "All defines at startup: ${COMPILE_DEFINES}")

set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/lib)
set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/lib)

macro(arjun_add_public_header LIBTARGET HEADER)
    get_target_property(EXISTING_PUBLIC_HEADERS ${LIBTARGET} PUBLIC_HEADER)
    if(EXISTING_PUBLIC_HEADERS)
        list(APPEND EXISTING_PUBLIC_HEADERS "${HEADER}")
    else()
        # Do not append to empty list
        set(EXISTING_PUBLIC_HEADERS "${HEADER}")
    endif()
    set_target_properties(
        ${LIBTARGET}
        PROPERTIES
        PUBLIC_HEADER "${EXISTING_PUBLIC_HEADERS}"
     )
endmacro()

find_package(cryptominisat5 CONFIG REQUIRED)
message(STATUS "CryptoMiniSat5 dynamic lib: ${CRYPTOMINISAT5_LIBRARIES}")
message(STATUS "CryptoMiniSat5 dynamic lib dirs: ${CRYPTOMINISAT5_LIBRARY_DIRS}")
message(STATUS "CryptoMiniSat5 static lib:  ${CRYPTOMINISAT5_STATIC_LIBRARIES}")
message(STATUS "CryptoMiniSat5 static lib deps: ${CRYPTOMINISAT5_STATIC_LIBRARIES_DEPS}")
message(STATUS "CryptoMiniSat5 include dirs: ${CRYPTOMINISAT5_INCLUDE_DIRS}")

# -----------------------------------------------------------------------------
# Provide an export name to be used by targets that wish to export themselves.
# -----------------------------------------------------------------------------
set(ARJUN_EXPORT_NAME "arjunTargets")

add_subdirectory(src)

# -----------------------------------------------------------------------------
# Add uninstall target for makefiles
# -----------------------------------------------------------------------------
configure_file(
    "${CMAKE_CURRENT_SOURCE_DIR}/cmake/cmake_uninstall.cmake.in"
    "${CMAKE_CURRENT_BINARY_DIR}/cmake_uninstall.cmake"
    IMMEDIATE @ONLY
)

add_custom_target(uninstall
    COMMAND ${CMAKE_COMMAND} -P ${CMAKE_CURRENT_BINARY_DIR}/cmake_uninstall.cmake
)

# -----------------------------------------------------------------------------
# Testing
# -----------------------------------------------------------------------------
if (ENABLE_TESTING)
    enable_testing()

    message(STATUS "Testing is enabled")
    set(UNIT_TEST_EXE_SUFFIX "Tests" CACHE STRING "Suffix for Unit test executable")
    #add_subdirectory(tests)

else()
    message(WARNING "Testing is disabled")
endif()

# -----------------------------------------------------------------------------
# Export our targets so that other CMake based projects can interface with
# the build of arjun in the build-tree
# -----------------------------------------------------------------------------
set(ARJUN_TARGETS_FILENAME "arjunTargets.cmake")
set(ARJUN_CONFIG_FILENAME "arjunConfig.cmake")

# Export targets
export(
    TARGETS arjun
    FILE "${CMAKE_CURRENT_BINARY_DIR}/${ARJUN_TARGETS_FILENAME}"
)

# Create arjunConfig file
set(EXPORT_TYPE "Build-tree")
set(CONF_INCLUDE_DIRS "${CMAKE_CURRENT_BINARY_DIR}/include")
configure_file(arjunConfig.cmake.in
    "${CMAKE_CURRENT_BINARY_DIR}/${ARJUN_CONFIG_FILENAME}" @ONLY
)

# Export this package to the CMake user package registry
# Now the user can just use find_package(arjun) on their system
export(PACKAGE arjun)

set(DEF_INSTALL_CMAKE_DIR lib/cmake/arjun)
set(ARJUN_INSTALL_CMAKE_DIR ${DEF_INSTALL_CMAKE_DIR} CACHE PATH
    "Installation directory for arjun CMake files")

# Create arjunConfig file
set(EXPORT_TYPE "installed")
set(CONF_INCLUDE_DIRS "${CMAKE_INSTALL_PREFIX}/include")
configure_file(arjunConfig.cmake.in
   "${CMAKE_CURRENT_BINARY_DIR}/${CMAKE_FILES_DIRECTORY}/${ARJUN_CONFIG_FILENAME}" @ONLY
)

install(FILES
    "${CMAKE_CURRENT_BINARY_DIR}/${CMAKE_FILES_DIRECTORY}/${ARJUN_CONFIG_FILENAME}"
    DESTINATION "${ARJUN_INSTALL_CMAKE_DIR}"
)

# Install the export set for use with the install-tree
install(
    EXPORT ${ARJUN_EXPORT_NAME}
    DESTINATION "${ARJUN_INSTALL_CMAKE_DIR}"
)
