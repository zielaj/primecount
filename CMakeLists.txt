cmake_minimum_required(VERSION 3.4...3.22)
project(primecount CXX)
set(PRIMECOUNT_VERSION_MAJOR 7)
set(PRIMECOUNT_VERSION_MINOR 4)
set(PRIMECOUNT_VERSION "${PRIMECOUNT_VERSION_MAJOR}.${PRIMECOUNT_VERSION_MINOR}")

# Build options ######################################################

option(BUILD_PRIMECOUNT    "Build the primecount binary"           ON)
option(BUILD_LIBPRIMESIEVE "Build libprimesieve"                   ON)
option(BUILD_SHARED_LIBS   "Build the shared libprimecount"        OFF)
option(BUILD_STATIC_LIBS   "Build the static libprimecount"        ON)
option(BUILD_MANPAGE       "Regenerate man page using a2x program" OFF)
option(BUILD_TESTS         "Build the test programs"               OFF)

option(WITH_POPCNT          "Use the POPCNT instruction"            ON)
option(WITH_LIBDIVIDE       "Use libdivide.h"                       ON)
option(WITH_OPENMP          "Enable OpenMP multi-threading"         ON)
option(WITH_DIV32           "Use 32-bit division instead of 64-bit division whenever possible" ON)
option(WITH_MSVC_CRT_STATIC "Link primecount.lib with /MT instead of the default /MD" OFF)
option(WITH_FLOAT128        "Use __float128 (requires libquadmath)" OFF)
option(WITH_JEMALLOC        "Use jemalloc allocator"                OFF)

# Option sanity checks ###############################################

# We don't yet support building libprimecount as a shared DLL
# library on Windows. If you need this let me know...
if(WIN32)
    set(BUILD_SHARED_LIBS OFF)
endif()

if(NOT BUILD_SHARED_LIBS AND NOT BUILD_STATIC_LIBS)
    message(FATAL_ERROR "One or both of BUILD_SHARED_LIBS or BUILD_STATIC_LIBS must be set to ON!")
endif()

if(STATICALLY_LINK_LIBPRIMECOUNT AND NOT BUILD_STATIC_LIBS)
    message(FATAL_ERROR "Using STATICALLY_LINK_LIBPRIMECOUNT=ON requires BUILD_STATIC_LIBS=ON!")
endif()

# Static vs. shared linking ##########################################

# By default libprimecount is linked statically if only the static
# libprimecount has been built. If libprimecount has been built as
# both a static and shared library then the shared libprimecount will
# be used for linking.

# It is possible to force static linking by setting:
# cmake -DSTATICALLY_LINK_LIBPRIMECOUNT=ON
# This way libprimecount will be linked statically even if
# libprimecount has been built as both a static and shared library.

if(NOT STATICALLY_LINK_LIBPRIMECOUNT)
    if(BUILD_STATIC_LIBS AND NOT BUILD_SHARED_LIBS)
        set(STATICALLY_LINK_LIBPRIMECOUNT TRUE)
    endif()
endif()

# Set default build type to Release ##################################

if(NOT CMAKE_VERSION VERSION_LESS 3.9)
    get_property(isMultiConfig GLOBAL PROPERTY GENERATOR_IS_MULTI_CONFIG)
elseif(CMAKE_CONFIGURATION_TYPES)
    set(isMultiConfig TRUE)
endif()

if(NOT isMultiConfig AND NOT CMAKE_BUILD_TYPE)
    set(CMAKE_BUILD_TYPE Release CACHE STRING
    "Choose the type of build, options are: None Debug Release RelWithDebInfo MinSizeRel." FORCE)
endif()

# primecount binary source files #####################################

set(BIN_SRC src/app/cmdoptions.cpp
            src/app/main.cpp
            src/app/help.cpp
            src/app/test.cpp)

# primecount library source files ####################################

set(LIB_SRC src/api.cpp
            src/api_c.cpp
            src/BitSieve240.cpp
            src/FactorTable.cpp
            src/RiemannR.cpp
            src/P2.cpp
            src/P3.cpp
            src/PhiTiny.cpp
            src/PiTable.cpp
            src/S1.cpp
            src/Sieve.cpp
            src/LoadBalancerP2.cpp
            src/LoadBalancerS2.cpp
            src/StatusS2.cpp
            src/generate.cpp
            src/nth_prime.cpp
            src/phi.cpp
            src/pi_legendre.cpp
            src/pi_lehmer.cpp
            src/pi_meissel.cpp
            src/pi_primesieve.cpp
            src/print.cpp
            src/util.cpp
            src/lmo/pi_lmo1.cpp
            src/lmo/pi_lmo2.cpp
            src/lmo/pi_lmo3.cpp
            src/lmo/pi_lmo4.cpp
            src/lmo/pi_lmo5.cpp
            src/lmo/pi_lmo_parallel.cpp
            src/deleglise-rivat/S2_hard.cpp
            src/deleglise-rivat/S2_trivial.cpp
            src/deleglise-rivat/pi_deleglise_rivat.cpp
            src/gourdon/pi_gourdon.cpp
            src/gourdon/Phi0.cpp
            src/gourdon/B.cpp
            src/gourdon/D.cpp
            src/gourdon/LoadBalancerAC.cpp
            src/gourdon/SegmentedPiTable.cpp
            src/gourdon/Sigma.cpp)

# Required includes ##################################################

include(GNUInstallDirs)
include(CheckCXXCompilerFlag)
include(CheckCXXSourceCompiles)
include(CheckCXXSourceRuns)
include(CMakePushCheckState)

# Use 32-bit integer division ########################################

# Check at runtime if the dividend and divisor are < 2^32 and
# if so use 32-bit integer division instead of 64-bit integer
# division. On most CPUs before 2020 this significantly
# improves performance.
if(WITH_DIV32)
    set(ENABLE_DIV32 "ENABLE_DIV32")
endif()

# Check if int128_t is supported #####################################

# GCC & Clang support 128-bit integers on 64-bit CPUs. However
# support for 128-bit integers in the C++ standard library is
# currently (2021) only enabled if the GNU extensions are enabled.
# The GNU extensions are usually enabled by default but will be
# disabled if the user compiles with the -std=c++* option. You
# should use -std=gnu++* instead of -std=c++* if you want to enable
# 128-bit integer support in primecount (or simply omit both
# -std=c++* and -std=gnu++*).

cmake_push_check_state()
set(CMAKE_REQUIRED_INCLUDES "${CMAKE_CURRENT_SOURCE_DIR}/include")

check_cxx_source_compiles("
    #include <int128_t.hpp>
    #include <limits>
    #include <type_traits>
    int main() {
        using namespace primecount;
        static_assert(std::numeric_limits<uint128_t>::max() != 0, \"\");
        static_assert(std::is_integral<int128_t>::value, \"\");
        static_assert(std::is_integral<uint128_t>::value, \"\");
        static_assert(std::is_signed<int128_t>::value, \"\");
        static_assert(std::is_unsigned<uint128_t>::value, \"\");
        static_assert(std::is_unsigned<typename std::make_unsigned<int128_t>::type>::value, \"\");
        return 0;
    }" int128)

if(NOT int128)
    # Let's try it again with C++11, this usually works for old
    # GCC/Clang versions that use C++03 by default. We add the
    # -std=gnu++11 option before the user's CXXFLAGS to ensure
    # we don't overwrite any of the user's flags.
    if(CMAKE_CXX11_EXTENSION_COMPILE_OPTION)
        set(CMAKE_REQUIRED_FLAGS "${CMAKE_CXX11_EXTENSION_COMPILE_OPTION} ${CMAKE_CXX_FLAGS}")
    elseif(CMAKE_CXX11_STANDARD_COMPILE_OPTION)
        set(CMAKE_REQUIRED_FLAGS "${CMAKE_CXX11_STANDARD_COMPILE_OPTION} ${CMAKE_CXX_FLAGS}")
    endif()

    check_cxx_source_compiles("
        #include <int128_t.hpp>
        #include <limits>
        #include <type_traits>
        int main() {
            using namespace primecount;
            static_assert(std::numeric_limits<uint128_t>::max() != 0, \"\");
            static_assert(std::is_integral<int128_t>::value, \"\");
            static_assert(std::is_integral<uint128_t>::value, \"\");
            static_assert(std::is_signed<int128_t>::value, \"\");
            static_assert(std::is_unsigned<uint128_t>::value, \"\");
            static_assert(std::is_unsigned<typename std::make_unsigned<int128_t>::type>::value, \"\");
            return 0;
        }" int128_with_cpp11)

    if(NOT int128_with_cpp11)
        set(DISABLE_INT128 "DISABLE_INT128")

        # Print a warning message if the user has specified the -std=c++*
        # option and 128-bit integers are disabled because this of this
        # option. We try to overwrite -std=c++* by -std=gnu++11 and check
        # if this would enable 128-bit integers.
        if(CMAKE_CXX11_EXTENSION_COMPILE_OPTION AND "${CMAKE_CXX_FLAGS}" MATCHES "-std=c\\+\\+[0-9]+")
            set(CMAKE_REQUIRED_FLAGS "${CMAKE_CXX11_EXTENSION_COMPILE_OPTION}")
            set(CMAKE_REQUIRED_QUIET TRUE)

            check_cxx_source_compiles("
                #include <int128_t.hpp>
                #include <limits>
                #include <type_traits>
                int main() {
                    using namespace primecount;
                    static_assert(std::numeric_limits<uint128_t>::max() != 0, \"\");
                    static_assert(std::is_integral<int128_t>::value, \"\");
                    static_assert(std::is_integral<uint128_t>::value, \"\");
                    static_assert(std::is_signed<int128_t>::value, \"\");
                    static_assert(std::is_unsigned<uint128_t>::value, \"\");
                    static_assert(std::is_unsigned<typename std::make_unsigned<int128_t>::type>::value, \"\");
                    return 0;
                }" int128_with_gnu11)

            if(int128_with_gnu11)
                message(WARNING "Your usage of -std=c++* disables 128-bit integer support in "
                                "primecount, primecount will only support numbers <= 2^63. "
                                "Use -std=gnu++* instead to enable 128-bit integer support "
                                "(or omit both -std=c++* and -std=gnu++*).")
            endif()
        endif()
    endif()
endif()

cmake_pop_check_state()

# Check if libdivide.h compiles ######################################

if(WITH_LIBDIVIDE)
    cmake_push_check_state()
    set(CMAKE_REQUIRED_INCLUDES "${CMAKE_CURRENT_SOURCE_DIR}/include")

    check_cxx_source_compiles("
        #include <libdivide.h>
        #include <stdint.h>
        int main() {
            libdivide::divider<uint64_t, libdivide::BRANCHFREE> d(3);
            uint64_t n = 1000000000;
            return (n / d == n / 3) ? 0 : 1;
        }" libdivide_branchfree)

    cmake_pop_check_state()
endif()

if(WITH_LIBDIVIDE AND libdivide_branchfree)
    set(LIB_SRC ${LIB_SRC} src/deleglise-rivat/S2_easy_libdivide.cpp)
    set(LIB_SRC ${LIB_SRC} src/gourdon/AC_libdivide.cpp)
else()
    set(LIB_SRC ${LIB_SRC} src/deleglise-rivat/S2_easy.cpp)
    set(LIB_SRC ${LIB_SRC} src/gourdon/AC.cpp)
endif()

# Enable __float128 support (requires libquadmath) ###################

if(WITH_FLOAT128)
    set(LIB_QUADMATH "quadmath")
    set_source_files_properties(src/RiemannR.cpp PROPERTIES COMPILE_DEFINITIONS HAVE_FLOAT128)
endif()

# Check for OpenMP ###################################################

if(WITH_OPENMP)
    find_package(OpenMP QUIET)

    if(NOT (OpenMP_FOUND OR OpenMP_CXX_FOUND))
        message(STATUS "Performing Test OpenMP")
        message(STATUS "Performing Test OpenMP - Failed")
    endif()

    # Check if libatomic is required (usually by Clang)
    # to support 128-bit integers with OpenMP.
    if(OpenMP_FOUND OR OpenMP_CXX_FOUND)
        cmake_push_check_state()
        set(CMAKE_REQUIRED_INCLUDES "${CMAKE_CURRENT_SOURCE_DIR}/include")

        if(TARGET OpenMP::OpenMP_CXX)
            set(CMAKE_REQUIRED_LIBRARIES "OpenMP::OpenMP_CXX")
        else()
            set(CMAKE_REQUIRED_FLAGS "${OpenMP_CXX_FLAGS}")
        endif()

        if(DISABLE_INT128)
            set(CMAKE_REQUIRED_DEFINITIONS "-D${DISABLE_INT128}")
        endif()

        # Check if compiles without libatomic
        check_cxx_source_compiles("
            #include <int128_t.hpp>
            #include <omp.h>
            #include <stdint.h>
            #include <iostream>
            int main(int, char** argv) {
                using primecount::maxint_t;
                uintptr_t n = (uintptr_t) argv;
                maxint_t sum = (maxint_t) n;
                int iters = (int) n;
                #pragma omp parallel for reduction(+: sum)
                for (int i = 0; i < iters; i++)
                    sum += (i / 3) * omp_get_thread_num();
                std::cout << (long) sum;
                return 0;
            }" OpenMP)

        if(NOT OpenMP)
            find_library(LIB_ATOMIC NAMES atomic libatomic.so.1)

            if(LIB_ATOMIC)
                set(CMAKE_REQUIRED_FLAGS "${OpenMP_CXX_FLAGS}")
                set(CMAKE_REQUIRED_LIBRARIES "${LIB_ATOMIC}")

                # Check if compiles with libatomic
                check_cxx_source_compiles("
                    #include <int128_t.hpp>
                    #include <omp.h>
                    #include <stdint.h>
                    #include <iostream>
                    int main(int, char** argv) {
                        using primecount::maxint_t;
                        uintptr_t n = (uintptr_t) argv;
                        maxint_t sum = (maxint_t) n;
                        int iters = (int) n;
                        #pragma omp parallel for reduction(+: sum)
                        for (int i = 0; i < iters; i++)
                            sum += (i / 3) * omp_get_thread_num();
                        std::cout << (long) sum;
                        return 0;
                    }" OpenMP_with_libatomic)
            endif()

            if(NOT OpenMP_with_libatomic)
                set(LIB_ATOMIC "")
            endif()
        endif()

        cmake_pop_check_state()

        # OpenMP has been tested successfully, enable it
        if(OpenMP OR OpenMP_with_libatomic)
            if(TARGET OpenMP::OpenMP_CXX)
                set(LIB_OPENMP "OpenMP::OpenMP_CXX")
            else()
                set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${OpenMP_CXX_FLAGS}")
            endif()

            # Create list of OpenMP libs for pkg-config/pkgconf
            foreach(X IN LISTS OpenMP_CXX_LIB_NAMES)
                string(APPEND PKGCONFIG_LIBS_OPENMP "-l${X} ")
            endforeach()
        endif()
    endif()

    # OpenMP test has failed, print warning message
    if(NOT OpenMP AND NOT OpenMP_with_libatomic)
        if (CMAKE_CXX_COMPILER_ID MATCHES "Clang|LLVM")
            message(WARNING "Install the OpenMP library (libomp) to enable multithreading in primecount!")
        elseif (CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
            message(WARNING "Install the OpenMP library (libgomp) to enable multithreading in primecount!")
        else()
            message(WARNING "Install the OpenMP library to enable multithreading in primecount!")
        endif()
    endif()
endif()

# Check if x86 CPU supports POPCNT instruction #######################

if(WITH_POPCNT)
    cmake_push_check_state()
    set(CMAKE_REQUIRED_FLAGS -Werror)
    check_cxx_compiler_flag(-mpopcnt mpopcnt)
    cmake_pop_check_state()

    if(mpopcnt)
        set(POPCNT_FLAG "-mpopcnt")
    endif()

    # Since the POPCNT instruction is very important for performance
    # (up to 50% speedup), we will only disable POPCNT if we can
    # prove (using 2 tests) that the CPU does not support it.
    cmake_push_check_state()
    set(CMAKE_REQUIRED_INCLUDES "${CMAKE_CURRENT_SOURCE_DIR}/include")
    set(CMAKE_REQUIRED_QUIET TRUE)

    if(NOT CMAKE_CROSSCOMPILING)
        # GCC/Clang & x86 CPU
        if(mpopcnt)
            check_cxx_source_runs("
                #include <popcnt.hpp>
                #include <stdint.h>
                #include <iostream>
                int main(int, char** argv) {
                    uintptr_t n = (uintptr_t) argv;
                    std::cout << popcnt64((uint64_t) n);
                    return 0;
                }" popcnt64_without_mpopcnt)

            if(popcnt64_without_mpopcnt)
                set(CMAKE_REQUIRED_FLAGS "${POPCNT_FLAG}")
                set(CMAKE_REQUIRED_QUIET FALSE)

                check_cxx_source_runs("
                    #include <popcnt.hpp>
                    #include <stdint.h>
                    #include <iostream>
                    int main(int, char** argv) {
                        uintptr_t n = (uintptr_t) argv;
                        std::cout << popcnt64((uint64_t) n);
                        return 0;
                    }" cpu_supports_popcnt)

                if(NOT cpu_supports_popcnt)
                    set(POPCNT_FLAG "")
                endif()
            endif()
        # MSVC compiler & x86 CPU
        else()
            set(CMAKE_REQUIRED_DEFINITIONS "-DDISABLE_POPCNT")
            check_cxx_source_runs("
                #include <popcnt.hpp>
                #include <stdint.h>
                #include <iostream>
                int main(int, char** argv) {
                    #if defined(_MSC_VER) && (defined(_M_IX86) || defined(_M_X64))
                        uintptr_t n = (uintptr_t) argv;
                        std::cout << popcnt64((uint64_t) n);
                        return 0;
                    #else
                        Error: not MSVC compiler
                    #endif
                }" MSVC_without_popcnt)

            if(MSVC_without_popcnt)
                set(CMAKE_REQUIRED_DEFINITIONS "")
                set(CMAKE_REQUIRED_QUIET FALSE)

                check_cxx_source_runs("
                    #include <popcnt.hpp>
                    #include <stdint.h>
                    #include <iostream>
                    int main(int, char** argv) {
                        #if defined(_MSC_VER) && (defined(_M_IX86) || defined(_M_X64))
                            uintptr_t n = (uintptr_t) argv;
                            std::cout << popcnt64((uint64_t) n);
                            return 0;
                        #else
                            Error: not MSVC compiler
                        #endif
                    }" cpu_supports_popcnt)

                if(NOT cpu_supports_popcnt)
                    set(DISABLE_POPCNT "DISABLE_POPCNT")
                endif()
            endif()
        endif()
    endif()

    cmake_pop_check_state()
else()
    # On the x86/x64 CPU architectures WITH_POPCNT=OFF disables the
    # POPCNT instruction and instead uses a portable integer popcount
    # algorithm. This deteriorates performance by up to 50%.
    # Disabling POPCNT on x86/x64 is necessary for old CPUs from
    # before 2008. On other CPU architectures POPCNT is always used
    # if it is available as this generally does not cause any issues.
    # Hence WITH_POPCNT=OFF is ignored on non x86/x64 CPUs.

    check_cxx_source_compiles("
        int main() {
            #if defined(_MSC_VER) && (defined(_M_IX86) || defined(_M_X64))
                return 0;
            #else
                Error: not MSVC compiler
            #endif
        }" MSVC_x86_or_x64)

    # We only need to disable POPCNT for MSVC on x86/x64.
    # For GCC/Clang __builtin_popcountll() will automatically
    # be portable if we compile without the -mpopcnt flag.
    if(MSVC_x86_or_x64)
        set(DISABLE_POPCNT "DISABLE_POPCNT")
    endif()
endif()

# libprimesieve ######################################################

# By default the libprimesieve dependency is built from source
# (BUILD_LIBPRIMESIEVE=ON). However when packaging primecount
# for e.g. a Linux distro this is not a good idea. For this use
# case it is better to install the libprimesieve package
# (e.g. libprimesieve-dev) and link against that version.

if(BUILD_LIBPRIMESIEVE)
    set(COPY_BUILD_MANPAGE "${BUILD_MANPAGE}")
    set(COPY_BUILD_TESTS "${BUILD_TESTS}")
    set(BUILD_MANPAGE OFF CACHE BOOL "Build primesieve manpage" FORCE)
    set(BUILD_TESTS OFF CACHE BOOL "Build primesieve tests" FORCE)
    option(BUILD_PRIMESIEVE "Build primesieve binary" OFF)

    add_subdirectory(lib/primesieve)

    if(BUILD_SHARED_LIBS)
        target_compile_options(libprimesieve PRIVATE "${POPCNT_FLAG}")
    endif()

    if(BUILD_STATIC_LIBS)
        target_compile_options(libprimesieve-static PRIVATE "${POPCNT_FLAG}")
    endif()

    set(BUILD_MANPAGE "${COPY_BUILD_MANPAGE}" CACHE BOOL "Regenerate man page using a2x" FORCE)
    set(BUILD_TESTS "${COPY_BUILD_TESTS}" CACHE BOOL "Build test programs" FORCE)
else()
    find_package(primesieve REQUIRED)
endif()

# Testing ############################################################

if(BUILD_TESTS)
    enable_testing()
    add_subdirectory(test)
endif()

# libprimecount ######################################################

if(BUILD_SHARED_LIBS)
    add_library(libprimecount SHARED ${LIB_SRC})
    set_target_properties(libprimecount PROPERTIES OUTPUT_NAME primecount)
    set_target_properties(libprimecount PROPERTIES SOVERSION ${PRIMECOUNT_VERSION_MAJOR})
    set_target_properties(libprimecount PROPERTIES VERSION ${PRIMECOUNT_VERSION})
    target_compile_definitions(libprimecount PRIVATE "${DISABLE_POPCNT}" "${DISABLE_INT128}" "${ENABLE_DIV32}")
    target_compile_options(libprimecount PRIVATE "${POPCNT_FLAG}")
    target_link_libraries(libprimecount PRIVATE primesieve::primesieve "${LIB_OPENMP}" "${LIB_QUADMATH}" "${LIB_ATOMIC}")

    target_compile_features(libprimecount
    PRIVATE
        cxx_constexpr
        cxx_lambdas
        cxx_range_for)

    target_include_directories(libprimecount PUBLIC
        $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
        $<INSTALL_INTERFACE:include>)

    install(TARGETS libprimecount
            RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR}
            LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR}
            ARCHIVE DESTINATION ${CMAKE_INSTALL_LIBDIR})
endif()

# libprimecount-static ###############################################

if(BUILD_STATIC_LIBS)
    add_library(libprimecount-static STATIC ${LIB_SRC})
    set_target_properties(libprimecount-static PROPERTIES OUTPUT_NAME primecount)
    target_compile_definitions(libprimecount-static PRIVATE "${DISABLE_POPCNT}" "${DISABLE_INT128}" "${ENABLE_DIV32}")
    target_compile_options(libprimecount-static PRIVATE "${POPCNT_FLAG}")
    target_link_libraries(libprimecount-static PRIVATE primesieve::primesieve "${LIB_OPENMP}" "${LIB_QUADMATH}" "${LIB_ATOMIC}")

    if(WITH_MSVC_CRT_STATIC)
        set_target_properties(libprimecount-static PROPERTIES MSVC_RUNTIME_LIBRARY "MultiThreaded")
    endif()

    target_compile_features(libprimecount-static
    PRIVATE
        cxx_constexpr
        cxx_lambdas
        cxx_range_for)

    target_include_directories(libprimecount-static PUBLIC
        $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
        $<INSTALL_INTERFACE:include>)

    install(TARGETS libprimecount-static
            RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR}
            LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR}
            ARCHIVE DESTINATION ${CMAKE_INSTALL_LIBDIR})
endif()

# Shared vs. static linking ##########################################

if(STATICALLY_LINK_LIBPRIMECOUNT)
    add_library(primecount::primecount ALIAS libprimecount-static)
else()
    add_library(primecount::primecount ALIAS libprimecount)
endif()

# primecount binary ##################################################

if(BUILD_PRIMECOUNT)
    add_executable(primecount ${BIN_SRC})
    target_link_libraries(primecount PRIVATE primecount::primecount primesieve::primesieve)
    target_compile_definitions(primecount PRIVATE "${DISABLE_POPCNT}" "${DISABLE_INT128}" "${ENABLE_DIV32}")
    target_compile_features(primecount PRIVATE cxx_auto_type)
    install(TARGETS primecount DESTINATION ${CMAKE_INSTALL_BINDIR})

    if(WITH_MSVC_CRT_STATIC)
        set_target_properties(primecount PROPERTIES MSVC_RUNTIME_LIBRARY "MultiThreaded")
    endif()
endif()

# Use jemalloc allocator (better scaling) ############################

if(WITH_JEMALLOC)
    find_package(PkgConfig REQUIRED)
    pkg_check_modules(JEMALLOC jemalloc)
    pkg_search_module(JEMALLOC REQUIRED jemalloc)

    if(BUILD_PRIMECOUNT)
        target_link_libraries(primecount PRIVATE ${JEMALLOC_LIBRARIES})
        target_include_directories(primecount PRIVATE ${JEMALLOC_INCLUDE_DIRS})
    endif()
    if(BUILD_SHARED_LIBS)
        target_link_libraries(libprimecount PRIVATE ${JEMALLOC_LIBRARIES})
        target_include_directories(libprimecount PRIVATE ${JEMALLOC_INCLUDE_DIRS})
    endif()
    if(BUILD_STATIC_LIBS)
        target_link_libraries(libprimecount-static PRIVATE ${JEMALLOC_LIBRARIES})
        target_include_directories(libprimecount-static PRIVATE ${JEMALLOC_INCLUDE_DIRS})
    endif()
endif()

# Install header #####################################################

install(FILES include/primecount.h
              include/primecount.hpp
        COMPONENT libprimecount-headers
        DESTINATION ${CMAKE_INSTALL_INCLUDEDIR})

# Regenerate man page ################################################

if(BUILD_MANPAGE)
    find_program(A2X_EXECUTABLE a2x)

    if(NOT A2X_EXECUTABLE)
        message(FATAL_ERROR "Missing a2x program (required for man page generation)!")
    else()
        message(STATUS "Found a2x: ${A2X_EXECUTABLE}")

        add_custom_command(
            TARGET ${PROJECT_NAME} POST_BUILD
            COMMAND ${A2X_EXECUTABLE}
            ARGS --format=manpage
                 -D "${PROJECT_SOURCE_DIR}/doc"
                 "${PROJECT_SOURCE_DIR}/doc/primecount.txt"
            VERBATIM)
    endif()
endif()

# Install man page ###################################################

if(BUILD_PRIMECOUNT)
    install(FILES ${PROJECT_SOURCE_DIR}/doc/primecount.1
            DESTINATION ${CMAKE_INSTALL_MANDIR}/man1)
endif()

# Install primecount.pc (pkg-config) #################################

configure_file(primecount.pc.in primecount.pc @ONLY)

install(FILES ${CMAKE_CURRENT_BINARY_DIR}/primecount.pc
        DESTINATION ${CMAKE_INSTALL_LIBDIR}/pkgconfig)
