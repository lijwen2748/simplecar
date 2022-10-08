cmake_minimum_required(VERSION 3.1)
project(simplecar)

if (NOT CMAKE_BUILD_TYPE)
  set(CMAKE_BUILD_TYPE Debug)
endif()
message(STATUS "Build type: ${CMAKE_BUILD_TYPE}")
if (CYGWIN OR MINGW)
  add_compile_options(-Wa,-mbig-obj)
endif()
add_compile_options(-fpermissive)
add_compile_options(-O3)

include (ExternalProject)
ExternalProject_Add(
  libpicosat
  SOURCE_DIR ${PROJECT_SOURCE_DIR}/picosat
  BUILD_IN_SOURCE TRUE
  CONFIGURE_COMMAND ./configure.sh
  INSTALL_COMMAND ""
)

add_subdirectory(minisat)

set(CMAKE_CXX_STANDARD 11)

set(CMAKE_THREAD_PREFER_PTHREAD TRUE)
set(THREADS_PREFER_PTHREAD_FLAG TRUE)
find_package(Threads REQUIRED)
if (NOT DEFINED CMAKE_USE_PTHREADS_INIT)
  message(FATAL_ERROR "pthread not found")
endif()

find_package(ZLIB REQUIRED)
include_directories(minisat ${ZLIB_INCLUDE_DIRS})
link_directories(picosat)

aux_source_directory(. DIR_SRCS)
list(REMOVE_ITEM DIR_SRCS ./recycle.cpp)
add_executable(simplecar ${DIR_SRCS})
add_executable(simplecar-picosat ${DIR_SRCS})

add_dependencies(simplecar-picosat libpicosat)
target_compile_definitions(simplecar-picosat PUBLIC -DENABLE_PICOSAT)

target_link_libraries(simplecar Threads::Threads ZLIB::ZLIB minisat)
target_link_libraries(simplecar-picosat Threads::Threads ZLIB::ZLIB picosat)

install(TARGETS simplecar simplecar-picosat
        RUNTIME DESTINATION bin
        ARCHIVE DESTINATION lib
        INCLUDES DESTINATION include
        )