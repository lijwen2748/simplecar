aux_source_directory(core DIR_SRCS)
aux_source_directory(utils DIR_SRCS)

find_package(ZLIB REQUIRED)
include_directories(. ${ZLIB_INCLUDE_DIRS})
add_library(minisat ${DIR_SRCS})
