
 cmake_minimum_required(VERSION 3.15)

 set(project_name LearnedSkipList)
 PROJECT(${project_name})

 if (CMAKE_SYSTEM_NAME MATCHES "Linux")
    # AddressSanitizer, currently removed to pass basic tests
    set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS_DEBUG} -fsanitize=address")
    set(CMAKE_CXX_FLAGS "-g -Wall")
    # set(CMAKE_CXX_FLAGS "-lprofiler")
    SET(CMAKE_BUILE_TYPE Release)
    SET(CMAKE_CXX_FLAGS_DEBUG "$ENV{CXXFLAGS} -O0 -Wall -g2 -ggdb")  
    SET(CMAKE_CXX_FLAGS_RELEASE "$ENV{CXXFLAGS} -O3 -Wall")
endif(CMAKE_SYSTEM_NAME MATCHES "Linux")

add_compile_options(-std=c++17)

# make target
file(GLOB_RECURSE source_files ${PROJECT_SOURCE_DIR}/src/*.cpp )
include_directories(${PROJECT_SOURCE_DIR}/include)
add_executable(${project_name} ${source_files})
target_compile_definitions(${project_name} PRIVATE DEBUG_ON)
target_link_libraries(${project_name} atomic pthread  libjemalloc.so)#profiler

