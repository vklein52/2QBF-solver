cmake_minimum_required(VERSION 3.10)
project(Research)

set(CMAKE_CXX_STANDARD 11)

find_package(Z3
        REQUIRED
        CONFIG
        )

add_executable(Research main.cpp)

target_include_directories(Research PRIVATE ${Z3_CXX_INCLUDE_DIRS})
target_link_libraries(Research PRIVATE ${Z3_LIBRARIES})
