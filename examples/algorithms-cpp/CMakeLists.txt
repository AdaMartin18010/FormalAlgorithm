cmake_minimum_required(VERSION 3.14)
project(algorithms_cpp)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# 编译选项
if(MSVC)
    add_compile_options(/W4 /EHsc)
else()
    add_compile_options(-Wall -Wextra -O2)
endif()

# 可执行文件
add_executable(sorting sorting.cpp)
add_executable(graph graph.cpp)
add_executable(segment_tree segment_tree.cpp)

# 启用测试
enable_testing()

# 安装目标
install(TARGETS sorting graph segment_tree
        RUNTIME DESTINATION bin)
