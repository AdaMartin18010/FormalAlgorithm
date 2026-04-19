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
add_executable(search search.cpp)
add_executable(dynamic dynamic.cpp)
add_executable(union_find union_find.cpp)

# 启用测试
enable_testing()

# 添加测试
add_test(NAME sorting_test COMMAND sorting)
add_test(NAME graph_test COMMAND graph)
add_test(NAME segment_tree_test COMMAND segment_tree)
add_test(NAME search_test COMMAND search)
add_test(NAME dynamic_test COMMAND dynamic)
add_test(NAME union_find_test COMMAND union_find)

# 安装目标
install(TARGETS sorting graph segment_tree search dynamic union_find
        RUNTIME DESTINATION bin)
