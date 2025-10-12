//! # 算法演示程序 / Algorithm Demonstration
//!
//! 展示所有实现的算法的使用示例。

use algorithms::*;
use std::collections::HashMap;

fn main() {
    println!("=".repeat(80));
    println!("形式化算法实现示例 / Formal Algorithm Implementation Examples");
    println!("=".repeat(80));
    println!();
    
    demo_sorting();
    demo_searching();
    demo_dynamic_programming();
    demo_graph_algorithms();
    
    println!("=".repeat(80));
    println!("所有演示完成！ / All Demonstrations Complete!");
    println!("=".repeat(80));
}

fn demo_sorting() {
    println!("## 1. 排序算法 / Sorting Algorithms");
    println!();
    
    let mut arr1 = vec![64, 34, 25, 12, 22, 11, 90];
    println!("原始数组 / Original: {:?}", arr1);
    
    sorting::merge_sort(&mut arr1);
    println!("归并排序 / Merge Sort: {:?}", arr1);
    println!("时间复杂度 / Time: O(n log n), 空间 / Space: O(n)");
    println!();
    
    let mut arr2 = vec![64, 34, 25, 12, 22, 11, 90];
    sorting::quick_sort(&mut arr2);
    println!("快速排序 / Quick Sort: {:?}", arr2);
    println!("平均时间 / Avg Time: O(n log n), 空间 / Space: O(log n)");
    println!();
}

fn demo_searching() {
    println!("## 2. 搜索算法 / Searching Algorithms");
    println!();
    
    let arr = vec![1, 3, 5, 7, 9, 11, 13, 15, 17, 19];
    println!("已排序数组 / Sorted Array: {:?}", arr);
    
    let target = 13;
    match searching::binary_search(&arr, &target) {
        Some(index) => println!("二分搜索 / Binary Search: 找到 {} 在索引 {}", target, index),
        None => println!("二分搜索 / Binary Search: 未找到 {}", target),
    }
    println!("时间复杂度 / Time: O(log n), 空间 / Space: O(1)");
    println!();
    
    let target2 = 14;
    match searching::binary_search(&arr, &target2) {
        Some(index) => println!("搜索 {} / Search {}: 找到在索引 {}", target2, target2, index),
        None => println!("搜索 {} / Search {}: 未找到", target2, target2),
    }
    println!();
}

fn demo_dynamic_programming() {
    println!("## 3. 动态规划 / Dynamic Programming");
    println!();
    
    let x = "ABCDGH";
    let y = "AEDFHR";
    println!("序列 X / Sequence X: {}", x);
    println!("序列 Y / Sequence Y: {}", y);
    
    let (length, lcs) = dynamic_programming::longest_common_subsequence(x, y);
    println!("最长公共子序列 / LCS: \"{}\" (长度 / length: {})", lcs, length);
    println!("时间复杂度 / Time: O(m × n), 空间 / Space: O(m × n)");
    println!();
    
    let x2 = "AGGTAB";
    let y2 = "GXTXAYB";
    println!("序列 X / Sequence X: {}", x2);
    println!("序列 Y / Sequence Y: {}", y2);
    let (length2, lcs2) = dynamic_programming::longest_common_subsequence(x2, y2);
    println!("最长公共子序列 / LCS: \"{}\" (长度 / length: {})", lcs2, length2);
    println!();
}

fn demo_graph_algorithms() {
    println!("## 4. 图算法 / Graph Algorithms");
    println!();
    
    // 创建示例图
    let mut graph = HashMap::new();
    graph.insert(0, vec![
        graph::Edge { to: 1, weight: 4 },
        graph::Edge { to: 2, weight: 1 },
    ]);
    graph.insert(1, vec![
        graph::Edge { to: 3, weight: 1 },
    ]);
    graph.insert(2, vec![
        graph::Edge { to: 1, weight: 2 },
        graph::Edge { to: 3, weight: 5 },
    ]);
    graph.insert(3, vec![]);
    
    println!("图结构 / Graph Structure:");
    println!("  0 --4--> 1");
    println!("  |        |");
    println!("  1        1");
    println!("  |        |");
    println!("  v        v");
    println!("  2 --2--> 1");
    println!("  |");
    println!("  5");
    println!("  |");
    println!("  v");
    println!("  3");
    println!();
    
    let start = 0;
    println!("从节点 {} 开始的Dijkstra算法 / Dijkstra from node {}:", start, start);
    
    let (distances, predecessors) = graph::dijkstra_with_path(&graph, start, 4);
    
    for (node, dist) in distances.iter().enumerate() {
        match dist {
            Some(d) => {
                let path = graph::reconstruct_path(&predecessors, node);
                let path_str: Vec<String> = path.iter().map(|n| n.to_string()).collect();
                println!("  到节点 {} / To node {}: 距离 {} / distance {}, 路径 / path: {}",
                    node, node, d, d, path_str.join(" → "));
            }
            None => println!("  到节点 {} / To node {}: 不可达 / unreachable", node, node),
        }
    }
    
    println!();
    println!("时间复杂度 / Time: O((V + E) log V), 空间 / Space: O(V)");
    println!();
}

