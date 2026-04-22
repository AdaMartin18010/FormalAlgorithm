//! LeetCode 207. 课程表
//!
//! 你这个学期必须选修 numCourses 门课程，记为 0 到 numCourses - 1。
//! 在选修某些课程之前需要一些先修课程。请你判断是否可能完成所有课程的学习。
//!
//! 对标: LeetCode 207 / docs/13-LeetCode算法面试专题/06-面试专题/02-高频Top100-树与图.md

use std::collections::VecDeque;

/// 判断是否能完成所有课程（检测有向图是否存在环）。
///
/// # 形式化规约
///
/// - **前置条件 (Pre)**：`num_courses` 范围 `[1, 2000]`，`prerequisites` 长度范围 `[0, 5000]`。
/// - **后置条件 (Post)**：返回 `true` 当且仅当课程依赖图是无环的（即存在拓扑排序）。
///
/// # 核心思路
///
/// 拓扑排序（Kahn 算法 / BFS）：
/// 1. 计算每个节点的入度。
/// 2. 将所有入度为 0 的节点加入队列。
/// 3. 依次取出节点，将其邻接节点入度减 1；若变为 0，入队。
/// 4. 若处理的节点数等于总节点数，则图无环。
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(V + E) — V 为课程数，E 为先修关系数。
/// - **空间复杂度**：O(V + E) — 邻接表和入度数组。
///
/// # 证明要点
///
/// - 引理：DAG 中至少存在一个入度为 0 的节点。
/// - Kahn 算法每次移除一个入度为 0 的节点及其出边，剩余图仍为 DAG。
/// - 若最终所有节点均被移除，原图为 DAG，存在拓扑排序。
/// - 若存在环，环上所有节点入度均 >= 1，永远不会入队，处理节点数 < V。
pub fn can_finish(num_courses: i32, prerequisites: Vec<Vec<i32>>) -> bool {
    let n = num_courses as usize;
    let mut adj: Vec<Vec<i32>> = vec![vec![]; n];
    let mut in_degree = vec![0; n];

    for pre in prerequisites {
        let ai = pre[0] as usize;
        let bi = pre[1] as usize;
        adj[bi].push(pre[0]);
        in_degree[ai] += 1;
    }

    let mut queue: VecDeque<usize> = VecDeque::new();
    for i in 0..n {
        if in_degree[i] == 0 {
            queue.push_back(i);
        }
    }

    let mut processed = 0;
    while let Some(node) = queue.pop_front() {
        processed += 1;
        for &neighbor in &adj[node] {
            let nb = neighbor as usize;
            in_degree[nb] -= 1;
            if in_degree[nb] == 0 {
                queue.push_back(nb);
            }
        }
    }

    processed == n
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_example_1() {
        assert!(can_finish(2, vec![vec![1, 0]]));
    }

    #[test]
    fn test_example_2() {
        assert!(!can_finish(2, vec![vec![1, 0], vec![0, 1]]));
    }

    #[test]
    fn test_single_course() {
        assert!(can_finish(1, vec![]));
    }

    #[test]
    fn test_no_prerequisites() {
        assert!(can_finish(3, vec![]));
    }

    #[test]
    fn test_cycle_of_three() {
        assert!(!can_finish(3, vec![vec![1, 0], vec![2, 1], vec![0, 2]]));
    }

    #[test]
    fn test_dag() {
        assert!(can_finish(4, vec![vec![1, 0], vec![2, 0], vec![3, 1], vec![3, 2]]));
    }
}
