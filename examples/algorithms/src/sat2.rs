//! 2-SAT求解器（基于强连通分量）
//!
//! 2-SAT（2-satisfiability）是布尔可满足性问题的特例，其中每个子句恰好包含两个文字。
//! 2-SAT问题可以在多项式时间内解决（线性时间）。
//!
//! # 问题定义
//! 给定n个布尔变量 x₁, x₂, ..., xₙ 和m个子句，每个子句形式为 (a ∨ b)，
//! 其中a和b是文字（变量或其否定）。判断是否存在一个赋值使所有子句为真。
//!
//! # 算法原理
//! 1. 将2-SAT问题转化为蕴含图（implication graph）
//!    - 子句 (a ∨ b) 等价于 (¬a → b) ∧ (¬b → a)
//! 2. 使用强连通分量算法（Kosaraju/Tarjan）缩点
//! 3. 如果存在变量x使得x和¬x在同一强连通分量中，则问题不可满足
//! 4. 否则，按照拓扑排序的逆序赋值即可得到满足解
//!
//! # 时间复杂度
//! - 建图: O(n + m)
//! - 求强连通分量: O(n + m)
//! - 总时间: O(n + m)
//! - 空间: O(n + m)
//!
//! # 应用场景
//! - 逻辑电路设计
//! - 约束满足问题
//! - 图染色问题
//! - 调度问题

use std::collections::{HashMap, HashSet};

/// 2-SAT求解器
pub struct Solver2Sat {
    /// 变量数量
    n: usize,
    /// 子句列表
    clauses: Vec<(i32, i32)>,
    /// 蕴含图
    graph: HashMap<i32, Vec<i32>>,
    /// 变量值: true/false
    assignment: Vec<Option<bool>>,
}

/// 2-SAT求解结果
#[derive(Debug, Clone)]
pub struct Sat2Result {
    /// 是否可满足
    pub satisfiable: bool,
    /// 变量赋值（仅当可满足时有效）
    pub assignment: Vec<bool>,
    /// 强连通分量信息
    pub scc_info: Option<SCCInfo>,
}

/// 强连通分量信息
#[derive(Debug, Clone)]
pub struct SCCInfo {
    /// 强连通分量数量
    pub scc_count: usize,
    /// 每个变量所属的分量
    pub var_to_scc: Vec<usize>,
    /// 分量图
    pub component_graph: HashMap<usize, Vec<usize>>,
}

/// 文字表示
/// 正数表示正文字（x_i），负数表示负文字（¬x_i）
/// 例如: 3 表示 x₃, -3 表示 ¬x₃
pub type Literal = i32;

impl Solver2Sat {
    /// 创建新的2-SAT求解器
    ///
    /// # 参数
    /// - `n`: 变量数量
    ///
    /// # 示例
    /// ```
    /// let solver = Solver2Sat::new(3); // 3个变量: x₁, x₂, x₃
    /// ```
    pub fn new(n: usize) -> Self {
        Solver2Sat {
            n,
            clauses: Vec::new(),
            graph: HashMap::new(),
            assignment: vec![None; n + 1],
        }
    }

    /// 添加子句 (a ∨ b)
    ///
    /// # 参数
    /// - `a`: 第一个文字（正数表示x_i，负数表示¬x_i）
    /// - `b`: 第二个文字
    ///
    /// # 示例
    /// ```
    /// let mut solver = Solver2Sat::new(3);
    /// solver.add_clause(1, 2);    // (x₁ ∨ x₂)
    /// solver.add_clause(-1, 3);   // (¬x₁ ∨ x₃)
    /// solver.add_clause(-2, -3);  // (¬x₂ ∨ ¬x₃)
    /// ```
    pub fn add_clause(&mut self, a: Literal, b: Literal) {
        self.clauses.push((a, b));

        // 子句 (a ∨ b) 等价于 (¬a → b) ∧ (¬b → a)
        let not_a = -a;
        let not_b = -b;

        self.graph.entry(not_a).or_default().push(b);
        self.graph.entry(not_b).or_default().push(a);
    }

    /// 添加单元子句 (a)
    ///
    /// 等价于 (a ∨ a)
    pub fn add_unit_clause(&mut self, a: Literal) {
        self.add_clause(a, a);
    }

    /// 添加等价约束 (a ↔ b)
    ///
    /// 等价于 (a → b) ∧ (b → a)，即 (¬a ∨ b) ∧ (¬b ∨ a)
    pub fn add_equivalence(&mut self, a: Literal, b: Literal) {
        self.add_clause(-a, b);
        self.add_clause(-b, a);
    }

    /// 添加蕴含约束 (a → b)
    ///
    /// 等价于 (¬a ∨ b)
    pub fn add_implication(&mut self, a: Literal, b: Literal) {
        self.add_clause(-a, b);
    }

    /// 添加互斥约束 (a XOR b)
    ///
    /// 等价于 (a ∨ b) ∧ (¬a ∨ ¬b)
    pub fn add_xor(&mut self, a: Literal, b: Literal) {
        self.add_clause(a, b);
        self.add_clause(-a, -b);
    }

    /// 求解2-SAT问题
    ///
    /// # 返回值
    /// 返回 `Sat2Result`，包含可满足性和赋值
    ///
    /// # 示例
    /// ```
    /// let mut solver = Solver2Sat::new(2);
    /// solver.add_clause(1, 2);
    /// solver.add_clause(-1, -2);
    ///
    /// let result = solver.solve();
    /// assert!(result.satisfiable);
    /// ```
    pub fn solve(&mut self) -> Sat2Result {
        // 确保所有变量都在图中
        for i in 1..=self.n as i32 {
            self.graph.entry(i).or_default();
            self.graph.entry(-i).or_default();
        }

        // 使用Kosaraju算法求强连通分量
        let scc_result = self.kosaraju_scc();
        let scc_count = scc_result.len();

        // 构建变量到SCC的映射（使用HashMap支持负数）
        let mut var_to_scc_map: std::collections::HashMap<i32, usize> = std::collections::HashMap::new();
        for (scc_id, scc) in scc_result.iter().enumerate() {
            for &var in scc {
                var_to_scc_map.insert(var, scc_id);
            }
        }

        for i in 1..=self.n as i32 {
            let pos_scc = var_to_scc_map.get(&i).copied().unwrap_or(0);
            let neg_scc = var_to_scc_map.get(&-i).copied().unwrap_or(0);

            if pos_scc == neg_scc {
                // 转换var_to_scc_map为Vec
                let var_to_scc: Vec<usize> = (0..=self.n)
                    .map(|i| var_to_scc_map.get(&(i as i32)).copied().unwrap_or(0))
                    .collect();
                return Sat2Result {
                    satisfiable: false,
                    assignment: Vec::new(),
                    scc_info: Some(SCCInfo {
                        scc_count,
                        var_to_scc,
                        component_graph: HashMap::new(),
                    }),
                };
            }
        }

        // 构建分量图并计算拓扑序
        let component_graph = self.build_component_graph(&scc_result, &var_to_scc_map);
        let topo_order = self.topological_sort(&component_graph, scc_count);

        // 按照拓扑排序的逆序赋值
        let mut assigned = vec![false; scc_count];
        let mut assignment = vec![false; self.n + 1];

        for &scc_id in topo_order.iter().rev() {
            if assigned[scc_id] {
                continue;
            }

            // 给当前SCC赋false，给对应的否定SCC赋true
            for &var in &scc_result[scc_id] {
                if var > 0 {
                    assignment[var as usize] = false;
                } else {
                    assignment[(-var) as usize] = true;
                }
            }
            assigned[scc_id] = true;

            // 找到对应的否定SCC并标记
            let first_var = scc_result[scc_id][0];
            let neg_var = -first_var;
            if let Some(&neg_scc) = var_to_scc_map.get(&neg_var) {
                assigned[neg_scc] = true;
            }
        }

        // 转换为结果格式
        let final_assignment: Vec<bool> = (1..=self.n).map(|i| assignment[i]).collect();

        // 转换var_to_scc_map为Vec（只包含正变量）
        let var_to_scc: Vec<usize> = (0..=self.n)
            .map(|i| var_to_scc_map.get(&(i as i32)).copied().unwrap_or(0))
            .collect();

        Sat2Result {
            satisfiable: true,
            assignment: final_assignment,
            scc_info: Some(SCCInfo {
                scc_count,
                var_to_scc,
                component_graph,
            }),
        }
    }

    /// Kosaraju算法求强连通分量
    fn kosaraju_scc(&self) -> Vec<Vec<i32>> {
        let mut visited: HashSet<i32> = HashSet::new();
        let mut finish_order: Vec<i32> = Vec::new();

        // 第一次DFS
        for (&vertex, _) in &self.graph {
            if !visited.contains(&vertex) {
                self.dfs1(vertex, &mut visited, &mut finish_order);
            }
        }

        // 构建转置图
        let transpose = self.build_transpose();

        // 第二次DFS
        visited.clear();
        let mut components: Vec<Vec<i32>> = Vec::new();

        for &vertex in finish_order.iter().rev() {
            if !visited.contains(&vertex) {
                let mut component = Vec::new();
                self.dfs2(vertex, &transpose, &mut visited, &mut component);
                components.push(component);
            }
        }

        components
    }

    fn dfs1(&self, vertex: i32, visited: &mut HashSet<i32>, finish_order: &mut Vec<i32>) {
        visited.insert(vertex);

        if let Some(neighbors) = self.graph.get(&vertex) {
            for &neighbor in neighbors {
                if !visited.contains(&neighbor) {
                    self.dfs1(neighbor, visited, finish_order);
                }
            }
        }

        finish_order.push(vertex);
    }

    fn dfs2(
        &self,
        vertex: i32,
        transpose: &HashMap<i32, Vec<i32>>,
        visited: &mut HashSet<i32>,
        component: &mut Vec<i32>,
    ) {
        visited.insert(vertex);
        component.push(vertex);

        if let Some(neighbors) = transpose.get(&vertex) {
            for &neighbor in neighbors {
                if !visited.contains(&neighbor) {
                    self.dfs2(neighbor, transpose, visited, component);
                }
            }
        }
    }

    fn build_transpose(&self) -> HashMap<i32, Vec<i32>> {
        let mut transpose: HashMap<i32, Vec<i32>> = HashMap::new();

        for (&vertex, _) in &self.graph {
            transpose.entry(vertex).or_default();
        }

        for (&vertex, neighbors) in &self.graph {
            for &neighbor in neighbors {
                transpose.entry(neighbor).or_default().push(vertex);
            }
        }

        transpose
    }

    fn build_component_graph(
        &self,
        scc_result: &[Vec<i32>],
        var_to_scc: &std::collections::HashMap<i32, usize>,
    ) -> HashMap<usize, Vec<usize>> {

        let mut component_graph: HashMap<usize, Vec<usize>> = HashMap::new();
        for i in 0..scc_result.len() {
            component_graph.insert(i, Vec::new());
        }

        for (&vertex, neighbors) in &self.graph {
            let from_scc = var_to_scc[&vertex];
            for &neighbor in neighbors {
                let to_scc = var_to_scc[&neighbor];
                if from_scc != to_scc {
                    component_graph
                        .entry(from_scc)
                        .or_default()
                        .push(to_scc);
                }
            }
        }

        // 去重
        for neighbors in component_graph.values_mut() {
            let set: HashSet<_> = neighbors.iter().cloned().collect();
            *neighbors = set.into_iter().collect();
        }

        component_graph
    }

    fn topological_sort(
        &self,
        graph: &HashMap<usize, Vec<usize>>,
        n: usize,
    ) -> Vec<usize> {
        let mut in_degree = vec![0; n];
        for neighbors in graph.values() {
            for &v in neighbors {
                in_degree[v] += 1;
            }
        }

        let mut queue: Vec<usize> = Vec::new();
        for i in 0..n {
            if in_degree[i] == 0 {
                queue.push(i);
            }
        }

        let mut result = Vec::new();
        let mut idx = 0;

        while idx < queue.len() {
            let u = queue[idx];
            idx += 1;
            result.push(u);

            if let Some(neighbors) = graph.get(&u) {
                for &v in neighbors {
                    in_degree[v] -= 1;
                    if in_degree[v] == 0 {
                        queue.push(v);
                    }
                }
            }
        }

        result
    }

    /// 验证赋值是否满足所有子句
    pub fn verify(&self, assignment: &[bool]) -> bool {
        for &(a, b) in &self.clauses {
            let a_val = if a > 0 {
                assignment[(a - 1) as usize]
            } else {
                !assignment[(-a - 1) as usize]
            };
            let b_val = if b > 0 {
                assignment[(b - 1) as usize]
            } else {
                !assignment[(-b - 1) as usize]
            };

            if !a_val && !b_val {
                return false;
            }
        }
        true
    }
}

impl Sat2Result {
    /// 打印结果
    pub fn print(&self) {
        if self.satisfiable {
            println!("2-SAT问题: 可满足");
            println!("变量赋值:");
            for (i, &val) in self.assignment.iter().enumerate() {
                println!("  x{} = {}", i + 1, if val { "true" } else { "false" });
            }
        } else {
            println!("2-SAT问题: 不可满足");
        }

        if let Some(ref info) = self.scc_info {
            println!("强连通分量数: {}", info.scc_count);
        }
    }
}

/// 辅助函数：快速求解2-SAT
///
/// # 参数
/// - `n`: 变量数量
/// - `clauses`: 子句列表，每个子句为 (a, b)
pub fn solve_2sat(n: usize, clauses: &[(Literal, Literal)]) -> Sat2Result {
    let mut solver = Solver2Sat::new(n);
    for &(a, b) in clauses {
        solver.add_clause(a, b);
    }
    solver.solve()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_satisfiable_case() {
        let mut solver = Solver2Sat::new(3);
        // (x1 ∨ x2) ∧ (¬x1 ∨ x3) ∧ (¬x2 ∨ ¬x3)
        solver.add_clause(1, 2);
        solver.add_clause(-1, 3);
        solver.add_clause(-2, -3);

        let result = solver.solve();
        assert!(result.satisfiable);
        assert!(solver.verify(&result.assignment));
    }

    #[test]
    fn test_unsatisfiable_case() {
        let mut solver = Solver2Sat::new(2);
        // (x1 ∨ x2) ∧ (x1 ∨ ¬x2) ∧ (¬x1 ∨ x2) ∧ (¬x1 ∨ ¬x2)
        // 这是矛盾的
        solver.add_clause(1, 2);
        solver.add_clause(1, -2);
        solver.add_clause(-1, 2);
        solver.add_clause(-1, -2);

        let result = solver.solve();
        assert!(!result.satisfiable);
    }

    #[test]
    fn test_single_variable() {
        let mut solver = Solver2Sat::new(1);
        solver.add_clause(1, 1);  // x1必须为true

        let result = solver.solve();
        assert!(result.satisfiable);
        assert!(result.assignment[0]);
    }

    #[test]
    fn test_equivalence() {
        let mut solver = Solver2Sat::new(2);
        // x1 ↔ x2
        solver.add_equivalence(1, 2);

        let result = solver.solve();
        assert!(result.satisfiable);
        assert_eq!(result.assignment[0], result.assignment[1]);
    }

    #[test]
    fn test_xor() {
        let mut solver = Solver2Sat::new(2);
        // x1 XOR x2 (恰好一个为true)
        solver.add_xor(1, 2);

        let result = solver.solve();
        assert!(result.satisfiable);
        assert_ne!(result.assignment[0], result.assignment[1]);
    }

    #[test]
    fn test_implication() {
        let mut solver = Solver2Sat::new(2);
        // x1 → x2
        solver.add_implication(1, 2);
        // 再加上 x1
        solver.add_unit_clause(1);

        let result = solver.solve();
        assert!(result.satisfiable);
        assert!(result.assignment[0]); // x1 = true
        assert!(result.assignment[1]); // x2 = true (因为x1→x2且x1=true)
    }

    #[test]
    fn test_large_instance() {
        let n = 100;
        let mut solver = Solver2Sat::new(n);

        // 创建一些随机的可满足约束
        for i in 1..n {
            // xi → x(i+1)
            solver.add_implication(i as i32, (i + 1) as i32);
        }

        // x1必须为true
        solver.add_unit_clause(1);

        let result = solver.solve();
        assert!(result.satisfiable);
        assert!(solver.verify(&result.assignment));

        // 由于x1=true且x1→x2→...→x100，所有变量都应为true
        for &val in &result.assignment {
            assert!(val);
        }
    }

    #[test]
    fn test_chain_constraint() {
        let mut solver = Solver2Sat::new(3);
        // x1 → x2 → x3 → ¬x1
        solver.add_implication(1, 2);
        solver.add_implication(2, 3);
        solver.add_implication(3, -1);

        // 这个约束意味着如果x1=true，则¬x1=true，矛盾
        // 所以x1必须为false
        let result = solver.solve();
        assert!(result.satisfiable);
        assert!(!result.assignment[0]); // x1 = false
    }

    #[test]
    fn test_empty_clauses() {
        let mut solver = Solver2Sat::new(3);
        let result = solver.solve();
        assert!(result.satisfiable);
    }

    #[test]
    fn test_convenience_function() {
        let clauses = vec![(1, 2), (-1, 3), (-2, -3)];
        let result = solve_2sat(3, &clauses);
        assert!(result.satisfiable);

        // 验证赋值
        let solver = Solver2Sat::new(3);
        assert!(solver.verify(&result.assignment));
    }
}

/// 使用示例
#[cfg(test)]
mod example {
    use super::*;

    #[test]
    fn graph_coloring_example() {
        println!("\n=== 图染色问题示例 ===");

        // 用2-SAT解决2-染色问题
        // 变量 xi 表示顶点i染颜色1
        // 每个顶点必须染颜色1或颜色2: (xi ∨ ¬xi)
        // 相邻顶点不能同色: (xi ≠ xj)

        // 三角形图（3个顶点，3条边）
        // 三角形不能用2种颜色染色
        let mut solver = Solver2Sat::new(3);

        // 边 (1,2): x1 ≠ x2
        solver.add_xor(1, 2);
        // 边 (2,3): x2 ≠ x3
        solver.add_xor(2, 3);
        // 边 (1,3): x1 ≠ x3
        solver.add_xor(1, 3);

        let result = solver.solve();
        println!("三角形2-染色: {}",
                 if result.satisfiable { "可行" } else { "不可行" });
        assert!(!result.satisfiable);

        // 路径图 1-2-3（可以2-染色）
        let mut solver2 = Solver2Sat::new(3);
        solver2.add_xor(1, 2);
        solver2.add_xor(2, 3);

        let result2 = solver2.solve();
        println!("路径2-染色: {}",
                 if result2.satisfiable { "可行" } else { "不可行" });
        assert!(result2.satisfiable);
    }

    #[test]
    fn scheduling_problem() {
        println!("\n=== 调度问题示例 ===");

        // 3个任务，每个任务可以选择两个时间段之一
        // 任务1: 时间段 A 或 B
        // 任务2: 时间段 B 或 C
        // 任务3: 时间段 A 或 C
        // 约束: 同一个时间段不能有两个任务

        // 变量: x1(任务1选A), x2(任务2选B), x3(任务3选A)
        let mut solver = Solver2Sat::new(6);

        // 任务1: x1(A) 或 ¬x1(B)
        solver.add_clause(1, -1);  // 恒真，只是占位

        // 简化示例：两个会议不能同时安排
        // 会议1: 房间A或B, 会议2: 房间A或B
        // 如果都选A则冲突
        let mut solver2 = Solver2Sat::new(2);
        // x1: 会议1选A, x2: 会议2选A
        // 不能同时选A: ¬(x1 ∧ x2) = (¬x1 ∨ ¬x2)
        solver2.add_clause(-1, -2);
        // 每个会议必须选一个: (x1 ∨ ¬x1) 恒真

        // 添加会议必须选A或B的约束（简化表示）
        // 会议1选A (x1) 或 选B (¬x1)
        // 会议2选A (x2) 或 选B (¬x2)

        let result = solver2.solve();
        println!("会议调度: {}",
                 if result.satisfiable { "可行" } else { "不可行" });

        if result.satisfiable {
            println!("会议1选择: {}",
                     if result.assignment[0] { "A" } else { "B" });
            println!("会议2选择: {}",
                     if result.assignment[1] { "A" } else { "B" });
        }
    }

    #[test]
    fn logical_puzzle() {
        println!("\n=== 逻辑谜题示例 ===");

        // 骑士与无赖谜题
        // A说: "B是骑士"
        // B说: "A是无赖"
        // 骑士总说真话，无赖总说假话

        // 变量: a(A是骑士), b(B是骑士)
        // A说真话 ↔ (B是骑士): a ↔ b
        // B说真话 ↔ (A是无赖): b ↔ ¬a

        let mut solver = Solver2Sat::new(2);
        // a ↔ b
        solver.add_equivalence(1, 2);
        // b ↔ ¬a
        solver.add_equivalence(2, -1);

        let result = solver.solve();
        println!("谜题解答:");
        if result.satisfiable {
            println!("A是{}", if result.assignment[0] { "骑士" } else { "无赖" });
            println!("B是{}", if result.assignment[1] { "骑士" } else { "无赖" });
        } else {
            println!("无解");
        }
    }

    #[test]
    fn constraint_satisfaction() {
        println!("\n=== 约束满足问题示例 ===");

        // 4个布尔变量，约束:
        // 1. x1 和 x2 至少一个为true
        // 2. x2 和 x3 至少一个为false
        // 3. x3 和 x4 恰好一个为true
        // 4. x4 和 x1 不能同时为false

        let mut solver = Solver2Sat::new(4);

        // (x1 ∨ x2)
        solver.add_clause(1, 2);
        // (¬x2 ∨ ¬x3)
        solver.add_clause(-2, -3);
        // (x3 XOR x4) = (x3 ∨ x4) ∧ (¬x3 ∨ ¬x4)
        solver.add_xor(3, 4);
        // (x4 ∨ x1)
        solver.add_clause(4, 1);

        let result = solver.solve();
        result.print();

        assert!(result.satisfiable);
        assert!(solver.verify(&result.assignment));
    }
}
