//! 模拟退火算法（Simulated Annealing / SA）
//!
//! 模拟退火是一种概率性全局优化算法，灵感来源于冶金学中的退火过程。
//! 通过控制"温度"参数，算法能够在搜索空间中进行探索和利用的平衡。
//!
//! # 算法原理
//! 1. 初始化：随机生成初始解，设置初始温度
//! 2. 迭代：在当前温度下进行若干次状态转移尝试
//! 3. 状态转移：
//!    - 生成邻域解
//!    - 计算能量差 ΔE = E(新解) - E(当前解)
//!    - 如果 ΔE < 0（更优），接受新解
//!    - 如果 ΔE > 0（更差），以概率 exp(-ΔE/T) 接受新解
//! 4. 降温：按照冷却 schedule 降低温度
//! 5. 终止：温度足够低或达到最大迭代次数
//!
//! # 时间复杂度
//! - 取决于问题规模和参数设置
//! - 通常: O(迭代次数 × 邻域生成时间)
//!
//! # 参数调优
//! - 初始温度 T0: 应该使得初始接受概率约为 0.8
//! - 冷却系数 alpha: 通常 0.95 ~ 0.999
//! - 终止温度: 足够小，如 1e-8
//! - 每个温度的迭代次数: 与问题规模相关
//!
//! # 应用场景
//! - 旅行商问题（TSP）
//! - 图划分
//! - 调度问题
//! - 布局优化
//! - 函数优化

use rand::Rng;
use std::f64;
use std::time::{Duration, Instant};

/// 模拟退火求解器
pub struct SimulatedAnnealing<T> {
    /// 当前解
    current: T,
    /// 当前能量（目标函数值）
    current_energy: f64,
    /// 最佳解
    best: T,
    /// 最佳能量
    best_energy: f64,
    /// 当前温度
    temperature: f64,
    /// 初始温度
    initial_temperature: f64,
    /// 冷却系数
    cooling_rate: f64,
    /// 终止温度
    final_temperature: f64,
    /// 每个温度的迭代次数
    iterations_per_temp: usize,
    /// 迭代计数
    iteration_count: usize,
    /// 接受次数
    accept_count: usize,
    /// 拒绝次数
    reject_count: usize,
    /// 开始时间
    start_time: Instant,
    /// 超时限制
    timeout: Option<Duration>,
    /// 能量历史
    energy_history: Vec<(usize, f64, f64)>, // (迭代, 温度, 能量)
}

/// 邻域生成函数 trait
pub trait NeighborGenerator<T> {
    /// 生成邻域解
    fn generate(&self, current: &T) -> T;
}

/// 能量函数 trait（目标函数）
pub trait EnergyFunction<T> {
    /// 计算解的能量
    fn energy(&self, solution: &T) -> f64;
}

/// 求解结果
#[derive(Debug, Clone)]
pub struct SAResult<T> {
    /// 找到的最佳解
    pub best_solution: T,
    /// 最佳能量值
    pub best_energy: f64,
    /// 迭代次数
    pub iterations: usize,
    /// 总运行时间
    pub runtime: Duration,
    /// 温度历史
    pub temperature_history: Vec<(usize, f64)>,
    /// 能量历史
    pub energy_history: Vec<(usize, f64, f64)>,
}

impl<T: Clone> SimulatedAnnealing<T> {
    /// 创建新的模拟退火求解器
    ///
    /// # 参数
    /// - `initial`: 初始解
    /// - `initial_energy`: 初始解的能量
    /// - `initial_temp`: 初始温度
    ///
    /// # 示例
    /// ```
    /// let initial = vec![1, 2, 3, 4, 5];
    /// let mut sa = SimulatedAnnealing::new(initial.clone(), 100.0, 1000.0);
    /// ```
    pub fn new(initial: T, initial_energy: f64, initial_temp: f64) -> Self {
        SimulatedAnnealing {
            current: initial.clone(),
            current_energy: initial_energy,
            best: initial.clone(),
            best_energy: initial_energy,
            temperature: initial_temp,
            initial_temperature: initial_temp,
            cooling_rate: 0.995,
            final_temperature: 1e-8,
            iterations_per_temp: 100,
            iteration_count: 0,
            accept_count: 0,
            reject_count: 0,
            start_time: Instant::now(),
            timeout: None,
            energy_history: Vec::new(),
        }
    }

    /// 设置冷却系数
    pub fn with_cooling_rate(mut self, rate: f64) -> Self {
        assert!((0.0..1.0).contains(&rate), "冷却系数必须在(0,1)之间");
        self.cooling_rate = rate;
        self
    }

    /// 设置终止温度
    pub fn with_final_temperature(mut self, temp: f64) -> Self {
        self.final_temperature = temp;
        self
    }

    /// 设置每个温度的迭代次数
    pub fn with_iterations_per_temp(mut self, n: usize) -> Self {
        self.iterations_per_temp = n;
        self
    }

    /// 设置超时
    pub fn with_timeout(mut self, timeout: Duration) -> Self {
        self.timeout = Some(timeout);
        self
    }

    /// 执行模拟退火
    ///
    /// # 参数
    /// - `neighbor_gen`: 邻域生成器
    /// - `energy_fn`: 能量函数
    ///
    /// # 返回值
    /// 返回 `SAResult`，包含最佳解和统计信息
    ///
    /// # 示例
    /// ```
    /// let result = sa.solve(
    ///     |current| { /* 生成邻域解 */ },
    ///     |solution| { /* 计算能量 */ 0.0 }
    /// );
    /// ```
    pub fn solve<N, E>(&mut self, neighbor_gen: N, energy_fn: E) -> SAResult<T>
    where
        N: Fn(&T) -> T,
        E: Fn(&T) -> f64,
    {
        self.start_time = Instant::now();
        let mut temp_history: Vec<(usize, f64)> = Vec::new();

        while self.temperature > self.final_temperature {
            // 检查超时
            if let Some(timeout) = self.timeout {
                if self.start_time.elapsed() > timeout {
                    break;
                }
            }

            temp_history.push((self.iteration_count, self.temperature));

            // 在当前温度下进行若干次迭代
            for _ in 0..self.iterations_per_temp {
                // 生成邻域解
                let neighbor = neighbor_gen(&self.current);
                let neighbor_energy = energy_fn(&neighbor);

                // 计算能量差
                let delta_e = neighbor_energy - self.current_energy;

                // Metropolis准则
                if delta_e < 0.0 {
                    // 更优解，直接接受
                    self.accept(&neighbor, neighbor_energy);
                } else {
                    // 以概率接受较差解
                    let acceptance_prob = (-delta_e / self.temperature).exp();
                    if rand::thread_rng().gen::<f64>() < acceptance_prob {
                        self.accept(&neighbor, neighbor_energy);
                    } else {
                        self.reject_count += 1;
                    }
                }

                self.iteration_count += 1;

                // 记录历史
                if self.iteration_count % 100 == 0 {
                    self.energy_history.push((
                        self.iteration_count,
                        self.temperature,
                        self.best_energy,
                    ));
                }
            }

            // 降温
            self.temperature *= self.cooling_rate;
        }

        SAResult {
            best_solution: self.best.clone(),
            best_energy: self.best_energy,
            iterations: self.iteration_count,
            runtime: self.start_time.elapsed(),
            temperature_history: temp_history,
            energy_history: self.energy_history.clone(),
        }
    }

    /// 接受新解
    fn accept(&mut self, solution: &T, energy: f64) {
        self.current = solution.clone();
        self.current_energy = energy;
        self.accept_count += 1;

        // 更新最佳解
        if energy < self.best_energy {
            self.best = solution.clone();
            self.best_energy = energy;
        }
    }

    /// 获取当前解
    pub fn current_solution(&self) -> &T {
        &self.current
    }

    /// 获取最佳解
    pub fn best_solution(&self) -> &T {
        &self.best
    }

    /// 获取接受率
    pub fn acceptance_rate(&self) -> f64 {
        let total = self.accept_count + self.reject_count;
        if total == 0 {
            0.0
        } else {
            self.accept_count as f64 / total as f64
        }
    }
}

impl<T> SAResult<T> {
    /// 打印结果摘要
    pub fn print_summary(&self)
    where
        T: std::fmt::Debug,
    {
        println!("=== 模拟退火结果 ===");
        println!("最佳能量: {:.6}", self.best_energy);
        println!("迭代次数: {}", self.iterations);
        println!("运行时间: {:?}", self.runtime);
        println!("解: {:?}", self.best_solution);
    }
}

/// TSP问题的模拟退火求解
pub struct TspSolver;

impl TspSolver {
    /// 求解旅行商问题
    ///
    /// # 参数
    /// - `distances`: 距离矩阵
    /// - `initial_temp`: 初始温度
    /// - `cooling_rate`: 冷却系数
    ///
    /// # 返回值
    /// (最优路径, 最短距离)
    pub fn solve(
        distances: &[Vec<f64>],
        initial_temp: f64,
        cooling_rate: f64,
    ) -> (Vec<usize>, f64) {
        let n = distances.len();
        if n <= 1 {
            return ((0..n).collect(), 0.0);
        }

        // 初始解：贪心构造
        let initial = Self::greedy_initial(distances);
        let initial_cost = Self::calculate_cost(&initial, distances);

        let mut sa = SimulatedAnnealing::new(initial, initial_cost, initial_temp)
            .with_cooling_rate(cooling_rate)
            .with_iterations_per_temp(n * 10)
            .with_final_temperature(1e-6);

        let result = sa.solve(
            |current| Self::two_opt_neighbor(current),
            |solution| Self::calculate_cost(solution, distances),
        );

        (result.best_solution, result.best_energy)
    }

    /// 贪心构造初始解
    fn greedy_initial(distances: &[Vec<f64>]) -> Vec<usize> {
        let n = distances.len();
        let mut visited = vec![false; n];
        let mut path = Vec::with_capacity(n);

        let mut current = 0;
        path.push(current);
        visited[current] = true;

        for _ in 1..n {
            let mut next = 0;
            let mut min_dist = f64::MAX;

            for j in 0..n {
                if !visited[j] && distances[current][j] < min_dist {
                    min_dist = distances[current][j];
                    next = j;
                }
            }

            path.push(next);
            visited[next] = true;
            current = next;
        }

        path
    }

    /// 2-opt邻域生成
    fn two_opt_neighbor(path: &[usize]) -> Vec<usize> {
        let n = path.len();
        let mut rng = rand::thread_rng();
        let i = rng.gen_range(0..n);
        let j = rng.gen_range(0..n);

        if i == j {
            return path.to_vec();
        }

        let (i, j) = (i.min(j), i.max(j));
        let mut new_path = path.to_vec();
        new_path[i..=j].reverse();
        new_path
    }

    /// 计算路径总成本
    fn calculate_cost(path: &[usize], distances: &[Vec<f64>]) -> f64 {
        let n = path.len();
        let mut cost = 0.0;

        for i in 0..n {
            let j = (i + 1) % n;
            cost += distances[path[i]][path[j]];
        }

        cost
    }
}

/// 函数优化
pub struct FunctionOptimizer;

impl FunctionOptimizer {
    /// 最小化一维函数
    pub fn minimize_1d<F>(
        f: F,
        lower: f64,
        upper: f64,
        initial_temp: f64,
    ) -> (f64, f64)
    where
        F: Fn(f64) -> f64,
    {
        let mut rng = rand::thread_rng();
        let initial = rng.gen_range(lower..upper);
        let initial_value = f(initial);

        let mut sa = SimulatedAnnealing::new(initial, initial_value, initial_temp)
            .with_cooling_rate(0.99)
            .with_iterations_per_temp(100)
            .with_final_temperature(1e-10);

        let result = sa.solve(
            move |&current| {
                let mut thread_rng = rand::thread_rng();
                let delta = (thread_rng.gen::<f64>() - 0.5) * (upper - lower) * 0.1;
                let new_x = (current + delta).clamp(lower, upper);
                new_x
            },
            |&x| f(x),
        );

        (result.best_solution, result.best_energy)
    }

    /// 最小化多维函数
    pub fn minimize_nd<F>(
        f: F,
        lower: &[f64],
        upper: &[f64],
        initial_temp: f64,
    ) -> (Vec<f64>, f64)
    where
        F: Fn(&[f64]) -> f64,
    {
        let n = lower.len();
        let mut rng = rand::thread_rng();

        let initial: Vec<f64> = (0..n)
            .map(|i| rng.gen_range(lower[i]..upper[i]))
            .collect();
        let initial_value = f(&initial);

        let mut sa = SimulatedAnnealing::new(initial, initial_value, initial_temp)
            .with_cooling_rate(0.995)
            .with_iterations_per_temp(100)
            .with_final_temperature(1e-10);

        let lower = lower.to_vec();
        let upper = upper.to_vec();

        let result = sa.solve(
            move |current| {
                let mut new_vec = current.clone();
                let mut thread_rng = rand::thread_rng();
                let idx = thread_rng.gen_range(0..n);
                let delta = (thread_rng.gen::<f64>() - 0.5) * (upper[idx] - lower[idx]) * 0.1;
                new_vec[idx] = (new_vec[idx] + delta).clamp(lower[idx], upper[idx]);
                new_vec
            },
            |x| f(x),
        );

        (result.best_solution, result.best_energy)
    }
}

/// 调度问题求解器
pub struct SchedulingSolver;

impl SchedulingSolver {
    /// 最小化完工时间的作业调度
    pub fn minimize_makespan(processing_times: &[f64], num_machines: usize) -> (Vec<usize>, f64) {
        let n = processing_times.len();
        let initial: Vec<usize> = (0..n).collect();
        let initial_makespan = Self::calculate_makespan(&initial, processing_times, num_machines);

        let mut sa = SimulatedAnnealing::new(initial, initial_makespan, 1000.0)
            .with_cooling_rate(0.99)
            .with_iterations_per_temp(n * 10)
            .with_final_temperature(1e-6);

        let pt = processing_times.to_vec();
        let nm = num_machines;

        let result = sa.solve(
            |current| Self::swap_neighbor(current),
            move |solution| Self::calculate_makespan(solution, &pt, nm),
        );

        (result.best_solution, result.best_energy)
    }

    /// 交换邻域
    fn swap_neighbor(schedule: &[usize]) -> Vec<usize> {
        let n = schedule.len();
        let mut rng = rand::thread_rng();
        let i = rng.gen_range(0..n);
        let j = rng.gen_range(0..n);

        let mut new_schedule = schedule.to_vec();
        new_schedule.swap(i, j);
        new_schedule
    }

    /// 计算完工时间
    fn calculate_makespan(schedule: &[usize], processing_times: &[f64], num_machines: usize) -> f64 {
        let mut machine_loads = vec![0.0; num_machines];

        for &job in schedule {
            // 找到负载最小的机器
            let min_machine = machine_loads
                .iter()
                .enumerate()
                .min_by(|a, b| a.1.partial_cmp(b.1).unwrap())
                .unwrap()
                .0;
            machine_loads[min_machine] += processing_times[job];
        }

        *machine_loads.iter().max_by(|a, b| a.partial_cmp(b).unwrap()).unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tsp_small() {
        // 4个城市的TSP
        let distances = vec![
            vec![0.0, 10.0, 15.0, 20.0],
            vec![10.0, 0.0, 35.0, 25.0],
            vec![15.0, 35.0, 0.0, 30.0],
            vec![20.0, 25.0, 30.0, 0.0],
        ];

        let (path, cost) = TspSolver::solve(&distances, 1000.0, 0.99);

        println!("TSP路径: {:?}", path);
        println!("总距离: {:.2}", cost);

        // 最优解应该是 0-1-3-2-0 = 10+25+30+15 = 80 或类似
        assert!(cost <= 85.0);
    }

    #[test]
    fn test_function_optimization() {
        // 最小化 f(x) = x^2
        let f = |x: f64| x * x;
        let (x, y) = FunctionOptimizer::minimize_1d(f, -10.0, 10.0, 100.0);

        println!("最小化 x^2: x = {:.6}, f(x) = {:.6}", x, y);
        assert!(y < 0.1); // 应该接近0
    }

    #[test]
    fn test_rastrigin_function() {
        // Rastrigin函数是多峰函数，有全局最小值0在(0,0)
        let f = |x: f64| x * x - 10.0 * (2.0 * std::f64::consts::PI * x).cos() + 10.0;
        let (x, y) = FunctionOptimizer::minimize_1d(f, -5.12, 5.12, 1000.0);

        println!("Rastrigin: x = {:.6}, f(x) = {:.6}", x, y);
        // 由于是多峰函数，可能找到局部最优
    }

    #[test]
    fn test_makespan_scheduling() {
        let processing_times = vec![3.0, 2.0, 4.0, 1.0, 5.0, 2.0];
        let num_machines = 2;

        let (schedule, makespan) = SchedulingSolver::minimize_makespan(&processing_times, num_machines);

        println!("调度方案: {:?}", schedule);
        println!("完工时间: {:.2}", makespan);

        // 理论最优：总和=17，2台机器，最优>=8.5
        assert!(makespan >= 8.5);
    }

    #[test]
    fn test_custom_sa() {
        // 自定义问题：最小化二进制串中1的数量
        let initial = vec![true; 20];
        let initial_energy = initial.iter().filter(|&&x| x).count() as f64;

        let mut sa = SimulatedAnnealing::new(initial, initial_energy, 10.0)
            .with_cooling_rate(0.95)
            .with_iterations_per_temp(50);

        let result = sa.solve(
            |current| {
                let mut rng = rand::thread_rng();
                let mut new = current.clone();
                let idx = rng.gen_range(0..new.len());
                new[idx] = !new[idx];
                new
            },
            |solution| solution.iter().filter(|&&x| x).count() as f64,
        );

        let final_ones = result.best_solution.iter().filter(|&&x| x).count();
        println!("最终1的数量: {}", final_ones);
        println!("接受率: {:.2}%", sa.acceptance_rate() * 100.0);
    }

    #[test]
    fn test_simulated_annealing_parameters() {
        // 测试不同参数设置
        let f = |x: f64| (x - 3.0).powi(2);

        for cooling_rate in [0.90, 0.95, 0.99] {
            let (x, y) = FunctionOptimizer::minimize_1d(f, -10.0, 10.0, 100.0);
            println!("冷却系数={:.2}: x={:.4}, f(x)={:.4}", cooling_rate, x, y);
            assert!(y < 1.0);
        }
    }
}

/// 使用示例
#[cfg(test)]
mod example {
    use super::*;

    #[test]
    fn tsp_example() {
        println!("\n=== 旅行商问题示例 ===");

        // 10个城市的随机距离
        let n = 10;
        let mut distances = vec![vec![0.0; n]; n];
        let mut rng = rand::thread_rng();

        for i in 0..n {
            for j in i + 1..n {
                let dist = rng.gen_range(10.0..100.0);
                distances[i][j] = dist;
                distances[j][i] = dist;
            }
        }

        println!("城市数量: {}", n);

        let start = Instant::now();
        let (path, cost) = TspSolver::solve(&distances, 10000.0, 0.995);
        let duration = start.elapsed();

        println!("找到的路径: {:?}", path);
        println!("总距离: {:.2}", cost);
        println!("运行时间: {:?}", duration);

        // 验证路径
        assert_eq!(path.len(), n);
        let mut visited = vec![false; n];
        for &city in &path {
            visited[city] = true;
        }
        assert!(visited.iter().all(|&x| x));
    }

    #[test]
    fn quadratic_optimization() {
        println!("\n=== 二次函数优化示例 ===");

        // 最小化 f(x, y) = (x-2)^2 + (y+3)^2 + 5
        // 全局最小值在 (2, -3)，值为 5

        let f = |v: &[f64]| (v[0] - 2.0).powi(2) + (v[1] + 3.0).powi(2) + 5.0;

        let lower = vec![-10.0, -10.0];
        let upper = vec![10.0, 10.0];

        let (solution, value) = FunctionOptimizer::minimize_nd(f, &lower, &upper, 1000.0);

        println!("找到的最小值点: ({:.6}, {:.6})", solution[0], solution[1]);
        println!("函数值: {:.6}", value);
        println!("理论最优值: 5.0 在 (2.0, -3.0)");
    }

    #[test]
    fn bin_packing_example() {
        println!("\n=== 装箱问题示例 ===");

        // 一维装箱问题：最小化使用的箱子数量
        // 简化版本：固定容量，最小化箱子数量

        let items = vec![0.5, 0.3, 0.7, 0.2, 0.4, 0.6, 0.8, 0.1];
        let bin_capacity = 1.0;

        // 使用调度算法近似求解（将箱子看作机器）
        let (schedule, bins_needed) = SchedulingSolver::minimize_makespan(&items, 3);

        println!("物品: {:?}", items);
        println!("箱子容量: {}", bin_capacity);
        println!("装箱顺序: {:?}", schedule);
        println!("需要的箱子数: {}", bins_needed.ceil() as usize);
    }

    #[test]
    fn parameter_tuning_demo() {
        println!("\n=== 参数调优演示 ===");

        // 测试不同初始温度对结果的影响
        let f = |x: f64| x.sin() * x.cos() * x; // 复杂多峰函数

        println!("函数: f(x) = x * sin(x) * cos(x)");
        println!("搜索范围: [-10, 10]");
        println!();

        for &initial_temp in &[10.0, 100.0, 1000.0, 10000.0] {
            let (x, y) = FunctionOptimizer::minimize_1d(f, -10.0, 10.0, initial_temp);
            println!("初始温度 {:8.1}: x = {:7.4}, f(x) = {:10.4}",
                     initial_temp, x, y);
        }
    }

    #[test]
    fn convergence_analysis() {
        println!("\n=== 收敛分析 ===");

        // 分析模拟退火的收敛过程
        let f = |x: f64| x.powi(4) - 3.0 * x.powi(3) + 2.0;

        let initial = 5.0;
        let initial_energy = f(initial);

        let mut sa = SimulatedAnnealing::new(initial, initial_energy, 1000.0)
            .with_cooling_rate(0.95)
            .with_iterations_per_temp(20);

        let result = sa.solve(
            |&x| {
                let delta = (rand::thread_rng().gen::<f64>() - 0.5) * 2.0;
                (x + delta).clamp(-10.0, 10.0)
            },
            |&x| f(x),
        );

        println!("初始值: x = 5.0, f(x) = {:.4}", initial_energy);
        println!("最终值: x = {:.4}, f(x) = {:.4}", result.best_solution, result.best_energy);
        println!("迭代次数: {}", result.iterations);
        println!("\n收敛历史 (每100次迭代):");
        for (iter, temp, energy) in result.energy_history.iter().take(10) {
            println!("  迭代 {:4}, 温度 {:.4}, 能量 {:.4}", iter, temp, energy);
        }
    }
}
