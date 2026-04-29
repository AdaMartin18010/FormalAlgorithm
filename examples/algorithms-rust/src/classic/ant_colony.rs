//! # 蚁群优化（Ant Colony Optimization, ACO）
//!
//! 模拟蚂蚁觅食行为的元启发式优化算法，常用于解决组合优化问题（如TSP）。
//!
//! ## 示例
//! ```
//! use algorithms::ant_colony::{aco_tsp, TspGraph};
//!
//! let graph = TspGraph::new(vec![
//!     vec![0.0, 2.0, 9.0, 10.0],
//!     vec![2.0, 0.0, 6.0, 4.0],
//!     vec![9.0, 6.0, 0.0, 8.0],
//!     vec![10.0, 4.0, 8.0, 0.0],
//! ]);
//! let (tour, cost) = aco_tsp(&graph, 100, 50, 1.0, 2.0, 0.5);
//! ```

use rand::prelude::*;

/// TSP 图表示
#[derive(Debug, Clone)]
pub struct TspGraph {
    distances: Vec<Vec<f64>>,
    n: usize,
}

impl TspGraph {
    /// 创建新的 TSP 图
    pub fn new(distances: Vec<Vec<f64>>) -> Self {
        let n = distances.len();
        Self { distances, n }
    }

    /// 获取两城市之间的距离
    pub fn distance(&self, i: usize, j: usize) -> f64 {
        self.distances[i][j]
    }

    /// 城市数量
    pub fn n(&self) -> usize {
        self.n
    }
}

/// 使用蚁群优化求解 TSP
///
/// # 参数
/// - `graph`: TSP 图
/// - `n_ants`: 蚂蚁数量
/// - `n_iterations`: 迭代次数
/// - `alpha`: 信息素重要性系数
/// - `beta`: 启发函数重要性系数
/// - `rho`: 信息素蒸发率
///
/// # 返回
/// (最优路径, 最优路径长度)
pub fn aco_tsp(
    graph: &TspGraph,
    n_ants: usize,
    n_iterations: usize,
    alpha: f64,
    beta: f64,
    rho: f64,
) -> (Vec<usize>, f64) {
    let n = graph.n();
    if n == 0 {
        return (vec![], 0.0);
    }

    let mut rng = thread_rng();
    let mut pheromone = vec![vec![1.0; n]; n];
    let mut best_tour: Option<Vec<usize>> = None;
    let mut best_cost = f64::INFINITY;

    for _ in 0..n_iterations {
        let mut iteration_best_tour = None;
        let mut iteration_best_cost = f64::INFINITY;

        for _ in 0..n_ants {
            let tour = construct_tour(graph, &pheromone, alpha, beta, &mut rng);
            let cost = tour_cost(graph, &tour);

            if cost < iteration_best_cost {
                iteration_best_cost = cost;
                iteration_best_tour = Some(tour);
            }
        }

        if let Some(ref tour) = iteration_best_tour {
            if iteration_best_cost < best_cost {
                best_cost = iteration_best_cost;
                best_tour = Some(tour.clone());
            }
        }

        // 蒸发信息素
        for i in 0..n {
            for j in 0..n {
                pheromone[i][j] *= 1.0 - rho;
            }
        }

        //  deposit pheromone from iteration best
        if let Some(ref tour) = iteration_best_tour {
            let deposit = 1.0 / iteration_best_cost;
            for k in 0..tour.len() - 1 {
                let i = tour[k];
                let j = tour[k + 1];
                pheromone[i][j] += deposit;
                pheromone[j][i] += deposit;
            }
            // close the loop
            let last = tour[tour.len() - 1];
            let first = tour[0];
            pheromone[last][first] += deposit;
            pheromone[first][last] += deposit;
        }
    }

    (best_tour.unwrap_or_else(|| (0..n).collect()), best_cost)
}

fn construct_tour(
    graph: &TspGraph,
    pheromone: &[Vec<f64>],
    alpha: f64,
    beta: f64,
    rng: &mut ThreadRng,
) -> Vec<usize> {
    let n = graph.n();
    let mut tour = Vec::with_capacity(n);
    let mut visited = vec![false; n];
    let start = rng.gen_range(0..n);
    tour.push(start);
    visited[start] = true;

    for _ in 1..n {
        let current = tour[tour.len() - 1];
        let mut probs = Vec::new();
        let mut total = 0.0;

        for j in 0..n {
            if !visited[j] {
                let tau = pheromone[current][j].powf(alpha);
                let eta = (1.0 / graph.distance(current, j)).powf(beta);
                let prob = tau * eta;
                probs.push((j, prob));
                total += prob;
            }
        }

        if total == 0.0 || probs.is_empty() {
            // fallback: pick first unvisited
            for j in 0..n {
                if !visited[j] {
                    tour.push(j);
                    visited[j] = true;
                    break;
                }
            }
            continue;
        }

        let threshold = rng.gen::<f64>() * total;
        let mut cumsum = 0.0;
        let mut chosen = probs[0].0;
        for (j, prob) in probs {
            cumsum += prob;
            if cumsum >= threshold {
                chosen = j;
                break;
            }
        }
        tour.push(chosen);
        visited[chosen] = true;
    }

    tour
}

fn tour_cost(graph: &TspGraph, tour: &[usize]) -> f64 {
    if tour.len() < 2 {
        return 0.0;
    }
    let mut cost = 0.0;
    for i in 0..tour.len() - 1 {
        cost += graph.distance(tour[i], tour[i + 1]);
    }
    cost += graph.distance(tour[tour.len() - 1], tour[0]);
    cost
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tsp_small() {
        let graph = TspGraph::new(vec![
            vec![0.0, 2.0, 9.0, 10.0],
            vec![2.0, 0.0, 6.0, 4.0],
            vec![9.0, 6.0, 0.0, 8.0],
            vec![10.0, 4.0, 8.0, 0.0],
        ]);
        let (_tour, cost) = aco_tsp(&graph, 20, 100, 1.0, 2.0, 0.5);
        // Optimal for this graph is 21.0 (0-1-3-2-0)
        assert!(
            cost <= 25.0,
            "ACO should find a reasonably good solution, got {}",
            cost
        );
    }

    #[test]
    fn test_tsp_two_cities() {
        let graph = TspGraph::new(vec![vec![0.0, 5.0], vec![5.0, 0.0]]);
        let (_tour, cost) = aco_tsp(&graph, 5, 20, 1.0, 2.0, 0.5);
        assert_eq!(cost, 10.0);
    }

    #[test]
    fn test_tsp_single_city() {
        let graph = TspGraph::new(vec![vec![0.0]]);
        let (tour, cost) = aco_tsp(&graph, 1, 10, 1.0, 2.0, 0.5);
        assert_eq!(tour.len(), 1);
        assert_eq!(cost, 0.0);
    }

    #[test]
    fn test_tour_cost() {
        let graph = TspGraph::new(vec![
            vec![0.0, 1.0, 2.0],
            vec![1.0, 0.0, 3.0],
            vec![2.0, 3.0, 0.0],
        ]);
        assert_eq!(tour_cost(&graph, &[0, 1, 2]), 6.0); // 0->1->2->0 = 1+3+2
    }
}
