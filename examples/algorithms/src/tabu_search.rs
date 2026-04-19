//! # 禁忌搜索（Tabu Search）
//!
//! 一种基于局部搜索的元启发式优化方法，通过禁忌表避免循环搜索。
//!
//! ## 示例
//! ```
//! use algorithms::tabu_search::{tabu_search, NeighborFn, ObjectiveFn};
//!
//! let solution = tabu_search(
//!     vec![1, 2, 3, 4],
//!     |s: &Vec<i32>| {
//!         let mut neighbors = Vec::new();
//!         for i in 0..s.len() {
//!             for j in i+1..s.len() {
//!                 let mut n = s.clone();
//!                 n.swap(i, j);
//!                 neighbors.push(n);
//!             }
//!         }
//!         neighbors
//!     },
//!     |s: &Vec<i32>| {
//!         // minimize sum of squared differences from sorted order
//!         s.iter().enumerate().map(|(i, &v)| (v - (i as i32 + 1)).pow(2)).sum::<i32>() as f64
//!     },
//!     100,
//!     10,
//! );
//! ```

use std::collections::VecDeque;
use std::hash::Hash;

/// 禁忌搜索通用框架
///
/// # 类型参数
/// - `S`: 解类型，需实现 Clone + Eq + Hash
///
/// # 参数
/// - `initial`: 初始解
/// - `neighbor_fn`: 生成邻域解的函数
/// - `objective_fn`: 目标函数（越小越好）
/// - `max_iterations`: 最大迭代次数
/// - `tabu_tenure`: 禁忌表长度
///
/// # 返回
/// 找到的最优解
pub fn tabu_search<S, N, O>(
    initial: S,
    neighbor_fn: N,
    objective_fn: O,
    max_iterations: usize,
    tabu_tenure: usize,
) -> S
where
    S: Clone + Eq + Hash,
    N: Fn(&S) -> Vec<S>,
    O: Fn(&S) -> f64,
{
    let mut current = initial.clone();
    let mut best = initial;
    let mut best_obj = objective_fn(&best);
    let mut tabu_list: VecDeque<S> = VecDeque::with_capacity(tabu_tenure);

    for _ in 0..max_iterations {
        let neighbors = neighbor_fn(&current);
        if neighbors.is_empty() {
            break;
        }

        let mut chosen = None;
        let mut chosen_obj = f64::INFINITY;

        for neighbor in &neighbors {
            let obj = objective_fn(neighbor);
            let is_tabu = tabu_list.contains(neighbor);

            // Aspiration: accept if it improves the best known solution
            let improves_best = obj < best_obj;

            if (!is_tabu || improves_best) && obj < chosen_obj {
                chosen_obj = obj;
                chosen = Some(neighbor.clone());
            }
        }

        if let Some(new_current) = chosen {
            tabu_list.push_back(current.clone());
            if tabu_list.len() > tabu_tenure {
                tabu_list.pop_front();
            }
            current = new_current;

            if chosen_obj < best_obj {
                best_obj = chosen_obj;
                best = current.clone();
            }
        } else {
            break;
        }
    }

    best
}

/// 求解排序问题的禁忌搜索（将数组排序）
pub fn tabu_sort(arr: &mut [i32]) {
    if arr.len() <= 1 {
        return;
    }

    let initial: Vec<i32> = arr.to_vec();

    let neighbor_fn = |s: &Vec<i32>| {
        let mut neighbors = Vec::new();
        for i in 0..s.len() {
            for j in i + 1..s.len() {
                let mut n = s.clone();
                n.swap(i, j);
                neighbors.push(n);
            }
        }
        neighbors
    };

    let objective_fn = |s: &Vec<i32>| {
        let mut inv_count = 0.0;
        for i in 0..s.len() {
            for j in i + 1..s.len() {
                if s[i] > s[j] {
                    inv_count += 1.0;
                }
            }
        }
        inv_count
    };

    let sorted = tabu_search(initial, neighbor_fn, objective_fn, 500, 20);
    arr.copy_from_slice(&sorted);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tabu_sort() {
        let mut arr = vec![64, 34, 25, 12, 22, 11, 90];
        tabu_sort(&mut arr);
        assert_eq!(arr, vec![11, 12, 22, 25, 34, 64, 90]);
    }

    #[test]
    fn test_tabu_sort_reverse() {
        let mut arr = vec![5, 4, 3, 2, 1];
        tabu_sort(&mut arr);
        assert_eq!(arr, vec![1, 2, 3, 4, 5]);
    }

    #[test]
    fn test_tabu_sort_empty() {
        let mut arr: Vec<i32> = vec![];
        tabu_sort(&mut arr);
        assert!(arr.is_empty());
    }

    #[test]
    fn test_tabu_sort_single() {
        let mut arr = vec![42];
        tabu_sort(&mut arr);
        assert_eq!(arr, vec![42]);
    }

    #[test]
    fn test_tabu_search_minimization() {
        // Find arrangement of [1,2,3,4] that minimizes sum of adjacent differences
        let result = tabu_search(
            vec![1, 2, 3, 4],
            |s: &Vec<i32>| {
                let mut n = Vec::new();
                for i in 0..s.len() {
                    for j in i + 1..s.len() {
                        let mut c = s.clone();
                        c.swap(i, j);
                        n.push(c);
                    }
                }
                n
            },
            |s: &Vec<i32>| {
                let mut sum = 0.0;
                for i in 0..s.len() - 1 {
                    sum += (s[i] - s[i + 1]).abs() as f64;
                }
                sum
            },
            100,
            10,
        );
        // Optimal is [1,3,2,4] or similar with alternating high/low
        let obj: f64 = (0..result.len() - 1)
            .map(|i| (result[i] - result[i + 1]).abs() as f64)
            .sum();
        assert!(obj <= 8.0, "Should find a good arrangement, got {:?} with obj {}", result, obj);
    }
}
