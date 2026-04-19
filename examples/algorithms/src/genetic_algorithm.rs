//! # 遗传算法（Genetic Algorithm）
//!
//! 经典进化算法实现，包含选择、交叉、变异操作。
//!
//! ## 示例
//! ```
//! use algorithms::genetic_algorithm::{GeneticAlgorithm, SelectionMethod};
//!
//! let ga = GeneticAlgorithm::new(100, 0.8, 0.01, SelectionMethod::Tournament(3));
//! let solution = ga.optimize(|chrom| {
//!     // 最大化染色体中1的个数（OneMax问题）
//!     chrom.iter().filter(|&&b| b).count() as f64
//! }, 100, 10);
//! ```

use rand::prelude::*;

/// 遗传算法配置
#[derive(Debug, Clone)]
pub struct GeneticAlgorithm {
    population_size: usize,
    crossover_rate: f64,
    mutation_rate: f64,
    selection: SelectionMethod,
}

/// 选择方法
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SelectionMethod {
    /// 轮盘赌选择
    Roulette,
    /// 锦标赛选择（参数为锦标赛大小）
    Tournament(usize),
}

impl GeneticAlgorithm {
    /// 创建新的遗传算法实例
    pub fn new(
        population_size: usize,
        crossover_rate: f64,
        mutation_rate: f64,
        selection: SelectionMethod,
    ) -> Self {
        Self {
            population_size,
            crossover_rate,
            mutation_rate,
            selection,
        }
    }

    /// 优化给定的适应度函数
    ///
    /// # 参数
    /// - `fitness`: 适应度函数，输入染色体，输出适应度值（越大越好）
    /// - `generations`: 最大迭代代数
    /// - `chromosome_len`: 染色体长度
    ///
    /// # 返回
    /// 最优染色体及其适应度
    pub fn optimize<F>(
        &self,
        fitness: F,
        generations: usize,
        chromosome_len: usize,
    ) -> (Vec<bool>, f64)
    where
        F: Fn(&[bool]) -> f64,
    {
        let mut rng = thread_rng();
        let mut population = self.init_population(chromosome_len, &mut rng);
        let mut best = None;
        let mut best_fitness = f64::NEG_INFINITY;

        for _ in 0..generations {
            // 评估适应度
            let fitnesses: Vec<f64> = population.iter().map(|c| fitness(c)).collect();

            // 更新最优
            for (i, &f) in fitnesses.iter().enumerate() {
                if f > best_fitness {
                    best_fitness = f;
                    best = Some(population[i].clone());
                }
            }

            // 选择父代
            let parents = self.select(&population, &fitnesses, &mut rng);

            // 交叉和变异产生新种群
            population = self.reproduce(&parents, &mut rng);
        }

        // 最终评估
        let fitnesses: Vec<f64> = population.iter().map(|c| fitness(c)).collect();
        for (i, &f) in fitnesses.iter().enumerate() {
            if f > best_fitness {
                best_fitness = f;
                best = Some(population[i].clone());
            }
        }

        (best.unwrap_or_else(|| vec![false; chromosome_len]), best_fitness)
    }

    fn init_population(&self, len: usize, rng: &mut ThreadRng) -> Vec<Vec<bool>> {
        (0..self.population_size)
            .map(|_| (0..len).map(|_| rng.gen_bool(0.5)).collect())
            .collect()
    }

    fn select(
        &self,
        population: &[Vec<bool>],
        fitnesses: &[f64],
        rng: &mut ThreadRng,
    ) -> Vec<Vec<bool>> {
        match self.selection {
            SelectionMethod::Roulette => self.roulette_select(population, fitnesses, rng),
            SelectionMethod::Tournament(k) => {
                self.tournament_select(population, fitnesses, k, rng)
            }
        }
    }

    fn roulette_select(
        &self,
        population: &[Vec<bool>],
        fitnesses: &[f64],
        rng: &mut ThreadRng,
    ) -> Vec<Vec<bool>> {
        let total: f64 = fitnesses.iter().sum();
        if total <= 0.0 {
            return population.to_vec();
        }
        (0..self.population_size)
            .map(|_| {
                let threshold = rng.gen::<f64>() * total;
                let mut cumsum = 0.0;
                for (i, &f) in fitnesses.iter().enumerate() {
                    cumsum += f;
                    if cumsum >= threshold {
                        return population[i].clone();
                    }
                }
                population[population.len() - 1].clone()
            })
            .collect()
    }

    fn tournament_select(
        &self,
        population: &[Vec<bool>],
        fitnesses: &[f64],
        k: usize,
        rng: &mut ThreadRng,
    ) -> Vec<Vec<bool>> {
        (0..self.population_size)
            .map(|_| {
                let mut best_idx = rng.gen_range(0..population.len());
                let mut best_f = fitnesses[best_idx];
                for _ in 1..k {
                    let idx = rng.gen_range(0..population.len());
                    if fitnesses[idx] > best_f {
                        best_f = fitnesses[idx];
                        best_idx = idx;
                    }
                }
                population[best_idx].clone()
            })
            .collect()
    }

    fn reproduce(&self, parents: &[Vec<bool>], rng: &mut ThreadRng) -> Vec<Vec<bool>> {
        let mut new_pop = Vec::with_capacity(self.population_size);

        while new_pop.len() < self.population_size {
            let p1 = &parents[rng.gen_range(0..parents.len())];
            let p2 = &parents[rng.gen_range(0..parents.len())];

            let (mut c1, mut c2) = if rng.gen_bool(self.crossover_rate) {
                self.crossover(p1, p2, rng)
            } else {
                (p1.clone(), p2.clone())
            };

            self.mutate(&mut c1, rng);
            self.mutate(&mut c2, rng);

            new_pop.push(c1);
            if new_pop.len() < self.population_size {
                new_pop.push(c2);
            }
        }

        new_pop
    }

    fn crossover(
        &self,
        p1: &[bool],
        p2: &[bool],
        rng: &mut ThreadRng,
    ) -> (Vec<bool>, Vec<bool>) {
        let point = rng.gen_range(1..p1.len());
        let mut c1 = p1[..point].to_vec();
        c1.extend_from_slice(&p2[point..]);
        let mut c2 = p2[..point].to_vec();
        c2.extend_from_slice(&p1[point..]);
        (c1, c2)
    }

    fn mutate(&self, chrom: &mut [bool], rng: &mut ThreadRng) {
        for bit in chrom.iter_mut() {
            if rng.gen_bool(self.mutation_rate) {
                *bit = !*bit;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_onemax() {
        let ga = GeneticAlgorithm::new(50, 0.8, 0.01, SelectionMethod::Tournament(3));
        let (best, fitness) = ga.optimize(
            |c| c.iter().filter(|&&b| b).count() as f64,
            100,
            20,
        );
        assert_eq!(fitness, 20.0);
        assert!(best.iter().all(|&b| b));
    }

    #[test]
    fn test_roulette_selection() {
        let ga = GeneticAlgorithm::new(30, 0.8, 0.01, SelectionMethod::Roulette);
        let (best, fitness) = ga.optimize(
            |c| c.iter().filter(|&&b| b).count() as f64,
            200,
            15,
        );
        assert_eq!(fitness, 15.0);
        assert!(best.iter().all(|&b| b));
    }

    #[test]
    fn test_small_population() {
        let ga = GeneticAlgorithm::new(10, 0.9, 0.05, SelectionMethod::Tournament(2));
        let (_, fitness) = ga.optimize(
            |c| c.iter().filter(|&&b| b).count() as f64,
            50,
            8,
        );
        assert_eq!(fitness, 8.0);
    }

    #[test]
    fn test_zero_mutation() {
        let ga = GeneticAlgorithm::new(20, 1.0, 0.0, SelectionMethod::Tournament(2));
        let (_, fitness) = ga.optimize(
            |c| c.iter().filter(|&&b| b).count() as f64,
            50,
            5,
        );
        // Without mutation, might not reach optimal if initial population lacks all-ones
        // But with crossover and tournament selection, it usually does
        assert!(fitness >= 4.0);
    }
}
