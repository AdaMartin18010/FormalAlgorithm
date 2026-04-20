/// 信息论下界计算工具
use std::f64::consts::E;

/// Shannon 熵 H(X) = -Σ p(x) log₂ p(x)
pub fn shannon_entropy(probs: &[f64]) -> f64 {
    probs.iter().filter(|&&p| p > 0.0).map(|&p| {
        -p * p.log2()
    }).sum()
}

/// 决策树高度下界: h ≥ ⌈log₂(叶子数)⌉ = ⌈log₂(N)⌉
pub fn decision_tree_lower_bound(output_count: usize) -> usize {
    if output_count <= 1 { return 0; }
    let log2 = (output_count as f64).log2();
    log2.ceil() as usize
}

/// 排序的比较下界: ⌈log₂(n!)⌉ ≈ n·log₂(n) - n·log₂(e)
pub fn sorting_comparison_lower_bound(n: usize) -> f64 {
    if n <= 1 { return 0.0; }
    // Stirling: log₂(n!) ≈ n·log₂(n) - n·log₂(e) + 0.5·log₂(2πn)
    let n_f = n as f64;
    n_f * n_f.log2() - n_f * E.log2() + 0.5 * (2.0 * std::f64::consts::PI * n_f).log2()
}

/// 搜索的比较下界: ⌈log₂(n)⌉
pub fn search_comparison_lower_bound(n: usize) -> usize {
    if n == 0 { return 0; }
    let log2 = (n as f64).log2();
    log2.ceil() as usize
}

/// Bloom Filter 空间-误差权衡
/// m = -n·ln(p) / (ln 2)², 其中 p 为误报率, n 为元素数
pub fn bloom_filter_space(n: usize, p: f64) -> usize {
    let n_f = n as f64;
    let m = -n_f * p.ln() / (2.0f64.ln().powi(2));
    m.ceil() as usize
}

/// 最优哈希函数数 k = (m/n)·ln 2
pub fn bloom_filter_optimal_k(n: usize, m: usize) -> usize {
    let k = (m as f64 / n as f64) * 2.0f64.ln();
    k.round() as usize
}

/// Kolmogorov 复杂度下界估计（不可压缩串）
/// 对均匀随机 n 位串，E[K(x)] ≈ n
pub fn kolmogorov_lower_bound(n: usize) -> usize {
    n
}

/// 数据压缩下界（Shannon 第一定理）
/// 平均码长 L ≥ H(X)
pub fn compression_lower_bound(entropy: f64) -> f64 {
    entropy
}

/// 通信复杂度信息论下界
/// 若输出有 N 种可能，且输入分布的熵为 H，则通信量 ≥ H - H(output)
pub fn communication_info_lower_bound(input_entropy: f64, output_entropy: f64) -> f64 {
    (input_entropy - output_entropy).max(0.0)
}

fn main() {
    println!("=== 信息论下界计算工具 ===\n");

    println!("1. 排序比较下界");
    for n in [8, 16, 32, 64, 128, 1000] {
        let lb = sorting_comparison_lower_bound(n);
        println!("   n={:4} | log₂(n!) ≈ {:.2} | Θ(n·log n) = {:.2}", n, lb, n as f64 * (n as f64).log2());
    }

    println!("\n2. 搜索比较下界");
    for n in [8, 16, 32, 64, 1024, 1_048_576] {
        let lb = search_comparison_lower_bound(n);
        println!("   n={:8} | ⌈log₂ n⌉ = {}", n, lb);
    }

    println!("\n3. 决策树下界");
    for outputs in [2, 4, 8, 16, 32, 256] {
        let lb = decision_tree_lower_bound(outputs);
        println!("   输出数={:3} | 高度 ≥ {}", outputs, lb);
    }

    println!("\n4. Shannon 熵示例");
    let fair_coin = vec![0.5, 0.5];
    let biased_coin = vec![0.9, 0.1];
    let die = vec![1.0/6.0; 6];
    println!("   公平硬币 H = {:.4} bits", shannon_entropy(&fair_coin));
    println!("   偏置硬币 H = {:.4} bits", shannon_entropy(&biased_coin));
    println!("   均匀骰子 H = {:.4} bits", shannon_entropy(&die));

    println!("\n5. Bloom Filter 空间-误差权衡");
    let n = 1_000_000usize;
    for p in [0.01, 0.001, 0.0001] {
        let m = bloom_filter_space(n, p);
        let k = bloom_filter_optimal_k(n, m);
        println!("   n={} p={:.4} | m={} bits | k={} hashes", n, p, m, k);
    }

    println!("\n6. 压缩下界");
    let english_entropy = 1.0; // 每字符约 1 bit（考虑冗余）
    let text_len = 1000usize;
    let min_bits = compression_lower_bound(english_entropy * text_len as f64);
    println!("   1000字符英文文本 | 熵下界 ≈ {:.0} bits", min_bits);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_entropy() {
        let fair = vec![0.5, 0.5];
        assert!((shannon_entropy(&fair) - 1.0).abs() < 1e-6);

        let certain = vec![1.0, 0.0];
        assert!(shannon_entropy(&certain).abs() < 1e-6);
    }

    #[test]
    fn test_sorting_lb() {
        let lb_8 = sorting_comparison_lower_bound(8);
        assert!(lb_8 >= 15.0 && lb_8 <= 16.0);
    }

    #[test]
    fn test_search_lb() {
        assert_eq!(search_comparison_lower_bound(1024), 10);
    }
}
