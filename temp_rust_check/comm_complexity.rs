/// 通信复杂度下界计算工具
use std::collections::HashSet;

/// 计算通信矩阵的秩下界
/// D(f) ≥ ⌈log₂(rank(M_f))⌉
pub fn rank_lower_bound(rank: usize) -> usize {
    if rank == 0 { return 0; }
    let log2 = (rank as f64).log2();
    log2.ceil() as usize
}

/// Fooling Set 下界
/// D(f) ≥ ⌈log₂(|S|)⌉
pub fn fooling_set_lower_bound(set_size: usize) -> usize {
    if set_size == 0 { return 0; }
    let log2 = (set_size as f64).log2();
    log2.ceil() as usize
}

/// 矩形覆盖下界
/// D(f) ≥ ⌈log₂(χ(f))⌉
pub fn rectangle_cover_lower_bound(rect_count: usize) -> usize {
    if rect_count == 0 { return 0; }
    let log2 = (rect_count as f64).log2();
    log2.ceil() as usize
}

/// 相等性问题的通信矩阵：单位矩阵 I_{2^n}
pub fn eq_matrix_size(n: usize) -> (usize, usize) {
    let dim = 1usize << n;
    (dim, dim)
}

/// EQ_n 的秩 = 2^n
pub fn eq_rank(n: usize) -> usize {
    1usize << n
}

/// EQ_n 的确定性下界 = n
pub fn eq_deterministic_lower_bound(n: usize) -> usize {
    n
}

/// DISJ_n 的 fooling set 大小 = 2^n
pub fn disj_fooling_set_size(n: usize) -> usize {
    1usize << n
}

/// 生成 EQ_n 通信矩阵的文本表示（仅适用于小 n）
pub fn format_eq_matrix(n: usize) -> String {
    let dim = 1usize << n;
    let mut lines = vec![format!("EQ_{} 通信矩阵 ({}×{}):", n, dim, dim)];
    for i in 0..dim.min(8) {
        let row: Vec<String> = (0..dim.min(8))
            .map(|j| if i == j { "1".to_string() } else { "0".to_string() })
            .collect();
        lines.push(format!("  [{}]", row.join(" ")));
    }
    if dim > 8 {
        lines.push("  ...".to_string());
    }
    lines.join("\n")
}

/// 计算 Set-Disjointness 的通信矩阵秩
/// M_{DISJ}[x,y] = 1 当且仅当 x ∧ y = 0
/// 该矩阵的秩 = 2^n（在实数域上）
pub fn disj_rank(n: usize) -> usize {
    1usize << n
}

/// 信息复杂度下界估计
/// 若互信息 I(X;Y | f(X,Y)) = I，则通信量 ≥ I
pub fn information_lower_bound(mutual_info_bits: f64) -> f64 {
    mutual_info_bits
}

fn main() {
    println!("=== 通信复杂度下界计算工具 ===\n");

    for n in 1..=6 {
        let (rows, cols) = eq_matrix_size(n);
        let rank = eq_rank(n);
        let lb = eq_deterministic_lower_bound(n);
        println!(
            "EQ_{:2} | 矩阵: {:4}×{:4} | 秩: {:4} | 秩下界: ⌈log₂({})⌉ = {} | 已知下界: {}",
            n, rows, cols, rank, rank, rank_lower_bound(rank), lb
        );
    }

    println!("\n---\n");
    for n in 1..=6 {
        let fs = disj_fooling_set_size(n);
        let lb = fooling_set_lower_bound(fs);
        println!(
            "DISJ_{:2} | Fooling Set 大小: {:4} | 下界: ⌈log₂({})⌉ = {}",
            n, fs, fs, lb
        );
    }

    println!("\n---\n");
    println!("{}", format_eq_matrix(3));

    println!("\n---\n");
    println!("信息复杂度下界示例:");
    println!("  若 I(X;Y | f(X,Y)) = 100 bits, 则通信量 ≥ 100 bits");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_eq_lb() {
        assert_eq!(eq_deterministic_lower_bound(10), 10);
        assert_eq!(rank_lower_bound(eq_rank(10)), 10);
    }

    #[test]
    fn test_disj_lb() {
        let n = 5;
        assert_eq!(fooling_set_lower_bound(disj_fooling_set_size(n)), n);
    }
}
