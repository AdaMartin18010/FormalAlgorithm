/// Master Theorem 自动判断器
/// 对于递推式 T(n) = a·T(n/b) + Θ(n^d · log^k n)
#[derive(Debug, Clone, PartialEq)]
pub enum MasterCase {
    Case1 { log_b_a: f64 },
    Case2 { log_b_a: f64, k: f64 },
    Case3 { log_b_a: f64 },
    ExtendedCase2Prime { log_b_a: f64, k: f64 },
    NonStandard,
}

impl MasterCase {
    pub fn describe(&self) -> String {
        match self {
            MasterCase::Case1 { log_b_a } => {
                format!("Case 1: f(n) = O(n^{:.3} - ε), T(n) = Θ(n^{:.3})", log_b_a, log_b_a)
            }
            MasterCase::Case2 { log_b_a, .. } => {
                format!("Case 2: f(n) = Θ(n^{:.3}), T(n) = Θ(n^{:.3} · log n)", log_b_a, log_b_a)
            }
            MasterCase::Case3 { log_b_a } => {
                format!("Case 3: f(n) = Ω(n^{:.3} + ε), T(n) = Θ(f(n))", log_b_a)
            }
            MasterCase::ExtendedCase2Prime { log_b_a, k } => {
                format!(
                    "Case 2': f(n) = Θ(n^{:.3} · log^{:.0} n), T(n) = Θ(n^{:.3} · log^{:.0} n)",
                    log_b_a, k + 1.0, log_b_a, k + 1.0
                )
            }
            MasterCase::NonStandard => "非标准形式，主定理不适用".to_string(),
        }
    }
}

/// 判断主定理情形
/// a: 子问题数量, b: 规模缩小因子, d: f(n) = n^d 的指数, k: log^k n 的幂次
pub fn classify(a: f64, b: f64, d: f64, k: f64) -> Result<MasterCase, String> {
    if a < 1.0 {
        return Err("参数 a 必须 ≥ 1".to_string());
    }
    if b <= 1.0 {
        return Err("参数 b 必须 > 1".to_string());
    }

    let log_b_a = a.log(b);
    let eps = 1e-9;

    if (d - log_b_a).abs() < eps {
        if k.abs() < eps {
            Ok(MasterCase::Case2 { log_b_a, k })
        } else {
            Ok(MasterCase::ExtendedCase2Prime { log_b_a, k })
        }
    } else if d < log_b_a - eps {
        Ok(MasterCase::Case1 { log_b_a })
    } else if d > log_b_a + eps {
        // 需验证正则条件 a·f(n/b) ≤ c·f(n)
        // 对多项式 f(n)=n^d·log^k n，正则条件在 d > log_b_a 时自动满足
        Ok(MasterCase::Case3 { log_b_a })
    } else {
        Ok(MasterCase::NonStandard)
    }
}

/// 递推关系求解器
pub fn solve_recurrence(name: &str, a: f64, b: f64, d: f64, k: f64) -> String {
    let case = classify(a, b, d, k).unwrap_or(MasterCase::NonStandard);
    format!("{} → {}\n  结论: {}", name, case.describe(), asymptotic_solution(&case))
}

fn asymptotic_solution(case: &MasterCase) -> String {
    match case {
        MasterCase::Case1 { log_b_a } => format!("Θ(n^{:.3})", log_b_a),
        MasterCase::Case2 { log_b_a, .. } => format!("Θ(n^{:.3} · log n)", log_b_a),
        MasterCase::Case3 { .. } => "Θ(f(n)) — 由合并代价主导".to_string(),
        MasterCase::ExtendedCase2Prime { log_b_a, k } => {
            format!("Θ(n^{:.3} · log^{:.0} n)", log_b_a, k + 1.0)
        }
        MasterCase::NonStandard => "需使用 Akra-Bazzi 或递归树方法".to_string(),
    }
}

fn main() {
    println!("=== 主定理自动判断器 ===\n");

    let examples = vec![
        ("归并排序", 2.0, 2.0, 1.0, 0.0),
        ("Strassen", 7.0, 2.0, 0.0, 0.0),
        ("整数乘法", 3.0, 2.0, 1.0, 0.0),
        ("T(n)=4T(n/2)+n^2", 4.0, 2.0, 2.0, 0.0),
        ("T(n)=2T(n/2)+n·log n", 2.0, 2.0, 1.0, 1.0),
    ];

    for (name, a, b, d, k) in examples {
        println!("{}", solve_recurrence(name, a, b, d, k));
        println!();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_merge_sort() {
        let case = classify(2.0, 2.0, 1.0, 0.0).unwrap();
        assert!(matches!(case, MasterCase::Case2 { .. }));
    }

    #[test]
    fn test_strassen() {
        let case = classify(7.0, 2.0, 0.0, 0.0).unwrap();
        assert!(matches!(case, MasterCase::Case1 { .. }));
    }

    #[test]
    fn test_case3() {
        let case = classify(3.0, 4.0, 2.0, 0.0).unwrap();
        assert!(matches!(case, MasterCase::Case3 { .. }));
    }
}
