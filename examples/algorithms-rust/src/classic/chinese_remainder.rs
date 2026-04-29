//! 中国剩余定理（CRT）模块
//!
//! 求解两两互素模数下的同余方程组。
//! 对标: CLRS Chapter 31.5

use super::extended_euclidean::extended_gcd;

/// 中国剩余定理
///
/// 给定同余方程组 `x ≡ remainders[i] (mod moduli[i])`，其中 `moduli` 两两互素，
/// 返回在模 `N = ∏ moduli[i]` 下的唯一最小非负解 `(solution, N)`。
///
/// # 复杂度
/// - 时间: O(k² · log(max(moduli)))，其中 k 为方程个数（主要来自互素性校验）
/// - 空间: O(1) 额外空间（不含输入）
///
/// # 参数
/// - `remainders`: 余数数组 `a_i`
/// - `moduli`: 模数数组 `n_i`，要求两两互素
///
/// # 返回值
/// - `Some((solution, combined_modulus))`：满足所有同余方程的最小非负解及其总模数
/// - `None`：输入长度不匹配、为空、模数不两两互素，或总模数溢出 `i64`
///
/// # 示例
/// ```
/// use formal_algorithms::chinese_remainder::chinese_remainder;
/// let remainders = vec![2, 3, 2];
/// let moduli = vec![3, 5, 7];
/// let (x, n) = chinese_remainder(&remainders, &moduli).unwrap();
/// assert_eq!(x, 23);
/// assert_eq!(n, 105);
/// assert_eq!(x % 3, 2);
/// assert_eq!(x % 5, 3);
/// assert_eq!(x % 7, 2);
/// ```
pub fn chinese_remainder(remainders: &[i64], moduli: &[i64]) -> Option<(i64, i64)> {
    if remainders.len() != moduli.len() || remainders.is_empty() {
        return None;
    }

    // 检查两两互素
    for i in 0..moduli.len() {
        for j in (i + 1)..moduli.len() {
            let (g, _, _) = extended_gcd(moduli[i], moduli[j]);
            if g != 1 {
                return None;
            }
        }
    }

    // 计算总模数 N，使用 i128 防止中间溢出
    let mut product: i128 = 1;
    for &m in moduli {
        product = product.checked_mul(m as i128)?;
    }
    if product > i64::MAX as i128 {
        return None;
    }
    let product_i64 = product as i64;

    let mut sum: i128 = 0;
    for (&a, &m) in remainders.iter().zip(moduli.iter()) {
        let mi = product_i64 / m;
        let (_, yi, _) = extended_gcd(mi, m);
        let yi = yi.rem_euclid(m);
        sum += (a as i128) * (mi as i128) * (yi as i128);
    }

    let result = sum.rem_euclid(product) as i64;
    Some((result, product_i64))
}

/// 逐次合并版中国剩余定理
///
/// 不要求预先检查所有模数的两两互素性，而是在合并过程中逐对验证。
/// 每次合并两个方程 `x ≡ a1 (mod n1)` 与 `x ≡ a2 (mod n2)` 为
/// `x ≡ a (mod lcm(n1, n2))`。
///
/// 若某一步 `a1 ≢ a2 (mod gcd(n1, n2))`，则返回 `None`。
///
/// # 复杂度
/// - 时间: O(k · log(max(moduli)))
/// - 空间: O(1) 额外空间
///
/// # 示例
/// ```
/// use formal_algorithms::chinese_remainder::chinese_remainder_iterative;
/// let remainders = vec![2, 3, 2];
/// let moduli = vec![3, 5, 7];
/// let (x, n) = chinese_remainder_iterative(&remainders, &moduli).unwrap();
/// assert_eq!(x, 23);
/// assert_eq!(n, 105);
/// ```
pub fn chinese_remainder_iterative(remainders: &[i64], moduli: &[i64]) -> Option<(i64, i64)> {
    if remainders.len() != moduli.len() || remainders.is_empty() {
        return None;
    }

    let mut a = remainders[0];
    let mut n = moduli[0];

    for (&ai, &ni) in remainders.iter().zip(moduli.iter()).skip(1) {
        let (g, p, _q) = extended_gcd(n, ni);
        // 需要满足 a ≡ ai (mod g)
        if (a - ai).rem_euclid(g) != 0 {
            return None;
        }

        // 合并：x = a + n * t，其中 t = ((ai - a) / g) * p (mod ni / g)
        let diff = (ai - a) / g;
        let lcm = (n as i128).checked_mul((ni / g) as i128)?;
        if lcm > i64::MAX as i128 {
            return None;
        }

        let t = (diff as i128 * p as i128).rem_euclid((ni / g) as i128);
        a = (a as i128 + (n as i128) * t).rem_euclid(lcm) as i64;
        n = lcm as i64;
    }

    Some((a.rem_euclid(n), n))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_crt_basic() {
        let remainders = vec![2, 3, 2];
        let moduli = vec![3, 5, 7];
        let (x, n) = chinese_remainder(&remainders, &moduli).unwrap();
        assert_eq!(n, 105);
        assert_eq!(x, 23);
        assert_eq!(x % 3, 2);
        assert_eq!(x % 5, 3);
        assert_eq!(x % 7, 2);
    }

    #[test]
    fn test_crt_two_equations() {
        let remainders = vec![1, 2];
        let moduli = vec![3, 5];
        let (x, n) = chinese_remainder(&remainders, &moduli).unwrap();
        assert_eq!(n, 15);
        assert_eq!(x, 7); // 7 % 3 = 1, 7 % 5 = 2
    }

    #[test]
    fn test_crt_single_equation() {
        let remainders = vec![4];
        let moduli = vec![7];
        let (x, n) = chinese_remainder(&remainders, &moduli).unwrap();
        assert_eq!(n, 7);
        assert_eq!(x, 4);
    }

    #[test]
    fn test_crt_not_coprime() {
        let remainders = vec![1, 2];
        let moduli = vec![4, 6];
        assert!(chinese_remainder(&remainders, &moduli).is_none());
    }

    #[test]
    fn test_crt_mismatched_lengths() {
        assert!(chinese_remainder(&[1, 2], &[3]).is_none());
    }

    #[test]
    fn test_crt_empty() {
        assert!(chinese_remainder(&[], &[]).is_none());
    }

    #[test]
    fn test_crt_iterative_basic() {
        let remainders = vec![2, 3, 2];
        let moduli = vec![3, 5, 7];
        let (x, n) = chinese_remainder_iterative(&remainders, &moduli).unwrap();
        assert_eq!(n, 105);
        assert_eq!(x, 23);
    }

    #[test]
    fn test_crt_iterative_not_coprime_compatible() {
        // 4 和 6 不互素，但 1 ≡ 3 (mod 2)，有解
        let remainders = vec![1, 3];
        let moduli = vec![4, 6];
        let (x, n) = chinese_remainder_iterative(&remainders, &moduli).unwrap();
        assert_eq!(n, 12);
        assert_eq!(x % 4, 1);
        assert_eq!(x % 6, 3);
    }

    #[test]
    fn test_crt_iterative_not_coprime_incompatible() {
        // 4 和 6 不互素，且 1 ≢ 2 (mod 2)，无解
        let remainders = vec![1, 2];
        let moduli = vec![4, 6];
        assert!(chinese_remainder_iterative(&remainders, &moduli).is_none());
    }
}
