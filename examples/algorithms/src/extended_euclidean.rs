//! 扩展欧几里得算法模块
//!
//! 提供 Bézout 系数计算与模逆元求解。
//! - 扩展欧几里得算法
//! - 模逆元
//!
//! 对标: CLRS Chapter 31.2

/// 扩展欧几里得算法
///
/// 计算整数 `a` 与 `b` 的最大公约数 `g`，以及 Bézout 系数 `(x, y)`，
/// 使得 `ax + by = g = gcd(a, b)`。返回的 `g` 始终非负。
///
/// # 复杂度
/// - 时间: O(log min(|a|, |b|))
/// - 空间: O(log min(|a|, |b|))（递归栈深度）
///
/// # 参数
/// - `a`: 第一个整数
/// - `b`: 第二个整数
///
/// # 返回值
/// 三元组 `(g, x, y)`，满足 `a * x + b * y = g` 且 `g >= 0`。
///
/// # 示例
/// ```
/// use formal_algorithms::extended_euclidean::extended_gcd;
/// let (g, x, y) = extended_gcd(30, 12);
/// assert_eq!(g, 6);
/// assert_eq!(30 * x + 12 * y, 6);
/// ```
///
/// 负数输入同样成立：
/// ```
/// use formal_algorithms::extended_euclidean::extended_gcd;
/// let (g, x, y) = extended_gcd(-30, 12);
/// assert_eq!(g, 6);
/// assert_eq!((-30) * x + 12 * y, 6);
/// ```
pub fn extended_gcd(a: i64, b: i64) -> (i64, i64, i64) {
    let (g, x, y) = extended_gcd_inner(a, b);
    if g < 0 {
        (-g, -x, -y)
    } else {
        (g, x, y)
    }
}

fn extended_gcd_inner(a: i64, b: i64) -> (i64, i64, i64) {
    if b == 0 {
        (a, 1, 0)
    } else {
        let (g, x1, y1) = extended_gcd_inner(b, a % b);
        (g, y1, x1 - (a / b) * y1)
    }
}

/// 计算模逆元
///
/// 若 `a` 与 `modulus` 互素（即 `gcd(a, modulus) == 1`），返回 `a` 在模 `modulus` 下的
/// 最小非负乘法逆元 `x`，使得 `a * x ≡ 1 (mod modulus)`。
/// 若不互素，返回 `None`。
///
/// # 复杂度
/// - 时间: O(log min(|a|, |modulus|))
/// - 空间: O(log min(|a|, |modulus|))
///
/// # 示例
/// ```
/// use formal_algorithms::extended_euclidean::mod_inverse;
/// assert_eq!(mod_inverse(3, 11), Some(4)); // 3 * 4 = 12 ≡ 1 (mod 11)
/// assert_eq!(mod_inverse(10, 17), Some(12));
/// assert_eq!(mod_inverse(6, 9), None);     // 不互素
/// ```
pub fn mod_inverse(a: i64, modulus: i64) -> Option<i64> {
    if modulus <= 0 {
        return None;
    }
    let (g, x, _) = extended_gcd(a, modulus);
    if g != 1 {
        return None;
    }
    Some(x.rem_euclid(modulus))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_extended_gcd_basic() {
        let (g, x, y) = extended_gcd(30, 12);
        assert_eq!(g, 6);
        assert_eq!(30 * x + 12 * y, 6);

        let (g, x, y) = extended_gcd(35, 15);
        assert_eq!(g, 5);
        assert_eq!(35 * x + 15 * y, 5);
    }

    #[test]
    fn test_extended_gcd_coprime() {
        let (g, x, y) = extended_gcd(17, 13);
        assert_eq!(g, 1);
        assert_eq!(17 * x + 13 * y, 1);
    }

    #[test]
    fn test_extended_gcd_negative() {
        let (g, x, y) = extended_gcd(-30, 12);
        assert_eq!(g, 6);
        assert_eq!((-30) * x + 12 * y, 6);

        let (g, x, y) = extended_gcd(30, -12);
        assert_eq!(g, 6);
        assert_eq!(30 * x + (-12) * y, 6);

        let (g, x, y) = extended_gcd(-30, -12);
        assert_eq!(g, 6);
        assert_eq!((-30) * x + (-12) * y, 6);
    }

    #[test]
    fn test_extended_gcd_zero() {
        let (g, x, y) = extended_gcd(0, 5);
        assert_eq!(g, 5);
        assert_eq!(0 * x + 5 * y, 5);

        let (g, x, y) = extended_gcd(5, 0);
        assert_eq!(g, 5);
        assert_eq!(5 * x + 0 * y, 5);

        let (g, _x, _y) = extended_gcd(0, 0);
        assert_eq!(g, 0);
    }

    #[test]
    fn test_mod_inverse_basic() {
        assert_eq!(mod_inverse(3, 11), Some(4));
        assert_eq!(mod_inverse(10, 17), Some(12));
        assert_eq!(mod_inverse(6, 9), None);
    }

    #[test]
    fn test_mod_inverse_verification() {
        for a in [3_i64, 7, 10, 15] {
            for m in [11_i64, 13, 17, 23] {
                if let Some(inv) = mod_inverse(a, m) {
                    assert_eq!((a * inv).rem_euclid(m), 1, "a={}, m={}", a, m);
                }
            }
        }
    }
}
