//! LeetCode 372. 超级次方
//!
//! 计算 a^b mod 1337，其中 b 以数组形式给出（大指数）。
//!
//! # Approach
//! 利用模运算性质和递归：
//! - a^b mod 1337 = (a mod 1337)^b mod 1337
//! - 若 b = [b0, b1, ..., bn]，则指数 e = b0·10^n + b1·10^(n-1) + ... + bn
//! - a^e = a^(10·prefix + last) = (a^prefix)^10 · a^last
//! - 因此 super_pow(a, b) = pow_mod(super_pow(a, b[..n-1]), 10) · pow_mod(a, last) mod 1337
//!
//! 辅助函数 pow_mod 使用快速幂（二进制分解）在 O(log n) 时间内计算 base^exp mod mod_val。
//!
//! # Correctness Proof
//! 引理 1：pow_mod 正确性。快速幂不变式：//! result · base^exp ≡ original_base^original_exp (mod mod_val)。
//! 引理 2：super_pow 递归正确性。
//!   设 f(a, [b0,...,bk]) 为所求。
//!   令 prefix = [b0,...,b_{k-1}]，last = bk。
//!   则指数 e = 10·prefix_val + last。
//!   a^e mod 1337 = (a^(10·prefix_val) · a^last) mod 1337
//!                = ((a^prefix_val)^10 · a^last) mod 1337
//!                = (pow_mod(f(a, prefix), 10) · pow_mod(a, last)) mod 1337。
//!
//! # Complexity
//! - Time complexity: O(k · log 1337) = O(k)，k 为数组 b 的长度
//!   （快速幂模数固定为 1337，最多 log₂1337 ≈ 11 次乘法）。
//! - Space complexity: O(k) 递归栈深度。

const MOD: i32 = 1337;

/// 快速幂：计算 (base^exp) % mod_val
fn pow_mod(mut base: i32, mut exp: i32, mod_val: i32) -> i32 {
    let mut result = 1;
    base %= mod_val;
    while exp > 0 {
        if exp % 2 == 1 {
            result = (result * base) % mod_val;
        }
        base = (base * base) % mod_val;
        exp /= 2;
    }
    result
}

pub fn super_pow(a: i32, b: Vec<i32>) -> i32 {
    if b.is_empty() {
        return 1 % MOD;
    }
    let last = *b.last().unwrap();
    let prefix = &b[..b.len() - 1];

    let part1 = pow_mod(super_pow(a, prefix.to_vec()), 10, MOD);
    let part2 = pow_mod(a, last, MOD);
    (part1 * part2) % MOD
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_example_1() {
        assert_eq!(super_pow(2, vec![3]), 8);
    }

    #[test]
    fn test_example_2() {
        assert_eq!(super_pow(2, vec![1, 0]), 1024);
    }

    #[test]
    fn test_example_3() {
        assert_eq!(super_pow(1, vec![4, 3, 3, 8, 5, 2]), 1);
    }

    #[test]
    fn test_large_exponent() {
        assert_eq!(super_pow(2147483647, vec![2, 0, 0]), 1198);
    }

    #[test]
    fn test_mod_property() {
        assert_eq!(super_pow(2, vec![0]), 1);
    }
}
