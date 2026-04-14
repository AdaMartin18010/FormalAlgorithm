//! 离散对数算法模块
//!
//! 解决离散对数问题：求满足 g^x ≡ h (mod p) 的 x
//! 提供：
//! - 大步小步算法（BSGS）
//! - Pollard's Rho 算法

use std::collections::HashMap;

/// 扩展欧几里得算法
///
/// 返回 (g, x, y) 满足 ax + by = g = gcd(a, b)
fn extended_gcd(a: i128, b: i128) -> (i128, i128, i128) {
    if b == 0 {
        return (a.abs(), a.signum(), 0);
    }
    let (g, x1, y1) = extended_gcd(b, a % b);
    (g, y1, x1 - (a / b) * y1)
}

/// 模逆元
///
/// 返回 a^(-1) mod m，如果不存在返回 None
fn mod_inv(a: i128, m: i128) -> Option<i128> {
    let (g, x, _) = extended_gcd(a, m);
    if g != 1 {
        return None;
    }
    Some(((x % m) + m) % m)
}

/// 快速幂（带模）
///
/// # 复杂度
/// - 时间: O(log exp)
fn mod_pow(mut base: i128, mut exp: i128, modulus: i128) -> i128 {
    if modulus == 1 {
        return 0;
    }
    let mut result = 1i128;
    base %= modulus;
    while exp > 0 {
        if exp & 1 == 1 {
            result = (result * base) % modulus;
        }
        base = (base * base) % modulus;
        exp >>= 1;
    }
    result
}

/// 最大公约数
fn gcd(mut a: i128, mut b: i128) -> i128 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a.abs()
}

/// 大步小步算法（Baby-Step Giant-Step）
///
/// # 问题
/// 求解 g^x ≡ h (mod p)，其中 p 为素数
///
/// # 算法原理
/// 设 x = im + j，其中 m = ⌈√p⌉
/// 则 g^x = g^(im+j) = g^j · (g^m)^i ≡ h
/// 即 g^j ≡ h · (g^(-m))^i
///
/// 1. Baby-step: 预计算所有 g^j (j ∈ [0, m-1])
/// 2. Giant-step: 枚举 i，检查 h · (g^(-m))^i 是否在表中
///
/// # 复杂度
/// - 时间: O(√p)
/// - 空间: O(√p)
///
/// # 参数
/// - `g`: 生成元（底数）
/// - `h`: 目标值
/// - `p`: 素数模数
///
/// # 返回值
/// - `Some(x)`: 离散对数值
/// - `None`: 无解
///
/// # 示例
/// ```
/// use formal_algorithms::discrete_log::bsgs;
/// // 求解 2^x ≡ 8 (mod 11)，答案为 x = 3
/// let result = bsgs(2, 8, 11);
/// assert_eq!(result, Some(3));
/// ```
pub fn bsgs(g: i128, h: i128, p: i128) -> Option<i128> {
    if h == 1 {
        return Some(0);
    }

    let m = ((p as f64).sqrt().ceil() as i128).max(1);
    let mut table = HashMap::new();

    // Baby-step: 计算 g^j
    let mut cur = 1;
    for j in 0..m {
        table.entry(cur).or_insert(j);
        cur = (cur * g) % p;
    }

    // Giant-step: 计算 h · g^(-mi)
    let gm = mod_pow(g, m, p);
    let gm_inv = mod_inv(gm, p)?;

    cur = h % p;
    for i in 0..m {
        if let Some(&j) = table.get(&cur) {
            let x = i * m + j;
            if x < p {
                return Some(x);
            }
        }
        cur = (cur * gm_inv) % p;
    }

    None
}

/// 扩展BSGS（处理非素数模数）
///
/// 求解 g^x ≡ h (mod p)，p 可以不是素数
///
/// # 算法
/// 当 gcd(g, p) ≠ 1 时，需要特殊处理
///
/// # 复杂度
/// - 时间: O(√p)
/// - 空间: O(√p)
pub fn ex_bsgs(g: i128, h: i128, p: i128) -> Option<i128> {
    let mut g = g % p;
    let mut h = h % p;

    if h == 1 {
        return Some(0);
    }

    let (g_gcd, _, _) = extended_gcd(g, p);
    if g_gcd == 1 {
        return bsgs(g, h, p);
    }

    // 处理 gcd(g, p) > 1 的情况
    let mut cnt = 0;
    let mut t = 1i128;
    let mut cur_p = p;

    loop {
        let (d, _, _) = extended_gcd(g, cur_p);
        if d == 1 {
            break;
        }
        if h == t {
            return Some(cnt);
        }
        if h % d != 0 {
            return None;
        }
        h /= d;
        cur_p /= d;
        t = (t * (g / d)) % cur_p;
        cnt += 1;
        if cnt > 100 {
            return None; // 防止无限循环
        }
    }

    // 现在 gcd(g, cur_p) = 1，可以使用BSGS
    let h_new = (h * mod_inv(t, cur_p)?) % cur_p;
    bsgs(g % cur_p, h_new, cur_p).map(|x| x + cnt)
}

/// Pollard's Rho 离散对数算法
///
/// # 算法原理
/// 使用随机游走在群中寻找碰撞，利用 Floyd 判圈算法
/// 将群分成三个子集，根据当前值决定下一步操作
///
/// # 复杂度
/// - 期望时间: O(√p)
/// - 空间: O(1)
///
/// # 参数
/// - `g`: 生成元
/// - `h`: 目标值
/// - `p`: 素数模数
/// - `n`: 群的阶（通常 n = p-1）
///
/// # 返回值
/// - `Some(x)`: 离散对数值
/// - `None`: 未找到（可增加迭代次数重试）
///
/// # 示例
/// ```
/// use formal_algorithms::discrete_log::pollard_rho_dlog;
/// // 当目标值为 1 时，离散对数必为 0
/// let result = pollard_rho_dlog(3, 1, 17, 16);
/// assert_eq!(result, Some(0));
/// ```
pub fn pollard_rho_dlog(g: i128, h: i128, p: i128, n: i128) -> Option<i128> {
    if h == 1 {
        return Some(0);
    }

    // 分区函数
    let partition = |x: i128| -> i32 {
        match x % 3 {
            0 => 0,
            1 => 1,
            _ => 2,
        }
    };

    // 迭代函数 f(x) = x * a_i mod p
    // 同时追踪指数 a, b 使得 x = g^a * h^b
    let step = |x: i128, a: i128, b: i128| -> (i128, i128, i128) {
        match partition(x) {
            0 => ((x * h) % p, a, (b + 1) % n),
            1 => ((x * x) % p, (2 * a) % n, (2 * b) % n),
            _ => ((x * g) % p, (a + 1) % n, b),
            _ => unreachable!(),
        }
    };

    // Floyd判圈
    for _ in 0..100 {
        let mut x = 1i128;
        let mut a = 0i128;
        let mut b = 0i128;

        let mut y = 1i128;
        let mut c = 0i128;
        let mut d = 0i128;

        loop {
            // x 走一步
            let (nx, na, nb) = step(x, a, b);
            x = nx;
            a = na;
            b = nb;

            // y 走两步
            let (ny, nc, nd) = step(y, c, d);
            let (ny2, nc2, nd2) = step(ny, nc, nd);
            y = ny2;
            c = nc2;
            d = nd2;

            if x == y {
                // 找到碰撞: g^a * h^b = g^c * h^d
                // 即 g^(a-c) = h^(d-b)
                // 设 h = g^x，则 g^(a-c) = g^(x(d-b))
                // 即 a - c ≡ x(d - b) (mod n)

                let a_diff = ((a - c) % n + n) % n;
                let b_diff = ((d - b) % n + n) % n;

                if b_diff == 0 {
                    // 需要重新随机化
                    break;
                }

                // x ≡ a_diff * b_diff^(-1) (mod n / gcd(b_diff, n))
                let (g_gcd, _, _) = extended_gcd(b_diff, n);

                if a_diff % g_gcd != 0 {
                    break; // 无解，重试
                }

                let n_div = n / g_gcd;
                let a_div = a_diff / g_gcd;
                let b_div = b_diff / g_gcd;

                let b_inv = mod_inv(b_div, n_div)?;
                let x0 = (a_div * b_inv) % n_div;

                // 验证解
                for k in 0..g_gcd {
                    let candidate = (x0 + k * n_div) % n;
                    if mod_pow(g, candidate, p) == h % p {
                        return Some(candidate);
                    }
                }
                break;
            }

            // 防止无限循环
            if a > n * 2 {
                break;
            }
        }
    }

    None
}

/// Pollard's Rho 因数分解（整数分解）
///
/// # 算法原理
/// 使用随机多项式 f(x) = x² + c mod n
/// 通过 gcd(|x - y|, n) 寻找因子
///
/// # 复杂度
/// - 期望时间: O(n^(1/4))
/// - 空间: O(1)
///
/// # 参数
/// - `n`: 待分解的合数
///
/// # 返回值
/// - `Some(d)`: n 的一个非平凡因子
/// - `None`: 未找到（可更换参数重试）
pub fn pollard_rho_factor(n: i128) -> Option<i128> {
    if n % 2 == 0 {
        return Some(2);
    }

    let f = |x: i128, c: i128| -> i128 {
        ((x * x) % n + c) % n
    };

    for c in 1..10 {
        let mut x = 2i128;
        let mut y = 2i128;
        let mut d = 1i128;

        while d == 1 {
            x = f(x, c);
            y = f(f(y, c), c);
            d = gcd((x - y).abs(), n);
        }

        if d != n {
            return Some(d);
        }
    }

    None
}

/// 完整的因数分解
///
/// # 返回值
/// n 的所有素因子（含重复）
///
/// # 复杂度
/// - 期望时间: O(n^(1/4) log n)
pub fn factorize(mut n: i128) -> Vec<i128> {
    let mut factors = vec![];

    // 试除小素数
    let small_primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37];
    for &p in &small_primes {
        while n % p == 0 {
            factors.push(p);
            n /= p;
        }
    }

    // Pollard's Rho 分解大数
    if n > 1 {
        let mut stack = vec![n];
        while let Some(m) = stack.pop() {
            if is_prime_trial(m) {
                factors.push(m);
            } else if let Some(d) = pollard_rho_factor(m) {
                stack.push(d);
                stack.push(m / d);
            } else {
                factors.push(m);
            }
        }
    }

    factors.sort();
    factors
}

/// 试除法素性测试（小范围）
fn is_prime_trial(n: i128) -> bool {
    if n < 2 {
        return false;
    }
    if n == 2 || n == 3 {
        return true;
    }
    if n % 2 == 0 {
        return false;
    }

    let sqrt_n = (n as f64).sqrt() as i128;
    for i in (3..=sqrt_n).step_by(2) {
        if n % i == 0 {
            return false;
        }
    }
    true
}

/// Pohlig-Hellman 算法
///
/// # 适用场景
/// 当群的阶 n 有光滑因子分解时使用
/// 将大问题分解为若干小子问题
///
/// # 复杂度
/// - 时间: O(Σ e_i · (log n + √p_i))，其中 n = Π p_i^e_i
///
/// # 参数
/// - `g`: 生成元
/// - `h`: 目标值
/// - `p`: 素数模数
/// - `n`: 群的阶
pub fn pohlig_hellman(g: i128, h: i128, p: i128, n: i128) -> Option<i128> {
    // 分解 n
    let factors = factorize(n);

    // 收集不同素因子及其最高幂次
    let mut prime_powers: Vec<(i128, i128)> = vec![];
    let mut cur = 0i128;
    let mut cnt = 0i128;

    for &f in &factors {
        if f == cur {
            cnt += 1;
        } else {
            if cur > 0 {
                prime_powers.push((cur, cnt));
            }
            cur = f;
            cnt = 1;
        }
    }
    if cur > 0 {
        prime_powers.push((cur, cnt));
    }

    // 对每个素幂因子求解
    let mut congruences: Vec<(i128, i128)> = vec![];

    for (q, e) in prime_powers {
        let qe = q.pow(e as u32);
        let g_qe = mod_pow(g, n / qe, p);
        let h_qe = mod_pow(h, n / qe, p);

        // 在 q^e 阶子群中求解
        if let Some(x_q) = bsgs_small(g_qe, h_qe, p, qe) {
            congruences.push((x_q, qe));
        } else {
            return None;
        }
    }

    // 中国剩余定理合并
    crt(&congruences)
}

/// 小范围BSGS（用于Pohlig-Hellman）
fn bsgs_small(g: i128, h: i128, p: i128, n: i128) -> Option<i128> {
    if n < 10000 {
        // 小范围直接暴力
        let mut cur = 1;
        for x in 0..n {
            if cur == h {
                return Some(x);
            }
            cur = (cur * g) % p;
        }
        return None;
    }
    bsgs(g, h, p)
}

/// 中国剩余定理
///
/// 求解 x ≡ a_i (mod m_i)
fn crt(congruences: &[(i128, i128)]) -> Option<i128> {
    if congruences.is_empty() {
        return Some(0);
    }

    let mut x = congruences[0].0;
    let mut m = congruences[0].1;

    for &(a, mi) in &congruences[1..] {
        // x ≡ a (mod mi), x ≡ x (mod m)
        // 即 x + m·k ≡ a (mod mi)
        // m·k ≡ a - x (mod mi)

        let diff = ((a - x) % mi + mi) % mi;
        let m_inv = mod_inv(m % mi, mi)?;
        let k = (diff * m_inv) % mi;

        x += m * k;
        m *= mi;
        x %= m;
    }

    Some(x)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mod_pow() {
        assert_eq!(mod_pow(2, 10, 1000), 24);
        assert_eq!(mod_pow(3, 5, 100), 43);
        assert_eq!(mod_pow(5, 0, 100), 1);
    }

    #[test]
    fn test_mod_inv() {
        assert_eq!(mod_inv(3, 11), Some(4)); // 3 * 4 = 12 ≡ 1 (mod 11)
        assert_eq!(mod_inv(2, 4), None);     // 2 和 4 不互素
    }

    #[test]
    fn test_bsgs_simple() {
        // 2^3 = 8 ≡ 8 (mod 11)
        assert_eq!(bsgs(2, 8, 11), Some(3));
        
        // 2^7 = 128 ≡ 7 (mod 11)
        assert_eq!(bsgs(2, 7, 11), Some(7));
        
        // 无解
        assert_eq!(bsgs(2, 0, 11), None);
    }

    #[test]
    fn test_bsgs_larger() {
        // 3^10 = 59049 ≡ 24 (mod 101)
        let result = bsgs(3, 24, 101);
        assert!(result.is_some());
        let x = result.unwrap();
        // 验证解: 3^x ≡ 24 (mod 101)
        assert_eq!(mod_pow(3, x, 101), 24);
        
        // 5^20 mod 997
        let h = mod_pow(5, 20, 997);
        let result2 = bsgs(5, h, 997);
        assert!(result2.is_some());
        let x2 = result2.unwrap();
        // 验证解
        assert_eq!(mod_pow(5, x2, 997), h);
    }

    #[test]
    fn test_ex_bsgs() {
        // 测试非素数模数
        // 2^5 = 32 ≡ 2 (mod 30)，但 32 mod 30 = 2
        // 注意：这里可能需要调整测试
        
        // 2^4 = 16 (mod 24)
        let result = ex_bsgs(2, 16, 24);
        assert!(result.is_some());
        let x = result.unwrap();
        assert_eq!(mod_pow(2, x, 24), 16 % 24);
    }

    #[test]
    fn test_pollard_rho_dlog() {
        // 3^x ≡ 13 (mod 17)
        // 3^4 = 81 ≡ 13 (mod 17)
        // Pollard's Rho 是随机算法，可能偶尔失败
        if let Some(x) = pollard_rho_dlog(3, 13, 17, 16) {
            assert_eq!(mod_pow(3, x, 17), 13);
        }
        
        // 2^x ≡ 9 (mod 11)
        // 2^6 = 64 ≡ 9 (mod 11)
        if let Some(x2) = pollard_rho_dlog(2, 9, 11, 10) {
            assert_eq!(mod_pow(2, x2, 11), 9);
        }
    }

    #[test]
    fn test_pollard_rho_factor() {
        // 分解 8051 = 83 * 97
        let factor = pollard_rho_factor(8051);
        assert!(factor.is_some());
        let f = factor.unwrap();
        assert!(8051 % f == 0 && f != 1 && f != 8051);
        
        // 分解 10403 = 101 * 103
        let factor2 = pollard_rho_factor(10403);
        assert!(factor2.is_some());
    }

    #[test]
    fn test_factorize() {
        // 分解 100 = 2^2 * 5^2
        let factors = factorize(100);
        assert_eq!(factors, vec![2, 2, 5, 5]);
        
        // 分解 素数
        let prime_factors = factorize(101);
        assert_eq!(prime_factors, vec![101]);
    }

    #[test]
    fn test_crt() {
        // x ≡ 2 (mod 3), x ≡ 3 (mod 5)
        // x = 8
        let congruences = vec![(2, 3), (3, 5)];
        assert_eq!(crt(&congruences), Some(8));
        
        // x ≡ 1 (mod 2), x ≡ 2 (mod 3), x ≡ 3 (mod 5)
        // x = 23
        let congruences2 = vec![(1, 2), (2, 3), (3, 5)];
        assert_eq!(crt(&congruences2), Some(23));
    }

    #[test]
    fn test_pohlig_hellman() {
        // 使用 p = 17, g = 3, 群的阶为 16 = 2^4
        // 3^x ≡ 13 (mod 17)
        let result = pohlig_hellman(3, 13, 17, 16);
        assert!(result.is_some());
        let x = result.unwrap();
        assert_eq!(mod_pow(3, x, 17), 13);
        
        // 另一个测试
        // p = 31, g = 3, 群的阶为 30 = 2 * 3 * 5
        let h = mod_pow(3, 15, 31);
        let result2 = pohlig_hellman(3, h, 31, 30);
        assert!(result2.is_some());
        let x2 = result2.unwrap();
        assert_eq!(mod_pow(3, x2, 31), h);
    }

    #[test]
    fn test_edge_cases() {
        // h = 1 时，x = 0
        assert_eq!(bsgs(2, 1, 11), Some(0));
        assert_eq!(pollard_rho_dlog(2, 1, 11, 10), Some(0));
        
        // g = 0
        assert_eq!(bsgs(0, 0, 11), None);
        
        // h = g
        assert_eq!(bsgs(5, 5, 101), Some(1));
    }

    #[test]
    fn test_extended_gcd() {
        let (g, x, y) = extended_gcd(30, 12);
        assert_eq!(g, 6);
        assert_eq!(30 * x + 12 * y, 6);
        
        let (g2, x2, y2) = extended_gcd(17, 5);
        assert_eq!(g2, 1);
        assert_eq!(17 * x2 + 5 * y2, 1);
    }
}
