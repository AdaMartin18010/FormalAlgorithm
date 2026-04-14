//! 素性测试与因数分解模块
//!
//! 提供高效的素数判定和因数分解算法：
//! - Miller-Rabin 素性测试（确定性/概率性）
//! - Pollard's Rho 因数分解
//! - 试除法与小素数筛

use std::collections::HashMap;

/// 快速幂（带模）
///
/// # 复杂度
/// - 时间: O(log exp)
fn mod_pow(mut base: u128, mut exp: u128, modulus: u128) -> u128 {
    if modulus == 1 {
        return 0;
    }
    let mut result = 1u128;
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

/// Miller-Rabin 素性测试
///
/// # 算法原理
/// 基于费马小定理和二次探测定理：
/// 若 p 是素数，则对于任意 a (1 < a < p-1)：
/// 1. a^(p-1) ≡ 1 (mod p)
/// 2. 若 x² ≡ 1 (mod p)，则 x ≡ ±1 (mod p)
///
/// # 复杂度
/// - 时间: O(k log³n)，k为测试轮数
/// - 空间: O(1)
///
/// # 参数
/// - `n`: 待测试数
/// - `k`: 测试轮数（决定错误概率 ≤ 4^(-k)）
///
/// # 返回值
/// - `true`: 可能是素数（概率性）
/// - `false`: 一定是合数
///
/// # 示例
/// ```
/// use formal_algorithms::primality_test::is_probable_prime;
/// assert!(is_probable_prime(17, 10));
/// assert!(!is_probable_prime(18, 10));
/// ```
pub fn is_probable_prime(n: u128, k: u32) -> bool {
    if n < 2 {
        return false;
    }
    if n == 2 || n == 3 {
        return true;
    }
    if n % 2 == 0 {
        return false;
    }

    // 将 n-1 写成 d * 2^s
    let mut d = n - 1;
    let mut s = 0;
    while d % 2 == 0 {
        d /= 2;
        s += 1;
    }

    // 使用确定性底数（对于 n < 2^64）
    let witnesses: Vec<u128> = if n < 3_474_749_660_383 {
        vec![2, 3, 5, 7, 11, 13, 17]
    } else if n < 341_550_071_728_321 {
        vec![2, 3, 5, 7, 11, 13, 17]
    } else if n < 3_825_123_056_546_413_051 {
        vec![2, 3, 5, 7, 11, 13, 17, 19, 23]
    } else {
        // 随机选择底数
        (0..k).map(|i| (2 + i as u128 * 7) % (n - 3) + 2).collect()
    };

    for &a in &witnesses {
        if a >= n {
            continue;
        }

        let mut x = mod_pow(a, d, n);
        if x == 1 || x == n - 1 {
            continue;
        }

        let mut composite = true;
        for _ in 1..s {
            x = (x * x) % n;
            if x == n - 1 {
                composite = false;
                break;
            }
        }

        if composite {
            return false;
        }
    }

    true
}

/// 确定性素性测试（64位整数）
///
/// # 算法
/// 对于 64 位整数，使用确定的底数集保证正确性
///
/// # 复杂度
/// - 时间: O(log³n)
/// - 空间: O(1)
///
/// # 参数
/// - `n`: 待测试数（n < 2^64）
///
/// # 返回值
/// - `true`: 是素数
/// - `false`: 是合数
pub fn is_prime_deterministic(n: u64) -> bool {
    if n < 2 {
        return false;
    }
    if n == 2 || n == 3 {
        return true;
    }
    if n % 2 == 0 {
        return false;
    }

    // 小素数表
    let small_primes: [u64; 12] = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41];
    for &p in &small_primes {
        if n == p {
            return true;
        }
        if n % p == 0 {
            return false;
        }
    }

    // 确定底数（Jaeschke 1993, Sinclair 2011）
    let witnesses: [u64; 12] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37];

    let mut d = n - 1;
    let mut s = 0u32;
    while d % 2 == 0 {
        d /= 2;
        s += 1;
    }

    for &a in &witnesses {
        if a % n == 0 {
            continue;
        }

        let mut x = mod_pow(a as u128, d as u128, n as u128) as u64;
        if x == 1 || x == n - 1 {
            continue;
        }

        let mut composite = true;
        for _ in 1..s {
            x = ((x as u128 * x as u128) % n as u128) as u64;
            if x == n - 1 {
                composite = false;
                break;
            }
        }

        if composite {
            return false;
        }
    }

    true
}

/// 最大公约数
fn gcd(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

/// Pollard's Rho 因数分解算法
///
/// # 算法原理
/// Floyd 判圈算法 + 随机多项式：
/// 1. 选择随机多项式 f(x) = x² + c (mod n)
/// 2. 使用快慢指针在序列中寻找碰撞
/// 3. 通过 gcd(|x - y|, n) 寻找因子
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
/// - `None`: 未找到
///
/// # 示例
/// ```
/// use formal_algorithms::primality_test::pollard_rho;
/// let factor = pollard_rho(8051);
/// assert!(factor.is_some());
/// ```
pub fn pollard_rho(n: u128) -> Option<u128> {
    if n % 2 == 0 {
        return Some(2);
    }
    if n % 3 == 0 {
        return Some(3);
    }

    let f = |x: u128, c: u128| -> u128 {
        ((x * x) % n + c) % n
    };

    // 尝试不同的参数
    for c in 1u128..100 {
        let mut x = 2u128;
        let mut y = 2u128;
        let mut d = 1u128;

        while d == 1 {
            x = f(x, c);
            y = f(f(y, c), c);
            d = gcd((x as i128 - y as i128).abs() as u128, n);
        }

        if d != n {
            return Some(d);
        }
    }

    None
}

/// 试除法因数分解
///
/// # 复杂度
/// - 时间: O(√n)
/// - 空间: O(1)
///
/// 适用于小整数或获取小素因子
fn trial_division(mut n: u128, limit: u128) -> Vec<u128> {
    let mut factors = vec![];

    // 处理因子2
    while n % 2 == 0 {
        factors.push(2);
        n /= 2;
    }

    // 奇数因子
    let mut i = 3u128;
    while i <= limit && i * i <= n {
        while n % i == 0 {
            factors.push(i);
            n /= i;
        }
        i += 2;
    }

    if n > 1 {
        factors.push(n);
    }

    factors
}

/// 完整因数分解
///
/// # 算法
/// 1. 先用试除法分解小因子
/// 2. 对剩余大数使用 Pollard's Rho
///
/// # 复杂度
/// - 期望时间: O(n^(1/4))
///
/// # 返回值
/// n 的所有素因子（含重复，升序）
///
/// # 示例
/// ```
/// use formal_algorithms::primality_test::factorize;
/// let factors = factorize(100);
/// assert_eq!(factors, vec![2, 2, 5, 5]);
/// ```
pub fn factorize(mut n: u128) -> Vec<u128> {
    if n <= 1 {
        return vec![];
    }

    let mut factors: Vec<u128> = vec![];
    let mut stack = vec![n];

    while let Some(m) = stack.pop() {
        if m == 1 {
            continue;
        }

        if is_probable_prime(m, 10) {
            factors.push(m);
            continue;
        }

        // 试除小素数
        let small_primes: [u128; 15] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47];
        let mut found_small = false;
        for &p in &small_primes {
            if m % p == 0 {
                factors.push(p);
                stack.push(m / p);
                found_small = true;
                break;
            }
        }
        if found_small {
            continue;
        }

        // 使用 Pollard's Rho
        if let Some(d) = pollard_rho(m) {
            stack.push(d);
            stack.push(m / d);
        } else {
            factors.push(m);
        }
    }

    factors.sort();
    factors
}

/// 获取素因子及其指数
///
/// # 返回值
/// (素因子, 指数) 的向量
///
/// # 示例
/// ```
/// use formal_algorithms::primality_test::prime_factorization;
/// let pf = prime_factorization(100);
/// assert_eq!(pf, vec![(2, 2), (5, 2)]); // 100 = 2^2 * 5^2
/// ```
pub fn prime_factorization(n: u128) -> Vec<(u128, u32)> {
    let factors = factorize(n);
    let mut result: Vec<(u128, u32)> = vec![];

    for &f in &factors {
        if let Some(last) = result.last_mut() {
            if last.0 == f {
                last.1 += 1;
                continue;
            }
        }
        result.push((f, 1));
    }

    result
}

/// 欧拉函数 φ(n)
///
/// φ(n) = 小于等于 n 且与 n 互素的正整数个数
///
/// # 公式
/// φ(n) = n * Π(1 - 1/p)，其中 p 取遍 n 的所有不同素因子
///
/// # 复杂度
/// - 时间: O(√n)（需分解 n）
///
/// # 示例
/// ```
/// use formal_algorithms::primality_test::euler_totient;
/// assert_eq!(euler_totient(10), 4); // 1, 3, 7, 9
/// ```
pub fn euler_totient(n: u128) -> u128 {
    if n == 0 {
        return 0;
    }
    if n == 1 {
        return 1;
    }

    let pf = prime_factorization(n);
    let mut result = n;

    for (p, _) in pf {
        result = result / p * (p - 1);
    }

    result
}

/// 莫比乌斯函数 μ(n)
///
/// - μ(1) = 1
/// - μ(n) = 0，若 n 有平方因子
/// - μ(n) = (-1)^k，若 n 是 k 个不同素数的乘积
///
/// # 复杂度
/// - 时间: O(√n)
pub fn mobius(n: u128) -> i32 {
    if n == 1 {
        return 1;
    }

    let pf = prime_factorization(n);

    for &(_, exp) in &pf {
        if exp > 1 {
            return 0;
        }
    }

    if pf.len() % 2 == 0 {
        1
    } else {
        -1
    }
}

/// 素数筛（埃拉托斯特尼筛法）
///
/// # 复杂度
/// - 时间: O(n log log n)
/// - 空间: O(n)
///
/// # 返回值
/// 小于 n 的所有素数
///
/// # 示例
/// ```
/// use formal_algorithms::primality_test::sieve_of_eratosthenes;
/// let primes = sieve_of_eratosthenes(30);
/// assert_eq!(primes, vec![2, 3, 5, 7, 11, 13, 17, 19, 23, 29]);
/// ```
pub fn sieve_of_eratosthenes(n: usize) -> Vec<usize> {
    if n <= 2 {
        return vec![];
    }

    let mut is_prime = vec![true; n];
    is_prime[0] = false;
    is_prime[1] = false;

    for i in 2..((n as f64).sqrt() as usize + 1) {
        if is_prime[i] {
            for j in ((i * i)..n).step_by(i) {
                is_prime[j] = false;
            }
        }
    }

    is_prime
        .iter()
        .enumerate()
        .filter(|(_, &p)| p)
        .map(|(i, _)| i)
        .collect()
}

/// 线性筛（欧拉筛）
///
/// # 复杂度
/// - 时间: O(n)
/// - 空间: O(n)
///
/// 每个合数只被其最小素因子筛去一次
pub fn linear_sieve(n: usize) -> Vec<usize> {
    if n <= 2 {
        return vec![];
    }

    let mut is_composite = vec![false; n];
    let mut primes: Vec<usize> = vec![];

    for i in 2..n {
        if !is_composite[i] {
            primes.push(i);
        }
        for &p in &primes {
            if i * p >= n {
                break;
            }
            is_composite[i * p] = true;
            if i % p == 0 {
                break;
            }
        }
    }

    primes
}

/// 第 k 个素数
///
/// # 复杂度
/// - 时间: O(n log log n)，其中 n 为估计上界
///
/// # 示例
/// ```
/// use formal_algorithms::primality_test::nth_prime;
/// assert_eq!(nth_prime(1), 2);
/// assert_eq!(nth_prime(6), 13);
/// ```
pub fn nth_prime(k: usize) -> usize {
    if k == 0 {
        panic!("k must be positive");
    }

    // 估计上界：对于 n >= 6，p_n <= n (ln n + ln ln n)
    let mut upper = if k < 6 {
        15
    } else {
        let kf = k as f64;
        (kf * (kf.ln() + kf.ln().ln())).ceil() as usize + 3
    };

    loop {
        let primes = sieve_of_eratosthenes(upper);
        if primes.len() >= k {
            return primes[k - 1];
        }
        upper *= 2;
    }
}

/// 统计小于 n 的素数个数（素数计数函数 π(n)）
///
/// # 复杂度
/// - 时间: O(n log log n)
pub fn prime_counting(n: usize) -> usize {
    sieve_of_eratosthenes(n + 1).len()
}

/// 寻找下一个素数
///
/// # 复杂度
/// - 期望时间: O(k log³n)，k为测试轮数
///
/// # 示例
/// ```
/// use formal_algorithms::primality_test::next_prime;
/// assert_eq!(next_prime(10), 11);
/// assert_eq!(next_prime(13), 17);
/// ```
pub fn next_prime(n: u128) -> u128 {
    if n < 2 {
        return 2;
    }
    
    let mut candidate = n + 1;
    if candidate % 2 == 0 {
        candidate += 1;
    }
    
    while !is_probable_prime(candidate, 20) {
        candidate += 2;
    }
    
    candidate
}

/// 寻找前一个素数
///
/// # 返回值
/// - `Some(p)`: 小于 n 的最大素数
/// - `None`: n <= 2
pub fn prev_prime(n: u128) -> Option<u128> {
    if n <= 2 {
        return None;
    }
    
    let mut candidate = n - 1;
    if candidate % 2 == 0 && candidate > 2 {
        candidate -= 1;
    }
    
    while candidate >= 2 {
        if is_probable_prime(candidate, 20) {
            return Some(candidate);
        }
        candidate -= if candidate == 2 { 1 } else { 2 };
    }
    
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_probable_prime() {
        // 小素数
        assert!(is_probable_prime(2, 10));
        assert!(is_probable_prime(3, 10));
        assert!(is_probable_prime(17, 10));
        assert!(is_probable_prime(97, 10));
        
        // 合数
        assert!(!is_probable_prime(4, 10));
        assert!(!is_probable_prime(15, 10));
        assert!(!is_probable_prime(100, 10));
        
        // 大素数（已知）
        assert!(is_probable_prime(1_000_003, 10));
        assert!(!is_probable_prime(1_000_004, 10));
        
        // 边界情况
        assert!(!is_probable_prime(0, 10));
        assert!(!is_probable_prime(1, 10));
    }

    #[test]
    fn test_is_prime_deterministic() {
        // 小素数
        assert!(is_prime_deterministic(2));
        assert!(is_prime_deterministic(97));
        assert!(!is_prime_deterministic(100));
        
        // 64位大素数
        assert!(is_prime_deterministic(9_223_372_036_854_775_783)); // 大素数
    }

    #[test]
    fn test_pollard_rho() {
        // 8051 = 83 * 97
        let factor = pollard_rho(8051).unwrap();
        assert!(8051 % factor == 0);
        assert!(factor != 1 && factor != 8051);
        
        // 10403 = 101 * 103
        let factor2 = pollard_rho(10403).unwrap();
        assert!(10403 % factor2 == 0);
    }

    #[test]
    fn test_factorize() {
        // 100 = 2^2 * 5^2
        assert_eq!(factorize(100), vec![2, 2, 5, 5]);
        
        // 97 是素数
        assert_eq!(factorize(97), vec![97]);
        
        // 1
        assert_eq!(factorize(1), vec![]);
        
        // 大数分解
        let factors = factorize(2 * 3 * 5 * 7 * 11 * 13);
        assert_eq!(factors, vec![2, 3, 5, 7, 11, 13]);
    }

    #[test]
    fn test_prime_factorization() {
        let pf = prime_factorization(360); // 360 = 2^3 * 3^2 * 5
        assert_eq!(pf, vec![(2, 3), (3, 2), (5, 1)]);
    }

    #[test]
    fn test_euler_totient() {
        assert_eq!(euler_totient(1), 1);
        assert_eq!(euler_totient(10), 4);  // 1, 3, 7, 9
        assert_eq!(euler_totient(12), 4);  // 1, 5, 7, 11
        assert_eq!(euler_totient(97), 96); // 素数的欧拉函数
    }

    #[test]
    fn test_mobius() {
        assert_eq!(mobius(1), 1);
        assert_eq!(mobius(2), -1);   // 1个素因子
        assert_eq!(mobius(6), 1);    // 2个素因子 (2*3)
        assert_eq!(mobius(30), -1);  // 3个素因子 (2*3*5)
        assert_eq!(mobius(4), 0);    // 有平方因子
        assert_eq!(mobius(12), 0);   // 有平方因子
    }

    #[test]
    fn test_sieve_of_eratosthenes() {
        let primes = sieve_of_eratosthenes(30);
        assert_eq!(primes, vec![2, 3, 5, 7, 11, 13, 17, 19, 23, 29]);
        
        assert_eq!(sieve_of_eratosthenes(2), vec![]);
        assert_eq!(sieve_of_eratosthenes(3), vec![2]);
    }

    #[test]
    fn test_linear_sieve() {
        let primes = linear_sieve(30);
        assert_eq!(primes, vec![2, 3, 5, 7, 11, 13, 17, 19, 23, 29]);
    }

    #[test]
    fn test_nth_prime() {
        assert_eq!(nth_prime(1), 2);
        assert_eq!(nth_prime(2), 3);
        assert_eq!(nth_prime(6), 13);
        assert_eq!(nth_prime(10), 29);
        assert_eq!(nth_prime(25), 97);
    }

    #[test]
    fn test_next_prime() {
        assert_eq!(next_prime(10), 11);
        assert_eq!(next_prime(13), 17);
        assert_eq!(next_prime(1), 2);
        assert_eq!(next_prime(2), 3);
    }

    #[test]
    fn test_prev_prime() {
        assert_eq!(prev_prime(10), Some(7));
        assert_eq!(prev_prime(17), Some(13));
        assert_eq!(prev_prime(2), None);
        assert_eq!(prev_prime(3), Some(2));
    }

    #[test]
    fn test_prime_counting() {
        assert_eq!(prime_counting(10), 4);   // 2, 3, 5, 7
        assert_eq!(prime_counting(30), 10);
        assert_eq!(prime_counting(100), 25);
    }

    #[test]
    fn test_mod_pow() {
        assert_eq!(mod_pow(2, 10, 1000), 24);
        assert_eq!(mod_pow(3, 5, 100), 43);
        assert_eq!(mod_pow(5, 0, 100), 1);
    }

    #[test]
    fn test_large_prime() {
        // 测试大数素性
        let large_prime: u128 = 1_000_000_007;
        assert!(is_probable_prime(large_prime, 20));
        
        // 测试邻近的合数
        assert!(!is_probable_prime(large_prime - 1, 10));
        assert!(!is_probable_prime(large_prime + 1, 10));
    }

    #[test]
    fn test_carmichael_numbers() {
        // Carmichael数是合数但能通过某些费马测试
        // 最小的Carmichael数是 561 = 3 * 11 * 17
        assert!(!is_probable_prime(561, 10));
        
        let factors = factorize(561);
        assert!(factors.len() > 1 || factors[0] != 561);
    }
}
