//! 数论算法
//! 
//! 包含:
//! - 最大公约数 (GCD)
//! - 模幂运算
//! - 素数测试 (Miller-Rabin)

/// GCD
pub fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

/// 模幂运算
pub fn mod_pow(mut base: u64, mut exp: u64, mod_val: u64) -> u64 {
    let mut result = 1;
    base %= mod_val;
    while exp > 0 {
        if exp & 1 == 1 {
            result = (result * base) % mod_val;
        }
        base = (base * base) % mod_val;
        exp >>= 1;
    }
    result
}

/// Miller-Rabin素数测试
pub fn is_prime(n: u64) -> bool {
    if n < 2 { return false; }
    if n == 2 || n == 3 { return true; }
    if n % 2 == 0 { return false; }
    
    let mut d = n - 1;
    let mut s = 0;
    while d % 2 == 0 {
        d /= 2;
        s += 1;
    }
    
    let bases = [2, 3, 5, 7, 11, 13];
    for &a in &bases {
        if a % n == 0 { continue; }
        let mut x = mod_pow(a, d, n);
        if x == 1 || x == n - 1 { continue; }
        
        let mut composite = true;
        for _ in 0..s-1 {
            x = mod_pow(x, 2, n);
            if x == n - 1 {
                composite = false;
                break;
            }
        }
        if composite { return false; }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_gcd() {
        assert_eq!(gcd(48, 18), 6);
    }
    
    #[test]
    fn test_is_prime() {
        assert!(is_prime(97));
        assert!(!is_prime(100));
    }
}
