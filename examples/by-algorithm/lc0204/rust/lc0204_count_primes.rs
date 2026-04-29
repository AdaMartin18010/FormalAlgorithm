/// LeetCode 204. Count Primes
///
/// Given an integer `n`, return the number of prime numbers that are strictly less than `n`.
///
/// # Approach
/// Sieve of Eratosthenes. For each prime `i` starting from 2,
/// mark all multiples of `i` starting from `i*i` as non-prime.
///
/// # Correctness Proof
/// A composite number `c < n` has at least one prime factor `p ≤ √c < √n`.
/// When the outer loop reaches `i = p`, the inner loop marks `c` as non-prime.
/// Conversely, any number marked is a multiple of some `i ≥ 2`, hence composite.
///
/// # Complexity
/// - Time complexity: O(n log log n)
/// - Space complexity: O(n)

pub struct Solution;

impl Solution {
    pub fn count_primes(n: i32) -> i32 {
        if n <= 2 {
            return 0;
        }

        let n = n as usize;
        let mut is_prime = vec![true; n];
        is_prime[0] = false;
        is_prime[1] = false;

        for i in 2.. {
            if i * i >= n {
                break;
            }
            if is_prime[i] {
                // Start from i*i because smaller multiples are already marked
                let mut j = i * i;
                while j < n {
                    is_prime[j] = false;
                    j += i;
                }
            }
        }

        is_prime.iter().filter(|&&x| x).count() as i32
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_example_1() {
        assert_eq!(Solution::count_primes(10), 4); // 2, 3, 5, 7
    }

    #[test]
    fn test_example_2() {
        assert_eq!(Solution::count_primes(0), 0);
    }

    #[test]
    fn test_example_3() {
        assert_eq!(Solution::count_primes(1), 0);
    }

    #[test]
    fn test_n_is_prime() {
        assert_eq!(Solution::count_primes(7), 3); // 2, 3, 5
    }

    #[test]
    fn test_large() {
        assert_eq!(Solution::count_primes(100), 25);
    }
}
