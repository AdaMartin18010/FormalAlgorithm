package leetcode

// LeetCode 204 - Count Primes
// https://leetcode.com/problems/count-primes/
//
// Problem: Given an integer n, return the number of prime numbers strictly less than n.
//
// Approach: Sieve of Eratosthenes. For each prime i starting from 2,
// mark all multiples of i starting from i*i as non-prime.
//
// Time: O(n log log n), Space: O(n).

// CountPrimes returns the number of primes strictly less than n.
func CountPrimes(n int) int {
	if n <= 2 {
		return 0
	}

	isPrime := make([]bool, n)
	for i := 2; i < n; i++ {
		isPrime[i] = true
	}

	for i := 2; i*i < n; i++ {
		if isPrime[i] {
			for j := i * i; j < n; j += i {
				isPrime[j] = false
			}
		}
	}

	count := 0
	for _, v := range isPrime {
		if v {
			count++
		}
	}
	return count
}
