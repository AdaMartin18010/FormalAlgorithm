// Package algorithms provides number theory implementations in Go.
package algorithms

import "math"

// GCD computes the greatest common divisor using Euclidean algorithm.
// Time complexity: O(log min(a,b))
func GCD(a, b int64) int64 {
	if a < 0 { a = -a }
	if b < 0 { b = -b }
	for b != 0 {
		a, b = b, a%b
	}
	return a
}

// LCM computes the least common multiple.
func LCM(a, b int64) int64 {
	return int64(math.Abs(float64(a*b))) / GCD(a, b)
}

// ExtendedGCD returns [g, x, y] such that ax + by = gcd(a,b).
func ExtendedGCD(a, b int64) [3]int64 {
	if b == 0 {
		return [3]int64{a, 1, 0}
	}
	vals := ExtendedGCD(b, a%b)
	g, x1, y1 := vals[0], vals[1], vals[2]
	x := y1
	y := x1 - (a/b)*y1
	return [3]int64{g, x, y}
}

// ModInverse returns the modular inverse of a modulo mod, or -1 if it doesn't exist.
func ModInverse(a, mod int64) int64 {
	vals := ExtendedGCD(a, mod)
	if vals[0] != 1 {
		return -1
	}
	x := vals[1] % mod
	if x < 0 { x += mod }
	return x
}

// FastPow computes (base^exp) % mod using binary exponentiation.
// Time complexity: O(log exp)
func FastPow(base, exp, mod int64) int64 {
	result := int64(1 % mod)
	b := ((base % mod) + mod) % mod
	e := exp
	for e > 0 {
		if e&1 == 1 {
			result = (result * b) % mod
		}
		b = (b * b) % mod
		e >>= 1
	}
	return result
}

// IsPrime performs the Miller-Rabin primality test.
func IsPrime(n int64, k int) bool {
	if n < 2 { return false }
	if n == 2 || n == 3 { return true }
	if n%2 == 0 { return false }
	d := n - 1
	s := 0
	for d%2 == 0 { d /= 2; s++ }
	witnesses := []int64{2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37}
	for i := 0; i < min(k, len(witnesses)); i++ {
		a := witnesses[i]
		if a >= n { continue }
		x := FastPow(a, d, n)
		if x == 1 || x == n-1 { continue }
		composite := true
		for r := 1; r < s; r++ {
			x = (x * x) % n
			if x == n-1 { composite = false; break }
		}
		if composite { return false }
	}
	return true
}

// Sieve returns a boolean slice where isPrime[i] indicates if i is prime.
// Time complexity: O(n log log n)
func Sieve(n int) []bool {
	isPrime := make([]bool, n+1)
	for i := 2; i <= n; i++ { isPrime[i] = true }
	for i := 2; i*i <= n; i++ {
		if isPrime[i] {
			for j := i * i; j <= n; j += i {
				isPrime[j] = false
			}
		}
	}
	return isPrime
}

func min(a, b int) int {
	if a < b { return a }
	return b
}
