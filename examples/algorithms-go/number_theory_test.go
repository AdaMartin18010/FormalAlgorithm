package algorithms

import (
	"testing"
)

func TestGCD(t *testing.T) {
	if GCD(48, 18) != 6 {
		t.Error("GCD failed")
	}
}

func TestFastPow(t *testing.T) {
	if FastPow(2, 10, 1000) != 24 {
		t.Errorf("FastPow failed")
	}
}

func TestIsPrime(t *testing.T) {
	if !IsPrime(97, 5) {
		t.Error("IsPrime(97) should be true")
	}
	if IsPrime(100, 5) {
		t.Error("IsPrime(100) should be false")
	}
}

func TestSieve(t *testing.T) {
	sp := Sieve(10)
	if !sp[2] || !sp[3] || !sp[5] || !sp[7] {
		t.Error("Sieve missed primes")
	}
	if sp[4] || sp[9] {
		t.Error("Sieve false positives")
	}
}
