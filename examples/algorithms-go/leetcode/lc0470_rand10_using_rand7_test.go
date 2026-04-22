package leetcode

import "testing"

func TestRand10Range(t *testing.T) {
	for i := 0; i < 1000; i++ {
		v := Rand10()
		if v < 1 || v > 10 {
			t.Errorf("Rand10() = %d, out of range [1,10]", v)
		}
	}
}

func TestRand10UniformityApproximate(t *testing.T) {
	count := make([]int, 11)
	const N = 10000
	for i := 0; i < N; i++ {
		v := Rand10()
		count[v]++
	}

	expected := N / 10
	low := expected * 8 / 10
	high := expected * 12 / 10
	for v := 1; v <= 10; v++ {
		if count[v] < low || count[v] > high {
			t.Errorf("value %d count %d out of range [%d, %d]", v, count[v], low, high)
		}
	}
}
