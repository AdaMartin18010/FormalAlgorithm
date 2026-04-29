package leetcode

import (
	"sort"
	"testing"
)

func TestShuffleAndReset(t *testing.T) {
	nums := []int{1, 2, 3}
	sol := ConstructorShuffleArray(nums)

	shuffled := sol.Shuffle()
	shuffledSorted := make([]int, len(shuffled))
	copy(shuffledSorted, shuffled)
	sort.Ints(shuffledSorted)
	expected := []int{1, 2, 3}
	for i := range expected {
		if shuffledSorted[i] != expected[i] {
			t.Errorf("Shuffle elements mismatch")
		}
	}

	reset := sol.Reset()
	for i := range expected {
		if reset[i] != expected[i] {
			t.Errorf("Reset failed at index %d", i)
		}
	}
}

func TestShuffleEdgeCases(t *testing.T) {
	sol := ConstructorShuffleArray([]int{})
	if len(sol.Shuffle()) != 0 {
		t.Error("Empty array shuffle failed")
	}

	sol2 := ConstructorShuffleArray([]int{5})
	if sol2.Shuffle()[0] != 5 {
		t.Error("Single element shuffle failed")
	}
}
