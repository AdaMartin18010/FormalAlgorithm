package algorithms

import "testing"

func TestKnapsack01(t *testing.T) {
	weights := []int{2, 3, 4, 5}
	values := []int{3, 4, 5, 6}
	capacity := 5
	result := Knapsack01(weights, values, capacity)
	if result != 7 {
		t.Errorf("Knapsack01 = %d, want 7", result)
	}
}

func TestKnapsack01Empty(t *testing.T) {
	if Knapsack01([]int{}, []int{}, 10) != 0 {
		t.Error("Knapsack01 with empty input should return 0")
	}
}

func TestKnapsack01ZeroCapacity(t *testing.T) {
	if Knapsack01([]int{1, 2}, []int{10, 20}, 0) != 0 {
		t.Error("Knapsack01 with zero capacity should return 0")
	}
}

func TestKnapsack01WithSelection(t *testing.T) {
	weights := []int{2, 3, 4, 5}
	values := []int{3, 4, 5, 6}
	capacity := 5
	maxVal, selected := Knapsack01WithSelection(weights, values, capacity)
	if maxVal != 7 {
		t.Errorf("Knapsack01WithSelection value = %d, want 7", maxVal)
	}
	// Selected items should sum to capacity 5: items 0 (weight 2) + 1 (weight 3) = 5
	selectedSet := make(map[int]bool)
	for _, idx := range selected {
		selectedSet[idx] = true
	}
	totalWeight := 0
	for _, idx := range selected {
		totalWeight += weights[idx]
	}
	if totalWeight > capacity {
		t.Errorf("Selected weight %d exceeds capacity %d", totalWeight, capacity)
	}
}

func TestLISLength(t *testing.T) {
	tests := []struct {
		input    []int
		expected int
	}{
		{[]int{10, 9, 2, 5, 3, 7, 101, 18}, 4},
		{[]int{}, 0},
		{[]int{1}, 1},
		{[]int{1, 2, 3, 4, 5}, 5},
		{[]int{5, 4, 3, 2, 1}, 1},
		{[]int{3, 10, 2, 1, 20}, 3},
	}
	for _, tt := range tests {
		result := LISLength(tt.input)
		if result != tt.expected {
			t.Errorf("LISLength(%v) = %d, want %d", tt.input, result, tt.expected)
		}
	}
}

func TestLISDP(t *testing.T) {
	arr := []int{10, 9, 2, 5, 3, 7, 101, 18}
	result := LISDP(arr)
	if len(result) != 4 {
		t.Errorf("LISDP length = %d, want 4", len(result))
	}
	// Verify it's increasing
	for i := 1; i < len(result); i++ {
		if result[i] <= result[i-1] {
			t.Errorf("LISDP result not increasing: %v", result)
		}
	}
}

func TestLISDPEmpty(t *testing.T) {
	result := LISDP([]int{})
	if len(result) != 0 {
		t.Error("LISDP on empty slice should return empty")
	}
}

func TestCoinChangeMin(t *testing.T) {
	tests := []struct {
		coins    []int
		amount   int
		expected int
	}{
		{[]int{1, 2, 5}, 11, 3},
		{[]int{1, 2, 5}, 3, 2},
		{[]int{2}, 3, -1},
		{[]int{1}, 0, 0},
		{[]int{1, 3, 4}, 6, 2},
	}
	for _, tt := range tests {
		result := CoinChangeMin(tt.coins, tt.amount)
		if result != tt.expected {
			t.Errorf("CoinChangeMin(%v, %d) = %d, want %d", tt.coins, tt.amount, result, tt.expected)
		}
	}
}

func TestCoinChangeWays(t *testing.T) {
	tests := []struct {
		coins    []int
		amount   int
		expected int
	}{
		{[]int{1, 2, 5}, 5, 4},
		{[]int{2}, 3, 0},
		{[]int{1, 3, 4}, 6, 4},
		{[]int{1, 2, 3}, 4, 4},
	}
	for _, tt := range tests {
		result := CoinChangeWays(tt.coins, tt.amount)
		if result != tt.expected {
			t.Errorf("CoinChangeWays(%v, %d) = %d, want %d", tt.coins, tt.amount, result, tt.expected)
		}
	}
}
