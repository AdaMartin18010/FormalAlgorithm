// Package algorithms provides Fenwick Tree implementation in Go.
package algorithms

// FenwickTree supports point update and prefix sum query.
// Time complexity: O(log n) per operation.
type FenwickTree struct {
	tree []int64
}

// NewFenwickTree creates a Fenwick tree with n elements.
func NewFenwickTree(n int) *FenwickTree {
	return &FenwickTree{tree: make([]int64, n+1)}
}

// Add adds delta at index idx (0-based).
func (ft *FenwickTree) Add(idx int, delta int64) {
	i := idx + 1
	for i < len(ft.tree) {
		ft.tree[i] += delta
		i += i & -i
	}
}

// PrefixSum returns sum of [0, idx] (0-based).
func (ft *FenwickTree) PrefixSum(idx int) int64 {
	var res int64
	i := idx + 1
	for i > 0 {
		res += ft.tree[i]
		i -= i & -i
	}
	return res
}

// RangeSum returns sum of [l, r] (0-based).
func (ft *FenwickTree) RangeSum(l, r int) int64 {
	return ft.PrefixSum(r) - ft.PrefixSum(l-1)
}
