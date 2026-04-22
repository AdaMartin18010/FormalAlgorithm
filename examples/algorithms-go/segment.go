// Package algorithms provides Segment Tree implementation in Go.
package algorithms

// SegmentTree supports range sum query and point update.
// Time complexity: O(log n) per operation.
type SegmentTree struct {
	tree []int64
	n    int
}

// NewSegmentTree builds a segment tree from arr.
func NewSegmentTree(arr []int64) *SegmentTree {
	n := len(arr)
	st := &SegmentTree{tree: make([]int64, 4*n), n: n}
	st.build(0, 0, n-1, arr)
	return st
}

func (st *SegmentTree) build(node, l, r int, arr []int64) {
	if l == r {
		st.tree[node] = arr[l]
		return
	}
	mid := (l + r) >> 1
	st.build(2*node+1, l, mid, arr)
	st.build(2*node+2, mid+1, r, arr)
	st.tree[node] = st.tree[2*node+1] + st.tree[2*node+2]
}

// Query returns sum of [ql, qr] (inclusive, 0-based).
func (st *SegmentTree) Query(ql, qr int) int64 {
	return st.query(0, 0, st.n-1, ql, qr)
}

func (st *SegmentTree) query(node, l, r, ql, qr int) int64 {
	if ql <= l && r <= qr {
		return st.tree[node]
	}
	if r < ql || l > qr {
		return 0
	}
	mid := (l + r) >> 1
	return st.query(2*node+1, l, mid, ql, qr) + st.query(2*node+2, mid+1, r, ql, qr)
}

// Update sets index idx to val.
func (st *SegmentTree) Update(idx int, val int64) {
	st.update(0, 0, st.n-1, idx, val)
}

func (st *SegmentTree) update(node, l, r, idx int, val int64) {
	if l == r {
		st.tree[node] = val
		return
	}
	mid := (l + r) >> 1
	if idx <= mid {
		st.update(2*node+1, l, mid, idx, val)
	} else {
		st.update(2*node+2, mid+1, r, idx, val)
	}
	st.tree[node] = st.tree[2*node+1] + st.tree[2*node+2]
}
