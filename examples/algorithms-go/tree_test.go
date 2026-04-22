package algorithms

import (
	"testing"
)

func TestLCA(t *testing.T) {
	adj := [][]int{{1, 2}, {3, 4}, {5}, {}, {}, {}}
	lca := NewLCA(adj, 0)
	if lca.Query(3, 4) != 1 {
		t.Errorf("LCA(3,4) = %d, want 1", lca.Query(3, 4))
	}
	if lca.Query(3, 5) != 0 {
		t.Errorf("LCA(3,5) = %d, want 0", lca.Query(3, 5))
	}
}

func TestCartesianTree(t *testing.T) {
	arr := []int{3, 2, 6, 1, 0, 8, 7}
	ct := NewCartesianTree(arr)
	if ct.Root != 4 {
		t.Errorf("Root = %d, want 4", ct.Root)
	}
}
