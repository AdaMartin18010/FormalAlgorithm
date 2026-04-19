package algorithms

import "testing"

func TestUnionFindBasic(t *testing.T) {
	uf := NewUnionFind(5)
	if uf.Count() != 5 {
		t.Errorf("Count = %d, want 5", uf.Count())
	}

	uf.Union(0, 1)
	if !uf.Connected(0, 1) {
		t.Error("0 and 1 should be connected")
	}
	if uf.Count() != 4 {
		t.Errorf("Count = %d, want 4", uf.Count())
	}

	uf.Union(1, 2)
	if !uf.Connected(0, 2) {
		t.Error("0 and 2 should be connected via 1")
	}
	if uf.Count() != 3 {
		t.Errorf("Count = %d, want 3", uf.Count())
	}
}

func TestUnionFindNoConnection(t *testing.T) {
	uf := NewUnionFind(5)
	uf.Union(0, 1)
	uf.Union(2, 3)
	if uf.Connected(0, 2) {
		t.Error("0 and 2 should not be connected")
	}
	if uf.Count() != 3 {
		t.Errorf("Count = %d, want 3", uf.Count())
	}
}

func TestUnionFindSelf(t *testing.T) {
	uf := NewUnionFind(3)
	if !uf.Connected(0, 0) {
		t.Error("Self connection should be true")
	}
}

func TestUnionFindLarge(t *testing.T) {
	n := 1000
	uf := NewUnionFind(n)
	for i := 0; i < n-1; i++ {
		uf.Union(i, i+1)
	}
	if uf.Count() != 1 {
		t.Errorf("Count = %d, want 1", uf.Count())
	}
	if !uf.Connected(0, n-1) {
		t.Error("0 and n-1 should be connected")
	}
}

func TestUnionFindPathCompression(t *testing.T) {
	uf := NewUnionFind(5)
	uf.Union(0, 1)
	uf.Union(1, 2)
	uf.Union(2, 3)
	uf.Union(3, 4)

	// All should have the same root after path compression
	root := uf.Find(0)
	for i := 1; i < 5; i++ {
		if uf.Find(i) != root {
			t.Errorf("Find(%d) = %d, want %d", i, uf.Find(i), root)
		}
	}
}
