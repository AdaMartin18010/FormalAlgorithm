// Package algorithms provides tree algorithm implementations in Go.
package algorithms

import "math"

// LCA represents a Lowest Common Ancestor structure using binary lifting.
// Preprocessing: O(n log n), Query: O(log n)
type LCA struct {
	n     int
	logN  int
	up    [][]int
	depth []int
}

// NewLCA constructs an LCA structure from an adjacency list and root.
func NewLCA(adj [][]int, root int) *LCA {
	n := len(adj)
	logN := int(math.Log2(float64(n))) + 1
	up := make([][]int, n)
	for i := range up {
		up[i] = make([]int, logN)
		for j := range up[i] { up[i][j] = -1 }
	}
	depth := make([]int, n)
	var dfs func(u, p int)
	dfs = func(u, p int) {
		up[u][0] = p
		for j := 1; j < logN; j++ {
			if up[u][j-1] != -1 {
				up[u][j] = up[up[u][j-1]][j-1]
			}
		}
		for _, v := range adj[u] {
			if v != p {
				depth[v] = depth[u] + 1
				dfs(v, u)
			}
		}
	}
	dfs(root, -1)
	return &LCA{n: n, logN: logN, up: up, depth: depth}
}

// Query returns the LCA of u and v.
func (lca *LCA) Query(u, v int) int {
	if lca.depth[u] < lca.depth[v] {
		u, v = v, u
	}
	diff := lca.depth[u] - lca.depth[v]
	for j := lca.logN - 1; j >= 0; j-- {
		if (diff>>j)&1 == 1 {
			u = lca.up[u][j]
		}
	}
	if u == v { return u }
	for j := lca.logN - 1; j >= 0; j-- {
		if lca.up[u][j] != lca.up[v][j] {
			u = lca.up[u][j]
			v = lca.up[v][j]
		}
	}
	return lca.up[u][0]
}

// CartesianTree represents a min-heap Cartesian tree.
// Time complexity: O(n)
type CartesianTree struct {
	Parent []int
	Root   int
}

// NewCartesianTree builds a Cartesian tree from an array.
func NewCartesianTree(arr []int) *CartesianTree {
	n := len(arr)
	parent := make([]int, n)
	for i := range parent { parent[i] = -1 }
	stack := make([]int, n)
	top := -1
	last := -1
	for i := 0; i < n; i++ {
		last = -1
		for top >= 0 && arr[stack[top]] > arr[i] {
			last = stack[top]
			top--
		}
		if top >= 0 {
			parent[i] = stack[top]
		}
		if last != -1 {
			parent[last] = i
		}
		top++
		stack[top] = i
	}
	root := -1
	for i := 0; i < n; i++ {
		if parent[i] == -1 {
			root = i
			break
		}
	}
	return &CartesianTree{Parent: parent, Root: root}
}
