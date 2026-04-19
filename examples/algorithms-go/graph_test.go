package algorithms

import (
	"reflect"
	"testing"
)

func TestBFS(t *testing.T) {
	graph := map[int][]int{
		0: {1, 2},
		1: {2},
		2: {3},
		3: {},
	}
	result := BFS(graph, 0)
	expected := []int{0, 1, 2, 3}
	if !reflect.DeepEqual(result, expected) {
		t.Errorf("BFS = %v, want %v", result, expected)
	}
}

func TestBFSEmpty(t *testing.T) {
	if len(BFS(map[int][]int{}, 0)) != 0 {
		t.Error("BFS on empty graph should return empty")
	}
}

func TestBFSSingleVertex(t *testing.T) {
	graph := map[int][]int{0: {}}
	result := BFS(graph, 0)
	if !reflect.DeepEqual(result, []int{0}) {
		t.Errorf("BFS single vertex = %v, want [0]", result)
	}
}

func TestBFSShortestPath(t *testing.T) {
	graph := map[int][]int{
		0: {1, 2},
		1: {3},
		2: {3},
		3: {},
	}
	path := BFSShortestPath(graph, 0, 3)
	if path == nil || len(path) != 3 {
		t.Errorf("Shortest path length should be 3, got %v", path)
	}
	if path != nil && (path[0] != 0 || path[2] != 3) {
		t.Errorf("Shortest path should start at 0 and end at 3, got %v", path)
	}
}

func TestBFSShortestPathNoPath(t *testing.T) {
	graph := map[int][]int{
		0: {1},
		1: {},
		2: {3},
		3: {},
	}
	path := BFSShortestPath(graph, 0, 3)
	if path != nil {
		t.Errorf("Should return nil for disconnected graph, got %v", path)
	}
}

func TestDFS(t *testing.T) {
	graph := map[int][]int{
		0: {1, 2},
		1: {3},
		2: {3},
		3: {},
	}
	result := DFS(graph, 0)
	if len(result) != 4 || result[0] != 0 {
		t.Errorf("DFS = %v, want 4 elements starting with 0", result)
	}
	seen := make(map[int]bool)
	for _, v := range result {
		seen[v] = true
	}
	if len(seen) != 4 {
		t.Error("DFS should visit all 4 vertices")
	}
}

func TestDFSEmpty(t *testing.T) {
	if len(DFS(map[int][]int{}, 0)) != 0 {
		t.Error("DFS on empty graph should return empty")
	}
}

func TestHasPath(t *testing.T) {
	graph := map[int][]int{
		0: {1, 2},
		1: {3},
		2: {},
		3: {},
	}
	if !HasPath(graph, 0, 3) {
		t.Error("Should have path from 0 to 3")
	}
	if HasPath(graph, 2, 3) {
		t.Error("Should not have path from 2 to 3")
	}
	if !HasPath(graph, 0, 0) {
		t.Error("Should have path from 0 to 0")
	}
}

func TestDijkstra(t *testing.T) {
	graph := map[int][][2]int{
		0: {{1, 4}, {2, 1}},
		1: {{3, 1}},
		2: {{1, 2}, {3, 5}},
		3: {},
	}
	dist := Dijkstra(graph, 0)
	if dist[0] != 0 {
		t.Errorf("dist[0] = %d, want 0", dist[0])
	}
	if dist[1] != 3 {
		t.Errorf("dist[1] = %d, want 3", dist[1])
	}
	if dist[2] != 1 {
		t.Errorf("dist[2] = %d, want 1", dist[2])
	}
	if dist[3] != 4 {
		t.Errorf("dist[3] = %d, want 4", dist[3])
	}
}

func TestDijkstraSingleVertex(t *testing.T) {
	graph := map[int][][2]int{
		0: {},
	}
	dist := Dijkstra(graph, 0)
	if dist[0] != 0 {
		t.Errorf("dist[0] = %d, want 0", dist[0])
	}
}

func TestDijkstraDisconnected(t *testing.T) {
	graph := map[int][][2]int{
		0: {{1, 1}},
		1: {},
		2: {},
	}
	dist := Dijkstra(graph, 0)
	maxInt32 := int(^uint32(0) >> 1)
	if dist[2] != maxInt32 {
		t.Errorf("dist[2] = %d, want MaxInt32 (%d)", dist[2], maxInt32)
	}
}
