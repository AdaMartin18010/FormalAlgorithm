package algorithms

import (
	"container/heap"
	"math"
)

// BFS returns vertices in breadth-first search order starting from start.
// Time complexity: O(V + E). Space complexity: O(V).
func BFS(adj map[int][]int, start int) []int {
	if _, ok := adj[start]; !ok {
		return []int{}
	}
	visited := make(map[int]bool)
	queue := []int{start}
	visited[start] = true
	order := []int{}

	for len(queue) > 0 {
		v := queue[0]
		queue = queue[1:]
		order = append(order, v)
		for _, neighbor := range adj[v] {
			if !visited[neighbor] {
				visited[neighbor] = true
				queue = append(queue, neighbor)
			}
		}
	}
	return order
}

// BFSShortestPath returns the shortest path from start to goal using BFS.
// Returns nil if no path exists.
func BFSShortestPath(adj map[int][]int, start, goal int) []int {
	if start == goal {
		return []int{start}
	}
	if _, ok := adj[start]; !ok {
		return nil
	}
	visited := make(map[int]bool)
	visited[start] = true
	type node struct {
		vertex int
		path   []int
	}
	queue := []node{{start, []int{start}}}

	for len(queue) > 0 {
		curr := queue[0]
		queue = queue[1:]
		for _, neighbor := range adj[curr.vertex] {
			if neighbor == goal {
				return append(append([]int{}, curr.path...), neighbor)
			}
			if !visited[neighbor] {
				visited[neighbor] = true
				newPath := append(append([]int{}, curr.path...), neighbor)
				queue = append(queue, node{neighbor, newPath})
			}
		}
	}
	return nil
}

// DFS returns vertices in depth-first search order starting from start.
// Time complexity: O(V + E). Space complexity: O(V).
func DFS(adj map[int][]int, start int) []int {
	if _, ok := adj[start]; !ok {
		return []int{}
	}
	visited := make(map[int]bool)
	stack := []int{start}
	visited[start] = true
	order := []int{}

	for len(stack) > 0 {
		v := stack[len(stack)-1]
		stack = stack[:len(stack)-1]
		order = append(order, v)
		// Push neighbors in reverse order for predictable order
		neighbors := adj[v]
		for i := len(neighbors) - 1; i >= 0; i-- {
			if !visited[neighbors[i]] {
				visited[neighbors[i]] = true
				stack = append(stack, neighbors[i])
			}
		}
	}
	return order
}

// HasPath checks if a path exists from start to goal.
func HasPath(adj map[int][]int, start, goal int) bool {
	if start == goal {
		return true
	}
	if _, ok := adj[start]; !ok {
		return false
	}
	visited := make(map[int]bool)
	stack := []int{start}
	visited[start] = true

	for len(stack) > 0 {
		v := stack[len(stack)-1]
		stack = stack[:len(stack)-1]
		for _, neighbor := range adj[v] {
			if neighbor == goal {
				return true
			}
			if !visited[neighbor] {
				visited[neighbor] = true
				stack = append(stack, neighbor)
			}
		}
	}
	return false
}

// item represents a node in the priority queue for Dijkstra.
type item struct {
	vertex   int
	distance int
	index    int
}

type priorityQueue []*item

func (pq priorityQueue) Len() int { return len(pq) }
func (pq priorityQueue) Less(i, j int) bool {
	return pq[i].distance < pq[j].distance
}
func (pq priorityQueue) Swap(i, j int) {
	pq[i], pq[j] = pq[j], pq[i]
	pq[i].index = i
	pq[j].index = j
}
func (pq *priorityQueue) Push(x interface{}) {
	n := len(*pq)
	it := x.(*item)
	it.index = n
	*pq = append(*pq, it)
}
func (pq *priorityQueue) Pop() interface{} {
	old := *pq
	n := len(old)
	it := old[n-1]
	it.index = -1
	*pq = old[:n-1]
	return it
}

// Dijkstra returns the shortest distances from start to all vertices.
// adj is a map from vertex to (neighbor, weight) pairs.
// Returns a map of vertex -> shortest distance.
func Dijkstra(adj map[int][][2]int, start int) map[int]int {
	dist := make(map[int]int)
	for v := range adj {
		dist[v] = math.MaxInt32
	}
	dist[start] = 0
	pq := make(priorityQueue, 0)
	heap.Init(&pq)
	heap.Push(&pq, &item{vertex: start, distance: 0})

	for pq.Len() > 0 {
		curr := heap.Pop(&pq).(*item)
		if curr.distance > dist[curr.vertex] {
			continue
		}
		for _, edge := range adj[curr.vertex] {
			neighbor, weight := edge[0], edge[1]
			newDist := curr.distance + weight
			if newDist < dist[neighbor] {
				dist[neighbor] = newDist
				heap.Push(&pq, &item{vertex: neighbor, distance: newDist})
			}
		}
	}
	return dist
}
