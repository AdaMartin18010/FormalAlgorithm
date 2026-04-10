// graph.go - 图算法实现
// 包含图的基本操作、BFS、DFS、Dijkstra算法

package main

import (
	"container/heap"
	"fmt"
)

// ==================== 数据结构定义 ====================

// Graph 表示一个无向/有向图，使用邻接表存储
type Graph struct {
	vertices int           // 顶点数量
	adjList  map[int][]int // 邻接表（无权图）
	weighted map[int]map[int]int // 带权邻接表
	directed bool          // 是否是有向图
}

// NewGraph 创建一个新的图
func NewGraph(vertices int, directed bool) *Graph {
	return &Graph{
		vertices: vertices,
		adjList:  make(map[int][]int),
		weighted: make(map[int]map[int]int),
		directed: directed,
	}
}

// AddEdge 添加无权重边
func (g *Graph) AddEdge(u, v int) {
	g.adjList[u] = append(g.adjList[u], v)
	if !g.directed {
		g.adjList[v] = append(g.adjList[v], u)
	}
}

// AddWeightedEdge 添加带权重边
func (g *Graph) AddWeightedEdge(u, v, weight int) {
	if g.weighted[u] == nil {
		g.weighted[u] = make(map[int]int)
	}
	g.weighted[u][v] = weight
	
	if !g.directed {
		if g.weighted[v] == nil {
			g.weighted[v] = make(map[int]int)
		}
		g.weighted[v][u] = weight
	}
}

// ==================== BFS 广度优先搜索 ====================

// BFS 广度优先搜索，返回遍历顺序
func (g *Graph) BFS(start int) []int {
	visited := make([]bool, g.vertices)
	queue := []int{start}
	result := []int{}
	
	visited[start] = true
	
	for len(queue) > 0 {
		// 出队
		u := queue[0]
		queue = queue[1:]
		result = append(result, u)
		
		// 访问所有邻接顶点
		for _, v := range g.adjList[u] {
			if !visited[v] {
				visited[v] = true
				queue = append(queue, v)
			}
		}
	}
	
	return result
}

// BFSPath BFS寻找最短路径（无权图）
func (g *Graph) BFSPath(start, end int) ([]int, int) {
	if start == end {
		return []int{start}, 0
	}
	
	visited := make([]bool, g.vertices)
	parent := make([]int, g.vertices)
	for i := range parent {
		parent[i] = -1
	}
	
	queue := []int{start}
	visited[start] = true
	
	for len(queue) > 0 {
		u := queue[0]
		queue = queue[1:]
		
		for _, v := range g.adjList[u] {
			if !visited[v] {
				visited[v] = true
				parent[v] = u
				
				if v == end {
					// 重建路径
					path := []int{}
					curr := end
					for curr != -1 {
						path = append([]int{curr}, path...)
						curr = parent[curr]
					}
					return path, len(path) - 1
				}
				
				queue = append(queue, v)
			}
		}
	}
	
	return nil, -1 // 无路径
}

// ==================== DFS 深度优先搜索 ====================

// DFS 深度优先搜索（递归实现）
func (g *Graph) DFS(start int) []int {
	visited := make([]bool, g.vertices)
	result := []int{}
	
	var dfsHelper func(int)
	dfsHelper = func(u int) {
		visited[u] = true
		result = append(result, u)
		
		for _, v := range g.adjList[u] {
			if !visited[v] {
				dfsHelper(v)
			}
		}
	}
	
	dfsHelper(start)
	return result
}

// DFSIterative 深度优先搜索（迭代实现）
func (g *Graph) DFSIterative(start int) []int {
	visited := make([]bool, g.vertices)
	stack := []int{start}
	result := []int{}
	
	for len(stack) > 0 {
		// 出栈
		u := stack[len(stack)-1]
		stack = stack[:len(stack)-1]
		
		if !visited[u] {
			visited[u] = true
			result = append(result, u)
			
			// 将邻接顶点入栈（逆序以保证顺序）
			neighbors := g.adjList[u]
			for i := len(neighbors) - 1; i >= 0; i-- {
				if !visited[neighbors[i]] {
					stack = append(stack, neighbors[i])
				}
			}
		}
	}
	
	return result
}

// HasCycle 检测图中是否有环（DFS方式）
func (g *Graph) HasCycle() bool {
	visited := make([]bool, g.vertices)
	recStack := make([]bool, g.vertices)
	
	var hasCycleHelper func(int, int) bool
	hasCycleHelper = func(u int, parent int) bool {
		visited[u] = true
		recStack[u] = true
		
		for _, v := range g.adjList[u] {
			if !visited[v] {
				if hasCycleHelper(v, u) {
					return true
				}
			} else if recStack[v] && v != parent {
				// 发现回边（指向祖先节点）
				return true
			}
		}
		
		recStack[u] = false
		return false
	}
	
	for i := 0; i < g.vertices; i++ {
		if !visited[i] {
			if hasCycleHelper(i, -1) {
				return true
			}
		}
	}
	
	return false
}

// ==================== Dijkstra 最短路径算法 ====================

// Item 优先队列中的元素
type Item struct {
	vertex   int
	distance int
	index    int // 用于heap接口
}

// PriorityQueue 优先队列（最小堆）
type PriorityQueue []*Item

func (pq PriorityQueue) Len() int { return len(pq) }

func (pq PriorityQueue) Less(i, j int) bool {
	return pq[i].distance < pq[j].distance
}

func (pq PriorityQueue) Swap(i, j int) {
	pq[i], pq[j] = pq[j], pq[i]
	pq[i].index = i
	pq[j].index = j
}

func (pq *PriorityQueue) Push(x interface{}) {
	n := len(*pq)
	item := x.(*Item)
	item.index = n
	*pq = append(*pq, item)
}

func (pq *PriorityQueue) Pop() interface{} {
	old := *pq
	n := len(old)
	item := old[n-1]
	old[n-1] = nil
	item.index = -1
	*pq = old[:n-1]
	return item
}

// Dijkstra Dijkstra最短路径算法
// 返回从起点到所有顶点的最短距离和最短路径
func (g *Graph) Dijkstra(start int) ([]int, []int) {
	dist := make([]int, g.vertices)
	parent := make([]int, g.vertices)
	visited := make([]bool, g.vertices)
	
	// 初始化
	for i := 0; i < g.vertices; i++ {
		dist[i] = int(^uint(0) >> 1) // MaxInt
		parent[i] = -1
	}
	dist[start] = 0
	
	// 优先队列
	pq := &PriorityQueue{}
	heap.Init(pq)
	heap.Push(pq, &Item{vertex: start, distance: 0})
	
	for pq.Len() > 0 {
		item := heap.Pop(pq).(*Item)
		u := item.vertex
		
		if visited[u] {
			continue
		}
		visited[u] = true
		
		// 遍历邻接顶点
		for v, weight := range g.weighted[u] {
			if !visited[v] && dist[u]+weight < dist[v] {
				dist[v] = dist[u] + weight
				parent[v] = u
				heap.Push(pq, &Item{vertex: v, distance: dist[v]})
			}
		}
	}
	
	return dist, parent
}

// GetPath 根据parent数组重建路径
func GetPath(parent []int, start, end int) []int {
	if parent[end] == -1 && start != end {
		return nil // 不可达
	}
	
	path := []int{}
	curr := end
	for curr != -1 {
		path = append([]int{curr}, path...)
		curr = parent[curr]
	}
	return path
}

// ==================== 测试示例 ====================

func main() {
	fmt.Println("=================== 图算法测试 ===================")
	
	// 测试1: BFS和DFS
	fmt.Println("\n1. BFS和DFS测试（无权无向图）:")
	g1 := NewGraph(6, false)
	g1.AddEdge(0, 1)
	g1.AddEdge(0, 2)
	g1.AddEdge(1, 3)
	g1.AddEdge(1, 4)
	g1.AddEdge(2, 4)
	g1.AddEdge(3, 5)
	g1.AddEdge(4, 5)
	
	fmt.Printf("图的邻接表: %v\n", g1.adjList)
	fmt.Printf("从顶点0的BFS遍历: %v\n", g1.BFS(0))
	fmt.Printf("从顶点0的DFS遍历(递归): %v\n", g1.DFS(0))
	fmt.Printf("从顶点0的DFS遍历(迭代): %v\n", g1.DFSIterative(0))
	
	// 测试2: BFS最短路径
	fmt.Println("\n2. BFS最短路径测试:")
	path, dist := g1.BFSPath(0, 5)
	fmt.Printf("从0到5的最短路径: %v, 距离: %d\n", path, dist)
	
	// 测试3: 环检测
	fmt.Println("\n3. 环检测测试:")
	g2 := NewGraph(4, false)
	g2.AddEdge(0, 1)
	g2.AddEdge(1, 2)
	g2.AddEdge(2, 3)
	fmt.Printf("无环图是否有环: %v\n", g2.HasCycle())
	g2.AddEdge(2, 0) // 添加一条边形成环
	fmt.Printf("添加边后是否有环: %v\n", g2.HasCycle())
	
	// 测试4: Dijkstra算法
	fmt.Println("\n4. Dijkstra最短路径测试:")
	g3 := NewGraph(6, false)
	g3.AddWeightedEdge(0, 1, 4)
	g3.AddWeightedEdge(0, 2, 2)
	g3.AddWeightedEdge(1, 2, 1)
	g3.AddWeightedEdge(1, 3, 5)
	g3.AddWeightedEdge(2, 3, 8)
	g3.AddWeightedEdge(2, 4, 10)
	g3.AddWeightedEdge(3, 4, 2)
	g3.AddWeightedEdge(3, 5, 6)
	g3.AddWeightedEdge(4, 5, 3)
	
	distances, parents := g3.Dijkstra(0)
	fmt.Printf("从顶点0到各顶点的最短距离: %v\n", distances)
	
	fmt.Println("\n各顶点的最短路径:")
	for i := 0; i < g3.vertices; i++ {
		path := GetPath(parents, 0, i)
		fmt.Printf("  到顶点%d: %v, 距离: %d\n", i, path, distances[i])
	}
	
	fmt.Println("\n=================== 测试完成 ===================")
}
