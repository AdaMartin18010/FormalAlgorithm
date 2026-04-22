// LeetCode 743. Network Delay Time
// 链接: https://leetcode.com/problems/network-delay-time/
// 难度: Medium
//
// 题目描述:
// 有 n 个网络节点，标记为 1 到 n。给你一个列表 times，表示信号经过有向边的传递时间。
// 现在，从某个节点 K 发出一个信号。需要多久才能使所有节点都收到信号？如果不能使所有节点收到信号，返回 -1。
//
// 形式化规约:
//   输入: G = (V, E), |V| = n, w(u,v) > 0, 源点 k
//   输出: max_{v∈V} δ(k, v)，若存在不可达节点则返回 -1
//
// 最优解思路:
//   Dijkstra 贪心算法。维护已确定最短距离的集合，每次从优先队列中
//   取出当前距离估计最小的顶点，松弛其所有出边。
//
// 复杂度:
//   时间: O((V + E) log V)
//   空间: O(V + E)

package leetcode

import (
	"container/heap"
)

type IntHeap [][2]int // [][distance, node]

func (h IntHeap) Len() int           { return len(h) }
func (h IntHeap) Less(i, j int) bool { return h[i][0] < h[j][0] }
func (h IntHeap) Swap(i, j int)      { h[i], h[j] = h[j], h[i] }

func (h *IntHeap) Push(x interface{}) {
	*h = append(*h, x.([2]int))
}

func (h *IntHeap) Pop() interface{} {
	old := *h
	n := len(old)
	x := old[n-1]
	*h = old[0 : n-1]
	return x
}

func networkDelayTime(times [][]int, n int, k int) int {
	// 建图（邻接表），转为 0-based
	graph := make([][][2]int, n)
	for _, edge := range times {
		u, v, w := edge[0]-1, edge[1]-1, edge[2]
		graph[u] = append(graph[u], [2]int{v, w})
	}

	src := k - 1
	const INF = int(1e9)
	dist := make([]int, n)
	visited := make([]bool, n)
	for i := range dist {
		dist[i] = INF
	}
	dist[src] = 0

	h := &IntHeap{{0, src}}
	heap.Init(h)

	for h.Len() > 0 {
		item := heap.Pop(h).([2]int)
		_, u := item[0], item[1]
		if visited[u] {
			continue
		}
		visited[u] = true

		for _, neighbor := range graph[u] {
			v, w := neighbor[0], neighbor[1]
			if !visited[v] && dist[u]+w < dist[v] {
				dist[v] = dist[u] + w
				heap.Push(h, [2]int{dist[v], v})
			}
		}
	}

	maxDist := 0
	for i := 0; i < n; i++ {
		if dist[i] == INF {
			return -1
		}
		if dist[i] > maxDist {
			maxDist = dist[i]
		}
	}
	return maxDist
}

// TestNetworkDelayTime 测试网络延迟时间函数
func TestNetworkDelayTime() {
	// 示例 1
	times1 := [][]int{{2, 1, 1}, {2, 3, 1}, {3, 4, 1}}
	if networkDelayTime(times1, 4, 2) != 2 {
		panic("Test 1 failed")
	}

	// 示例 2
	times2 := [][]int{{1, 2, 1}}
	if networkDelayTime(times2, 2, 1) != 1 {
		panic("Test 2 failed")
	}

	// 不可达
	times3 := [][]int{{1, 2, 1}}
	if networkDelayTime(times3, 2, 2) != -1 {
		panic("Test 3 failed")
	}

	// 单节点
	if networkDelayTime([][]int{}, 1, 1) != 0 {
		panic("Test 4 failed")
	}
}
