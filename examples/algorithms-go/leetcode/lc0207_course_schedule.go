// LeetCode 207. Course Schedule
// 链接: https://leetcode.com/problems/course-schedule/
// 难度: Medium
//
// 题目描述:
// 你这个学期必须选修 numCourses 门课程，记为 0 到 numCourses - 1 。
// 在选修某些课程之前需要一些先修课程。先修课程按数组 prerequisites 给出，
// 其中 prerequisites[i] = [a, b] ，表示如果要学习课程 a 则必须先学习课程 b 。
// 请你判断是否可能完成所有课程的学习。
//
// 形式化规约:
//   输入: 课程数 numCourses，先修关系 prerequisites = [(a, b)] 表示 b 是 a 的先修课
//   输出: 能否完成所有课程（即图是否为 DAG）
//
// 最优解思路:
//   拓扑排序 - Kahn 算法：计算每个节点的入度，将入度为 0 的节点入队，
//   依次移除并更新邻居入度。若最终处理节点数等于 numCourses，则无环。
//
// 复杂度:
//   时间: O(V + E)
//   空间: O(V + E)
//
// 正确性要点:
//   1. Kahn 算法的核心：入度为 0 的节点没有未完成的先修依赖
//   2. 若处理节点数 < numCourses，说明图中存在环
//   3. 也可用 DFS 染色法（0/1/2 标记）检测环

package leetcode

func canFinish(numCourses int, prerequisites [][]int) bool {
	// 建图 + 计算入度
	graph := make([][]int, numCourses)
	inDegree := make([]int, numCourses)
	for _, pre := range prerequisites {
		a, b := pre[0], pre[1]
		graph[b] = append(graph[b], a)
		inDegree[a]++
	}

	// Kahn 算法：入度为 0 的节点入队
	queue := make([]int, 0)
	for i := 0; i < numCourses; i++ {
		if inDegree[i] == 0 {
			queue = append(queue, i)
		}
	}

	visited := 0
	for front := 0; front < len(queue); front++ {
		curr := queue[front]
		visited++
		for _, neighbor := range graph[curr] {
			inDegree[neighbor]--
			if inDegree[neighbor] == 0 {
				queue = append(queue, neighbor)
			}
		}
	}

	return visited == numCourses
}

// TestCourseSchedule 测试课程表函数
func TestCourseSchedule() {
	// 示例 1: 可以完成
	if !canFinish(2, [][]int{{1, 0}}) {
		panic("Test 1 failed")
	}
	// 示例 2: 有环，无法完成
	if canFinish(2, [][]int{{1, 0}, {0, 1}}) {
		panic("Test 2 failed")
	}
	// 示例 3: 多课程无环
	if !canFinish(4, [][]int{{1, 0}, {2, 1}, {3, 2}}) {
		panic("Test 3 failed")
	}
	// 示例 4: 空先修关系
	if !canFinish(1, [][]int{}) {
		panic("Test 4 failed")
	}
}
