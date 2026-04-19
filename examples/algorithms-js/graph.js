/**
 * graph.js - JavaScript图算法实现
 * 包含：BFS、DFS、最短路径判断
 */

class Graph {
    /**
     * BFS遍历
     * @param {Map<number, number[]>} adj - 邻接表
     * @param {number} start - 起始顶点
     * @returns {number[]} BFS顺序
     */
    static bfs(adj, start) {
        if (!adj.has(start)) return [];
        const visited = new Set();
        const queue = [start];
        const order = [];
        visited.add(start);
        while (queue.length > 0) {
            const v = queue.shift();
            order.push(v);
            for (const neighbor of (adj.get(v) || [])) {
                if (!visited.has(neighbor)) {
                    visited.add(neighbor);
                    queue.push(neighbor);
                }
            }
        }
        return order;
    }

    /**
     * DFS遍历
     */
    static dfs(adj, start) {
        if (!adj.has(start)) return [];
        const visited = new Set();
        const stack = [start];
        const order = [];
        visited.add(start);
        while (stack.length > 0) {
            const v = stack.pop();
            order.push(v);
            const neighbors = adj.get(v) || [];
            for (let i = neighbors.length - 1; i >= 0; i--) {
                const neighbor = neighbors[i];
                if (!visited.has(neighbor)) {
                    visited.add(neighbor);
                    stack.push(neighbor);
                }
            }
        }
        return order;
    }

    /**
     * 判断是否存在路径
     */
    static hasPath(adj, start, goal) {
        if (start === goal) return true;
        if (!adj.has(start)) return false;
        const visited = new Set();
        const stack = [start];
        visited.add(start);
        while (stack.length > 0) {
            const v = stack.pop();
            for (const neighbor of (adj.get(v) || [])) {
                if (neighbor === goal) return true;
                if (!visited.has(neighbor)) {
                    visited.add(neighbor);
                    stack.push(neighbor);
                }
            }
        }
        return false;
    }
}

// 简单测试
function assertEq(name, expected, actual) {
    const e = JSON.stringify(expected);
    const a = JSON.stringify(actual);
    if (e !== a) throw new Error(`FAIL ${name}: expected ${e}, got ${a}`);
}

function runTests() {
    const adj = new Map([
        [0, [1, 2]],
        [1, [2]],
        [2, [3]],
        [3, []]
    ]);
    assertEq("BFS", [0, 1, 2, 3], Graph.bfs(adj, 0));
    assertEq("DFS size", 4, Graph.dfs(adj, 0).length);
    assertEq("HasPath", true, Graph.hasPath(adj, 0, 3));
    assertEq("NoPath", false, Graph.hasPath(adj, 2, 0));
    console.log("All graph tests passed!");
}

runTests();

module.exports = { Graph };
