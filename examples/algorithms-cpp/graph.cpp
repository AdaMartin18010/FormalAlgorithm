/**
 * graph.cpp - C++图算法实现
 * 包含：Dijkstra、BFS、DFS、Floyd-Warshall、拓扑排序
 */

#include <iostream>
#include <vector>
#include <queue>
#include <stack>
#include <algorithm>
#include <climits>
#include <functional>

namespace graph {

using namespace std;

const int INF = INT_MAX / 2;

/**
 * Dijkstra最短路径算法
 * 使用优先队列优化，时间复杂度: O((V+E) log V)
 */
vector<int> dijkstra(const vector<vector<pair<int, int>>>& adj, int source) {
    int n = adj.size();
    vector<int> dist(n, INF);
    dist[source] = 0;
    
    // (距离, 顶点)
    priority_queue<pair<int, int>, vector<pair<int, int>>, greater<pair<int, int>>> pq;
    pq.push({0, source});
    
    while (!pq.empty()) {
        auto [d, u] = pq.top();
        pq.pop();
        
        if (d > dist[u]) continue;
        
        for (auto [v, w] : adj[u]) {
            if (dist[u] + w < dist[v]) {
                dist[v] = dist[u] + w;
                pq.push({dist[v], v});
            }
        }
    }
    
    return dist;
}

/**
 * Dijkstra算法（返回路径）
 */
pair<vector<int>, vector<int>> dijkstraWithPath(
    const vector<vector<pair<int, int>>>& adj, int source) {
    int n = adj.size();
    vector<int> dist(n, INF);
    vector<int> parent(n, -1);
    dist[source] = 0;
    
    priority_queue<pair<int, int>, vector<pair<int, int>>, greater<pair<int, int>>> pq;
    pq.push({0, source});
    
    while (!pq.empty()) {
        auto [d, u] = pq.top();
        pq.pop();
        
        if (d > dist[u]) continue;
        
        for (auto [v, w] : adj[u]) {
            if (dist[u] + w < dist[v]) {
                dist[v] = dist[u] + w;
                parent[v] = u;
                pq.push({dist[v], v});
            }
        }
    }
    
    return {dist, parent};
}

/**
 * 重建路径
 */
vector<int> getPath(int source, int target, const vector<int>& parent) {
    vector<int> path;
    int current = target;
    
    while (current != -1) {
        path.push_back(current);
        if (current == source) break;
        current = parent[current];
    }
    
    reverse(path.begin(), path.end());
    return path;
}

/**
 * BFS广度优先搜索
 * 时间复杂度: O(V + E)
 */
vector<int> bfs(const vector<vector<int>>& adj, int start) {
    int n = adj.size();
    vector<bool> visited(n, false);
    vector<int> result;
    queue<int> q;
    
    visited[start] = true;
    q.push(start);
    
    while (!q.empty()) {
        int u = q.front();
        q.pop();
        result.push_back(u);
        
        for (int v : adj[u]) {
            if (!visited[v]) {
                visited[v] = true;
                q.push(v);
            }
        }
    }
    
    return result;
}

/**
 * BFS求无权图最短路径
 */
vector<int> bfsShortestPath(const vector<vector<int>>& adj, int start, int target) {
    int n = adj.size();
    vector<bool> visited(n, false);
    vector<int> parent(n, -1);
    queue<int> q;
    
    visited[start] = true;
    q.push(start);
    
    while (!q.empty()) {
        int u = q.front();
        q.pop();
        
        if (u == target) break;
        
        for (int v : adj[u]) {
            if (!visited[v]) {
                visited[v] = true;
                parent[v] = u;
                q.push(v);
            }
        }
    }
    
    return getPath(start, target, parent);
}

/**
 * DFS深度优先搜索 - 递归
 */
void dfsRecursive(const vector<vector<int>>& adj, int u, 
                  vector<bool>& visited, vector<int>& result) {
    visited[u] = true;
    result.push_back(u);
    
    for (int v : adj[u]) {
        if (!visited[v]) {
            dfsRecursive(adj, v, visited, result);
        }
    }
}

vector<int> dfs(const vector<vector<int>>& adj, int start) {
    int n = adj.size();
    vector<bool> visited(n, false);
    vector<int> result;
    dfsRecursive(adj, start, visited, result);
    return result;
}

/**
 * DFS深度优先搜索 - 迭代
 */
vector<int> dfsIterative(const vector<vector<int>>& adj, int start) {
    int n = adj.size();
    vector<bool> visited(n, false);
    vector<int> result;
    stack<int> stk;
    
    stk.push(start);
    
    while (!stk.empty()) {
        int u = stk.top();
        stk.pop();
        
        if (!visited[u]) {
            visited[u] = true;
            result.push_back(u);
            
            // 逆序入栈以保证正确遍历顺序
            for (auto it = adj[u].rbegin(); it != adj[u].rend(); ++it) {
                if (!visited[*it]) {
                    stk.push(*it);
                }
            }
        }
    }
    
    return result;
}

/**
 * Floyd-Warshall全源最短路径
 * 时间复杂度: O(V³)
 */
vector<vector<int>> floydWarshall(const vector<vector<int>>& graph) {
    int n = graph.size();
    vector<vector<int>> dist = graph;
    
    for (int k = 0; k < n; k++) {
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < n; j++) {
                if (dist[i][k] != INF && dist[k][j] != INF) {
                    dist[i][j] = min(dist[i][j], dist[i][k] + dist[k][j]);
                }
            }
        }
    }
    
    return dist;
}

/**
 * 拓扑排序 - Kahn算法（BFS）
 */
vector<int> topologicalSortKahn(const vector<vector<int>>& adj) {
    int n = adj.size();
    vector<int> inDegree(n, 0);
    
    for (int u = 0; u < n; u++) {
        for (int v : adj[u]) {
            inDegree[v]++;
        }
    }
    
    queue<int> q;
    for (int i = 0; i < n; i++) {
        if (inDegree[i] == 0) {
            q.push(i);
        }
    }
    
    vector<int> result;
    while (!q.empty()) {
        int u = q.front();
        q.pop();
        result.push_back(u);
        
        for (int v : adj[u]) {
            inDegree[v]--;
            if (inDegree[v] == 0) {
                q.push(v);
            }
        }
    }
    
    // 如果存在环，返回空数组
    if (result.size() != n) {
        return {};
    }
    return result;
}

/**
 * 检测图中是否有环（DFS）
 */
bool hasCycleDFS(int u, const vector<vector<int>>& adj, 
                 vector<bool>& visited, vector<bool>& recStack) {
    visited[u] = true;
    recStack[u] = true;
    
    for (int v : adj[u]) {
        if (!visited[v]) {
            if (hasCycleDFS(v, adj, visited, recStack)) {
                return true;
            }
        } else if (recStack[v]) {
            return true;
        }
    }
    
    recStack[u] = false;
    return false;
}

bool hasCycle(const vector<vector<int>>& adj) {
    int n = adj.size();
    vector<bool> visited(n, false);
    vector<bool> recStack(n, false);
    
    for (int i = 0; i < n; i++) {
        if (!visited[i]) {
            if (hasCycleDFS(i, adj, visited, recStack)) {
                return true;
            }
        }
    }
    return false;
}

// 辅助函数：打印数组
void printArray(const vector<int>& arr, const string& label = "") {
    if (!label.empty()) cout << label << ": ";
    for (int x : arr) cout << x << " ";
    cout << endl;
}

} // namespace graph

int main() {
    using namespace graph;
    
    cout << "=== 图算法演示 ===" << endl;
    
    // Dijkstra测试
    cout << "\n--- Dijkstra算法 ---" << endl;
    vector<vector<pair<int, int>>> weightedGraph(6);
    weightedGraph[0] = {{1, 4}, {2, 2}};
    weightedGraph[1] = {{2, 1}, {3, 5}};
    weightedGraph[2] = {{3, 8}, {4, 10}};
    weightedGraph[3] = {{4, 2}, {5, 6}};
    weightedGraph[4] = {{5, 3}};
    
    auto [dist, parent] = dijkstraWithPath(weightedGraph, 0);
    cout << "从顶点0出发的最短距离:" << endl;
    for (int i = 0; i < 6; i++) {
        cout << "到顶点 " << i << ": " << dist[i] << endl;
    }
    cout << "路径 (0 -> 5): ";
    printArray(getPath(0, 5, parent));
    
    // BFS/DFS测试
    cout << "\n--- BFS/DFS遍历 ---" << endl;
    vector<vector<int>> unweightedGraph(6);
    unweightedGraph[0] = {1, 2};
    unweightedGraph[1] = {3, 4};
    unweightedGraph[2] = {4};
    unweightedGraph[3] = {5};
    unweightedGraph[4] = {5};
    
    printArray(bfs(unweightedGraph, 0), "BFS from 0");
    printArray(dfs(unweightedGraph, 0), "DFS from 0");
    printArray(dfsIterative(unweightedGraph, 0), "DFS Iterative from 0");
    printArray(bfsShortestPath(unweightedGraph, 0, 5), "BFS Shortest Path (0->5)");
    
    // 拓扑排序
    cout << "\n--- 拓扑排序 ---" << endl;
    vector<vector<int>> dag(6);
    dag[5] = {2, 0};
    dag[4] = {0, 1};
    dag[2] = {3};
    dag[3] = {1};
    
    printArray(topologicalSortKahn(dag), "Topological Sort");
    cout << "Has cycle: " << (hasCycle(dag) ? "Yes" : "No") << endl;
    
    // Floyd-Warshall测试
    cout << "\n--- Floyd-Warshall ---" << endl;
    vector<vector<int>> fwGraph = {
        {0, 3, INF, 7},
        {8, 0, 2, INF},
        {5, INF, 0, 1},
        {2, INF, INF, 0}
    };
    
    auto fwResult = floydWarshall(fwGraph);
    cout << "全源最短路径矩阵:" << endl;
    for (const auto& row : fwResult) {
        for (int x : row) {
            if (x == INF) cout << "INF ";
            else cout << x << " ";
        }
        cout << endl;
    }
    
    return 0;
}
