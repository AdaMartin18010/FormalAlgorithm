/**
 * tree.cpp - C++树算法实现
 * 包含: LCA(倍增法)、笛卡尔树
 */

#include <vector>
#include <algorithm>
#include <cmath>

namespace tree {

/**
 * LCA - 倍增法
 * 预处理 O(n log n), 查询 O(log n)
 */
class LCA {
    int n, logN;
    std::vector<std::vector<int>> up;
    std::vector<int> depth;

    void dfs(const std::vector<std::vector<int>>& adj, int u, int p) {
        up[u][0] = p;
        for (int j = 1; j < logN; j++) {
            if (up[u][j - 1] != -1) up[u][j] = up[up[u][j - 1]][j - 1];
        }
        for (int v : adj[u]) {
            if (v != p) {
                depth[v] = depth[u] + 1;
                dfs(adj, v, u);
            }
        }
    }

public:
    LCA(const std::vector<std::vector<int>>& adj, int root = 0) {
        n = adj.size();
        logN = 32 - __builtin_clz(n);
        up.assign(n, std::vector<int>(logN, -1));
        depth.assign(n, 0);
        dfs(adj, root, -1);
    }

    int query(int u, int v) {
        if (depth[u] < depth[v]) std::swap(u, v);
        int diff = depth[u] - depth[v];
        for (int j = logN - 1; j >= 0; j--) {
            if ((diff >> j) & 1) u = up[u][j];
        }
        if (u == v) return u;
        for (int j = logN - 1; j >= 0; j--) {
            if (up[u][j] != up[v][j]) {
                u = up[u][j];
                v = up[v][j];
            }
        }
        return up[u][0];
    }
};

/**
 * 笛卡尔树 (小根堆)
 * 时间复杂度: O(n)
 */
struct CartesianTree {
    std::vector<int> parent;
    int root;

    CartesianTree(const std::vector<int>& arr) {
        int n = arr.size();
        parent.assign(n, -1);
        std::vector<int> stack(n);
        int top = -1;
        int last = -1;
        for (int i = 0; i < n; i++) {
            last = -1;
            while (top >= 0 && arr[stack[top]] > arr[i]) {
                last = stack[top--];
            }
            if (top >= 0) parent[i] = stack[top];
            if (last != -1) parent[last] = i;
            stack[++top] = i;
        }
        root = -1;
        for (int i = 0; i < n; i++) if (parent[i] == -1) { root = i; break; }
    }
};

} // namespace tree
