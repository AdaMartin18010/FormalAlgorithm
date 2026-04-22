/**
 * 树算法实现
 * 包含: LCA(倍增法)、笛卡尔树
 */
public class TreeAlgorithms {

    /**
     * LCA - 倍增法
     * 预处理 O(n log n), 查询 O(log n)
     */
    public static class LCA {
        private final int n;
        private final int log;
        private final int[][] up;
        private final int[] depth;

        public LCA(int[][] adj, int root) {
            this.n = adj.length;
            this.log = 32 - Integer.numberOfLeadingZeros(n);
            this.up = new int[n][log];
            this.depth = new int[n];
            for (int i = 0; i < n; i++) java.util.Arrays.fill(up[i], -1);
            dfs(adj, root, -1);
        }

        private void dfs(int[][] adj, int u, int p) {
            up[u][0] = p;
            for (int j = 1; j < log; j++) {
                if (up[u][j - 1] != -1) up[u][j] = up[up[u][j - 1]][j - 1];
            }
            for (int v : adj[u]) {
                if (v != p) {
                    depth[v] = depth[u] + 1;
                    dfs(adj, v, u);
                }
            }
        }

        public int query(int u, int v) {
            if (depth[u] < depth[v]) { int t = u; u = v; v = t; }
            int diff = depth[u] - depth[v];
            for (int j = log - 1; j >= 0; j--) {
                if ((diff >> j & 1) == 1) u = up[u][j];
            }
            if (u == v) return u;
            for (int j = log - 1; j >= 0; j--) {
                if (up[u][j] != up[v][j]) {
                    u = up[u][j];
                    v = up[v][j];
                }
            }
            return up[u][0];
        }
    }

    /**
     * 笛卡尔树 (小根堆)
     * 时间复杂度: O(n)
     */
    public static class CartesianTree {
        public final int[] parent;
        public final int root;

        public CartesianTree(int[] arr) {
            int n = arr.length;
            parent = new int[n];
            java.util.Arrays.fill(parent, -1);
            int[] stack = new int[n];
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
            int r = -1;
            for (int i = 0; i < n; i++) if (parent[i] == -1) { r = i; break; }
            this.root = r;
        }
    }
}
