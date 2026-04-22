"use strict";
/**
 * 树算法集合
 * 包含 LCA、树链剖分、重心分解、笛卡尔树
 */
Object.defineProperty(exports, "__esModule", { value: true });
exports.HeavyLightDecomposition = exports.LCA = void 0;
exports.centroidDecomposition = centroidDecomposition;
exports.cartesianTree = cartesianTree;
exports.runTreeTests = runTreeTests;
const utils_1 = require("./utils");
// ==================== LCA (倍增法) ====================
class LCA {
    constructor(adj, root = 0) {
        this.adj = adj;
        this.n = adj.length;
        this.log = Math.floor(Math.log2(this.n)) + 1;
        this.up = Array.from({ length: this.n }, () => new Array(this.log).fill(-1));
        this.depth = new Array(this.n).fill(0);
        this.dfs(root, -1);
    }
    dfs(u, p) {
        this.up[u][0] = p;
        for (let j = 1; j < this.log; j++) {
            if (this.up[u][j - 1] !== -1) {
                this.up[u][j] = this.up[this.up[u][j - 1]][j - 1];
            }
        }
        for (const v of this.adj[u]) {
            if (v !== p) {
                this.depth[v] = this.depth[u] + 1;
                this.dfs(v, u);
            }
        }
    }
    /** O(log n) */
    query(u, v) {
        if (this.depth[u] < this.depth[v])
            [u, v] = [v, u];
        const diff = this.depth[u] - this.depth[v];
        for (let j = this.log - 1; j >= 0; j--) {
            if ((diff >> j) & 1)
                u = this.up[u][j];
        }
        if (u === v)
            return u;
        for (let j = this.log - 1; j >= 0; j--) {
            if (this.up[u][j] !== this.up[v][j]) {
                u = this.up[u][j];
                v = this.up[v][j];
            }
        }
        return this.up[u][0];
    }
}
exports.LCA = LCA;
// ==================== 树链剖分 (HLD) ====================
class HeavyLightDecomposition {
    constructor(adj, root = 0) {
        this.curPos = 0;
        this.adj = adj;
        const n = adj.length;
        this.parent = new Array(n).fill(-1);
        this.depth = new Array(n).fill(0);
        this.heavy = new Array(n).fill(-1);
        this.head = new Array(n).fill(0);
        this.pos = new Array(n).fill(0);
        this.dfs(root);
        this.decompose(root, root);
    }
    dfs(u) {
        let size = 1;
        let maxSub = 0;
        for (const v of this.adj[u]) {
            if (v !== this.parent[u]) {
                this.parent[v] = u;
                this.depth[v] = this.depth[u] + 1;
                const sub = this.dfs(v);
                if (sub > maxSub) {
                    maxSub = sub;
                    this.heavy[u] = v;
                }
                size += sub;
            }
        }
        return size;
    }
    decompose(u, h) {
        this.head[u] = h;
        this.pos[u] = this.curPos++;
        if (this.heavy[u] !== -1) {
            this.decompose(this.heavy[u], h);
        }
        for (const v of this.adj[u]) {
            if (v !== this.parent[u] && v !== this.heavy[u]) {
                this.decompose(v, v);
            }
        }
    }
    getPosition(u) { return this.pos[u]; }
    getHead(u) { return this.head[u]; }
    getDepth(u) { return this.depth[u]; }
}
exports.HeavyLightDecomposition = HeavyLightDecomposition;
// ==================== 重心分解 ====================
function centroidDecomposition(adj) {
    const n = adj.length;
    const removed = new Array(n).fill(false);
    const subtrees = [];
    function calcSizes(u, p, sizes) {
        sizes[u] = 1;
        for (const v of adj[u]) {
            if (v !== p && !removed[v]) {
                calcSizes(v, u, sizes);
                sizes[u] += sizes[v];
            }
        }
    }
    function findCentroid(u, p, total, sizes) {
        for (const v of adj[u]) {
            if (v !== p && !removed[v] && sizes[v] > total / 2) {
                return findCentroid(v, u, total, sizes);
            }
        }
        return u;
    }
    function decompose(u) {
        const sizes = new Array(n).fill(0);
        calcSizes(u, -1, sizes);
        const c = findCentroid(u, -1, sizes[u], sizes);
        removed[c] = true;
        subtrees.push(c);
        for (const v of adj[c]) {
            if (!removed[v])
                decompose(v);
        }
    }
    decompose(0);
    return subtrees;
}
// ==================== 笛卡尔树 ====================
/**
 * 构建小根笛卡尔树（堆性质 + 中序遍历为原序列）
 * 时间复杂度: O(n)
 */
function cartesianTree(arr) {
    const n = arr.length;
    const parent = new Array(n).fill(-1);
    const stack = [];
    let last = -1;
    for (let i = 0; i < n; i++) {
        last = -1;
        while (stack.length > 0 && arr[stack[stack.length - 1]] > arr[i]) {
            last = stack.pop();
        }
        if (stack.length > 0) {
            parent[i] = stack[stack.length - 1];
        }
        if (last !== -1) {
            parent[last] = i;
        }
        stack.push(i);
    }
    let root = -1;
    for (let i = 0; i < n; i++) {
        if (parent[i] === -1) {
            root = i;
            break;
        }
    }
    return { parent, root };
}
function runTreeTests() {
    (0, utils_1.runTests)("Tree", {
        "LCA": () => {
            const adj = [[1, 2], [3, 4], [5], [], [], []];
            const lca = new LCA(adj, 0);
            (0, utils_1.assertEq)(lca.query(3, 4), 1);
            (0, utils_1.assertEq)(lca.query(3, 5), 0);
            (0, utils_1.assertEq)(lca.query(1, 2), 0);
        },
        "HeavyLightDecomposition": () => {
            const adj = [[1, 2], [3], [], []];
            const hld = new HeavyLightDecomposition(adj, 0);
            (0, utils_1.assertEq)(hld.getHead(3), 0); // 0-1-3 is one heavy path
            (0, utils_1.assertTrue)(hld.getPosition(0) < hld.getPosition(1));
        },
        "centroidDecomposition": () => {
            const adj = [[1, 2], [3, 4], [], [], []];
            const centroids = centroidDecomposition(adj);
            (0, utils_1.assertTrue)(centroids.length > 0);
        },
        "cartesianTree": () => {
            const arr = [3, 2, 6, 1, 0, 8, 7];
            const { parent, root } = cartesianTree(arr);
            (0, utils_1.assertEq)(root, 4); // 最小值 0 在索引 4
            (0, utils_1.assertEq)(parent[4], -1);
        },
    });
}
//# sourceMappingURL=tree.js.map