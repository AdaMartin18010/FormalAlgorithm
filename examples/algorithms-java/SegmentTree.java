/**
 * 线段树（区间求和版）
 * 支持区间查询与单点更新
 * 时间复杂度: O(log n)
 */
public class SegmentTree {
    private final long[] tree;
    private final int n;

    public SegmentTree(long[] arr) {
        this.n = arr.length;
        this.tree = new long[4 * n];
        build(0, 0, n - 1, arr);
    }

    private void build(int node, int l, int r, long[] arr) {
        if (l == r) {
            tree[node] = arr[l];
            return;
        }
        int mid = (l + r) >>> 1;
        build(2 * node + 1, l, mid, arr);
        build(2 * node + 2, mid + 1, r, arr);
        tree[node] = tree[2 * node + 1] + tree[2 * node + 2];
    }

    /**
     * 查询 [ql, qr] 区间和（0-based，闭区间）
     */
    public long query(int ql, int qr) {
        return query(0, 0, n - 1, ql, qr);
    }

    private long query(int node, int l, int r, int ql, int qr) {
        if (ql <= l && r <= qr) return tree[node];
        if (r < ql || l > qr) return 0;
        int mid = (l + r) >>> 1;
        return query(2 * node + 1, l, mid, ql, qr)
             + query(2 * node + 2, mid + 1, r, ql, qr);
    }

    /**
     * 将索引 idx 更新为 val
     */
    public void update(int idx, long val) {
        update(0, 0, n - 1, idx, val);
    }

    private void update(int node, int l, int r, int idx, long val) {
        if (l == r) {
            tree[node] = val;
            return;
        }
        int mid = (l + r) >>> 1;
        if (idx <= mid) update(2 * node + 1, l, mid, idx, val);
        else update(2 * node + 2, mid + 1, r, idx, val);
        tree[node] = tree[2 * node + 1] + tree[2 * node + 2];
    }
}
