/**
 * 树状数组（Binary Indexed Tree / Fenwick Tree）
 * 支持单点更新与前缀和查询
 * 时间复杂度: O(log n)
 */
public class FenwickTree {
    private final long[] tree;

    public FenwickTree(int n) {
        this.tree = new long[n + 1];
    }

    /**
     * 在索引 idx 处增加 delta（0-based）
     */
    public void add(int idx, long delta) {
        int i = idx + 1;
        while (i < tree.length) {
            tree[i] += delta;
            i += i & -i;
        }
    }

    /**
     * 查询 [0, idx] 的前缀和（0-based）
     */
    public long prefixSum(int idx) {
        long res = 0;
        int i = idx + 1;
        while (i > 0) {
            res += tree[i];
            i -= i & -i;
        }
        return res;
    }

    /**
     * 查询 [l, r] 的区间和（0-based）
     */
    public long rangeSum(int l, int r) {
        return prefixSum(r) - (l > 0 ? prefixSum(l - 1) : 0);
    }
}
