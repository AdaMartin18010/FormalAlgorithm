/**
 * fenwick_tree.cpp - C++树状数组实现
 * 支持单点更新与前缀和查询
 */

#include <vector>

namespace fenwick {

class FenwickTree {
    std::vector<long long> tree;
public:
    explicit FenwickTree(int n) : tree(n + 1, 0) {}

    void add(int idx, long long delta) {
        int i = idx + 1;
        while (i < (int)tree.size()) {
            tree[i] += delta;
            i += i & -i;
        }
    }

    long long prefixSum(int idx) const {
        long long res = 0;
        int i = idx + 1;
        while (i > 0) {
            res += tree[i];
            i -= i & -i;
        }
        return res;
    }

    long long rangeSum(int l, int r) const {
        return prefixSum(r) - (l > 0 ? prefixSum(l - 1) : 0);
    }
};

} // namespace fenwick
