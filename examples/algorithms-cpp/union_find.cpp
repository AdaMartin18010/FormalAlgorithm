/**
 * union_find.cpp - C++并查集实现
 * 支持：路径压缩、按秩合并
 */

#include <iostream>
#include <vector>
#include <cassert>

namespace union_find {

class UnionFind {
public:
    explicit UnionFind(int n) : parent(n), rank_(n, 0), count_(n) {
        for (int i = 0; i < n; ++i) parent[i] = i;
    }

    int find(int x) {
        if (parent[x] != x) parent[x] = find(parent[x]);
        return parent[x];
    }

    void unite(int x, int y) {
        int rx = find(x), ry = find(y);
        if (rx == ry) return;
        if (rank_[rx] < rank_[ry]) std::swap(rx, ry);
        parent[ry] = rx;
        if (rank_[rx] == rank_[ry]) ++rank_[rx];
        --count_;
    }

    bool connected(int x, int y) {
        return find(x) == find(y);
    }

    int count() const { return count_; }

private:
    std::vector<int> parent;
    std::vector<int> rank_;
    int count_;
};

} // namespace union_find

int main() {
    using namespace union_find;
    UnionFind uf(5);
    assert(uf.count() == 5);
    uf.unite(0, 1);
    assert(uf.connected(0, 1));
    assert(uf.count() == 4);
    uf.unite(1, 2);
    assert(uf.connected(0, 2));
    assert(uf.count() == 3);
    assert(!uf.connected(0, 3));

    UnionFind uf2(1000);
    for (int i = 0; i < 999; ++i) uf2.unite(i, i + 1);
    assert(uf2.count() == 1);
    assert(uf2.connected(0, 999));

    std::cout << "All union-find tests passed!" << std::endl;
    return 0;
}
