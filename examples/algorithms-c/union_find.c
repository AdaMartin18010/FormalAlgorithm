/**
 * union_find.c - C语言并查集实现
 * 支持：路径压缩、按秩合并
 */

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

typedef struct {
    int* parent;
    int* rank;
    int count;
    int n;
} UnionFind;

UnionFind* uf_create(int n) {
    UnionFind* uf = (UnionFind*)malloc(sizeof(UnionFind));
    uf->parent = (int*)malloc(n * sizeof(int));
    uf->rank = (int*)calloc(n, sizeof(int));
    uf->count = n;
    uf->n = n;
    for (int i = 0; i < n; i++) uf->parent[i] = i;
    return uf;
}

void uf_free(UnionFind* uf) {
    free(uf->parent);
    free(uf->rank);
    free(uf);
}

int uf_find(UnionFind* uf, int x) {
    if (uf->parent[x] != x) {
        uf->parent[x] = uf_find(uf, uf->parent[x]);
    }
    return uf->parent[x];
}

void uf_union(UnionFind* uf, int x, int y) {
    int rx = uf_find(uf, x);
    int ry = uf_find(uf, y);
    if (rx == ry) return;
    if (uf->rank[rx] < uf->rank[ry]) {
        int tmp = rx; rx = ry; ry = tmp;
    }
    uf->parent[ry] = rx;
    if (uf->rank[rx] == uf->rank[ry]) uf->rank[rx]++;
    uf->count--;
}

int uf_connected(UnionFind* uf, int x, int y) {
    return uf_find(uf, x) == uf_find(uf, y);
}

int main() {
    UnionFind* uf = uf_create(5);
    assert(uf->count == 5);
    uf_union(uf, 0, 1);
    assert(uf_connected(uf, 0, 1));
    assert(uf->count == 4);
    uf_union(uf, 1, 2);
    assert(uf_connected(uf, 0, 2));
    assert(uf->count == 3);
    assert(!uf_connected(uf, 0, 3));
    
    UnionFind* uf2 = uf_create(1000);
    for (int i = 0; i < 999; i++) uf_union(uf2, i, i + 1);
    assert(uf2->count == 1);
    assert(uf_connected(uf2, 0, 999));
    uf_free(uf2);
    uf_free(uf);
    
    printf("All union-find tests passed!\n");
    return 0;
}
