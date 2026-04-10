/**
 * data_structures.c - C语言数据结构实现
 * 包含：并查集、线段树、Trie树
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>

// ==================== 并查集 (Disjoint Set Union) ====================

typedef struct {
    int* parent;
    int* rank;
    int n;
} DSU;

// 创建并查集
DSU* dsu_create(int n) {
    DSU* dsu = (DSU*)malloc(sizeof(DSU));
    dsu->parent = (int*)malloc(n * sizeof(int));
    dsu->rank = (int*)calloc(n, sizeof(int));
    dsu->n = n;
    
    for (int i = 0; i < n; i++)
        dsu->parent[i] = i;
    
    return dsu;
}

// 查找（路径压缩）
int dsu_find(DSU* dsu, int x) {
    if (dsu->parent[x] != x)
        dsu->parent[x] = dsu_find(dsu, dsu->parent[x]);
    return dsu->parent[x];
}

// 合并（按秩合并）
void dsu_union(DSU* dsu, int x, int y) {
    int px = dsu_find(dsu, x);
    int py = dsu_find(dsu, y);
    
    if (px == py) return;
    
    if (dsu->rank[px] < dsu->rank[py]) {
        dsu->parent[px] = py;
    } else if (dsu->rank[px] > dsu->rank[py]) {
        dsu->parent[py] = px;
    } else {
        dsu->parent[py] = px;
        dsu->rank[px]++;
    }
}

// 释放并查集
void dsu_free(DSU* dsu) {
    free(dsu->parent);
    free(dsu->rank);
    free(dsu);
}

// ==================== 线段树 (Segment Tree) ====================

typedef struct {
    int* tree;
    int* lazy;
    int n;
} SegmentTree;

// 创建线段树
SegmentTree* seg_tree_create(int arr[], int n) {
    SegmentTree* st = (SegmentTree*)malloc(sizeof(SegmentTree));
    st->tree = (int*)calloc(4 * n, sizeof(int));
    st->lazy = (int*)calloc(4 * n, sizeof(int));
    st->n = n;
    
    // 初始化
    for (int i = 0; i < 4 * n; i++) {
        st->tree[i] = 0;
        st->lazy[i] = 0;
    }
    
    return st;
}

// 构建线段树
void seg_tree_build(SegmentTree* st, int arr[], int node, int start, int end) {
    if (start == end) {
        st->tree[node] = arr[start];
        return;
    }
    
    int mid = (start + end) / 2;
    seg_tree_build(st, arr, 2 * node + 1, start, mid);
    seg_tree_build(st, arr, 2 * node + 2, mid + 1, end);
    
    st->tree[node] = st->tree[2 * node + 1] + st->tree[2 * node + 2];
}

// 区间查询
int seg_tree_query(SegmentTree* st, int node, int start, int end, int l, int r) {
    if (r < start || end < l)
        return 0;
    
    if (l <= start && end <= r)
        return st->tree[node];
    
    int mid = (start + end) / 2;
    int left_sum = seg_tree_query(st, 2 * node + 1, start, mid, l, r);
    int right_sum = seg_tree_query(st, 2 * node + 2, mid + 1, end, l, r);
    
    return left_sum + right_sum;
}

// 单点更新
void seg_tree_update(SegmentTree* st, int node, int start, int end, int idx, int val) {
    if (start == end) {
        st->tree[node] = val;
        return;
    }
    
    int mid = (start + end) / 2;
    if (idx <= mid)
        seg_tree_update(st, 2 * node + 1, start, mid, idx, val);
    else
        seg_tree_update(st, 2 * node + 2, mid + 1, end, idx, val);
    
    st->tree[node] = st->tree[2 * node + 1] + st->tree[2 * node + 2];
}

// 释放线段树
void seg_tree_free(SegmentTree* st) {
    free(st->tree);
    free(st->lazy);
    free(st);
}

// ==================== Trie树 (前缀树) ====================

#define ALPHABET_SIZE 26

typedef struct TrieNode {
    struct TrieNode* children[ALPHABET_SIZE];
    bool is_end_of_word;
    int count;  // 经过该节点的单词数
} TrieNode;

// 创建Trie节点
TrieNode* trie_create_node() {
    TrieNode* node = (TrieNode*)malloc(sizeof(TrieNode));
    node->is_end_of_word = false;
    node->count = 0;
    
    for (int i = 0; i < ALPHABET_SIZE; i++)
        node->children[i] = NULL;
    
    return node;
}

// 插入单词
void trie_insert(TrieNode* root, const char* word) {
    TrieNode* current = root;
    
    for (int i = 0; word[i] != '\0'; i++) {
        int index = word[i] - 'a';
        
        if (current->children[index] == NULL)
            current->children[index] = trie_create_node();
        
        current = current->children[index];
        current->count++;
    }
    
    current->is_end_of_word = true;
}

// 查找单词
bool trie_search(TrieNode* root, const char* word) {
    TrieNode* current = root;
    
    for (int i = 0; word[i] != '\0'; i++) {
        int index = word[i] - 'a';
        
        if (current->children[index] == NULL)
            return false;
        
        current = current->children[index];
    }
    
    return current->is_end_of_word;
}

// 前缀匹配
bool trie_starts_with(TrieNode* root, const char* prefix) {
    TrieNode* current = root;
    
    for (int i = 0; prefix[i] != '\0'; i++) {
        int index = prefix[i] - 'a';
        
        if (current->children[index] == NULL)
            return false;
        
        current = current->children[index];
    }
    
    return true;
}

// 删除单词（简化版）
void trie_delete(TrieNode* root, const char* word) {
    // 简化实现：仅标记为非单词结尾
    TrieNode* current = root;
    
    for (int i = 0; word[i] != '\0'; i++) {
        int index = word[i] - 'a';
        
        if (current->children[index] == NULL)
            return;
        
        current = current->children[index];
        current->count--;
    }
    
    current->is_end_of_word = false;
}

// 释放Trie
void trie_free(TrieNode* node) {
    if (node == NULL) return;
    
    for (int i = 0; i < ALPHABET_SIZE; i++)
        trie_free(node->children[i]);
    
    free(node);
}

// ==================== 测试 ====================

void test_dsu() {
    printf("=== DSU Test ===\n");
    DSU* dsu = dsu_create(5);
    
    dsu_union(dsu, 0, 2);
    dsu_union(dsu, 4, 2);
    dsu_union(dsu, 1, 3);
    
    printf("0 and 4 connected: %s\n", dsu_find(dsu, 0) == dsu_find(dsu, 4) ? "Yes" : "No");
    printf("0 and 1 connected: %s\n", dsu_find(dsu, 0) == dsu_find(dsu, 1) ? "Yes" : "No");
    
    dsu_free(dsu);
    printf("\n");
}

void test_segment_tree() {
    printf("=== Segment Tree Test ===\n");
    int arr[] = {1, 3, 5, 7, 9, 11};
    int n = sizeof(arr) / sizeof(arr[0]);
    
    SegmentTree* st = seg_tree_create(arr, n);
    seg_tree_build(st, arr, 0, 0, n - 1);
    
    printf("Sum of range [1, 3]: %d\n", seg_tree_query(st, 0, 0, n - 1, 1, 3));
    
    printf("Update index 1 to 10\n");
    seg_tree_update(st, 0, 0, n - 1, 1, 10);
    printf("Sum of range [1, 3] after update: %d\n", seg_tree_query(st, 0, 0, n - 1, 1, 3));
    
    seg_tree_free(st);
    printf("\n");
}

void test_trie() {
    printf("=== Trie Test ===\n");
    TrieNode* root = trie_create_node();
    
    trie_insert(root, "hello");
    trie_insert(root, "world");
    trie_insert(root, "hell");
    trie_insert(root, "heaven");
    
    printf("Search 'hello': %s\n", trie_search(root, "hello") ? "Found" : "Not found");
    printf("Search 'hell': %s\n", trie_search(root, "hell") ? "Found" : "Not found");
    printf("Search 'heavenly': %s\n", trie_search(root, "heavenly") ? "Found" : "Not found");
    printf("Starts with 'he': %s\n", trie_starts_with(root, "he") ? "Yes" : "No");
    printf("Starts with 'ho': %s\n", trie_starts_with(root, "ho") ? "Yes" : "No");
    
    trie_free(root);
    printf("\n");
}

int main() {
    test_dsu();
    test_segment_tree();
    test_trie();
    
    return 0;
}
