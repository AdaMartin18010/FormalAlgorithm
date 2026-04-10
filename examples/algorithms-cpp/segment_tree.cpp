/**
 * segment_tree.cpp - C++线段树实现
 * 支持：区间查询、区间更新、延迟传播
 */

#include <iostream>
#include <vector>
#include <functional>
#include <climits>

namespace segment_tree {

using namespace std;

/**
 * 线段树类
 * 支持：区间最值查询、区间和查询、单点更新、区间更新（延迟传播）
 */
class SegmentTree {
private:
    int n;
    vector<long long> tree;
    vector<long long> lazy;
    vector<long long> arr;
    function<long long(long long, long long)> merge;
    long long defaultVal;
    
    void build(int node, int start, int end) {
        if (start == end) {
            tree[node] = arr[start];
        } else {
            int mid = (start + end) / 2;
            build(2 * node, start, mid);
            build(2 * node + 1, mid + 1, end);
            tree[node] = merge(tree[2 * node], tree[2 * node + 1]);
        }
    }
    
    void pushDown(int node, int start, int end) {
        if (lazy[node] != 0) {
            int mid = (start + end) / 2;
            int leftChild = 2 * node;
            int rightChild = 2 * node + 1;
            
            // 更新子节点
            tree[leftChild] += lazy[node] * (mid - start + 1);
            tree[rightChild] += lazy[node] * (end - mid);
            
            lazy[leftChild] += lazy[node];
            lazy[rightChild] += lazy[node];
            
            lazy[node] = 0;
        }
    }
    
    void updateRange(int node, int start, int end, int l, int r, long long val) {
        if (start > r || end < l) return;
        
        if (start >= l && end <= r) {
            tree[node] += val * (end - start + 1);
            lazy[node] += val;
            return;
        }
        
        pushDown(node, start, end);
        
        int mid = (start + end) / 2;
        updateRange(2 * node, start, mid, l, r, val);
        updateRange(2 * node + 1, mid + 1, end, l, r, val);
        
        tree[node] = merge(tree[2 * node], tree[2 * node + 1]);
    }
    
    void updatePoint(int node, int start, int end, int idx, long long val) {
        if (start == end) {
            tree[node] = val;
            return;
        }
        
        pushDown(node, start, end);
        
        int mid = (start + end) / 2;
        if (idx <= mid) {
            updatePoint(2 * node, start, mid, idx, val);
        } else {
            updatePoint(2 * node + 1, mid + 1, end, idx, val);
        }
        
        tree[node] = merge(tree[2 * node], tree[2 * node + 1]);
    }
    
    long long query(int node, int start, int end, int l, int r) {
        if (start > r || end < l) return defaultVal;
        
        if (start >= l && end <= r) {
            return tree[node];
        }
        
        pushDown(node, start, end);
        
        int mid = (start + end) / 2;
        long long left = query(2 * node, start, mid, l, r);
        long long right = query(2 * node + 1, mid + 1, end, l, r);
        
        return merge(left, right);
    }

public:
    /**
     * 构造函数
     * @param input 输入数组
     * @param mergeFunc 合并函数（如求和、求最值）
     * @param defaultValue 默认值（用于空区间）
     */
    SegmentTree(const vector<long long>& input, 
                function<long long(long long, long long)> mergeFunc,
                long long defaultValue) {
        arr = input;
        n = arr.size();
        merge = mergeFunc;
        defaultVal = defaultValue;
        
        tree.resize(4 * n);
        lazy.resize(4 * n, 0);
        
        build(1, 0, n - 1);
    }
    
    // 区间查询
    long long query(int l, int r) {
        return query(1, 0, n - 1, l, r);
    }
    
    // 单点更新
    void update(int idx, long long val) {
        updatePoint(1, 0, n - 1, idx, val);
    }
    
    // 区间更新（加值）
    void updateRange(int l, int r, long long val) {
        updateRange(1, 0, n - 1, l, r, val);
    }
};

/**
 * 区间最值线段树（专用版本）
 */
class RangeMinSegmentTree {
private:
    int n;
    vector<int> tree;
    vector<int> lazy;
    
    void build(const vector<int>& arr, int node, int start, int end) {
        if (start == end) {
            tree[node] = arr[start];
        } else {
            int mid = (start + end) / 2;
            build(arr, 2 * node, start, mid);
            build(arr, 2 * node + 1, mid + 1, end);
            tree[node] = min(tree[2 * node], tree[2 * node + 1]);
        }
    }
    
    void pushDown(int node) {
        if (lazy[node] != 0) {
            tree[2 * node] += lazy[node];
            tree[2 * node + 1] += lazy[node];
            lazy[2 * node] += lazy[node];
            lazy[2 * node + 1] += lazy[node];
            lazy[node] = 0;
        }
    }
    
    void update(int node, int start, int end, int l, int r, int val) {
        if (start > r || end < l) return;
        
        if (start >= l && end <= r) {
            tree[node] += val;
            lazy[node] += val;
            return;
        }
        
        pushDown(node);
        
        int mid = (start + end) / 2;
        update(2 * node, start, mid, l, r, val);
        update(2 * node + 1, mid + 1, end, l, r, val);
        
        tree[node] = min(tree[2 * node], tree[2 * node + 1]);
    }
    
    int query(int node, int start, int end, int l, int r) {
        if (start > r || end < l) return INT_MAX;
        
        if (start >= l && end <= r) {
            return tree[node];
        }
        
        pushDown(node);
        
        int mid = (start + end) / 2;
        return min(query(2 * node, start, mid, l, r),
                   query(2 * node + 1, mid + 1, end, l, r));
    }

public:
    RangeMinSegmentTree(const vector<int>& arr) {
        n = arr.size();
        tree.resize(4 * n);
        lazy.resize(4 * n, 0);
        build(arr, 1, 0, n - 1);
    }
    
    int query(int l, int r) {
        return query(1, 0, n - 1, l, r);
    }
    
    void update(int l, int r, int val) {
        update(1, 0, n - 1, l, r, val);
    }
};

/**
 * 区间最大子段和线段树
 */
class MaxSubarraySegmentTree {
private:
    struct Node {
        long long sum;      // 区间和
        long long prefix;   // 最大前缀和
        long long suffix;   // 最大后缀和
        long long maxSum;   // 最大子段和
        
        Node() : sum(0), prefix(0), suffix(0), maxSum(0) {}
    };
    
    int n;
    vector<Node> tree;
    
    Node merge(const Node& left, const Node& right) {
        Node res;
        res.sum = left.sum + right.sum;
        res.prefix = max(left.prefix, left.sum + right.prefix);
        res.suffix = max(right.suffix, right.sum + left.suffix);
        res.maxSum = max({left.maxSum, right.maxSum, left.suffix + right.prefix});
        return res;
    }
    
    void build(const vector<long long>& arr, int node, int start, int end) {
        if (start == end) {
            tree[node].sum = arr[start];
            tree[node].prefix = arr[start];
            tree[node].suffix = arr[start];
            tree[node].maxSum = arr[start];
        } else {
            int mid = (start + end) / 2;
            build(arr, 2 * node, start, mid);
            build(arr, 2 * node + 1, mid + 1, end);
            tree[node] = merge(tree[2 * node], tree[2 * node + 1]);
        }
    }
    
    void update(int node, int start, int end, int idx, long long val) {
        if (start == end) {
            tree[node].sum = val;
            tree[node].prefix = val;
            tree[node].suffix = val;
            tree[node].maxSum = val;
            return;
        }
        
        int mid = (start + end) / 2;
        if (idx <= mid) {
            update(2 * node, start, mid, idx, val);
        } else {
            update(2 * node + 1, mid + 1, end, idx, val);
        }
        
        tree[node] = merge(tree[2 * node], tree[2 * node + 1]);
    }
    
    Node query(int node, int start, int end, int l, int r) {
        if (start > r || end < l) return Node();
        
        if (start >= l && end <= r) {
            return tree[node];
        }
        
        int mid = (start + end) / 2;
        Node left = query(2 * node, start, mid, l, r);
        Node right = query(2 * node + 1, mid + 1, end, l, r);
        
        return merge(left, right);
    }

public:
    MaxSubarraySegmentTree(const vector<long long>& arr) {
        n = arr.size();
        tree.resize(4 * n);
        build(arr, 1, 0, n - 1);
    }
    
    void update(int idx, long long val) {
        update(1, 0, n - 1, idx, val);
    }
    
    long long query(int l, int r) {
        return query(1, 0, n - 1, l, r).maxSum;
    }
};

} // namespace segment_tree

int main() {
    using namespace segment_tree;
    
    cout << "=== 线段树演示 ===" << endl;
    
    // 区间和线段树
    cout << "\n--- 区间和线段树 ---" << endl;
    vector<long long> arr = {1, 3, 5, 7, 9, 11};
    SegmentTree sumTree(arr, [](long long a, long long b) { return a + b; }, 0);
    
    cout << "数组: ";
    for (auto x : arr) cout << x << " ";
    cout << endl;
    
    cout << "区间 [1, 3] 和: " << sumTree.query(1, 3) << endl;
    
    sumTree.update(2, 10);
    cout << "更新 arr[2] = 10 后，区间 [1, 3] 和: " << sumTree.query(1, 3) << endl;
    
    sumTree.updateRange(0, 2, 5);
    cout << "区间 [0, 2] 加 5 后，区间 [0, 3] 和: " << sumTree.query(0, 3) << endl;
    
    // 区间最小值线段树
    cout << "\n--- 区间最小值线段树 ---" << endl;
    vector<int> arr2 = {5, 2, 8, 1, 9, 3, 7};
    RangeMinSegmentTree minTree(arr2);
    
    cout << "数组: ";
    for (auto x : arr2) cout << x << " ";
    cout << endl;
    
    cout << "区间 [1, 4] 最小值: " << minTree.query(1, 4) << endl;
    
    minTree.update(2, 3, -3);
    cout << "区间 [2, 3] 减 3 后，区间 [1, 4] 最小值: " << minTree.query(1, 4) << endl;
    
    // 最大子段和线段树
    cout << "\n--- 最大子段和线段树 ---" << endl;
    vector<long long> arr3 = {-2, 1, -3, 4, -1, 2, 1, -5, 4};
    MaxSubarraySegmentTree maxSubTree(arr3);
    
    cout << "数组: ";
    for (auto x : arr3) cout << x << " ";
    cout << endl;
    
    cout << "区间 [0, 8] 最大子段和: " << maxSubTree.query(0, 8) << endl;
    cout << "区间 [3, 6] 最大子段和: " << maxSubTree.query(3, 6) << endl;
    
    maxSubTree.update(3, -1);
    cout << "更新 arr[3] = -1 后，区间 [0, 8] 最大子段和: " << maxSubTree.query(0, 8) << endl;
    
    return 0;
}
