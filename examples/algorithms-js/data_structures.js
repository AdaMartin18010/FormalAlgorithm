/**
 * data_structures.js - JavaScript数据结构实现
 * 包含：堆、并查集、Trie树、LRU缓存、线段树
 */

/**
 * 最小堆 / 最大堆
 */
class Heap {
    constructor(compare = (a, b) => a - b) {
        this.data = [];
        this.compare = compare;
    }

    size() {
        return this.data.length;
    }

    isEmpty() {
        return this.size() === 0;
    }

    peek() {
        return this.isEmpty() ? null : this.data[0];
    }

    push(value) {
        this.data.push(value);
        this.siftUp(this.size() - 1);
    }

    pop() {
        if (this.isEmpty()) return null;
        
        const result = this.data[0];
        const last = this.data.pop();
        
        if (!this.isEmpty()) {
            this.data[0] = last;
            this.siftDown(0);
        }
        
        return result;
    }

    siftUp(index) {
        while (index > 0) {
            const parent = Math.floor((index - 1) / 2);
            if (this.compare(this.data[index], this.data[parent]) >= 0) break;
            
            [this.data[index], this.data[parent]] = [this.data[parent], this.data[index]];
            index = parent;
        }
    }

    siftDown(index) {
        const n = this.size();
        
        while (true) {
            let smallest = index;
            const left = 2 * index + 1;
            const right = 2 * index + 2;
            
            if (left < n && this.compare(this.data[left], this.data[smallest]) < 0) {
                smallest = left;
            }
            if (right < n && this.compare(this.data[right], this.data[smallest]) < 0) {
                smallest = right;
            }
            
            if (smallest === index) break;
            
            [this.data[index], this.data[smallest]] = [this.data[smallest], this.data[index]];
            index = smallest;
        }
    }

    // 从数组构建堆
    static fromArray(arr, compare = (a, b) => a - b) {
        const heap = new Heap(compare);
        heap.data = [...arr];
        for (let i = Math.floor(heap.size() / 2) - 1; i >= 0; i--) {
            heap.siftDown(i);
        }
        return heap;
    }
}

/**
 * 并查集 (Union-Find)
 */
class UnionFind {
    constructor(n) {
        this.parent = new Array(n).fill(0).map((_, i) => i);
        this.rank = new Array(n).fill(0);
        this.count = n;
    }

    find(x) {
        if (this.parent[x] !== x) {
            this.parent[x] = this.find(this.parent[x]); // 路径压缩
        }
        return this.parent[x];
    }

    union(x, y) {
        const px = this.find(x);
        const py = this.find(y);
        
        if (px === py) return false;
        
        // 按秩合并
        if (this.rank[px] < this.rank[py]) {
            this.parent[px] = py;
        } else if (this.rank[px] > this.rank[py]) {
            this.parent[py] = px;
        } else {
            this.parent[py] = px;
            this.rank[px]++;
        }
        
        this.count--;
        return true;
    }

    connected(x, y) {
        return this.find(x) === this.find(y);
    }

    getCount() {
        return this.count;
    }
}

/**
 * Trie树 (前缀树)
 */
class TrieNode {
    constructor() {
        this.children = new Map();
        this.isEnd = false;
        this.count = 0; // 经过该节点的单词数
    }
}

class Trie {
    constructor() {
        this.root = new TrieNode();
    }

    insert(word) {
        let node = this.root;
        for (const char of word) {
            if (!node.children.has(char)) {
                node.children.set(char, new TrieNode());
            }
            node = node.children.get(char);
            node.count++;
        }
        node.isEnd = true;
    }

    search(word) {
        const node = this.findNode(word);
        return node !== null && node.isEnd;
    }

    startsWith(prefix) {
        return this.findNode(prefix) !== null;
    }

    countPrefix(prefix) {
        const node = this.findNode(prefix);
        return node ? node.count : 0;
    }

    findNode(str) {
        let node = this.root;
        for (const char of str) {
            if (!node.children.has(char)) return null;
            node = node.children.get(char);
        }
        return node;
    }

    // 获取所有以prefix开头的单词
    getWordsWithPrefix(prefix) {
        const result = [];
        const node = this.findNode(prefix);
        if (!node) return result;
        
        this.dfs(node, prefix, result);
        return result;
    }

    dfs(node, current, result) {
        if (node.isEnd) {
            result.push(current);
        }
        
        for (const [char, child] of node.children) {
            this.dfs(child, current + char, result);
        }
    }
}

/**
 * LRU缓存 (Least Recently Used)
 */
class LRUCache {
    constructor(capacity) {
        this.capacity = capacity;
        this.cache = new Map();
    }

    get(key) {
        if (!this.cache.has(key)) return -1;
        
        // 移动到末尾（最新使用）
        const value = this.cache.get(key);
        this.cache.delete(key);
        this.cache.set(key, value);
        return value;
    }

    put(key, value) {
        if (this.cache.has(key)) {
            this.cache.delete(key);
        } else if (this.cache.size >= this.capacity) {
            // 删除最久未使用的（Map的第一个元素）
            const firstKey = this.cache.keys().next().value;
            this.cache.delete(firstKey);
        }
        
        this.cache.set(key, value);
    }

    size() {
        return this.cache.size;
    }
}

/**
 * 线段树（区间求和）
 */
class SegmentTree {
    constructor(arr) {
        this.n = arr.length;
        this.tree = new Array(4 * this.n).fill(0);
        this.lazy = new Array(4 * this.n).fill(0);
        this.build(arr, 1, 0, this.n - 1);
    }

    build(arr, node, start, end) {
        if (start === end) {
            this.tree[node] = arr[start];
        } else {
            const mid = Math.floor((start + end) / 2);
            this.build(arr, 2 * node, start, mid);
            this.build(arr, 2 * node + 1, mid + 1, end);
            this.tree[node] = this.tree[2 * node] + this.tree[2 * node + 1];
        }
    }

    pushDown(node, start, end) {
        if (this.lazy[node] !== 0) {
            const mid = Math.floor((start + end) / 2);
            
            this.tree[2 * node] += this.lazy[node] * (mid - start + 1);
            this.tree[2 * node + 1] += this.lazy[node] * (end - mid);
            
            this.lazy[2 * node] += this.lazy[node];
            this.lazy[2 * node + 1] += this.lazy[node];
            
            this.lazy[node] = 0;
        }
    }

    updateRange(node, start, end, l, r, val) {
        if (start > r || end < l) return;
        
        if (start >= l && end <= r) {
            this.tree[node] += val * (end - start + 1);
            this.lazy[node] += val;
            return;
        }
        
        this.pushDown(node, start, end);
        
        const mid = Math.floor((start + end) / 2);
        this.updateRange(2 * node, start, mid, l, r, val);
        this.updateRange(2 * node + 1, mid + 1, end, l, r, val);
        
        this.tree[node] = this.tree[2 * node] + this.tree[2 * node + 1];
    }

    query(node, start, end, l, r) {
        if (start > r || end < l) return 0;
        
        if (start >= l && end <= r) {
            return this.tree[node];
        }
        
        this.pushDown(node, start, end);
        
        const mid = Math.floor((start + end) / 2);
        return this.query(2 * node, start, mid, l, r) +
               this.query(2 * node + 1, mid + 1, end, l, r);
    }

    // 公共接口
    rangeUpdate(l, r, val) {
        this.updateRange(1, 0, this.n - 1, l, r, val);
    }

    rangeQuery(l, r) {
        return this.query(1, 0, this.n - 1, l, r);
    }
}

/**
 * 双向链表节点（用于实现LCA的另一种方式）
 */
class ListNode {
    constructor(val) {
        this.val = val;
        this.prev = null;
        this.next = null;
    }
}

/**
 * 单调栈
 */
class MonotonicStack {
    constructor(ascending = true) {
        this.stack = [];
        this.ascending = ascending;
    }

    push(val) {
        while (this.stack.length > 0) {
            const top = this.stack[this.stack.length - 1];
            if (this.ascending ? top < val : top > val) break;
            this.stack.pop();
        }
        this.stack.push(val);
    }

    pop() {
        return this.stack.pop();
    }

    top() {
        return this.stack.length > 0 ? this.stack[this.stack.length - 1] : null;
    }

    isEmpty() {
        return this.stack.length === 0;
    }
}

// 测试
if (require.main === module) {
    console.log('=== JavaScript数据结构演示 ===\n');

    // 堆测试
    console.log('--- 最小堆 ---');
    const minHeap = new Heap();
    [5, 3, 8, 1, 9, 2].forEach(x => minHeap.push(x));
    console.log('堆大小:', minHeap.size());
    console.log('弹出元素:', minHeap.pop(), minHeap.pop(), minHeap.pop());

    // 并查集测试
    console.log('\n--- 并查集 ---');
    const uf = new UnionFind(5);
    console.log('初始集合数:', uf.getCount());
    uf.union(0, 1);
    uf.union(2, 3);
    uf.union(1, 2);
    console.log('合并后集合数:', uf.getCount());
    console.log('0和3是否连通:', uf.connected(0, 3));
    console.log('0和4是否连通:', uf.connected(0, 4));

    // Trie测试
    console.log('\n--- Trie树 ---');
    const trie = new Trie();
    ['apple', 'app', 'application', 'banana'].forEach(w => trie.insert(w));
    console.log('搜索 apple:', trie.search('apple'));
    console.log('搜索 app:', trie.search('app'));
    console.log('前缀搜索 ap:', trie.startsWith('ap'));
    console.log('以app开头的单词:', trie.getWordsWithPrefix('app'));

    // LRU缓存测试
    console.log('\n--- LRU缓存 ---');
    const cache = new LRUCache(2);
    cache.put(1, 1);
    cache.put(2, 2);
    console.log('获取1:', cache.get(1));
    cache.put(3, 3); // 淘汰2
    console.log('获取2:', cache.get(2));
    console.log('获取3:', cache.get(3));

    // 线段树测试
    console.log('\n--- 线段树 ---');
    const segTree = new SegmentTree([1, 3, 5, 7, 9, 11]);
    console.log('区间 [1, 3] 和:', segTree.rangeQuery(1, 3));
    segTree.rangeUpdate(0, 2, 5);
    console.log('区间更新后 [0, 3] 和:', segTree.rangeQuery(0, 3));
}

module.exports = {
    Heap,
    UnionFind,
    Trie,
    TrieNode,
    LRUCache,
    SegmentTree,
    ListNode,
    MonotonicStack
};
