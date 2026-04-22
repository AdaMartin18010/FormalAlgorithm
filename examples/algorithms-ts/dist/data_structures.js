"use strict";
/**
 * 经典数据结构实现
 * 包含链表、栈、队列、哈希表、并查集、线段树、树状数组、Trie、跳表
 */
Object.defineProperty(exports, "__esModule", { value: true });
exports.SkipList = exports.SkipListNode = exports.Trie = exports.TrieNode = exports.FenwickTree = exports.SegmentTree = exports.UnionFind = exports.Queue = exports.Stack = exports.LinkedList = exports.ListNode = void 0;
exports.runDataStructureTests = runDataStructureTests;
const utils_1 = require("./utils");
// ==================== 链表 ====================
class ListNode {
    constructor(value, next = null) {
        this.value = value;
        this.next = next;
    }
}
exports.ListNode = ListNode;
class LinkedList {
    constructor() {
        this.head = null;
        this.tail = null;
        this._size = 0;
    }
    get size() { return this._size; }
    /** O(1) */
    append(value) {
        const node = new ListNode(value);
        if (!this.tail) {
            this.head = this.tail = node;
        }
        else {
            this.tail.next = node;
            this.tail = node;
        }
        this._size++;
    }
    /** O(1) */
    prepend(value) {
        const node = new ListNode(value, this.head);
        this.head = node;
        if (!this.tail)
            this.tail = node;
        this._size++;
    }
    /** O(n) */
    remove(value) {
        if (!this.head)
            return false;
        if (this.head.value === value) {
            this.head = this.head.next;
            if (!this.head)
                this.tail = null;
            this._size--;
            return true;
        }
        let curr = this.head;
        while (curr.next && curr.next.value !== value) {
            curr = curr.next;
        }
        if (curr.next) {
            if (curr.next === this.tail)
                this.tail = curr;
            curr.next = curr.next.next;
            this._size--;
            return true;
        }
        return false;
    }
    /** O(n) */
    toArray() {
        const res = [];
        let curr = this.head;
        while (curr) {
            res.push(curr.value);
            curr = curr.next;
        }
        return res;
    }
}
exports.LinkedList = LinkedList;
// ==================== 栈 ====================
class Stack {
    constructor() {
        this.items = [];
    }
    push(item) { this.items.push(item); }
    pop() { return this.items.pop(); }
    peek() { return this.items[this.items.length - 1]; }
    get size() { return this.items.length; }
    isEmpty() { return this.items.length === 0; }
}
exports.Stack = Stack;
// ==================== 队列 ====================
class Queue {
    constructor() {
        this.items = [];
        this.frontIdx = 0;
    }
    enqueue(item) { this.items.push(item); }
    dequeue() {
        if (this.frontIdx >= this.items.length)
            return undefined;
        return this.items[this.frontIdx++];
    }
    peek() { return this.items[this.frontIdx]; }
    get size() { return this.items.length - this.frontIdx; }
    isEmpty() { return this.size === 0; }
}
exports.Queue = Queue;
// ==================== 并查集 (Disjoint Set Union) ====================
class UnionFind {
    constructor(n) {
        this.parent = Array.from({ length: n }, (_, i) => i);
        this.rank = new Array(n).fill(0);
    }
    /** O(α(n)) ~ O(1) */
    find(x) {
        if (this.parent[x] !== x) {
            this.parent[x] = this.find(this.parent[x]);
        }
        return this.parent[x];
    }
    /** O(α(n)) ~ O(1) */
    union(x, y) {
        const rx = this.find(x), ry = this.find(y);
        if (rx === ry)
            return false;
        if (this.rank[rx] < this.rank[ry]) {
            this.parent[rx] = ry;
        }
        else if (this.rank[rx] > this.rank[ry]) {
            this.parent[ry] = rx;
        }
        else {
            this.parent[ry] = rx;
            this.rank[rx]++;
        }
        return true;
    }
    connected(x, y) {
        return this.find(x) === this.find(y);
    }
}
exports.UnionFind = UnionFind;
// ==================== 线段树 (区间求和) ====================
class SegmentTree {
    constructor(arr) {
        this.n = arr.length;
        this.tree = new Array(4 * this.n).fill(0);
        this.build(0, 0, this.n - 1, arr);
    }
    build(node, l, r, arr) {
        if (l === r) {
            this.tree[node] = arr[l];
            return;
        }
        const mid = Math.floor((l + r) / 2);
        this.build(2 * node + 1, l, mid, arr);
        this.build(2 * node + 2, mid + 1, r, arr);
        this.tree[node] = this.tree[2 * node + 1] + this.tree[2 * node + 2];
    }
    /** O(log n) */
    query(ql, qr) {
        return this._query(0, 0, this.n - 1, ql, qr);
    }
    _query(node, l, r, ql, qr) {
        if (ql <= l && r <= qr)
            return this.tree[node];
        if (r < ql || l > qr)
            return 0;
        const mid = Math.floor((l + r) / 2);
        return this._query(2 * node + 1, l, mid, ql, qr) +
            this._query(2 * node + 2, mid + 1, r, ql, qr);
    }
    /** O(log n) */
    update(idx, val) {
        this._update(0, 0, this.n - 1, idx, val);
    }
    _update(node, l, r, idx, val) {
        if (l === r) {
            this.tree[node] = val;
            return;
        }
        const mid = Math.floor((l + r) / 2);
        if (idx <= mid)
            this._update(2 * node + 1, l, mid, idx, val);
        else
            this._update(2 * node + 2, mid + 1, r, idx, val);
        this.tree[node] = this.tree[2 * node + 1] + this.tree[2 * node + 2];
    }
}
exports.SegmentTree = SegmentTree;
// ==================== 树状数组 (Fenwick Tree / Binary Indexed Tree) ====================
class FenwickTree {
    constructor(n) {
        this.tree = new Array(n + 1).fill(0);
    }
    /** O(log n) */
    add(idx, delta) {
        const n = this.tree.length;
        let i = idx + 1;
        while (i < n) {
            this.tree[i] += delta;
            i += i & -i;
        }
    }
    /** O(log n) */
    prefixSum(idx) {
        let res = 0;
        let i = idx + 1;
        while (i > 0) {
            res += this.tree[i];
            i -= i & -i;
        }
        return res;
    }
    /** O(log n) */
    rangeSum(l, r) {
        return this.prefixSum(r) - (l > 0 ? this.prefixSum(l - 1) : 0);
    }
}
exports.FenwickTree = FenwickTree;
// ==================== Trie (前缀树) ====================
class TrieNode {
    constructor() {
        this.children = new Map();
        this.isEndOfWord = false;
    }
}
exports.TrieNode = TrieNode;
class Trie {
    constructor() {
        this.root = new TrieNode();
    }
    /** O(m) m = word.length */
    insert(word) {
        let node = this.root;
        for (const ch of word) {
            if (!node.children.has(ch)) {
                node.children.set(ch, new TrieNode());
            }
            node = node.children.get(ch);
        }
        node.isEndOfWord = true;
    }
    /** O(m) */
    search(word) {
        const node = this._findNode(word);
        return node !== null && node.isEndOfWord;
    }
    /** O(m) */
    startsWith(prefix) {
        return this._findNode(prefix) !== null;
    }
    _findNode(word) {
        let node = this.root;
        for (const ch of word) {
            if (!node.children.has(ch))
                return null;
            node = node.children.get(ch);
        }
        return node;
    }
}
exports.Trie = Trie;
// ==================== 跳表 (Skip List) ====================
class SkipListNode {
    constructor(value, next = []) {
        this.value = value;
        this.next = next;
    }
}
exports.SkipListNode = SkipListNode;
class SkipList {
    constructor(compare) {
        this.maxLevel = 16;
        this.level = 1;
        this.compare = compare ?? ((a, b) => (a < b ? -1 : a > b ? 1 : 0));
        this.head = new SkipListNode(null, new Array(this.maxLevel).fill(null));
    }
    randomLevel() {
        let lvl = 1;
        while (Math.random() < 0.5 && lvl < this.maxLevel)
            lvl++;
        return lvl;
    }
    /** O(log n) 平均 */
    search(target) {
        let curr = this.head;
        for (let i = this.level - 1; i >= 0; i--) {
            while (curr.next[i] && this.compare(curr.next[i].value, target) < 0) {
                curr = curr.next[i];
            }
        }
        const node = curr.next[0];
        return node !== null && this.compare(node.value, target) === 0;
    }
    /** O(log n) 平均 */
    insert(value) {
        const update = new Array(this.maxLevel).fill(null);
        let curr = this.head;
        for (let i = this.level - 1; i >= 0; i--) {
            while (curr.next[i] && this.compare(curr.next[i].value, value) < 0) {
                curr = curr.next[i];
            }
            update[i] = curr;
        }
        const lvl = this.randomLevel();
        if (lvl > this.level) {
            for (let i = this.level; i < lvl; i++)
                update[i] = this.head;
            this.level = lvl;
        }
        const newNode = new SkipListNode(value, new Array(lvl).fill(null));
        for (let i = 0; i < lvl; i++) {
            newNode.next[i] = update[i].next[i];
            update[i].next[i] = newNode;
        }
    }
}
exports.SkipList = SkipList;
function runDataStructureTests() {
    (0, utils_1.runTests)("DataStructures", {
        "LinkedList": () => {
            const list = new LinkedList();
            list.append(1);
            list.append(2);
            list.prepend(0);
            (0, utils_1.assertArrayEq)(list.toArray(), [0, 1, 2]);
            (0, utils_1.assertEq)(list.size, 3);
            list.remove(1);
            (0, utils_1.assertArrayEq)(list.toArray(), [0, 2]);
        },
        "Stack": () => {
            const s = new Stack();
            s.push(1);
            s.push(2);
            s.push(3);
            (0, utils_1.assertEq)(s.pop(), 3);
            (0, utils_1.assertEq)(s.peek(), 2);
            (0, utils_1.assertEq)(s.size, 2);
        },
        "Queue": () => {
            const q = new Queue();
            q.enqueue(1);
            q.enqueue(2);
            q.enqueue(3);
            (0, utils_1.assertEq)(q.dequeue(), 1);
            (0, utils_1.assertEq)(q.peek(), 2);
            (0, utils_1.assertEq)(q.size, 2);
        },
        "UnionFind": () => {
            const uf = new UnionFind(5);
            uf.union(0, 1);
            uf.union(1, 2);
            (0, utils_1.assertTrue)(uf.connected(0, 2));
            (0, utils_1.assertTrue)(!uf.connected(0, 3));
        },
        "SegmentTree": () => {
            const st = new SegmentTree([1, 3, 5, 7, 9, 11]);
            (0, utils_1.assertEq)(st.query(1, 3), 15); // 3+5+7
            st.update(2, 10);
            (0, utils_1.assertEq)(st.query(1, 3), 20); // 3+10+7
        },
        "FenwickTree": () => {
            const ft = new FenwickTree(5);
            ft.add(0, 1);
            ft.add(1, 2);
            ft.add(2, 3);
            (0, utils_1.assertEq)(ft.prefixSum(2), 6);
            (0, utils_1.assertEq)(ft.rangeSum(1, 2), 5);
        },
        "Trie": () => {
            const trie = new Trie();
            trie.insert("apple");
            trie.insert("app");
            (0, utils_1.assertTrue)(trie.search("app"));
            (0, utils_1.assertTrue)(trie.startsWith("app"));
            (0, utils_1.assertTrue)(!trie.search("appl"));
        },
        "SkipList": () => {
            const sl = new SkipList();
            sl.insert(3);
            sl.insert(1);
            sl.insert(2);
            (0, utils_1.assertTrue)(sl.search(2));
            (0, utils_1.assertTrue)(!sl.search(5));
        },
    });
}
//# sourceMappingURL=data_structures.js.map