/**
 * 经典数据结构实现
 * 包含链表、栈、队列、哈希表、并查集、线段树、树状数组、Trie、跳表
 */

import { runTests, assertEq, assertTrue, assertArrayEq } from "./utils";

// ==================== 链表 ====================

export class ListNode<T> {
  constructor(public value: T, public next: ListNode<T> | null = null) {}
}

export class LinkedList<T> {
  private head: ListNode<T> | null = null;
  private tail: ListNode<T> | null = null;
  private _size = 0;

  get size(): number { return this._size; }

  /** O(1) */
  append(value: T): void {
    const node = new ListNode(value);
    if (!this.tail) {
      this.head = this.tail = node;
    } else {
      this.tail.next = node;
      this.tail = node;
    }
    this._size++;
  }

  /** O(1) */
  prepend(value: T): void {
    const node = new ListNode(value, this.head);
    this.head = node;
    if (!this.tail) this.tail = node;
    this._size++;
  }

  /** O(n) */
  remove(value: T): boolean {
    if (!this.head) return false;
    if (this.head.value === value) {
      this.head = this.head.next;
      if (!this.head) this.tail = null;
      this._size--;
      return true;
    }
    let curr = this.head;
    while (curr.next && curr.next.value !== value) {
      curr = curr.next;
    }
    if (curr.next) {
      if (curr.next === this.tail) this.tail = curr;
      curr.next = curr.next.next;
      this._size--;
      return true;
    }
    return false;
  }

  /** O(n) */
  toArray(): T[] {
    const res: T[] = [];
    let curr = this.head;
    while (curr) {
      res.push(curr.value);
      curr = curr.next;
    }
    return res;
  }
}

// ==================== 栈 ====================

export class Stack<T> {
  private items: T[] = [];

  push(item: T): void { this.items.push(item); }
  pop(): T | undefined { return this.items.pop(); }
  peek(): T | undefined { return this.items[this.items.length - 1]; }
  get size(): number { return this.items.length; }
  isEmpty(): boolean { return this.items.length === 0; }
}

// ==================== 队列 ====================

export class Queue<T> {
  private items: T[] = [];
  private frontIdx = 0;

  enqueue(item: T): void { this.items.push(item); }
  dequeue(): T | undefined {
    if (this.frontIdx >= this.items.length) return undefined;
    return this.items[this.frontIdx++];
  }
  peek(): T | undefined { return this.items[this.frontIdx]; }
  get size(): number { return this.items.length - this.frontIdx; }
  isEmpty(): boolean { return this.size === 0; }
}

// ==================== 并查集 (Disjoint Set Union) ====================

export class UnionFind {
  private parent: number[];
  private rank: number[];

  constructor(n: number) {
    this.parent = Array.from({ length: n }, (_, i) => i);
    this.rank = new Array(n).fill(0);
  }

  /** O(α(n)) ~ O(1) */
  find(x: number): number {
    if (this.parent[x] !== x) {
      this.parent[x] = this.find(this.parent[x]);
    }
    return this.parent[x];
  }

  /** O(α(n)) ~ O(1) */
  union(x: number, y: number): boolean {
    const rx = this.find(x), ry = this.find(y);
    if (rx === ry) return false;
    if (this.rank[rx] < this.rank[ry]) {
      this.parent[rx] = ry;
    } else if (this.rank[rx] > this.rank[ry]) {
      this.parent[ry] = rx;
    } else {
      this.parent[ry] = rx;
      this.rank[rx]++;
    }
    return true;
  }

  connected(x: number, y: number): boolean {
    return this.find(x) === this.find(y);
  }
}

// ==================== 线段树 (区间求和) ====================

export class SegmentTree {
  private tree: number[];
  private n: number;

  constructor(arr: number[]) {
    this.n = arr.length;
    this.tree = new Array(4 * this.n).fill(0);
    this.build(0, 0, this.n - 1, arr);
  }

  private build(node: number, l: number, r: number, arr: number[]): void {
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
  query(ql: number, qr: number): number {
    return this._query(0, 0, this.n - 1, ql, qr);
  }

  private _query(node: number, l: number, r: number, ql: number, qr: number): number {
    if (ql <= l && r <= qr) return this.tree[node];
    if (r < ql || l > qr) return 0;
    const mid = Math.floor((l + r) / 2);
    return this._query(2 * node + 1, l, mid, ql, qr) +
           this._query(2 * node + 2, mid + 1, r, ql, qr);
  }

  /** O(log n) */
  update(idx: number, val: number): void {
    this._update(0, 0, this.n - 1, idx, val);
  }

  private _update(node: number, l: number, r: number, idx: number, val: number): void {
    if (l === r) {
      this.tree[node] = val;
      return;
    }
    const mid = Math.floor((l + r) / 2);
    if (idx <= mid) this._update(2 * node + 1, l, mid, idx, val);
    else this._update(2 * node + 2, mid + 1, r, idx, val);
    this.tree[node] = this.tree[2 * node + 1] + this.tree[2 * node + 2];
  }
}

// ==================== 树状数组 (Fenwick Tree / Binary Indexed Tree) ====================

export class FenwickTree {
  private tree: number[];

  constructor(n: number) {
    this.tree = new Array(n + 1).fill(0);
  }

  /** O(log n) */
  add(idx: number, delta: number): void {
    const n = this.tree.length;
    let i = idx + 1;
    while (i < n) {
      this.tree[i] += delta;
      i += i & -i;
    }
  }

  /** O(log n) */
  prefixSum(idx: number): number {
    let res = 0;
    let i = idx + 1;
    while (i > 0) {
      res += this.tree[i];
      i -= i & -i;
    }
    return res;
  }

  /** O(log n) */
  rangeSum(l: number, r: number): number {
    return this.prefixSum(r) - (l > 0 ? this.prefixSum(l - 1) : 0);
  }
}

// ==================== Trie (前缀树) ====================

export class TrieNode {
  children = new Map<string, TrieNode>();
  isEndOfWord = false;
}

export class Trie {
  root = new TrieNode();

  /** O(m) m = word.length */
  insert(word: string): void {
    let node = this.root;
    for (const ch of word) {
      if (!node.children.has(ch)) {
        node.children.set(ch, new TrieNode());
      }
      node = node.children.get(ch)!;
    }
    node.isEndOfWord = true;
  }

  /** O(m) */
  search(word: string): boolean {
    const node = this._findNode(word);
    return node !== null && node.isEndOfWord;
  }

  /** O(m) */
  startsWith(prefix: string): boolean {
    return this._findNode(prefix) !== null;
  }

  private _findNode(word: string): TrieNode | null {
    let node = this.root;
    for (const ch of word) {
      if (!node.children.has(ch)) return null;
      node = node.children.get(ch)!;
    }
    return node;
  }
}

// ==================== 跳表 (Skip List) ====================

export class SkipListNode<T> {
  constructor(
    public value: T,
    public next: (SkipListNode<T> | null)[] = []
  ) {}
}

export class SkipList<T> {
  private head: SkipListNode<T>;
  private maxLevel = 16;
  private level = 1;
  private compare: (a: T, b: T) => number;

  constructor(compare?: (a: T, b: T) => number) {
    this.compare = compare ?? ((a, b) => (a < b ? -1 : a > b ? 1 : 0));
    this.head = new SkipListNode<T>(null as unknown as T, new Array(this.maxLevel).fill(null));
  }

  private randomLevel(): number {
    let lvl = 1;
    while (Math.random() < 0.5 && lvl < this.maxLevel) lvl++;
    return lvl;
  }

  /** O(log n) 平均 */
  search(target: T): boolean {
    let curr = this.head;
    for (let i = this.level - 1; i >= 0; i--) {
      while (curr.next[i] && this.compare(curr.next[i]!.value, target) < 0) {
        curr = curr.next[i]!;
      }
    }
    const node = curr.next[0];
    return node !== null && this.compare(node.value, target) === 0;
  }

  /** O(log n) 平均 */
  insert(value: T): void {
    const update: (SkipListNode<T> | null)[] = new Array(this.maxLevel).fill(null);
    let curr = this.head;
    for (let i = this.level - 1; i >= 0; i--) {
      while (curr.next[i] && this.compare(curr.next[i]!.value, value) < 0) {
        curr = curr.next[i]!;
      }
      update[i] = curr;
    }
    const lvl = this.randomLevel();
    if (lvl > this.level) {
      for (let i = this.level; i < lvl; i++) update[i] = this.head;
      this.level = lvl;
    }
    const newNode = new SkipListNode(value, new Array(lvl).fill(null));
    for (let i = 0; i < lvl; i++) {
      newNode.next[i] = update[i]!.next[i];
      update[i]!.next[i] = newNode;
    }
  }
}

export function runDataStructureTests(): void {
  runTests("DataStructures", {
    "LinkedList": () => {
      const list = new LinkedList<number>();
      list.append(1); list.append(2); list.prepend(0);
      assertArrayEq(list.toArray(), [0, 1, 2]);
      assertEq(list.size, 3);
      list.remove(1);
      assertArrayEq(list.toArray(), [0, 2]);
    },
    "Stack": () => {
      const s = new Stack<number>();
      s.push(1); s.push(2); s.push(3);
      assertEq(s.pop(), 3);
      assertEq(s.peek(), 2);
      assertEq(s.size, 2);
    },
    "Queue": () => {
      const q = new Queue<number>();
      q.enqueue(1); q.enqueue(2); q.enqueue(3);
      assertEq(q.dequeue(), 1);
      assertEq(q.peek(), 2);
      assertEq(q.size, 2);
    },
    "UnionFind": () => {
      const uf = new UnionFind(5);
      uf.union(0, 1); uf.union(1, 2);
      assertTrue(uf.connected(0, 2));
      assertTrue(!uf.connected(0, 3));
    },
    "SegmentTree": () => {
      const st = new SegmentTree([1, 3, 5, 7, 9, 11]);
      assertEq(st.query(1, 3), 15); // 3+5+7
      st.update(2, 10);
      assertEq(st.query(1, 3), 20); // 3+10+7
    },
    "FenwickTree": () => {
      const ft = new FenwickTree(5);
      ft.add(0, 1); ft.add(1, 2); ft.add(2, 3);
      assertEq(ft.prefixSum(2), 6);
      assertEq(ft.rangeSum(1, 2), 5);
    },
    "Trie": () => {
      const trie = new Trie();
      trie.insert("apple"); trie.insert("app");
      assertTrue(trie.search("app"));
      assertTrue(trie.startsWith("app"));
      assertTrue(!trie.search("appl"));
    },
    "SkipList": () => {
      const sl = new SkipList<number>();
      sl.insert(3); sl.insert(1); sl.insert(2);
      assertTrue(sl.search(2));
      assertTrue(!sl.search(5));
    },
  });
}
