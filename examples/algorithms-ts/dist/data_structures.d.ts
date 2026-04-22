/**
 * 经典数据结构实现
 * 包含链表、栈、队列、哈希表、并查集、线段树、树状数组、Trie、跳表
 */
export declare class ListNode<T> {
    value: T;
    next: ListNode<T> | null;
    constructor(value: T, next?: ListNode<T> | null);
}
export declare class LinkedList<T> {
    private head;
    private tail;
    private _size;
    get size(): number;
    /** O(1) */
    append(value: T): void;
    /** O(1) */
    prepend(value: T): void;
    /** O(n) */
    remove(value: T): boolean;
    /** O(n) */
    toArray(): T[];
}
export declare class Stack<T> {
    private items;
    push(item: T): void;
    pop(): T | undefined;
    peek(): T | undefined;
    get size(): number;
    isEmpty(): boolean;
}
export declare class Queue<T> {
    private items;
    private frontIdx;
    enqueue(item: T): void;
    dequeue(): T | undefined;
    peek(): T | undefined;
    get size(): number;
    isEmpty(): boolean;
}
export declare class UnionFind {
    private parent;
    private rank;
    constructor(n: number);
    /** O(α(n)) ~ O(1) */
    find(x: number): number;
    /** O(α(n)) ~ O(1) */
    union(x: number, y: number): boolean;
    connected(x: number, y: number): boolean;
}
export declare class SegmentTree {
    private tree;
    private n;
    constructor(arr: number[]);
    private build;
    /** O(log n) */
    query(ql: number, qr: number): number;
    private _query;
    /** O(log n) */
    update(idx: number, val: number): void;
    private _update;
}
export declare class FenwickTree {
    private tree;
    constructor(n: number);
    /** O(log n) */
    add(idx: number, delta: number): void;
    /** O(log n) */
    prefixSum(idx: number): number;
    /** O(log n) */
    rangeSum(l: number, r: number): number;
}
export declare class TrieNode {
    children: Map<string, TrieNode>;
    isEndOfWord: boolean;
}
export declare class Trie {
    root: TrieNode;
    /** O(m) m = word.length */
    insert(word: string): void;
    /** O(m) */
    search(word: string): boolean;
    /** O(m) */
    startsWith(prefix: string): boolean;
    private _findNode;
}
export declare class SkipListNode<T> {
    value: T;
    next: (SkipListNode<T> | null)[];
    constructor(value: T, next?: (SkipListNode<T> | null)[]);
}
export declare class SkipList<T> {
    private head;
    private maxLevel;
    private level;
    private compare;
    constructor(compare?: (a: T, b: T) => number);
    private randomLevel;
    /** O(log n) 平均 */
    search(target: T): boolean;
    /** O(log n) 平均 */
    insert(value: T): void;
}
export declare function runDataStructureTests(): void;
//# sourceMappingURL=data_structures.d.ts.map