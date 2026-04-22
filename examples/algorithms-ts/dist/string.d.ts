/**
 * 字符串算法集合
 * 包含 KMP、Manacher、Z算法、滚动哈希、AC自动机、后缀数组
 */
/**
 * KMP 前缀函数
 * 时间复杂度: O(m)
 */
export declare function kmpPrefix(pattern: string): number[];
/**
 * KMP 搜索
 * 时间复杂度: O(n + m)
 * 空间复杂度: O(m)
 */
export declare function kmpSearch(text: string, pattern: string): number[];
/**
 * Manacher 算法（最长回文子串半径）
 * 时间复杂度: O(n)
 * 空间复杂度: O(n)
 */
export declare function manacher(s: string): number[];
/**
 * Z 函数
 * 时间复杂度: O(n)
 * 空间复杂度: O(n)
 */
export declare function zFunction(s: string): number[];
/**
 * 滚动哈希 (Rabin-Karp)
 * 时间复杂度: O(n) 预处理, O(1) 查询子串哈希
 * 空间复杂度: O(n)
 */
export declare class RollingHash {
    private prefix;
    private power;
    private readonly base;
    private readonly mod;
    constructor(s: string, base?: number, mod?: number);
    /** O(1) 获取 [l, r) 子串哈希 */
    getHash(l: number, r: number): number;
}
export declare class ACNode {
    children: Map<string, ACNode>;
    fail: ACNode | null;
    output: string[];
}
export declare class AhoCorasick {
    root: ACNode;
    insert(word: string): void;
    build(): void;
    search(text: string): {
        pos: number;
        words: string[];
    }[];
}
/**
 * 后缀数组 O(n log² n) 实现（倍增法）
 */
export declare function suffixArray(s: string): number[];
/**
 * Kasai LCP 算法
 * 时间复杂度: O(n)
 */
export declare function lcpArray(s: string, sa: number[]): number[];
export declare function runStringTests(): void;
//# sourceMappingURL=string.d.ts.map