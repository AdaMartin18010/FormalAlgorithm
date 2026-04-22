"use strict";
/**
 * 字符串算法集合
 * 包含 KMP、Manacher、Z算法、滚动哈希、AC自动机、后缀数组
 */
Object.defineProperty(exports, "__esModule", { value: true });
exports.AhoCorasick = exports.ACNode = exports.RollingHash = void 0;
exports.kmpPrefix = kmpPrefix;
exports.kmpSearch = kmpSearch;
exports.manacher = manacher;
exports.zFunction = zFunction;
exports.suffixArray = suffixArray;
exports.lcpArray = lcpArray;
exports.runStringTests = runStringTests;
const utils_1 = require("./utils");
/**
 * KMP 前缀函数
 * 时间复杂度: O(m)
 */
function kmpPrefix(pattern) {
    const m = pattern.length;
    const pi = new Array(m).fill(0);
    let k = 0;
    for (let q = 1; q < m; q++) {
        while (k > 0 && pattern[k] !== pattern[q])
            k = pi[k - 1];
        if (pattern[k] === pattern[q])
            k++;
        pi[q] = k;
    }
    return pi;
}
/**
 * KMP 搜索
 * 时间复杂度: O(n + m)
 * 空间复杂度: O(m)
 */
function kmpSearch(text, pattern) {
    if (pattern.length === 0)
        return [];
    const pi = kmpPrefix(pattern);
    const matches = [];
    let q = 0;
    for (let i = 0; i < text.length; i++) {
        while (q > 0 && pattern[q] !== text[i])
            q = pi[q - 1];
        if (pattern[q] === text[i])
            q++;
        if (q === pattern.length) {
            matches.push(i - pattern.length + 1);
            q = pi[q - 1];
        }
    }
    return matches;
}
/**
 * Manacher 算法（最长回文子串半径）
 * 时间复杂度: O(n)
 * 空间复杂度: O(n)
 */
function manacher(s) {
    const t = "^#" + s.split("").join("#") + "#$";
    const n = t.length;
    const p = new Array(n).fill(0);
    let c = 0, r = 0;
    for (let i = 1; i < n - 1; i++) {
        const mirr = 2 * c - i;
        if (i < r)
            p[i] = Math.min(r - i, p[mirr]);
        while (t[i + 1 + p[i]] === t[i - 1 - p[i]])
            p[i]++;
        if (i + p[i] > r) {
            c = i;
            r = i + p[i];
        }
    }
    return p;
}
/**
 * Z 函数
 * 时间复杂度: O(n)
 * 空间复杂度: O(n)
 */
function zFunction(s) {
    const n = s.length;
    const z = new Array(n).fill(0);
    let l = 0, r = 0;
    for (let i = 1; i < n; i++) {
        if (i <= r)
            z[i] = Math.min(r - i + 1, z[i - l]);
        while (i + z[i] < n && s[z[i]] === s[i + z[i]])
            z[i]++;
        if (i + z[i] - 1 > r) {
            l = i;
            r = i + z[i] - 1;
        }
    }
    return z;
}
/**
 * 滚动哈希 (Rabin-Karp)
 * 时间复杂度: O(n) 预处理, O(1) 查询子串哈希
 * 空间复杂度: O(n)
 */
class RollingHash {
    constructor(s, base = 911, mod = 10 ** 9 + 7) {
        this.base = base;
        this.mod = mod;
        const n = s.length;
        this.prefix = new Array(n + 1).fill(0);
        this.power = new Array(n + 1).fill(1);
        for (let i = 0; i < n; i++) {
            this.prefix[i + 1] = (this.prefix[i] * this.base + s.charCodeAt(i)) % this.mod;
            this.power[i + 1] = (this.power[i] * this.base) % this.mod;
        }
    }
    /** O(1) 获取 [l, r) 子串哈希 */
    getHash(l, r) {
        let res = this.prefix[r] - (this.prefix[l] * this.power[r - l]) % this.mod;
        if (res < 0)
            res += this.mod;
        return res;
    }
}
exports.RollingHash = RollingHash;
// ==================== AC 自动机 ====================
class ACNode {
    constructor() {
        this.children = new Map();
        this.fail = null;
        this.output = [];
    }
}
exports.ACNode = ACNode;
class AhoCorasick {
    constructor() {
        this.root = new ACNode();
    }
    insert(word) {
        let node = this.root;
        for (const ch of word) {
            if (!node.children.has(ch))
                node.children.set(ch, new ACNode());
            node = node.children.get(ch);
        }
        node.output.push(word);
    }
    build() {
        const q = [];
        for (const node of this.root.children.values()) {
            node.fail = this.root;
            q.push(node);
        }
        while (q.length > 0) {
            const curr = q.shift();
            for (const [ch, child] of curr.children) {
                let fail = curr.fail;
                while (fail !== null && !fail.children.has(ch))
                    fail = fail.fail;
                child.fail = fail !== null ? fail.children.get(ch) ?? this.root : this.root;
                child.output.push(...child.fail.output);
                q.push(child);
            }
        }
    }
    search(text) {
        const res = [];
        let node = this.root;
        for (let i = 0; i < text.length; i++) {
            const ch = text[i];
            while (node !== this.root && !node.children.has(ch)) {
                node = node.fail;
            }
            node = node.children.get(ch) ?? this.root;
            if (node.output.length > 0) {
                res.push({ pos: i, words: node.output.slice() });
            }
        }
        return res;
    }
}
exports.AhoCorasick = AhoCorasick;
// ==================== 后缀数组 (SA) + LCP (Kasai) ====================
/**
 * 后缀数组 O(n log² n) 实现（倍增法）
 */
function suffixArray(s) {
    const n = s.length;
    const sa = Array.from({ length: n }, (_, i) => i);
    const ranks = s.split("").map(c => c.charCodeAt(0));
    const tmp = new Array(n);
    for (let k = 1; k < n; k *= 2) {
        sa.sort((a, b) => {
            if (ranks[a] !== ranks[b])
                return ranks[a] - ranks[b];
            const ra = a + k < n ? ranks[a + k] : -1;
            const rb = b + k < n ? ranks[b + k] : -1;
            return ra - rb;
        });
        tmp[sa[0]] = 0;
        for (let i = 1; i < n; i++) {
            const prev = sa[i - 1], curr = sa[i];
            const prevRank = ranks[prev];
            const currRank = ranks[curr];
            const prevNext = prev + k < n ? ranks[prev + k] : -1;
            const currNext = curr + k < n ? ranks[curr + k] : -1;
            tmp[curr] = tmp[prev] + (prevRank !== currRank || prevNext !== currNext ? 1 : 0);
        }
        for (let i = 0; i < n; i++)
            ranks[i] = tmp[i];
        if (ranks[sa[n - 1]] === n - 1)
            break;
    }
    return sa;
}
/**
 * Kasai LCP 算法
 * 时间复杂度: O(n)
 */
function lcpArray(s, sa) {
    const n = s.length;
    const rank = new Array(n);
    for (let i = 0; i < n; i++)
        rank[sa[i]] = i;
    const lcp = new Array(n - 1).fill(0);
    let k = 0;
    for (let i = 0; i < n; i++) {
        if (rank[i] === n - 1) {
            k = 0;
            continue;
        }
        const j = sa[rank[i] + 1];
        while (i + k < n && j + k < n && s[i + k] === s[j + k])
            k++;
        lcp[rank[i]] = k;
        if (k > 0)
            k--;
    }
    return lcp;
}
function runStringTests() {
    (0, utils_1.runTests)("String", {
        "kmpSearch": () => {
            (0, utils_1.assertArrayEq)(kmpSearch("abababc", "ababc"), [2]);
            (0, utils_1.assertArrayEq)(kmpSearch("aaaa", "aa"), [0, 1, 2]);
        },
        "manacher": () => {
            const p = manacher("abba");
            (0, utils_1.assertTrue)(p.some(v => v >= 4)); // "abba" 长度为4
        },
        "zFunction": () => {
            (0, utils_1.assertArrayEq)(zFunction("aaaaa"), [0, 4, 3, 2, 1]);
            (0, utils_1.assertArrayEq)(zFunction("ababa"), [0, 0, 3, 0, 1]);
        },
        "RollingHash": () => {
            const rh = new RollingHash("hello world");
            (0, utils_1.assertEq)(rh.getHash(0, 5), rh.getHash(6, 11)); // "hello" vs "world" no
            (0, utils_1.assertEq)(rh.getHash(0, 5), rh.getHash(0, 5));
        },
        "AhoCorasick": () => {
            const ac = new AhoCorasick();
            ac.insert("he");
            ac.insert("she");
            ac.insert("his");
            ac.insert("hers");
            ac.build();
            const res = ac.search("ushers");
            (0, utils_1.assertTrue)(res.some(r => r.words.includes("she")));
            (0, utils_1.assertTrue)(res.some(r => r.words.includes("he")));
            (0, utils_1.assertTrue)(res.some(r => r.words.includes("hers")));
        },
        "suffixArray": () => {
            const sa = suffixArray("banana");
            (0, utils_1.assertArrayEq)(sa, [5, 3, 1, 0, 4, 2]);
        },
        "lcpArray": () => {
            const s = "banana";
            const sa = suffixArray(s);
            (0, utils_1.assertArrayEq)(lcpArray(s, sa), [1, 3, 0, 0, 2]);
        },
    });
}
//# sourceMappingURL=string.js.map