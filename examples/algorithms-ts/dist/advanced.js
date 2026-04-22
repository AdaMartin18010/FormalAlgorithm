"use strict";
/**
 * 高级算法集合
 * 包含 FFT、莫队算法、舞蹈链、模拟退火
 */
Object.defineProperty(exports, "__esModule", { value: true });
exports.DancingLinks = exports.DLXColumn = exports.DLXNode = exports.Complex = void 0;
exports.multiplyPolynomials = multiplyPolynomials;
exports.moAlgorithm = moAlgorithm;
exports.simulatedAnnealing = simulatedAnnealing;
exports.runAdvancedTests = runAdvancedTests;
const utils_1 = require("./utils");
// ==================== FFT (快速傅里叶变换) ====================
class Complex {
    constructor(re, im = 0) {
        this.re = re;
        this.im = im;
    }
    add(other) { return new Complex(this.re + other.re, this.im + other.im); }
    sub(other) { return new Complex(this.re - other.re, this.im - other.im); }
    mul(other) {
        return new Complex(this.re * other.re - this.im * other.im, this.re * other.im + this.im * other.re);
    }
}
exports.Complex = Complex;
function _fft(a, invert) {
    const n = a.length;
    if (n === 1)
        return;
    const a0 = [];
    const a1 = [];
    for (let i = 0; i < n; i += 2) {
        a0.push(a[i]);
        a1.push(a[i + 1]);
    }
    _fft(a0, invert);
    _fft(a1, invert);
    const ang = (2 * Math.PI / n) * (invert ? -1 : 1);
    let w = new Complex(1);
    const wn = new Complex(Math.cos(ang), Math.sin(ang));
    for (let i = 0; i < n / 2; i++) {
        a[i] = a0[i].add(w.mul(a1[i]));
        a[i + n / 2] = a0[i].sub(w.mul(a1[i]));
        if (invert) {
            a[i] = new Complex(a[i].re / 2, a[i].im / 2);
            a[i + n / 2] = new Complex(a[i + n / 2].re / 2, a[i + n / 2].im / 2);
        }
        w = w.mul(wn);
    }
}
/**
 * 多项式乘法（卷积）
 * 时间复杂度: O(n log n)
 */
function multiplyPolynomials(a, b) {
    let n = 1;
    while (n < a.length + b.length)
        n *= 2;
    const fa = Array.from({ length: n }, (_, i) => new Complex(a[i] ?? 0));
    const fb = Array.from({ length: n }, (_, i) => new Complex(b[i] ?? 0));
    _fft(fa, false);
    _fft(fb, false);
    for (let i = 0; i < n; i++)
        fa[i] = fa[i].mul(fb[i]);
    _fft(fa, true);
    const result = [];
    for (let i = 0; i < a.length + b.length - 1; i++) {
        result.push(Math.round(fa[i].re));
    }
    return result;
}
/**
 * 莫队算法（离线区间查询）
 * 时间复杂度: O((n + q) √n · f)，其中 f 为单次添加/删除代价
 */
function moAlgorithm(arr, queries, process) {
    const n = arr.length;
    const block = Math.floor(Math.sqrt(n)) + 1;
    queries.sort((a, b) => {
        const ba = Math.floor(a.l / block);
        const bb = Math.floor(b.l / block);
        if (ba !== bb)
            return ba - bb;
        return (ba & 1) ? b.r - a.r : a.r - b.r;
    });
    const ans = new Array(queries.length);
    // 以下为框架示例：实际计数逻辑由调用方通过回调扩展
    // 这里提供一个频率统计模板
    const freq = new Map();
    let curL = 0, curR = -1;
    let distinct = 0;
    function add(pos) {
        const x = arr[pos];
        const c = freq.get(x) ?? 0;
        if (c === 0)
            distinct++;
        freq.set(x, c + 1);
    }
    function remove(pos) {
        const x = arr[pos];
        const c = freq.get(x) ?? 0;
        if (c === 1) {
            freq.delete(x);
            distinct--;
        }
        else
            freq.set(x, c - 1);
    }
    for (const q of queries) {
        while (curL > q.l) {
            curL--;
            add(curL);
        }
        while (curR < q.r) {
            curR++;
            add(curR);
        }
        while (curL < q.l) {
            remove(curL);
            curL++;
        }
        while (curR > q.r) {
            remove(curR);
            curR--;
        }
        ans[q.idx] = distinct;
    }
    for (let i = 0; i < queries.length; i++) {
        process(ans, queries[i]);
    }
}
// ==================== 舞蹈链 (Exact Cover / DLX) ====================
class DLXNode {
    constructor(col = null, row = -1) {
        this.col = col;
        this.row = row;
        this.l = this.r = this.u = this.d = this;
    }
}
exports.DLXNode = DLXNode;
class DLXColumn extends DLXNode {
    constructor(name) {
        super(null, -1);
        this.name = name;
        this.size = 0;
        this.col = this;
    }
}
exports.DLXColumn = DLXColumn;
class DancingLinks {
    constructor(colNames) {
        this.solution = [];
        this.solutions = [];
        this.header = new DLXNode();
        this.columns = colNames.map(name => new DLXColumn(name));
        for (let i = 0; i < this.columns.length; i++) {
            this.columns[i].r = this.columns[(i + 1) % this.columns.length];
            this.columns[i].l = this.columns[(i - 1 + this.columns.length) % this.columns.length];
        }
        this.header.r = this.columns[0];
        this.header.l = this.columns[this.columns.length - 1];
        this.columns[0].l = this.header;
        this.columns[this.columns.length - 1].r = this.header;
    }
    addRow(rowIdx, colIndices) {
        let first = null;
        for (const ci of colIndices) {
            const col = this.columns[ci];
            const node = new DLXNode(col, rowIdx);
            node.u = col.u;
            node.d = col;
            col.u.d = node;
            col.u = node;
            if (first) {
                node.l = first.l;
                node.r = first;
                first.l.r = node;
                first.l = node;
            }
            else {
                first = node;
            }
            col.size++;
        }
    }
    cover(c) {
        c.r.l = c.l;
        c.l.r = c.r;
        for (let row = c.d; row !== c; row = row.d) {
            for (let node = row.r; node !== row; node = node.r) {
                node.d.u = node.u;
                node.u.d = node.d;
                node.col.size--;
            }
        }
    }
    uncover(c) {
        for (let row = c.u; row !== c; row = row.u) {
            for (let node = row.l; node !== row; node = node.l) {
                node.col.size++;
                node.d.u = node;
                node.u.d = node;
            }
        }
        c.r.l = c;
        c.l.r = c;
    }
    search(k, maxSolutions) {
        if (this.solutions.length >= maxSolutions)
            return;
        if (this.header.r === this.header) {
            this.solutions.push(this.solution.map(n => n.row));
            return;
        }
        let c = this.header.r.col;
        let minSize = c.size;
        for (let col = this.header.r; col !== this.header; col = col.r) {
            if (col.col.size < minSize) {
                minSize = col.col.size;
                c = col.col;
            }
        }
        if (minSize === 0)
            return;
        this.cover(c);
        for (let row = c.d; row !== c; row = row.d) {
            this.solution.push(row);
            for (let node = row.r; node !== row; node = node.r)
                this.cover(node.col);
            this.search(k + 1, maxSolutions);
            this.solution.pop();
            for (let node = row.l; node !== row; node = node.l)
                this.uncover(node.col);
        }
        this.uncover(c);
    }
    solve(maxSolutions = 1) {
        this.solutions = [];
        this.search(0, maxSolutions);
        return this.solutions;
    }
}
exports.DancingLinks = DancingLinks;
// ==================== 模拟退火 ====================
/**
 * 模拟退火（求函数最小值）
 * 时间复杂度: O(iterations)
 */
function simulatedAnnealing(initial, neighbor, energy, iterations = 100000, initialTemp = 1.0, coolingRate = 0.9999) {
    let current = initial;
    let currentEnergy = energy(current);
    let best = current;
    let bestEnergy = currentEnergy;
    let temp = initialTemp;
    for (let i = 0; i < iterations; i++) {
        const next = neighbor(current);
        const nextEnergy = energy(next);
        const delta = nextEnergy - currentEnergy;
        if (delta < 0 || Math.random() < Math.exp(-delta / temp)) {
            current = next;
            currentEnergy = nextEnergy;
            if (currentEnergy < bestEnergy) {
                best = current;
                bestEnergy = currentEnergy;
            }
        }
        temp *= coolingRate;
    }
    return { state: best, energy: bestEnergy };
}
function runAdvancedTests() {
    (0, utils_1.runTests)("Advanced", {
        "multiplyPolynomials": () => {
            const a = [1, 2, 3];
            const b = [4, 5];
            (0, utils_1.assertArrayEq)(multiplyPolynomials(a, b), [4, 13, 22, 15]);
        },
        "DancingLinks": () => {
            const dlx = new DancingLinks(["A", "B", "C"]);
            dlx.addRow(0, [0, 2]);
            dlx.addRow(1, [1]);
            dlx.addRow(2, [0, 1]);
            const sols = dlx.solve(10);
            (0, utils_1.assertTrue)(sols.length > 0);
        },
        "simulatedAnnealing": () => {
            const res = simulatedAnnealing(10, (x) => x + (Math.random() - 0.5) * 2, (x) => (x - 3) * (x - 3), 50000, 10, 0.9995);
            (0, utils_1.assertTrue)(Math.abs(res.state - 3) < 0.5);
        },
    });
}
//# sourceMappingURL=advanced.js.map