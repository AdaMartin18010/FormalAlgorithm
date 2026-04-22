/**
 * 高级算法集合
 * 包含 FFT、莫队算法、舞蹈链、模拟退火
 */
export declare class Complex {
    re: number;
    im: number;
    constructor(re: number, im?: number);
    add(other: Complex): Complex;
    sub(other: Complex): Complex;
    mul(other: Complex): Complex;
}
/**
 * 多项式乘法（卷积）
 * 时间复杂度: O(n log n)
 */
export declare function multiplyPolynomials(a: number[], b: number[]): number[];
export type Query = {
    l: number;
    r: number;
    idx: number;
};
/**
 * 莫队算法（离线区间查询）
 * 时间复杂度: O((n + q) √n · f)，其中 f 为单次添加/删除代价
 */
export declare function moAlgorithm(arr: number[], queries: Query[], process: (ans: number[], q: Query) => void): void;
export declare class DLXNode {
    col: DLXColumn | null;
    row: number;
    l: DLXNode;
    r: DLXNode;
    u: DLXNode;
    d: DLXNode;
    constructor(col?: DLXColumn | null, row?: number);
}
export declare class DLXColumn extends DLXNode {
    name: string;
    size: number;
    constructor(name: string);
}
export declare class DancingLinks {
    private header;
    private columns;
    private solution;
    private solutions;
    constructor(colNames: string[]);
    addRow(rowIdx: number, colIndices: number[]): void;
    private cover;
    private uncover;
    private search;
    solve(maxSolutions?: number): number[][];
}
/**
 * 模拟退火（求函数最小值）
 * 时间复杂度: O(iterations)
 */
export declare function simulatedAnnealing<T>(initial: T, neighbor: (current: T) => T, energy: (state: T) => number, iterations?: number, initialTemp?: number, coolingRate?: number): {
    state: T;
    energy: number;
};
export declare function runAdvancedTests(): void;
//# sourceMappingURL=advanced.d.ts.map