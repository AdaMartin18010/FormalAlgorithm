/**
 * 树算法集合
 * 包含 LCA、树链剖分、重心分解、笛卡尔树
 */
export type TreeAdj = number[][];
export declare class LCA {
    private adj;
    private n;
    private log;
    private up;
    private depth;
    constructor(adj: TreeAdj, root?: number);
    private dfs;
    /** O(log n) */
    query(u: number, v: number): number;
}
export declare class HeavyLightDecomposition {
    private adj;
    private parent;
    private depth;
    private heavy;
    private head;
    private pos;
    private curPos;
    constructor(adj: TreeAdj, root?: number);
    private dfs;
    private decompose;
    getPosition(u: number): number;
    getHead(u: number): number;
    getDepth(u: number): number;
}
export declare function centroidDecomposition(adj: TreeAdj): number[];
/**
 * 构建小根笛卡尔树（堆性质 + 中序遍历为原序列）
 * 时间复杂度: O(n)
 */
export declare function cartesianTree(arr: number[]): {
    parent: number[];
    root: number;
};
export declare function runTreeTests(): void;
//# sourceMappingURL=tree.d.ts.map