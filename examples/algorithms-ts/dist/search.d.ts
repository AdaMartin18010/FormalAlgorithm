/**
 * 搜索算法集合
 */
import { CompareFn } from "./utils";
/**
 * 线性搜索
 * 时间复杂度: O(n)
 * 空间复杂度: O(1)
 */
export declare function linearSearch<T>(arr: T[], target: T, compare?: CompareFn<T>): number;
/**
 * 二分搜索（要求数组已排序）
 * 时间复杂度: O(log n)
 * 空间复杂度: O(1)
 */
export declare function binarySearch<T>(arr: T[], target: T, compare?: CompareFn<T>): number;
/**
 * 二分搜索下界（第一个 >= target 的位置）
 * 时间复杂度: O(log n)
 */
export declare function lowerBound<T>(arr: T[], target: T, compare?: CompareFn<T>): number;
/**
 * 二分搜索上界（第一个 > target 的位置）
 * 时间复杂度: O(log n)
 */
export declare function upperBound<T>(arr: T[], target: T, compare?: CompareFn<T>): number;
/**
 * 插值搜索（适用于均匀分布的数值数组）
 * 时间复杂度: O(log log n) 平均, O(n) 最坏
 * 空间复杂度: O(1)
 */
export declare function interpolationSearch(arr: number[], target: number): number;
/**
 * 三分搜索（求单峰函数极值，离散版本）
 * 时间复杂度: O(log₃ n)
 * 空间复杂度: O(1)
 */
export declare function ternarySearch<T>(arr: T[], compare?: CompareFn<T>): T;
export declare function runSearchTests(): void;
//# sourceMappingURL=search.d.ts.map