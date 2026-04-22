/**
 * 排序算法集合
 * 所有算法均基于原地或近原地实现，附带严格的类型约束与复杂度标注
 */
import { CompareFn } from "./utils";
/**
 * 冒泡排序
 * 时间复杂度: O(n²) 最坏/平均, O(n) 最好
 * 空间复杂度: O(1)
 * 稳定性: 稳定
 */
export declare function bubbleSort<T>(arr: T[], compare?: CompareFn<T>): T[];
/**
 * 选择排序
 * 时间复杂度: O(n²)
 * 空间复杂度: O(1)
 * 稳定性: 不稳定
 */
export declare function selectionSort<T>(arr: T[], compare?: CompareFn<T>): T[];
/**
 * 插入排序
 * 时间复杂度: O(n²) 最坏/平均, O(n) 最好
 * 空间复杂度: O(1)
 * 稳定性: 稳定
 */
export declare function insertionSort<T>(arr: T[], compare?: CompareFn<T>): T[];
/**
 * 希尔排序
 * 时间复杂度: O(n log n) ~ O(n²) 取决于增量序列
 * 空间复杂度: O(1)
 * 稳定性: 不稳定
 */
export declare function shellSort<T>(arr: T[], compare?: CompareFn<T>): T[];
/**
 * 归并排序
 * 时间复杂度: O(n log n)
 * 空间复杂度: O(n)
 * 稳定性: 稳定
 */
export declare function mergeSort<T>(arr: T[], compare?: CompareFn<T>): T[];
/**
 * 快速排序（原地双指针）
 * 时间复杂度: O(n log n) 平均, O(n²) 最坏
 * 空间复杂度: O(log n) 栈空间
 * 稳定性: 不稳定
 */
export declare function quickSort<T>(arr: T[], compare?: CompareFn<T>): T[];
/**
 * 堆排序
 * 时间复杂度: O(n log n)
 * 空间复杂度: O(1)
 * 稳定性: 不稳定
 */
export declare function heapSort<T>(arr: T[], compare?: CompareFn<T>): T[];
/**
 * 计数排序（仅适用于非负整数）
 * 时间复杂度: O(n + k)
 * 空间复杂度: O(k)
 * 稳定性: 稳定
 */
export declare function countingSort(arr: number[]): number[];
/**
 * 桶排序（适用于均匀分布数据）
 * 时间复杂度: O(n) 平均, O(n²) 最坏
 * 空间复杂度: O(n + k)
 * 稳定性: 稳定（若底层排序稳定）
 */
export declare function bucketSort(arr: number[], bucketCount?: number): number[];
/**
 * 基数排序（LSD，仅适用于非负整数）
 * 时间复杂度: O(d(n + k))
 * 空间复杂度: O(n + k)
 * 稳定性: 稳定
 */
export declare function radixSort(arr: number[]): number[];
export declare function runSortingTests(): void;
//# sourceMappingURL=sorting.d.ts.map