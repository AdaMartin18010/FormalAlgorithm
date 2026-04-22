/**
 * 搜索算法集合
 */

import { CompareFn, defaultCompare, runTests, assertEq, assertTrue } from "./utils";

/**
 * 线性搜索
 * 时间复杂度: O(n)
 * 空间复杂度: O(1)
 */
export function linearSearch<T>(arr: T[], target: T, compare: CompareFn<T> = defaultCompare): number {
  for (let i = 0; i < arr.length; i++) {
    if (compare(arr[i], target) === 0) return i;
  }
  return -1;
}

/**
 * 二分搜索（要求数组已排序）
 * 时间复杂度: O(log n)
 * 空间复杂度: O(1)
 */
export function binarySearch<T>(arr: T[], target: T, compare: CompareFn<T> = defaultCompare): number {
  let left = 0, right = arr.length - 1;
  while (left <= right) {
    const mid = Math.floor((left + right) / 2);
    const cmp = compare(arr[mid], target);
    if (cmp === 0) return mid;
    if (cmp < 0) left = mid + 1;
    else right = mid - 1;
  }
  return -1;
}

/**
 * 二分搜索下界（第一个 >= target 的位置）
 * 时间复杂度: O(log n)
 */
export function lowerBound<T>(arr: T[], target: T, compare: CompareFn<T> = defaultCompare): number {
  let left = 0, right = arr.length;
  while (left < right) {
    const mid = Math.floor((left + right) / 2);
    if (compare(arr[mid], target) < 0) left = mid + 1;
    else right = mid;
  }
  return left;
}

/**
 * 二分搜索上界（第一个 > target 的位置）
 * 时间复杂度: O(log n)
 */
export function upperBound<T>(arr: T[], target: T, compare: CompareFn<T> = defaultCompare): number {
  let left = 0, right = arr.length;
  while (left < right) {
    const mid = Math.floor((left + right) / 2);
    if (compare(arr[mid], target) <= 0) left = mid + 1;
    else right = mid;
  }
  return left;
}

/**
 * 插值搜索（适用于均匀分布的数值数组）
 * 时间复杂度: O(log log n) 平均, O(n) 最坏
 * 空间复杂度: O(1)
 */
export function interpolationSearch(arr: number[], target: number): number {
  let low = 0, high = arr.length - 1;
  while (low <= high && target >= arr[low] && target <= arr[high]) {
    if (low === high) return arr[low] === target ? low : -1;
    const pos = low + Math.floor(((target - arr[low]) / (arr[high] - arr[low])) * (high - low));
    if (arr[pos] === target) return pos;
    if (arr[pos] < target) low = pos + 1;
    else high = pos - 1;
  }
  return -1;
}

/**
 * 三分搜索（求单峰函数极值，离散版本）
 * 时间复杂度: O(log₃ n)
 * 空间复杂度: O(1)
 */
export function ternarySearch<T>(arr: T[], compare: CompareFn<T> = defaultCompare): T {
  if (arr.length === 0) throw new Error("Empty array");
  let left = 0, right = arr.length - 1;
  while (right - left > 2) {
    const m1 = left + Math.floor((right - left) / 3);
    const m2 = right - Math.floor((right - left) / 3);
    if (compare(arr[m1], arr[m2]) < 0) left = m1;
    else right = m2;
  }
  let best = arr[left];
  for (let i = left + 1; i <= right; i++) {
    if (compare(arr[i], best) < 0) best = arr[i];
  }
  return best;
}

export function runSearchTests(): void {
  runTests("Search", {
    "linearSearch found": () => {
      assertEq(linearSearch([4, 2, 5, 1, 3], 5), 2);
    },
    "linearSearch not found": () => {
      assertEq(linearSearch([1, 2, 3], 4), -1);
    },
    "binarySearch found": () => {
      assertEq(binarySearch([1, 2, 3, 4, 5], 4), 3);
    },
    "binarySearch not found": () => {
      assertEq(binarySearch([1, 3, 5], 4), -1);
    },
    "lowerBound": () => {
      assertEq(lowerBound([1, 2, 2, 3, 4], 2), 1);
      assertEq(lowerBound([1, 3, 5], 2), 1);
    },
    "upperBound": () => {
      assertEq(upperBound([1, 2, 2, 3, 4], 2), 3);
      assertEq(upperBound([1, 3, 5], 2), 1);
    },
    "interpolationSearch": () => {
      assertEq(interpolationSearch([10, 20, 30, 40, 50], 30), 2);
      assertEq(interpolationSearch([10, 20, 30], 25), -1);
    },
    "ternarySearch": () => {
      assertEq(ternarySearch([5, 3, 1, 2, 4]), 1);
    },
  });
}
