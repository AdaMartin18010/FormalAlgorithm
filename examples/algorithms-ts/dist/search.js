"use strict";
/**
 * 搜索算法集合
 */
Object.defineProperty(exports, "__esModule", { value: true });
exports.linearSearch = linearSearch;
exports.binarySearch = binarySearch;
exports.lowerBound = lowerBound;
exports.upperBound = upperBound;
exports.interpolationSearch = interpolationSearch;
exports.ternarySearch = ternarySearch;
exports.runSearchTests = runSearchTests;
const utils_1 = require("./utils");
/**
 * 线性搜索
 * 时间复杂度: O(n)
 * 空间复杂度: O(1)
 */
function linearSearch(arr, target, compare = utils_1.defaultCompare) {
    for (let i = 0; i < arr.length; i++) {
        if (compare(arr[i], target) === 0)
            return i;
    }
    return -1;
}
/**
 * 二分搜索（要求数组已排序）
 * 时间复杂度: O(log n)
 * 空间复杂度: O(1)
 */
function binarySearch(arr, target, compare = utils_1.defaultCompare) {
    let left = 0, right = arr.length - 1;
    while (left <= right) {
        const mid = Math.floor((left + right) / 2);
        const cmp = compare(arr[mid], target);
        if (cmp === 0)
            return mid;
        if (cmp < 0)
            left = mid + 1;
        else
            right = mid - 1;
    }
    return -1;
}
/**
 * 二分搜索下界（第一个 >= target 的位置）
 * 时间复杂度: O(log n)
 */
function lowerBound(arr, target, compare = utils_1.defaultCompare) {
    let left = 0, right = arr.length;
    while (left < right) {
        const mid = Math.floor((left + right) / 2);
        if (compare(arr[mid], target) < 0)
            left = mid + 1;
        else
            right = mid;
    }
    return left;
}
/**
 * 二分搜索上界（第一个 > target 的位置）
 * 时间复杂度: O(log n)
 */
function upperBound(arr, target, compare = utils_1.defaultCompare) {
    let left = 0, right = arr.length;
    while (left < right) {
        const mid = Math.floor((left + right) / 2);
        if (compare(arr[mid], target) <= 0)
            left = mid + 1;
        else
            right = mid;
    }
    return left;
}
/**
 * 插值搜索（适用于均匀分布的数值数组）
 * 时间复杂度: O(log log n) 平均, O(n) 最坏
 * 空间复杂度: O(1)
 */
function interpolationSearch(arr, target) {
    let low = 0, high = arr.length - 1;
    while (low <= high && target >= arr[low] && target <= arr[high]) {
        if (low === high)
            return arr[low] === target ? low : -1;
        const pos = low + Math.floor(((target - arr[low]) / (arr[high] - arr[low])) * (high - low));
        if (arr[pos] === target)
            return pos;
        if (arr[pos] < target)
            low = pos + 1;
        else
            high = pos - 1;
    }
    return -1;
}
/**
 * 三分搜索（求单峰函数极值，离散版本）
 * 时间复杂度: O(log₃ n)
 * 空间复杂度: O(1)
 */
function ternarySearch(arr, compare = utils_1.defaultCompare) {
    if (arr.length === 0)
        throw new Error("Empty array");
    let left = 0, right = arr.length - 1;
    while (right - left > 2) {
        const m1 = left + Math.floor((right - left) / 3);
        const m2 = right - Math.floor((right - left) / 3);
        if (compare(arr[m1], arr[m2]) < 0)
            left = m1;
        else
            right = m2;
    }
    let best = arr[left];
    for (let i = left + 1; i <= right; i++) {
        if (compare(arr[i], best) < 0)
            best = arr[i];
    }
    return best;
}
function runSearchTests() {
    (0, utils_1.runTests)("Search", {
        "linearSearch found": () => {
            (0, utils_1.assertEq)(linearSearch([4, 2, 5, 1, 3], 5), 2);
        },
        "linearSearch not found": () => {
            (0, utils_1.assertEq)(linearSearch([1, 2, 3], 4), -1);
        },
        "binarySearch found": () => {
            (0, utils_1.assertEq)(binarySearch([1, 2, 3, 4, 5], 4), 3);
        },
        "binarySearch not found": () => {
            (0, utils_1.assertEq)(binarySearch([1, 3, 5], 4), -1);
        },
        "lowerBound": () => {
            (0, utils_1.assertEq)(lowerBound([1, 2, 2, 3, 4], 2), 1);
            (0, utils_1.assertEq)(lowerBound([1, 3, 5], 2), 1);
        },
        "upperBound": () => {
            (0, utils_1.assertEq)(upperBound([1, 2, 2, 3, 4], 2), 3);
            (0, utils_1.assertEq)(upperBound([1, 3, 5], 2), 1);
        },
        "interpolationSearch": () => {
            (0, utils_1.assertEq)(interpolationSearch([10, 20, 30, 40, 50], 30), 2);
            (0, utils_1.assertEq)(interpolationSearch([10, 20, 30], 25), -1);
        },
        "ternarySearch": () => {
            (0, utils_1.assertEq)(ternarySearch([5, 3, 1, 2, 4]), 1);
        },
    });
}
//# sourceMappingURL=search.js.map