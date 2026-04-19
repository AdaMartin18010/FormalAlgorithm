/**
 * search.js - JavaScript搜索算法实现
 * 包含：二分搜索、下界、上界
 */

class Search {
    /**
     * 二分搜索
     * @param {number[]} arr - 已排序数组
     * @param {number} target - 目标值
     * @returns {number} 目标索引，未找到返回 -1
     */
    static binarySearch(arr, target) {
        let left = 0, right = arr.length - 1;
        while (left <= right) {
            const mid = Math.floor((left + right) / 2);
            if (arr[mid] === target) return mid;
            else if (arr[mid] < target) left = mid + 1;
            else right = mid - 1;
        }
        return -1;
    }

    /**
     * 下界：第一个 >= target 的索引
     */
    static lowerBound(arr, target) {
        let left = 0, right = arr.length;
        while (left < right) {
            const mid = Math.floor((left + right) / 2);
            if (arr[mid] < target) left = mid + 1;
            else right = mid;
        }
        return left;
    }

    /**
     * 上界：第一个 > target 的索引
     */
    static upperBound(arr, target) {
        let left = 0, right = arr.length;
        while (left < right) {
            const mid = Math.floor((left + right) / 2);
            if (arr[mid] <= target) left = mid + 1;
            else right = mid;
        }
        return left;
    }
}

// 简单测试
function assertEq(name, expected, actual) {
    if (expected !== actual) {
        throw new Error(`FAIL ${name}: expected ${expected}, got ${actual}`);
    }
}

function runTests() {
    const arr = [1, 3, 5, 7, 9];
    assertEq("BS found", 2, Search.binarySearch(arr, 5));
    assertEq("BS not found", -1, Search.binarySearch(arr, 4));
    assertEq("BS empty", -1, Search.binarySearch([], 1));
    assertEq("LowerBound", 2, Search.lowerBound(arr, 5));
    assertEq("UpperBound", 4, Search.upperBound([1, 3, 5, 5, 7, 9], 5));
    console.log("All search tests passed!");
}

runTests();

module.exports = { Search };
