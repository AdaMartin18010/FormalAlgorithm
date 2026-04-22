"use strict";
/**
 * 排序算法集合
 * 所有算法均基于原地或近原地实现，附带严格的类型约束与复杂度标注
 */
Object.defineProperty(exports, "__esModule", { value: true });
exports.bubbleSort = bubbleSort;
exports.selectionSort = selectionSort;
exports.insertionSort = insertionSort;
exports.shellSort = shellSort;
exports.mergeSort = mergeSort;
exports.quickSort = quickSort;
exports.heapSort = heapSort;
exports.countingSort = countingSort;
exports.bucketSort = bucketSort;
exports.radixSort = radixSort;
exports.runSortingTests = runSortingTests;
const utils_1 = require("./utils");
/**
 * 冒泡排序
 * 时间复杂度: O(n²) 最坏/平均, O(n) 最好
 * 空间复杂度: O(1)
 * 稳定性: 稳定
 */
function bubbleSort(arr, compare = utils_1.defaultCompare) {
    const n = arr.length;
    for (let i = 0; i < n - 1; i++) {
        let swapped = false;
        for (let j = 0; j < n - 1 - i; j++) {
            if (compare(arr[j], arr[j + 1]) > 0) {
                (0, utils_1.swap)(arr, j, j + 1);
                swapped = true;
            }
        }
        if (!swapped)
            break;
    }
    return arr;
}
/**
 * 选择排序
 * 时间复杂度: O(n²)
 * 空间复杂度: O(1)
 * 稳定性: 不稳定
 */
function selectionSort(arr, compare = utils_1.defaultCompare) {
    const n = arr.length;
    for (let i = 0; i < n - 1; i++) {
        let minIdx = i;
        for (let j = i + 1; j < n; j++) {
            if (compare(arr[j], arr[minIdx]) < 0) {
                minIdx = j;
            }
        }
        if (minIdx !== i)
            (0, utils_1.swap)(arr, i, minIdx);
    }
    return arr;
}
/**
 * 插入排序
 * 时间复杂度: O(n²) 最坏/平均, O(n) 最好
 * 空间复杂度: O(1)
 * 稳定性: 稳定
 */
function insertionSort(arr, compare = utils_1.defaultCompare) {
    const n = arr.length;
    for (let i = 1; i < n; i++) {
        const key = arr[i];
        let j = i - 1;
        while (j >= 0 && compare(arr[j], key) > 0) {
            arr[j + 1] = arr[j];
            j--;
        }
        arr[j + 1] = key;
    }
    return arr;
}
/**
 * 希尔排序
 * 时间复杂度: O(n log n) ~ O(n²) 取决于增量序列
 * 空间复杂度: O(1)
 * 稳定性: 不稳定
 */
function shellSort(arr, compare = utils_1.defaultCompare) {
    const n = arr.length;
    let gap = Math.floor(n / 2);
    while (gap > 0) {
        for (let i = gap; i < n; i++) {
            const temp = arr[i];
            let j = i;
            while (j >= gap && compare(arr[j - gap], temp) > 0) {
                arr[j] = arr[j - gap];
                j -= gap;
            }
            arr[j] = temp;
        }
        gap = Math.floor(gap / 2);
    }
    return arr;
}
/**
 * 归并排序
 * 时间复杂度: O(n log n)
 * 空间复杂度: O(n)
 * 稳定性: 稳定
 */
function mergeSort(arr, compare = utils_1.defaultCompare) {
    if (arr.length <= 1)
        return arr;
    const mid = Math.floor(arr.length / 2);
    const left = mergeSort(arr.slice(0, mid), compare);
    const right = mergeSort(arr.slice(mid), compare);
    return merge(left, right, compare);
}
function merge(left, right, compare) {
    const result = [];
    let i = 0, j = 0;
    while (i < left.length && j < right.length) {
        if (compare(left[i], right[j]) <= 0) {
            result.push(left[i++]);
        }
        else {
            result.push(right[j++]);
        }
    }
    while (i < left.length)
        result.push(left[i++]);
    while (j < right.length)
        result.push(right[j++]);
    return result;
}
/**
 * 快速排序（原地双指针）
 * 时间复杂度: O(n log n) 平均, O(n²) 最坏
 * 空间复杂度: O(log n) 栈空间
 * 稳定性: 不稳定
 */
function quickSort(arr, compare = utils_1.defaultCompare) {
    _quickSort(arr, 0, arr.length - 1, compare);
    return arr;
}
function _quickSort(arr, low, high, compare) {
    if (low < high) {
        const pi = partition(arr, low, high, compare);
        _quickSort(arr, low, pi - 1, compare);
        _quickSort(arr, pi + 1, high, compare);
    }
}
function partition(arr, low, high, compare) {
    const pivot = arr[high];
    let i = low - 1;
    for (let j = low; j < high; j++) {
        if (compare(arr[j], pivot) <= 0) {
            i++;
            (0, utils_1.swap)(arr, i, j);
        }
    }
    (0, utils_1.swap)(arr, i + 1, high);
    return i + 1;
}
/**
 * 堆排序
 * 时间复杂度: O(n log n)
 * 空间复杂度: O(1)
 * 稳定性: 不稳定
 */
function heapSort(arr, compare = utils_1.defaultCompare) {
    const n = arr.length;
    for (let i = Math.floor(n / 2) - 1; i >= 0; i--) {
        heapify(arr, n, i, compare);
    }
    for (let i = n - 1; i > 0; i--) {
        (0, utils_1.swap)(arr, 0, i);
        heapify(arr, i, 0, compare);
    }
    return arr;
}
function heapify(arr, n, i, compare) {
    let largest = i;
    const left = 2 * i + 1;
    const right = 2 * i + 2;
    if (left < n && compare(arr[left], arr[largest]) > 0)
        largest = left;
    if (right < n && compare(arr[right], arr[largest]) > 0)
        largest = right;
    if (largest !== i) {
        (0, utils_1.swap)(arr, i, largest);
        heapify(arr, n, largest, compare);
    }
}
/**
 * 计数排序（仅适用于非负整数）
 * 时间复杂度: O(n + k)
 * 空间复杂度: O(k)
 * 稳定性: 稳定
 */
function countingSort(arr) {
    if (arr.length === 0)
        return arr;
    const max = Math.max(...arr);
    const min = Math.min(...arr);
    const range = max - min + 1;
    const count = new Array(range).fill(0);
    const output = new Array(arr.length);
    for (const num of arr)
        count[num - min]++;
    for (let i = 1; i < range; i++)
        count[i] += count[i - 1];
    for (let i = arr.length - 1; i >= 0; i--) {
        output[count[arr[i] - min] - 1] = arr[i];
        count[arr[i] - min]--;
    }
    return output;
}
/**
 * 桶排序（适用于均匀分布数据）
 * 时间复杂度: O(n) 平均, O(n²) 最坏
 * 空间复杂度: O(n + k)
 * 稳定性: 稳定（若底层排序稳定）
 */
function bucketSort(arr, bucketCount = 10) {
    if (arr.length === 0)
        return arr;
    const min = Math.min(...arr);
    const max = Math.max(...arr);
    const buckets = Array.from({ length: bucketCount }, () => []);
    for (const num of arr) {
        const idx = Math.floor(((num - min) / (max - min + 1e-9)) * bucketCount);
        buckets[Math.min(idx, bucketCount - 1)].push(num);
    }
    let idx = 0;
    for (const bucket of buckets) {
        insertionSort(bucket);
        for (const num of bucket)
            arr[idx++] = num;
    }
    return arr;
}
/**
 * 基数排序（LSD，仅适用于非负整数）
 * 时间复杂度: O(d(n + k))
 * 空间复杂度: O(n + k)
 * 稳定性: 稳定
 */
function radixSort(arr) {
    if (arr.length === 0)
        return arr;
    const max = Math.max(...arr);
    let exp = 1;
    while (Math.floor(max / exp) > 0) {
        countingSortByDigit(arr, exp);
        exp *= 10;
    }
    return arr;
}
function countingSortByDigit(arr, exp) {
    const n = arr.length;
    const output = new Array(n);
    const count = new Array(10).fill(0);
    for (let i = 0; i < n; i++) {
        const digit = Math.floor(arr[i] / exp) % 10;
        count[digit]++;
    }
    for (let i = 1; i < 10; i++)
        count[i] += count[i - 1];
    for (let i = n - 1; i >= 0; i--) {
        const digit = Math.floor(arr[i] / exp) % 10;
        output[count[digit] - 1] = arr[i];
        count[digit]--;
    }
    for (let i = 0; i < n; i++)
        arr[i] = output[i];
}
function runSortingTests() {
    (0, utils_1.runTests)("Sorting", {
        "bubbleSort basic": () => {
            (0, utils_1.assertArrayEq)(bubbleSort([3, 1, 4, 1, 5]), [1, 1, 3, 4, 5]);
        },
        "selectionSort basic": () => {
            (0, utils_1.assertArrayEq)(selectionSort([5, 2, 8, 1]), [1, 2, 5, 8]);
        },
        "insertionSort basic": () => {
            (0, utils_1.assertArrayEq)(insertionSort([9, 3, 7, 4]), [3, 4, 7, 9]);
        },
        "shellSort basic": () => {
            (0, utils_1.assertArrayEq)(shellSort([64, 34, 25, 12, 22]), [12, 22, 25, 34, 64]);
        },
        "mergeSort basic": () => {
            (0, utils_1.assertArrayEq)(mergeSort([38, 27, 43, 3, 9, 82, 10]), [3, 9, 10, 27, 38, 43, 82]);
        },
        "quickSort basic": () => {
            (0, utils_1.assertArrayEq)(quickSort([10, 7, 8, 9, 1, 5]), [1, 5, 7, 8, 9, 10]);
        },
        "heapSort basic": () => {
            (0, utils_1.assertArrayEq)(heapSort([12, 11, 13, 5, 6, 7]), [5, 6, 7, 11, 12, 13]);
        },
        "countingSort basic": () => {
            (0, utils_1.assertArrayEq)(countingSort([4, 2, 2, 8, 3, 3, 1]), [1, 2, 2, 3, 3, 4, 8]);
        },
        "bucketSort basic": () => {
            (0, utils_1.assertArrayEq)(bucketSort([0.42, 0.32, 0.33, 0.52, 0.37, 0.47, 0.51]), [0.32, 0.33, 0.37, 0.42, 0.47, 0.51, 0.52]);
        },
        "radixSort basic": () => {
            (0, utils_1.assertArrayEq)(radixSort([170, 45, 75, 90, 802, 24, 2, 66]), [2, 24, 45, 66, 75, 90, 170, 802]);
        },
        "empty array": () => {
            (0, utils_1.assertArrayEq)(quickSort([]), []);
            (0, utils_1.assertArrayEq)(mergeSort([]), []);
        },
        "single element": () => {
            (0, utils_1.assertArrayEq)(quickSort([42]), [42]);
        },
        "already sorted": () => {
            (0, utils_1.assertArrayEq)(quickSort([1, 2, 3, 4, 5]), [1, 2, 3, 4, 5]);
        },
        "reverse sorted": () => {
            (0, utils_1.assertArrayEq)(quickSort([5, 4, 3, 2, 1]), [1, 2, 3, 4, 5]);
        },
        "custom compare": () => {
            (0, utils_1.assertArrayEq)(quickSort([3, 1, 4], (a, b) => b - a), [4, 3, 1]);
        },
    });
}
//# sourceMappingURL=sorting.js.map