/**
 * sorting.js - JavaScript排序算法实现
 * 包含：快速排序、归并排序、堆排序、计数排序、希尔排序
 */

class Sorting {
    /**
     * 快速排序 - 原地排序
     * 时间复杂度: 平均 O(n log n), 最坏 O(n²)
     * @param {number[]} arr - 待排序数组
     * @returns {number[]} 排序后的数组（原地修改）
     */
    static quickSort(arr, low = 0, high = arr.length - 1) {
        if (low < high) {
            const pivotIndex = this.partition(arr, low, high);
            this.quickSort(arr, low, pivotIndex - 1);
            this.quickSort(arr, pivotIndex + 1, high);
        }
        return arr;
    }

    static partition(arr, low, high) {
        // 三数取中
        const mid = Math.floor((low + high) / 2);
        if (arr[mid] < arr[low]) [arr[low], arr[mid]] = [arr[mid], arr[low]];
        if (arr[high] < arr[low]) [arr[low], arr[high]] = [arr[high], arr[low]];
        if (arr[high] < arr[mid]) [arr[mid], arr[high]] = [arr[high], arr[mid]];

        [arr[mid], arr[high - 1]] = [arr[high - 1], arr[mid]];
        const pivot = arr[high - 1];

        let i = low;
        let j = high - 1;

        while (true) {
            while (arr[++i] < pivot) {}
            while (arr[--j] > pivot) {}
            if (i >= j) break;
            [arr[i], arr[j]] = [arr[j], arr[i]];
        }

        [arr[i], arr[high - 1]] = [arr[high - 1], arr[i]];
        return i;
    }

    /**
     * 归并排序
     * 时间复杂度: O(n log n)
     * 空间复杂度: O(n)
     * @param {number[]} arr - 待排序数组
     * @returns {number[]} 新数组（不修改原数组）
     */
    static mergeSort(arr) {
        if (arr.length <= 1) return arr;

        const mid = Math.floor(arr.length / 2);
        const left = this.mergeSort(arr.slice(0, mid));
        const right = this.mergeSort(arr.slice(mid));

        return this.merge(left, right);
    }

    static merge(left, right) {
        const result = [];
        let i = 0, j = 0;

        while (i < left.length && j < right.length) {
            if (left[i] <= right[j]) {
                result.push(left[i++]);
            } else {
                result.push(right[j++]);
            }
        }

        return result.concat(left.slice(i), right.slice(j));
    }

    /**
     * 堆排序
     * 时间复杂度: O(n log n)
     * 空间复杂度: O(1)
     * @param {number[]} arr - 待排序数组
     * @returns {number[]} 排序后的数组（原地修改）
     */
    static heapSort(arr) {
        const n = arr.length;
        if (n <= 1) return arr;

        // 建堆
        for (let i = Math.floor(n / 2) - 1; i >= 0; i--) {
            this.heapify(arr, n, i);
        }

        // 提取元素
        for (let i = n - 1; i > 0; i--) {
            [arr[0], arr[i]] = [arr[i], arr[0]];
            this.heapify(arr, i, 0);
        }

        return arr;
    }

    static heapify(arr, heapSize, root) {
        let largest = root;
        const left = 2 * root + 1;
        const right = 2 * root + 2;

        if (left < heapSize && arr[left] > arr[largest]) {
            largest = left;
        }
        if (right < heapSize && arr[right] > arr[largest]) {
            largest = right;
        }

        if (largest !== root) {
            [arr[root], arr[largest]] = [arr[largest], arr[root]];
            this.heapify(arr, heapSize, largest);
        }
    }

    /**
     * 希尔排序
     * 时间复杂度: O(n log n) ~ O(n²)
     * @param {number[]} arr - 待排序数组
     * @returns {number[]} 排序后的数组（原地修改）
     */
    static shellSort(arr) {
        const n = arr.length;
        for (let gap = Math.floor(n / 2); gap > 0; gap = Math.floor(gap / 2)) {
            for (let i = gap; i < n; i++) {
                const temp = arr[i];
                let j = i;
                while (j >= gap && arr[j - gap] > temp) {
                    arr[j] = arr[j - gap];
                    j -= gap;
                }
                arr[j] = temp;
            }
        }
        return arr;
    }

    /**
     * 计数排序
     * 时间复杂度: O(n + k), k为数值范围
     * @param {number[]} arr - 待排序数组（非负整数）
     * @param {number} maxVal - 数组中的最大值
     * @returns {number[]} 新数组
     */
    static countingSort(arr, maxVal) {
        const count = new Array(maxVal + 1).fill(0);
        const output = new Array(arr.length);

        for (const num of arr) {
            count[num]++;
        }

        for (let i = 1; i <= maxVal; i++) {
            count[i] += count[i - 1];
        }

        for (let i = arr.length - 1; i >= 0; i--) {
            output[count[arr[i]] - 1] = arr[i];
            count[arr[i]]--;
        }

        return output;
    }

    /**
     * 基数排序
     * 时间复杂度: O(d * (n + k)), d为数字位数
     * @param {number[]} arr - 待排序数组（非负整数）
     * @returns {number[]} 新数组
     */
    static radixSort(arr) {
        if (arr.length === 0) return arr;

        const maxVal = Math.max(...arr);
        let exp = 1;

        while (Math.floor(maxVal / exp) > 0) {
            this.countingSortForRadix(arr, exp);
            exp *= 10;
        }

        return arr;
    }

    static countingSortForRadix(arr, exp) {
        const n = arr.length;
        const output = new Array(n);
        const count = new Array(10).fill(0);

        for (let i = 0; i < n; i++) {
            const digit = Math.floor(arr[i] / exp) % 10;
            count[digit]++;
        }

        for (let i = 1; i < 10; i++) {
            count[i] += count[i - 1];
        }

        for (let i = n - 1; i >= 0; i--) {
            const digit = Math.floor(arr[i] / exp) % 10;
            output[count[digit] - 1] = arr[i];
            count[digit]--;
        }

        for (let i = 0; i < n; i++) {
            arr[i] = output[i];
        }
    }

    /**
     * 插入排序（适合小数组）
     * @param {number[]} arr - 待排序数组
     * @returns {number[]} 排序后的数组
     */
    static insertionSort(arr) {
        for (let i = 1; i < arr.length; i++) {
            const key = arr[i];
            let j = i - 1;
            while (j >= 0 && arr[j] > key) {
                arr[j + 1] = arr[j];
                j--;
            }
            arr[j + 1] = key;
        }
        return arr;
    }

    /**
     * TimSort（JavaScript内置）
     * @param {number[]} arr - 待排序数组
     * @returns {number[]} 排序后的数组
     */
    static timSort(arr) {
        return arr.slice().sort((a, b) => a - b);
    }
}

// 辅助函数
function printArray(arr, label = '') {
    console.log(`${label}: [${arr.join(', ')}]`);
}

// 测试
if (require.main === module) {
    console.log('=== JavaScript排序算法演示 ===\n');

    // 快速排序
    let arr1 = [64, 34, 25, 12, 22, 11, 90];
    printArray(arr1, '快速排序前');
    Sorting.quickSort(arr1);
    printArray(arr1, '快速排序后');

    // 归并排序
    let arr2 = [38, 27, 43, 3, 9, 82, 10];
    printArray(arr2, '\n归并排序前');
    const sorted2 = Sorting.mergeSort(arr2);
    printArray(sorted2, '归并排序后');

    // 堆排序
    let arr3 = [12, 11, 13, 5, 6, 7];
    printArray(arr3, '\n堆排序前');
    Sorting.heapSort(arr3);
    printArray(arr3, '堆排序后');

    // 希尔排序
    let arr4 = [8, 3, 5, 4, 7, 6, 2, 1];
    printArray(arr4, '\n希尔排序前');
    Sorting.shellSort(arr4);
    printArray(arr4, '希尔排序后');

    // 计数排序
    const arr5 = [4, 2, 2, 8, 3, 3, 1];
    printArray(arr5, '\n计数排序前');
    const sorted5 = Sorting.countingSort(arr5, 8);
    printArray(sorted5, '计数排序后');

    // 基数排序
    let arr6 = [170, 45, 75, 90, 802, 24, 2, 66];
    printArray(arr6, '\n基数排序前');
    Sorting.radixSort(arr6);
    printArray(arr6, '基数排序后');
}

module.exports = Sorting;
