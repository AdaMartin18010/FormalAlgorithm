/**
 * sorting.cpp - C++排序算法实现
 * 包含：快速排序、归并排序、堆排序、计数排序、希尔排序
 */

#include <iostream>
#include <vector>
#include <algorithm>
#include <random>
#include <chrono>

namespace sorting {

/**
 * 快速排序 - 原地排序
 * 时间复杂度: 平均 O(n log n), 最坏 O(n²)
 */
template<typename T>
void quickSort(std::vector<T>& arr, int low, int high) {
    if (low < high) {
        // 三数取中法选择枢轴
        int mid = low + (high - low) / 2;
        if (arr[mid] < arr[low]) std::swap(arr[low], arr[mid]);
        if (arr[high] < arr[low]) std::swap(arr[low], arr[high]);
        if (arr[high] < arr[mid]) std::swap(arr[mid], arr[high]);
        
        std::swap(arr[mid], arr[high - 1]);
        T pivot = arr[high - 1];
        
        int i = low;
        int j = high - 1;
        
        while (true) {
            while (arr[++i] < pivot) {}
            while (arr[--j] > pivot) {}
            if (i >= j) break;
            std::swap(arr[i], arr[j]);
        }
        
        std::swap(arr[i], arr[high - 1]);
        
        quickSort(arr, low, i - 1);
        quickSort(arr, i + 1, high);
    }
}

template<typename T>
void quickSort(std::vector<T>& arr) {
    if (arr.size() > 1) {
        quickSort(arr, 0, static_cast<int>(arr.size()) - 1);
    }
}

/**
 * 归并排序
 * 时间复杂度: O(n log n)
 * 空间复杂度: O(n)
 */
template<typename T>
void merge(std::vector<T>& arr, std::vector<T>& temp, int left, int mid, int right) {
    int i = left;      // 左子数组索引
    int j = mid + 1;   // 右子数组索引
    int k = left;      // 临时数组索引
    
    while (i <= mid && j <= right) {
        if (arr[i] <= arr[j]) {
            temp[k++] = arr[i++];
        } else {
            temp[k++] = arr[j++];
        }
    }
    
    while (i <= mid) temp[k++] = arr[i++];
    while (j <= right) temp[k++] = arr[j++];
    
    for (i = left; i <= right; i++) {
        arr[i] = temp[i];
    }
}

template<typename T>
void mergeSortHelper(std::vector<T>& arr, std::vector<T>& temp, int left, int right) {
    if (left < right) {
        int mid = left + (right - left) / 2;
        mergeSortHelper(arr, temp, left, mid);
        mergeSortHelper(arr, temp, mid + 1, right);
        merge(arr, temp, left, mid, right);
    }
}

template<typename T>
void mergeSort(std::vector<T>& arr) {
    if (arr.size() > 1) {
        std::vector<T> temp(arr.size());
        mergeSortHelper(arr, temp, 0, static_cast<int>(arr.size()) - 1);
    }
}

/**
 * 堆排序
 * 时间复杂度: O(n log n)
 * 空间复杂度: O(1)
 */
template<typename T>
void heapify(std::vector<T>& arr, int n, int i) {
    int largest = i;
    int left = 2 * i + 1;
    int right = 2 * i + 2;
    
    if (left < n && arr[left] > arr[largest])
        largest = left;
    if (right < n && arr[right] > arr[largest])
        largest = right;
    
    if (largest != i) {
        std::swap(arr[i], arr[largest]);
        heapify(arr, n, largest);
    }
}

template<typename T>
void heapSort(std::vector<T>& arr) {
    int n = static_cast<int>(arr.size());
    if (n <= 1) return;
    
    // 建堆
    for (int i = n / 2 - 1; i >= 0; i--)
        heapify(arr, n, i);
    
    // 提取元素
    for (int i = n - 1; i > 0; i--) {
        std::swap(arr[0], arr[i]);
        heapify(arr, i, 0);
    }
}

/**
 * 希尔排序
 * 时间复杂度: O(n log n) ~ O(n²)
 */
template<typename T>
void shellSort(std::vector<T>& arr) {
    int n = static_cast<int>(arr.size());
    for (int gap = n / 2; gap > 0; gap /= 2) {
        for (int i = gap; i < n; i++) {
            T temp = arr[i];
            int j;
            for (j = i; j >= gap && arr[j - gap] > temp; j -= gap) {
                arr[j] = arr[j - gap];
            }
            arr[j] = temp;
        }
    }
}

/**
 * 计数排序（适用于非负整数）
 * 时间复杂度: O(n + k), k为数值范围
 */
void countingSort(std::vector<int>& arr, int maxVal) {
    if (arr.empty()) return;
    
    std::vector<int> count(maxVal + 1, 0);
    std::vector<int> output(arr.size());
    
    for (int num : arr) count[num]++;
    for (int i = 1; i <= maxVal; i++) count[i] += count[i - 1];
    for (int i = static_cast<int>(arr.size()) - 1; i >= 0; i--) {
        output[count[arr[i]] - 1] = arr[i];
        count[arr[i]]--;
    }
    
    arr = std::move(output);
}

/**
 * 基数排序
 * 时间复杂度: O(d * (n + k)), d为数字位数
 */
void radixSort(std::vector<int>& arr) {
    if (arr.empty()) return;
    
    int maxVal = *std::max_element(arr.begin(), arr.end());
    
    for (int exp = 1; maxVal / exp > 0; exp *= 10) {
        std::vector<int> output(arr.size());
        std::vector<int> count(10, 0);
        
        for (int num : arr) count[(num / exp) % 10]++;
        for (int i = 1; i < 10; i++) count[i] += count[i - 1];
        for (int i = static_cast<int>(arr.size()) - 1; i >= 0; i--) {
            output[count[(arr[i] / exp) % 10] - 1] = arr[i];
            count[(arr[i] / exp) % 10]--;
        }
        
        arr = std::move(output);
    }
}

// 辅助函数：打印数组
template<typename T>
void printArray(const std::vector<T>& arr, const std::string& label = "") {
    if (!label.empty()) std::cout << label << ": ";
    for (const auto& elem : arr) {
        std::cout << elem << " ";
    }
    std::cout << std::endl;
}

} // namespace sorting

int main() {
    using namespace sorting;
    
    std::cout << "=== 排序算法演示 ===" << std::endl;
    
    // 快速排序
    std::vector<int> arr1 = {64, 34, 25, 12, 22, 11, 90};
    printArray(arr1, "Original");
    quickSort(arr1);
    printArray(arr1, "QuickSort");
    
    // 归并排序
    std::vector<int> arr2 = {38, 27, 43, 3, 9, 82, 10};
    printArray(arr2, "\nOriginal");
    mergeSort(arr2);
    printArray(arr2, "MergeSort");
    
    // 堆排序
    std::vector<int> arr3 = {12, 11, 13, 5, 6, 7};
    printArray(arr3, "\nOriginal");
    heapSort(arr3);
    printArray(arr3, "HeapSort");
    
    // 希尔排序
    std::vector<int> arr4 = {8, 3, 5, 4, 7, 6, 2, 1};
    printArray(arr4, "\nOriginal");
    shellSort(arr4);
    printArray(arr4, "ShellSort");
    
    // 计数排序
    std::vector<int> arr5 = {4, 2, 2, 8, 3, 3, 1};
    printArray(arr5, "\nOriginal");
    countingSort(arr5, 8);
    printArray(arr5, "CountingSort");
    
    // 基数排序
    std::vector<int> arr6 = {170, 45, 75, 90, 802, 24, 2, 66};
    printArray(arr6, "\nOriginal");
    radixSort(arr6);
    printArray(arr6, "RadixSort");
    
    return 0;
}
