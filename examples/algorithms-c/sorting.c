/**
 * sorting.c - C语言排序算法实现
 * 包含：快速排序、归并排序、堆排序、计数排序
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// 快速排序 - 原地排序
void quick_sort(int arr[], int low, int high) {
    if (low < high) {
        // 分区
        int pivot = arr[high];
        int i = low - 1;
        
        for (int j = low; j < high; j++) {
            if (arr[j] <= pivot) {
                i++;
                int temp = arr[i];
                arr[i] = arr[j];
                arr[j] = temp;
            }
        }
        
        int temp = arr[i + 1];
        arr[i + 1] = arr[high];
        arr[high] = temp;
        
        int pi = i + 1;
        
        // 递归排序
        quick_sort(arr, low, pi - 1);
        quick_sort(arr, pi + 1, high);
    }
}

// 归并排序辅助函数
void merge(int arr[], int left, int mid, int right) {
    int n1 = mid - left + 1;
    int n2 = right - mid;
    
    // 临时数组
    int* L = (int*)malloc(n1 * sizeof(int));
    int* R = (int*)malloc(n2 * sizeof(int));
    
    // 复制数据
    for (int i = 0; i < n1; i++)
        L[i] = arr[left + i];
    for (int j = 0; j < n2; j++)
        R[j] = arr[mid + 1 + j];
    
    // 合并
    int i = 0, j = 0, k = left;
    while (i < n1 && j < n2) {
        if (L[i] <= R[j]) {
            arr[k] = L[i];
            i++;
        } else {
            arr[k] = R[j];
            j++;
        }
        k++;
    }
    
    // 复制剩余元素
    while (i < n1) {
        arr[k] = L[i];
        i++;
        k++;
    }
    while (j < n2) {
        arr[k] = R[j];
        j++;
        k++;
    }
    
    free(L);
    free(R);
}

// 归并排序
void merge_sort(int arr[], int left, int right) {
    if (left < right) {
        int mid = left + (right - left) / 2;
        
        merge_sort(arr, left, mid);
        merge_sort(arr, mid + 1, right);
        
        merge(arr, left, mid, right);
    }
}

// 堆排序辅助函数
void heapify(int arr[], int n, int i) {
    int largest = i;
    int left = 2 * i + 1;
    int right = 2 * i + 2;
    
    if (left < n && arr[left] > arr[largest])
        largest = left;
    
    if (right < n && arr[right] > arr[largest])
        largest = right;
    
    if (largest != i) {
        int temp = arr[i];
        arr[i] = arr[largest];
        arr[largest] = temp;
        
        heapify(arr, n, largest);
    }
}

// 堆排序
void heap_sort(int arr[], int n) {
    // 建堆
    for (int i = n / 2 - 1; i >= 0; i--)
        heapify(arr, n, i);
    
    // 提取元素
    for (int i = n - 1; i > 0; i--) {
        int temp = arr[0];
        arr[0] = arr[i];
        arr[i] = temp;
        
        heapify(arr, i, 0);
    }
}

// 插入排序 - 适合小数组
void insertion_sort(int arr[], int n) {
    for (int i = 1; i < n; i++) {
        int key = arr[i];
        int j = i - 1;
        
        while (j >= 0 && arr[j] > key) {
            arr[j + 1] = arr[j];
            j--;
        }
        arr[j + 1] = key;
    }
}

// 计数排序
void counting_sort(int arr[], int n, int max_val) {
    int* count = (int*)calloc(max_val + 1, sizeof(int));
    int* output = (int*)malloc(n * sizeof(int));
    
    // 计数
    for (int i = 0; i < n; i++)
        count[arr[i]]++;
    
    // 累加
    for (int i = 1; i <= max_val; i++)
        count[i] += count[i - 1];
    
    // 输出（保持稳定性）
    for (int i = n - 1; i >= 0; i--) {
        output[count[arr[i]] - 1] = arr[i];
        count[arr[i]]--;
    }
    
    // 复制回原数组
    for (int i = 0; i < n; i++)
        arr[i] = output[i];
    
    free(count);
    free(output);
}

// 打印数组
void print_array(int arr[], int n) {
    for (int i = 0; i < n; i++)
        printf("%d ", arr[i]);
    printf("\n");
}

// 主函数
int main() {
    int arr1[] = {64, 34, 25, 12, 22, 11, 90};
    int n1 = sizeof(arr1) / sizeof(arr1[0]);
    
    printf("Original array: ");
    print_array(arr1, n1);
    
    quick_sort(arr1, 0, n1 - 1);
    printf("Quick sorted: ");
    print_array(arr1, n1);
    
    int arr2[] = {38, 27, 43, 3, 9, 82, 10};
    int n2 = sizeof(arr2) / sizeof(arr2[0]);
    
    printf("\nOriginal array: ");
    print_array(arr2, n2);
    
    merge_sort(arr2, 0, n2 - 1);
    printf("Merge sorted: ");
    print_array(arr2, n2);
    
    int arr3[] = {12, 11, 13, 5, 6, 7};
    int n3 = sizeof(arr3) / sizeof(arr3[0]);
    
    printf("\nOriginal array: ");
    print_array(arr3, n3);
    
    heap_sort(arr3, n3);
    printf("Heap sorted: ");
    print_array(arr3, n3);
    
    return 0;
}
