package sorting;

/**
 * 快速排序实现
 * 时间复杂度: 平均 O(n log n), 最坏 O(n²)
 * 空间复杂度: O(log n)
 */
public class QuickSort {
    
    /**
     * 对数组进行快速排序（原地排序）
     * @param arr 待排序数组
     */
    public static void sort(int[] arr) {
        if (arr == null || arr.length <= 1) {
            return;
        }
        quickSortHelper(arr, 0, arr.length - 1);
    }
    
    private static void quickSortHelper(int[] arr, int low, int high) {
        if (low < high) {
            int pivotIndex = partition(arr, low, high);
            quickSortHelper(arr, low, pivotIndex - 1);
            quickSortHelper(arr, pivotIndex + 1, high);
        }
    }
    
    private static int partition(int[] arr, int low, int high) {
        int pivot = arr[high];
        int i = low - 1;
        
        for (int j = low; j < high; j++) {
            if (arr[j] <= pivot) {
                i++;
                swap(arr, i, j);
            }
        }
        swap(arr, i + 1, high);
        return i + 1;
    }
    
    private static void swap(int[] arr, int i, int j) {
        int temp = arr[i];
        arr[i] = arr[j];
        arr[j] = temp;
    }
    
    /**
     * 三数取中法优化快速排序
     */
    public static void sortOptimized(int[] arr) {
        if (arr == null || arr.length <= 1) {
            return;
        }
        quickSortOptimized(arr, 0, arr.length - 1);
    }
    
    private static void quickSortOptimized(int[] arr, int low, int high) {
        // 小数组使用插入排序
        if (high - low <= 10) {
            insertionSort(arr, low, high);
            return;
        }
        
        int pivotIndex = partitionMedianOfThree(arr, low, high);
        quickSortOptimized(arr, low, pivotIndex - 1);
        quickSortOptimized(arr, pivotIndex + 1, high);
    }
    
    private static int partitionMedianOfThree(int[] arr, int low, int high) {
        int mid = low + (high - low) / 2;
        
        // 三数取中
        if (arr[mid] < arr[low]) swap(arr, low, mid);
        if (arr[high] < arr[low]) swap(arr, low, high);
        if (arr[high] < arr[mid]) swap(arr, mid, high);
        
        swap(arr, mid, high - 1);
        int pivot = arr[high - 1];
        
        int i = low;
        int j = high - 1;
        
        while (true) {
            while (arr[++i] < pivot) {}
            while (arr[--j] > pivot) {}
            if (i >= j) break;
            swap(arr, i, j);
        }
        
        swap(arr, i, high - 1);
        return i;
    }
    
    private static void insertionSort(int[] arr, int low, int high) {
        for (int i = low + 1; i <= high; i++) {
            int key = arr[i];
            int j = i - 1;
            while (j >= low && arr[j] > key) {
                arr[j + 1] = arr[j];
                j--;
            }
            arr[j + 1] = key;
        }
    }
    
    // 测试
    public static void main(String[] args) {
        int[] arr = {3, 6, 8, 10, 1, 2, 1, 5, 9, 4};
        System.out.print("Original: ");
        printArray(arr);
        
        sort(arr);
        System.out.print("Sorted: ");
        printArray(arr);
        
        // 测试优化版本
        int[] arr2 = {64, 34, 25, 12, 22, 11, 90, 5};
        System.out.print("\nOriginal: ");
        printArray(arr2);
        
        sortOptimized(arr2);
        System.out.print("Optimized Sorted: ");
        printArray(arr2);
    }
    
    private static void printArray(int[] arr) {
        for (int num : arr) {
            System.out.print(num + " ");
        }
        System.out.println();
    }
}
