package sorting;

/**
 * 归并排序实现
 * 时间复杂度: O(n log n)
 * 空间复杂度: O(n)
 * 稳定排序
 */
public class MergeSort {
    
    /**
     * 对数组进行归并排序
     * @param arr 待排序数组
     */
    public static void sort(int[] arr) {
        if (arr == null || arr.length <= 1) {
            return;
        }
        int[] temp = new int[arr.length];
        mergeSort(arr, temp, 0, arr.length - 1);
    }
    
    private static void mergeSort(int[] arr, int[] temp, int left, int right) {
        if (left < right) {
            int mid = left + (right - left) / 2;
            mergeSort(arr, temp, left, mid);
            mergeSort(arr, temp, mid + 1, right);
            merge(arr, temp, left, mid, right);
        }
    }
    
    private static void merge(int[] arr, int[] temp, int left, int mid, int right) {
        // 复制到临时数组
        for (int i = left; i <= right; i++) {
            temp[i] = arr[i];
        }
        
        int i = left;      // 左子数组索引
        int j = mid + 1;   // 右子数组索引
        int k = left;      // 合并位置索引
        
        // 合并两个有序数组
        while (i <= mid && j <= right) {
            if (temp[i] <= temp[j]) {
                arr[k++] = temp[i++];
            } else {
                arr[k++] = temp[j++];
            }
        }
        
        // 复制剩余元素
        while (i <= mid) {
            arr[k++] = temp[i++];
        }
        while (j <= right) {
            arr[k++] = temp[j++];
        }
    }
    
    /**
     * 自底向上的归并排序（非递归）
     */
    public static void sortBottomUp(int[] arr) {
        if (arr == null || arr.length <= 1) {
            return;
        }
        
        int n = arr.length;
        int[] temp = new int[n];
        
        // 从大小为1开始，逐步翻倍
        for (int size = 1; size < n; size *= 2) {
            for (int left = 0; left < n - size; left += 2 * size) {
                int mid = left + size - 1;
                int right = Math.min(left + 2 * size - 1, n - 1);
                merge(arr, temp, left, mid, right);
            }
        }
    }
    
    /**
     * 自然归并排序 - 利用数组中已有的有序序列
     */
    public static void sortNatural(int[] arr) {
        if (arr == null || arr.length <= 1) {
            return;
        }
        
        int n = arr.length;
        int[] temp = new int[n];
        
        while (true) {
            int runCount = 0;
            int i = 0;
            
            while (i < n) {
                // 找到当前run的结束位置
                int runEnd = i + 1;
                while (runEnd < n && arr[runEnd] >= arr[runEnd - 1]) {
                    runEnd++;
                }
                
                // 找到下一个run
                if (runEnd < n) {
                    int nextRunStart = runEnd;
                    int nextRunEnd = nextRunStart + 1;
                    while (nextRunEnd < n && arr[nextRunEnd] >= arr[nextRunEnd - 1]) {
                        nextRunEnd++;
                    }
                    
                    // 合并两个run
                    merge(arr, temp, i, runEnd - 1, nextRunEnd - 1);
                    runCount++;
                    i = nextRunEnd;
                } else {
                    i = runEnd;
                }
            }
            
            if (runCount == 0) break;
        }
    }
    
    // 测试
    public static void main(String[] args) {
        int[] arr = {38, 27, 43, 3, 9, 82, 10, 15, 5};
        System.out.print("Original: ");
        printArray(arr);
        
        sort(arr);
        System.out.print("Sorted: ");
        printArray(arr);
        
        // 测试自底向上版本
        int[] arr2 = {64, 34, 25, 12, 22, 11, 90};
        System.out.print("\nOriginal: ");
        printArray(arr2);
        
        sortBottomUp(arr2);
        System.out.print("BottomUp Sorted: ");
        printArray(arr2);
    }
    
    private static void printArray(int[] arr) {
        for (int num : arr) {
            System.out.print(num + " ");
        }
        System.out.println();
    }
}
