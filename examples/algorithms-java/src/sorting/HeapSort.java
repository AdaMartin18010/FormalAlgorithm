package sorting;

/**
 * 堆排序实现
 * 时间复杂度: O(n log n)
 * 空间复杂度: O(1)
 * 不稳定排序
 */
public class HeapSort {
    
    /**
     * 对数组进行堆排序（原地排序）
     * @param arr 待排序数组
     */
    public static void sort(int[] arr) {
        if (arr == null || arr.length <= 1) {
            return;
        }
        
        int n = arr.length;
        
        // 构建最大堆（从最后一个非叶子节点开始）
        for (int i = n / 2 - 1; i >= 0; i--) {
            heapify(arr, n, i);
        }
        
        // 逐个提取最大值
        for (int i = n - 1; i > 0; i--) {
            // 将根（最大值）移到末尾
            swap(arr, 0, i);
            // 调整剩余元素为最大堆
            heapify(arr, i, 0);
        }
    }
    
    /**
     * 调整以root为根的子树为最大堆
     * @param arr 数组
     * @param heapSize 堆大小
     * @param root 根节点索引
     */
    private static void heapify(int[] arr, int heapSize, int root) {
        int largest = root;
        int left = 2 * root + 1;
        int right = 2 * root + 2;
        
        // 找出根、左子节点、右子节点中的最大值
        if (left < heapSize && arr[left] > arr[largest]) {
            largest = left;
        }
        if (right < heapSize && arr[right] > arr[largest]) {
            largest = right;
        }
        
        // 如果最大值不是根，交换并递归调整
        if (largest != root) {
            swap(arr, root, largest);
            heapify(arr, heapSize, largest);
        }
    }
    
    /**
     * 优化版本：使用迭代代替递归的heapify
     */
    public static void sortIterative(int[] arr) {
        if (arr == null || arr.length <= 1) {
            return;
        }
        
        int n = arr.length;
        
        // 建堆
        for (int i = n / 2 - 1; i >= 0; i--) {
            heapifyIterative(arr, n, i);
        }
        
        // 排序
        for (int i = n - 1; i > 0; i--) {
            swap(arr, 0, i);
            heapifyIterative(arr, i, 0);
        }
    }
    
    private static void heapifyIterative(int[] arr, int heapSize, int root) {
        int current = root;
        int value = arr[current];
        
        while (true) {
            int left = 2 * current + 1;
            int right = 2 * current + 2;
            int largest = current;
            
            if (left < heapSize && arr[left] > arr[largest]) {
                largest = left;
            }
            if (right < heapSize && arr[right] > arr[largest]) {
                largest = right;
            }
            
            if (largest == current) {
                arr[current] = value;
                break;
            }
            
            arr[current] = arr[largest];
            current = largest;
        }
    }
    
    private static void swap(int[] arr, int i, int j) {
        int temp = arr[i];
        arr[i] = arr[j];
        arr[j] = temp;
    }
    
    // 测试
    public static void main(String[] args) {
        int[] arr = {12, 11, 13, 5, 6, 7, 9, 3};
        System.out.print("Original: ");
        printArray(arr);
        
        sort(arr);
        System.out.print("Heap Sorted: ");
        printArray(arr);
        
        // 测试迭代版本
        int[] arr2 = {64, 34, 25, 12, 22, 11, 90};
        System.out.print("\nOriginal: ");
        printArray(arr2);
        
        sortIterative(arr2);
        System.out.print("Iterative Heap Sorted: ");
        printArray(arr2);
    }
    
    private static void printArray(int[] arr) {
        for (int num : arr) {
            System.out.print(num + " ");
        }
        System.out.println();
    }
}
