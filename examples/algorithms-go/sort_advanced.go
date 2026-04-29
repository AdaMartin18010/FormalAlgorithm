// sort_advanced.go - 高级排序算法实现
// 包含计数排序、基数排序、桶排序

package main

import (
	"fmt"
	"math"
)

// ==================== 计数排序 (Counting Sort) ====================

// CountingSort 计数排序
// 时间复杂度: O(n + k)，其中k是数据范围
// 空间复杂度: O(n + k)
// 适用于数据范围不大的整数排序
func CountingSort(arr []int) []int {
	if len(arr) <= 1 {
		return append([]int(nil), arr...)
	}
	
	// 找到最大值和最小值
	maxVal, minVal := arr[0], arr[0]
	for _, v := range arr {
		if v > maxVal {
			maxVal = v
		}
		if v < minVal {
			minVal = v
		}
	}
	
	// 计数数组，大小为数据范围
	rangeSize := maxVal - minVal + 1
	count := make([]int, rangeSize)
	
	// 统计每个元素出现次数
	for _, v := range arr {
		count[v-minVal]++
	}
	
	// 计算前缀和（得到每个元素的最终位置）
	for i := 1; i < rangeSize; i++ {
		count[i] += count[i-1]
	}
	
	// 从后向前遍历，将元素放入正确位置（保持稳定）
	result := make([]int, len(arr))
	for i := len(arr) - 1; i >= 0; i-- {
		val := arr[i]
		pos := count[val-minVal] - 1
		result[pos] = val
		count[val-minVal]--
	}
	
	return result
}

// CountingSortInPlace 原地计数排序（不稳定但空间优化）
func CountingSortInPlace(arr []int) {
	if len(arr) <= 1 {
		return
	}
	
	maxVal, minVal := arr[0], arr[0]
	for _, v := range arr {
		if v > maxVal {
			maxVal = v
		}
		if v < minVal {
			minVal = v
		}
	}
	
	rangeSize := maxVal - minVal + 1
	count := make([]int, rangeSize)
	
	for _, v := range arr {
		count[v-minVal]++
	}
	
	// 直接按顺序填充
	idx := 0
	for i := 0; i < rangeSize; i++ {
		for count[i] > 0 {
			arr[idx] = i + minVal
			idx++
			count[i]--
		}
	}
}

// ==================== 基数排序 (Radix Sort) ====================

// GetDigit 获取数字的第d位（从1开始，个位为1）
func GetDigit(num, d int) int {
	for i := 1; i < d; i++ {
		num /= 10
	}
	return num % 10
}

// GetMaxDigits 获取数组中最大数字的位数
func GetMaxDigits(arr []int) int {
	if len(arr) == 0 {
		return 0
	}
	
	maxVal := arr[0]
	for _, v := range arr {
		if v > maxVal {
			maxVal = v
		}
	}
	
	digits := 0
	for maxVal > 0 {
		digits++
		maxVal /= 10
	}
	return digits
}

// RadixSortLSD LSD（最低位优先）基数排序
// 时间复杂度: O(d * (n + k))，d为最大位数，k为基数（通常为10）
func RadixSortLSD(arr []int) []int {
	if len(arr) <= 1 {
		return append([]int(nil), arr...)
	}
	
	// 处理负数：分离正负
	negatives, nonNegatives := []int{}, []int{}
	for _, v := range arr {
		if v < 0 {
			negatives = append(negatives, -v)
		} else {
			nonNegatives = append(nonNegatives, v)
		}
	}
	
	radix := 10
	
	// 对非负数排序
	if len(nonNegatives) > 0 {
		maxDigits := GetMaxDigits(nonNegatives)
		result := append([]int(nil), nonNegatives...)
		
		for d := 1; d <= maxDigits; d++ {
			// 使用计数排序对第d位排序
			buckets := make([][]int, radix)
			for _, v := range result {
				digit := GetDigit(v, d)
				buckets[digit] = append(buckets[digit], v)
			}
			
			// 收集
			idx := 0
			for i := 0; i < radix; i++ {
				for _, v := range buckets[i] {
					result[idx] = v
					idx++
				}
			}
		}
		nonNegatives = result
	}
	
	// 对负数排序（逆序）
	if len(negatives) > 0 {
		maxDigits := GetMaxDigits(negatives)
		result := append([]int(nil), negatives...)
		
		for d := 1; d <= maxDigits; d++ {
			buckets := make([][]int, radix)
			for _, v := range result {
				digit := GetDigit(v, d)
				buckets[digit] = append(buckets[digit], v)
			}
			
			idx := 0
			for i := 0; i < radix; i++ {
				for _, v := range buckets[i] {
					result[idx] = v
					idx++
				}
			}
		}
		// 反转并取负
		for i := 0; i < len(result)/2; i++ {
			result[i], result[len(result)-1-i] = result[len(result)-1-i], result[i]
		}
		for i := range result {
			result[i] = -result[i]
		}
		negatives = result
	}
	
	// 合并结果
	return append(negatives, nonNegatives...)
}

// RadixSortBinary 二进制基数排序（LSD，以2^8为基数）
func RadixSortBinary(arr []int32) []int32 {
	if len(arr) <= 1 {
		return append([]int32(nil), arr...)
	}
	
	const bits = 8
	const radix = 1 << bits
	const mask = radix - 1
	
	result := append([]int32(nil), arr...)
	temp := make([]int32, len(arr))
	
	// 对32位整数的每8位进行一次计数排序
	for shift := 0; shift < 32; shift += bits {
		count := make([]int, radix+1)
		
		// 统计
		for _, v := range result {
			// 处理有符号数，将负数转为无符号表示
			uv := uint32(v)
			digit := (uv >> shift) & mask
			count[digit+1]++
		}
		
		// 前缀和
		for i := 1; i <= radix; i++ {
			count[i] += count[i-1]
		}
		
		// 稳定排序
		for i := len(result) - 1; i >= 0; i-- {
			uv := uint32(result[i])
			digit := (uv >> shift) & mask
			pos := count[digit]
			temp[pos] = result[i]
			count[digit]++
		}
		
		result, temp = temp, result
	}
	
	return result
}

// ==================== 桶排序 (Bucket Sort) ====================

// BucketSort 桶排序（适用于均匀分布的数据）
// 时间复杂度: 平均O(n + k)，最坏O(n^2)，其中k是桶的数量
func BucketSort(arr []float64, bucketCount int) []float64 {
	if len(arr) <= 1 {
		return append([]float64(nil), arr...)
	}
	
	// 找到范围
	minVal, maxVal := arr[0], arr[0]
	for _, v := range arr {
		if v < minVal {
			minVal = v
		}
		if v > maxVal {
			maxVal = v
		}
	}
	
	// 创建桶
	buckets := make([][]float64, bucketCount)
	
	// 将元素分配到桶中
	rangeSize := maxVal - minVal
	if rangeSize == 0 {
		return append([]float64(nil), arr...)
	}
	
	for _, v := range arr {
		// 计算桶索引
		idx := int((v - minVal) / rangeSize * float64(bucketCount-1))
		buckets[idx] = append(buckets[idx], v)
	}
	
	// 对每个桶排序（使用插入排序）并合并
	result := make([]float64, 0, len(arr))
	for _, bucket := range buckets {
		if len(bucket) > 0 {
			insertionSort(bucket)
			result = append(result, bucket...)
		}
	}
	
	return result
}

// 插入排序（用于桶内排序）
func insertionSort(arr []float64) {
	for i := 1; i < len(arr); i++ {
		key := arr[i]
		j := i - 1
		for j >= 0 && arr[j] > key {
			arr[j+1] = arr[j]
			j--
		}
		arr[j+1] = key
	}
}

// IntegerBucketSort 整数桶排序
func IntegerBucketSort(arr []int, bucketCount int) []int {
	if len(arr) <= 1 {
		return append([]int(nil), arr...)
	}
	
	minVal, maxVal := arr[0], arr[0]
	for _, v := range arr {
		if v < minVal {
			minVal = v
		}
		if v > maxVal {
			maxVal = v
		}
	}
	
	buckets := make([][]int, bucketCount)
	
	rangeSize := maxVal - minVal
	if rangeSize == 0 {
		return append([]int(nil), arr...)
	}
	
	for _, v := range arr {
		idx := (v - minVal) * (bucketCount - 1) / rangeSize
		buckets[idx] = append(buckets[idx], v)
	}
	
	result := make([]int, 0, len(arr))
	for _, bucket := range buckets {
		if len(bucket) > 0 {
			// 桶内使用快速排序
			quickSort(bucket, 0, len(bucket)-1)
			result = append(result, bucket...)
		}
	}
	
	return result
}

// 快速排序（用于桶内排序）
func quickSort(arr []int, low, high int) {
	if low < high {
		pivot := partition(arr, low, high)
		quickSort(arr, low, pivot-1)
		quickSort(arr, pivot+1, high)
	}
}

func partition(arr []int, low, high int) int {
	pivot := arr[high]
	i := low - 1
	
	for j := low; j < high; j++ {
		if arr[j] < pivot {
			i++
			arr[i], arr[j] = arr[j], arr[i]
		}
	}
	
	arr[i+1], arr[high] = arr[high], arr[i+1]
	return i + 1
}

// ==================== 额外的高级排序 ====================

// ShellSort 希尔排序
func ShellSort(arr []int) []int {
	result := append([]int(nil), arr...)
	n := len(result)
	
	// 使用Knuth序列: 1, 4, 13, 40, 121, ...
	for gap := n / 2; gap > 0; gap /= 2 {
		// 对每个子序列进行插入排序
		for i := gap; i < n; i++ {
			temp := result[i]
			j := i
			for j >= gap && result[j-gap] > temp {
				result[j] = result[j-gap]
				j -= gap
			}
			result[j] = temp
		}
	}
	
	return result
}

// HeapSort 堆排序
func HeapSort(arr []int) []int {
	result := append([]int(nil), arr...)
	n := len(result)
	
	// 建大顶堆
	for i := n/2 - 1; i >= 0; i-- {
		heapify(result, n, i)
	}
	
	// 一个个取出堆顶元素
	for i := n - 1; i > 0; i-- {
		result[0], result[i] = result[i], result[0]
		heapify(result, i, 0)
	}
	
	return result
}

func heapify(arr []int, n, i int) {
	largest := i
	left := 2*i + 1
	right := 2*i + 2
	
	if left < n && arr[left] > arr[largest] {
		largest = left
	}
	
	if right < n && arr[right] > arr[largest] {
		largest = right
	}
	
	if largest != i {
		arr[i], arr[largest] = arr[largest], arr[i]
		heapify(arr, n, largest)
	}
}

// ==================== 辅助函数 ====================

// IsSorted 检查数组是否已排序
func IsSorted(arr []int) bool {
	for i := 1; i < len(arr); i++ {
		if arr[i] < arr[i-1] {
			return false
		}
	}
	return true
}

// IsSortedFloat 检查浮点数组是否已排序
func IsSortedFloat(arr []float64) bool {
	for i := 1; i < len(arr); i++ {
		if arr[i] < arr[i-1] {
			return false
		}
	}
	return true
}

// GenerateRandomArray 生成随机数组（用于测试）
func GenerateRandomArray(size, min, max int) []int {
	arr := make([]int, size)
	for i := 0; i < size; i++ {
		arr[i] = min + int(float64(max-min)*float64(i)/float64(size))
		// 添加一些随机性
		if i%2 == 0 {
			arr[i] = max - arr[i]
		}
	}
	return arr
}

// ==================== 测试示例 ====================

func main() {
	fmt.Println("=================== 高级排序算法测试 ===================")
	
	// 测试1: 计数排序
	fmt.Println("\n1. 计数排序 (Counting Sort):")
	arr1 := []int{4, 2, 2, 8, 3, 3, 1, 5, 1, 7}
	fmt.Printf("  原数组: %v\n", arr1)
	sorted1 := CountingSort(arr1)
	fmt.Printf("  排序后: %v\n", sorted1)
	fmt.Printf("  是否已排序: %v\n", IsSorted(sorted1))
	
	// 测试2: 计数排序原地版本
	fmt.Println("\n2. 计数排序 (原地版本):")
	arr2 := []int{4, 2, 2, 8, 3, 3, 1}
	fmt.Printf("  原数组: %v\n", arr2)
	CountingSortInPlace(arr2)
	fmt.Printf("  排序后: %v\n", arr2)
	
	// 测试3: 基数排序
	fmt.Println("\n3. 基数排序 (Radix Sort):")
	arr3 := []int{170, 45, 75, 90, 802, 24, 2, 66, -5, -10, 0}
	fmt.Printf("  原数组: %v\n", arr3)
	sorted3 := RadixSortLSD(arr3)
	fmt.Printf("  排序后: %v\n", sorted3)
	fmt.Printf("  是否已排序: %v\n", IsSorted(sorted3))
	
	// 测试4: 二进制基数排序
	fmt.Println("\n4. 二进制基数排序 (Binary Radix Sort):")
	arr4 := []int32{170, 45, 75, 90, 802, 24, 2, 66, 0}
	fmt.Printf("  原数组: %v\n", arr4)
	sorted4 := RadixSortBinary(arr4)
	fmt.Printf("  排序后: %v\n", sorted4)
	
	// 测试5: 桶排序（浮点数）
	fmt.Println("\n5. 桶排序 - 浮点数 (Bucket Sort):")
	arr5 := []float64{0.42, 0.32, 0.33, 0.52, 0.37, 0.47, 0.51}
	fmt.Printf("  原数组: %v\n", arr5)
	sorted5 := BucketSort(arr5, 5)
	fmt.Printf("  排序后: %v\n", sorted5)
	fmt.Printf("  是否已排序: %v\n", IsSortedFloat(sorted5))
	
	// 测试6: 桶排序（整数）
	fmt.Println("\n6. 桶排序 - 整数 (Bucket Sort):")
	arr6 := []int{29, 25, 3, 49, 9, 37, 21, 43}
	fmt.Printf("  原数组: %v\n", arr6)
	sorted6 := IntegerBucketSort(arr6, 5)
	fmt.Printf("  排序后: %v\n", sorted6)
	fmt.Printf("  是否已排序: %v\n", IsSorted(sorted6))
	
	// 测试7: 希尔排序
	fmt.Println("\n7. 希尔排序 (Shell Sort):")
	arr7 := []int{64, 34, 25, 12, 22, 11, 90}
	fmt.Printf("  原数组: %v\n", arr7)
	sorted7 := ShellSort(arr7)
	fmt.Printf("  排序后: %v\n", sorted7)
	fmt.Printf("  是否已排序: %v\n", IsSorted(sorted7))
	
	// 测试8: 堆排序
	fmt.Println("\n8. 堆排序 (Heap Sort):")
	arr8 := []int{12, 11, 13, 5, 6, 7}
	fmt.Printf("  原数组: %v\n", arr8)
	sorted8 := HeapSort(arr8)
	fmt.Printf("  排序后: %v\n", sorted8)
	fmt.Printf("  是否已排序: %v\n", IsSorted(sorted8))
	
	// 测试9: 性能对比（大数据量）
	fmt.Println("\n9. 性能测试 (n=10000):")
	testArr := GenerateRandomArray(10000, 0, 100000)
	
	// 复制数组用于不同排序
	arrCopy := append([]int(nil), testArr...)
	_ = CountingSort(arrCopy)
	fmt.Printf("  计数排序: 完成\n")
	
	arrCopy = append([]int(nil), testArr...)
	// 转换为int32进行基数排序
	arr32 := make([]int32, len(arrCopy))
	for i, v := range arrCopy {
		arr32[i] = int32(v)
	}
	_ = RadixSortBinary(arr32)
	fmt.Printf("  基数排序: 完成\n")
	
	arrCopy = append([]int(nil), testArr...)
	_ = HeapSort(arrCopy)
	fmt.Printf("  堆排序: 完成\n")
	
	arrCopy = append([]int(nil), testArr...)
	_ = ShellSort(arrCopy)
	fmt.Printf("  希尔排序: 完成\n")
	
	fmt.Println("\n=================== 测试完成 ===================")
	
	fmt.Println("\n算法复杂度总结:")
	fmt.Println("  计数排序: 时间O(n+k), 空间O(n+k), 稳定")
	fmt.Println("  基数排序: 时间O(d*(n+k)), 空间O(n+k), 稳定")
	fmt.Println("  桶排序:   时间O(n+k), 空间O(n+k), 稳定")
	fmt.Println("  希尔排序: 时间O(n^(1.3)~n^2), 空间O(1), 不稳定")
	fmt.Println("  堆排序:   时间O(n log n), 空间O(1), 不稳定")
}
