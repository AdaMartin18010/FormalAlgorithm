// sorting.go - Go语言排序算法实现
package main

import (
	"fmt"
)

// QuickSort 快速排序 - 原地排序
func QuickSort(arr []int) {
	if len(arr) <= 1 {
		return
	}
	quickSortHelper(arr, 0, len(arr)-1)
}

func quickSortHelper(arr []int, low, high int) {
	if low < high {
		pivot := partition(arr, low, high)
		quickSortHelper(arr, low, pivot-1)
		quickSortHelper(arr, pivot+1, high)
	}
}

func partition(arr []int, low, high int) int {
	pivot := arr[high]
	i := low - 1
	
	for j := low; j < high; j++ {
		if arr[j] <= pivot {
			i++
			arr[i], arr[j] = arr[j], arr[i]
		}
	}
	arr[i+1], arr[high] = arr[high], arr[i+1]
	return i + 1
}

// MergeSort 归并排序
func MergeSort(arr []int) []int {
	if len(arr) <= 1 {
		return arr
	}
	
	mid := len(arr) / 2
	left := MergeSort(arr[:mid])
	right := MergeSort(arr[mid:])
	
	return merge(left, right)
}

func merge(left, right []int) []int {
	result := make([]int, 0, len(left)+len(right))
	i, j := 0, 0
	
	for i < len(left) && j < len(right) {
		if left[i] <= right[j] {
			result = append(result, left[i])
			i++
		} else {
			result = append(result, right[j])
			j++
		}
	}
	
	result = append(result, left[i:]...)
	result = append(result, right[j:]...)
	return result
}

// HeapSort 堆排序
func HeapSort(arr []int) {
	n := len(arr)
	if n <= 1 {
		return
	}
	
	// 建堆
	for i := n/2 - 1; i >= 0; i-- {
		heapify(arr, n, i)
	}
	
	// 提取元素
	for i := n - 1; i > 0; i-- {
		arr[0], arr[i] = arr[i], arr[0]
		heapify(arr, i, 0)
	}
}

func heapify(arr []int, heapSize, root int) {
	largest := root
	left := 2*root + 1
	right := 2*root + 2
	
	if left < heapSize && arr[left] > arr[largest] {
		largest = left
	}
	if right < heapSize && arr[right] > arr[largest] {
		largest = right
	}
	
	if largest != root {
		arr[root], arr[largest] = arr[largest], arr[root]
		heapify(arr, heapSize, largest)
	}
}

// InsertionSort 插入排序
func InsertionSort(arr []int) {
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

// CountingSort 计数排序
func CountingSort(arr []int, maxVal int) []int {
	count := make([]int, maxVal+1)
	
	// 计数
	for _, v := range arr {
		count[v]++
	}
	
	// 累加
	for i := 1; i <= maxVal; i++ {
		count[i] += count[i-1]
	}
	
	// 输出
	output := make([]int, len(arr))
	for i := len(arr) - 1; i >= 0; i-- {
		output[count[arr[i]]-1] = arr[i]
		count[arr[i]]--
	}
	
	return output
}

func main() {
	// 测试快速排序
	arr1 := []int{3, 6, 8, 10, 1, 2, 1}
	fmt.Println("Original:", arr1)
	QuickSort(arr1)
	fmt.Println("QuickSort:", arr1)
	
	// 测试归并排序
	arr2 := []int{38, 27, 43, 3, 9, 82, 10}
	fmt.Println("\nOriginal:", arr2)
	sorted := MergeSort(arr2)
	fmt.Println("MergeSort:", sorted)
	
	// 测试堆排序
	arr3 := []int{12, 11, 13, 5, 6, 7}
	fmt.Println("\nOriginal:", arr3)
	HeapSort(arr3)
	fmt.Println("HeapSort:", arr3)
	
	// 测试计数排序
	arr4 := []int{4, 2, 2, 8, 3, 3, 1}
	fmt.Println("\nOriginal:", arr4)
	counted := CountingSort(arr4, 8)
	fmt.Println("CountingSort:", counted)
}
