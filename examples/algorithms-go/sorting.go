// Package algorithms provides core algorithm implementations in Go.
package algorithms

// QuickSort sorts a slice of ints in-place using the quicksort algorithm.
// Time complexity: O(n log n) average, O(n²) worst case.
// Space complexity: O(log n) due to recursion.
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

// MergeSort returns a new sorted slice using the merge sort algorithm.
// Time complexity: O(n log n). Space complexity: O(n).
func MergeSort(arr []int) []int {
	if len(arr) <= 1 {
		result := make([]int, len(arr))
		copy(result, arr)
		return result
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

// HeapSort sorts a slice of ints in-place using the heap sort algorithm.
// Time complexity: O(n log n). Space complexity: O(1).
func HeapSort(arr []int) {
	n := len(arr)
	if n <= 1 {
		return
	}
	// Build max heap
	for i := n/2 - 1; i >= 0; i-- {
		heapify(arr, n, i)
	}
	// Extract elements
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

// InsertionSort sorts a slice of ints in-place using insertion sort.
// Time complexity: O(n²) worst case, O(n) best case.
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

// CountingSort returns a new sorted slice using counting sort.
// Requires all elements to be non-negative and within the range [0, maxVal].
// Time complexity: O(n + k) where k = maxVal. Space complexity: O(n + k).
func CountingSort(arr []int, maxVal int) []int {
	if len(arr) == 0 {
		return []int{}
	}
	count := make([]int, maxVal+1)
	for _, v := range arr {
		if v >= 0 && v <= maxVal {
			count[v]++
		}
	}
	for i := 1; i <= maxVal; i++ {
		count[i] += count[i-1]
	}
	output := make([]int, len(arr))
	for i := len(arr) - 1; i >= 0; i-- {
		v := arr[i]
		output[count[v]-1] = v
		count[v]--
	}
	return output
}
