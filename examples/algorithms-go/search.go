package algorithms

// BinarySearch returns the index of target in sorted arr, or -1 if not found.
// Time complexity: O(log n). Space complexity: O(1).
func BinarySearch(arr []int, target int) int {
	left, right := 0, len(arr)-1
	for left <= right {
		mid := (left + right) / 2
		if arr[mid] == target {
			return mid
		} else if arr[mid] < target {
			left = mid + 1
		} else {
			right = mid - 1
		}
	}
	return -1
}

// LowerBound returns the first index i such that arr[i] >= target.
// Returns len(arr) if all elements are < target.
func LowerBound(arr []int, target int) int {
	left, right := 0, len(arr)
	for left < right {
		mid := (left + right) / 2
		if arr[mid] < target {
			left = mid + 1
		} else {
			right = mid
		}
	}
	return left
}

// UpperBound returns the first index i such that arr[i] > target.
// Returns len(arr) if all elements are <= target.
func UpperBound(arr []int, target int) int {
	left, right := 0, len(arr)
	for left < right {
		mid := (left + right) / 2
		if arr[mid] <= target {
			left = mid + 1
		} else {
			right = mid
		}
	}
	return left
}
