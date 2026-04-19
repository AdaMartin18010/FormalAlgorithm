/**
 * search.c - C语言搜索算法实现
 * 包含：二分搜索、下界、上界
 */

#include <stdio.h>
#include <assert.h>

int binary_search(const int arr[], int n, int target) {
    int left = 0, right = n - 1;
    while (left <= right) {
        int mid = left + (right - left) / 2;
        if (arr[mid] == target) return mid;
        else if (arr[mid] < target) left = mid + 1;
        else right = mid - 1;
    }
    return -1;
}

int lower_bound(const int arr[], int n, int target) {
    int left = 0, right = n;
    while (left < right) {
        int mid = left + (right - left) / 2;
        if (arr[mid] < target) left = mid + 1;
        else right = mid;
    }
    return left;
}

int upper_bound(const int arr[], int n, int target) {
    int left = 0, right = n;
    while (left < right) {
        int mid = left + (right - left) / 2;
        if (arr[mid] <= target) left = mid + 1;
        else right = mid;
    }
    return left;
}

int main() {
    int arr[] = {1, 3, 5, 7, 9};
    int n = sizeof(arr) / sizeof(arr[0]);
    assert(binary_search(arr, n, 5) == 2);
    assert(binary_search(arr, n, 4) == -1);
    assert(lower_bound(arr, n, 5) == 2);
    assert(upper_bound(arr, n, 5) == 3);
    printf("All search tests passed!\n");
    return 0;
}
