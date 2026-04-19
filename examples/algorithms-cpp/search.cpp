/**
 * search.cpp - C++搜索算法实现
 * 包含：二分搜索、下界、上界
 */

#include <iostream>
#include <vector>
#include <cassert>

namespace search {

int binarySearch(const std::vector<int>& arr, int target) {
    int left = 0, right = static_cast<int>(arr.size()) - 1;
    while (left <= right) {
        int mid = left + (right - left) / 2;
        if (arr[mid] == target) return mid;
        else if (arr[mid] < target) left = mid + 1;
        else right = mid - 1;
    }
    return -1;
}

int lowerBound(const std::vector<int>& arr, int target) {
    int left = 0, right = static_cast<int>(arr.size());
    while (left < right) {
        int mid = left + (right - left) / 2;
        if (arr[mid] < target) left = mid + 1;
        else right = mid;
    }
    return left;
}

int upperBound(const std::vector<int>& arr, int target) {
    int left = 0, right = static_cast<int>(arr.size());
    while (left < right) {
        int mid = left + (right - left) / 2;
        if (arr[mid] <= target) left = mid + 1;
        else right = mid;
    }
    return left;
}

} // namespace search

// 简单测试
int main() {
    using namespace search;
    std::vector<int> arr = {1, 3, 5, 7, 9};
    assert(binarySearch(arr, 5) == 2);
    assert(binarySearch(arr, 4) == -1);
    assert(binarySearch({}, 1) == -1);
    assert(lowerBound(arr, 5) == 2);
    assert(upperBound(std::vector<int>{1, 3, 5, 5, 7, 9}, 5) == 4);
    std::cout << "All search tests passed!" << std::endl;
    return 0;
}
