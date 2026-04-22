# LeetCode 算法实现 — Go

## 目录定位

本目录存放 LeetCode 经典题目的工程级 Go 实现，作为 `docs/13-LeetCode算法面试专题/` 的可执行参考代码。所有实现遵循 LeetCode 官方函数签名。

## 文件命名规范

```
lc{题号}_{题目简称}.go
```

示例：

- `lc0704_binary_search.go`
- `lc0033_search_in_rotated_sorted_array.go`
- `lc0153_find_minimum_in_rotated_sorted_array.go`

## 注释规范模板

每个导出函数必须包含完整的 package doc 风格注释：

```go
// Package leetcode 提供 LeetCode 经典题目的 Go 实现。
//
// 正确性证明与复杂度分析参见：
//   docs/13-LeetCode算法面试专题/02-算法范式专题/05-二分查找.md
package leetcode

// Search 在有序数组中查找目标值的索引。
//
// 形式化规约：
//   Pre: nums 为升序排列，len(nums) >= 0。
//   Post: 若 target 在 nums 中，返回索引 i 满足 nums[i] == target；否则返回 -1。
//
// 循环不变式：
//   设当前搜索区间为 [left, right]（闭区间）。
//   若 target 存在于 nums，则其索引必然位于 [left, right] 之内。
//
// 复杂度：
//   时间复杂度: O(log n)
//   空间复杂度: O(1)
//
// 证明要点：
//   - 终止性由区间长度严格递减保证。
//   - 部分正确性由循环不变式在区间为空时推出。
func Search(nums []int, target int) int { ... }
```

## 测试规范

每个文件必须包含 `func TestXxx(t *testing.T)` 测试函数：

1. **LeetCode 官方示例用例**：使用表驱动测试覆盖所有示例
2. **边界条件**：
   - 空切片 `[]int{}`
   - 单元素切片
   - 全部相同元素
   - 目标值为边界值

```go
func TestSearch(t *testing.T) {
 tests := []struct {
  nums     []int
  target   int
  expected int
 }{
  {[]int{-1, 0, 3, 5, 9, 12}, 9, 4},
  {[]int{-1, 0, 3, 5, 9, 12}, 2, -1},
  {[]int{}, 1, -1},
  {[]int{5}, 5, 0},
  {[]int{5}, 1, -1},
 }

 for _, tt := range tests {
  result := Search(tt.nums, tt.target)
  if result != tt.expected {
   t.Errorf("Search(%v, %d) = %d, want %d", tt.nums, tt.target, result, tt.expected)
  }
 }
}
```

## 与 docs/ 的交叉引用

- 算法范式：`docs/13-LeetCode算法面试专题/02-算法范式专题/`
- 数据结构：`docs/13-LeetCode算法面试专题/01-数据结构专题/`
- 复杂度分析：`docs/04-算法复杂度/`

在函数注释的 "证明要点" 区块中使用相对路径引用。

## 代码风格

- 遵循 `gofmt` 和 `go vet` 规范
- 导出函数使用 `CamelCase`
- 包内私有函数使用 `camelCase`
- 优先使用迭代实现
