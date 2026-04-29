package leetcode

import (
	"math/rand"
	"time"
)

// LeetCode 398. 随机数索引
//
// 给定一个可能包含重复数字的整数数组，等概率随机返回目标数的索引。
//
// 形式化规约：
//   Pre: nums 为整数数组。
//   Post: 返回 target 在 nums 中等概率随机的一个索引。
//
// 算法思路：
//   蓄水池抽样（Reservoir Sampling）：
//   遍历数组，维护计数器 count。
//   遇到第 k 个目标数时，以 1/k 的概率选择其索引。
//
// 正确性：
//   数学归纳法证明每个目标数索引被选中概率为 1/m（m 为出现次数）。
//
// 复杂度：
//   时间: O(n) 每次 Pick
//   空间: O(1)

// RandomPickIndex 保存数组
type RandomPickIndex struct {
	nums []int
	rng  *rand.Rand
}

// ConstructorRandomPickIndex 初始化结构体
func ConstructorRandomPickIndex(nums []int) RandomPickIndex {
	return RandomPickIndex{
		nums: nums,
		rng:  rand.New(rand.NewSource(time.Now().UnixNano())),
	}
}

// PickIndex 等概率随机返回 target 的一个索引
func (this *RandomPickIndex) PickIndex(target int) int {
	count := 0
	result := 0
	for i, num := range this.nums {
		if num == target {
			count++
			// 以 1/count 的概率选择当前索引
			if this.rng.Intn(count) == 0 {
				result = i
			}
		}
	}
	return result
}
