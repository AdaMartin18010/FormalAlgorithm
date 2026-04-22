package leetcode

import (
	"math/rand"
	"time"
)

// LeetCode 384. 打乱数组
//
// 实现 Fisher-Yates 洗牌算法，支持 reset 和 shuffle 操作。
//
// 形式化规约：
//   Pre: nums 为整数数组。
//   Post: reset 返回原始数组；shuffle 返回均匀随机打乱后的数组。
//
// 算法思路：
//   Fisher-Yates 洗牌：从后往前遍历 i = n-1 .. 1，
//   从 [0, i] 中随机选择 j 并交换 nums[i] 和 nums[j]。
//   每个排列出现的概率均为 1/n!。
//
// 复杂度：
//   shuffle: 时间 O(n)，空间 O(1)（原地交换）
//   reset:   时间 O(n)，空间 O(n)

// ShuffleArray 保存原始数组和当前数组
type ShuffleArray struct {
	original []int
	nums     []int
	rng      *rand.Rand
}

// ConstructorShuffleArray 初始化结构体
func ConstructorShuffleArray(nums []int) ShuffleArray {
	original := make([]int, len(nums))
	copy(original, nums)
	return ShuffleArray{
		original: original,
		nums:     nums,
		rng:      rand.New(rand.NewSource(time.Now().UnixNano())),
	}
}

// Reset 将数组重置为初始状态并返回
func (this *ShuffleArray) Reset() []int {
	res := make([]int, len(this.original))
	copy(res, this.original)
	this.nums = res
	return res
}

// Shuffle 使用 Fisher-Yates 算法打乱数组并返回
func (this *ShuffleArray) Shuffle() []int {
	n := len(this.nums)
	for i := n - 1; i > 0; i-- {
		j := this.rng.Intn(i + 1)
		this.nums[i], this.nums[j] = this.nums[j], this.nums[i]
	}
	res := make([]int, len(this.nums))
	copy(res, this.nums)
	return res
}
