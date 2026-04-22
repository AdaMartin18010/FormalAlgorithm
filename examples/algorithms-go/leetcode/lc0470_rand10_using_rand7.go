package leetcode

import (
	"math/rand"
	"time"
)

// LeetCode 470. 用 Rand7() 实现 Rand10()
//
// 已有方法 rand7() 可生成 1 到 7 范围内的均匀随机整数，
// 试利用此方法生成 1 到 10 范围内的均匀随机整数。
//
// 思路：拒绝采样（Rejection Sampling）
// 1. 调用两次 rand7()，构造均匀分布的 num ∈ [0, 48]：
//    num = (rand7() - 1) * 7 + (rand7() - 1)
// 2. 若 num < 40，则 num % 10 + 1 即为 rand10() 的结果。
// 3. 若 num >= 40，拒绝并重新采样。
//
// 期望时间复杂度：O(1)，空间复杂度：O(1)。

func init() {
	rand.Seed(time.Now().UnixNano())
}

// rand7 生成 1 到 7 的均匀随机整数（题目给定）。
func rand7() int {
	return rand.Intn(7) + 1
}

// Rand10 利用 rand7() 生成 1 到 10 的均匀随机整数。
func Rand10() int {
	for {
		a := rand7() - 1 // 0..6
		b := rand7() - 1 // 0..6
		num := a*7 + b   // 0..48，均匀分布
		if num < 40 {
			return num%10 + 1 // 1..10，均匀分布
		}
	}
}
