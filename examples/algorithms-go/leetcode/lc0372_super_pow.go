package leetcode

// LeetCode 372. 超级次方
//
// 计算 a^b mod 1337，其中 b 以数组形式给出（大指数）。
//
// 形式化规约：
//   Pre: a ∈ [1, 2^31-1]；b 为数字数组，长度 ∈ [1, 2000]。
//   Post: 返回 (a^b) % 1337。
//
// 算法思路：
//   利用模运算递归性质：
//   a^[b0,b1,...,bn] = (a^[b0,...,bn-1])^10 · a^bn  (mod 1337)
//
//   辅助函数 powMod 使用快速幂（二进制分解）在 O(log exp) 内计算。
//
// 复杂度：
//   时间复杂度: O(k · log 1337) = O(k)，k 为 b 的长度。
//   空间复杂度: O(k) 递归栈深度。

const mod372 = 1337

// powMod 快速幂：计算 (base^exp) % mod
func powMod(base, exp, mod int) int {
	result := 1
	base %= mod
	for exp > 0 {
		if exp%2 == 1 {
			result = (result * base) % mod
		}
		base = (base * base) % mod
		exp /= 2
	}
	return result
}

// SuperPow 计算 a^b mod 1337，b 为大数数组
func SuperPow(a int, b []int) int {
	if len(b) == 0 {
		return 1 % mod372
	}
	last := b[len(b)-1]
	prefix := b[:len(b)-1]

	part1 := powMod(SuperPow(a, prefix), 10, mod372)
	part2 := powMod(a, last, mod372)
	return (part1 * part2) % mod372
}
