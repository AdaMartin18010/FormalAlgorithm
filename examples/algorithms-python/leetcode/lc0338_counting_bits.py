"""
LeetCode 338. Counting Bits
链接: https://leetcode.com/problems/counting-bits/
难度: Easy

算法: 动态规划 + 位运算
时间复杂度: O(n)
空间复杂度: O(n)

最优子结构: dp[i] = dp[i >> 1] + (i & 1)
证明: i 右移一位去掉最低位，i & 1 得到最低位的值。
"""

from typing import List


class Solution:
    def countBits(self, n: int) -> List[int]:
        """
        返回 [0, n] 范围内每个数的二进制表示中 1 的个数。
        
        形式化规约:
        - 前置条件: n >= 0
        - 后置条件: ∀ i ∈ [0, n]: result[i] = hammingWeight(i)
        
        递推关系: dp[i] = dp[i >> 1] + (i & 1)
        - i >> 1: i 右移一位（去掉最低位）
        - i & 1: i 的最低位
        - 归纳证明: 假设 dp[i>>1] 正确，则 dp[i] = hammingWeight(i>>1) + (i&1) = hammingWeight(i)
        """
        dp = [0] * (n + 1)
        for i in range(1, n + 1):
            dp[i] = dp[i >> 1] + (i & 1)
        return dp


# ---------- 测试 ----------
if __name__ == "__main__":
    sol = Solution()
    
    # 测试用例 1
    n1 = 2
    res1 = sol.countBits(n1)
    print(f"n = {n1}: {res1} (expected: [0, 1, 1])")
    assert res1 == [0, 1, 1]
    
    # 测试用例 2
    n2 = 5
    res2 = sol.countBits(n2)
    print(f"n = {n2}: {res2} (expected: [0, 1, 1, 2, 1, 2])")
    assert res2 == [0, 1, 1, 2, 1, 2]
    
    # 测试用例 3
    n3 = 0
    res3 = sol.countBits(n3)
    print(f"n = {n3}: {res3} (expected: [0])")
    assert res3 == [0]
    
    print("\nAll tests passed!")
