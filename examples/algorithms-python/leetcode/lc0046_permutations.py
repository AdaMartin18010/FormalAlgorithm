"""
LeetCode 46. Permutations
链接: https://leetcode.com/problems/permutations/
难度: Medium

算法: 回溯（排列树）
时间复杂度: O(n * n!)
空间复杂度: O(n)
"""

from typing import List


class Solution:
    def permute(self, nums: List[int]) -> List[List[int]]:
        """
        生成 nums 的所有全排列。
        
        形式化规约:
        - 前置条件: nums 为无重复元素的整数数组
        - 后置条件: 返回 nums 的所有 n! 个排列，无重复
        
        约束函数: C(X_k) = 所有已选元素互不重复
        状态恢复: used 数组 + path 列表在递归后撤销
        """
        n = len(nums)
        res: List[List[int]] = []
        path: List[int] = []
        used = [False] * n

        def backtrack(k: int) -> None:
            """第 k 层: 为 path[k] 选择一个未使用的元素。"""
            if k == n:
                # 找到一个完整解，复制路径到结果集
                res.append(path.copy())
                return
            
            for i in range(n):
                if used[i]:
                    continue
                # 做选择: 将 nums[i] 放入 path[k]
                used[i] = True
                path.append(nums[i])
                # 递归到第 k+1 层
                backtrack(k + 1)
                # 撤销选择: 恢复状态
                path.pop()
                used[i] = False
        
        backtrack(0)
        return res


# ---------- 测试 ----------
if __name__ == "__main__":
    sol = Solution()
    
    # 测试用例 1
    nums1 = [1, 2, 3]
    res1 = sol.permute(nums1)
    print(f"Input: {nums1}")
    print(f"Permutations: {res1}")
    print(f"Count: {len(res1)} (expected: 6)")
    assert len(res1) == 6
    
    # 测试用例 2
    nums2 = [0, 1]
    res2 = sol.permute(nums2)
    print(f"\nInput: {nums2}")
    print(f"Permutations: {res2}")
    assert len(res2) == 2
    
    # 测试用例 3: 单元素
    nums3 = [1]
    res3 = sol.permute(nums3)
    print(f"\nInput: {nums3}")
    print(f"Permutations: {res3}")
    assert res3 == [[1]]
    
    print("\nAll tests passed!")
