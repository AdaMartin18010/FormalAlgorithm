"""
LeetCode 470. 用 Rand7() 实现 Rand10()

已有方法 rand7() 可生成 1 到 7 范围内的均匀随机整数，
试利用此方法生成 1 到 10 范围内的均匀随机整数。

思路：拒绝采样（Rejection Sampling）
1. 调用两次 rand7()，构造均匀分布的 num ∈ [0, 48]：
   num = (rand7() - 1) * 7 + (rand7() - 1)
2. 若 num < 40，则 num % 10 + 1 即为 rand10() 的结果。
3. 若 num >= 40，拒绝并重新采样。

期望时间复杂度：O(1)，空间复杂度：O(1)。
"""

import random


def rand7() -> int:
    """生成 1 到 7 的均匀随机整数（题目给定）。"""
    return random.randint(1, 7)


def rand10() -> int:
    """利用 rand7() 生成 1 到 10 的均匀随机整数。"""
    while True:
        a = rand7() - 1  # 0..6
        b = rand7() - 1  # 0..6
        num = a * 7 + b  # 0..48，均匀分布
        if num < 40:
            return num % 10 + 1  # 1..10，均匀分布


# --- Tests ---
if __name__ == "__main__":
    # 测试范围
    for _ in range(1000):
        v = rand10()
        assert 1 <= v <= 10, f"rand10() = {v} out of range"

    # 粗略均匀性测试
    count = [0] * 11
    N = 10_000
    for _ in range(N):
        count[rand10()] += 1

    expected = N // 10
    low = expected * 8 // 10
    high = expected * 12 // 10
    for v in range(1, 11):
        assert low <= count[v] <= high, (
            f"value {v} count {count[v]} out of range [{low}, {high}]"
        )

    print("All tests passed for LC 470 - Rand10 using Rand7")
