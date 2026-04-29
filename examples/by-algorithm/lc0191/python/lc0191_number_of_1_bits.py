"""LeetCode 191. 位1的个数 — Python 实现

编写一个函数，输入是一个无符号整数（以二进制串的形式），返回其二进制表达式中数字位数为 '1' 的个数（汉明重量）。

对标: LeetCode 191 / docs/13-LeetCode算法面试专题/02-算法范式专题/11-位运算.md
"""


def hamming_weight(n: int) -> int:
    """返回无符号整数 n 的二进制表示中 1 的个数。

    前置条件 (Pre):
        - n 为 32 位无符号整数，0 <= n <= 2^32 - 1。

    后置条件 (Post):
        - 返回 n 的二进制表示中 1 的个数。

    算法思路:
        n & (n - 1) 操作将 n 的最低位的 1 变为 0。
        重复此操作直到 n 为 0，操作次数即为 1 的个数。

    复杂度:
        时间复杂度: O(k) — k 为二进制中 1 的个数，最坏情况 O(32) = O(1)。
        空间复杂度: O(1)。

    证明要点:
        设 n 的最低位 1 位于第 i 位。
        - n 的第 0 到 i-1 位均为 0。
        - n - 1 的第 0 到 i-1 位变为 1，第 i 位变为 0，更高位不变。
        - 因此 n & (n - 1) 恰好将第 i 位的 1 清零，其余位不变。
        每次循环消除一个 1，计数准确。

    Args:
        n: 32 位无符号整数。

    Returns:
        二进制中 1 的个数。
    """
    count = 0
    while n:
        n &= n - 1
        count += 1
    return count


def hamming_weight_builtin(n: int) -> int:
    """使用 Python 内置 bin count 的实现（参考）。"""
    return bin(n).count("1")


if __name__ == "__main__":
    # LeetCode 官方示例
    assert hamming_weight(0b00000000000000000000000000001011) == 3, "Example 1 failed"
    assert hamming_weight(0b00000000000000000000000010000000) == 1, "Example 2 failed"
    assert hamming_weight(0b11111111111111111111111111111101) == 31, "Example 3 failed"

    # 边界条件
    assert hamming_weight(0) == 0, "Zero"
    assert hamming_weight(0xFFFFFFFF) == 32, "All ones"
    assert hamming_weight(1) == 1, "Single one"

    print("All tests passed.")
