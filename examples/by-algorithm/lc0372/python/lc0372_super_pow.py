"""LeetCode 372. 超级次方 — Python 实现

计算 a^b mod 1337，其中 b 以数组形式给出（大指数）。

对标: LeetCode 372
"""

from typing import List


MOD = 1337


def _pow_mod(base: int, exp: int, mod: int = MOD) -> int:
    """快速幂：计算 (base^exp) % mod。"""
    result = 1
    base %= mod
    while exp > 0:
        if exp % 2 == 1:
            result = (result * base) % mod
        base = (base * base) % mod
        exp //= 2
    return result


def super_pow(a: int, b: List[int]) -> int:
    """计算 a^b mod 1337，b 为大数（数组形式）。

    前置条件 (Pre):
        - a ∈ [1, 2^31-1]
        - b 为数字数组，长度 ∈ [1, 2000]，不含前导零（除非 b == [0]）

    后置条件 (Post):
        - 返回 (a^b) % 1337

    算法框架:
        利用模运算递归性质：
        a^[b0,b1,...,bn] = (a^[b0,...,bn-1])^10 · a^bn  (mod 1337)

        辅助函数 _pow_mod 使用快速幂在 O(log exp) 内计算。

    复杂度:
        时间复杂度: O(k · log 1337) = O(k)，k 为 b 的长度。
        空间复杂度: O(k) 递归栈。
    """
    if not b:
        return 1 % MOD

    last = b[-1]
    prefix = b[:-1]

    part1 = _pow_mod(super_pow(a, prefix), 10, MOD)
    part2 = _pow_mod(a, last, MOD)
    return (part1 * part2) % MOD


if __name__ == "__main__":
    assert super_pow(2, [3]) == 8, "Example 1 failed"
    assert super_pow(2, [1, 0]) == 1024, "Example 2 failed"
    assert super_pow(1, [4, 3, 3, 8, 5, 2]) == 1, "Example 3 failed"
    assert super_pow(2147483647, [2, 0, 0]) == 1198, "Large exponent failed"
    assert super_pow(2, [0]) == 1, "Zero exponent failed"
    print("All tests passed.")
