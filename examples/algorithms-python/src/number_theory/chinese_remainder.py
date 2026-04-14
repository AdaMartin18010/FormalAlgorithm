"""
中国剩余定理（CRT）- Python 版本

求解两两互素模数下的同余方程组。
对标: CLRS Chapter 31.5
"""

from .extended_euclidean import extended_gcd


def chinese_remainder(remainders: list[int], moduli: list[int]) -> tuple[int, int] | None:
    """
    中国剩余定理（经典形式）。

    求解同余方程组 x ≡ remainders[i] (mod moduli[i])，
    要求 moduli 两两互素。

    参数:
        remainders: 余数列表
        moduli: 模数列表

    返回:
        (solution, combined_modulus) 元组，其中 solution 为最小非负解；
        若输入不合法或模数不两两互素，返回 None。

    示例:
        >>> chinese_remainder([2, 3, 2], [3, 5, 7])
        (23, 105)
    """
    if len(remainders) != len(moduli) or not remainders:
        return None

    # 检查两两互素
    for i in range(len(moduli)):
        for j in range(i + 1, len(moduli)):
            g, _, _ = extended_gcd(moduli[i], moduli[j])
            if g != 1:
                return None

    product = 1
    for m in moduli:
        product *= m

    total = 0
    for a, m in zip(remainders, moduli):
        mi = product // m
        _, yi, _ = extended_gcd(mi, m)
        yi = yi % m
        total += a * mi * yi

    return total % product, product


def chinese_remainder_iterative(
    remainders: list[int], moduli: list[int]
) -> tuple[int, int] | None:
    """
    逐次合并版中国剩余定理。

    每次合并两个同余方程，可处理部分非互素模数（只要相容）。

    参数:
        remainders: 余数列表
        moduli: 模数列表

    返回:
        (solution, combined_modulus) 元组；若无解返回 None。

    示例:
        >>> chinese_remainder_iterative([2, 3, 2], [3, 5, 7])
        (23, 105)
        >>> chinese_remainder_iterative([1, 3], [4, 6])  # 不互素但相容
        (9, 12)
    """
    if len(remainders) != len(moduli) or not remainders:
        return None

    a = remainders[0]
    n = moduli[0]

    for ai, ni in zip(remainders[1:], moduli[1:]):
        g, p, _ = extended_gcd(n, ni)
        if (a - ai) % g != 0:
            return None

        diff = (ai - a) // g
        lcm = n * (ni // g)

        t = (diff * p) % (ni // g)
        a = (a + n * t) % lcm
        n = lcm

    return a % n, n
