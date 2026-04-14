"""
扩展欧几里得算法 - Python 版本

计算 Bézout 系数与模逆元。
对标: CLRS Chapter 31.2
"""


def extended_gcd(a: int, b: int) -> tuple[int, int, int]:
    """
    扩展欧几里得算法。

    计算整数 a 与 b 的最大公约数 g，以及 Bézout 系数 (x, y)，
    使得 a*x + b*y = g = gcd(a, b)。返回的 g 始终非负。

    参数:
        a: 第一个整数
        b: 第二个整数

    返回:
        三元组 (g, x, y)

    示例:
        >>> extended_gcd(30, 12)
        (6, 1, -2)
        >>> extended_gcd(17, 13)
        (1, -3, 4)
    """

    def _inner(x: int, y: int) -> tuple[int, int, int]:
        if y == 0:
            return x, 1, 0
        g, x1, y1 = _inner(y, x % y)
        return g, y1, x1 - (x // y) * y1

    g, x, y = _inner(a, b)
    if g < 0:
        return -g, -x, -y
    return g, x, y


def mod_inverse(a: int, modulus: int) -> int | None:
    """
    计算 a 在模 modulus 下的乘法逆元。

    若 gcd(a, modulus) == 1，返回最小非负逆元 x 使得 a*x ≡ 1 (mod modulus)。
    否则返回 None。

    参数:
        a: 待求逆元的整数
        modulus: 模数，必须为正

    返回:
        逆元整数或 None

    示例:
        >>> mod_inverse(3, 11)
        4
        >>> mod_inverse(6, 9) is None
        True
    """
    if modulus <= 0:
        return None
    g, x, _ = extended_gcd(a, modulus)
    if g != 1:
        return None
    return x % modulus
