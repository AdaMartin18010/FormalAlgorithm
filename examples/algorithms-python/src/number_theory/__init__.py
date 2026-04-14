"""
数论算法模块

包含:
- 扩展欧几里得算法 (Bézout 系数)
- 中国剩余定理 (CRT)
"""

from .extended_euclidean import extended_gcd, mod_inverse
from .chinese_remainder import chinese_remainder, chinese_remainder_iterative

__all__ = [
    "extended_gcd",
    "mod_inverse",
    "chinese_remainder",
    "chinese_remainder_iterative",
]
