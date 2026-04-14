import pytest
from src.number_theory.extended_euclidean import extended_gcd, mod_inverse


def test_extended_gcd_basic():
    g, x, y = extended_gcd(30, 12)
    assert g == 6
    assert 30 * x + 12 * y == 6


def test_extended_gcd_coprime():
    g, x, y = extended_gcd(17, 13)
    assert g == 1
    assert 17 * x + 13 * y == 1


def test_extended_gcd_negative():
    g, x, y = extended_gcd(-30, 12)
    assert g == 6
    assert (-30) * x + 12 * y == 6

    g, x, y = extended_gcd(30, -12)
    assert g == 6
    assert 30 * x + (-12) * y == 6

    g, x, y = extended_gcd(-30, -12)
    assert g == 6
    assert (-30) * x + (-12) * y == 6


def test_extended_gcd_zero():
    g, x, y = extended_gcd(0, 5)
    assert g == 5
    assert 0 * x + 5 * y == 5

    g, x, y = extended_gcd(5, 0)
    assert g == 5
    assert 5 * x + 0 * y == 5

    assert extended_gcd(0, 0) == (0, 1, 0)


def test_mod_inverse_basic():
    assert mod_inverse(3, 11) == 4
    assert mod_inverse(10, 17) == 12
    assert mod_inverse(6, 9) is None


def test_mod_inverse_verification():
    for a in (3, 7, 10, 15):
        for m in (11, 13, 17, 23):
            inv = mod_inverse(a, m)
            if inv is not None:
                assert (a * inv) % m == 1, f"failed for a={a}, m={m}"


def test_mod_inverse_non_positive_modulus():
    assert mod_inverse(3, 0) is None
    assert mod_inverse(3, -5) is None
