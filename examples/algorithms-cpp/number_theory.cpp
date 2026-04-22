/**
 * number_theory.cpp - C++数论算法实现
 * 包含: GCD、扩展欧几里得、快速幂、Miller-Rabin、筛法
 */

#include <vector>
#include <cmath>

namespace number_theory {

/**
 * GCD
 * 时间复杂度: O(log min(a,b))
 */
long long gcd(long long a, long long b) {
    a = std::abs(a); b = std::abs(b);
    while (b != 0) { long long t = b; b = a % b; a = t; }
    return a;
}

/**
 * LCM
 */
long long lcm(long long a, long long b) {
    return std::abs(a * b) / gcd(a, b);
}

/**
 * 扩展欧几里得
 * 返回 {g, x, y} 满足 ax + by = gcd(a,b)
 */
typedef struct { long long g, x, y; } ExGcdResult;

ExGcdResult extendedGcd(long long a, long long b) {
    if (b == 0) return {a, 1, 0};
    auto r = extendedGcd(b, a % b);
    long long x = r.y;
    long long y = r.x - (a / b) * r.y;
    return {r.g, x, y};
}

/**
 * 快速幂
 * 时间复杂度: O(log exp)
 */
long long fastPow(long long base, long long exp, long long mod) {
    long long result = 1 % mod;
    long long b = ((base % mod) + mod) % mod;
    long long e = exp;
    while (e > 0) {
        if (e & 1) result = (result * b) % mod;
        b = (b * b) % mod;
        e >>= 1;
    }
    return result;
}

/**
 * Miller-Rabin素性测试
 */
bool isPrime(long long n, int k = 5) {
    if (n < 2) return false;
    if (n == 2 || n == 3) return true;
    if (n % 2 == 0) return false;
    long long d = n - 1;
    int s = 0;
    while (d % 2 == 0) { d /= 2; s++; }
    long long witnesses[] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37};
    for (int i = 0; i < std::min(k, (int)(sizeof(witnesses)/sizeof(witnesses[0]))); i++) {
        long long a = witnesses[i];
        if (a >= n) continue;
        long long x = fastPow(a, d, n);
        if (x == 1 || x == n - 1) continue;
        bool composite = true;
        for (int r = 1; r < s; r++) {
            x = (x * x) % n;
            if (x == n - 1) { composite = false; break; }
        }
        if (composite) return false;
    }
    return true;
}

/**
 * 埃氏筛
 * 时间复杂度: O(n log log n)
 */
std::vector<bool> sieve(int n) {
    std::vector<bool> isPrime(n + 1, true);
    isPrime[0] = isPrime[1] = false;
    for (int i = 2; i * i <= n; i++) {
        if (isPrime[i]) {
            for (int j = i * i; j <= n; j += i) isPrime[j] = false;
        }
    }
    return isPrime;
}

} // namespace number_theory
