"use strict";
/**
 * 数论算法集合
 */
Object.defineProperty(exports, "__esModule", { value: true });
exports.gcd = gcd;
exports.lcm = lcm;
exports.extendedGcd = extendedGcd;
exports.modInverse = modInverse;
exports.fastPow = fastPow;
exports.isPrime = isPrime;
exports.sieve = sieve;
exports.discreteLog = discreteLog;
exports.runNumberTheoryTests = runNumberTheoryTests;
const utils_1 = require("./utils");
/**
 * 欧几里得算法求 GCD
 * 时间复杂度: O(log min(a,b))
 */
function gcd(a, b) {
    a = Math.abs(a);
    b = Math.abs(b);
    while (b !== 0) {
        const t = b;
        b = a % b;
        a = t;
    }
    return a;
}
/**
 * LCM
 */
function lcm(a, b) {
    return Math.abs(a * b) / gcd(a, b);
}
/**
 * 扩展欧几里得算法
 * 返回 [g, x, y] 满足 ax + by = gcd(a,b)
 * 时间复杂度: O(log min(a,b))
 */
function extendedGcd(a, b) {
    if (b === 0)
        return [a, 1, 0];
    const [g, x1, y1] = extendedGcd(b, a % b);
    const x = y1;
    const y = x1 - Math.floor(a / b) * y1;
    return [g, x, y];
}
/**
 * 模逆元（a 与 mod 互质时存在）
 */
function modInverse(a, mod) {
    const [g, x] = extendedGcd(a, mod);
    if (g !== 1)
        return null;
    return ((x % mod) + mod) % mod;
}
/**
 * 快速幂
 * 时间复杂度: O(log exp)
 */
function fastPow(base, exp, mod) {
    let result = 1 % mod;
    let b = ((base % mod) + mod) % mod;
    let e = exp;
    while (e > 0) {
        if (e & 1)
            result = (result * b) % mod;
        b = (b * b) % mod;
        e >>= 1;
    }
    return result;
}
/**
 * Miller-Rabin 素性测试
 * 时间复杂度: O(k log³ n)
 */
function isPrime(n, k = 5) {
    if (n < 2)
        return false;
    if (n === 2 || n === 3)
        return true;
    if (n % 2 === 0)
        return false;
    let d = n - 1;
    let s = 0;
    while (d % 2 === 0) {
        d /= 2;
        s++;
    }
    const witnesses = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37];
    for (let i = 0; i < Math.min(k, witnesses.length); i++) {
        const a = witnesses[i];
        if (a >= n)
            continue;
        let x = fastPow(a, d, n);
        if (x === 1 || x === n - 1)
            continue;
        let composite = true;
        for (let r = 1; r < s; r++) {
            x = (x * x) % n;
            if (x === n - 1) {
                composite = false;
                break;
            }
        }
        if (composite)
            return false;
    }
    return true;
}
/**
 * 筛法求素数（埃氏筛）
 * 时间复杂度: O(n log log n)
 */
function sieve(n) {
    const isPrimeArr = new Array(n + 1).fill(true);
    isPrimeArr[0] = isPrimeArr[1] = false;
    for (let i = 2; i * i <= n; i++) {
        if (isPrimeArr[i]) {
            for (let j = i * i; j <= n; j += i)
                isPrimeArr[j] = false;
        }
    }
    return isPrimeArr;
}
/**
 * 离散对数（Baby-step Giant-step）
 * 求解 a^x ≡ b (mod p)
 * 时间复杂度: O(√p)
 */
function discreteLog(a, b, p) {
    a %= p;
    b %= p;
    if (b === 1)
        return 0;
    const m = Math.ceil(Math.sqrt(p));
    const table = new Map();
    let e = 1;
    for (let i = 0; i < m; i++) {
        if (!table.has(e))
            table.set(e, i);
        e = (e * a) % p;
    }
    const factor = fastPow(a, p - 1 - m, p);
    e = b;
    for (let i = 0; i < m; i++) {
        if (table.has(e)) {
            const res = i * m + table.get(e);
            if (res < p)
                return res;
        }
        e = (e * factor) % p;
    }
    return null;
}
function runNumberTheoryTests() {
    (0, utils_1.runTests)("NumberTheory", {
        "gcd": () => {
            (0, utils_1.assertEq)(gcd(48, 18), 6);
            (0, utils_1.assertEq)(gcd(101, 103), 1);
        },
        "lcm": () => {
            (0, utils_1.assertEq)(lcm(4, 6), 12);
        },
        "extendedGcd": () => {
            const [g, x, y] = extendedGcd(30, 12);
            (0, utils_1.assertEq)(g, 6);
            (0, utils_1.assertEq)(30 * x + 12 * y, 6);
        },
        "modInverse": () => {
            (0, utils_1.assertEq)(modInverse(3, 11), 4);
            (0, utils_1.assertEq)(modInverse(10, 17), 12);
        },
        "fastPow": () => {
            (0, utils_1.assertEq)(fastPow(2, 10, 1000), 24);
            (0, utils_1.assertEq)(fastPow(3, 0, 97), 1);
        },
        "isPrime": () => {
            (0, utils_1.assertTrue)(isPrime(2));
            (0, utils_1.assertTrue)(isPrime(97));
            (0, utils_1.assertTrue)(!isPrime(100));
            (0, utils_1.assertTrue)(isPrime(104729)); // 10000th prime
        },
        "sieve": () => {
            const sp = sieve(10);
            (0, utils_1.assertTrue)(sp[2] && sp[3] && sp[5] && sp[7]);
            (0, utils_1.assertTrue)(!sp[4] && !sp[9]);
        },
        "discreteLog": () => {
            (0, utils_1.assertEq)(discreteLog(2, 3, 5), 3); // 2^3 = 8 ≡ 3 (mod 5)
        },
    });
}
//# sourceMappingURL=number_theory.js.map