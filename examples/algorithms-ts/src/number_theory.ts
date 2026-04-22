/**
 * 数论算法集合
 */

import { runTests, assertEq, assertTrue } from "./utils";

/**
 * 欧几里得算法求 GCD
 * 时间复杂度: O(log min(a,b))
 */
export function gcd(a: number, b: number): number {
  a = Math.abs(a); b = Math.abs(b);
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
export function lcm(a: number, b: number): number {
  return Math.abs(a * b) / gcd(a, b);
}

/**
 * 扩展欧几里得算法
 * 返回 [g, x, y] 满足 ax + by = gcd(a,b)
 * 时间复杂度: O(log min(a,b))
 */
export function extendedGcd(a: number, b: number): [number, number, number] {
  if (b === 0) return [a, 1, 0];
  const [g, x1, y1] = extendedGcd(b, a % b);
  const x = y1;
  const y = x1 - Math.floor(a / b) * y1;
  return [g, x, y];
}

/**
 * 模逆元（a 与 mod 互质时存在）
 */
export function modInverse(a: number, mod: number): number | null {
  const [g, x] = extendedGcd(a, mod);
  if (g !== 1) return null;
  return ((x % mod) + mod) % mod;
}

/**
 * 快速幂
 * 时间复杂度: O(log exp)
 */
export function fastPow(base: number, exp: number, mod: number): number {
  let result = 1 % mod;
  let b = ((base % mod) + mod) % mod;
  let e = exp;
  while (e > 0) {
    if (e & 1) result = (result * b) % mod;
    b = (b * b) % mod;
    e >>= 1;
  }
  return result;
}

/**
 * Miller-Rabin 素性测试
 * 时间复杂度: O(k log³ n)
 */
export function isPrime(n: number, k = 5): boolean {
  if (n < 2) return false;
  if (n === 2 || n === 3) return true;
  if (n % 2 === 0) return false;

  let d = n - 1;
  let s = 0;
  while (d % 2 === 0) { d /= 2; s++; }

  const witnesses = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37];
  for (let i = 0; i < Math.min(k, witnesses.length); i++) {
    const a = witnesses[i];
    if (a >= n) continue;
    let x = fastPow(a, d, n);
    if (x === 1 || x === n - 1) continue;
    let composite = true;
    for (let r = 1; r < s; r++) {
      x = (x * x) % n;
      if (x === n - 1) { composite = false; break; }
    }
    if (composite) return false;
  }
  return true;
}

/**
 * 筛法求素数（埃氏筛）
 * 时间复杂度: O(n log log n)
 */
export function sieve(n: number): boolean[] {
  const isPrimeArr = new Array(n + 1).fill(true);
  isPrimeArr[0] = isPrimeArr[1] = false;
  for (let i = 2; i * i <= n; i++) {
    if (isPrimeArr[i]) {
      for (let j = i * i; j <= n; j += i) isPrimeArr[j] = false;
    }
  }
  return isPrimeArr;
}

/**
 * 离散对数（Baby-step Giant-step）
 * 求解 a^x ≡ b (mod p)
 * 时间复杂度: O(√p)
 */
export function discreteLog(a: number, b: number, p: number): number | null {
  a %= p; b %= p;
  if (b === 1) return 0;
  const m = Math.ceil(Math.sqrt(p));
  const table = new Map<number, number>();
  let e = 1;
  for (let i = 0; i < m; i++) {
    if (!table.has(e)) table.set(e, i);
    e = (e * a) % p;
  }
  const factor = fastPow(a, p - 1 - m, p);
  e = b;
  for (let i = 0; i < m; i++) {
    if (table.has(e)) {
      const res = i * m + table.get(e)!;
      if (res < p) return res;
    }
    e = (e * factor) % p;
  }
  return null;
}

export function runNumberTheoryTests(): void {
  runTests("NumberTheory", {
    "gcd": () => {
      assertEq(gcd(48, 18), 6);
      assertEq(gcd(101, 103), 1);
    },
    "lcm": () => {
      assertEq(lcm(4, 6), 12);
    },
    "extendedGcd": () => {
      const [g, x, y] = extendedGcd(30, 12);
      assertEq(g, 6);
      assertEq(30 * x + 12 * y, 6);
    },
    "modInverse": () => {
      assertEq(modInverse(3, 11), 4);
      assertEq(modInverse(10, 17), 12);
    },
    "fastPow": () => {
      assertEq(fastPow(2, 10, 1000), 24);
      assertEq(fastPow(3, 0, 97), 1);
    },
    "isPrime": () => {
      assertTrue(isPrime(2));
      assertTrue(isPrime(97));
      assertTrue(!isPrime(100));
      assertTrue(isPrime(104729)); // 10000th prime
    },
    "sieve": () => {
      const sp = sieve(10);
      assertTrue(sp[2] && sp[3] && sp[5] && sp[7]);
      assertTrue(!sp[4] && !sp[9]);
    },
    "discreteLog": () => {
      assertEq(discreteLog(2, 3, 5), 3); // 2^3 = 8 ≡ 3 (mod 5)
    },
  });
}
