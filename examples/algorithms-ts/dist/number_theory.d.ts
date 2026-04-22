/**
 * 数论算法集合
 */
/**
 * 欧几里得算法求 GCD
 * 时间复杂度: O(log min(a,b))
 */
export declare function gcd(a: number, b: number): number;
/**
 * LCM
 */
export declare function lcm(a: number, b: number): number;
/**
 * 扩展欧几里得算法
 * 返回 [g, x, y] 满足 ax + by = gcd(a,b)
 * 时间复杂度: O(log min(a,b))
 */
export declare function extendedGcd(a: number, b: number): [number, number, number];
/**
 * 模逆元（a 与 mod 互质时存在）
 */
export declare function modInverse(a: number, mod: number): number | null;
/**
 * 快速幂
 * 时间复杂度: O(log exp)
 */
export declare function fastPow(base: number, exp: number, mod: number): number;
/**
 * Miller-Rabin 素性测试
 * 时间复杂度: O(k log³ n)
 */
export declare function isPrime(n: number, k?: number): boolean;
/**
 * 筛法求素数（埃氏筛）
 * 时间复杂度: O(n log log n)
 */
export declare function sieve(n: number): boolean[];
/**
 * 离散对数（Baby-step Giant-step）
 * 求解 a^x ≡ b (mod p)
 * 时间复杂度: O(√p)
 */
export declare function discreteLog(a: number, b: number, p: number): number | null;
export declare function runNumberTheoryTests(): void;
//# sourceMappingURL=number_theory.d.ts.map