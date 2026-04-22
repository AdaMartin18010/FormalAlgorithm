/**
 * 数论算法实现
 * 包含: GCD、扩展欧几里得、快速幂、Miller-Rabin素性测试、筛法
 */
public class NumberTheory {

    /**
     * 欧几里得算法求GCD
     * 时间复杂度: O(log min(a,b))
     */
    public static long gcd(long a, long b) {
        a = Math.abs(a); b = Math.abs(b);
        while (b != 0) { long t = b; b = a % b; a = t; }
        return a;
    }

    /**
     * LCM
     */
    public static long lcm(long a, long b) {
        return Math.abs(a * b) / gcd(a, b);
    }

    /**
     * 扩展欧几里得算法
     * 返回 [g, x, y] 满足 ax + by = gcd(a,b)
     */
    public static long[] extendedGcd(long a, long b) {
        if (b == 0) return new long[]{a, 1, 0};
        long[] vals = extendedGcd(b, a % b);
        long g = vals[0], x1 = vals[1], y1 = vals[2];
        long x = y1;
        long y = x1 - (a / b) * y1;
        return new long[]{g, x, y};
    }

    /**
     * 模逆元
     */
    public static Long modInverse(long a, long mod) {
        long[] vals = extendedGcd(a, mod);
        if (vals[0] != 1) return null;
        long x = vals[1] % mod;
        if (x < 0) x += mod;
        return x;
    }

    /**
     * 快速幂
     * 时间复杂度: O(log exp)
     */
    public static long fastPow(long base, long exp, long mod) {
        long result = 1 % mod;
        long b = ((base % mod) + mod) % mod;
        long e = exp;
        while (e > 0) {
            if ((e & 1) == 1) result = (result * b) % mod;
            b = (b * b) % mod;
            e >>= 1;
        }
        return result;
    }

    /**
     * Miller-Rabin素性测试
     */
    public static boolean isPrime(long n, int k) {
        if (n < 2) return false;
        if (n == 2 || n == 3) return true;
        if (n % 2 == 0) return false;
        long d = n - 1;
        int s = 0;
        while (d % 2 == 0) { d /= 2; s++; }
        long[] witnesses = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37};
        for (int i = 0; i < Math.min(k, witnesses.length); i++) {
            long a = witnesses[i];
            if (a >= n) continue;
            long x = fastPow(a, d, n);
            if (x == 1 || x == n - 1) continue;
            boolean composite = true;
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
    public static boolean[] sieve(int n) {
        boolean[] isPrime = new boolean[n + 1];
        java.util.Arrays.fill(isPrime, true);
        isPrime[0] = isPrime[1] = false;
        for (int i = 2; i * i <= n; i++) {
            if (isPrime[i]) {
                for (int j = i * i; j <= n; j += i) isPrime[j] = false;
            }
        }
        return isPrime;
    }
}
