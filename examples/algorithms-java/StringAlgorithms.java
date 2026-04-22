/**
 * 字符串算法实现
 * 包含: KMP、Manacher、Z函数、滚动哈希
 */
public class StringAlgorithms {

    /**
     * KMP前缀函数
     * 时间复杂度: O(m)
     */
    public static int[] kmpPrefix(String pattern) {
        int m = pattern.length();
        int[] pi = new int[m];
        int k = 0;
        for (int q = 1; q < m; q++) {
            while (k > 0 && pattern.charAt(k) != pattern.charAt(q)) {
                k = pi[k - 1];
            }
            if (pattern.charAt(k) == pattern.charAt(q)) k++;
            pi[q] = k;
        }
        return pi;
    }

    /**
     * KMP搜索
     * 时间复杂度: O(n + m)
     */
    public static java.util.List<Integer> kmpSearch(String text, String pattern) {
        java.util.List<Integer> matches = new java.util.ArrayList<>();
        if (pattern.isEmpty()) return matches;
        int[] pi = kmpPrefix(pattern);
        int q = 0;
        for (int i = 0; i < text.length(); i++) {
            while (q > 0 && pattern.charAt(q) != text.charAt(i)) q = pi[q - 1];
            if (pattern.charAt(q) == text.charAt(i)) q++;
            if (q == pattern.length()) {
                matches.add(i - pattern.length() + 1);
                q = pi[q - 1];
            }
        }
        return matches;
    }

    /**
     * Manacher算法 - 返回改造后字符串的半径数组
     * 时间复杂度: O(n)
     */
    public static int[] manacher(String s) {
        StringBuilder sb = new StringBuilder("^#");
        for (char c : s.toCharArray()) { sb.append(c).append('#'); }
        sb.append('$');
        String t = sb.toString();
        int n = t.length();
        int[] p = new int[n];
        int c = 0, r = 0;
        for (int i = 1; i < n - 1; i++) {
            int mirr = 2 * c - i;
            if (i < r) p[i] = Math.min(r - i, p[mirr]);
            while (t.charAt(i + 1 + p[i]) == t.charAt(i - 1 - p[i])) p[i]++;
            if (i + p[i] > r) { c = i; r = i + p[i]; }
        }
        return p;
    }

    /**
     * Z函数
     * 时间复杂度: O(n)
     */
    public static int[] zFunction(String s) {
        int n = s.length();
        int[] z = new int[n];
        int l = 0, r = 0;
        for (int i = 1; i < n; i++) {
            if (i <= r) z[i] = Math.min(r - i + 1, z[i - l]);
            while (i + z[i] < n && s.charAt(z[i]) == s.charAt(i + z[i])) z[i]++;
            if (i + z[i] - 1 > r) { l = i; r = i + z[i] - 1; }
        }
        return z;
    }

    /**
     * 滚动哈希 (Rabin-Karp)
     * 时间复杂度: O(n)预处理, O(1)查询
     */
    public static class RollingHash {
        private final long[] prefix;
        private final long[] power;
        private final long base;
        private final long mod;

        public RollingHash(String s, long base, long mod) {
            this.base = base;
            this.mod = mod;
            int n = s.length();
            prefix = new long[n + 1];
            power = new long[n + 1];
            power[0] = 1;
            for (int i = 0; i < n; i++) {
                prefix[i + 1] = (prefix[i] * base + s.charAt(i)) % mod;
                power[i + 1] = (power[i] * base) % mod;
            }
        }

        public long getHash(int l, int r) {
            long res = prefix[r] - (prefix[l] * power[r - l]) % mod;
            if (res < 0) res += mod;
            return res;
        }
    }
}
