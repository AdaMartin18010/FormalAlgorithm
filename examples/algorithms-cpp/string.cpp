/**
 * string.cpp - C++字符串算法实现
 * 包含: KMP、Manacher、Z函数、滚动哈希
 */

#include <vector>
#include <string>
#include <cmath>

namespace string_algo {

/**
 * KMP前缀函数
 * 时间复杂度: O(m)
 */
std::vector<int> kmpPrefix(const std::string& pattern) {
    int m = pattern.size();
    std::vector<int> pi(m, 0);
    int k = 0;
    for (int q = 1; q < m; q++) {
        while (k > 0 && pattern[k] != pattern[q]) k = pi[k - 1];
        if (pattern[k] == pattern[q]) k++;
        pi[q] = k;
    }
    return pi;
}

/**
 * KMP搜索
 * 时间复杂度: O(n + m)
 */
std::vector<int> kmpSearch(const std::string& text, const std::string& pattern) {
    std::vector<int> matches;
    if (pattern.empty()) return matches;
    auto pi = kmpPrefix(pattern);
    int q = 0;
    for (size_t i = 0; i < text.size(); i++) {
        while (q > 0 && pattern[q] != text[i]) q = pi[q - 1];
        if (pattern[q] == text[i]) q++;
        if (q == (int)pattern.size()) {
            matches.push_back(i - pattern.size() + 1);
            q = pi[q - 1];
        }
    }
    return matches;
}

/**
 * Z函数
 * 时间复杂度: O(n)
 */
std::vector<int> zFunction(const std::string& s) {
    int n = s.size();
    std::vector<int> z(n, 0);
    int l = 0, r = 0;
    for (int i = 1; i < n; i++) {
        if (i <= r) z[i] = std::min(r - i + 1, z[i - l]);
        while (i + z[i] < n && s[z[i]] == s[i + z[i]]) z[i]++;
        if (i + z[i] - 1 > r) { l = i; r = i + z[i] - 1; }
    }
    return z;
}

/**
 * Manacher算法
 * 时间复杂度: O(n)
 */
std::vector<int> manacher(const std::string& s) {
    std::string t = "^#";
    for (char c : s) { t += c; t += '#'; }
    t += '$';
    int n = t.size();
    std::vector<int> p(n, 0);
    int c = 0, r = 0;
    for (int i = 1; i < n - 1; i++) {
        int mirr = 2 * c - i;
        if (i < r) p[i] = std::min(r - i, p[mirr]);
        while (t[i + 1 + p[i]] == t[i - 1 - p[i]]) p[i]++;
        if (i + p[i] > r) { c = i; r = i + p[i]; }
    }
    return p;
}

/**
 * 滚动哈希
 */
class RollingHash {
    std::vector<long long> prefix, power;
    long long base, mod;
public:
    RollingHash(const std::string& s, long long b, long long m) : base(b), mod(m) {
        int n = s.size();
        prefix.resize(n + 1);
        power.resize(n + 1);
        power[0] = 1;
        for (int i = 0; i < n; i++) {
            prefix[i + 1] = (prefix[i] * base + s[i]) % mod;
            power[i + 1] = (power[i] * base) % mod;
        }
    }
    long long getHash(int l, int r) {
        long long res = prefix[r] - (prefix[l] * power[r - l]) % mod;
        if (res < 0) res += mod;
        return res;
    }
};

} // namespace string_algo
