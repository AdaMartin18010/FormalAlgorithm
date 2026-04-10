//! Manacher算法 - 最长回文子串
//! 
//! 时间复杂度: O(n)
//! 空间复杂度: O(n)

/// Manacher算法
/// 
/// 返回每个位置的最长回文半径
pub fn manacher(s: &str) -> Vec<usize> {
    let chars: Vec<char> = s.chars().collect();
    let n = chars.len();
    if n == 0 {
        return Vec::new();
    }
    
    // 插入特殊字符处理奇偶
    let mut t = vec!['#'];
    for c in &chars {
        t.push(*c);
        t.push('#');
    }
    
    let m = t.len();
    let mut p = vec![0; m];  // 回文半径
    let mut center = 0;      // 当前最右回文的中心
    let mut right = 0;       // 当前最右回文的右边界
    
    for i in 0..m {
        // 利用对称性
        if i < right {
            let mirror = 2 * center - i;
            p[i] = p[mirror].min(right - i);
        }
        
        // 中心扩展
        let mut l = i as i32 - p[i] as i32 - 1;
        let mut r = i + p[i] + 1;
        
        while l >= 0 && r < m && t[l as usize] == t[r] {
            p[i] += 1;
            l -= 1;
            r += 1;
        }
        
        // 更新最右回文
        if i + p[i] > right {
            center = i;
            right = i + p[i];
        }
    }
    
    p
}

/// 获取最长回文子串
pub fn longest_palindrome(s: &str) -> String {
    let p = manacher(s);
    let max_len = *p.iter().max().unwrap_or(&0);
    let center = p.iter().position(|&x| x == max_len).unwrap_or(0);
    
    // 转换回原字符串索引
    let start = (center - max_len) / 2;
    s.chars().skip(start).take(max_len).collect()
}

/// 统计回文子串数量
pub fn count_palindromes(s: &str) -> usize {
    let p = manacher(s);
    // 每个位置的回文半径之和（不包括中心字符）
    p.iter().sum::<usize>() / 2
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_manacher() {
        let s = "babad";
        let result = longest_palindrome(s);
        assert!(result == "bab" || result == "aba");
        
        let s2 = "cbbd";
        assert_eq!(longest_palindrome(s2), "bb");
    }
    
    #[test]
    fn test_count() {
        assert_eq!(count_palindromes("aaa"), 6);  // a, a, a, aa, aa, aaa
        assert_eq!(count_palindromes("abc"), 3);  // a, b, c
    }
}
