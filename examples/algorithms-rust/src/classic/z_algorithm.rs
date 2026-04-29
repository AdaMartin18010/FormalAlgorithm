//! Z算法 - 字符串匹配
//! 
//! 计算Z数组: z[i] = s[0..]与s[i..]的最长公共前缀
//! 时间复杂度: O(n)

/// Z算法
/// 
/// 返回Z数组
pub fn z_algorithm(s: &[u8]) -> Vec<usize> {
    let n = s.len();
    let mut z = vec![0; n];
    z[0] = n;
    
    let mut l = 0;
    let mut r = 0;
    
    for i in 1..n {
        if i < r {
            z[i] = z[i - l].min(r - i);
        }
        
        while i + z[i] < n && s[z[i]] == s[i + z[i]] {
            z[i] += 1;
        }
        
        if i + z[i] > r {
            l = i;
            r = i + z[i];
        }
    }
    
    z
}

/// 使用Z算法进行字符串匹配
/// 
/// 返回模式串在文本中的所有匹配位置
pub fn z_search(text: &str, pattern: &str) -> Vec<usize> {
    if pattern.is_empty() || text.len() < pattern.len() {
        return Vec::new();
    }
    
    // 构造: pattern + '$' + text
    let concat: Vec<u8> = pattern.bytes()
        .chain(std::iter::once(b'$'))
        .chain(text.bytes())
        .collect();
    
    let z = z_algorithm(&concat);
    let p_len = pattern.len();
    let mut result = Vec::new();
    
    for i in p_len + 1..z.len() {
        if z[i] == p_len {
            result.push(i - p_len - 1);
        }
    }
    
    result
}

/// 统计模式串出现次数
pub fn z_count(text: &str, pattern: &str) -> usize {
    z_search(text, pattern).len()
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_z_algorithm() {
        let s = b"aaaaa";
        let z = z_algorithm(s);
        assert_eq!(z, vec![5, 4, 3, 2, 1]);
        
        let s2 = b"abacaba";
        let z2 = z_algorithm(s2);
        assert_eq!(z2, vec![7, 0, 1, 0, 3, 0, 1]);
    }
    
    #[test]
    fn test_z_search() {
        let text = "abacabadabacabae";
        let pattern = "abacaba";
        let matches = z_search(text, pattern);
        assert_eq!(matches, vec![0, 8]);
    }
}
