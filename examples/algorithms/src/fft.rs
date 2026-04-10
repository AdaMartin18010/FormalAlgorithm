//! 快速傅里叶变换 (FFT)
//! 
//! Cooley-Tukey算法
//! 复杂度: O(n log n)

use num_complex::Complex;

/// FFT (迭代版本)
pub fn fft(input: &[Complex<f64>]) -> Vec<Complex<f64>> {
    let n = input.len();
    assert!(n.is_power_of_two(), "FFT length must be power of 2");
    
    // 位反转置换
    let mut result = bit_reverse_copy(input);
    
    let mut len = 2;
    while len <= n {
        let omega_len = Complex::new(0.0, -2.0 * std::f64::consts::PI / len as f64).exp();
        for i in (0..n).step_by(len) {
            let mut omega = Complex::new(1.0, 0.0);
            for j in 0..len/2 {
                let u = result[i + j];
                let v = result[i + j + len/2] * omega;
                result[i + j] = u + v;
                result[i + j + len/2] = u - v;
                omega *= omega_len;
            }
        }
        len <<= 1;
    }
    
    result
}

/// 逆FFT
pub fn ifft(input: &[Complex<f64>]) -> Vec<Complex<f64>> {
    let n = input.len();
    let mut conjugated: Vec<_> = input.iter().map(|&c| c.conj()).collect();
    let mut result = fft(&conjugated);
    for x in &mut result {
        *x = x.conj() / n as f64;
    }
    result
}

/// 位反转
fn bit_reverse_copy(input: &[Complex<f64>]) -> Vec<Complex<f64>> {
    let n = input.len();
    let mut result = vec![Complex::new(0.0, 0.0); n];
    let bits = n.trailing_zeros();
    
    for i in 0..n {
        let rev = i.reverse_bits() >> (32 - bits);
        result[rev] = input[i];
    }
    result
}

/// 多项式乘法 (使用FFT)
pub fn polynomial_multiply(a: &[f64], b: &[f64]) -> Vec<f64> {
    let n = (a.len() + b.len() - 1).next_power_of_two();
    
    let mut fa: Vec<_> = a.iter().map(|&x| Complex::new(x, 0.0)).collect();
    let mut fb: Vec<_> = b.iter().map(|&x| Complex::new(x, 0.0)).collect();
    
    fa.resize(n, Complex::new(0.0, 0.0));
    fb.resize(n, Complex::new(0.0, 0.0));
    
    let fa_fft = fft(&fa);
    let fb_fft = fft(&fb);
    
    let fc: Vec<_> = fa_fft.iter().zip(fb_fft).map(|(a, b)| a * b).collect();
    let result = ifft(&fc);
    
    result.iter().take(a.len() + b.len() - 1).map(|c| c.re.round()).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_fft_roundtrip() {
        let input = vec![
            Complex::new(1.0, 0.0),
            Complex::new(2.0, 0.0),
            Complex::new(3.0, 0.0),
            Complex::new(4.0, 0.0),
        ];
        
        let fft_result = fft(&input);
        let ifft_result = ifft(&fft_result);
        
        for (a, b) in input.iter().zip(ifft_result) {
            assert!((a.re - b.re).abs() < 1e-10);
        }
    }
    
    #[test]
    fn test_polynomial_multiply() {
        // (1 + 2x) * (1 + 3x) = 1 + 5x + 6x^2
        let a = vec![1.0, 2.0];
        let b = vec![1.0, 3.0];
        let result = polynomial_multiply(&a, &b);
        assert_eq!(result, vec![1.0, 5.0, 6.0]);
    }
}
