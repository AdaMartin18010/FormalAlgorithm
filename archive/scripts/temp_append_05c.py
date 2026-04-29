append_text = """

### A.16 通信协议树的形式化性质

**定义 A.16.1**（协议树的叶子数）[2] Kushilevitz & Nisan. Communication Complexity. Cambridge University Press, 1997：

对于函数 $f: X \\times Y \\rightarrow Z$，设 $L(f)$ 是协议树中叶子的最小数量。则：

$$D(f) = \\lceil \\log_2 L(f) \\rceil$$

**定理 A.16.2**（叶子数与矩形划分）：

$L(f)$ 等于将通信矩阵 $M_f$ 划分为 $f$-单色矩形所需的最少矩形数。

**定理 A.16.3**（协议树的平衡性）：

虽然最优协议树的深度为 $D(f)$，但协议树不一定需要是平衡的。某些函数可能要求高度不平衡的协议树才能达到最优深度。

### A.17 非均匀通信复杂度

**定义 A.17.1**（非均匀协议）[2] Kushilevitz & Nisan. Communication Complexity. Cambridge University Press, 1997：

在非均匀通信复杂度模型中，Alice 和 Bob 可以预先根据输入长度 $n$ 准备无限量的建议信息（advice），但通信量仍然只计算交互过程中交换的比特数。

**定理 A.17.1**：

任何函数 $f: \\{0,1\\}^n \\times \\{0,1\\}^n \\rightarrow \\{0,1\\}$ 的非均匀确定性通信复杂度至多为 $n$（Alice 可以直接发送她的输入，因为 Bob 可以拥有无限的预处理信息）。

### A.18 通信复杂度中的开放问题

1. **Log-Rank 猜想**：$D(f) = O(\\log^c \\text{rank}(M_f))$ 的最佳常数 $c$。目前已知 $D(f) = O(\\sqrt{\\text{rank}(M_f)} \\log \\text{rank}(M_f))$ [11] Lovett. Communication is Bounded by Root of Rank. J. ACM, 2016。

2. **直接和问题**：$D(f^{\\otimes k}) = k \\cdot D(f)$ 是否对所有函数成立？目前已知对于某些函数（如 $DISJ_n$）成立，但对于一般函数仍开放。

3. **$P = NP$ 与通信复杂度的关系**：Karchmer-Wigderson 框架表明，证明 $NC^1 \\neq L$ 或 $P \\neq NC^1$ 可以归约为证明特定函数的通信复杂度下界。

4. **量子与经典的指数差距**：对于哪些自然函数，量子通信复杂度可以指数级低于经典通信复杂度？

### A.19 更多实现代码

以下是一个通信复杂度分析器的扩展 Rust 实现：

```rust
/// 通信矩阵分析器
pub struct CommunicationMatrixAnalyzer {
    matrix: Vec<Vec<i32>>,
}

impl CommunicationMatrixAnalyzer {
    pub fn new(matrix: Vec<Vec<i32>>) -> Self {
        CommunicationMatrixAnalyzer { matrix }
    }

    /// 计算矩阵在实数域上的秩（简化版，使用高斯消元）
    pub fn rank(&self) -> usize {
        let n = self.matrix.len();
        if n == 0 { return 0; }
        let m = self.matrix[0].len();
        let mut mat: Vec<Vec<f64>> = self.matrix.iter()
            .map(|row| row.iter().map(|&x| x as f64).collect())
            .collect();
        let mut rank = 0;
        for col in 0..m {
            let mut pivot = None;
            for row in rank..n {
                if mat[row][col].abs() > 1e-9 {
                    pivot = Some(row);
                    break;
                }
            }
            if let Some(p) = pivot {
                mat.swap(rank, p);
                let pivot_val = mat[rank][col];
                for j in col..m {
                    mat[rank][j] /= pivot_val;
                }
                for row in 0..n {
                    if row != rank {
                        let factor = mat[row][col];
                        for j in col..m {
                            mat[row][j] -= factor * mat[rank][j];
                        }
                    }
                }
                rank += 1;
            }
        }
        rank
    }

    /// 基于秩下界估计确定性通信复杂度
    pub fn rank_lower_bound(&self) -> f64 {
        let r = self.rank();
        (r as f64).log2()
    }
}
```

### A.20 结论

通信复杂度理论为我们理解分布式计算、并行计算、流算法和电路复杂性的基本极限提供了深刻的数学工具。从 Yao 的开创性工作到现代的信息复杂度理论，通信复杂度在过去四十年中取得了丰富的成果。本文档系统地介绍了确定性、非确定性、随机化和量子通信复杂度模型，详细阐述了 fooling set、矩形覆盖、秩方法、discrepancy 和信息复杂度等核心下界技术，并分析了相等性、集合不交性、内积和 Greater-Than 等经典问题的完整下界。这些理论成果不仅是纯数学上的优美结构，更是指导实际系统设计和算法分析的重要工具。
"""

with open('docs/04-算法复杂度/05-通信复杂度.md', 'a', encoding='utf-8') as f:
    f.write(append_text)
print("Final append to 05-通信复杂度.md")
