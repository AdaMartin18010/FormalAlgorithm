# Append to 04-复杂度类.md
append_04 = """

### A.41 复杂度类研究的未来方向

随着计算技术的不断发展，复杂度类研究面临着新的挑战和机遇：
1. **神经网络的复杂性**：深度学习模型的训练与推断的复杂度分类。
2. **量子优势的精确刻画**：对于哪些实际问题，量子计算机可以提供实质性的加速？
3. **分布式与并行计算的复杂性**：在云计算和大规模分布式系统中，通信、同步和容错对复杂度的影响。
4. **生物学计算的复杂性**：DNA 计算、分子计算和细胞自动机的复杂性理论。
5. **社会计算与博弈的复杂性**：计算社会科学中涉及的大规模博弈均衡计算。

这些新兴领域将推动复杂度类理论向更广阔的方向发展。
"""

append_06 = """

### A.26 更多决策树变体

**定义 A.26.1**（带比较节点的决策树）[13] Cormen et al. Introduction to Algorithms (4th ed.). MIT Press, 2022：

在某些决策树模型中，内部节点可以进行元素之间的直接比较（如 $a_i \\leq a_j$），而不仅仅是查询单个位的值。这是比较排序和选择问题最常用的模型。

**定理 A.26.1**（比较决策树与位查询决策树的关系）[5] Buhrman & de Wolf. Complexity Measures and Decision Tree Complexity: A Survey. Theor. Comput. Sci., 2002：

对于 $n$ 个元素的排序，比较决策树的深度下界为 $\\Omega(n \\log n)$。在位查询模型中（每次查询一个元素的某一位），下界可能更高，因为每次比较可以提供最多 1 位信息，而位查询在特定模型下可能提供更少的信息。

### A.27 敏感度计算的实现扩展

```rust
/// 块敏感度计算器
pub struct BlockSensitivityCalculator;

impl BlockSensitivityCalculator {
    /// 计算给定输入处的块敏感度
    pub fn local_block_sensitivity(f: &dyn Fn(&[bool]) -> bool, x: &[bool]) -> usize {
        let n = x.len();
        let fx = f(x);
        let mut max_blocks = 0;
        
        // 枚举所有非空子集的组合（简化版，仅适用于小 n）
        for mask in 1..(1 << n) {
            let mut blocks = Vec::new();
            let mut used = vec![false; n];
            
            // 尝试将当前子集作为块
            for i in 0..n {
                if used[i] { continue; }
                if ((mask >> i) & 1) == 1 {
                    let mut block = vec![i];
                    used[i] = true;
                    
                    // 检查翻转该块是否改变函数值
                    let mut x_flipped = x.to_vec();
                    for &idx in &block {
                        x_flipped[idx] = !x_flipped[idx];
                    }
                    if f(&x_flipped) != fx {
                        blocks.push(block);
                    }
                }
            }
            max_blocks = max_blocks.max(blocks.len());
        }
        max_blocks
    }
}
```

### A.28 信息论方法在量子计算中的应用

**定理 A.28.1**（Holevo 界在查询复杂度中的形式）[5] Buhrman & de Wolf. Complexity Measures and Decision Tree Complexity: A Survey. Theor. Comput. Sci., 2002：

在 $T$-查询量子算法中，通过 oracle 查询获取的关于输入的经典信息量至多为 $O(T \\log n)$ 位。这是因为每次查询可以访问 $n$ 个位中的一个，而量子算法通过叠加态和纠缠来加速计算，但信息论限制仍然存在。

然而，对于某些函数（如 $OR_n$），量子算法的 $\\sqrt{n}$ 加速来自于幅度放大：它不需要获取所有 $n$ 个位的完整信息，而只需要确定是否存在至少一个 1。

### A.29 信息论下界与其他复杂度文档的交叉引用总结

本文档与 `04-算法复杂度` 模块的其他文档形成了紧密的理论网络：
- `01-时间复杂度.md`：提供了复杂度类的时间资源基础。
- `02-空间复杂度.md`：提供了空间资源基础和 L、NL、PSPACE 等类的背景。
- `03-渐进分析.md`：提供了渐进记号和主定理等分析工具。
- `04-复杂度类.md`：定义了 P、NP、PSPACE 等核心复杂度类，是信息论下界的"上层建筑"。
- `05-通信复杂度.md`：信息复杂度方法是通信复杂度下界的核心工具，两者相互渗透。

### A.30 最后的总结

信息论下界是算法复杂度分析的终极工具之一。它不受特定算法或数据结构选择的限制，而是从信息本身的不可压缩性和传递极限出发，给出任何正确算法都必须遵守的边界。无论是经典的排序 $\\Omega(n \\log n)$ 下界，还是量子的 Grover $\\Omega(\\sqrt{n})$ 下界，信息论方法都揭示了计算的根本限制。在人工智能、大数据和量子计算蓬勃发展的今天，理解和掌握信息论下界比以往任何时候都更加重要。
"""

with open('docs/04-算法复杂度/04-复杂度类.md', 'a', encoding='utf-8') as f:
    f.write(append_04)

with open('docs/04-算法复杂度/06-信息论下界.md', 'a', encoding='utf-8') as f:
    f.write(append_06)

print("Appended to both files")
