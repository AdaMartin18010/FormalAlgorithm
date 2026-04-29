with open('docs/05-类型理论/08-量子类型系统.md','r',encoding='utf-8') as f:
    text = f.read()

insert_text = """
### 7.3 量子傅里叶变换的类型安全封装 / Type-Safe Quantum Fourier Transform

量子傅里叶变换（Quantum Fourier Transform, QFT）是 Shor 算法与量子相位估计的核心子程序。在量子类型系统中，QFT 可以被封装为一个高阶类型构造，确保输入与输出量子比特数组的长度一致，并且在变换过程中不发生量子信息的非物理复制。

**类型签名**：

```rust
/// 量子傅里叶变换类型 / Quantum Fourier Transform Type
pub struct QFT;

impl QFT {
    /// 对 n 个量子比特执行 QFT
    /// Apply QFT to n qubits
    pub fn apply(n: usize, qubits: QuantumQubitArray) -> Result<QuantumQubitArray, QuantumTypeError> {
        if qubits.len() != n {
            return Err(QuantumTypeError::DimensionMismatch {
                expected: n,
                actual: qubits.len(),
            });
        }
        // 类型系统保证：qubits 在此之后不再可用（线性消耗）
        let mut result = qubits;
        for i in 0..n {
            // 应用 Hadamard 门
            result = QuantumGate::Hadamard.apply_to(&result, i)?;
            for j in (i + 1)..n {
                // 应用受控相位门 R_k
                let k = j - i + 1;
                let phase = 2.0 * std::f64::consts::PI / (1usize << k) as f64;
                result = QuantumGate::ControlledPhase(phase)
                    .apply_controlled(&result, j, i)?;
            }
        }
        // 可选：反转比特顺序以匹配标准 QFT 定义
        result.reverse();
        Ok(result)
    }
}
```

**类型安全保证**：

1. **维度匹配**：输入数组的长度必须与声明的 `n` 一致，否则类型检查器在编译时（若使用依赖类型）或运行时（若使用动态检查）拒绝调用。
2. **线性使用**：`qubits` 参数在线性类型系统下被消耗，确保 QFT 执行后原数组不可再次访问，防止幽灵量子态（ghost state）干扰后续计算。
3. **酉性保持**：`QFT::apply` 内部仅组合 `Hadamard` 与 `ControlledPhase` 门，二者均为酉门，因此整个变换的酉性由组合规则自动保证 [44]。

> **交叉引用**：关于量子计算模型的详细形式化，参见 `07-计算模型/05-量子计算模型.md`。

---

## 8. 未来发展方向 / Future Developments"""

# We want to replace the '## 8. 未来发展方向' with our insert + that header
text = text.replace('## 8. 未来发展方向 / Future Developments', insert_text.lstrip())

with open('docs/05-类型理论/08-量子类型系统.md','w',encoding='utf-8') as f:
    f.write(text)
print('Added 7.3 to 08')
