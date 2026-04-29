with open('docs/05-类型理论/08-量子类型系统.md','r',encoding='utf-8') as f:
    text = f.read()

insert_text = """
### 7.4 量子隐形传态的类型验证 / Type Verification of Quantum Teleportation

量子隐形传态（Quantum Teleportation）是量子通信中的基础协议。在量子类型系统中，我们可以形式化地验证该协议满足以下类型安全性质：爱丽丝（Alice）持有的待传态量子比特、贝尔态（Bell state）的一半，以及鲍勃（Bob）收到的经典信息共同决定鲍勃重构出的量子态与原始态一致。

**协议的类型签名**：

```rust
/// 量子隐形传态协议 / Quantum Teleportation Protocol
pub struct Teleportation;

impl Teleportation {
    /// 执行隐形传态
    /// Performs quantum teleportation
    /// 
    /// # 类型约束
    /// - `psi`: 待传输的未知量子态（线性类型，调用后消耗）
    /// - `bell`: 爱丽丝与鲍勃共享的贝尔态（量子纠缠对）
    /// 
    /// # 返回值
    /// - 经典比特对 (c1, c2) 与鲍勃手中的修正后量子态
    pub fn teleport(
        psi: Qubit,
        bell: (Qubit, Qubit),
    ) -> Result<((bool, bool), Qubit), QuantumTypeError> {
        let (alice_q, bob_q) = bell;
        // 步骤 1：爱丽丝对 psi 与她的贝尔量子比特进行 CNOT 与 H 门操作
        let (psi, alice_q) = QuantumGate::CNOT.apply((psi, alice_q))?;
        let psi = QuantumGate::Hadamard.apply(psi)?;
        // 步骤 2：测量并获取经典比特（类型从 Qubit 转为经典 bool）
        let c1 = psi.measure();
        let c2 = alice_q.measure();
        // 步骤 3：鲍勃根据经典比特应用修正门
        let bob_state = match (c1, c2) {
            (false, false) => bob_q,
            (false, true)  => QuantumGate::X.apply(bob_q)?,
            (true, false)  => QuantumGate::Z.apply(bob_q)?,
            (true, true)   => {
                let tmp = QuantumGate::X.apply(bob_q)?;
                QuantumGate::Z.apply(tmp)?
            }
        };
        Ok(((c1, c2), bob_state))
    }
}
```

**形式化验证目标**：

1. **纠缠守恒**：输入的贝尔态 `bell` 为两个量子比特的纠缠对，协议执行后该纠缠对被消耗（测量坍缩），类型系统通过线性类型确保不会出现对 `bell` 的二次使用。
2. **信息不增**：返回的经典比特对 `(c1, c2)` 为纯经典数据（类型 `!((bool, bool), Qubit)` 中的经典部分），不包含原始量子态的连续信息，符合量子不可克隆定理 [44]。
3. **输出态等价**：若将量子态表示为密度矩阵，则有：

$$
   \\rho_{\\text{out}} = \\rho_{\\psi}
   $$

该等式可在 QRHL 框架中形式化证明 [50; 53]。

> **交叉引用**：量子计算的形式化模型与量子通信协议的安全性分析，参见 `03-形式化证明/02-程序验证.md`。

---

## 8. 未来发展方向 / Future Developments"""

text = text.replace('## 8. 未来发展方向 / Future Developments', insert_text.lstrip())

with open('docs/05-类型理论/08-量子类型系统.md','w',encoding='utf-8') as f:
    f.write(text)
print('Added 7.4 to 08')
