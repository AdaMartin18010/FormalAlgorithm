with open('docs/05-类型理论/08-量子类型系统.md','r',encoding='utf-8') as f:
    text = f.read()

insert_text = """
### 7.6 量子密钥分发的类型安全信道 / Type-Safe Channels in Quantum Key Distribution

量子密钥分发（QKD）协议（如 BB84）结合了量子信道与经典认证信道。在量子类型系统中，这两类信道可被建模为不同的类型：量子信道承载 `Qubit` 或 `QuantumQubitArray`（线性类型），而经典认证信道承载 `!Bit`（指数模态，允许无限复制）。

**BB84 协议的类型化草图**：

```rust
/// BB84 量子密钥分发协议 / BB84 QKD Protocol
pub struct BB84;

impl BB84 {
    /// 爱丽丝发送随机基矢下的量子比特
    pub fn alice_send(
        rng: &mut RandomGenerator,
        n: usize,
    ) -> (Vec<Basis>, QuantumQubitArray) {
        let mut bases = Vec::with_capacity(n);
        let mut qubits = QuantumQubitArray::new(n);
        for i in 0..n {
            let basis = rng.random_basis(); // Rectilinear or Diagonal
            let bit = rng.random_bit();
            qubits.set(i, prepare_qubit(basis, bit));
            bases.push(basis);
        }
        (bases, qubits) // qubits 为线性类型，移交给量子信道
    }

    /// 鲍勃接收并测量
    pub fn bob_receive(
        his_bases: Vec<Basis>,
        qubits: QuantumQubitArray, // 线性消耗
    ) -> Vec<Bit> {
        let mut bits = Vec::with_capacity(his_bases.len());
        for (i, basis) in his_bases.iter().enumerate() {
            bits.push(measure_in_basis(qubits.get(i), *basis));
        }
        bits // 经典结果，类型为 !Vec<Bit>
    }
}
```

**安全性的类型化视角**：量子信道的线性类型保证每个量子比特仅被测量一次（不可克隆定理），而经典认证信道的指数模态 `!` 保证基矢比对结果可以被公开讨论而不泄露密钥本身 [44; 50]。

> **交叉引用**：关于密码学形式化验证，参见 `03-形式化证明/04-密码学证明.md`。

---

## 8. 未来发展方向 / Future Developments"""

text = text.replace('## 8. 未来发展方向 / Future Developments', insert_text.lstrip())

with open('docs/05-类型理论/08-量子类型系统.md','w',encoding='utf-8') as f:
    f.write(text)
print('Added 7.6 to 08')
