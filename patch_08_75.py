with open('docs/05-类型理论/08-量子类型系统.md','r',encoding='utf-8') as f:
    text = f.read()

insert_text = """
### 7.5 量子态层析的线性类型约束 / Linear Type Constraints in Quantum State Tomography

量子态层析（Quantum State Tomography, QST）旨在通过多次测量重构未知量子态的密度矩阵。在类型化框架中，QST 的核心挑战在于：测量操作会**破坏**（消耗）输入量子态，因此必须在类型层面显式追踪每个副本的使用次数。

**副本类型（Clone Types）**：

为满足 QST 对大量独立样本的需求，研究者引入了**副本类型** `!_n τ`，表示可以安全复制 $n$ 次的经典资源，或准备 $n$ 个相同量子态的独立副本：

```rust
/// 量子态副本 / Quantum State Copies
pub struct QuantumCopies {
    pub count: usize,
    pub states: Vec<Qubit>,
}

impl QuantumCopies {
    /// 生成 n 个独立的量子态副本（假设源设备可重复制备）
    pub fn prepare(n: usize, source: &mut QuantumSource) -> QuantumCopies {
        let mut states = Vec::with_capacity(n);
        for _ in 0..n {
            states.push(source.prepare_qubit());
        }
        QuantumCopies { count: n, states }
    }

    /// 消耗一个副本进行测量
    pub fn consume_one(self) -> (Qubit, QuantumCopies) {
        assert!(self.count > 0);
        let mut rest = self.states;
        let q = rest.pop().unwrap();
        (q, QuantumCopies { count: self.count - 1, states: rest })
    }
}
```

**线性类型保证**：`consume_one` 接收 `self` 的所有权，返回被消耗的量子态与剩余的 `QuantumCopies`。由于 `self` 被移动，调用者无法在事后再次访问原始集合，从而防止对同一样本的重复测量。

> **交叉引用**：关于量子信息论的更多形式化内容，参见 `09-算法理论/05-量子算法.md`。

---

## 8. 未来发展方向 / Future Developments"""

text = text.replace('## 8. 未来发展方向 / Future Developments', insert_text.lstrip())

with open('docs/05-类型理论/08-量子类型系统.md','w',encoding='utf-8') as f:
    f.write(text)
print('Added 7.5 to 08')
