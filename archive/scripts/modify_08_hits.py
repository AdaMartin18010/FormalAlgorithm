with open("docs/06-逻辑系统/08-高阶逻辑理论.md", "r", encoding="utf-8") as f:
    content = f.read()

extra_hits = '''#### 高阶归纳类型在 Lean 中的实现细节

在 Lean 4 中，标准的 `inductive` 命令生成的是**严格正递归**（strictly positive recursive）类型。例如，自然数的定义：

```lean
inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
```

Lean 的类型检查器会自动生成相应的**递归原理**（recursor）：

```lean
Nat.rec : {motive : Nat → Sort u} → motive zero → ((n : Nat) → motive n → motive (succ n)) → (t : Nat) → motive t
```

对于更复杂的高阶归纳类型，如包含路径构造子的 S1，Lean 的 HoTT 库提供了 `hott_inductive` 宏，自动生成相应的**路径归纳原理**（path induction principle）。这里的关键约束在于：在覆盖空间 B 中，沿 loop 运输点 b 必须回到自身 [Jacobs1999]。

**Coq 中的实践**：Coq 的 `Inductive` 机制通过 guardedness 条件确保所有归纳定义都是良基的。对于余归纳，Coq 要求所有构造子都是**生产性的**（productive）——即每次展开都必须产生至少一个可观察的构造子。Coq 8.13 之后引入的 `Equations` 插件极大地简化了高阶（相互）归纳和余归纳定义的编写与证明。

'''

marker = '它们是现代证明助手处理代数拓扑、范畴论语义等高级主题的关键工具。'
content = content.replace(marker, marker + '\n\n' + extra_hits)

with open("docs/06-逻辑系统/08-高阶逻辑理论.md", "w", encoding="utf-8") as f:
    f.write(content)

print("08 HITs expanded, length:", len(content))
