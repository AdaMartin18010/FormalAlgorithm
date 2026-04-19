append_text = """

### A.16 完全性理论的深入讨论

**定理 A.16.1**（Ladner 定理的构造性证明）[2] Sipser. Introduction to the Theory of Computation (3rd ed.). Cengage Learning, 2012：

若 $P \\neq NP$，则存在语言 $L \\in NP \\setminus P$ 且 $L$ 不是 NP-完全的。

**证明概要**：Ladner 构造了一个" paddable "语言 $L$，它"足够像 SAT"以保持在 NP 中，但"足够不像 SAT"以避免 NP-完全性。具体地，定义：

$$L = \\{\\langle \\phi, 1^k \\rangle : \\phi \\in SAT \\text{ 且 } k \\geq f(|\\phi|)\\}$$

其中 $f$ 是一个缓慢增长的函数。通过仔细选择 $f$，可以确保 $L \\in NP$、$L \\notin P$（因为 $f$ 增长得足够慢，$L$ 仍然编码了 SAT 的困难实例），且 $L$ 不是 NP-完全的（因为 $f$ 的缓慢增长阻止了从 SAT 的有效归约）。

**NPI 问题的结构性意义**：

Ladner 定理表明，若 $P \\neq NP$，则 NP 中存在着"无限层次"的困难度。这与递归函数理论中的 Post 问题类似：在可计算和不可判定之间存在着无限多的中间层次。

### A.17 多项式层次（Polynomial Hierarchy, PH）

**定义 A.17.1**（多项式层次）[1] Arora & Barak. Computational Complexity: A Modern Approach. Cambridge University Press, 2009：

多项式层次 $PH$ 定义为一族复杂度类的并集：

$$PH = \\bigcup_{k=0}^{\\infty} \\Sigma_k^P = \\bigcup_{k=0}^{\\infty} \\Pi_k^P$$

其中：
- $\\Sigma_0^P = \\Pi_0^P = P$
- $\\Sigma_{k+1}^P = NP^{\\Sigma_k^P}$
- $\\Pi_k^P = co\\Sigma_k^P$

**等价定义**：

语言 $L \\in \\Sigma_k^P$，如果存在多项式时间图灵机 $M$ 和多项式 $p$，使得：

$$x \\in L \\Leftrightarrow \\exists y_1 \\forall y_2 \\exists y_3 \\cdots Q_k y_k : M(x, y_1, \\ldots, y_k) = 1$$

其中 $|y_i| \\leq p(|x|)$，量词交替 $k$ 次，$Q_k$ 是 $\\exists$ 若 $k$ 为奇数，$\\forall$ 若 $k$ 为偶数。

**定理 A.17.1**（PH 的坍塌）[1] Arora & Barak. Computational Complexity: A Modern Approach. Cambridge University Press, 2009：

若对于某个 $k$，$\\Sigma_k^P = \\Pi_k^P$，则 $PH = \\Sigma_k^P$。特别地，若 $NP = coNP$，则 $PH = NP$。

**PH-完全问题**：

$\\Sigma_k^P$-完全问题包括 $k$-量词交替的 QBF 问题（$\\Sigma_k$-QBF）。例如：
- $\\Sigma_1^P$-完全：SAT
- $\\Sigma_2^P$-完全：$\\exists\\forall$-SAT
- $\\Sigma_3^P$-完全：$\\exists\\forall\\exists$-SAT

### A.18 空间复杂度类的详细层次

**定义 A.18.1**（空间复杂度类层次）：

- **L**：$DSPACE(O(\\log n))$
- **NL**：$NSPACE(O(\\log n))$
- **L^2**：$DSPACE(O(\\log^2 n))$
- **POLYLOGSPACE**：$\\bigcup_k DSPACE(O(\\log^k n))$

**已知关系**：
- $L \\subseteq NL \\subseteq L^2 \\subseteq POLYLOGSPACE \\subseteq P$
- $NL \\subseteq POLYLOGSPACE$（由 Savitch 定理）

**定理 A.18.1**（Reingold, 2005）[1] Arora & Barak. Computational Complexity: A Modern Approach. Cambridge University Press, 2009：

无向图 s-t 连通性问题（$USTCON$）属于 $L$。即：

$$USTCON \\in L$$

这一结果是空间复杂度理论的重大突破，之前 $USTCON$ 只已知属于 $RL$（随机化对数空间）。

**定理 A.18.2**（Immerman-Szelepcsényi, 1987-1988）[2] Sipser. Introduction to the Theory of Computation (3rd ed.). Cengage Learning, 2012：

$$NL = coNL$$

证明的核心技术是一种巧妙的"归纳计数"（inductive counting）方法，允许在 NL 中计算可达顶点数，从而补问题的验证也可以在 NL 中完成。

### A.19 指数时间与多项式空间的比较

**定理 A.19.1**（$PSPACE \\subseteq EXP$）[1] Arora & Barak. Computational Complexity: A Modern Approach. Cambridge University Press, 2009：

任何使用多项式空间 $S(n) = n^{O(1)}$ 的图灵机最多运行 $2^{O(S(n))}$ 步。因此：

$$PSPACE \\subseteq EXP$$

**证明**：图灵机的配置由当前状态、磁头位置和磁带内容组成。对于 $S(n)$ 空间，不同配置的数量最多为 $|Q| \\cdot S(n) \\cdot |\\Gamma|^{S(n)} = 2^{O(S(n))}$。若图灵机运行超过此步数，则必然进入一个循环，可以停机并拒绝（对于判定问题）。

**严格分离**：由空间层次定理，$PSPACE \\subsetneq EXPSPACE$。结合 $EXP \\subseteq NEXP \\subseteq EXPSPACE$，我们有：

$$PSPACE \\subsetneq EXPSPACE$$

但 $PSPACE = EXP$、$EXP = NEXP$、或 $NEXP = EXPSPACE$ 是否成立都是未知的。

### A.20 复杂度类研究的开放问题汇总

以下是计算复杂性理论中最重要的开放问题：

1. **$P \\stackrel{?}{=} NP$**：计算复杂性理论的核心问题。
2. **$NP \\stackrel{?}{=} coNP$**：与证明系统的对偶性相关。
3. **$P \\stackrel{?}{=} PSPACE$**：多项式时间与多项式空间的关系。
4. **$L \\stackrel{?}{=} P$**：对数空间与多项式时间的关系。
5. **$NL \\stackrel{?}{=} P$**：非确定性对数空间与多项式时间的关系。
6. **$EXP \\stackrel{?}{=} NEXP$**：指数时间版本的 P vs NP。
7. **$P \\stackrel{?}{=} BPP$**：随机化是否带来计算优势？
8. **$NP \\stackrel{?}{=} BQP$**：量子计算能否解决所有 NP 问题？
9. **$PH \\stackrel{?}{=} PSPACE$**：多项式层次是否坍塌到 PSPACE？
10. **$NC \\stackrel{?}{=} P$**：P 中的所有问题是否都可以高效并行化？

这些问题中的任何一个的解决都将深刻地改变我们对计算的理解。
"""

with open('docs/04-算法复杂度/04-复杂度类.md', 'a', encoding='utf-8') as f:
    f.write(append_text)
print("Appended even more to 04-复杂度类.md")
