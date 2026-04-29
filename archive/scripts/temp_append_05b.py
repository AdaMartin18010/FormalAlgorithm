append_text = """

### A.11 矩形法的更多应用

**定理 A.11.1**（矩形大小与通信复杂度的关系）[2] Kushilevitz & Nisan. Communication Complexity. Cambridge University Press, 1997：

设 $\\mu$ 是 $X \\times Y$ 上的一个概率分布。若所有 $f$-单色矩形的 $\\mu$-测度至多为 $\\alpha$，则：

$$D(f) \\geq \\log_2 \\left(\\frac{1}{\\alpha}\\right)$$

**证明**：协议树有 $2^{D(f)}$ 个叶子，每个叶子对应一个 $f$-单色矩形。这些矩形必须覆盖整个 $X \\times Y$，因此：

$$1 = \\mu(X \\times Y) \\leq \\sum_{\\text{leaf } \\ell} \\mu(R_\\ell) \\leq 2^{D(f)} \\cdot \\alpha$$

从而 $2^{D(f)} \\geq 1/\\alpha$，即 $D(f) \\geq \\log_2(1/\\alpha)$。

**应用**：对于 $EQ_n$ 的通信矩阵（单位矩阵），任何 1-单色矩形最多只能覆盖一个对角线元素。若 $\\mu$ 是均匀分布在对角线上的分布，则每个 1-单色矩形的 $\\mu$-测度至多为 $1/2^n$，从而 $D(EQ_n) \\geq n$。

### A.12 随机化与量子下界技术对比

| 技术 | 适用模型 | 核心思想 | 典型应用 |
|------|---------|---------|---------|
| **Fooling Set** | 确定性 | 构造大量必须位于不同矩形中的输入对 | $EQ_n$、$DISJ_n$ |
| **Rank Bound** | 确定性 | 通信矩阵的秩限制协议树深度 | $IP_n$ |
| **Discrepancy** | 随机化 | 大矩形上的函数值必须接近平衡 | $DISJ_n$、$IP_n$ |
| **Corruption** | 随机化 | 大矩形必然包含大量"错误"输入 | $DISJ_n$ |
| **Information Complexity** | 随机化 | 通信必须传递足够的信息 | $DISJ_n$、流算法下界 |
| **Approximate Degree** | 量子 | 函数的近似多项式次数限制量子查询 | $OR_n$、$AND-OR$ 树 |
| **Adversary Method** | 量子 | 构造难以区分的输入对集合 | $OR_n$、$ED_n$ |

### A.13 分布式计算中的通信下界实例

**MapReduce 排序的通信下界** [3] Rao & Yehudayoff. Communication Complexity and Applications. Cambridge University Press, 2020：

在 MapReduce 模型中，对 $n$ 个元素进行全局排序的通信复杂度为 $\\Theta(n \\log n)$ 位。

**证明概要**：
- 排序的输出是一个排列，包含 $\\log_2(n!) = \\Theta(n \\log n)$ 位信息。
- 最终所有 $p$ 个节点都必须知道这个排列（或至少知道与本地数据相关的部分）。
- 若总通信量小于 $\\Omega(n \\log n)$，则某些节点无法获得足够的信息来正确输出。

**分布式机器学习中的梯度同步** [3] Rao & Yehudayoff. Communication Complexity and Applications. Cambridge University Press, 2020：

在参数服务器架构中，$p$ 个工作节点各持有一个 $d$-维梯度向量。每轮迭代中，所有梯度必须聚合到服务器。总通信量为 $\\Theta(p \\cdot d \\cdot B)$ 位，其中 $B$ 是每个参数的位宽。

信息论分析表明，若要求服务器以 $\\epsilon$-精度估计平均梯度，则通信量至少为 $\\Omega(d \\log(1/\\epsilon))$ 位每轮。

### A.14 通信矩阵的更多代数性质

**定义 A.14.1**（奇异值与通信复杂度）[2] Kushilevitz & Nisan. Communication Complexity. Cambridge University Press, 1997：

通信矩阵 $M_f$ 的奇异值分解（SVD）为 $M_f = U \\Sigma V^T$。最大的奇异值 $\\sigma_1$ 与矩阵的谱范数相关，而所有奇异值的平方和等于矩阵的 Frobenius 范数：

$$\\sum_i \\sigma_i^2 = \\|M_f\\|_F^2 = \\sum_{x,y} f(x,y)^2$$

**定理 A.14.1**（谱方法与 discrepancy）[2] Kushilevitz & Nisan. Communication Complexity. Cambridge University Press, 1997：

对于函数 $f: X \\times Y \\rightarrow \\{-1, +1\\}$ 和均匀分布 $\\mu$：

$$\\text{disc}_\\mu(f) \\leq \\frac{\\sqrt{|X| \\cdot |Y|}}{|\\text{rank}(M_f)|} \\cdot \\sigma_{max}(M_f)$$

其中 $\\sigma_{max}(M_f)$ 是最大奇异值。对于 $\\{-1, +1\\}$ 矩阵，$\\sigma_{max}(M_f) \\leq \\sqrt{|X| \\cdot |Y|}$。

### A.15 延伸阅读

**核心教材**：
- [2] Kushilevitz & Nisan. Communication Complexity. Cambridge University Press, 1997.
- [3] Rao & Yehudayoff. Communication Complexity and Applications. Cambridge University Press, 2020.

**量子通信复杂度**：
- [5] Buhrman & de Wolf. Quantum Communication Complexity: A Survey. arXiv:quant-ph/0103060, 2001.

**电路复杂性与通信复杂性的联系**：
- [10] Karchmer & Wigderson. Monotone Circuits for Connectivity Require Super-Logarithmic Depth. SIAM J. Discrete Math., 1990.
"""

with open('docs/04-算法复杂度/05-通信复杂度.md', 'a', encoding='utf-8') as f:
    f.write(append_text)
print("Appended more to 05-通信复杂度.md")
