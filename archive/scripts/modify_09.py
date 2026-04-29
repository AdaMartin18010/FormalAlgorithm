import re

with open("docs/06-逻辑系统/09-时序逻辑理论.md", "r", encoding="utf-8") as f:
    content = f.read()

# 1. Add LTL expressiveness analysis and tableau construction
ltl_extra = """#### LTL 表达力分析：安全性与活性 / Expressiveness: Safety and Liveness

LTL 公式的表达能力可以按其所描述的系统性质进行分类。Alpern 和 Schneider 证明了：任何 LTL 可表达的 $\\omega$-正则性质都可以分解为**安全性**（safety）与**活性**（liveness）两类性质的交集 [Pnueli1977]。

**定义** (安全性 / Safety Property)
一个性质 $P$ 是安全性的，当且仅当：若某个执行轨迹 $\\pi$ 不满足 $P$，则存在 $\\pi$ 的一个有限前缀 $\\pi_{|n}$，使得任何以该前缀开头的无限轨迹都不满足 $P$。直觉上，安全性表示"某些坏事永远不会发生"。

LTL 中的安全性公式通常具有以下形式：
- $G \\neg \\text{bad}$：全局上坏事不发生；
- $\\phi \\rightarrow G \\neg \\text{bad}$：若 $\\phi$ 发生，则此后坏事永不发生。

**定义** (活性 / Liveness Property)
一个性质 $P$ 是活性的，当且仅当：对于任何有限前缀 $\\pi_{|n}$，都存在某个以该前缀开头的无限轨迹满足 $P$。直觉上，活性表示"某些好事最终会发生"。

LTL 中的活性公式通常具有以下形式：
- $F \\phi$：$\\phi$ 最终会发生；
- $G(\\phi \\rightarrow F \\psi)$：每当 $\\phi$ 发生时，$\\psi$ 最终会发生；
- $GF \\phi$：$\\phi$ 无限次发生。

**定理** (Safety-Liveness 分解定理)
对于任意 $\\omega$-正则语言 $L$，存在安全性语言 $L_{safe}$ 和活性语言 $L_{live}$，使得 $L = L_{safe} \\cap L_{live}$。

#### 基于 Tableau 的 LTL 模型检测 / Tableau-Based LTL Model Checking

LTL 到 Büchi 自动机的构造可通过 **tableau 方法** 系统地完成 [VardiWolper1986]。该方法将 LTL 公式 $\\phi$ 分解为一组**局部一致性约束**（local consistency constraints），每个约束对应自动机的一个状态：

**定义** (LTL 的 Tableau 节点 / Tableau Node)
一个 tableau 节点 $\\Gamma$ 是 LTL 公式的一个有限集合，满足以下局部一致性条件：
1. 若 $\\psi_1 \\land \\psi_2 \\in \\Gamma$，则 $\\psi_1 \\in \\Gamma$ 且 $\\psi_2 \\in \\Gamma$；
2. 若 $\\neg(\\psi_1 \\land \\psi_2) \\in \\Gamma$，则 $\\neg\\psi_1 \\in \\Gamma$ 或 $\\neg\\psi_2 \\in \\Gamma$；
3. 若 $X\\psi \\in \\Gamma$，则在后继节点中包含 $\\psi$；
4. 若 $\\phi \\,U\\, \\psi \\in \\Gamma$，则 $\\psi \\in \\Gamma$ 或 ($\\phi \\in \\Gamma$ 且 $X(\\phi \\,U\\, \\psi) \\in \\Gamma$)。

**Tableau 构造算法**：
1. 从初始节点 $\\Gamma_0 = \\{\\phi\\}$ 开始；
2. 反复应用分解规则，生成新的节点，直到所有节点都满足原子封闭性（即不再包含可分解的复合公式）；
3. 将每个封闭节点作为 Büchi 自动机的一个状态；
4. 对 $\\phi \\,U\\, \\psi$ 相关的节点设置接受条件：任何不经过满足 $\\psi$ 的 $U$-节点的无限路径都是不可接受的。

这一构造的时间复杂度在最坏情况下为 $O(2^{|\\phi|})$，由此也直接导出了 LTL 可满足性和模型检测问题的 **PSPACE-完全性** [SistlaClarke1985]。

"""

content = content.replace(
    "这意味着 LTL 的表达能力严格弱于 Büchi 自动机（亦即严格弱于 $\\omega$-正则语言）。例如，LTL 无法表达\"$p$ 在偶数位置成立\"这一性质，而 Büchi 自动机可以。",
    "这意味着 LTL 的表达能力严格弱于 Büchi 自动机（亦即严格弱于 $\\omega$-正则语言）。例如，LTL 无法表达\"$p$ 在偶数位置成立\"这一性质，而 Büchi 自动机可以。\n\n" + ltl_extra
)

# 2. Add CTL fixed point and labeling algorithm details after CTL semantics
ctl_extra = """#### CTL 的不动点计算与标记算法 / Fixed-Point Computation and Labeling Algorithm

CTL 的模型检测算法可以清晰地表述为**不动点迭代**。设 $S$ 为状态集，$\\llbracket \\phi \\rrbracket = \\{s \\in S \\mid \\mathcal{M}, s \\models \\phi\\}$ 为满足 $\\phi$ 的状态集合，转移关系为 $R$。

**定义** (CTL 算子的不动点刻画)
CTL 的主要时序算子可以刻画为以下不动点方程 [ClarkeEmerson1981]：

$$
\\begin{aligned}
\\llbracket EX\\phi \\rrbracket &= \\{s \\in S \\mid \\exists s'. (s, s') \\in R \\land s' \\in \\llbracket \\phi \\rrbracket\\} \\\\
\\llbracket EG\\phi \\rrbracket &= \\nu Z. \\llbracket \\phi \\rrbracket \\cap \\{s \\in S \\mid \\exists s'. (s, s') \\in R \\land s' \\in Z\\} \\\\
\\llbracket EF\\phi \\rrbracket &= \\mu Z. \\llbracket \\phi \\rrbracket \\cup \\{s \\in S \\mid \\exists s'. (s, s') \\in R \\land s' \\in Z\\} \\\\
\\llbracket E[\\phi \\,U\\, \\psi] \\rrbracket &= \\mu Z. \\llbracket \\psi \\rrbracket \\cup (\\llbracket \\phi \\rrbracket \\cap \\{s \\in S \\mid \\exists s'. (s, s') \\in R \\land s' \\in Z\\})
\\end{aligned}
$$

其中 $\\mu Z. f(Z)$ 表示最小不动点，$\\nu Z. f(Z)$ 表示最大不动点。

**标记算法 (Labeling Algorithm)**：
CTL 模型检测的经典标记算法按子公式大小自底向上地为每个状态打标签：
1. 对于原子命题 $p$，直接根据标记函数 $L$ 标记；
2. 对于布尔连接词 $\\neg, \\land, \\lor$，按集合运算处理；
3. 对于 $EX\\phi$，找出所有存在后继已标记为 $\\phi$ 的状态；
4. 对于 $EG\\phi$，通过最大不动点迭代计算所有满足 $\\phi$ 且存在无限路径保持 $\\phi$ 的状态集合；
5. 对于 $E[\\phi \\,U\\, \\psi]$，通过最小不动点迭代逐步扩展已满足 $\\psi$ 的状态，并包含其前驱中满足 $\\phi$ 的状态。

**复杂度分析**：
设 $|S|$ 为状态数，$|R|$ 为转移数，$|\\phi|$ 为公式大小。显式状态 CTL 模型检测的时间复杂度为 $O(|S| + |R|) \\cdot |\\phi|$，即关于模型大小和公式大小的乘积呈**线性增长**。这使得 CTL 模型检测具有**多项式时间复杂度**（具体为 P-完全）[ClarkeEmerson1981]。

**CTL* 简介**：
CTL* 是 LTL 和 CTL 的超集，允许路径公式中嵌套路径量词。例如，$A[(Fp) \\,U\\, (Gq)]$ 是合法的 CTL* 公式，但在 CTL 和 LTL 中都无法表达。CTL* 的模型检测复杂度为 PSPACE-完全，与 LTL 相同 [EmersonHalpern1986]。

"""

content = content.replace(
    "#### LTL 与 CTL 的表达能力对比 / Expressiveness Comparison",
    ctl_extra + "#### LTL 与 CTL 的表达能力对比 / Expressiveness Comparison"
)

# 3. Add hybrid systems to applications
hybrid_app = """### 混合系统验证 / Hybrid System Verification

时序逻辑已被扩展应用于**混合系统**（Hybrid Systems）的验证——这类系统同时包含离散状态转移和连续动态演化（如物理过程的控制器）。**混合时序逻辑**（如 TLH 和 STL）在经典时序算子基础上引入了对连续时间区间和微分约束的表达能力：

- **信号时序逻辑 (STL)**：允许公式如 $\\phi \\mathcal{U}_{[a,b]} \\psi$，表示 $\\psi$ 必须在时间区间 $[a,b]$ 内成立，且此前 $\\phi$ 一直成立；
- **航天器控制**：验证"在高度低于阈值后的 5 秒内，推进器必须点火"；
- **自动驾驶**：验证"若前车距离小于安全距离，则 0.5 秒内必须启动制动"。

这些应用展示了时序逻辑从纯离散系统向连续-离散混合系统扩展的重要方向 [BaierKatoen2008]。

"""

content = content.replace(
    "## 应用领域 / Application Domains",
    "## 应用领域 / Application Domains\n\n" + hybrid_app
)

with open("docs/06-逻辑系统/09-时序逻辑理论.md", "w", encoding="utf-8") as f:
    f.write(content)

print("09 modifications done, length:", len(content))
