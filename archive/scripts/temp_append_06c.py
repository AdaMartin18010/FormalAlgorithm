append_text = """

### A.19 决策树与电路复杂性的更多联系

**定理 A.19.1**（决策树与 $DNF$ 大小的关系）[5] Buhrman & de Wolf. Complexity Measures and Decision Tree Complexity: A Survey. Theor. Comput. Sci., 2002：

对于布尔函数 $f$，设 $dnf(f)$ 是表示 $f$ 的最小 $DNF$ 公式的大小。则：

$$dnf(f) \\leq 2^{D(f)}$$

且：

$$D(f) \\leq O(\\log dnf(f) \\cdot \\log n)$$

**证明概要**：
- 任何深度为 $D(f)$ 的决策树有至多 $2^{D(f)}$ 个叶子。
- 每个叶子对应一个项（term），所有 1-叶子的 OR 构成一个 $DNF$。
- 反过来，给定一个大小为 $s$ 的 $DNF$，可以通过二分搜索在 $O(\\log s)$ 深度内找到一个满足的项，但需要额外的 $O(\\log n)$ 因子来确定哪个文字被满足。

### A.20 信息论方法在通信复杂度中的交叉应用

**定理 A.20.1**（信息复杂度与通信矩阵的熵）[1] Cover & Thomas. Elements of Information Theory (2nd ed.). Wiley-Interscience, 2006：

对于函数 $f: X \\times Y \\rightarrow Z$ 和输入分布 $\\mu$，通信协议 $\\pi$ 的 transcript $\\Pi$ 满足：

$$I(X; \\Pi | Y) + I(Y; \\Pi | X) \\leq |\\Pi|$$

其中 $|\\Pi|$ 是 transcript 的期望长度。这表明内部信息复杂度不会超过通信复杂度。

**应用**：这一不等式是信息复杂度方法证明通信下界的基础。对于 $DISJ_n$，若可以证明 $I(X; \\Pi | Y) + I(Y; \\Pi | X) = \\Omega(n)$，则直接得到 $R(DISJ_n) = \\Omega(n)$。

### A.21 近似次数与电路下界

**定理 A.21.1**（$AC^0$ 函数的近似次数）[5] Buhrman & de Wolf. Complexity Measures and Decision Tree Complexity: A Survey. Theor. Comput. Sci., 2002：

对于深度为 $d$、规模为 $S$ 的 $AC^0$ 电路计算的函数 $f$，其近似次数满足：

$$\\widetilde{\\deg}(f) = O(\\log S)^{O(d)}$$

**推论**：对于 $PARITY_n$（不在 $AC^0$ 中），任何 $AC^0$ 电路需要指数级规模。

这是因为 $\\widetilde{\\deg}(PARITY_n) = n$，而 $AC^0$ 电路只能计算低近似次数的函数。

### A.22 数据结构的熵下界

**定理 A.22.1**（静态字典的空间下界）[1] Cover & Thomas. Elements of Information Theory (2nd ed.). Wiley-Interscience, 2006：

存储 $n$ 个来自全集 $U$（$|U| = m$）的元素的静态字典，支持成员查询（membership query），所需的最小空间为至少：

$$\\log_2 \\binom{m}{n} = n \\log_2(m/n) + O(n)$$

**信息论解释**：从 $m$ 个元素中选择 $n$ 个元素有 $\\binom{m}{n}$ 种可能。要区分所有这些可能性，存储结构必须至少编码 $\\log_2 \\binom{m}{n}$ 位的信息。

**与 Bloom Filter 的比较**：Bloom Filter 使用约 $1.44 n \\log_2(1/\\epsilon)$ 位空间，允许误报率 $\\epsilon$。当 $m/n = 1/\\epsilon$ 时，Bloom Filter 的空间与信息论下界 $n \\log_2(m/n)$ 相差约 1.44 倍的常数因子，这在实践中是非常高效的。

### A.23 排序下界的变体

**定理 A.23.1**（部分排序的下界）[13] Cormen et al. Introduction to Algorithms (4th ed.). MIT Press, 2022：

若只需要找出 $n$ 个元素中的第 $k$ 小元素（选择问题），任何基于比较的算法至少需要 $n + \\min(k, n - k + 1) - 2$ 次比较（下界），且存在算法可以在 $3n + o(n)$ 次比较内完成（上界）。

**中位数问题的精确复杂度**：

找中位数（$k = \\lceil n/2 \\rceil$）的比较复杂度为 $\\Theta(n)$。更精确地：
- 下界：$3n/2 - O(1)$ 次比较
- 上界：$3n + o(n)$ 次比较（复杂算法）
- 实用算法：Quickselect 平均 $O(n)$，最坏 $O(n^2)$

### A.24 几何问题的信息论下界

**定理 A.24.1**（点定位的决策树下界）[3] Ben-Or. Lower Bounds for Algebraic Computation Trees. STOC, 1983：

给定平面上 $n$ 条直线划分出的平面细分，对于点定位问题（判断查询点位于哪个区域），任何代数决策树算法需要 $\\Omega(\\log n)$ 次查询。

**证明概要**：平面细分有 $n^2$ 个区域（在一般位置下）。查询点可能位于 $n^2$ 个区域中的任何一个，因此决策树至少需要 $\\log_2(n^2) = 2\\log_2 n$ 个叶子，深度至少为 $\\Omega(\\log n)$。

这与 $O(\\log n)$ 时间的点定位数据结构（如梯形图、KD-tree）的上界匹配。

### A.25 推荐阅读

**信息论教材**：
1. [1] Cover & Thomas. Elements of Information Theory (2nd ed.). Wiley-Interscience, 2006.
2. [12] Li & Vitányi. An Introduction to Kolmogorov Complexity and Its Applications (3rd ed.). Springer, 2008.

**决策树与查询复杂度**：
3. [5] Buhrman & de Wolf. Complexity Measures and Decision Tree Complexity: A Survey. Theor. Comput. Sci., 2002.
4. [7] Nisan & Szegedy. On the Degree of Boolean Functions as Real Polynomials. Comput. Complex., 1994.
5. [8] Huang. Induced Subgraphs of Hypercubes and a Proof of the Sensitivity Conjecture. Annals of Mathematics, 2019.

**算法教材**：
6. [13] Cormen et al. Introduction to Algorithms (4th ed.). MIT Press, 2022.
7. [14] Knuth. The Art of Computer Programming, Volume 3: Sorting and Searching (2nd ed.). Addison-Wesley, 1998.
"""

with open('docs/04-算法复杂度/06-信息论下界.md', 'a', encoding='utf-8') as f:
    f.write(append_text)
print("Appended to 06-信息论下界.md")
