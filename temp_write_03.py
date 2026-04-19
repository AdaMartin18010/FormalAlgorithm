with open('docs/04-算法复杂度/03-渐进分析.md', 'r', encoding='utf-8') as f:
    content = f.read()

insert_text = """
### 3.5 平滑分析 (Smoothed Analysis)

**定义 3.5.1**（平滑分析）[14] Spielman & Teng. Smoothed Analysis of Algorithms: Why the Simplex Algorithm Usually Takes Polynomial Time. J. ACM, 2004：

平滑分析研究算法在输入受到微小随机扰动时的性能。形式上，设 $A$ 是一个算法，$I$ 是一个输入实例，$\\sigma$ 是扰动幅度参数。算法 $A$ 在输入规模 $n$ 和扰动幅度 $\\sigma$ 下的平滑运行时间为：

$$\\text{Smoothed-Time}_A(n, \\sigma) = \\max_{I: |I| = n} \\mathbb{E}_{g \\sim \\mathcal{N}(0, \\sigma^2)} [T_A(I + g)]$$

其中 $T_A(I + g)$ 是算法 $A$ 在扰动后的输入 $I + g$ 上的运行时间，$g$ 是从均值为 0、方差为 $\\sigma^2$ 的高斯分布中抽取的随机噪声。

**平滑分析的意义**：
- 最坏情况分析可能过于悲观，因为某些"病态"输入在实际中极少出现；
- 平均情况分析依赖于特定的输入分布假设；
- 平滑分析桥接了最坏情况和平均情况：即使在最坏输入附近添加微小扰动，算法的期望运行时间也可能显著改善。

**定理 3.5.1**（单纯形法的平滑多项式时间）[14] Spielman & Teng. Smoothed Analysis of Algorithms: Why the Simplex Algorithm Usually Takes Polynomial Time. J. ACM, 2004：

对于线性规划问题，单纯形法（使用某些转轴规则）的平滑运行时间为多项式时间。具体地，对于标准形式的线性规划，使用 Gaussian 扰动的平滑时间复杂度为：

$$\\text{Smoothed-Time} = O(n^4 \\sigma^{-2} \\log^{O(1)} n)$$

其中 $n$ 是变量数，$\\sigma$ 是扰动幅度。

**历史意义**：
- Spielman 和 Teng 的平滑分析解释了为什么单纯形法在实践中表现优异，尽管其在最坏情况下是指数时间的（Klee-Minty 例子）。
- 这一工作为 Spielman 和 Teng 赢得了 2008 年的 Gödel 奖和 2022 年的 Nevanlinna 奖（Teng）及 2023 年的 ACM Turing 奖提名贡献。

**平滑分析在其他问题中的应用**：
- **k-均值聚类**：平滑分析证明了 k-均值算法在平滑输入下具有多项式期望运行时间。
- **局部搜索算法**：许多局部搜索启发式算法在平滑分析下被证明具有多项式时间性能。
- **数值线性代数**：矩阵求逆和特征值计算的平滑分析给出了更好的条件数估计。

### 3.6 摊还分析 (Amortized Analysis)

**定义 3.6.1**（摊还分析）[15] Tarjan. Amortized Computational Complexity. SIAM J. Algebraic Discrete Methods, 1985：

摊还分析研究一系列操作的总成本，而不是单个操作的最坏情况成本。它给出了每个操作的"平均"成本上界，但这个平均不是基于概率的，而是基于操作序列的结构性特征。

**三种主要的摊还分析方法**：

#### 3.6.1 聚合分析 (Aggregate Analysis)

**方法**：直接计算 $n$ 个操作的总成本 $T(n)$，则每个操作的摊还成本为 $T(n)/n$。

**例子：栈操作**
- 假设栈支持 `PUSH`、`POP` 和 `MULTIPOP`（弹出 $k$ 个元素）。
- 每个元素最多被压入和弹出各一次。
- 因此 $n$ 个操作的总成本为 $O(n)$，每个操作的摊还成本为 $O(1)$。

#### 3.6.2 记账方法 (Accounting Method)

**方法**：为每个操作分配一个"摊还成本"，可能高于或低于其实际成本。当操作的摊还成本高于实际成本时，差额作为"信用"（credit）存储在数据结构的特定对象上；当后续操作的实际成本高于摊还成本时，使用之前存储的信用支付差额。

**约束条件**：任何时候，数据结构中存储的总信用必须非负。

**例子：二进制计数器**
- 将一个二进制计数器从 0 递增到 $n$。
- 为 `INCREMENT` 操作分配摊还成本 2。
- 每次 `INCREMENT` 翻转一个 0 为 1（实际成本的一部分），存储 1 单位信用在该位上。
- 当该位从 1 翻转为 0 时，使用存储的信用支付成本。
- $n$ 次递增的总摊还成本为 $O(n)$。

#### 3.6.3 势能方法 (Potential Method)

**方法**：定义一个势能函数 $\\Phi$，将数据结构的状态映射到一个实数（势能）。操作 $i$ 的摊还成本定义为：

$$\\hat{c}_i = c_i + \\Phi(D_i) - \\Phi(D_{i-1})$$

其中 $c_i$ 是实际成本，$D_i$ 是第 $i$ 个操作后的数据结构状态。

**约束条件**：势能函数必须满足 $\\Phi(D_i) \\geq \\Phi(D_0)$ 对所有 $i$ 成立（通常取 $\\Phi(D_0) = 0$）。

**例子：动态表（Dynamic Table）**
- 当表满时，分配一个两倍大小的表并将所有元素复制过去。
- 定义势能 $\\Phi(T) = 2 \\cdot \\text{num}[T] - \\text{size}[T]$。
- `TABLE-INSERT` 的摊还成本为 $O(1)$。
- 即使在扩展表的"昂贵"操作中，摊还成本仍然是 $O(1)$。

**定理 3.6.1**（动态表的插入摊还成本）[15] Tarjan. Amortized Computational Complexity. SIAM J. Algebraic Discrete Methods, 1985：

对于支持扩展（但不支持收缩）的动态表，连续 $n$ 次 `INSERT` 操作的总成本为 $O(n)$，每次操作的摊还成本为 $O(1)$。

**定理 3.6.2**（带收缩的动态表）[13] Cormen et al. Introduction to Algorithms (4th ed.). MIT Press, 2022：

对于支持扩展和收缩的动态表（使用负载因子阈值 $1/4$ 触发收缩），`INSERT` 和 `DELETE` 的摊还成本均为 $O(1)$。

### 3.7 概率分析 (Probabilistic Analysis)

**定义 3.7.1**（概率分析）[13] Cormen et al. Introduction to Algorithms (4th ed.). MIT Press, 2022：

概率分析研究算法在随机输入上的期望运行时间。与摊还分析不同，概率分析明确假设输入服从某种概率分布。

**典型应用场景**：
- **快速排序的平均情况**：假设输入排列均匀随机，快速排序的期望比较次数为 $O(n \\log n)$。
- **哈希表的期望查询时间**：在简单均匀哈希假设下，链地址法的期望查询时间为 $O(1 + \\alpha)$，其中 $\\alpha$ 是负载因子。
- **随机化算法的分析**：概率分析是分析 Las Vegas 算法和 Monte Carlo 算法的核心工具。

**定理 3.7.1**（快速排序的期望比较次数）[13] Cormen et al. Introduction to Algorithms (4th ed.). MIT Press, 2022：

对于 $n$ 个互异元素的随机排列，快速排序的期望比较次数为 $2n \\ln n + O(n) \\approx 1.39 n \\log_2 n$。

**证明概要**：
- 设 $X$ 为总比较次数。
- 定义指示随机变量 $X_{ij} = I\\{z_i \\text{ 与 } z_j \\text{ 被比较}\\}$。
- 由于输入是随机排列，$z_i$ 和 $z_j$ 被比较当且仅当它们是子数组 $Z_{ij}$ 中第一个被选为枢轴的元素。
- $P(X_{ij} = 1) = 2/(j - i + 1)$。
- 因此：

$$E[X] = \\sum_{i=1}^{n-1} \\sum_{j=i+1}^n \\frac{2}{j-i+1} = \\sum_{k=1}^{n-1} \\frac{2(n-k)}{k+1} = 2n \\sum_{k=1}^{n-1} \\frac{1}{k+1} - 2\\sum_{k=1}^{n-1} \\frac{k}{k+1} = 2n \\ln n + O(n)$$

**定理 3.7.2**（生日悖论的算法分析）[13] Cormen et al. Introduction to Algorithms (4th ed.). MIT Press, 2022：

在 $n$ 个独立均匀随机的元素中，出现碰撞的期望时间为 $\\Theta(\\sqrt{n})$。这一分析是许多随机化算法（如 Pollard's rho 算法）的基础。

**概率分析与最坏情况分析的对比**：

| 分析类型 | 假设 | 典型结果 | 应用场景 |
|---------|------|---------|---------|
| 最坏情况 | 无 | $O(n^2)$（快速排序） | 实时系统、安全关键系统 |
| 平均情况 | 输入均匀随机 | $O(n \\log n)$（快速排序） | 通用算法设计 |
| 摊还分析 | 操作序列的结构 | $O(1)$（动态表插入） | 数据结构分析 |
| 平滑分析 | 输入有微小扰动 | 多项式时间（单纯形法） | 实际性能解释 |
| 概率分析 | 输入随机分布 | 期望 $O(n \\log n)$（快速排序） | 随机化算法、哈希表 |

"""

marker = "### 3.4 动态规划分析 (Dynamic Programming Analysis)\n\n> 💻 **代码示例引用**：排序算法与动态规划的实现示例及复杂度分析可参见"

if marker in content:
    parts = content.split(marker, 1)
    # Find the end of section 3.4
    next_section_marker = "## 4. 渐进分析应用 (Applications of Asymptotic Analysis)"
    if next_section_marker in parts[1]:
        subparts = parts[1].split(next_section_marker, 1)
        new_content = parts[0] + marker + subparts[0] + insert_text + next_section_marker + subparts[1]
        with open('docs/04-算法复杂度/03-渐进分析.md', 'w', encoding='utf-8') as f:
            f.write(new_content)
        print("Updated 03-渐进分析.md successfully")
    else:
        print("Could not find section 4 marker")
else:
    print("Could not find section 3.4 marker")
