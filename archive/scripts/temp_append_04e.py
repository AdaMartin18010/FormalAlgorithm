append_text = """

### A.25 复杂度类之间的更多已知关系

**定理 A.25.1**（Karp-Lipton 定理）[1] Arora & Barak. Computational Complexity: A Modern Approach. Cambridge University Press, 2009：

若 $NP \\subseteq P/poly$（即 NP 中的所有问题都有多项式大小的电路族），则：

$$PH = \\Sigma_2^P$$

这意味着如果 NP 问题可以被多项式大小电路解决，整个多项式层次都会坍塌到第二层。

**定理 A.25.2**（Sipser-Gács-Lautemann 定理）[1] Arora & Barak. Computational Complexity: A Modern Approach. Cambridge University Press, 2009：

$$BPP \\subseteq \\Sigma_2^P \\cap \\Pi_2^P$$

这表明即使随机化带来了额外的计算能力，BPP 仍然包含在多项式层次的较低层中。

**定理 A.25.3**（Adleman 定理）[1] Arora & Barak. Computational Complexity: A Modern Approach. Cambridge University Press, 2009：

$$BPP \\subseteq P/poly$$

即 BPP 中的任何问题都可以被多项式大小的电路族解决。这与 $P \\subseteq P/poly$ 一致，但 $BPP \\subseteq P$ 是否成立仍是未知的。

**定理 A.25.4**（Stockmeyer 定理）[5] Papadimitriou. Computational Complexity. Addison-Wesley, 1994：

$\\Sigma_2^P$ 包含 $NP^{NP}$，即带有 NP 预言机的非确定性多项式时间。更一般地：

$$\\Sigma_k^P = NP^{\\Sigma_{k-1}^P}$$

**定理 A.25.5**（Toda 定理的推论）[5] Papadimitriou. Computational Complexity. Addison-Wesley, 1994：

$$PH \\subseteq P^{#P}$$

且实际上可以证明 $PH \\subseteq BPP^{NP} \\subseteq P^{#P}$。

### A.26 复杂度类学习中的常见误区

**误区 1：$P$ 中的所有问题都很容易**

$P$ 只是表示问题可以在多项式时间内解决，但多项式的次数可能很高。例如，$O(n^{100})$ 的算法在理论上属于 $P$，但在实际中对于任何合理大小的输入都是不可行的。

**误区 2：$NP$-完全问题没有任何多项式时间算法**

$NP$-完全问题目前没有在 $P$ 中的算法（若 $P \\neq NP$），但：
- 对于特定输入分布，$NP$-完全问题可能很容易；
- 近似算法可以在多项式时间内找到接近最优的解；
- 参数化算法可以在固定参数较小时高效运行；
- 启发式算法和 SAT 求解器在实践中往往能处理大规模实例。

**误区 3：量子计算可以解决所有 $NP$ 问题**

目前没有证据表明 $NP \\subseteq BQP$。虽然 Shor 算法在整数分解和离散对数问题上提供了指数级加速，但这些问题的复杂度位置（$NP \\cap coNP$）与一般的 $NP$-完全问题不同。对于 $NP$-完全问题（如 SAT、TSP），量子计算目前只能提供多项式级或次多项式级的加速（通过 Grover 搜索的二次加速）。

**误区 4：$P = NP$ 只影响理论计算机科学**

若 $P = NP$，其影响将远远超出理论计算机科学：
- 现代密码学（RSA、椭圆曲线密码）将变得不安全；
- 数学定理的自动证明将变得高效；
- 许多工业优化问题（物流、调度、资源配置）将可以被精确解决；
- 机器学习中的许多推断问题将变得容易。

### A.27 推荐阅读路径

**入门教材**：
1. [2] Sipser, M. Introduction to the Theory of Computation (3rd ed.). Cengage Learning, 2012.
   - 最佳入门教材，清晰地介绍了 P、NP、PSPACE 等基本概念。

**进阶教材**：
2. [5] Papadimitriou, C. H. Computational Complexity. Addison-Wesley, 1994.
   - 经典教材，深入讨论各种复杂度类和归约技术。
3. [1] Arora, S., & Barak, B. Computational Complexity: A Modern Approach. Cambridge University Press, 2009.
   - 现代综合教材，涵盖 PCP 定理、电路复杂性、量子计算等前沿主题。

**专题阅读**：
4. [12] Agrawal, Kayal, & Saxena. PRIMES is in P. Annals of Mathematics, 2004.
5. [13] Babai, L. Graph Isomorphism in Quasipolynomial Time. arXiv:1512.03547, 2015.
6. [14] Spielman & Teng. Smoothed Analysis of Algorithms. J. ACM, 2004.
7. [15] Razborov & Rudich. Natural Proofs. J. Comput. Syst. Sci., 1997.

### A.28 文档更新日志

- **v2.0 (2026-04-16)**：全面深化 P 类分析（Cobham-Edmonds 论题、强/弱多项式时间、Khachiyan LP、AKS 素性测试、Babai 图同构）；扩展 NP 类分析（验证器视角、证书、NP-完全分类、NPI 问题）；深化 PSPACE 分析（TQBF、广义地理游戏、博弈论）；补充完整复杂度层次 $L \\subseteq NL \\subseteq P \\subseteq NP \\subseteq PSPACE \\subseteq EXP \\subseteq NEXP \\subseteq EXPSPACE$；统一引用格式为 `[N] Author. Title. Venue/Publisher, Year.`；新增扩展内容（随机化复杂度类、量子复杂度类、#P、参数化复杂度、交互式证明、PCP 定理、电路复杂性等）。
- **v1.1 (2025-01-11)**：基础框架，包含 P、NP、PSPACE、EXP 的基本定义和关系。
"""

with open('docs/04-算法复杂度/04-复杂度类.md', 'a', encoding='utf-8') as f:
    f.write(append_text)
print("Appended to 04-复杂度类.md")
