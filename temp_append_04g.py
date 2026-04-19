append_text = """

### A.32 复杂度类的更多实际应用

**密码学中的计算假设**：

现代密码学的安全性基于特定的计算困难性假设。不同的密码原语依赖于不同复杂度类中的困难问题：
- **RSA**：基于整数分解的困难性（$Factoring \\in NP \\cap coNP$）。
- **椭圆曲线密码学（ECC）**：基于椭圆曲线离散对数问题。
- **格密码学（Lattice-Based Cryptography）**：基于最短向量问题（SVP）和最近向量问题（CVP），被认为是后量子密码学的主要候选。
- **全同态加密（FHE）**：基于格问题的特定变体，允许在加密数据上进行任意计算。

**优化与运筹学**：
- 线性规划（LP）属于 $P$，可以使用单纯形法、内点法或椭球法在多项式时间内解决。
- 整数线性规划（ILP）是 NP-完全的，但现代求解器（如 CPLEX、Gurobi）可以处理大规模实例。
- 旅行商问题（TSP）是 NP-困难的，但分支定界法和启发式算法（如 Lin-Kernighan）在实践中表现优异。

**人工智能与机器学习**：
- 训练神经网络的某些变体是 NP-困难的，但梯度下降等启发式方法在实践中通常能找到好的解。
- 贝叶斯网络推断是 NP-困难的（精确推断）或 #P-完全的（计数问题）。
- 强化学习中的某些规划问题是 PSPACE-完全的。

### A.33 复杂度类术语中英对照表

| 中文术语 | 英文术语 | 相关复杂度类 |
|---------|---------|-------------|
| 多项式时间 | Polynomial Time | P |
| 非确定性多项式时间 | Nondeterministic Polynomial Time | NP |
| 多项式空间 | Polynomial Space | PSPACE |
| 指数时间 | Exponential Time | EXP |
| 对数空间 | Logarithmic Space | L |
| 非确定性对数空间 | Nondeterministic Logarithmic Space | NL |
| 随机多项式时间 | Randomized Polynomial Time | BPP, RP, ZPP |
| 量子多项式时间 | Quantum Polynomial Time | BQP |
| 计数多项式时间 | Counting Polynomial Time | #P |
| 多项式层次 | Polynomial Hierarchy | PH |

### A.34 文档贡献者与致谢

本文档的编写参考了计算复杂性理论领域的经典教材和前沿论文，特别感谢以下学者的工作：
- Stephen Cook 和 Leonid Levin（NP-完全性理论）
- Richard Karp（21 个 NP-完全问题）
- Michael Sipser（教材《Introduction to the Theory of Computation》）
- Sanjeev Arora 和 Boaz Barak（教材《Computational Complexity: A Modern Approach》）
- Christos Papadimitriou（教材《Computational Complexity》）
- Andrew Yao（通信复杂度理论）
- László Babai（图同构的拟多项式时间算法）
- Manindra Agrawal, Neeraj Kayal, Nitin Saxena（AKS 素性测试）
- Hao Huang（敏感度猜想的证明）

### A.35 最终总结

本文档从基础概念出发，系统地构建了复杂度类的完整理论框架：
- **P 类**：Cobham-Edmonds 论题、强/弱多项式时间、里程碑算法（Khachiyan LP、AKS、Babai GI）。
- **NP 类**：验证器视角、证书、NP-完全分类、NPI 问题、P vs NP 障碍。
- **PSPACE 类**：TQBF、广义地理游戏、博弈论联系、Savitch 定理。
- **EXP/NEXP/EXPSPACE**：定义、完全问题、层次关系。
- **完整复杂度层次**：$L \\subseteq NL \\subseteq P \\subseteq NP \\subseteq PSPACE \\subseteq EXP \\subseteq NEXP \\subseteq EXPSPACE$。
- **归约与完全性**：多项式时间归约、各类完全问题、经典归约示例。
- **扩展主题**：随机化复杂度类、量子复杂度类、#P、参数化复杂度、交互式证明、PCP 定理、电路复杂性。

希望本文档为读者提供了一个全面、深入、系统的复杂度类学习资源。
"""

with open('docs/04-算法复杂度/04-复杂度类.md', 'a', encoding='utf-8') as f:
    f.write(append_text)
print("Appended to 04-复杂度类.md")
