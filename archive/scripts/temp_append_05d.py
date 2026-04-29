append_text = """

### A.21 通信复杂度与 VC 维度的联系

**定义 A.21.1**（VC 维度）[3] Rao & Yehudayoff. Communication Complexity and Applications. Cambridge University Press, 2020：

对于一个集合族 $\\mathcal{F} \\subseteq 2^X$，其 VC 维度是最大的 $d$，使得存在大小为 $d$ 的子集 $S \\subseteq X$ 可以被 $\\mathcal{F}$ "打散"（shatter）。

**定理 A.21.1**（Sauer-Shelah 引理）[3] Rao & Yehudayoff. Communication Complexity and Applications. Cambridge University Press, 2020：

若集合族 $\\mathcal{F}$ 的 VC 维度为 $d$，则对于任何大小为 $n$ 的集合 $X$：

$$|\\mathcal{F}| \\leq \\sum_{i=0}^{d} \\binom{n}{i} = O(n^d)$$

**与通信复杂度的联系**：对于某些函数类（如半空间指示函数），VC 维度可以用来限制学习这些函数所需的样本复杂度，进而与通信复杂度产生联系。在分布式学习场景中，通信复杂度下界可以通过 VC 维度和信息论方法联合证明。

### A.22 带限制的通信模型

**单向通信复杂度（One-Way Communication Complexity）** [2] Kushilevitz & Nisan. Communication Complexity. Cambridge University Press, 1997：

在单向模型中，只有 Alice 可以向 Bob 发送消息，Bob 不能回复。单向确定性通信复杂度记为 $D^{\\rightarrow}(f)$。

**定理 A.22.1** [2] Kushilevitz & Nisan. Communication Complexity. Cambridge University Press, 1997：

对于 $INDEX_n$ 问题：

$$D^{\\rightarrow}(INDEX_n) = n$$

因为 Alice 必须发送足够多的信息让 Bob 知道所有 $n$ 个位中的任意一个。

**同步轮数限制模型**：

在某些分布式模型中，通信复杂度不仅受总比特数限制，还受同步轮数限制。例如，$r$-轮通信复杂度 $D_r(f)$ 限制协议最多进行 $r$ 轮交互。对于许多问题，$D_r(f)$ 随 $r$ 增加而减小，最终收敛到 $D(f)$。

### A.23 通信复杂度在机器学习中的应用

**分布式学习中的梯度压缩** [3] Rao & Yehudayoff. Communication Complexity and Applications. Cambridge University Press, 2020：

在分布式随机梯度下降（SGD）中，$p$ 个工作节点需要每轮将梯度向量发送到参数服务器。对于 $d$-维梯度，原始通信量为 $O(p \\cdot d)$ 位每轮。通过梯度量化、稀疏化或低秩近似，可以将通信量压缩到 $O(p \\cdot d / k)$ 位（$k$ 是压缩因子），但信息论分析表明：若要求平均梯度的 $\\epsilon$-近似，通信量至少为 $\\Omega(p \\cdot d \\log(1/\\epsilon) / k)$ 位每轮。

**联邦学习中的通信下界** [3] Rao & Yehudayoff. Communication Complexity and Applications. Cambridge University Press, 2020：

在联邦学习中，客户端数据是私有的，不能直接共享。通信复杂度分析表明，在某些非凸优化问题中，达到 $\\epsilon$-稳定点需要的总通信量为 $\\Omega(1/\\epsilon^2)$ 位（对于平滑非凸目标函数）。
"""

with open('docs/04-算法复杂度/05-通信复杂度.md', 'a', encoding='utf-8') as f:
    f.write(append_text)
print("Appended to 05-通信复杂度.md")
