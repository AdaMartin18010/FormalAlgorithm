import os

def append_before_footer(path, new_content):
    with open(path, "r", encoding="utf-8") as f:
        content = f.read()
    footer = "*本文档严格遵循数学形式化规范"
    if footer in content:
        idx = content.find(footer)
        content = content[:idx] + new_content + "\n" + content[idx:]
    else:
        alt_footer = "*本文档介绍了启发式算法的核心理论"
        if alt_footer in content:
            idx = content.find(alt_footer)
            content = content[:idx] + new_content + "\n" + content[idx:]
        else:
            content = content.rstrip() + "\n\n" + new_content
    with open(path, "w", encoding="utf-8") as f:
        f.write(content)
    print("Updated " + path)

appendix_01 = """
## 7. 深度主题：摊还分析、缓存优化与I/O高效算法

### 7.1 摊还分析
**定义 7.1.1** (摊还分析) 摊还分析求取一个操作序列中每个操作的平均时间开销，其中某些操作可能代价高昂，但很少发生 [1]。

**定义 7.1.2** (聚合分析) 对 n 个操作的序列，总时间为 T(n)，则每个操作的摊还代价为 T(n)/n [1]。

**定义 7.1.3** (核算法 / Accounting Method) 为每个操作预先分配摊还代价，低价操作产生的信用用于支付后续高价操作 [1]。

**定义 7.1.4** (势能法 / Potential Method) 定义一个势函数 Phi，将操作代价与数据结构状态关联：摊还代价 = 实际代价 + Delta(Phi) [1]。

**定理 7.1.1** (动态表扩展) 对一个以翻倍策略扩展的表，n 次插入的总实际代价为 O(n)，因此每次插入的摊还代价为 O(1) [1]。
证明（势能法）：设 Phi(T) = 2 * num(T) - size(T)。当表满时触发扩展，实际代价为 num(T)，势能增加量恰好抵消复制开销，得出摊还代价 <= 3。

### 7.2 缓存友好与缓存无关算法
**定义 7.2.1** (缓存友好算法) 显式利用缓存块大小 B 和缓存容量 M 以最小化缓存未命中的算法 [2]。

**定义 7.2.2** (缓存无关算法 / Cache-Oblivious) 在不显式知道 B 和 M 的情况下，对任意层次缓存都达到渐进最优缓存复杂度的算法 [2]。

**定理 7.2.1** (缓存无关矩阵转置) 使用分块递归策略的缓存无关矩阵转置仅产生 O(n^2 / B) 缓存未命中 [2]。

**定理 7.2.2** (Funnelsort) 缓存无关的 Funnelsort 排序 n 个元素需要 O((n/B) log_{M/B} (n/B)) 次缓存未命中，与缓存感知下界匹配 [2]。

### 7.3 外部存储器模型与 I/O 高效算法
**定义 7.3.1** (外部存储器模型 / EM Model) 由 Aggarwal 与 Vitter 提出：主存容量为 M，每次 I/O 传输 B 个连续元素 [3]。

**定理 7.3.1** (EM 排序下界) 在 EM 模型中，排序 n 个元素需要 Omega((n/B) log_{M/B} (n/B)) 次 I/O [3]。

**定理 7.3.2** (EM 矩阵乘法) 在 EM 模型中，O(n^3) 运算的标准矩阵乘法可被重新组织为分块算法，产生 O(n^3 / (B sqrt(M))) 次 I/O [3]。

### 7.4 循环展开与顺序访问模式
**定义 7.4.1** (循环展开) 通过复制循环体减少循环控制开销并增加指令级并行的编译器或手工优化技术 [4]。

**定理 7.4.1** (顺序访问最优性) 对数组的连续顺序扫描在缓存模型中具有最小的每元素 I/O 代价：每 B 个元素仅产生 1 次未命中 [2][3]。

## 参考文献（补充）

- [1] Cormen, T. H., et al. (2022). Introduction to Algorithms (4th ed.). MIT Press.
- [2] Frigo, M., Leiserson, C. E., Prokop, H., & Ramachandran, S. (1999). Cache-oblivious algorithms. FOCS, 285-297.
- [3] Aggarwal, A., & Vitter, J. S. (1988). The input/output complexity of sorting and related problems. CACM, 31(9), 1116-1127.
- [4] Hennessy, J. L., & Patterson, D. A. (2019). Computer Architecture: A Quantitative Approach (6th ed.). Morgan Kaufmann.
- [5] Sanders, P., Mehlhorn, K., Dietzfelbinger, M., & Dementiev, R. (2019). Sequential and Parallel Algorithms and Data Structures. Springer.
"""

appendix_02 = """
## 9. 深度主题：并行复杂度类、负载均衡与前沿进展

### 9.1 并行复杂度类 NC 与 AC
**定义 9.1.1** (NC 类) NC 是可在多对数时间 (polylogarithmic time) 内由多项式数量处理器解决的问题类 [1]：
NC = Union_{k>=1} NC^k，其中 NC^k 使用 O(log^k n) 时间与 n^{O(1)} 个处理器。

**定义 9.1.2** (AC 类) AC 是可由多项式规模、常数深度、无界扇入门电路解决的问题类 [1]：
AC = Union_{k>=0} AC^k。已知 AC^0 subset NC^1 subset AC^1 = NC^2 subset ...

**定理 9.1.1** (PRAM 与电路等价) 在 CREW-PRAM 上于 O(log^k n) 时间使用多项式处理器可解的问题类恰好是 NC^k [1]。

**定理 9.1.2** (P-完全性) 若任一 P-完全问题属于 NC，则 P = NC。电路求值问题 (Circuit Value Problem) 是 P-完全的 [1]。

### 9.2 负载均衡与工作窃取
**定义 9.2.1** (静态负载均衡) 在运行前将任务映射到处理器，常用方法包括轮询、块划分与 LPT (Longest Processing Time first) [2]。

**定理 9.2.1** (LPT 近似比) 对 n 个独立任务与 p 个相同处理器，LPT 的 makespan 不超过最优值的 4/3 [2]。

**定义 9.2.2** (工作窃取 / Work Stealing) 空闲处理器从繁忙处理器的双端队列尾部窃取任务 [3]。

**定理 9.2.2** (工作窃取效率) [3] 对总工作量 T_1 与关键路径长度 T_infty，p 处理器上的期望运行时间为 O(T_1/p + T_infty)。
证明要点：每次成功的窃取减少一个尚未被执行的子树；期望窃取次数为 O(p * T_infty)。

### 9.3 GPU 优化与无锁数据结构
**定义 9.3.1** (SIMT 执行模型) GPU 采用单指令多线程模型，同一 warp 内线程执行相同指令但操作不同数据 [4]。

**定理 9.3.1** (合并访问) 若一个 warp 的线程访问全局内存中的连续地址，则硬件将这些访问合并为最少次数的事务，最大化带宽 [4]。

**定义 9.3.2** (无锁数据结构) 不依赖互斥锁即可保证系统级进展的数据结构 [5]。

**定理 9.3.2** (无锁栈) 使用比较-交换 (CAS) 实现的无锁栈支持 push/pop 的 O(1) 摊还步复杂度，并保证至少有一个线程在有限步内完成操作 [5]。

## 参考文献（补充）

- [1] JaJa, J. (1992). Introduction to Parallel Algorithms. Addison-Wesley.
- [2] Graham, R. L. (1969). Bounds on multiprocessing timing anomalies. SIAM J. Appl. Math., 17(2), 416-429.
- [3] Blumofe, R. D., & Leiserson, C. E. (1999). Scheduling multithreaded computations by work stealing. J. ACM, 46(5), 720-748.
- [4] Nvidia. (2024). CUDA C Programming Guide. docs.nvidia.com.
- [5] Herlihy, M., & Shavit, N. (2012). The Art of Multiprocessor Programming. Morgan Kaufmann.
"""

appendix_03 = """
## 9. 深度主题：分布式图算法、一致性与容错

### 9.1 消息传递模型的形式化
**定义 9.1.1** (同步网络) 在同步消息传递网络中，第 r 轮发送的所有消息在第 r+1 轮开始前被交付 [1]。

**定义 9.1.2** (异步网络) 消息传递时间有限但无上界，局部计算瞬间完成 [1]。

**定理 9.1.1** (FLP 不可能性) [2] 在异步网络中，即使只有一个进程可能故障，确定性共识算法也无法同时满足终止性与一致性。

**定义 9.1.3** (部分同步) 存在未知上界 Delta 的消息延迟与未知上界 Phi 的相对处理器速度 [1]。

**定理 9.1.2** (Dwork-Lynch-Stockmeyer) [1] 在部分同步假设下，若故障进程数 f < n/3，则拜占庭容错共识可在多项式时间内达成。

### 9.2 分布式图算法
**定义 9.2.1** (分布式 MST) 在消息传递网络中，每个节点仅知晓邻居信息，协同计算最小生成树 [1]。

**定理 9.2.1** (GHS 算法) [1] Gallager-Humblet-Spira 分布式 MST 算法在最坏情况下具有 O(n log n) 的消息复杂度与时间复杂度。

**定理 9.2.2** (MST 下界) [1] 任何分布式 MST 算法在最坏情况下至少需要 Omega(n log n) 条消息。

**定义 9.2.2** (分布式最短路径) 每个节点维护到所有其他节点的距离向量，并与邻居交换更新 [1]。

**定理 9.2.3** 在同步网络中，分布式 Bellman-Ford 算法在至多 n-1 轮内收敛。

**定义 9.2.3** (分布式图着色) 每个节点仅使用局部信息选择一种与所有邻居不同的颜色 [1]。

**定理 9.2.4** (Linial) [1] 在 LOCAL 模型中，可使用 O(log* n) 轮计算出一个合适的 O(Delta^2) 着色，其中 Delta 为最大度数。

### 9.3 CAP 定理与一致性
**定理 9.3.1** (CAP 定理) [3] 分布式数据存储不可能同时保证一致性 (Consistency)、可用性 (Availability) 与分区容错性 (Partition Tolerance) 中的超过两项。

**定义 9.3.1** (拜占庭将军问题) 一组将军必须就共同作战计划达成一致，但部分将军可能是叛徒并发送矛盾消息 [4]。

**定理 9.3.2** (Lamport-Shostak-Pease) [4] 拜占庭将军问题可解当且仅当 n >= 3f + 1，其中 f 为叛徒数。

### 9.4 故障检测与状态机复制
**定义 9.4.1** (故障检测器) 分布式系统中用于检测节点故障的组件。类别包括：完美型、最终完美型、弱型 [1]。

**定义 9.4.2** (状态机复制) 通过在所有非故障节点上以相同顺序执行相同操作序列来保证状态一致 [1]。

**定理 9.4.1** 若所有非故障节点按相同顺序执行相同的确定性状态转移，则它们将保持相同状态。

### 9.5 前沿进展：区块链共识与联邦学习
**定义 9.5.1** (权益证明 / PoS) 以太坊在 The Merge 后采用的共识机制，通过经济质押替代工作量证明 [5]。

**定理 9.5.1** (HotStuff) [5] 基于部分同步假设的 BFT 共识协议，具有线性通信复杂度与响应性。

**定义 9.5.2** (联邦学习) 在去中心化设备上协同训练机器学习模型，而不直接共享原始数据 [6]。

**定理 9.5.2** (FedAvg 收敛) [6] 在适当的学习率与数据分布假设下，联邦平均 (FedAvg) 可收敛到局部最优。

## 参考文献（补充）

- [1] Lynch, N. A. (1996). Distributed Algorithms. Morgan Kaufmann.
- [2] Fischer, M. J., Lynch, N. A., & Paterson, M. S. (1985). Impossibility of distributed consensus with one faulty process. J. ACM, 32(2), 374-382.
- [3] Gilbert, S., & Lynch, N. (2012). Brewers conjecture and the feasibility of consistent, available, partition-tolerant web services. ACM SIGACT News, 33(2), 51-59.
- [4] Lamport, L., Shostak, R., & Pease, M. (1982). The Byzantine generals problem. ACM TOPLAS, 4(3), 382-401.
- [5] Yin, M., et al. (2019). HotStuff: BFT consensus in the lens of blockchain. SOSP, 56-68.
- [6] McMahan, B., et al. (2017). Communication-efficient learning of deep networks from decentralized data. AISTATS, 1273-1282.
"""

appendix_04 = """
## 11. 深度主题：启发式分类学、近似保证、收敛理论与神经组合优化

### 11.1 启发式分类学
**定义 11.1.1** (局部搜索) 从初始解出发，在其邻域中迭代寻找更优解的启发式方法 [1]。

**定义 11.1.2** (爬山法 / Hill Climbing) 仅接受改进邻居的局部搜索；容易陷入局部最优 [1]。

**定义 11.1.3** (禁忌搜索 / Tabu Search) [2] 使用禁忌表与长期记忆机制避免循环并引导搜索离开局部最优。

**定义 11.1.4** (粒子群优化 / PSO) [3] 模拟鸟群/鱼群社会行为的随机优化技术。速度更新公式：
v_i(t+1) = w v_i(t) + c1 r1 (pbest_i - x_i) + c2 r2 (gbest - x_i)

**定义 11.1.5** (蚁群优化 / ACO) [4] 受蚂蚁觅食行为启发，通过信息素正反馈引导解的构造。

**定义 11.1.6** (超启发式 / Hyper-Heuristic) [5] 在元层次上自动选择或生成低层启发式的方法，旨在实现跨域优化。

### 11.2 近似保证与概率界
**定义 11.2.1** (近似比) 对最小化问题，算法 A 的近似比为 rho = sup_I (A(I) / OPT(I)) [6]。

**定理 11.2.1** (Johnson TSP 界) [6] 对欧几里得 TSP，最近邻启发式的近似比为 Theta(log n)。

**定理 11.2.2** (随机实例下的概率近似) 对某些随机分布的实例，简单构造启发式的期望近似比趋近于 1 [6]。

### 11.3 收敛理论
**定义 11.3.1** (马尔可夫链模型) 进化算法的状态演化可建模为种群空间上的马尔可夫链 [7]。

**定理 11.3.1** (GA 收敛) [7] 包含变异、交叉与选择的规范遗传算法在代数趋于无穷时以概率 1 收敛到全局最优。

**定理 11.3.2** (SA 收敛 / Geman-Geman) [1] 若冷却进度满足 T_k >= c / log(1+k)（c 足够大），则模拟退火以概率 1 收敛到全局最优。

**定理 11.3.3** (无免费午餐定理 / NFL) [8] 对所有可能问题取平均，任意两种优化算法的性能相同。
推论：启发式性能始终依赖于问题结构；不存在 universally best 的算法。

### 11.4 神经组合优化与学习优化
**定义 11.4.1** (神经组合优化 / NCO) 使用神经网络预测或构造组合优化问题的解 [9]。

**定理 11.4.1** (Pointer Networks) [9] 基于注意力机制的序列到序列模型可在多项式时间内为 TSP 生成可行解。

**定义 11.4.2** (Learning to Optimize) 使用机器学习加速经典优化求解器，例如学习 MIP 中的变量分支策略 [10]。

## 参考文献（补充）

- [1] Kirkpatrick, S., Gelatt, C. D., & Vecchi, M. P. (1983). Optimization by simulated annealing. Science, 220(4598), 671-680.
- [2] Glover, F. (1989). Tabu search - part I. ORSA Journal on Computing, 1(3), 190-206.
- [3] Kennedy, J., & Eberhart, R. (1995). Particle swarm optimization. Proc. ICNN, 1942-1948.
- [4] Dorigo, M., & Stutzle, T. (2004). Ant Colony Optimization. MIT Press.
- [5] Burke, E. K., et al. (2013). Hyper-heuristics: A survey of the state of the art. JORS, 64(12), 1695-1724.
- [6] Johnson, D. S., & McGeoch, L. A. (1997). The traveling salesman problem: A case study in local optimization. In Local Search in Combinatorial Optimization.
- [7] Rudolph, G. (1994). Convergence analysis of canonical genetic algorithms. IEEE Trans. Neural Networks, 5(1), 96-101.
- [8] Wolpert, D. H., & Macready, W. G. (1997). No free lunch theorems for optimization. IEEE Trans. Evol. Comput., 1(1), 67-82.
- [9] Vinyals, O., Fortunato, M., & Jaitly, N. (2015). Pointer networks. NeurIPS, 2692-2700.
- [10] Bengio, Y., Lodi, A., & Prouvost, A. (2021). Machine learning for combinatorial optimization: a methodological tour dhorizon. European Journal of Operational Research, 290(2), 405-421.
"""

base = "docs/09-算法理论/03-优化理论"
append_before_footer(os.path.join(base, "01-算法优化理论.md"), appendix_01.strip())
append_before_footer(os.path.join(base, "02-并行算法理论.md"), appendix_02.strip())
append_before_footer(os.path.join(base, "03-分布式算法理论.md"), appendix_03.strip())
append_before_footer(os.path.join(base, "04-启发式算法理论.md"), appendix_04.strip())
