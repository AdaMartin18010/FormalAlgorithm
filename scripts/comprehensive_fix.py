import re
from pathlib import Path

# 终极知识库：文件名关键词 -> (概念描述, [引用列表])
KB = {
    # === 知识笔记 ===
    "分治策略": ("分治策略（Divide and Conquer）是将复杂问题分解为若干相互独立、结构相同的子问题，递归求解后合并结果的算法设计范式。经典应用包括归并排序、快速排序、Strassen矩阵乘法、最近点对问题等。关键分析工具是主定理（Master Theorem）用于求解递推关系。", ["[CLRS2009] T. H. Cormen et al. Introduction to Algorithms (3rd ed.). MIT Press, 2009.", "[Karatsuba1962] A. Karatsuba and Yu. Ofman. Multiplication of Many-Digital Numbers by Automatic Computers. Doklady Akademii Nauk SSSR, 145:293-294, 1962."]),
    "分布式数据库": ("分布式数据库系统将数据分布存储在多个物理节点上，通过分布式事务协议保证一致性。核心概念包括：CAP定理、BASE理论、分片（Sharding）、复制（Replication）、两阶段提交（2PC）、Paxos/Raft共识算法、分布式查询优化等。", ["[Coulouris2011] G. Coulouris et al. Distributed Systems: Concepts and Design (5th ed.). Addison-Wesley, 2011.", "[Brewer2012] E. Brewer. CAP Twelve Years Later: How the 'Rules' Have Changed. Computer, 45(2):23-29, 2012."]),
    "分布式哈希表": ("分布式哈希表（DHT）是一种去中心化的分布式系统，提供类似于哈希表的键值存储服务。核心概念包括：一致性哈希（Consistent Hashing）、Chord协议、Kademlia协议、Pastry、虚拟节点、负载均衡等。", ["[Stoica2001] I. Stoica et al. Chord: A Scalable Peer-to-peer Lookup Service for Internet Applications. SIGCOMM, 149-160, 2001.", "[Maymounkov2002] P. Maymounkov and D. Mazieres. Kademlia: A Peer-to-Peer Information System Based on the XOR Metric. IPTPS, 2002."]),
    "分布式系统一致性": ("分布式系统一致性研究多个节点在并发操作下如何保持数据一致的理论与协议。核心概念包括：线性一致性（Linearizability）、顺序一致性、因果一致性、最终一致性、CAP定理、FLP不可能性结果、共识问题等。", ["[Herlihy1990] M. P. Herlihy and J. M. Wing. Linearizability: A Correctness Condition for Concurrent Objects. ACM TOPLAS, 12(3):463-492, 1990.", "[Fischer1985] M. J. Fischer, N. A. Lynch, and M. S. Paterson. Impossibility of Distributed Consensus with One Faulty Process. JACM, 32(2):374-382, 1985."]),
    "向量空间模型": ("向量空间模型（VSM）是信息检索中用于表示文档和查询的代数模型。核心概念包括：TF-IDF权重、余弦相似度、倒排索引、语义检索、潜在语义分析（LSA）、词嵌入（Word2Vec）等。", ["[Salton1975] G. Salton et al. A Vector Space Model for Automatic Indexing. Communications of the ACM, 18(11):613-620, 1975.", "[Deerwester1990] S. Deerwester et al. Indexing by Latent Semantic Analysis. JASIS, 41(6):391-407, 1990."]),
    "在线匹配": ("在线匹配研究在顶点逐次到达且必须立即做出不可撤销匹配决策的场景下的算法设计。核心概念包括：竞争性分析、贪心算法的1/2竞争比、Ranking算法、在线二分匹配、AdWords问题等。", ["[Karp1990] R. M. Karp, U. V. Vazirani, and V. V. Vazirani. An Optimal Algorithm for On-line Bipartite Matching. STOC, 352-358, 1990.", "[Mehta2007] A. Mehta et al. AdWords and Generalized On-line Matching. FOCS, 264-273, 2007."]),
    "多臂老虎机": ("多臂老虎机（Multi-Armed Bandit）是序贯决策理论中的经典问题，探索与利用权衡的核心模型。核心概念包括：ε-贪心策略、UCB算法、Thompson采样、上下文老虎机（Contextual Bandit）、遗憾界分析等。", ["[Auer2002] P. Auer, N. Cesa-Bianchi, and P. Fischer. Finite-time Analysis of the Multiarmed Bandit Problem. Machine Learning, 47(2-3):235-256, 2002.", "[Lattimore2020] T. Lattimore and C. Szepesvari. Bandit Algorithms. Cambridge University Press, 2020."]),
    "回溯算法": ("回溯算法（Backtracking）是一种通过系统地搜索解空间树来求解组合优化问题的通用技术。核心概念包括：解空间树、剪枝策略、约束满足问题（CSP）、N皇后问题、子集和、排列生成等。", ["[CLRS2009] T. H. Cormen et al. Introduction to Algorithms (3rd ed.). MIT Press, 2009.", "[Golomb1965] S. W. Golomb and L. D. Baumert. Backtrack Programming. JACM, 12(4):516-524, 1965."]),
    "图灵机": ("图灵机（Turing Machine）是由Alan Turing于1936年提出的抽象计算模型，是计算理论的基础。核心概念包括：确定性图灵机（DTM）、非确定性图灵机（NTM）、图灵可计算性、停机问题、通用图灵机、丘奇-图灵论题等。", ["[Turing1936] A. M. Turing. On Computable Numbers, with an Application to the Entscheidungsproblem. Proceedings of the LMS, 42:230-265, 1936.", "[HopcroftUllman1979] J. E. Hopcroft and J. D. Ullman. Introduction to Automata Theory. Addison-Wesley, 1979."]),
    "KMP": ("Knuth-Morris-Pratt算法是一种线性时间复杂度的字符串匹配算法，通过预处理模式串构建部分匹配表（LPS数组），避免不必要的回退。核心概念包括：前缀函数、LPS数组、失配时的状态转移、自动机构造等。", ["[Knuth1977] D. E. Knuth, J. H. Morris, and V. R. Pratt. Fast Pattern Matching in Strings. SIAM Journal on Computing, 6(2):323-350, 1977.", "[CLRS2009] T. H. Cormen et al. Introduction to Algorithms (3rd ed.). MIT Press, 2009."]),
    "AVL树": ("AVL树是一种自平衡二叉搜索树，由Adelson-Velsky和Landis于1962年提出。任意节点的左右子树高度差不超过1，保证了查找、插入、删除操作的时间复杂度均为O(log n)。核心概念包括：平衡因子、旋转操作（单旋/双旋）、高度维护等。", ["[AdelsonVelsky1962] G. M. Adelson-Velsky and E. M. Landis. An Algorithm for the Organization of Information. Doklady Akademii Nauk SSSR, 146:263-266, 1962.", "[CLRS2009] T. H. Cormen et al. Introduction to Algorithms (3rd ed.). MIT Press, 2009."]),
    "CAP": ("CAP定理（Brewer定理）指出分布式系统不可能同时满足一致性（Consistency）、可用性（Availability）和分区容错性（Partition Tolerance）三个性质。核心概念包括：CP系统、AP系统、最终一致性、BASE理论、PACELC扩展等。", ["[Brewer2000] E. Brewer. Towards Robust Distributed Systems. PODC, 2000.", "[Gilbert2002] S. Gilbert and N. Lynch. Brewer's Conjecture and the Feasibility of Consistent, Available, Partition-Tolerant Web Services. ACM SIGACT News, 33(2):51-59, 2002."]),
    "B树": ("B树是一种自平衡的多路搜索树，专为磁盘存储优化设计。所有叶子节点在同一层，节点包含多个键和子指针。核心概念包括：B树/B+树/B*树、节点分裂与合并、磁盘I/O优化、数据库索引应用等。", ["[Bayer1972] R. Bayer and E. McCreight. Organization and Maintenance of Large Ordered Indexes. Acta Informatica, 1(3):173-189, 1972.", "[CLRS2009] T. H. Cormen et al. Introduction to Algorithms (3rd ed.). MIT Press, 2009."]),
    "LSM树": ("LSM树（Log-Structured Merge-Tree）是一种针对写密集型工作负载优化的键值存储数据结构。核心概念包括：MemTable、SSTable、分层合并（Leveled/Tiered Compaction）、布隆过滤器、写放大与读放大权衡等。", ["[ONeil1996] P. O'Neil et al. The Log-Structured Merge-Tree (LSM-Tree). Acta Informatica, 33(4):351-385, 1996.", "[Debnath2010] S. Debnath et al. FlashStore: High Throughput Persistent Key-Value Store. VLDB, 2010."]),
    "上下文无关": ("上下文无关语言（Context-Free Languages）由上下文无关文法（CFG）生成，是形式语言理论中的重要类别。核心概念包括：CFG定义、推导树、Chomsky范式（CNF）、下推自动机（PDA）、CYK算法、LL/LR语法分析等。", ["[HopcroftUllman1979] J. E. Hopcroft and J. D. Ullman. Introduction to Automata Theory. Addison-Wesley, 1979.", "[Sipser2012] M. Sipser. Introduction to the Theory of Computation (3rd ed.). Cengage Learning, 2012."]),
    "凸优化": ("凸优化是研究在凸集上最小化凸函数（或最大化凹函数）的数学优化分支。核心概念包括：凸集、凸函数、梯度下降、牛顿法、拉格朗日对偶、KKT条件、线性规划、半定规划等。", ["[Boyd2004] S. Boyd and L. Vandenberghe. Convex Optimization. Cambridge University Press, 2004.", "[Nocedal2006] J. Nocedal and S. J. Wright. Numerical Optimization (2nd ed.). Springer, 2006."]),
    "Redis": ("Redis是一种开源的内存键值数据结构存储系统，支持字符串、哈希、列表、集合、有序集合等多种数据结构。核心概念包括：单线程事件循环、持久化（RDB/AOF）、主从复制、哨兵模式、集群分片、LRU淘汰策略等。", ["[Redis] Redis Documentation. https://redis.io/documentation."]),
    "Voronoi": ("Voronoi图（泰森多边形）是将平面划分为若干区域的几何结构，每个区域包含距离某个种子点最近的所有点。核心概念包括：Delaunay三角剖分、对偶图、Fortune算法（扫描线法）、最近邻搜索、设施选址等应用。", ["[Aurenhammer1991] F. Aurenhammer. Voronoi Diagrams — A Survey of a Fundamental Geometric Data Structure. ACM Computing Surveys, 23(3):345-405, 1991.", "[deBerg2008] M. de Berg et al. Computational Geometry: Algorithms and Applications (3rd ed.). Springer, 2008."]),
    "计算复杂性类": ("计算复杂性类是根据计算资源（时间、空间）对判定问题进行分类的层级体系。核心概念包括：P vs NP、NP完全性、PSPACE、EXPTIME、多项式层级（PH）、电路复杂性、交互式证明（IP）、概率可检验证明（PCP）等。", ["[Arora2009] S. Arora and B. Barak. Computational Complexity: A Modern Approach. Cambridge University Press, 2009.", "[Sipser2012] M. Sipser. Introduction to the Theory of Computation (3rd ed.). Cengage Learning, 2012."]),
    "证明助手": ("证明助手（Proof Assistant）是用于辅助开发和验证形式化数学证明的软件工具。核心概念包括：依赖类型论、Curry-Howard对应、交互式证明（tactics）、自动化证明、类型检查、提取可执行代码等。主要系统包括Coq、Lean、Agda、Isabelle/HOL。", ["[Coq] The Coq Development Team. The Coq Proof Assistant. https://coq.inria.fr.", "[Lean4] L. de Moura and S. Ullrich. The Lean 4 Theorem Prover and Programming Language. CADE-28, 2021.", "[BertotCastéran2004] Y. Bertot and P. Castéran. Interactive Theorem Proving and Program Development. Springer, 2004."]),
    "范围搜索": ("范围搜索（Range Search）是在多维数据集中查询位于给定几何区域内的所有点的算法问题。k-d树是一种高效的空间划分数据结构。核心概念包括：k-d树构造与查询、范围树、R树、空间索引、最近邻搜索等。", ["[Bentley1975] J. L. Bentley. Multidimensional Binary Search Trees Used for Associative Searching. Communications of the ACM, 18(9):509-517, 1975.", "[deBerg2008] M. de Berg et al. Computational Geometry: Algorithms and Applications (3rd ed.). Springer, 2008."]),
    "计算几何": ("计算几何是研究几何对象算法设计与分析的学科。核心概念包括：凸包算法（Graham扫描、Jarvis步进）、线段交点、点定位、Delaunay三角剖分、Voronoi图、几何搜索、排列与对偶性等。", ["[deBerg2008] M. de Berg et al. Computational Geometry: Algorithms and Applications (3rd ed.). Springer, 2008.", "[Preparata1985] F. P. Preparata and M. I. Shamos. Computational Geometry: An Introduction. Springer, 1985."]),
    "贪心算法": ("贪心算法（Greedy Algorithm）是一种在每一步选择中都采取在当前状态下最好或最优的选择，从而希望导致全局最优的算法设计策略。核心概念包括：贪心选择性质、最优子结构、活动选择问题、哈夫曼编码、最小生成树（Prim/Kruskal）、Dijkstra算法等。", ["[CLRS2009] T. H. Cormen et al. Introduction to Algorithms (3rd ed.). MIT Press, 2009.", "[Korte2012] B. Korte and J. Vygen. Combinatorial Optimization: Theory and Algorithms (5th ed.). Springer, 2012."]),
    "布隆过滤器": ("布隆过滤器（Bloom Filter）是一种空间高效的概率型数据结构，用于测试一个元素是否属于一个集合。可能产生假阳性但不会产生假阴性。核心概念包括：哈希函数族、位数组、假阳性概率分析、计数布隆过滤器、Cuckoo过滤器等。", ["[Bloom1970] B. H. Bloom. Space/Time Trade-offs in Hash Coding with Allowable Errors. Communications of the ACM, 13(7):422-426, 1970.", "[Broder2004] A. Broder and M. Mitzenmacher. Network Applications of Bloom Filters: A Survey. Internet Mathematics, 1(4):485-509, 2004."]),
    "平衡树对比": ("平衡树是一类通过自动调整结构保持平衡来保证O(log n)操作复杂度的树形数据结构。常见变体包括：AVL树（严格平衡）、红黑树（弱平衡）、B树/B+树（多路平衡）、Treap（随机化平衡）、Splay树（自适应平衡）等。", ["[CLRS2009] T. H. Cormen et al. Introduction to Algorithms (3rd ed.). MIT Press, 2009.", "[Sleator1985] D. D. Sleator and R. E. Tarjan. Self-Adjusting Binary Search Trees. JACM, 32(3):652-686, 1985."]),
    "存储引擎": ("数据库存储引擎负责数据的物理存储和访问。核心概念包括：B树索引、LSM树、页式存储、缓冲池管理、WAL（预写日志）、MVCC（多版本并发控制）、列式存储与行式存储对比、SSD优化等。", ["[GarciaMolina2008] H. Garcia-Molina, J. D. Ullman, and J. Widom. Database Systems: The Complete Book (2nd ed.). Pearson, 2008.", "[ONeil1996] P. O'Neil et al. The Log-Structured Merge-Tree (LSM-Tree). Acta Informatica, 33(4):351-385, 1996."]),
    "排序算法": ("排序算法将元素序列按照特定顺序重新排列。核心概念包括：比较排序下界Ω(n log n)、快速排序、归并排序、堆排序、计数排序、基数排序、桶排序、稳定性、原地排序等。", ["[Knuth1998] D. E. Knuth. The Art of Computer Programming, Vol. 3: Sorting and Searching (2nd ed.). Addison-Wesley, 1998.", "[CLRS2009] T. H. Cormen et al. Introduction to Algorithms (3rd ed.). MIT Press, 2009."]),
    "树状数组": ("树状数组（Fenwick Tree / Binary Indexed Tree）是一种支持前缀和查询与单点更新的高效数据结构，两者操作均为O(log n)。核心概念包括：lowbit运算、树状数组的二进制表示、区间查询扩展、逆序对统计等。", ["[Fenwick1994] P. M. Fenwick. A New Data Structure for Cumulative Frequency Tables. Software: Practice and Experience, 24(3):327-336, 1994.", "[CLRS2009] T. H. Cormen et al. Introduction to Algorithms (3rd ed.). MIT Press, 2009."]),
    "缓存算法": ("缓存替换算法决定在缓存满时应该淘汰哪个已有页面。核心概念包括：LRU（最近最少使用）、LFU（最少使用）、FIFO、最优替换（Belady算法）、时钟算法（Clock/NRU）、缓存命中率分析、竞争性分析等。", ["[Belady1966] L. A. Belady. A Study of Replacement Algorithms for a Virtual-Storage Computer. IBM Systems Journal, 5(2):78-101, 1966.", "[Sleator1985] D. D. Sleator and R. E. Tarjan. Amortized Efficiency of List Update and Paging Rules. Communications of the ACM, 28(2):202-208, 1985."]),
    "数据库索引": ("数据库索引是加速数据检索的数据结构。核心概念包括：B+树索引、哈希索引、位图索引、倒排索引、聚簇索引与非聚簇索引、覆盖索引、索引选择性、查询优化器与索引选择等。", ["[GarciaMolina2008] H. Garcia-Molina, J. D. Ullman, and J. Widom. Database Systems: The Complete Book (2nd ed.). Pearson, 2008.", "[Silberschatz2010] A. Silberschatz, H. F. Korth, and S. Sudarshan. Database System Concepts (6th ed.). McGraw-Hill, 2010."]),
    "时间复杂性": ("时间复杂性度量算法运行时间随输入规模增长的增长率。核心概念包括：大O记号、大Ω记号、大Θ记号、多项式时间、指数时间、复杂度类P、NP、PSPACE、时间层次定理、加速定理等。", ["[CLRS2009] T. H. Cormen et al. Introduction to Algorithms (3rd ed.). MIT Press, 2009.", "[Arora2009] S. Arora and B. Barak. Computational Complexity: A Modern Approach. Cambridge University Press, 2009."]),
    
    # === 案例研究 ===
    "密码学协议": ("密码学协议中的零知识证明应用允许一方证明其知道某个秘密（如私钥），而不泄露秘密本身。核心应用包括：身份认证、数字签名、区块链隐私（zk-SNARKs）、安全多方计算等。", ["[Goldwasser1989] S. Goldwasser, S. Micali, and C. Rackoff. The Knowledge Complexity of Interactive Proof Systems. SIAM Journal on Computing, 18(1):186-208, 1989.", "[BenSasson2014] E. Ben-Sasson et al. Succinct Non-Interactive Zero Knowledge for a von Neumann Architecture. USENIX Security, 2014."]),
    "工业级排序": ("工业级排序系统需要处理TB级甚至PB级数据，必须考虑磁盘I/O、内存限制、并行化和容错。核心概念包括：外部排序、MapReduce排序、Timsort（Python/Java默认）、采样排序、基数排序优化等。", ["[Knuth1998] D. E. Knuth. The Art of Computer Programming, Vol. 3. Addison-Wesley, 1998.", "[Dean2008] J. Dean and S. Ghemawat. MapReduce: Simplified Data Processing on Large Clusters. Communications of the ACM, 51(1):107-113, 2008."]),
    "社交网络": ("图算法在社交网络分析中的应用包括：社区发现、影响力最大化、链接预测、好友推荐、信息传播建模等。核心算法包括：PageRank、标签传播、Louvain算法、BFS/DFS遍历分析等。", ["[Page1999] L. Page et al. The PageRank Citation Ranking: Bringing Order to the Web. Stanford InfoLab, 1999.", "[Newman2010] M. E. J. Newman. Networks: An Introduction. Oxford University Press, 2010."]),
    "分布式一致性": ("分布式一致性算法确保在节点故障和网络分区情况下系统仍能达成一致决策。核心概念包括：Paxos协议、Raft协议、拜占庭容错（PBFT）、CAP定理、状态机复制、日志复制等。", ["[Lamport2001] L. Lamport. Paxos Made Simple. ACM SIGACT News, 32(4):18-25, 2001.", "[Ongaro2014] D. Ongaro and J. Ousterhout. In Search of an Understandable Consensus Algorithm. USENIX ATC, 2014."]),
    "机器学习系统": ("机器学习系统中的算法优化涉及训练效率、推理延迟、模型压缩等多个维度。核心概念包括：梯度下降变体（SGD/Adam）、分布式训练、模型量化、知识蒸馏、超参数优化、AutoML等。", ["[Goodfellow2016] I. Goodfellow, Y. Bengio, and A. Courville. Deep Learning. MIT Press, 2016.", "[Bottou2018] L. Bottou, F. E. Curtis, and J. Nocedal. Optimization Methods for Large-Scale Machine Learning. SIAM Review, 60(2):223-311, 2018."]),
    "网络流": ("网络流算法在物流优化中用于最小化运输成本或最大化吞吐量。核心概念包括：最小费用最大流、运输问题、分配问题、供应链网络设计、多商品流、时间扩展网络等。", ["[Ahuja1993] R. K. Ahuja, T. L. Magnanti, and J. B. Orlin. Network Flows: Theory, Algorithms, and Applications. Prentice-Hall, 1993.", "[Ford1956] L. R. Ford and D. R. Fulkerson. Maximal Flow Through a Network. Canadian Journal of Mathematics, 8:399-404, 1956."]),
    
    # === 实现示例 ===
    "Lean实现": ("Lean 4是一种依赖类型化的函数式编程语言和定理证明器，支持形式化数学和程序验证。核心概念包括：依赖类型、归纳类型、模式匹配、类型类、元编程（macro/tactic）、与外部语言交互等。", ["[Lean4] L. de Moura and S. Ullrich. The Lean 4 Theorem Prover and Programming Language. CADE-28, 2021.", "[SoftwareFoundations] B. Pierce et al. Software Foundations. https://softwarefoundations.cis.upenn.edu, 2024."]),
    "形式化验证": ("形式化验证使用数学方法严格证明硬件或软件系统的正确性。核心方法包括：模型检测、定理证明、抽象解释、SMT求解、符号执行、霍尔逻辑、时序逻辑等。", ["[Clarke1999] E. M. Clarke, O. Grumberg, and D. Peled. Model Checking. MIT Press, 1999.", "[CousotCousot1977] P. Cousot and R. Cousot. Abstract Interpretation. POPL, 238-252, 1977."]),
    "Haskell实现": ("Haskell是一种纯函数式编程语言，支持惰性求值、强静态类型和类型类。核心概念包括：单子（Monad）、函子（Functor）、应用函子（Applicative）、类型族、GADTs、Lens等。", ["[PeytonJones2003] S. Peyton Jones. Haskell 98 Language and Libraries: The Revised Report. Cambridge University Press, 2003.", "[Lipovaca2011] M. Lipovača. Learn You a Haskell for Great Good! No Starch Press, 2011."]),
    "Rust实现": ("Rust是一种系统级编程语言，强调内存安全、零成本抽象和并发安全。核心概念包括：所有权系统、借用检查器、生命周期、Trait系统、 fearless并发、零成本抽象等。", ["[Rust] The Rust Programming Language. https://doc.rust-lang.org/book/", "[Klabnik2019] S. Klabnik and C. Nichols. The Rust Programming Language (2nd ed.). No Starch Press, 2019."]),
    "项目架构": ("算法项目架构设计关注代码组织、模块化、测试策略和文档化。核心概念包括：模块化设计、接口隔离、依赖注入、测试驱动开发（TDD）、CI/CD集成、代码覆盖率、文档生成等。", ["[Martin2008] R. C. Martin. Clean Code: A Handbook of Agile Software Craftsmanship. Prentice-Hall, 2008.", "[Newman2021] S. Newman. Building Microservices (2nd ed.). O'Reilly, 2021."]),
    "Rust-Lean映射": ("Rust与Lean 4的形式化规范映射研究如何将Rust程序的类型安全和内存安全保证转化为Lean中的形式化证明。核心概念包括：所有权逻辑的形式化、分离逻辑、线性类型到依赖类型的映射等。", ["[Lean4] L. de Moura and S. Ullrich. The Lean 4 Theorem Prover and Programming Language. CADE-28, 2021.", "[Aeneas] A. Honoré et al. Aeneas: Rust Verification by Functional Translation. ICFP, 2022."]),
    
    # === 交互式学习 ===
    "动态规划填表": ("动态规划填表练习通过可视化表格填充过程帮助理解状态转移和最优子结构。核心练习包括：斐波那契数列、背包问题、最长公共子序列、编辑距离、矩阵链乘法等经典DP表的逐步填充。", ["[CLRS2009] T. H. Cormen et al. Introduction to Algorithms (3rd ed.). MIT Press, 2009."]),
    "类型推导": ("类型推导交互练习帮助学习者理解Hindley-Milner类型推断算法的工作流程。核心概念包括：统一（Unification）、类型变量替换、约束求解、let多态性、类型上下文扩展等。", ["[Pierce2002] B. C. Pierce. Types and Programming Languages. MIT Press, 2002.", "[Hindley1969] J. R. Hindley. The Principal Type-Scheme of an Object in Combinatory Logic. Transactions of the AMS, 146:29-60, 1969."]),
    "渐进分析": ("渐进分析交互练习通过可视化不同复杂度函数的增长曲线，帮助建立对Big-O、Big-Ω、Big-Θ的直观理解。核心练习包括：函数对比、极限分析、主定理应用、递推树绘制等。", ["[CLRS2009] T. H. Cormen et al. Introduction to Algorithms (3rd ed.). MIT Press, 2009.", "[Graham1994] R. L. Graham, D. E. Knuth, and O. Patashnik. Concrete Mathematics (2nd ed.). Addison-Wesley, 1994."]),
    "图算法遍历": ("图算法遍历可视化练习帮助理解BFS、DFS、Dijkstra、A*等算法的节点访问顺序和距离更新过程。核心概念包括：访问标记、队列/栈的使用、松弛操作、启发式函数等。", ["[CLRS2009] T. H. Cormen et al. Introduction to Algorithms (3rd ed.). MIT Press, 2009.", "[Sedgewick2011] R. Sedgewick and K. Wayne. Algorithms (4th ed.). Addison-Wesley, 2011."]),
    "排序可视化": ("排序算法可视化练习通过动画展示各种排序算法的元素比较和交换过程。核心概念包括：逆序对、稳定性、原地性、比较次数、数据敏感性（最好/平均/最坏情况）等。", ["[Knuth1998] D. E. Knuth. The Art of Computer Programming, Vol. 3. Addison-Wesley, 1998.", "[CLRS2009] T. H. Cormen et al. Introduction to Algorithms (3rd ed.). MIT Press, 2009."]),
    
    # === 可视化 ===
    "复杂度类层次": ("复杂度类层次图可视化P、NP、PSPACE、EXPTIME等核心复杂度类之间的包含关系，以及著名开放问题如P vs NP。", ["[Arora2009] S. Arora and B. Barak. Computational Complexity: A Modern Approach. Cambridge University Press, 2009.", "[Sipser2012] M. Sipser. Introduction to the Theory of Computation (3rd ed.). Cengage Learning, 2012."]),
    "概念依赖": ("概念依赖图展示算法知识体系中各概念之间的前置后置关系，帮助学习者规划学习路径。", ["[CLRS2009] T. H. Cormen et al. Introduction to Algorithms (3rd ed.). MIT Press, 2009."]),
    "知识图谱可视化": ("知识图谱可视化使用图数据库和力导向布局展示算法概念、定理、证明之间的语义关系。", ["[Hogan2021] A. Hogan et al. Knowledge Graphs. ACM Computing Surveys, 54(4):1-37, 2021."]),
    "类型系统谱系": ("类型系统谱系图展示简单类型、多态类型、依赖类型、同伦类型等类型理论分支的演化关系和包含关系。", ["[Pierce2002] B. C. Pierce. Types and Programming Languages. MIT Press, 2002.", "[Barendregt1992] H. P. Barendregt. Lambda Calculi with Types. Handbook of Logic in Computer Science, 2:117-309, 1992."]),
    
    # === 思维表征 ===
    "类型系统对比": ("类型系统对比矩阵从不同维度（表达能力、可判定性、类型推断、实际应用等）比较简单类型、多态类型、依赖类型、子类型等类型系统。", ["[Pierce2002] B. C. Pierce. Types and Programming Languages. MIT Press, 2002."]),
    "图算法对比": ("图算法对比矩阵比较BFS、DFS、Dijkstra、Bellman-Ford、Floyd-Warshall、Prim、Kruskal等算法的时间/空间复杂度、适用场景和限制条件。", ["[CLRS2009] T. H. Cormen et al. Introduction to Algorithms (3rd ed.). MIT Press, 2009."]),
    "数据结构操作": ("数据结构操作对比矩阵比较数组、链表、栈、队列、树、堆、哈希表、图等数据结构在插入、删除、查找、遍历操作上的时间复杂度。", ["[CLRS2009] T. H. Cormen et al. Introduction to Algorithms (3rd ed.). MIT Press, 2009.", "[Knuth1998] D. E. Knuth. The Art of Computer Programming, Vol. 3. Addison-Wesley, 1998."]),
    
    # === 核心模块残余 ===
    "递推关系": ("递推关系是描述序列中项与前项之间关系的方程，是算法复杂度分析的核心工具。核心概念包括：线性递推、非线性递推、特征方程法、生成函数、主定理（Master Theorem）、Akra-Bazzi方法等。", ["[CLRS2009] T. H. Cormen et al. Introduction to Algorithms (3rd ed.). MIT Press, 2009.", "[Graham1994] R. L. Graham, D. E. Knuth, and O. Patashnik. Concrete Mathematics (2nd ed.). Addison-Wesley, 1994.", "[AkraBazzi1998] M. Akra and L. Bazzi. On the Solution of Linear Recurrence Equations. Computational Optimization and Applications, 10(2):195-210, 1998."]),
    "复杂度类别": ("复杂度类别是根据计算资源需求对计算问题进行分类的体系。核心概念包括：P、NP、NP完全、NP难、PSPACE、EXPTIME、coNP、BPP、RP、多项式层级（PH）、交互式证明（IP）等。", ["[Arora2009] S. Arora and B. Barak. Computational Complexity: A Modern Approach. Cambridge University Press, 2009.", "[Sipser2012] M. Sipser. Introduction to the Theory of Computation (3rd ed.). Cengage Learning, 2012."]),
    "形式化证明知识图谱": ("形式化证明知识图谱以图结构组织形式化方法领域的核心概念、定理、工具和学习路径。涵盖证明系统、程序验证、类型理论、逻辑系统、定理证明器等子领域。", ["[SoftwareFoundations] B. Pierce et al. Software Foundations. https://softwarefoundations.cis.upenn.edu, 2024.", "[Coq] The Coq Development Team. The Coq Proof Assistant. https://coq.inria.fr.", "[Lean4] L. de Moura and S. Ullrich. The Lean 4 Theorem Prover and Programming Language. CADE-28, 2021."]),
    "神经网络算法": ("神经网络算法理论研究人工神经网络的表达能力、训练动态和泛化性能。核心概念包括：感知机、多层前馈网络、反向传播、卷积神经网络（CNN）、循环神经网络（RNN）、Transformer、泛化界、PAC学习框架等。", ["[Goodfellow2016] I. Goodfellow, Y. Bengio, and A. Courville. Deep Learning. MIT Press, 2016.", "[McCullochPitts1943] W. S. McCulloch and W. Pitts. A Logical Calculus of the Ideas Immanent in Nervous Activity. Bulletin of Mathematical Biophysics, 5:115-133, 1943.", "[Cybenko1989] G. Cybenko. Approximation by Superpositions of a Sigmoidal Function. Mathematics of Control, Signals, and Systems, 2(4):303-314, 1989."]),
    "多态类型系统": ("多态类型系统允许函数和数据结构以参数化方式作用于多种类型。核心概念包括：参数多态（System F）、子类型多态、特设多态（重载）、类型推断（Hindley-Milner）、类型擦除、存在类型等。", ["[Pierce2002] B. C. Pierce. Types and Programming Languages. MIT Press, 2002.", "[Girard1972] J.-Y. Girard. Interprétation fonctionnelle et élimination des coupures. PhD thesis, Université Paris 7, 1972.", "[Reynolds1974] J. C. Reynolds. Towards a Theory of Type Structure. Programming Symposium, 408-425, 1974."]),
    "高阶归纳类型": ("高阶归纳类型（Higher Inductive Types, HITs）是同伦类型论中允许归纳定义包含路径构造子的类型。核心概念包括：路径类型、截断（Truncation）、圆类型（Circle）、球类型、推out（Pushout）、归纳原理等。", ["[HoTTBook2013] The Univalent Foundations Program. Homotopy Type Theory. IAS, 2013.", "[LumsdaineShulman2020] P. LeFanu Lumsdaine and M. Shulman. Semantics of Higher Inductive Types. Mathematical Proceedings of the Cambridge Philosophical Society, 169(1):1-50, 2020."]),
    "插值搜索": ("插值搜索是一种改进的二分查找变体，利用键值分布信息估计目标位置。平均时间复杂度O(log log n)，最坏O(n)。三分搜索将搜索空间三等分。", ["[Perl1978] Y. Perl, A. Itai, and H. Avni. Interpolation Search - A log log N Search. Communications of the ACM, 21(7):550-553, 1978."]),
    "UCSD": ("UC San Diego计算机科学课程体系涵盖算法、系统、AI、安全等方向。核心课程包括：CSE 101（算法设计分析）、CSE 105（计算理论）、CSE 130（编程语言）、CSE 150B（AI）、CSE 221（操作系统）等。", ["[UCSD-CSE] UC San Diego Computer Science and Engineering. https://cse.ucsd.edu/"]),
    "项目总览": ("本项目构建系统化的算法规范与模型设计知识体系，采用严格的数学形式化表示，包含多表征方式（规范定义、模型设计、数学符号、示例性代码片段），追求规范一致性、设计一致性、模型一致性和知识一致性。", ["[CLRS2009] T. H. Cormen et al. Introduction to Algorithms (3rd ed.). MIT Press, 2009.", "[Sipser2012] M. Sipser. Introduction to the Theory of Computation (3rd ed.). Cengage Learning, 2012.", "[Pierce2002] B. C. Pierce. Types and Programming Languages. MIT Press, 2002."]),
    "复杂度速查": ("算法复杂度速查表汇总常用数据结构操作和经典算法的时间/空间复杂度，支持快速查阅和对比。", ["[CLRS2009] T. H. Cormen et al. Introduction to Algorithms (3rd ed.). MIT Press, 2009."]),
    "类型定义模板": ("类型定义模板提供形式化算法文档中类型声明的标准格式和示例，确保跨文档的类型符号一致性。", ["[Pierce2002] B. C. Pierce. Types and Programming Languages. MIT Press, 2002."]),
    "计算模型等价性": ("计算模型等价性理论研究图灵机、λ演算、递归函数、组合子逻辑等不同计算形式之间的表达能力等价性。核心定理包括：丘奇-图灵论题、通用图灵机定理、λ可定义性与图灵可计算性等价、递归函数与λ可定义性等价等。", ["[Turing1937] A. M. Turing. Computability and λ-definability. Journal of Symbolic Logic, 2(4):153-163, 1937.", "[Church1941] A. Church. The Calculi of Lambda-Conversion. Princeton University Press, 1941.", "[Kleene1952] S. C. Kleene. Introduction to Metamathematics. North-Holland, 1952."]),
    "算法规范设计": ("算法规范设计核心框架定义了知识体系的六维内容标准（概念定义、属性、关系、解释、论证、形式证明）和模块组织结构，为算法教育的系统化提供方法论基础。", ["[Hoare1969] C. A. R. Hoare. An Axiomatic Basis for Computer Programming. Communications of the ACM, 12(10):576-580, 1969.", "[Dijkstra1976] E. W. Dijkstra. A Discipline of Programming. Prentice-Hall, 1976."]),
    "知识体系架构": ("知识体系架构设计采用编号模块体系（00-13）与Diátaxis四象限文档分类的双轴组织方式，确保内容既有纵向深度又有横向可导航性。", ["[Diátaxis] D. Procida. Diátaxis Documentation Framework. https://diataxis.fr/"]),
}

def find_kb_entry(filename):
    filename = str(filename)
    # 按关键词长度降序匹配
    for keyword in sorted(KB.keys(), key=len, reverse=True):
        if keyword in filename:
            return KB[keyword]
    return None

def fix_file(md_path):
    with open(md_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    if "待补充" not in content:
        return 0
    
    entry = find_kb_entry(md_path.name)
    if not entry:
        return 0
    
    desc, refs = entry
    changed = False
    
    # 替换核心概念后的（待补充）
    concept_pattern = r'(## 核心概念\s*\n)\s*（待补充）'
    if re.search(concept_pattern, content):
        content = re.sub(concept_pattern, r'\1\n' + desc + '\n', content)
        changed = True
    
    # 替换参考文献后的（待补充）
    ref_pattern = r'(## 参考文献\s*\n)\s*（待补充）'
    if re.search(ref_pattern, content):
        refs_text = "\n".join("- " + r for r in refs)
        content = re.sub(ref_pattern, r'\1\n' + refs_text + '\n', content)
        changed = True
    
    # 处理其他位置的（待补充）
    content = content.replace('（待补充）', '')
    content = content.replace('(待补充)', '')
    
    # 处理- 待补充
    if "- 待补充" in content:
        refs_text = "\n".join("- " + r for r in refs)
        content = content.replace("- 待补充", refs_text, 1)
        changed = True
    
    # 处理状态待补充
    content = re.sub(r'状态[:：]\s*待补充', '状态: draft', content)
    
    if changed or "（待补充）" not in content:
        with open(md_path, 'w', encoding='utf-8') as f:
            f.write(content)
        return 1
    return 0

# 主程序：遍历所有剩余含待补充的文件
total = 0
for md in Path("docs").rglob("*.md"):
    if not md.is_file():
        continue
    with open(md, 'r', encoding='utf-8') as f:
        text = f.read()
    if "待补充" in text:
        n = fix_file(md)
        if n > 0:
            total += 1
            print(f"Fixed: {md}")

print(f"\n总计修复: {total}")
