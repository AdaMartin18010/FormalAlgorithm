# 项目结构

完整的算法规范与模型设计知识体系目录结构。

```
FormalAlgorithm/
├── 📄 项目根文件
│   ├── README.md                    # 项目介绍（中文）
│   ├── README_EN.md                 # 项目介绍（英文）
│   ├── CONTRIBUTING.md              # 贡献指南
│   ├── BUILD.md                     # 构建指南
│   ├── CHANGELOG.md                 # 更新日志
│   ├── PROJECT_STRUCTURE.md         # 本文件
│   ├── LICENSE                      # MIT许可证
│   └── CODE_OF_CONDUCT.md           # 行为准则
│
├── 📚 docs/                         # 知识文档 (818KB, 50个六维文档)
│   ├── 00-算法规范设计框架/
│   │   └── 01-知识体系架构.md
│   │
│   ├── 01-基础理论/                 # 3个文档
│   │   ├── 01-集合论基础-六维补充.md
│   │   ├── 02-数理逻辑基础-六维补充.md
│   │   └── 03-代数结构-六维补充.md
│   │
│   ├── 02-递归理论/                 # 2个文档
│   │   ├── 01-递归函数定义-深化补充-六维补充.md
│   │   └── 02-可计算性理论-六维补充.md
│   │
│   ├── 03-形式化证明/               # 2个文档
│   │   ├── 01-证明系统-六维补充.md
│   │   └── 02-程序验证-六维补充.md
│   │
│   ├── 04-算法复杂度/               # 5个文档
│   │   ├── 01-时间复杂度-六维补充.md
│   │   ├── 02-空间复杂度-六维补充.md
│   │   ├── 03-渐进分析-六维补充.md
│   │   ├── 04-复杂度类-六维补充.md
│   │   └── 05-摊还分析-六维补充.md
│   │
│   ├── 05-类型理论/                 # 3个文档
│   │   ├── 01-简单类型论-六维补充.md
│   │   ├── 02-多态类型-六维补充.md
│   │   └── 03-依赖类型-六维补充.md
│   │
│   ├── 06-逻辑系统/                 # 3个文档
│   │   ├── 01-命题逻辑-六维补充.md
│   │   ├── 02-谓词逻辑-六维补充.md
│   │   └── 03-模态逻辑-六维补充.md
│   │
│   ├── 07-计算模型/                 # 3个文档
│   │   ├── 01-图灵机-六维补充.md
│   │   ├── 02-自动机理论-六维补充.md
│   │   └── 03-λ演算-六维补充.md
│   │
│   ├── 08-实现示例/
│   │   └── 01-项目架构.md
│   │
│   ├── 09-算法理论/                 # 12个文档
│   │   ├── 01-算法基础/
│   │   │   ├── 01-算法分析基础-六维补充.md
│   │   │   ├── 03-平衡二叉搜索树-六维补充.md
│   │   │   ├── 04-堆与优先队列-六维补充.md
│   │   │   ├── 05-图算法理论-六维补充.md
│   │   │   ├── 06-动态规划理论-六维补充.md
│   │   │   ├── 07-贪心算法理论-六维补充.md
│   │   │   └── 24-高级数据结构.md
│   │   ├── 02-分治算法/
│   │   │   └── 01-分治算法理论-六维补充.md
│   │   ├── 03-搜索算法/
│   │   │   └── 01-搜索理论-六维补充.md
│   │   ├── 04-字符串算法/
│   │   │   ├── 01-字符串匹配理论-六维补充.md
│   │   │   └── 02-后缀数组理论-六维补充.md
│   │   ├── 05-NP完全性/
│   │   │   └── 01-NP完全性理论-六维补充.md
│   │   ├── 06-近似算法/
│   │   │   └── 01-近似算法理论-六维补充.md
│   │   ├── 07-随机算法/
│   │   │   └── 01-随机算法理论-六维补充.md
│   │   └── 08-在线算法/
│   │       └── 01-在线算法理论-六维补充.md
│   │
│   ├── 10-高级主题/                 # 7个文档
│   │   ├── 01-量子算法/
│   │   │   └── 01-量子计算基础-六维补充.md
│   │   ├── 02-机器学习算法/
│   │   │   └── 01-ML算法理论-六维补充.md
│   │   ├── 03-并行与分布式算法/
│   │   │   └── 01-并行算法-六维补充.md
│   │   ├── 04-流算法/
│   │   │   └── 01-数据流算法-六维补充.md
│   │   └── 05-分布式算法/
│   │       └── 01-一致性算法-六维补充.md
│   │
│   ├── 11-国际化/
│   │   ├── 01-国际课程深度对标/
│   │   └── 02-术语对照表.md
│   │
│   ├── 12-应用领域/                 # 10个文档
│   │   ├── 01-密码学/
│   │   │   └── 01-密码学算法-六维补充.md
│   │   ├── 02-生物信息学/
│   │   │   └── 01-生物序列算法-六维补充.md
│   │   ├── 03-图形学算法/
│   │   │   └── 01-计算几何应用-六维补充.md
│   │   ├── 04-数据库算法/
│   │   │   └── 01-数据库索引-六维补充.md
│   │   └── 05-编译器算法/
│   │       └── 01-编译优化-六维补充.md
│   │
│   ├── 习题库/                      # 10个文档, 520+题目
│   │   ├── 01-基础算法习题.md
│   │   ├── 02-高级算法习题.md
│   │   ├── 03-图论算法习题.md
│   │   ├── 04-动态规划习题.md
│   │   ├── 05-字符串算法习题.md
│   │   ├── 06-数学算法习题.md
│   │   ├── 07-综合实战题.md
│   │   ├── 08-NP完全性与近似算法习题.md
│   │   ├── 09-高级数据结构习题.md
│   │   └── 10-研究级开放问题.md
│   │
│   ├── 交叉索引/
│   │   ├── 01-全局概念索引.md
│   │   └── 02-算法选择决策树.md
│   │
│   ├── 质量保障体系/
│   │   ├── 01-文档质量检查清单.md
│   │   └── 02-代码质量检查清单.md
│   │
│   └── 致谢.md
│
├── 💻 examples/algorithms/          # Rust代码实现 (1096KB, 80个文件)
│   ├── Cargo.toml                   # Rust项目配置
│   ├── src/
│   │   ├── lib.rs                   # 库入口
│   │   ├── sorting.rs               # 排序算法
│   │   ├── merge_sort.rs
│   │   ├── quick_sort.rs
│   │   ├── heap_sort.rs
│   │   ├── binary_search.rs
│   │   ├── lcs.rs                   # 最长公共子序列
│   │   ├── graph_bfs_dfs.rs         # 图遍历
│   │   ├── dijkstra.rs              # 单源最短路径
│   │   ├── graph_mst.rs             # 最小生成树
│   │   ├── segment_tree.rs          # 线段树
│   │   ├── trie.rs                  # 前缀树
│   │   ├── union_find.rs            # 并查集
│   │   ├── fenwick_tree.rs          # 树状数组
│   │   ├── divide_and_conquer.rs    # 分治
│   │   ├── greedy_activity_selection.rs
│   │   ├── backtracking.rs          # 回溯
│   │   ├── backtracking_nqueens.rs
│   │   ├── fft.rs                   # 快速傅里叶变换
│   │   ├── lru_cache.rs             # LRU缓存
│   │   ├── consistent_hash.rs       # 一致性哈希
│   │   ├── bloom_filter.rs          # 布隆过滤器
│   │   ├── skiplist.rs              # 跳表
│   │   ├── suffix_array.rs          # 后缀数组
│   │   ├── ac_automaton.rs          # AC自动机
│   │   ├── suffix_automaton.rs      # 后缀自动机
│   │   ├── dsu_on_tree.rs           # 树上并查集
│   │   ├── mo_algorithm.rs          # Mo算法
│   │   ├── heavy_light_decomposition.rs  # 树链剖分
│   │   ├── centroid_decomposition.rs     # 点分治
│   │   ├── closest_pair.rs          # 最近点对
│   │   ├── red_black_tree.rs        # 红黑树
│   │   ├── topological_sort.rs      # 拓扑排序
│   │   ├── strongly_connected_components.rs  # 强连通分量
│   │   ├── fenwick_tree_2d.rs       # 二维树状数组
│   │   ├── cartesian_tree.rs        # 笛卡尔树
│   │   ├── manacher.rs              # Manacher算法
│   │   ├── z_algorithm.rs           # Z算法
│   │   ├── matrix_operations.rs     # 矩阵运算
│   │   ├── polynomial.rs            # 多项式
│   │   ├── geometry_utils.rs        # 几何工具
│   │   ├── discrete_log.rs          # 离散对数
│   │   ├── primality_test.rs        # 素数测试
│   │   ├── min_cost_max_flow.rs     # 最小费用最大流
│   │   ├── sat2.rs                  # 2-SAT
│   │   ├── rolling_hash.rs          # 滚动哈希
│   │   ├── persistent_segment_tree.rs  # 可持久化线段树
│   │   ├── dancing_links.rs         # 舞蹈链
│   │   └── simulated_annealing.rs   # 模拟退火
│   │
│   ├── string_algorithms/
│   │   ├── kmp.rs                   # KMP算法
│   │   └── edit_distance.rs         # 编辑距离
│   │
│   ├── network_flow/
│   │   └── max_flow.rs              # 最大流
│   │
│   ├── computational_geometry/
│   │   └── convex_hull.rs           # 凸包
│   │
│   ├── number_theory/
│   │   └── mod.rs                   # 数论算法
│   │
│   ├── graph.go                     # Go图算法
│   ├── dp.go                        # Go动态规划
│   ├── sort_advanced.go             # Go高级排序
│   ├── ml_algorithms.py             # Python机器学习
│   ├── quantum_simulation.py        # Python量子计算
│   ├── sorting.py                   # Python排序
│   ├── sorting.c                    # C排序
│   └── data_structures.c            # C数据结构
│
├── 💻 examples/algorithms-ts/       # TypeScript代码实现 ⭐ 新增 (13个文件)
│   ├── package.json
│   ├── tsconfig.json
│   ├── README.md
│   └── src/
│       ├── index.ts                 # 统一入口
│       ├── utils.ts                 # 工具与测试基础设施
│       ├── sorting.ts               # 10种排序算法
│       ├── data_structures.ts       # 链表、栈、队列、并查集、线段树、树状数组、Trie、跳表
│       ├── search.ts                # 线性/二分/插值/三分搜索
│       ├── graph.ts                 # BFS、DFS、最短路径、MST、拓扑排序、强连通分量
│       ├── dynamic_programming.ts   # 背包、LIS、LCS、零钱、编辑距离、矩阵链乘
│       ├── string.ts                # KMP、Manacher、Z函数、滚动哈希、AC自动机、后缀数组
│       ├── number_theory.ts         # GCD、扩展欧几里得、快速幂、素性测试、离散对数
│       ├── geometry.ts              # 凸包、最近点对、线段相交
│       ├── tree.ts                  # LCA、树链剖分、重心分解、笛卡尔树
│       ├── advanced.ts              # FFT、莫队、舞蹈链、模拟退火
│       └── tests/
│           └── all_tests.ts         # 统一测试运行器 (72个测试用例)
│
└── 📊 项目统计
    ├── 总文档: 100+
    ├── 总代码文件: 130+个
    ├── 总代码行数: 20,000+行
    ├── 总字数: 500,000+字
    ├── 算法实现: 110+个
    ├── 数据结构: 45+个
    └── 习题数量: 520+道
```

## 快速导航

### 学习者路径

1. **入门**: `docs/01-基础理论/` → `docs/习题库/01-基础算法习题.md`
2. **进阶**: `docs/09-算法理论/` → `docs/习题库/04-动态规划习题.md`
3. **高级**: `docs/10-高级主题/` → `docs/习题库/10-研究级开放问题.md`

### 代码实现索引

- **排序**: `examples/algorithms/src/sorting.rs`, `merge_sort.rs`, `quick_sort.rs`
- **图算法**: `examples/algorithms/src/dijkstra.rs`, `graph_mst.rs`, `network_flow/`
- **字符串**: `examples/algorithms/src/string_algorithms/kmp.rs`, `suffix_array.rs`
- **数据结构**: `examples/algorithms/src/segment_tree.rs`, `trie.rs`, `union_find.rs`

---

**总计**: 60+文档, 80+代码文件, 520+习题, 约2MB知识体系资源

### `docs/13-LeetCode算法面试专题/`

LeetCode 算法面试专题，形式化算法库的核心实战模块。按数据结构、算法范式、数学、字符串、图论、面试实战六大板块系统梳理 LeetCode 高频题。每道题遵循「四步法」框架（形式化规约→算法设计→正确性证明→参考实现），部分题目配备 Lean 4 形式化证明。配套代码分布在 `examples/algorithms/src/leetcode/` (Rust)、`examples/algorithms-python/src/leetcode/` (Python)、`examples/algorithms-go/leetcode/` (Go) 和 `examples/lean_proofs/FormalAlgorithm/leetcode/` (Lean)。

- `00-总览与方法论/` — 专题导论、解题四步法、复杂度速查与面试沟通模板
- `01-数据结构专题/` — 数组、链表、栈队列、哈希表、二叉树、堆、并查集、Trie
- `02-算法范式专题/` — 枚举、双指针、滑动窗口、前缀和、二分、分治、贪心、DP、回溯、BFS、位运算
- `03-数学专题/` — 数论、组合数学、计算几何、概率与随机算法
- `04-字符串专题/` — 字符串匹配与 KMP、回文问题、字符串动态规划
- `05-图论专题/` — 遍历、最短路径、拓扑排序、最小生成树
- `06-面试专题/` — 高频 Top 100、剑指 Offer 精选、大厂真题
- `99-附录/` — LeetCode 题号全局索引、常见错误清单、多语言代码模板速查
