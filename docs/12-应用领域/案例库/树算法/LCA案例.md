# 案例：LCA在文件系统路径解析与生物进化树分析中的应用

## 背景

在文件系统、类继承体系和生物分类学中，经常需要回答"两个节点的最近公共祖先是什么"。LCA（Lowest Common Ancestor）算法以 $O(1)$ 或 $O(\log n)$ 的查询时间解决这一问题，是树结构查询的基础工具。

## 问题定义

- **输入**：有根树 $T$，两个节点 $u, v$
- **输出**：$u$ 和 $v$ 的最近公共祖先（深度最大的共同祖先）

## 算法

### 倍增法（Binary Lifting）

预处理：

- `up[v][i]`：$v$ 的 $2^i$ 级祖先
- `depth[v]`：$v$ 的深度

查询：

1. 将较深节点上提到同一深度
2. 从最高位开始，若祖先不同则同时上提
3. 最终返回父节点

**预处理**：$O(n \log n)$，**查询**：$O(\log n)$

### Tarjan 离线算法

并查集 + DFS，离线处理所有查询。

**复杂度**：$O(n + q \cdot \alpha(n))$

### RMQ 转化

Euler Tour + 线段树/稀疏表，查询转化为 RMQ。

**预处理**：$O(n)$ 或 $O(n \log n)$，**查询**：$O(1)$

## 实际应用

### 文件系统路径解析

- 相对路径解析：`../../foo` 从当前目录出发
- 求两个目录的 LCA，计算相对路径
- Git 中分支合并点的确定

### 编程语言类型系统

- Java/C++ 多重继承/接口的菱形继承问题
- `instanceof` 检查：判断类型 A 是否是类型 B 的子类
- 异常处理：捕获最匹配的异常类型

### 生物进化树

- 物种分类树（界门纲目科属种）
- 比较两个物种的进化关系
- LCA 表示最近共同祖先物种
- 遗传距离估算

### DOM 树操作

- 浏览器 DOM 中，查找两个元素最近的共同容器
- 事件冒泡的停止判断
- React/Vue 的组件树 diff

### 版本控制

- Git 合并：找到两个分支的 LCA 作为合并基础
- 三路合并（3-way merge）的基础提交

## 代码参考

- TypeScript: `examples/algorithms-ts/src/tree.ts` → `LCA`
- Rust: `examples/algorithms/src/tree_algorithms/lca.rs`
- Java: `examples/algorithms-java/TreeAlgorithms.java` → `LCA`
- Go: `examples/algorithms-go/tree.go` → `LCA`

## 效果评估

- 倍增法查询：百万节点树，单次查询 $< 1\mu s$
- Git 合并：LCA 计算在大型仓库 $< 10$ms
- 生物进化树：LCA 是系统发育分析的基础操作
