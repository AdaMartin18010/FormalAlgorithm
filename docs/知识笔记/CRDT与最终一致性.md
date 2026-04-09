# CRDT与最终一致性

> **学科**: 分布式系统
> **难度**: ★★★★☆
> **先修**: 分布式系统基础、数据类型理论、序理论
> **学时**: 6学时
> **来源**: Shapiro《Conflict-free Replicated Data Types》, Marc Shapiro's CRDT Papers
> **版本**: v1.0
> **更新**: 2026-04-09

---

## 一、核心概念

### 1.1 定义

**正式定义**:
**CRDT（Conflict-free Replicated Data Type）**是在无协调情况下自动解决冲突的复制数据类型，保证最终一致性。

**最终一致性**: 若停止更新，所有副本最终收敛到相同状态。

**强最终一致性**: 在最终一致性基础上，若更新已传播到所有节点，副本立即一致（无需等待）。

**两类CRDT**:

1. **基于状态的CRDT（State-based / CvRDT）**: 通过合并整个状态传播更新
2. **基于操作的CRDT（Operation-based / CmRDT）**: 通过广播操作传播更新

**半格（Semilattice）**: 集合 $S$ 与合并操作 $\sqcup$ 满足：

- 交换律: $x \sqcup y = y \sqcup x$
- 结合律: $(x \sqcup y) \sqcup z = x \sqcup (y \sqcup z)$
- 幂等性: $x \sqcup x = x$

**直观解释**:
CRDT就像"可以独立编辑然后自动合并的文档"。
多人同时编辑时，传统方式需要锁定（协调），CRDT则允许各自编辑后自动合并，保证最终结果一致。
基于状态的CRDT像"发送整个文档让对方合并"，基于操作的CRDT像"只发送修改操作"。

**关键要点**:

- **无协调**: 不需要共识协议
- **单调性**: 状态单调增长（或定义合理的合并）
- **交换性**: 操作顺序不影响结果
- **应用场景**: 协作编辑、分布式计数器、购物车

### 1.2 属性

| 属性 | 描述 | 备注 |
|------|------|------|
| 交换性 | 操作顺序无关 | 冲突解决基础 |
| 结合性 | 分组方式无关 | 任意合并顺序 |
| 幂等性 | 重复应用无影响 | 容忍重复传输 |
| 单调性 | 状态单向增长 | 基于状态的CRDT |

**性质总结**:

1. **收敛性**: 半格性质保证收敛
2. **去重**: 幂等性容忍消息重复
3. **可用性**: 分区期间仍可读写
4. **因果一致性**: 可加强为因果+最终一致

### 1.3 变体

**G-Set（Grow-only Set）**:

- 定义: 只增不减的集合
- 操作: 添加元素
- 合并: 集合的并

**OR-Set（Observed-Remove Set）**:

- 定义: 支持添加和删除的集合
- 关键: 每个元素带唯一标记，删除时记住已观察的标记
- 解决: 删除后添加的冲突

**LWW-Register（Last-Writer-Wins）**:

- 定义: 用时间戳解决写入冲突
- 策略: 保留时间戳最新的值
- 问题: 时钟偏差可能导致数据丢失

---

## 二、关系网络

### 2.1 前置知识

| 前置知识 | 重要性 | 掌握程度检验 |
|----------|--------|--------------|
| 序理论（偏序、格） | ⭐⭐⭐⭐⭐ | 理解半格性质 |
| 向量时钟 | ⭐⭐⭐⭐⭐ | 理解因果序 |
| 复制理论 | ⭐⭐⭐⭐⭐ | 理解副本同步 |
| 最终一致性 | ⭐⭐⭐⭐⭐ | 理解BASE理论 |

### 2.2 相关概念

**紧密相关**:

- Gossip协议 - 状态传播机制
- 向量时钟 - 因果跟踪
- 版本向量 - 并发检测

**一般相关**:

- 分布式事务 - 强一致性方案
- 乐观复制 - 冲突处理策略

### 2.3 后续扩展

学习本主题后，可继续深入：

1. Delta-CRDT - 增量状态传播
2. 纯操作式CRDT - 无状态存储
3. CRDT与数据库 - Riak, Redis CRDT

### 2.4 思维导图

```
CRDT与最终一致性
├── 基础理论
│   ├── 最终一致性
│   ├── 强最终一致性
│   ├── 半格理论
│   └── 单调性
├── CRDT类型
│   ├── 基于状态 (CvRDT)
│   │   ├── G-Counter
│   │   ├── PN-Counter
│   │   ├── G-Set
│   │   ├── 2P-Set
│   │   ├── OR-Set
│   │   └── LWW-Register
│   └── 基于操作 (CmRDT)
│       ├── 操作广播
│       ├── 因果广播
│       └── 可靠传输
├── 实现技术
│   ├── 向量时钟
│   ├── 版本向量
│   ├── Dotted Version Vectors
│   └── Delta-State
├── 协作应用
│   ├── 协同文本编辑
│   ├── 共享白板
│   └── 分布式计数器
└── 数据库集成
    ├── Riak
    ├── Redis CRDT
    └── AntidoteDB
```

---

## 三、形式化证明

### 3.1 核心定理

**定理 1 (CRDT收敛性)**: 基于状态的CRDT在半格 $(S, \sqcup)$ 上实现强最终一致性。

**证明**:

**设定**: 每个副本维护状态 $s_i \in S$，通过合并操作 $\sqcup$ 同步。

**更新传播**:

- 副本 $i$ 本地更新: $s_i \leftarrow s_i \sqcup \Delta$
- 副本间合并: $s_i \leftarrow s_i \sqcup s_j$

**收敛性**:
由于 $\sqcup$ 满足：

1. **交换律**: $s_i \sqcup s_j = s_j \sqcup s_i$，合并顺序无关
2. **结合律**: $(s_i \sqcup s_j) \sqcup s_k = s_i \sqcup (s_j \sqcup s_k)$，分组无关
3. **幂等性**: $s_i \sqcup s_i = s_i$，重复合并无影响

所有副本应用相同更新集合后：
$$s_{final} = \bigsqcup_{\text{all updates}} \Delta$$

由于半格性质，最终状态唯一确定。

∎

**证明要点分析**:

1. 半格性质是收敛的充分条件
2. 不需要中央协调
3. 容忍任意网络延迟和乱序

**定理 2 (CmRDT与CvRDT等价性)**: 基于操作的CRDT可模拟基于状态的CRDT，反之亦然。

*证明概要*: 操作可累积为状态，状态变化可表示为操作。∎

### 3.2 辅助引理

**引理 1 (G-Counter的正确性)**: 增量计数器的合并结果等于各副本增量的总和。

*证明*: G-Counter维护向量 $[c_1, \ldots, c_n]$，$c_i$ 为副本 $i$ 的增量。合并取各分量最大值，总和为 $\sum \max_j(c_{i,j}) = \sum$ 实际增量。∎

**引理 2 (OR-Set的收敛性)**: OR-Set在添加-删除冲突时保留添加优先语义。

*证明*: 每个添加生成唯一标记，删除记录已观察的标记。合并时，标记不在删除集合的元素存在。∎

---

## 四、算法/方法详解

### 4.1 算法描述

**G-Counter（递增计数器）**:

```
类型: 向量 P[1..n]  // n个副本，初始为0

increment(i):  // 副本i执行
    P[i] ← P[i] + 1

value():  // 读取计数器值
    return Σ P[j]  for j=1 to n

merge(P, Q):  // 合并两个计数器
    for j = 1 to n do
        R[j] ← max(P[j], Q[j])
    end for
    return R
```

**OR-Set（观察删除集合）**:

```
类型: (A, R)  // A=添加标记集合, R=删除标记集合
// 元素e存在当且仅当存在标记(a, e) ∈ A \ R

add(e, i):  // 副本i添加元素e
    a ← generate_unique_tag(i)
    A ← A ∪ {(a, e)}

remove(e, i):  // 副本i删除元素e
    // 记录所有观察到的e的标记
    R ← R ∪ {(a, e) ∈ A : e = target}

lookup(e):  // 检查e是否存在
    return ∃a: (a, e) ∈ A ∧ (a, e) ∉ R

merge((A1, R1), (A2, R2)):
    A ← A1 ∪ A2
    R ← R1 ∪ R2
    return (A, R)
```

**基于操作的CRDT广播**:

```
类型: 操作队列 O，因果广播层

update(op):  // 执行本地更新
    apply(op)
    causal_broadcast(op)

deliver(op):  // 收到远程操作
    if causal_ready(op) then
        apply(op)
    else
        buffer(op)  // 等待因果前置
    end if

apply(op):
    // 根据操作类型更新本地状态
    // 操作需满足交换性和幂等性
```

**流程图**:

```
副本A:        副本B:
  ↓              ↓
本地更新 → 传播 → 接收合并
  ↓              ↓
状态合并 ← 传播 ← 本地更新
  ↓              ↓
最终一致     最终一致
```

### 4.2 正确性分析

**G-Counter正确性**:

- 每个副本只增加自己的计数器
- 合并取最大值保留所有增量
- 总和等于所有增量之和

**OR-Set正确性**:

- 添加生成唯一标记
- 删除记录观察到的标记
- 合并后，未被删除的添加标记保留
- 解决删除后添加的冲突（添加胜）

### 4.3 复杂度分析

**空间复杂度**:

- G-Counter: $O(n)$，$n$ 为副本数
- OR-Set: $O(m)$，$m$ 为历史操作数（可GC）

**时间复杂度**:

- 本地操作: $O(1)$（摊还）
- 合并: $O(s)$，$s$ 为状态大小

---

## 五、示例与实例

### 5.1 标准示例

**示例 1: G-Counter操作**

**初始**: 两个副本 A 和 B，计数器均为 $[0, 0]$

**操作序列**:

1. A 增加3次: A = $[3, 0]$
2. B 增加2次: B = $[0, 2]$
3. A 和 B 合并: 结果 = $[3, 2]$
4. 读取值: $3 + 2 = 5$

**示例 2: OR-Set处理冲突**

**场景**: 购物车添加商品"苹果"

**副本A**:

- 添加"苹果": A = ({(a1, "苹果")}, {})

**副本B**:

- 添加"苹果": B = ({(a2, "苹果")}, {})
- 删除"苹果": B = ({(a2, "苹果")}, {(a2, "苹果")})

**合并**:

- A ∪ B = ({(a1, "苹果"), (a2, "苹果")}, {(a2, "苹果")})
- 结果: "苹果"存在（标记a1未被删除）

**语义**: 保留A的添加（A未看到B的删除）

### 5.2 代码实现

**Python实现**:

```python
import uuid
from typing import Set, Tuple, Dict, Any
from dataclasses import dataclass

class GCounter:
    """递增计数器 (State-based CRDT)"""

    def __init__(self, replica_id: int, num_replicas: int):
        self.id = replica_id
        self.n = num_replicas
        self.p = [0] * num_replicas

    def increment(self):
        """本地增加"""
        self.p[self.id] += 1

    def value(self) -> int:
        """读取计数值"""
        return sum(self.p)

    def merge(self, other: 'GCounter') -> 'GCounter':
        """合并另一个计数器"""
        result = GCounter(self.id, self.n)
        for i in range(self.n):
            result.p[i] = max(self.p[i], other.p[i])
        return result

    def __repr__(self):
        return f"GCounter({self.p}, value={self.value()})"

class PNCounter:
    """可增可减计数器"""

    def __init__(self, replica_id: int, num_replicas: int):
        self.id = replica_id
        self.n = num_replicas
        self.p = [0] * num_replicas  # 增加计数
        self.n_counter = [0] * num_replicas  # 减少计数

    def increment(self):
        self.p[self.id] += 1

    def decrement(self):
        self.n_counter[self.id] += 1

    def value(self) -> int:
        return sum(self.p) - sum(self.n_counter)

    def merge(self, other: 'PNCounter') -> 'PNCounter':
        result = PNCounter(self.id, self.n)
        for i in range(self.n):
            result.p[i] = max(self.p[i], other.p[i])
            result.n_counter[i] = max(self.n_counter[i], other.n_counter[i])
        return result

@dataclass
class ORSet:
    """观察删除集合"""
    adds: Set[Tuple[str, Any]]  # (tag, element)
    removes: Set[Tuple[str, Any]]

    def __init__(self):
        self.adds = set()
        self.removes = set()

    def add(self, element: Any, replica_id: str):
        """添加元素"""
        tag = f"{replica_id}:{uuid.uuid4()}"
        self.adds.add((tag, element))
        return tag

    def remove(self, element: Any):
        """删除元素（记录观察到的所有标记）"""
        for tag, elem in list(self.adds):
            if elem == element:
                self.removes.add((tag, elem))

    def contains(self, element: Any) -> bool:
        """检查元素是否存在"""
        for tag, elem in self.adds:
            if elem == element and (tag, elem) not in self.removes:
                return True
        return False

    def elements(self) -> Set[Any]:
        """获取所有存在的元素"""
        result = set()
        for tag, elem in self.adds:
            if (tag, elem) not in self.removes:
                result.add(elem)
        return result

    def merge(self, other: 'ORSet') -> 'ORSet':
        """合并两个ORSet"""
        result = ORSet()
        result.adds = self.adds | other.adds
        result.removes = self.removes | other.removes
        return result

# 使用示例
if __name__ == "__main__":
    # G-Counter示例
    print("=== G-Counter ===")
    counter_a = GCounter(0, 2)
    counter_b = GCounter(1, 2)

    counter_a.increment()
    counter_a.increment()
    counter_b.increment()

    print(f"A: {counter_a}")
    print(f"B: {counter_b}")

    merged = counter_a.merge(counter_b)
    print(f"合并后: {merged}")

    # OR-Set示例
    print("\n=== OR-Set ===")
    set_a = ORSet()
    set_b = ORSet()

    # A添加"apple"
    set_a.add("apple", "A")
    print(f"A添加后，A包含apple: {set_a.contains('apple')}")

    # B添加"apple"然后删除
    set_b.add("apple", "B")
    set_b.remove("apple")
    print(f"B操作后，B包含apple: {set_b.contains('apple')}")

    # 合并
    merged_set = set_a.merge(set_b)
    print(f"合并后包含apple: {merged_set.contains('apple')}")
    print(f"合并后元素: {merged_set.elements()}")
```

### 5.3 反例

**常见错误**:

**错误1: 使用普通集合实现去重计数**

```python
# 错误：使用普通集合
class BadSet:
    def __init__(self):
        self.elements = set()

    def add(self, e):
        self.elements.add(e)

    def remove(self, e):
        self.elements.discard(e)  # 普通删除

    def merge(self, other):
        self.elements |= other.elements  # 简单并集
# 问题：删除后无法重新添加，冲突处理错误
```

**错误原因**: 普通集合无法满足CRDT语义
**正确做法**: 使用OR-Set或带标记的集合

**错误2: 忽略因果序**

```python
# 错误：直接应用操作
ops = [op1, op2, op3]  # 乱序接收
for op in ops:
    apply(op)  # 可能因果违规！
```

**错误原因**: CmRDT需要因果序
**正确做法**: 检查因果前置或使用向量时钟

---

## 六、习题

### 6.1 理解题

1. **解释**: 为什么CRDT能保证强最终一致性而不需要协调？

   <details>
   <summary>解答</summary>

   CRDT保证强最终一致性的原因：

   1. **半格性质**:
      - 合并操作满足交换律、结合律、幂等性
      - 这保证了无论以何种顺序、多少次合并，结果都相同

   2. **单调性**:
      - 状态单调增长（或按定义好的方式演进）
      - 不会产生无法调和的冲突

   3. **冲突避免**:
      - 通过设计消除冲突（如添加唯一标记）
      - 而非检测和解决冲突

   4. **无协调需要**:
      - 不需要共识协议确定全局顺序
      - 每个副本可独立处理更新

   对比传统复制：
   - 传统：需要锁或共识来保证一致性
   - CRDT：通过数据结构设计天然避免冲突
   </details>

### 6.2 应用题

1. **设计**: 设计一个支持优先级覆盖的LWW-Element-Set（最后写入者胜的元素集合）。

   <details>
   <summary>解答</summary>

   ```python
   class LWWElementSet:
       """最后写入者胜的元素集合"""

       def __init__(self):
           self.adds = {}  # element -> (timestamp, replica_id)
           self.removes = {}  # element -> (timestamp, replica_id)

       def add(self, element, timestamp, replica_id):
           if element not in self.adds or \
              (timestamp, replica_id) > self.adds[element]:
               self.adds[element] = (timestamp, replica_id)

       def remove(self, element, timestamp, replica_id):
           if element not in self.removes or \
              (timestamp, replica_id) > self.removes[element]:
               self.removes[element] = (timestamp, replica_id)

       def contains(self, element) -> bool:
           if element not in self.adds:
               return False
           if element not in self.removes:
               return True
           return self.adds[element] > self.removes[element]

       def merge(self, other):
           result = LWWElementSet()
           # 合并adds: 取每个元素的最大时间戳
           all_elements = set(self.adds.keys()) | set(other.adds.keys())
           for e in all_elements:
               candidates = []
               if e in self.adds:
                   candidates.append(self.adds[e])
               if e in other.adds:
                   candidates.append(other.adds[e])
               result.adds[e] = max(candidates)

           # 类似合并removes
           return result
   ```

   </details>

### 6.3 证明题

1. **证明**: 证明G-Counter的合并操作形成半格。

   <details>
   <summary>解答</summary>

   **证明**:

   设 $P = [p_1, \ldots, p_n]$，$Q = [q_1, \ldots, q_n]$ 为计数器向量。

   定义合并 $P \sqcup Q = [\max(p_1, q_1), \ldots, \max(p_n, q_n)]$。

   **交换律**:
   $P \sqcup Q = [\max(p_i, q_i)] = [\max(q_i, p_i)] = Q \sqcup P$ ✓

   **结合律**:
   $(P \sqcup Q) \sqcup R = [\max(\max(p_i, q_i), r_i)] = [\max(p_i, q_i, r_i)] = P \sqcup (Q \sqcup R)$ ✓

   **幂等性**:
   $P \sqcup P = [\max(p_i, p_i)] = [p_i] = P$ ✓

   因此 $(P, \sqcup)$ 形成半格。
   ∎
   </details>

---

## 七、应用场景

### 7.1 经典应用

| 应用场景 | 具体问题 | 使用本主题的原因 |
|----------|----------|------------------|
| 协同编辑 | 实时文档协作 | 无锁并发编辑 |
| 分布式购物车 | 电商系统 | 离线可用、合并购物车 |
| 社交网络 | 点赞/关注计数 | 高可用、最终一致 |
| 物联网 | 传感器数据聚合 | 容忍网络分区 |

### 7.2 实际案例

**案例**: Riak分布式数据库

**背景**: Riak使用CRDT作为数据类型

**应用方式**:

1. 支持计数器、集合、映射等CRDT
2. 自动处理并发更新
3. 无需手动冲突解决

**效果**: 高可用、分区容忍的数据存储

### 7.3 跨领域联系

**与数据库理论的联系**:
CRDT提供了BASE理论的形式化基础，与ACID形成对比。

**与分布式算法的联系**:
CRDT可与共识算法结合，实现从最终一致到强一致的可调一致性。

---

## 八、多维对比

### 8.1 方法对比

| 维度 | G-Set | OR-Set | LWW-Register | 分布式锁 |
|------|-------|--------|-------------|---------|
| 功能 | 只增集合 | 完整集合 | 单值 | 通用 |
| 冲突解决 | 无冲突 | 添加胜 | 时间戳 | 互斥 |
| 可用性 | 最高 | 高 | 高 | 低 |
| 一致性 | 最终 | 最终 | 最终 | 强 |
| 适用场景 | 日志、标签 | 购物车 | 配置 | 关键数据 |

### 8.2 决策建议

**何时使用CRDT**:

- 高可用性优先
- 可接受最终一致性
- 数据类型适合CRDT建模

**何时使用强一致性**:

- 一致性优先
- 数据强关联
- 可接受协调开销

---

## 九、扩展阅读

### 9.1 教材章节

| 教材 | 章节 | 页码 | 推荐度 |
|------|------|------|--------|
| Shapiro et al. | CRDT Survey | - | ⭐⭐⭐⭐⭐ |

### 9.2 论文

1. **"Conflict-free Replicated Data Types"** - Shapiro et al., 2011
   - **要点**: CRDT的奠基性论文

2. **"A Comprehensive Study of Convergent and Commutative Replicated Data Types"** - Shapiro et al., 2011
   - **要点**: CRDT分类与实现

### 9.3 在线资源

- **CRDT.tech**: <https://crdt.tech/> - CRDT资源汇总
- **Riak Documentation**: <https://docs.riak.com/>

---

## 十、专家批注

> **Marc Shapiro (CRDT发明人)**:
> CRDT证明了我们可以通过聪明的数据结构设计，在不需要协调的情况下实现可扩展的复制系统。

> **Peter Bailis**:
> 最终一致性不是缺陷，而是特征——它让系统在网络分区时仍可用。

---

## 十一、修订历史

| 版本 | 日期 | 修订者 | 修订内容 |
|------|------|--------|----------|
| v1.0 | 2026-04-09 | 系统 | 初始版本 |

---

**标签**: #分布式系统 #CRDT #最终一致性 #协作编辑 #无冲突复制

**相关笔记**:

- [分布式共识算法深化](分布式共识算法深化.md)
- [Gossip协议与epidemic广播](Gossip协议与epidemic广播.md)
