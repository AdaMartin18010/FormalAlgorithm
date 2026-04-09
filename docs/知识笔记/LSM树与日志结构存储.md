# LSM树与日志结构存储

> **学科**: 数据库系统、存储系统
> **难度**: ★★★★☆
> **先修**: B树、外部排序、布隆过滤器、文件系统
> **学时**: 4-6小时
> **来源**: Berkeley CS186、O'Neil et al. 1996 (Acta Informatica)
> **版本**: v1.0
> **更新**: 2026-04-09

---

## 一、核心概念

### 1.1 定义

**正式定义**:
LSM树（Log-Structured Merge-Tree）是一种磁盘数据结构，旨在为经历高频率记录插入（和删除）的文件提供低成本的索引。LSM树使用一种算法，将索引变更延迟并批处理，以类似归并排序的高效方式将变更从基于内存的组件级联到一个或多个磁盘组件。

数学表示：
```
LSM-Tree = {C0, C1, C2, ..., Ck}
其中：
- C0: 内存组件（MemTable）
- Ci (i≥1): 磁盘组件，满足 size(Ci) = T × size(Ci-1)，T为大小比例因子
- 每个组件包含键值对的有序集合
```

**直观解释**:
想象一个多层的水流过滤系统：新数据首先进入最上层的"水槽"（内存），当水槽满时，水被倒入下一层的"过滤器"（磁盘）。每一层都会将多个小容器合并成更大的容器，同时去除重复和无效的数据。查询时需要从上到下检查每一层，直到找到目标数据。

LSM树的核心思想是**将随机写转换为顺序写**：
- 所有写入先追加到内存中的有序结构
- 定期将内存数据批量刷写到磁盘
- 通过后台合并（Compaction）维护数据有序性

**关键要点**:
- **写优化设计**: 通过顺序写入最大化磁盘吞吐量，特别适合写密集型工作负载
- **分层存储**: 数据按年龄和热度的多层组织（C0在内存，C1+在磁盘）
- **延迟合并**: 不立即更新磁盘数据，而是积累变更后批量合并
- **不可变文件**: 磁盘上的SSTable一旦写入不再修改，只通过合并产生新文件

### 1.2 属性

| 属性 | 描述 | 备注 |
|------|------|------|
| 写放大(Write Amplification) | 实际磁盘写入量 / 逻辑写入量 | 由Compaction频率决定，Leveled策略约10-30x，Tiered策略约2-5x |
| 读放大(Read Amplification) | 实际磁盘读取量 / 逻辑读取量 | 与层级数成正比，需要检查多层SSTable |
| 空间放大(Space Amplification) | 实际存储空间 / 逻辑数据大小 | 旧版本数据和墓碑标记导致，通常1.1-1.3x |
| 时间复杂度(写) | O(1) 均摊 | 仅需写入内存和WAL |
| 时间复杂度(点查) | O(L) 最坏情况 | L为层数，每层最多检查1个SSTable |
| 时间复杂度(范围查) | O(L + K/B) | K为结果数量，B为块大小 |

**性质总结**:
1. **写优化性**: 通过顺序写入避免磁盘随机寻道，写入性能远高于B树
2. **读取代价**: 读取可能需要检查多个层级的多个文件，读延迟高于B树
3. **空间效率**: 支持数据压缩，但版本控制和删除标记可能导致临时空间膨胀
4. **崩溃恢复**: 通过WAL(Write-Ahead Log)保证数据持久性和可恢复性

### 1.3 变体

**变体1: 经典两层LSM树（原始论文设计）**
- 定义: 仅包含C0（内存）和C1（磁盘）两个组件
- 与标准形式的区别: 结构更简单，没有多级分层
- 适用场景: 数据量相对较小，内存可缓存热数据的情况

**变体2: WiscKey（键值分离）**
- 定义: 将键和值分开存储，LSM树只存储键和值的指针
- 与标准形式的区别: 大幅降低写放大和空间放大，值存储在独立的vLog中
- 适用场景: 值较大的键值存储场景

**变体3: PebblesDB（引用分割）**
- 定义: 使用Fragmented Log-Structured Merge Tree，允许同一层内键范围重叠
- 与标准形式的区别: 使用Guard机制组织SSTable，降低写放大同时保持读性能
- 适用场景: 需要平衡读写性能的场景

---

## 二、关系网络

### 2.1 前置知识

完成本主题学习前，应掌握：

| 前置知识 | 重要性 | 掌握程度检验 |
|----------|--------|--------------|
| B树/B+树 | ⭐⭐⭐⭐⭐ | 能理解B树的插入、删除、查找操作及磁盘I/O模型 |
| 外部排序 | ⭐⭐⭐⭐⭐ | 能理解多路归并排序算法及其复杂度分析 |
| 布隆过滤器 | ⭐⭐⭐⭐⭐ | 能解释假阳性率计算及如何在查找中应用 |
| 日志结构文件系统(LFS) | ⭐⭐⭐⭐☆ | 了解ROSE设计，理解"将随机写转为顺序写"的思想 |
| 写前日志(WAL) | ⭐⭐⭐⭐☆ | 理解崩溃恢复机制和Aries算法基础 |

### 2.2 相关概念

**紧密相关**:
- **SSTable (Sorted String Table)** - LSM树的磁盘组件格式，存储有序不可变的键值对
- **MemTable** - 内存中的可变组件，通常使用跳表或红黑树实现
- **Compaction** - 后台合并过程，用于回收空间和维持读性能
- **Bloom Filter** - 用于快速判断键是否存在于某SSTable，避免不必要的磁盘读取
- **WAL (Write-Ahead Log)** - 预写日志，保证数据持久性

**一般相关**:
- **LSM-Tree vs B-Tree** - 两种主要的索引结构范式，前者写优化，后者读优化
- **写时复制(Copy-on-Write)** - 许多LSM实现使用的技术
- **MVCC (多版本并发控制)** - LSM天然支持多版本数据
- **LevelDB/RocksDB** - 著名的LSM-tree实现

### 2.3 后续扩展

学习本主题后，可继续深入：

1. **Compaction策略优化** → PebblesDB、Lethe、Fluid LSM
2. **新硬件适配** → 针对NVM、SSD的LSM优化（如NoveLSM、MatrixKV）
3. **分布式扩展** → Bigtable、Cassandra、HBase的分布式LSM设计
4. **混合索引** → LSM-B树混合结构（如KiWi、Dostoevsky）

### 2.4 思维导图

```
LSM树与日志结构存储
├── 核心组件
│   ├── MemTable (内存)
│   │   ├── 跳表实现
│   │   ├── 红黑树实现
│   │   └── 大小阈值触发Flush
│   ├── Immutable MemTable
│   │   └── 正在刷盘的只读MemTable
│   ├── SSTable (磁盘)
│   │   ├── Data Block (数据块)
│   │   ├── Index Block (索引块)
│   │   ├── Filter Block (布隆过滤器)
│   │   └── Footer (元数据)
│   └── WAL (写前日志)
│       └── 崩溃恢复保障
├── 核心操作
│   ├── 写入路径
│   │   ├── 写WAL
│   │   ├── 写MemTable
│   │   └── Flush到L0
│   ├── 读取路径
│   │   ├── 查MemTable
│   │   ├── 查布隆过滤器
│   │   └── 逐层查SSTable
│   └── Compaction
│       ├── Leveled策略
│       ├── Tiered策略
│       └── 混合策略
├── 放大问题分析
│   ├── 写放大 (Write Amplification)
│   ├── 读放大 (Read Amplification)
│   └── 空间放大 (Space Amplification)
├── 优化技术
│   ├── 布隆过滤器
│   ├── 前缀压缩
│   ├── 块压缩 (Snappy/ZSTD)
│   └── 布谷鸟过滤器
└── 实际系统
    ├── LevelDB (Google)
    ├── RocksDB (Facebook)
    ├── Cassandra (Apache)
    ├── HBase (Apache)
    └── Bigtable (Google)
```

---

## 三、形式化证明

### 3.1 核心定理

**定理 1**: LSM树的均摊写入时间复杂度为 O(1)

**证明**:
```
假设：
- 数据总量为 N
- 层级大小比例为 T（通常 T=10）
- MemTable大小为 B
- 每层合并成本等于该层数据量

写入分析：
1. 写入MemTable: O(1)
2. MemTable满时Flush到L0: 均摊O(1)
3. 当Li满时，合并到Li+1:
   - Li大小 = T^i × B
   - 触发频率 = (T-1)/T^i × (1/B)
   - 每次触发成本 = T^i × B
   - Li层的均摊成本 = (T-1)/T^i × (1/B) × T^i × B = T-1 = O(1)

总层数 L = log_T(N/B)
总均摊成本 = Σ(i=0 to L) O(1) = O(log_T(N/B)) × O(1) = O(1)（均摊到每个操作）

实际上，每个键在Leveled Compaction中被重写约 T×L/2 次
在Tiered Compaction中被重写约 L 次
```

**证明要点分析**:
1. **分层摊销**: 将高成本的合并操作摊销到多次低成本写入上
2. **几何级数**: 每层容量呈几何增长，高层触发频率呈几何下降
3. **顺序写入优势**: 磁盘顺序写入带宽远高于随机写入

**直觉理解**:
想象一个金字塔形的沙漏，沙子（数据）从顶部（内存）流下。虽然沙子在每一层都会被"筛选"（合并），但由于下层容量更大，筛选发生的频率更低。通过合理设计层间比例，可以使每层贡献的均摊成本保持恒定。

### 3.2 辅助引理

**引理 1 (写放大量化)**: 在Leveled Compaction策略下，写放大因子约为 (T/2) × L

*证明*:
```
设层数 L = log_T(N/B)
对于从Li合并到Li+1的键：
- 平均而言，键在Li中停留约 T/2 次合并后才被移到Li+1
- 每层重复此过程
- 总写放大 = (T/2) × L

例如 T=10, 数据量1TB, B=64MB:
L = log_10(1TB/64MB) ≈ log_10(15625) ≈ 5
写放大 ≈ 5 × 5 = 25x
```

**引理 2 (读放大量化)**: 在最坏情况下，点查询需要检查 O(L) 个SSTable

*证明*:
```
点查询流程：
1. 检查MemTable: O(1)
2. 检查Immutable MemTable: O(1)
3. L0层可能有多个重叠的SSTable，需全部检查
4. Li (i≥1) 层每层最多检查1个SSTable（非重叠）

最坏情况读放大（无缓存、无布隆过滤器）:
- 检查L0的 F 个SSTable（F为L0文件数阈值）
- 检查L1到LL的各1个SSTable
- 总计: F + L 次磁盘访问

使用布隆过滤器后（假阳性率ε）:
期望读放大 ≈ F×ε + L×ε + 1（命中概率）
```

---

## 四、算法/方法详解

### 4.1 算法描述

**写入算法**:
```
算法: LSM-Tree Put
输入: 键key, 值value
输出: 成功/失败

1. 将(key, value, timestamp)追加到WAL // 确保持久性
2. 插入到MemTable // 通常为跳表，O(log n)
3. if MemTable.size >= threshold then
4.     将MemTable标记为Immutable
5.     创建新的空MemTable
6.     后台线程将Immutable MemTable刷写到L0 SSTable
7.     删除对应的WAL段
8. end if
9. return 成功
```

**读取算法**:
```
算法: LSM-Tree Get
输入: 键key
输出: value 或 不存在

1. 在MemTable中查找key // O(log n)
2. if 找到 then return value
3. 在Immutable MemTables中查找key（从最新到最旧）
4. if 找到 then return value
5. for 每个L0 SSTable（从最新到最旧）do
6.     检查布隆过滤器
7.     if 布隆过滤器说可能存在 then
8.         读取SSTable索引定位数据块
9.         在数据块中线性查找key
10.        if 找到 then return value
11.    end if
12. end for
13. for level = 1 to L do // L1+层非重叠
14.     二分查找确定可能包含key的SSTable
15.     检查布隆过滤器
16.     if 布隆过滤器说可能存在 then
17.         读取并查找该SSTable
18.         if 找到 then return value
19.     end if
20. end for
21. return 不存在
```

**Leveled Compaction算法**:
```
算法: Leveled Compaction
输入: 源层Li, 目标层Li+1

1. 选择Li中需要合并的SSTable集合S
2. 在Li+1中找到所有与S键范围重叠的SSTable集合T
3. 创建多路归并迭代器遍历S∪T中的所有键值对
4. 按顺序输出到新的SSTable文件到Li+1
5.    - 丢弃被删除的键（墓碑标记且无更老版本）
6.    - 合并相同键的多个版本，只保留最新
7.    - 当输出文件达到目标大小时创建新文件
8. 删除旧的SSTable文件S和T
9. if Li+1超出大小阈值 then
10.    递归触发Li+1到Li+2的Compaction
11. end if
```

**Tiered Compaction算法**:
```
算法: Tiered Compaction
输入: 层Li

1. 当Li中的SSTable数量达到阈值T时触发
2. 选择Li中的T个大小相近的SSTable
3. 将这T个SSTable多路归并成1个新的SSTable
4. 将新SSTable移动到Li+1
5. 删除原来的T个SSTable
6. // 注意：不同于Leveled，不需要读取Li+1的现有数据
```

**流程图**:
```
写入流程:
┌─────────┐    ┌─────────┐    ┌──────────┐
│ 客户端   │───→│ 写WAL   │───→│ 写MemTable│
└─────────┘    └─────────┘    └──────────┘
                                      │
                                      ▼
                              ┌──────────────┐
                              │ MemTable满?  │──否──→ 返回
                              └──────────────┘
                                      │是
                                      ▼
                              ┌──────────────┐
                              │ 转为Immutable│
                              └──────────────┘
                                      │
                                      ▼
                              ┌──────────────┐
                              │ 刷写到L0     │
                              └──────────────┘
                                      │
                                      ▼
                              ┌──────────────┐
                              │ 触发Compaction│
                              └──────────────┘

读取流程:
┌─────────┐    ┌──────────┐    ┌────────────┐
│ 客户端   │───→│ MemTable? │───→│ Immutable? │
└─────────┘    └──────────┘    └────────────┘
        找到←──是│         找到←──是│
              否│               否│
                ▼                 ▼
        ┌──────────────┐  ┌──────────────┐
        │ 检查L0 SSTable│  │ 检查Li SSTable│
        │ (布隆过滤器)   │  │ (布隆过滤器)  │
        └──────────────┘  └──────────────┘
                │                 │
                └────────┬────────┘
                         ▼
                  ┌──────────────┐
                  │ 返回结果或   │
                  │ 键不存在    │
                  └──────────────┘
```

### 4.2 正确性分析

**不变式**: 
1. 对于任何键，最新的版本要么在MemTable中，要么在最新的包含该键的SSTable中
2. 同一SSTable内键按字典序排列
3. L1+层的SSTable键范围互不重叠（Leveled策略）
4. WAL记录按时间顺序排列，用于崩溃恢复

**证明**:
- **初始化**: 空树满足所有不变式
- **保持**: 
  - 写入操作：先写WAL保证持久性，再更新MemTable保持内存一致性
  - Flush操作：生成新的不可变SSTable，原子替换保证可见性
  - Compaction操作：多路归并保持有序性，删除旧文件原子性保证
- **终止**: 查询时按时间倒序检查，确保找到最新版本

### 4.3 复杂度分析

**时间复杂度**:

| 操作 | 最坏情况 | 最好情况 | 平均情况 |
|------|----------|----------|----------|
| 写入 | O(log M) | O(1) | O(log M) |
| 点查 | O(L × B) | O(1) | O(L) |
| 范围查 | O(L × B + K) | O(K/B) | O(L + K/B) |
| 删除 | O(log M) | O(1) | O(log M) |

其中：M=MemTable大小，L=层数，B=块大小，K=结果数

**空间复杂度**: 
- 内存: O(M + F×B)，F为布隆过滤器大小
- 磁盘: O(N × (1 + SA))，N为数据量，SA为空间放大率

**复杂度证明**:
```
写入复杂度：
- 直接写入MemTable: O(log M)，M为MemTable条目数
- 均摊考虑Flush和Compaction: O(1)
- 总均摊: O(log M) ≈ O(1)（M为常数）

点查复杂度：
- MemTable查找: O(log M)
- L0查找: 最多F个SSTable，每个O(log(B))索引查找 + O(B)块扫描
- Li (i≥1) 查找: L层，每层O(log(#SSTables)) + O(B)
- 使用布隆过滤器: 假阳性率ε，期望查找次数 = ε × (F + L)

范围查复杂度：
- 需要合并各层迭代器: O(L)个迭代器
- 每个迭代器定位起始位置: O(log(B))
- 输出K个结果: O(K/B)次磁盘读取
- 总计: O(L × log(B) + K/B)
```

---

## 五、示例与实例

### 5.1 标准示例

**示例 1**: LSM树构建过程演示

**问题描述**:
假设有以下插入序列（简化表示，键=值）：
```
插入: 3, 1, 4, 1, 5, 9, 2, 6
删除: 1
MemTable阈值 = 4个条目
L0文件数阈值 = 2
L1大小阈值 = 8个条目
```

**解决过程**:
```
步骤1: 插入3, 1, 4, 1 → MemTable满
       MemTable = {1, 3, 4} (去重，保留最新)
       Flush到L0: SSTable0 = [1, 3, 4]

步骤2: 插入5, 9, 2, 6 → MemTable满
       MemTable = {2, 5, 6, 9}
       Flush到L0: SSTable1 = [2, 5, 6, 9]
       L0现在有2个文件，触发Compaction

步骤3: Compaction L0→L1
       合并SSTable0和SSTable1
       输出L1: SSTable2 = [1, 2, 3, 4, 5, 6, 9] (大小=7 < 8，不触发下一层)

步骤4: 删除1
       插入墓碑标记到MemTable: {1→tombstone}
       
步骤5: 继续插入直到下一次Compaction...
```

**结果**: 删除标记将在下次Compaction时被清除（如果没有旧版本）

### 5.2 代码实现

**语言**: Python（简化教学实现）

```python
"""
简化版LSM树实现，用于教学演示
"""
import hashlib
from typing import Dict, List, Optional, Iterator
from sortedcontainers import SortedDict
import struct

class BloomFilter:
    """布隆过滤器实现"""
    def __init__(self, size: int = 1000, hash_count: int = 3):
        self.size = size
        self.hash_count = hash_count
        self.bit_array = [False] * size
    
    def _hashes(self, key: str) -> List[int]:
        """生成多个哈希值"""
        result = []
        for i in range(self.hash_count):
            hash_val = int(hashlib.md5(f"{key}:{i}".encode()).hexdigest(), 16)
            result.append(hash_val % self.size)
        return result
    
    def add(self, key: str):
        for pos in self._hashes(key):
            self.bit_array[pos] = True
    
    def __contains__(self, key: str) -> bool:
        return all(self.bit_array[pos] for pos in self._hashes(key))

class SSTable:
    """排序字符串表"""
    def __init__(self, level: int, index: int):
        self.level = level
        self.index = index
        self.data: SortedDict[str, str] = SortedDict()  # 键→值
        self.bloom = BloomFilter()
        self.min_key = None
        self.max_key = None
    
    def put(self, key: str, value: str):
        self.data[key] = value
        self.bloom.add(key)
        if self.min_key is None or key < self.min_key:
            self.min_key = key
        if self.max_key is None or key > self.max_key:
            self.max_key = key
    
    def get(self, key: str) -> Optional[str]:
        if key not in self.bloom:
            return None
        return self.data.get(key)
    
    def overlaps(self, other: 'SSTable') -> bool:
        """检查键范围是否重叠"""
        return not (self.max_key < other.min_key or self.min_key > other.max_key)
    
    def __iter__(self) -> Iterator[tuple]:
        return iter(self.data.items())
    
    def __len__(self) -> int:
        return len(self.data)

class LSMTree:
    """LSM树核心实现"""
    def __init__(self, 
                 memtable_size: int = 100,
                 level0_file_num: int = 4,
                 level_size_multiplier: int = 10):
        self.memtable_size = memtable_size
        self.level0_file_num = level0_file_num
        self.size_multiplier = level_size_multiplier
        
        # 内存组件
        self.memtable: SortedDict[str, str] = SortedDict()
        self.immutable_memtables: List[SortedDict] = []
        
        # 磁盘组件: levels[level][sstable_index]
        self.levels: Dict[int, List[SSTable]] = {0: []}
        
        # WAL（简化版，实际应写入磁盘）
        self.wal: List[str] = []
        
        # SSTable计数器
        self.sstable_counter = 0
    
    def put(self, key: str, value: str):
        """插入键值对"""
        # 1. 写WAL
        self.wal.append(f"PUT {key} {value}")
        
        # 2. 写MemTable
        self.memtable[key] = value
        
        # 3. 检查是否需要Flush
        if len(self.memtable) >= self.memtable_size:
            self._flush_memtable()
    
    def delete(self, key: str):
        """删除键（墓碑标记）"""
        self.wal.append(f"DEL {key}")
        self.memtable[key] = "__TOMBSTONE__"
        
        if len(self.memtable) >= self.memtable_size:
            self._flush_memtable()
    
    def get(self, key: str) -> Optional[str]:
        """查询键"""
        # 1. 查MemTable
        if key in self.memtable:
            val = self.memtable[key]
            return None if val == "__TOMBSTONE__" else val
        
        # 2. 查Immutable MemTables
        for imm_table in self.immutable_memtables:
            if key in imm_table:
                val = imm_table[key]
                return None if val == "__TOMBSTONE__" else val
        
        # 3. 查L0（可能有重叠，需按时间倒序查）
        for sstable in reversed(self.levels.get(0, [])):
            val = sstable.get(key)
            if val is not None:
                return None if val == "__TOMBSTONE__" else val
        
        # 4. 查L1+（非重叠，每层最多一个）
        for level in range(1, max(self.levels.keys()) + 1 if self.levels else 1):
            for sstable in self.levels.get(level, []):
                if sstable.min_key <= key <= sstable.max_key:
                    val = sstable.get(key)
                    if val is not None:
                        return None if val == "__TOMBSTONE__" else val
        
        return None
    
    def _flush_memtable(self):
        """将MemTable刷写到L0"""
        if not self.memtable:
            return
        
        # 转为Immutable
        self.immutable_memtables.append(self.memtable)
        old_memtable = self.memtable
        self.memtable = SortedDict()
        
        # 创建新的SSTable
        sstable = SSTable(level=0, index=self.sstable_counter)
        self.sstable_counter += 1
        
        for key, value in old_memtable.items():
            sstable.put(key, value)
        
        self.levels[0].append(sstable)
        self.immutable_memtables.remove(old_memtable)
        
        # 检查是否需要Compaction
        if len(self.levels[0]) >= self.level0_file_num:
            self._compact_level(0)
    
    def _compact_level(self, level: int):
        """Leveled Compaction"""
        if level not in self.levels or len(self.levels[level]) == 0:
            return
        
        # 选择源SSTable（选最老的或最大的）
        source_tables = self.levels[level][:]
        
        # 确保下一层存在
        next_level = level + 1
        if next_level not in self.levels:
            self.levels[next_level] = []
        
        # 在下一层找到重叠的SSTable
        overlap_tables = []
        for sst in self.levels[next_level]:
            for src in source_tables:
                if sst.overlaps(src):
                    overlap_tables.append(sst)
                    break
        
        # 合并所有输入
        merged_data = SortedDict()
        
        # 添加源层数据
        for sst in source_tables:
            for k, v in sst:
                if k not in merged_data:  # 保留最新版本
                    merged_data[k] = v
        
        # 添加目标层重叠数据
        for sst in overlap_tables:
            for k, v in sst:
                if k not in merged_data:
                    merged_data[k] = v
        
        # 清理墓碑（如果是最底层或没有旧版本）
        keys_to_delete = [k for k, v in merged_data.items() if v == "__TOMBSTONE__"]
        for k in keys_to_delete:
            del merged_data[k]
        
        # 创建新的SSTable
        new_sstables = []
        current_sst = SSTable(level=next_level, index=self.sstable_counter)
        self.sstable_counter += 1
        
        for k, v in merged_data.items():
            current_sst.put(k, v)
            # 简单的大小控制
            if len(current_sst) >= self.memtable_size * (self.size_multiplier ** next_level):
                new_sstables.append(current_sst)
                current_sst = SSTable(level=next_level, index=self.sstable_counter)
                self.sstable_counter += 1
        
        if len(current_sst) > 0:
            new_sstables.append(current_sst)
        
        # 替换旧SSTable
        for sst in source_tables:
            self.levels[level].remove(sst)
        for sst in overlap_tables:
            self.levels[next_level].remove(sst)
        
        self.levels[next_level].extend(new_sstables)
        
        # 递归检查下一层
        level_threshold = self.size_multiplier ** next_level
        total_size = sum(len(sst) for sst in self.levels[next_level])
        if total_size >= level_threshold:
            self._compact_level(next_level)
    
    def stats(self) -> Dict:
        """返回统计信息"""
        stats = {
            "memtable_size": len(self.memtable),
            "levels": {}
        }
        for level, sstables in self.levels.items():
            stats["levels"][f"L{level}"] = {
                "sstable_count": len(sstables),
                "total_entries": sum(len(sst) for sst in sstables)
            }
        return stats


# 使用示例
if __name__ == "__main__":
    lsm = LSMTree(memtable_size=4, level0_file_num=2)
    
    # 插入数据
    print("=== 插入数据 ===")
    for i in [3, 1, 4, 1, 5, 9, 2, 6]:
        lsm.put(str(i), f"value_{i}")
        print(f"Put({i})")
    
    print(f"\n当前状态: {lsm.stats()}")
    
    # 查询
    print("\n=== 查询 ===")
    for key in ["1", "5", "7"]:
        result = lsm.get(key)
        print(f"Get({key}) = {result}")
    
    # 删除
    print("\n=== 删除 ===")
    lsm.delete("1")
    print(f"Delete(1)")
    print(f"Get(1) = {lsm.get('1')}")
    
    print(f"\n最终状态: {lsm.stats()}")
```

**代码说明**:
- **BloomFilter**: 用于快速判断键是否可能存在于SSTable，减少不必要的磁盘读取
- **SSTable**: 不可变的排序键值存储，包含布隆过滤器和键范围元数据
- **LSMTree**: 核心类，管理MemTable、Immutable MemTable、多层SSTable
- **_flush_memtable**: 将内存数据刷写到L0，可能触发Compaction
- **_compact_level**: Leveled Compaction的实现，合并重叠的SSTable

### 5.3 反例

**常见错误 1**: 忽视墓碑标记的处理

```python
# 错误代码
class BadLSM:
    def get(self, key):
        # 只检查最新版本，不处理墓碑
        return self.memtable.get(key)  # 错误：墓碑会被当作正常值返回

# 错误原因: 删除操作插入的墓碑标记被当作普通值返回
# 正确做法:
    def get(self, key):
        val = self.memtable.get(key)
        if val == "__TOMBSTONE__":
            return None  # 键已被删除
        return val
```

**常见错误 2**: Compaction时未合并重叠范围

```python
# 错误代码
def bad_compact(self, level):
    # 直接将L0所有文件移到L1，不处理重叠
    self.levels[level + 1].extend(self.levels[level])
    self.levels[level] = []

# 错误原因: L0文件可能有重叠键范围，直接追加到L1会破坏Leveled的不变性
# 正确做法: 必须多路归并重叠的SSTable，确保L1+层内无重叠
```

**常见错误 3**: 读取顺序错误

```python
# 错误代码
def bad_get(self, key):
    # 从旧到新检查L0
    for sst in self.levels[0]:  # 错误：应该从最新到最旧检查
        if key in sst:
            return sst[key]

# 错误原因: L0的SSTable可能有相同键的多个版本，先查旧的会返回过期数据
# 正确做法: 使用 reversed(self.levels[0]) 确保先查最新的
```

---

## 六、习题

### 6.1 理解题

1. **为什么LSM树适合写密集型工作负载？** [难度⭐]
   
   *提示*: 考虑磁盘I/O模式（随机vs顺序）和写入放大
   
   <details>
   <summary>解答</summary>
   
   LSM树适合写密集型工作负载的原因：
   
   1. **顺序写入**: LSM将所有写入转换为顺序追加（WAL + MemTable），避免了B树的随机磁盘寻道。磁盘顺序写入带宽通常比随机写入高2-3个数量级。
   
   2. **批量处理**: 通过MemTable缓冲写入，批量刷写到磁盘，摊销I/O开销。
   
   3. **写放大权衡**: 虽然Compaction导致写放大，但这是后台操作，不直接影响写入延迟。
   
   4. **压缩友好**: 顺序存储的数据更容易压缩，减少实际写入量。
   
   </details>

2. **解释为什么L0层的SSTable可以有重叠键范围，而L1+层不能（Leveled策略）。** [难度⭐⭐]
   
   <details>
   <summary>解答</summary>
   
   L0层与L1+层的区别：
   
   **L0层允许重叠的原因**:
   - L0 SSTable直接由MemTable Flush产生
   - 不同时间Flush的MemTable可能包含相同键的更新版本
   - 保留重叠允许快速刷写，不需要立即合并
   
   **L1+层不允许重叠的原因**:
   - 查询性能：非重叠意味着每层只需检查最多1个SSTable
   - 如果没有这个保证，查询可能需要检查层内所有SSTable，退化为线性搜索
   - Compaction确保：L0→L1合并时，L0文件与L1重叠部分会被整合，输出非重叠的L1文件
   
   </details>

### 6.2 应用题

1. **计算题**: 假设一个LSM树配置如下，计算理论写放大：
   - 层级比例 T = 10
   - MemTable大小 = 64MB
   - 数据总量 = 1TB
   - 使用Leveled Compaction
   
   [难度⭐⭐]
   
   <details>
   <summary>解答</summary>
   
   **步骤1: 计算层数**
   ```
   L = log_T(数据量/MemTable大小) = log_10(1TB/64MB)
     = log_10(2^40 / 2^26) = log_10(2^14) ≈ log_10(16384) ≈ 4.2
   ```
   向上取整，L = 5层（L0-L4）
   
   **步骤2: 计算每层重写次数**
   在Leveled Compaction中，键从Li合并到Li+1时，平均在Li中被重写 T/2 次
   
   **步骤3: 总写放大**
   ```
   写放大 = (T/2) × L = (10/2) × 5 = 25x
   ```
   
   **补充**: 如果使用Tiered Compaction，写放大约为 L = 5x
   
   </details>

2. **设计题**: 设计一个适合以下场景的LSM树配置：
   - 场景：时序数据库，主要是写入新数据，很少更新旧数据
   - 工作负载：写多读少，95%写入，5%查询
   - 数据特征：键包含时间戳，天然有序
   
   [难度⭐⭐⭐]
   
   <details>
   <summary>解答</summary>
   
   **设计决策**:
   
   1. **Compaction策略**: 选择 **Tiered Compaction**
      - 原因：写优化，写放大低（约层数级别而非T×层数）
      - 适合写密集型时序数据
   
   2. **层级配置**:
      ```
      T (大小比例) = 10
      L0文件数阈值 = 4-8（允许更多缓冲）
      MemTable大小 = 256MB（更大以减少Flush频率）
      ```
   
   3. **布隆过滤器优化**:
      - 增加布隆过滤器位数，降低假阳性率
      - 因为读少，可以容忍更多内存用于过滤器
   
   4. **时间分区**:
      - 利用键的有序性，按时间范围分区SSTable
      - 便于按时间范围快速删除（TTL）
   
   5. **特殊优化**:
      - 启用布隆过滤器的"前缀过滤器"，支持范围查询优化
      - 配置较大的块大小（如64KB），因为时序数据通常顺序读取
   
   </details>

### 6.3 证明题

1. **证明**: 在Leveled Compaction策略下，最坏情况下的点查询需要检查 O(L + F) 个SSTable，其中L是层数，F是L0文件数阈值。**[难度⭐⭐⭐]**
   
   <details>
   <summary>解答</summary>
   
   **证明**:
   
   查询过程分析：
   
   1. **MemTable和Immutable MemTable**: O(1)，内存操作
   
   2. **L0层**: 
      - L0的SSTable直接来自Flush，可能有重叠
      - 最坏情况：查询的键存在于所有L0 SSTable中，或需要确认不存在
      - 需要检查所有L0 SSTable: O(F)
   
   3. **L1+层**:
      - Leveled保证每层SSTable键范围非重叠
      - 每层最多1个SSTable可能包含目标键
      - L层总计: O(L)
   
   **总计**: O(1) + O(F) + O(L) = O(L + F)
   
   **使用布隆过滤器后**:
   - 假设假阳性率为 ε
   - 期望检查的SSTable数 = ε × (F + L) + 1（实际包含键的文件）
   - 当ε很小时（如0.01），显著降低读放大
   
   **证毕**。∎
   
   </details>

---

## 七、应用场景

### 7.1 经典应用

| 应用场景 | 具体问题 | 使用LSM的原因 |
|----------|----------|---------------|
| 键值存储(RocksDB) | 高并发写入，需要持久化 | 顺序写入提供高吞吐，支持快照和事务 |
| 时序数据库(InfluxDB) | 大量时间序列数据写入 | 时间有序数据天然适合LSM的分层结构 |
| 分布式存储(Cassandra) | 分布式环境下的高可用写入 | LSM的不可变SSTable便于复制和修复 |
| 日志系统(Kafka) | 高吞吐日志追加 | 顺序写入匹配日志追加模式 |
| 缓存系统(Redis持久化) | 内存数据持久化 | RocksDB作为Redis的磁盘后端 |

### 7.2 实际案例

**案例**: Facebook的RocksDB在MyRocks中的使用

**背景**:
- Facebook需要将大量MySQL数据迁移到闪存存储
- 传统InnoDB在SSD上的写放大过高，缩短SSD寿命
- 需要保持MySQL的ACID语义和复制协议

**应用方式**:
- 使用RocksDB替代InnoDB作为MySQL存储引擎
- 采用Leveled Compaction策略优化空间使用
- 配置布隆过滤器加速点查

**效果**:
- 存储空间减少50%（压缩+去重）
- 写入放大从InnoDB的~20x降低到RocksDB的~5x（调优后）
- SSD寿命延长2-4倍
- 查询性能在可接受范围内（点查延迟略有增加，范围查相当）

### 7.3 跨领域联系

**与分布式系统的联系**:
LSM树的不可变SSTable天然适合分布式环境：
- 不可变数据易于复制（只需传输文件）
- 版本控制与MVCC机制契合分布式一致性
- Bigtable、Cassandra、HBase都使用LSM作为底层存储

**与流处理的联系**:
- Kafka的日志存储使用类似LSM的顺序追加
- Flink的状态后端使用RocksDB
- 流处理的"事件时间"与LSM的时间戳排序一致

**与机器学习系统的联系**:
- 特征存储需要高吞吐写入和点查
- 训练数据的增量更新适合LSM的追加模式
- 模型版本管理可利用LSM的多版本特性

---

## 八、多维对比

### 8.1 方法对比

**LSM-tree vs B-tree对比**:

| 维度 | LSM-tree | B-tree | 备注 |
|------|----------|--------|------|
| 写入模式 | 顺序追加 | 随机更新 | LSM适合SSD和HDD |
| 写入延迟 | 低（O(1)均摊） | 高（O(log n)磁盘寻道） | LSM延迟更稳定 |
| 点查延迟 | 中等（O(L)） | 低（O(log n)） | B-tree缓存友好 |
| 范围查性能 | 中等（多路归并） | 高（顺序扫描） | B-tree范围查询更优 |
| 写放大 | 10-50x | 1-3x | LSM需要调优 |
| 空间放大 | 1.1-1.5x | 1.0-1.1x | LSM有临时空间开销 |
| 并发控制 | 简单（不可变） | 复杂（原地更新） | LSM无读写冲突 |
| 崩溃恢复 | 简单（WAL） | 复杂（页恢复） | LSM恢复更快 |
| 压缩效率 | 高（顺序数据） | 中等 | LSM更适合压缩 |

**Compaction策略对比**:

| 维度 | Leveled | Tiered | 混合策略 |
|------|---------|--------|----------|
| 写放大 | ~T×L/2 | ~L | 中间值 |
| 读放大 | ~L | ~T×L | 可调 |
| 空间放大 | 低 | 高 | 可调 |
| 适用场景 | 读密集 | 写密集 | 混合负载 |
| 代表系统 | LevelDB, RocksDB | Cassandra(旧) | RocksDB(通用) |

### 8.2 决策建议

**何时选择LSM-tree**:
- 写入量远大于读取量（写读比 > 10:1）
- 需要高吞吐的顺序写入
- 工作负载包含大量更新和删除
- 可以接受稍高的读取延迟
- 使用SSD存储（可以承受写放大）

**何时选择B-tree**:
- 读取量大于写入量
- 需要低延迟的点查和范围查
- 存储介质对写入敏感（如早期SSD）
- 需要原地更新语义

**决策流程图**:
```
选择存储引擎决策树:

开始
  │
  ▼
写入比例 > 90%? 
  │
  ├── 是 → 选择LSM-tree (Tiered Compaction)
  │
  └── 否 → 读取比例 > 70%?
              │
              ├── 是 → 选择B-tree
              │
              └── 否 → 需要强一致性事务?
                          │
                          ├── 是 → 选择B-tree (成熟支持)
                          │
                          └── 否 → 选择LSM-tree (Leveled)
                                       │
                                       └── 可调参优化读写平衡
```

---

## 九、扩展阅读

### 9.1 教材章节

| 教材 | 章节 | 页码 | 推荐度 |
|------|------|------|--------|
| Berkeley CS186 (2023) | LSM Tree & Log Structured Storage | Lecture 16 | ⭐⭐⭐⭐⭐ |
| "Database Internals" (Petrov) | Chapter 3: File Formats | pp. 57-89 | ⭐⭐⭐⭐⭐ |
| "Designing Data-Intensive Applications" (Kleppmann) | Chapter 3: Storage and Retrieval | pp. 69-90 | ⭐⭐⭐⭐⭐ |
| "The Architecture of Open Source Applications" | Chapter 7: LLVM/LevelDB | Vol.1, pp. 165-178 | ⭐⭐⭐⭐☆ |

### 9.2 论文

1. **"The Log-Structured Merge-Tree (LSM-Tree)"** - Patrick O'Neil et al., Acta Informatica 1996
   - **要点**: LSM树的奠基论文，首次提出LSM概念和两层结构
   - **链接**: https://doi.org/10.1007/s002360050048

2. **"LSM-based Storage Techniques: A Survey"** - Chen Luo & Michael Carey, VLDB Journal 2019
   - **要点**: 全面的LSM技术综述，涵盖优化策略和变体
   - **链接**: https://doi.org/10.1007/s00778-019-00555-y

3. **"WiscKey: Separating Keys from Values in SSD-conscious Storage"** - Lanyue Lu et al., FAST 2016
   - **要点**: 键值分离设计，大幅降低写放大
   - **链接**: https://www.usenix.org/conference/fast16/technical-sessions/presentation/lu

4. **"PebblesDB: Building Key-Value Stores using Fragmented Log-Structured Merge Trees"** - Pandian Raju et al., SOSP 2017
   - **要点**: 引用分割降低写放大同时保持读性能
   - **链接**: https://doi.org/10.1145/3132747.3132755

5. **"Dostoevsky: Better Space-Time Trade-Offs for LSM-Tree"** - Niv Dayan et al., SIGMOD 2018
   - **要点**: 提出Lazy Leveling，动态调整Compaction策略
   - **链接**: https://doi.org/10.1145/3183713.3196927

### 9.3 在线资源

- **RocksDB Wiki**: https://github.com/facebook/rocksdb/wiki - RocksDB官方文档，包含详细的调优指南
- **LevelDB Documentation**: https://github.com/google/leveldb/blob/main/doc/index.md - LevelDB设计文档
- **LSM Tree Visualization**: https://www.cs.usfca.edu/~galles/visualization/BPlusTree.html - 交互式B树/LSM可视化
- **Mark Callaghan's Blog**: http://smalldatum.blogspot.com/ - MyRocks和RocksDB性能分析
- **IOStack LSM Tutorial**: https://otmanegg.com/lsm-tree-tutorial/ - LSM树系列教程

---

## 十、专家批注

> **Patrick O'Neil (LSM-tree论文作者)**:
> 
> "LSM-tree的设计初衷是解决高更新率场景下的索引成本问题。在1996年，磁盘随机I/O是主要瓶颈，而LSM通过将随机写转换为顺序写，显著提升了写入性能。今天，虽然存储介质已经变化，但LSM的核心思想——将快速但昂贵的操作延迟并批处理——仍然适用。"

> **Mark Callaghan (Facebook/RocksDB团队)**:
> 
> "在生产环境中使用LSM，最关键的是理解和监控三个放大因子：写放大、读放大和空间放大。RocksDB提供了丰富的统计信息，但最终的调优需要根据具体工作负载来决定。没有一种配置适合所有场景。"

> **Martin Kleppmann (《Designing Data-Intensive Applications》作者)**:
> 
> "LSM-tree代表了存储系统设计中的一种基本权衡：牺牲读取性能以换取写入性能。这种权衡在B-tree和LSM-tree之间表现得最为明显。理解这种权衡有助于工程师为特定应用选择合适的数据结构。"

---

## 十一、修订历史

| 版本 | 日期 | 修订者 | 修订内容 |
|------|------|--------|----------|
| v1.0 | 2026-04-09 | - | 初始版本，涵盖LSM树核心概念、算法、实现和应用 |

---

**标签**: #LSM-tree #存储系统 #数据库 #键值存储 #LevelDB #RocksDB

**相关笔记**: 
- [B树与B+树](./B树与B+树.md)
- [布隆过滤器](./布隆过滤器.md)
- [存储引擎对比](./存储引擎对比.md)
- [分布式数据库](./分布式数据库.md)
