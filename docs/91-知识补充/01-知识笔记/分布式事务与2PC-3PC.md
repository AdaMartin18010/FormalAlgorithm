---
title: 分布式事务与2PC 3PC
version: 1.0
last_updated: 2026-04-19
---

# 分布式事务与2PC-3PC

> **学科**: 分布式系统
> **难度**: ★★★★☆
> **先修**: 数据库事务、分布式系统基础、故障模型
> **学时**: 6学时
> **来源**: Bernstein《Principles of Transaction Processing》, Gray《Notes on Data Base Operating Systems》
> **版本**: v1.0
> **更新**: 2026-04-09

---

## 一、核心概念

### 1.1 定义

**正式定义**:
**分布式事务**是跨越多个网络节点的事务，需要保证 **ACID** 特性：
- **原子性（Atomicity）**: 所有参与者要么全部提交，要么全部中止
- **一致性（Consistency）**: 事务保持数据库约束
- **隔离性（Isolation）**: 并发事务互不影响
- **持久性（Durability）**: 已提交事务的结果永久保存

**两阶段提交（2PC）**:
协调者（Coordinator）通过两阶段协议确保原子性：
1. **投票阶段（Voting Phase）**: 协调者询问所有参与者是否可以提交
2. **提交阶段（Commit Phase）**: 根据投票结果决定提交或中止

**三阶段提交（3PC）**:
在2PC基础上增加预提交阶段，减少阻塞：
1. **CanCommit阶段**: 参与者检查本地资源
2. **PreCommit阶段**: 参与者预执行，不释放锁
3. **DoCommit阶段**: 最终提交

**直观解释**:
2PC就像"组织一次聚餐"：先问所有人"能不能来"（投票阶段），如果所有人说能，再发确认"聚餐确定"（提交阶段）；如果有人说不能，发"聚餐取消"（中止阶段）。3PC增加了"预备备"阶段，让参与者在听到"确定"前保持准备状态，这样即使协调者挂了，参与者也能互相询问做决定。

**关键要点**:
- **阻塞问题**: 2PC中协调者故障可能导致参与者阻塞
- **超时处理**: 参与者通过超时机制推断协调者状态
- **日志先行**: 写日志先于操作，支持恢复
- **3PC非阻塞**: 网络分区时仍可推进，但可能不一致

### 1.2 属性

| 属性 | 描述 | 备注 |
|------|------|------|
| 原子性 | 全提交或全中止 | 2PC的核心目标 |
| 阻塞性 | 2PC可能阻塞 | 协调者单点问题 |
| 容错性 | 可容忍 $f < n/2$ 崩溃 | 日志恢复 |
| 性能开销 | 多次网络往返 | 延迟增加 |

**性质总结**:
1. **2PC阻塞条件**: 协调者故障且某参与者已投赞成票，其他参与者阻塞
2. **3PC非阻塞**: 引入预提交，参与者可独立决策
3. **脑裂风险**: 3PC在网络分区时可能不一致
4. **单点故障**: 协调者是2PC的弱点

### 1.3 变体

**阻塞2PC（Blocking 2PC）**:
- 定义: 标准2PC实现
- 与非阻塞的区别: 协调者故障时参与者阻塞
- 适用场景: 高可用网络环境

**非阻塞3PC（Non-blocking 3PC）**:
- 定义: 引入超时和预提交
- 与2PC的区别: 参与者可在超时后独立决策
- 适用场景: 对可用性要求高的场景

**Paxos Commit**:
- 定义: 使用Paxos协调提交决策
- 与传统2PC的区别: 协调者无单点故障
- 适用场景: 高可靠需求

---

## 二、关系网络

### 2.1 前置知识

| 前置知识 | 重要性 | 掌握程度检验 |
|----------|--------|--------------|
| ACID事务模型 | ⭐⭐⭐⭐⭐ | 理解事务的四个特性 |
| 两阶段锁（2PL） | ⭐⭐⭐⭐⭐ | 理解锁的获取和释放 |
| 预写日志（WAL） | ⭐⭐⭐⭐⭐ | 理解日志恢复机制 |
| 分布式共识 | ⭐⭐⭐⭐☆ | 理解Paxos/Raft |

### 2.2 相关概念

**紧密相关**:
- 分布式共识 - 解决协调者单点问题
- SAGA模式 - 长事务补偿方案
- 最终一致性 - BASE理论

**一般相关**:
- 死锁检测 - 分布式死锁
- 乐观并发控制 - 减少锁开销

### 2.3 后续扩展

学习本主题后，可继续深入：

1. 新型事务协议 → Spanner TrueTime、Percolator
2. 事务优化 → 确定性数据库
3. 区块链事务 → 跨链原子交换

### 2.4 思维导图

```
分布式事务与2PC-3PC
├── 基础概念
│   ├── ACID特性
│   ├── 分布式事务挑战
│   ├── 故障模型
│   └── 日志恢复
├── 两阶段提交 (2PC)
│   ├── 投票阶段
│   ├── 提交/中止阶段
│   ├── 协调者故障处理
│   ├── 参与者故障处理
│   └── 阻塞问题分析
├── 三阶段提交 (3PC)
│   ├── CanCommit阶段
│   ├── PreCommit阶段
│   ├── DoCommit阶段
│   ├── 超时机制
│   └── 非阻塞特性
├── 实现技术
│   ├── 预写日志 (WAL)
│   ├── 持久化状态
│   ├── 超时与重传
│   └── 恢复协议
└── 替代方案
    ├── Paxos Commit
    ├── SAGA模式
    └── TCC (Try-Confirm-Cancel)
```

---

## 三、形式化证明

### 3.1 核心定理

**定理 1 (2PC的原子性)**: 若2PC协议的某参与者提交（中止）事务，则所有正确参与者最终都会提交（中止）。

**证明**:

**情况分析**:

1. **所有参与者投赞成票**:
   - 协调者发送Commit消息
   - 所有收到Commit的参与者提交
   - 未收到的参与者通过协调者恢复或阻塞

2. **某参与者投反对票**:
   - 协调者发送Abort消息
   - 所有参与者中止

**故障恢复**:
- 参与者崩溃后重启，从日志恢复状态
- 若日志有"已投赞成票"记录，等待协调者决定
- 若日志有"已提交/中止"记录，完成操作

**关键不变式**:
协调者在收到所有投票前不会发送决定，因此决定后所有参与者会收到相同决定。

∎

**证明要点分析**:
1. 协调者的"原子广播"保证所有正确节点收到相同消息
2. 日志保证崩溃恢复后状态一致
3. 阻塞是安全性的代价

**定理 2 (3PC的非阻塞性)**: 在无网络分区的情况下，3PC的任何正确参与者最终都能做出决定，不会无限期阻塞。

*证明*: 预提交阶段确保所有参与者状态一致，超时后可通过多数派协商决策。∎

### 3.2 辅助引理

**引理 1 (协调者日志完备性)**: 协调者在发送Commit/Abort前已持久化决定。

*证明*: 写日志先于发送消息。∎

**引理 2 (参与者状态一致性)**: 在3PC的PreCommit阶段后，所有参与者状态一致（准备提交）。

*证明*: PreCommit消息确保参与者已锁定资源并准备提交。∎

---

## 四、算法/方法详解

### 4.1 算法描述

**两阶段提交（2PC）**:
```
角色: 协调者 C, 参与者集合 P = {P1, ..., Pn}

Phase 1: 投票阶段
    C → all Pi: VOTE_REQUEST
    
    each Pi:
        执行本地事务（不提交）
        写日志: VOTE_YES 或 VOTE_NO
        if 可以提交 then
            Pi → C: VOTE_YES
        else
            Pi → C: VOTE_NO
            中止本地事务

Phase 2: 提交阶段
    C收集所有投票:
        if 所有 Pi 投 VOTE_YES then
            写日志: COMMIT
            C → all Pi: GLOBAL_COMMIT
            each Pi:
                写日志: COMMIT
                提交本地事务
                释放锁
        else
            写日志: ABORT
            C → all Pi: GLOBAL_ABORT
            each Pi:
                写日志: ABORT
                中止本地事务
                释放锁

故障恢复:
    协调者崩溃:
        新协调者查询参与者状态
        若某参与者已提交/中止，所有参与者同步
        若所有参与者投赞成票，决定提交
    
    参与者崩溃:
        重启后从日志恢复
        若状态不确定，联系协调者
```

**三阶段提交（3PC）**:
```
Phase 1: CanCommit阶段
    C → all Pi: CAN_COMMIT?
    each Pi:
        检查本地资源
        if 资源可用 then
            Pi → C: YES
        else
            Pi → C: NO
            中止

Phase 2: PreCommit阶段
    if 所有 Pi 回应 YES then
        写日志: PREPARED
        C → all Pi: PREPARE
        each Pi:
            写日志: PREPARED
            预执行（获取锁，不提交）
            Pi → C: ACK
    else
        C → all Pi: ABORT
        each Pi 中止

Phase 3: DoCommit阶段
    C收到所有ACK:
        写日志: COMMIT
        C → all Pi: COMMIT
        each Pi:
            提交事务
            释放锁

超时处理:
    参与者等待CAN_COMMIT超时:
        单方面中止
    
    参与者等待PREPARE超时:
        单方面中止
    
    参与者等待COMMIT超时（已PREPARED）:
        联系其他参与者
        若某参与者已提交，则提交
        若多数未PREPARED，则中止
        否则阻塞（阻塞窗口更小）
```

**流程图**:
```
2PC:                     3PC:
C → P: Vote Request      C → P: Can Commit?
P → C: Vote Yes/No       P → C: Yes/No
   ↓                          ↓
C → P: Commit/Abort      C → P: Prepare
   ↓                     P → C: Ack
完成                        ↓
                        C → P: Commit
                           ↓
                        完成
```

### 4.2 正确性分析

**2PC正确性**:
- **原子性**: 协调者的统一决策保证
- **一致性**: 参与者本地事务保证
- **阻塞问题**: 协调者故障+网络分区导致阻塞

**3PC正确性**:
- **非阻塞**: 超时机制允许独立决策
- **风险**: 网络分区时可能出现不一致
- **折中**: 可用性优先于严格一致性

### 4.3 复杂度分析

**2PC**:
- 消息复杂度: $O(n)$ 每阶段，总计 $O(n)$ 消息
- 延迟: 2轮网络往返
- 协调者状态: $O(n)$

**3PC**:
- 消息复杂度: $O(n)$ 每阶段，总计 $O(n)$ 消息
- 延迟: 3轮网络往返
- 容错: 更好但有不一致风险

---

## 五、示例与实例

### 5.1 标准示例

**示例 1: 银行转账（2PC）**

**场景**: 从账户A（银行1）转账$100到账户B（银行2）

**执行过程**:
1. **投票阶段**:
   - 协调者向银行1、银行2发送VOTE_REQUEST
   - 银行1检查A余额，锁定$100，写日志VOTE_YES，回复协调者
   - 银行2检查B账户存在，写日志VOTE_YES，回复协调者

2. **提交阶段**:
   - 协调者收到两个YES，写日志COMMIT
   - 协调者向两家银行发送GLOBAL_COMMIT
   - 银行1提交（扣款A），释放锁，写日志COMMIT
   - 银行2提交（增加B），释放锁，写日志COMMIT

**故障场景**: 若银行1在投票后崩溃
- 银行1重启后从日志恢复
- 发现VOTE_YES记录，联系协调者
- 协调者告知决定（COMMIT或ABORT）

**示例 2: 3PC超时决策**

**场景**: 5个参与者，协调者在PreCommit后崩溃

**处理**:
1. 参与者P1等待COMMIT超时（已PREPARED）
2. P1联系其他参与者P2-P5
3. 若发现P3已收到COMMIT并提交：
   - P1也提交
4. 若所有参与者都处于PREPARED：
   - 等待新协调者或超时后协商
5. 若发现某参与者未PREPARED：
   - 中止（协调者未发送PREPARE）

### 5.2 代码实现

**Python实现 (简化2PC)**:

```python
from enum import Enum, auto
from typing import List, Dict, Optional
from dataclasses import dataclass
import json
import os

class TransactionState(Enum):
    ACTIVE = auto()
    PREPARED = auto()
    COMMITTED = auto()
    ABORTED = auto()

@dataclass
class LogEntry:
    tx_id: str
    state: TransactionState
    data: Dict

class Participant:
    """2PC参与者"""
    
    def __init__(self, participant_id: str, log_file: str):
        self.id = participant_id
        self.log_file = log_file
        self.transactions: Dict[str, TransactionState] = {}
        self.data_store: Dict[str, any] = {}
        self.load_log()
    
    def load_log(self):
        """从日志恢复状态"""
        if os.path.exists(self.log_file):
            with open(self.log_file, 'r') as f:
                for line in f:
                    entry = json.loads(line)
                    self.transactions[entry['tx_id']] = TransactionState[entry['state']]
    
    def write_log(self, tx_id: str, state: TransactionState, data: Dict = None):
        """写日志"""
        entry = {
            'tx_id': tx_id,
            'state': state.name,
            'data': data or {}
        }
        with open(self.log_file, 'a') as f:
            f.write(json.dumps(entry) + '\n')
        self.transactions[tx_id] = state
    
    def vote_request(self, tx_id: str, operation: Dict) -> bool:
        """
        处理投票请求
        返回: 是否可以提交
        """
        # 检查是否可以执行操作
        try:
            # 模拟本地执行（不提交）
            if operation['type'] == 'debit':
                account = operation['account']
                amount = operation['amount']
                current = self.data_store.get(account, 1000)  # 默认余额
                if current < amount:
                    print(f"[{self.id}] 余额不足，投反对票")
                    return False
            
            # 写日志: 准备提交
            self.write_log(tx_id, TransactionState.PREPARED, operation)
            print(f"[{self.id}] 投票赞成事务 {tx_id}")
            return True
            
        except Exception as e:
            print(f"[{self.id}] 执行失败: {e}")
            return False
    
    def commit(self, tx_id: str):
        """提交事务"""
        if tx_id not in self.transactions:
            raise ValueError(f"未知事务: {tx_id}")
        
        if self.transactions[tx_id] == TransactionState.COMMITTED:
            print(f"[{self.id}] 事务 {tx_id} 已提交")
            return
        
        # 实际提交操作
        self.write_log(tx_id, TransactionState.COMMITTED)
        print(f"[{self.id}] 提交事务 {tx_id}")
    
    def abort(self, tx_id: str):
        """中止事务"""
        self.write_log(tx_id, TransactionState.ABORTED)
        print(f"[{self.id}] 中止事务 {tx_id}")
    
    def get_status(self, tx_id: str) -> Optional[TransactionState]:
        """获取事务状态"""
        return self.transactions.get(tx_id)

class Coordinator:
    """2PC协调者"""
    
    def __init__(self, coordinator_id: str, log_file: str):
        self.id = coordinator_id
        self.log_file = log_file
        self.participants: List[Participant] = []
    
    def add_participant(self, participant: Participant):
        self.participants.append(participant)
    
    def execute_transaction(self, tx_id: str, operations: List[Dict]) -> bool:
        """
        执行2PC事务
        
        operations: [{'participant': 'P1', 'type': 'debit', ...}, ...]
        """
        print(f"\n=== 开始事务 {tx_id} ===")
        
        # Phase 1: 投票阶段
        print("Phase 1: 投票阶段")
        votes = {}
        
        for op in operations:
            participant_id = op['participant']
            participant = next(p for p in self.participants if p.id == participant_id)
            
            vote = participant.vote_request(tx_id, op)
            votes[participant_id] = vote
            
            if not vote:
                print(f"参与者 {participant_id} 投反对票")
        
        # 检查投票结果
        all_yes = all(votes.values())
        
        # Phase 2: 提交/中止阶段
        if all_yes:
            print("Phase 2: 提交")
            for participant in self.participants:
                participant.commit(tx_id)
            print(f"事务 {tx_id} 提交成功")
            return True
        else:
            print("Phase 2: 中止")
            for participant in self.participants:
                participant.abort(tx_id)
            print(f"事务 {tx_id} 中止")
            return False

# 使用示例
if __name__ == "__main__":
    # 创建参与者
    p1 = Participant("Bank_A", "bank_a.log")
    p1.data_store["account_A"] = 1000
    
    p2 = Participant("Bank_B", "bank_b.log")
    p2.data_store["account_B"] = 500
    
    # 创建协调者
    coord = Coordinator("Central", "coord.log")
    coord.add_participant(p1)
    coord.add_participant(p2)
    
    # 执行转账事务
    operations = [
        {'participant': 'Bank_A', 'type': 'debit', 'account': 'account_A', 'amount': 100},
        {'participant': 'Bank_B', 'type': 'credit', 'account': 'account_B', 'amount': 100}
    ]
    
    success = coord.execute_transaction("TX001", operations)
    print(f"\n事务结果: {'成功' if success else '失败'}")
    
    # 查看参与者状态
    print(f"\nBank_A事务状态: {p1.get_status('TX001')}")
    print(f"Bank_B事务状态: {p2.get_status('TX001')}")
```

## 5.3 反例
### 5.3 反例

**常见错误**:

**错误1: 先提交后写日志**
```python
# 错误：先提交后写日志
def commit(tx):
    apply_changes(tx)  # 先应用
    write_log("COMMIT", tx)  # 后写日志
    # 崩溃后无法恢复状态！
```
**错误原因**: 崩溃后无法知道事务状态
**正确做法**: 先写日志，再应用变更

**错误2: 2PC中忽视阻塞处理**
```python
# 错误：协调者故障后无处理
def participant_vote(tx):
    write_log("PREPARED", tx)
    vote = wait_for_coordinator()  # 永久等待！
```
**错误原因**: 协调者故障导致永久阻塞
**正确做法**: 实现超时和恢复协议

---

## 六、习题

### 6.1 理解题

1. **解释**: 为什么3PC可以解决2PC的阻塞问题，但引入了新的不一致风险？

   <details>
   <summary>解答</summary>
   
   **3PC解决阻塞问题**:
   - 引入PreCommit阶段，所有参与者在收到DoCommit前已准备就绪
   - 超时机制允许参与者在等待期间独立决策
   - 参与者可以联系其他参与者协商决策
   
   **引入不一致风险**:
   - 网络分区时，一部分参与者可能提交，另一部分中止
   - 例如：分区1的参与者收到COMMIT并提交
   - 分区2的参与者超时后决定中止
   - 结果：部分提交，违反原子性
   
   **权衡**: 3PC在非分区情况下提供更好的可用性，但牺牲了分区容忍下的严格一致性。
   </details>

### 6.2 应用题

1. **设计**: 设计一个支持故障恢复的2PC协调者选举协议。

   <details>
   <summary>解答</summary>
   
   故障恢复协议设计：
   
   1. **检测协调者故障**:
      - 参与者通过心跳超时检测协调者故障
      - 超时后启动协调者选举
   
   2. **选举新协调者**:
      - 使用Raft/Paxos选举新协调者
      - 或按预设优先级选择（如ID最小的参与者）
   
   3. **状态查询**:
      - 新协调者向所有参与者查询事务状态
      - 收集参与者的本地决定
   
   4. **决策恢复**:
      - 若某参与者已提交/中止，所有参与者同步
      - 若所有参与者准备就绪，决定提交
      - 否则决定中止
   
   ```python
   def recover_transaction(tx_id, participants):
       # 查询所有参与者状态
       states = {p.id: p.get_status(tx_id) for p in participants}
       
       # 决策逻辑
       if any(s == TransactionState.COMMITTED for s in states.values()):
           decision = "COMMIT"
       elif any(s == TransactionState.ABORTED for s in states.values()):
           decision = "ABORT"
       elif all(s == TransactionState.PREPARED for s in states.values()):
           decision = "COMMIT"  # 或根据策略
       else:
           decision = "ABORT"
       
       # 广播决策
       for p in participants:
           if decision == "COMMIT":
               p.commit(tx_id)
           else:
               p.abort(tx_id)
   ```
   </details>

### 6.3 证明题

1. **证明**: 若2PC协调者在写COMMIT日志后、发送GLOBAL_COMMIT前崩溃，事务仍然是原子的。

   <details>
   <summary>解答</summary>
   
   **证明**:
   
   场景分析：
   - 协调者已写COMMIT日志，证明所有参与者已投赞成票
   - 部分参与者可能已收到GLOBAL_COMMIT并提交
   - 其他参与者未收到决定，处于PREPARED状态
   
   **恢复过程**：
   1. 协调者重启后从日志恢复
   2. 发现COMMIT记录但部分参与者状态未知
   3. 协调者重新发送GLOBAL_COMMIT给所有参与者
   
   **参与者处理**：
   - 已提交的参与者忽略重复消息
   - PREPARED的参与者收到后提交
   
   **结果**：
   - 所有参与者最终都提交
   - 事务保持原子性
   
   **关键**：日志的持久性保证了决定的不可撤销性。
   ∎
   </details>

---

## 七、应用场景

### 7.1 经典应用

| 应用场景 | 具体问题 | 使用本主题的原因 |
|----------|----------|------------------|
| 分布式数据库 | 跨分片事务 | XA协议实现2PC |
| 消息队列 | 事务消息 | 确保消息与业务原子性 |
| 微服务 | 分布式事务 | TCC模式变体 |
| 金融系统 | 跨行转账 | 强一致性要求 |

### 7.2 实际案例

**案例**: MySQL XA事务

**背景**: MySQL支持XA分布式事务

**应用方式**:
1. 应用程序作为协调者
2. 多个MySQL实例作为参与者
3. 使用XA START/XA END/XA PREPARE/XA COMMIT

**效果**: 实现跨MySQL实例的原子操作

### 7.3 跨领域联系

**与分布式共识的联系**:
Paxos Commit用共识算法替代协调者，解决单点故障。

**与SAGA模式的联系**:
SAGA是长事务的补偿方案，牺牲ACID换取可用性。

---

## 八、多维对比

### 8.1 方法对比

| 维度 | 2PC | 3PC | Paxos Commit | SAGA |
|------|-----|-----|-------------|------|
| 阻塞性 | 可能阻塞 | 非阻塞 | 非阻塞 | 非阻塞 |
| 一致性 | 强 | 可能弱 | 强 | 最终一致 |
| 延迟 | 2轮 | 3轮 | 多轮 | 1轮/补偿 |
| 复杂度 | 中 | 高 | 高 | 中 |
| 适用场景 | 短事务 | 高可用 | 高可靠 | 长事务 |

### 8.2 决策建议

**何时选择2PC**:
- 短事务
- 强一致性要求
- 协调者高可用（如主备）

**何时选择SAGA**:
- 长事务
- 最终一致性可接受
- 需要高吞吐量

---

## 九、扩展阅读

### 9.1 教材章节

| 教材 | 章节 | 页码 | 推荐度 |
|------|------|------|--------|
| Bernstein & Newcomer | Chapter 7-9 | pp. 267-380 | ⭐⭐⭐⭐⭐ |
| Gray & Reuter | Chapter 3 | pp. 89-156 | ⭐⭐⭐⭐⭐ |
| Coulouris et al. | Chapter 16 | pp. 643-698 | ⭐⭐⭐⭐☆ |

### 9.2 论文

1. **"Notes on Data Base Operating Systems"** - Gray, 1978
   - **要点**: 2PC原始论文

2. **"Consensus on Transaction Commit"** - Lamport & Gray, 2003
   - **要点**: Paxos Commit

3. **"Life beyond Distributed Transactions"** - Helland, 2007
   - **要点**: SAGA模式的理论基础

### 9.3 在线资源

- **MySQL XA**: https://dev.mysql.com/doc/refman/8.0/en/xa.html
- **Seata**: https://seata.io/ - 开源分布式事务解决方案
- **CNCF Transaction SIG**: 分布式事务标准

---

## 十、专家批注

> **Jim Gray (2PC发明人)**:
> 分布式事务是两难的：我们需要原子性，但网络分区时必须在一致性和可用性之间选择。

> **Pat Helland (SAGA倡导者)**:
> 在大型系统中，放弃分布式事务，拥抱最终一致性，是工程务实的选择。

---

## 十一、修订历史

| 版本 | 日期 | 修订者 | 修订内容 |
|------|------|--------|----------|
| v1.0 | 2026-04-09 | 系统 | 初始版本 |

---

**标签**: #分布式系统 #分布式事务 #2PC #3PC #原子性

**相关笔记**: 
- [分布式共识算法深化](分布式共识算法深化.md)
- [CRDT与最终一致性](CRDT与最终一致性.md)
