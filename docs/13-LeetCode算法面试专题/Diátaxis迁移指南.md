---
title: 13-Diátaxis 迁移指南 / Diátaxis Migration Guide for LeetCode Module
version: 1.0
status: draft
last_updated: 2026-04-29
owner: 面试专题工作组
concepts: ["Diátaxis", "文档架构", "迁移策略", "LeetCode", "渐进式改造"]
level: 全级别
diataxis: how-to
---

> 📊 **项目全面梳理**：详细的项目结构、模块详解和学习路径，请参阅 [`项目全面梳理-2025.md`](../../项目全面梳理-2025.md)

## 13-Diátaxis 迁移指南 / Diátaxis Migration Guide for LeetCode Module

### 摘要 / Executive Summary

- 本文档为 `13-LeetCode算法面试专题` 模块的 **Diátaxis 文档架构改造总纲**，定义了从现有"按算法类别组织"的单一维度结构，向 Diátaxis 四象限（Tutorials / How-To Guides / Reference / Explanation）渐进式演进的路线图。
- **核心原则**：不废弃现有编号模块体系（`00-06`、`99`），而是在模块内部新增 Diátaxis 分类层，实现"主题 × 需求类型"的双维导航。
- 所有**新增文档**必须按 Diátaxis 分类归入对应目录；所有**现有文档**通过本指南标注目标分类，后续逐步迁移或重写。

---

## 目录 / Table of Contents

- [1. 改造背景与设计原则](#1-改造背景与设计原则)
- [2. Diátaxis 目录结构](#2-diátaxis-目录结构)
- [3. 现有文档分类映射](#3-现有文档分类映射)
- [4. YAML Frontmatter 扩展规范](#4-yaml-frontmatter-扩展规范)
- [5. 四象限写作规范](#5-四象限写作规范)
- [6. 迁移路线图](#6-迁移路线图)
- [7. 新增文档决策树](#7-新增文档决策树)
- [参考文献](#参考文献)

---

## 1. 改造背景与设计原则

### 1.1 为什么引入 Diátaxis

现有 `13-LeetCode算法面试专题` 采用**单一主题维度**组织：

```
00-总览与方法论 → 01-数据结构专题 → 02-算法范式专题 → ... → 06-面试专题 → 99-附录
```

这种结构对**系统学习**友好，但对以下场景支持不足：

| 用户场景 | 现有结构的问题 | Diátaxis 解决方案 |
|---------|-------------|-----------------|
| "我想跟着一个完整训练计划刷题" | 需要跨多个目录自行组合 | **Tutorials**：提供端到端学习体验 |
| "面试前如何快速准备口头证明" | 散落在各专题的"沟通模板"段落 | **How-To Guides**：聚焦步骤与清单 |
| "查某道题的复杂度下界和证明" | 题解与理论文档分离 | **Reference**：集中技术事实 |
| "为什么双指针能用于这道题" | 缺乏背景讨论深度 | **Explanation**：概念与原理讨论 |

### 1.2 设计原则

**原则一：渐进式，非颠覆式**

- 现有编号目录（`00-06`、`99`）**全部保留**，作为"主题索引"继续维护。
- 新增四个 Diátaxis 目录（`00-Tutorials` ~ `03-Explanation`）作为"需求类型索引"。
- 文档迁移以**复制+重写**为主，不删除原文件，直到新目录内容成熟。

**原则二：双维导航**

读者可以通过两条独立路径找到目标内容：

```
路径 A（主题维度）：我想学数据结构 → 01-数据结构专题/02-链表.md
路径 B（需求维度）：我想查题解 → 02-Reference/数据结构/链表/lc0021-merge-two-sorted-lists.md
```

**原则三：Frontmatter 驱动**

所有文档（新旧）统一扩展 YAML frontmatter，增加 `diataxis` 字段。后续可通过脚本自动生成跨维度索引。

---

## 2. Diátaxis 目录结构

在 `docs/13-LeetCode算法面试专题/` 根目录下新建以下结构：

```
docs/13-LeetCode算法面试专题/
│
├── 00-总览与方法论/          ← 现有，保留（主题维度）
├── 01-数据结构专题/          ← 现有，保留（主题维度）
├── 02-算法范式专题/          ← 现有，保留（主题维度）
├── 03-数学专题/              ← 现有，保留（主题维度）
├── 04-字符串专题/            ← 现有，保留（主题维度）
├── 05-图论专题/              ← 现有，保留（主题维度）
├── 06-面试专题/              ← 现有，保留（主题维度）
├── 99-附录/                  ← 现有，保留（主题维度）
│
├── Diátaxis迁移指南.md       ← 本文档
│
├── 00-Tutorials/             ← 新建：教程（学习体验）
│   ├── README.md
│   ├── 00-从零开始刷LeetCode/
│   │   └── 14天形式化训练计划.md
│   ├── 01-数据结构/
│   ├── 02-算法范式/
│   ├── 03-数学/
│   ├── 04-字符串/
│   ├── 05-图论/
│   └── 06-面试冲刺/
│
├── 01-How-To-Guides/         ← 新建：操作指南（解决实际问题）
│   ├── README.md
│   ├── formal-proof/
│   │   └── 如何用Lean4形式化证明LeetCode题目.md
│   ├── interview/
│   │   ├── 如何在面试中推导循环不变式.md
│   │   ├── 如何在5分钟内完成复杂度现场分析.md
│   │   └── 如何用四步法拆解一道新题.md
│   ├── optimization/
│   │   └── 如何将朴素解法优化到最优复杂度.md
│   └── communication/
│       └── 如何向面试官口头证明算法正确性.md
│
├── 02-Reference/             ← 新建：参考（技术事实）
│   ├── README.md
│   ├── problem-solutions/    ← 题解文档（含形式化规约、复杂度、证明）
│   │   ├── 数据结构/
│   │   ├── 算法范式/
│   │   ├── 数学/
│   │   ├── 字符串/
│   │   ├── 图论/
│   │   └── 面试高频/
│   ├── complexity/
│   │   └── 复杂度速查表（Reference版）.md
│   ├── glossary/
│   │   └── LeetCode形式化术语表.md
│   └── templates/
│       ├── 五元组规约模板.md
│       ├── 循环不变式模板.md
│       └── 多语言代码模板速查.md
│
└── 03-Explanation/           ← 新建：解释（背景与概念）
    ├── README.md
    ├── formal-specification/
    │   └── LeetCode题解中的形式化规约方法论.md
    ├── correctness/
    │   ├── 为什么双指针算法是正确的.md
    │   ├── 贪心算法的形式化本质.md
    │   └── 动态规划最优子结构的通用证明框架.md
    ├── complexity/
    │   └── 比较模型下界与面试算法最优性.md
    └── paradigm/
        ├── 二分查找的三种区间范式对比.md
        ├── 滑动窗口不变式设计原理.md
        └── 回溯算法的剪枝与完备性.md
```

### 2.1 四象限目录说明

| 目录 | Diátaxis 类型 | 核心问题 | 读者状态 | 内容形态 |
|------|-------------|---------|---------|---------|
| `00-Tutorials/` | **Tutorials** | "如何学会…？" | 学习者 | 渐进式课程、训练计划、动手实验 |
| `01-How-To-Guides/` | **How-To Guides** | "如何做…？" | 执行者 | 步骤清单、操作手册、面试话术 |
| `02-Reference/` | **Reference** | "…的事实是什么？" | 查阅者 | 题解、速查表、规约模板、术语定义 |
| `03-Explanation/` | **Explanation** | "为什么…？" | 理解者 | 概念讨论、原理分析、方法论阐释 |

---

## 3. 现有文档分类映射

以下表格为 **2026-04-29 版本的现有文档**标注应迁移到的 Diátaxis 分类。标注依据见 §3.1 的判定标准。

### 3.1 判定标准

| 象限 | 判定问题 | 关键特征 |
|------|---------|---------|
| **Tutorial** | 读者是否在学习一项技能？ | 有明确起点/终点、包含练习、假设读者为初学者 |
| **How-To** | 读者是否在解决一个具体问题？ | 以目标为导向、步骤明确、可独立执行 |
| **Reference** | 读者是否在查找事实？ | 描述性、可快速检索、按主题/字母排序 |
| **Explanation** | 读者是否在寻求理解？ | 讨论性、允许背景铺垫、回答"为什么" |

### 3.2 现有文档分类表

| 现有路径 | 文档名称 | 建议分类 | 迁移策略 | 备注 |
|---------|---------|---------|---------|------|
| `00-总览与方法论/00-专题导论.md` | 专题导论 | **Explanation** | 重写为 Explanation 版本，保留原文件 | 属于概念阐释与模块定位 |
| `00-总览与方法论/01-解题方法论（四步法与形式化思维）.md` | 解题方法论 | **Tutorial** + **How-To** | 拆分：训练计划入 Tutorial，步骤清单入 How-To | 混合类型，需拆分 |
| `00-总览与方法论/02-复杂度速查与面试沟通模板.md` | 复杂度速查与沟通模板 | **Reference** + **How-To** | 速查表入 Reference，沟通模板入 How-To | 混合类型，需拆分 |
| `01-数据结构专题/00-数据结构专题导论.md` | 数据结构专题导论 | **Explanation** | 重写为 Explanation 版本 | 概念性导论 |
| `01-数据结构专题/01-数组与矩阵.md` | 数组与矩阵 | **Reference** + **Tutorial** | 题解入 Reference，练习路径入 Tutorial | 含多道题解 |
| `01-数据结构专题/02-链表.md` | 链表 | **Reference** + **Tutorial** | 同上 | 含多道题解 |
| `01-数据结构专题/03-栈与队列.md` | 栈与队列 | **Reference** + **Tutorial** | 同上 | 含多道题解 |
| `01-数据结构专题/04-哈希表.md` | 哈希表 | **Reference** + **Tutorial** | 同上 | 含多道题解 |
| `01-数据结构专题/05-二叉树与BST.md` | 二叉树与BST | **Reference** + **Tutorial** | 同上 | 含多道题解 |
| `01-数据结构专题/06-堆与优先队列.md` | 堆与优先队列 | **Reference** + **Tutorial** | 同上 | 含多道题解 |
| `01-数据结构专题/07-并查集.md` | 并查集 | **Reference** + **Tutorial** | 同上 | 含多道题解 |
| `01-数据结构专题/08-Trie树.md` | Trie树 | **Reference** + **Tutorial** | 同上 | 含多道题解 |
| `02-算法范式专题/00-算法范式导论.md` | 算法范式导论 | **Explanation** | 重写为 Explanation 版本 | 概念性导论 |
| `02-算法范式专题/01-枚举与模拟.md` ~ `11-位运算.md` | 各算法范式专题 | **Reference** + **Tutorial** | 题解入 Reference，练习路径入 Tutorial | 全部 11 个专题文件 |
| `03-数学专题/00-数学专题导论.md` | 数学专题导论 | **Explanation** | 重写为 Explanation 版本 | 概念性导论 |
| `03-数学专题/01-数论基础` ~ `04-概率与随机算法面试题.md` | 各数学专题 | **Reference** + **Tutorial** | 同上 | 全部 4 个专题文件 |
| `04-字符串专题/00-字符串专题导论.md` | 字符串专题导论 | **Explanation** | 重写为 Explanation 版本 | 概念性导论 |
| `04-字符串专题/01-字符串匹配与KMP应用.md` ~ `03-字符串动态规划.md` | 各字符串专题 | **Reference** + **Tutorial** | 同上 | 全部 3 个专题文件 |
| `05-图论专题/00-图论专题导论.md` | 图论专题导论 | **Explanation** | 重写为 Explanation 版本 | 概念性导论 |
| `05-图论专题/01-图的遍历` ~ `04-最小生成树.md` | 各图论专题 | **Reference** + **Tutorial** | 同上 | 全部 4 个专题文件 |
| `06-面试专题/00-面试专题导论.md` | 面试专题导论 | **Explanation** | 重写为 Explanation 版本 | 概念性导论 |
| `06-面试专题/01-高频Top100-数组与链表.md` ~ `03-高频Top100-DP与贪心.md` | 高频 Top 100 专题 | **Reference** | 整理为题解集入 Reference | 属于事实信息 |
| `06-面试专题/04-剑指Offer精选形式化证明.md` | 剑指 Offer 形式化证明 | **Reference** + **How-To** | 题解入 Reference，证明技巧入 How-To | 混合类型 |
| `06-面试专题/05-大厂真题分类.md` | 大厂真题分类 | **Reference** | 整理为题解集入 Reference | 属于事实信息 |
| `99-附录/01-LeetCode题号全局索引.md` | 题号全局索引 | **Reference** | 直接迁移 | 纯参考 |
| `99-附录/02-面试常见错误清单.md` | 常见错误清单 | **How-To** | 重写为"如何避免…"步骤 | 可转化为操作指南 |
| `99-附录/03-多语言代码模板速查.md` | 多语言代码模板速查 | **Reference** | 直接迁移 | 纯参考 |

### 3.3 混合类型文档的处理策略

部分现有文档**同时包含多种 Diátaxis 类型**的内容（如 `01-解题方法论` 既有教程性质的四步法训练，又有操作指南性质的模板）。对此采用以下策略：

1. **拆分法**（首选）：将文档拆分为多个独立文档，分别归入对应象限。
   - 例：`01-解题方法论` → `00-Tutorials/00-从零开始刷LeetCode/四步法训练计划.md` + `01-How-To-Guides/interview/如何用四步法拆解一道新题.md`

2. **标注法**（次选）：若文档不易拆分，保留在原位置，但在 frontmatter 中标注 `diataxis: mixed`，并在文档头部增加 Diátaxis 导航提示。

3. **重写法**（长期）：对于核心文档，逐步重写为单一类型的深度版本，替换原混合文档。

---

## 4. YAML Frontmatter 扩展规范

### 4.1 扩展字段

在所有 `13-LeetCode算法面试专题` 模块的 Markdown 文档中，YAML frontmatter **必须**增加 `diataxis` 字段。

```yaml
---
title: 文档标题 / Document Title
version: 1.0
status: maintained   # 或 draft / deprecated
last_updated: 2026-04-29
owner: 面试专题工作组
concepts: ["概念A", "概念B"]
level: 中级          # 全级别 / 初级 / 中级 / 高级
diataxis: how-to     # ← 新增必填字段
---
```

### 4.2 `diataxis` 字段取值规范

| 取值 | 含义 | 适用场景 |
|------|------|---------|
| `tutorial` | 教程 | 训练计划、渐进式课程、动手实验 |
| `how-to` | 操作指南 | 步骤清单、面试话术、问题解决方案 |
| `reference` | 参考 | 题解、速查表、模板、术语定义、索引 |
| `explanation` | 解释 | 概念讨论、原理分析、方法论阐释 |
| `mixed` | 混合（过渡态） | 尚未拆分的旧文档，需逐步清理 |

### 4.3 示例

**Tutorial 文档示例**：

```yaml
---
title: 14天形式化训练计划 / 14-Day Formalization Training Plan
version: 1.0
status: maintained
last_updated: 2026-04-29
owner: 面试专题工作组
concepts: ["训练计划", "形式化方法", "LeetCode"]
level: 初级
diataxis: tutorial
---
```

**How-To 文档示例**：

```yaml
---
title: 如何用Lean 4形式化证明LeetCode题目 / How to Formally Prove LeetCode Problems in Lean 4
version: 1.0
status: maintained
last_updated: 2026-04-29
owner: 面试专题工作组
concepts: ["Lean 4", "形式化证明", "LeetCode", "操作指南"]
level: 高级
diataxis: how-to
---
```

**Reference 文档示例**：

```yaml
---
title: lc0001-two-sum / Two Sum 题解
version: 1.0
status: maintained
last_updated: 2026-04-29
owner: 面试专题工作组
concepts: ["哈希表", "数组", "两数之和"]
level: 简单
diataxis: reference
leetcode_tags: ["array", "hash-table"]
---
```

**Explanation 文档示例**：

```yaml
---
title: LeetCode题解中的形式化规约方法论 / Formal Specification Methodology in LeetCode Solutions
version: 1.0
status: maintained
last_updated: 2026-04-29
owner: 面试专题工作组
concepts: ["形式化规约", "五元组", "方法论", "Diátaxis"]
level: 中级
diataxis: explanation
---
```

### 4.4 自动化检查

新增脚本 `scripts/check_diataxis_frontmatter.py`（计划中）用于：

1. 扫描 `docs/13-LeetCode算法面试专题/` 下所有 `.md` 文件；
2. 检查 frontmatter 中是否包含合法 `diataxis` 字段；
3. 生成四象限文档分布报表。

---

## 5. 四象限写作规范

### 5.1 Tutorial（教程）

**核心问题**："我如何学会 X？"

- **必须有明确的起点和终点**：读者从什么状态出发，到什么状态结束。
- **必须是渐进式的**：每一步建立在前一步基础上，不跳跃。
- **必须包含实践**：每节配有练习或代码任务。
- **假设读者为初学者**：不预设高级知识。

**禁止内容**：

- 纯理论讨论（应放入 Explanation）
- 零散的技巧列表（应放入 How-To）
- 纯题解（应放入 Reference）

**推荐结构**：

```
1. 学习目标
2. 前置知识清单
3. 第1课：…（含练习）
4. 第2课：…（含练习）
5. …
6. 综合项目
7. 自测标准
```

### 5.2 How-To Guide（操作指南）

**核心问题**："我如何做 X？"

- **以目标为导向**：标题必须是"如何做…""如何在…""怎样…"。
- **步骤必须可独立执行**：读者不需要读完 Tutorial 才能看懂。
- **允许假设前置知识**：可以链接到 Tutorial 或 Explanation。
- **必须包含验证步骤**：如何确认操作成功。

**禁止内容**：

- 长篇理论铺垫（应放入 Explanation）
- 从零开始的教学（应放入 Tutorial）
- 纯定义描述（应放入 Reference）

**推荐结构**：

```
1. 目标与预期结果
2. 前置条件（链接到 Reference/Tutorial）
3. Step 1: …
4. Step 2: …
5. …
6. 验证结果
7. 常见问题与排查
8. 相关 How-To 链接
```

### 5.3 Reference（参考）

**核心问题**："关于 X 的事实是什么？"

- **可快速检索**：使用表格、列表、代码块，减少叙述性文字。
- **准确、完整、简洁**：不解释"为什么"，只陈述"是什么"。
- **按主题或字母排序**：便于查找。
- **题解必须包含**：形式化规约、复杂度分析、正确性证明梗概、多语言代码链接。

**禁止内容**：

- 主观讨论（应放入 Explanation）
- 教学性叙述（应放入 Tutorial）
- 操作步骤（应放入 How-To）

**推荐结构（题解）**：

```
1. 题目描述（链接 LeetCode）
2. 形式化规约（五元组）
3. 算法思路
4. 正确性证明（循环不变式 / 归纳法）
5. 复杂度分析
6. 参考实现（链接多语言代码）
7. 相关题解链接
```

### 5.4 Explanation（解释）

**核心问题**："为什么 X 是这样？"

- **讨论性、背景性**：允许历史沿革、设计权衡、哲学思考。
- **回答"为什么"**：不只是陈述事实，而是解释原因。
- **允许多视角**：可以对比不同方法论的优劣。
- **不假设读者要立刻行动**：读者是在"理解"，不是在"执行"。

**禁止内容**：

- 操作步骤（应放入 How-To）
- 训练计划（应放入 Tutorial）
- 纯数据表格（应放入 Reference）

**推荐结构**：

```
1. 核心问题提出
2. 背景与上下文
3. 概念逐层展开
4. 形式化定义（如有）
5. 示例与类比
6. 与其他概念的关系
7. 总结与启发
```

---

## 6. 迁移路线图

### 第一阶段：基础设施（2026-04 ~ 2026-05）

- [x] 创建四象限目录结构
- [x] 编写 Diátaxis 迁移指南（本文档）
- [x] 设计 YAML frontmatter 扩展规范
- [x] 创建示例文档（How-To × 1，Explanation × 1）
- [ ] 为全部现有文档添加 `diataxis: mixed` 标注
- [ ] 更新 `README.md`，增加 Diátaxis 导航入口

### 第二阶段：核心填充（2026-05 ~ 2026-06）

- [ ] 将 `99-附录` 内容拆分到 `02-Reference/` 和 `01-How-To-Guides/`
- [ ] 重写 `00-总览与方法论` 为三份独立文档：
  - `03-Explanation/`：模块定位与形式化思维 Explanation
  - `00-Tutorials/`：14 天训练计划 Tutorial
  - `01-How-To-Guides/`：四步法操作手册 How-To
- [ ] 将高频题解从 `06-面试专题/` 整理到 `02-Reference/problem-solutions/`

### 第三阶段：全面迁移（2026-06 ~ 2026-07）

- [ ] 逐个专题完成拆分：
  - 导论 → `03-Explanation/`
  - 题解 → `02-Reference/problem-solutions/`
  - 训练路径 → `00-Tutorials/`
- [ ] 编写自动化脚本，检查 frontmatter 合规性
- [ ] 建立跨维度索引（主题 × 需求类型）

### 第四阶段：评估优化（2026-07 ~ ）

- [ ] 收集读者反馈，优化分类边界
- [ ] 清理 `diataxis: mixed` 过渡态文档
- [ ] 将成熟模式推广到其他模块（如 `09-算法理论/`）

---

## 7. 新增文档决策树

当贡献者想要新增一篇文档时，按以下决策树确定其归属：

```mermaid
flowchart TD
    Start([新增文档])
    Start --> Q1{读者在阅读时<br/>是否亲自动手？}
    Q1 -->|是，有练习/代码任务| Q2{是否有明确起点终点？}
    Q1 -->|否，纯阅读| Q3

    Q2 -->|是| Tutorial[00-Tutorials/]
    Q2 -->|否| HowTo1[01-How-To-Guides/]

    Q3 --> Q4{文档是否在回答<br/>"如何做某事"？}
    Q4 -->|是| HowTo2[01-How-To-Guides/]
    Q4 -->|否| Q5{文档是否在回答<br/>"为什么"？}

    Q5 -->|是| Explanation[03-Explanation/]
    Q5 -->|否| Reference[02-Reference/]
```

**快速判定口诀**：

> - 有练习、渐进学 → **Tutorial**
> - 步骤清、解决题 → **How-To**
> - 查事实、看规约 → **Reference**
> - 问原理、探背景 → **Explanation**

---

## 参考文献

1. [Procida 2017] Procida, D. (2017). "The Diátaxis Framework." <https://diataxis.fr/>
   - Diátaxis 四象限框架的原始定义与哲学基础。
2. [CLRS2022] Cormen, T. H., et al. (2022). *Introduction to Algorithms* (4th ed.). MIT Press.
   - 算法形式化规约与证明的权威参考。
3. [Hoare1969] Hoare, C. A. R. (1969). "An Axiomatic Basis for Computer Programming." *Communications of the ACM*, 12(10), 576-580.
   - 循环不变式与霍尔逻辑的理论基础。

---

**文档版本**: 1.0
**最后更新**: 2026-04-29
**状态**: 草案（Draft）
**下一步行动**: 为现有文档批量添加 `diataxis` 字段，启动第一阶段。
