---
title: README
version: 1.0
last_updated: 2026-04-19
---

# 算法规范与模型设计知识体系 - 知识图谱

## 概述

本知识图谱是"算法规范与模型设计知识体系"项目的核心组件，旨在：
- 建立概念之间的关联关系
- 明确知识依赖结构
- 优化学习路径
- 支持内容导航

## 知识图谱结构

### 1. 概念节点 (concept_nodes.yaml)

定义知识体系中所有核心概念：
- **总数**: 156个概念节点
- **分类**: 10大模块
  - 基础理论 (8个概念)
  - 递归理论 (5个概念)
  - 形式化证明 (4个概念)
  - 算法复杂度 (6个概念)
  - 类型理论 (8个概念)
  - 逻辑系统 (9个概念)
  - 计算模型 (10个概念)
  - 算法理论 (22个概念)
  - 高级主题 (12个概念)
  - 应用领域 (14个概念)

每个概念包含：
```yaml
- id: 唯一标识符
  name: 中文名称
  name_en: 英文名称
  category: 所属类别
  definition: 定义描述
  document: 对应文档路径
  complexity: 难度级别(基础/中级/高级/专家)
  prerequisites: 前置知识列表
```

### 2. 关系边 (concept_edges.yaml)

定义概念之间的关系：
- **总数**: 124条关系边
- **关系类型**:
  - `depends_on` - 依赖关系
  - `implements` - 实现关系
  - `extends` - 扩展关系
  - `equivalent_to` - 等价关系
  - `applies_to` - 应用关系
  - `generalizes` - 泛化关系
  - `specializes` - 特化关系
  - `uses` - 使用关系
  - `defines` - 定义关系
  - `proves` - 证明关系

### 3. 依赖关系 (concept_dependencies.yaml)

定义学习路径依赖：
- **总数**: 85个依赖关系
- **学习路径**:
  - 初学者路径 (150小时)
  - 进阶路径 (200小时)
  - 专业路径 (250小时)

每个依赖包含：
```yaml
- concept: 概念名称
  concept_id: 概念ID
  requires: 前置知识列表
  difficulty: 难度级别
  estimated_hours: 预计学习时间
```

## 核心概念关系

### 计算模型等价性 (丘奇-图灵论题)
```
图灵机 ↔ λ演算 ↔ 一般递归函数
```

### 柯里-霍华德同构
```
简单类型论 ↔ 命题逻辑
依赖类型论 ↔ 一阶逻辑
```

### 算法复杂度层次
```
P ⊆ BPP ⊆ BQP ⊆ QMA ⊆ PSPACE
```

### 类型理论层次
```
简单类型论 → 依赖类型论 → 同伦类型论
```

## 可视化图表

知识图谱可视化位于 `visualization/` 目录：
- `module_overview.md` - 模块总览图
- `core_concepts.md` - 核心概念图
- `learning_paths.md` - 学习路径图

## 使用指南

### 1. 查找概念定义
```yaml
# 在 concept_nodes.yaml 中搜索
concepts:
  - id: "turing_machine"
    name: "图灵机"
    ...
```

## 2. 查看概念关系
### 2. 查看概念关系
```yaml
# 在 concept_edges.yaml 中搜索
edges:
  - source: "lambda_calculus"
    target: "turing_machine"
    relation: "equivalent_to"
```

## 3. 规划学习路径
### 3. 规划学习路径
```yaml
# 在 concept_dependencies.yaml 中查看
learning_paths:
  beginner:
    stages:
      - stage: 1
        concepts: ["set_theory", "function_theory", ...]
```

## 维护与更新

### 添加新概念
1. 在 `concept_nodes.yaml` 中添加概念定义
2. 在 `concept_edges.yaml` 中添加相关关系
3. 在 `concept_dependencies.yaml` 中添加依赖关系

### 修改现有概念
1. 更新 `concept_nodes.yaml` 中的定义
2. 检查并更新相关的关系边
3. 确保依赖关系的一致性

### 版本控制
- 版本号: 1.0
- 最后更新: 2025-04-08
- 更新记录：
  - v1.0: 初始版本，包含156个概念节点，124条关系边

## 相关文档

- [术语与符号总表](../术语与符号总表.md)
- [项目全面梳理-2025.md](../项目全面梳理-2025.md)
- [学习路径设计](../学习路径设计.md)

## 统计信息

| 指标 | 数量 |
|------|------|
| 概念节点 | 156 |
| 关系边 | 124 |
| 依赖关系 | 85 |
| 学习路径 | 3条 |
| 覆盖模块 | 10个 |

---

*本知识图谱与项目其他文档保持同步更新*
