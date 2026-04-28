# 学术引用规范 - ACM对齐版

> **版本**: 1.0
> **对齐标准**: ACM Reference Format (2023年7月更新)
> **创建日期**: 2025-01-25
> **状态**: ✅ 已完成

---

## 📋 规范说明

本文档基于**ACM Reference Format**（2023年7月更新），定义了项目中使用的学术引用标准，确保引用格式的统一性和规范性。

**This document is based on ACM Reference Format (updated July 2023), defining academic citation standards used in the project to ensure consistency and standardization of citation formats.**

---

## 1. ACM引用格式概述

### 1.1 格式特点

- **文内引用**: 使用方括号内的数字，如 [1] 或 [1, 2]
- **作者命名**: 优先使用全名而非缩写；4个或更多作者使用"et al."格式
- **页码范围**: 使用en-dash（不是连字符），如 "24–46"
- **DOI包含**: 参考文献包含DOI链接（如可用）

### 1.2 格式原则

1. **一致性**: 所有引用遵循相同格式
2. **完整性**: 包含所有必要信息（作者、标题、出版信息、年份、DOI）
3. **可访问性**: 优先包含DOI或URL
4. **准确性**: 所有信息准确无误

---

## 2. 文内引用格式

### 2.1 基本格式

**格式**: `[编号]` 或 `[编号1, 编号2]`

**示例**:

- 根据 [Cormen 2022]，归并排序的时间复杂度为 $O(n \log n)$。
- According to [Cormen 2022], the time complexity of merge sort is $O(n \log n)$.
- 多个引用：归并排序和快速排序都是分治算法 [Cormen 2022, Knuth 1998]。
- Multiple citations: Merge sort and quick sort are both divide-and-conquer algorithms [Cormen 2022, Knuth 1998].

### 2.2 作者-年份格式（备选）

**格式**: `[作者 年份]`

**示例**:

- 根据 [Cormen 2022]，...
- According to [Cormen 2022], ...

---

## 3. 参考文献列表格式

### 3.1 期刊论文 (Journal Articles)

**格式**:

```
[编号] Author(s). (Year). "Title". *Journal Name*, Volume(Issue), Page range. DOI
```

**示例**:

```
[1] Hoare, C. A. R. (1962). "Quicksort." *The Computer Journal*, 5(1), 10-16. DOI: 10.1093/comjnl/5.1.10
```

**字段说明**:

- **Author(s)**: 全名，多个作者用逗号分隔，最后用"and"连接
- **Year**: 出版年份
- **Title**: 文章标题，使用引号
- **Journal Name**: 期刊名称，使用斜体
- **Volume(Issue)**: 卷号(期号)
- **Page range**: 页码范围，使用en-dash (–)
- **DOI**: 数字对象标识符（如可用）

### 3.2 书籍 (Books)

**格式**:

```
[编号] Author(s). (Year). *Book Title* (Edition ed.). Publisher. ISBN: ISBN号
```

**示例**:

```
[2] Cormen, T. H., Leiserson, C. E., Rivest, R. L., & Stein, C. (2022). *Introduction to Algorithms* (4th ed.). MIT Press. ISBN: 978-0262046305
```

**字段说明**:

- **Author(s)**: 全名，多个作者用逗号分隔，最后用"&"连接
- **Year**: 出版年份
- **Book Title**: 书名，使用斜体
- **Edition**: 版本（如适用）
- **Publisher**: 出版社
- **ISBN**: 国际标准书号

### 3.3 会议论文 (Conference Papers)

**格式**:

```
[编号] Author(s). (Year). "Title". In *Conference Name* (pp. Page range). Publisher. DOI
```

**示例**:

```
[3] Dijkstra, E. W. (1959). "A note on two problems in connexion with graphs." In *Numerische Mathematik*, 1(1), 269-271. DOI: 10.1007/BF01386390
```

### 3.4 预印本 (Preprints)

**格式**:

```
[编号] Author(s). (Year). "Title". arXiv: arXiv编号
```

**示例**:

```
[4] Barbosa, M., et al. (2024). "A bargain for mergesorts -- How to prove your mergesort correct and stable, almost for free." arXiv:2403.08173
```

### 3.5 在线资源 (Online Resources)

**格式**:

```
[编号] Author/Organization. (Year). "Title". Retrieved from URL [Accessed: Date]
```

**示例**:

```
[5] Wikipedia contributors. (2024). "Merge sort." Wikipedia, The Free Encyclopedia. Retrieved from https://en.wikipedia.org/wiki/Merge_sort [Accessed: 2025-01-25]
```

---

## 4. 特殊格式规则

### 4.1 多个作者

- **1-3个作者**: 列出所有作者
- **4个或更多作者**: 列出前3个作者，然后使用"et al."

**示例**:

```
[6] Author1, A., Author2, B., Author3, C., et al. (Year). "Title". ...
```

### 4.2 页码范围

- 使用en-dash (–)，不是连字符 (-)
- 示例: "24–46"（正确），"24-46"（错误）

### 4.3 DOI格式

- 格式: `DOI: 10.xxxx/xxxxx` 或 `https://doi.org/10.xxxx/xxxxx`
- 优先使用完整URL格式

---

## 5. 项目引用标准

### 5.1 核心算法引用

每个核心算法应引用：

1. **原始论文**: 算法的首次提出论文
2. **经典教材**: 算法导论、TAOCP等
3. **最新研究**: 2020年后的重要进展（如适用）

### 5.2 引用位置

1. **算法描述后**: 在算法描述后立即引用
2. **定理后**: 在定理陈述后引用
3. **证明后**: 在证明方法后引用
4. **文档末尾**: 在"参考文献"章节列出完整引用

### 5.3 引用检查清单

- [ ] 每个算法都有原始论文引用
- [ ] 每个定理都有证明来源引用
- [ ] 每个定义都有来源引用（如适用）
- [ ] 所有引用格式统一
- [ ] 所有引用信息完整（作者、年份、标题、出版信息、DOI）

---

## 6. 常用引用模板

### 6.1 算法原始论文

```markdown
[Author Year]: Author, A. (Year). "Algorithm Name." *Journal/Conference*, Volume(Issue), Pages. DOI
```

### 6.2 经典教材

```markdown
[Author Year]: Author, A. (Year). *Book Title* (Edition ed.). Publisher. ISBN: ISBN号
```

### 6.3 最新研究

```markdown
[Author Year]: Author, A., et al. (Year). "Title." arXiv: arXiv编号 或 *Journal*, Volume(Issue), Pages. DOI
```

---

## 7. 引用数据库结构

### 7.1 数据库字段

```yaml
reference_id: 唯一标识符（如 "Cormen2022"）
type: 类型（paper/book/conference/online/preprint）
authors: 作者列表
title: 标题（中英文）
venue: 出版物/会议/期刊
year: 年份
volume: 卷号（如适用）
issue: 期号（如适用）
pages: 页码范围
doi: DOI号
isbn: ISBN号（如适用）
url: URL（如适用）
accessed_date: 访问日期（如适用）
tags: 标签列表
relevance: 相关文档路径列表
quality: 质量评级（classic/standard/recent）
notes: 备注
```

### 7.2 示例条目

```yaml
- reference_id: "Cormen2022"
  type: "book"
  authors: ["Thomas H. Cormen", "Charles E. Leiserson", "Ronald L. Rivest", "Clifford Stein"]
  title:
    en: "Introduction to Algorithms"
    zh: "算法导论"
  venue: "MIT Press"
  year: 2022
  edition: "4th"
  isbn: "978-0262046305"
  tags: ["algorithms", "data-structures", "complexity"]
  relevance: ["09-算法理论/01-算法基础/"]
  quality: "standard"
  notes: "算法领域的标准教材，简称CLRS"
```

---

## 8. 引用格式检查工具

### 8.1 检查清单

- [ ] 作者名称完整（全名而非缩写）
- [ ] 年份正确
- [ ] 标题格式正确（引号或斜体）
- [ ] 页码范围使用en-dash
- [ ] DOI格式正确
- [ ] ISBN格式正确（如适用）
- [ ] URL可访问（如适用）

### 8.2 常见错误

1. **错误**: `[Cormen et al. 2022]`（应使用编号格式）
   **正确**: `[Cormen 2022]` 或 `[1]`

2. **错误**: `24-46`（应使用en-dash）
   **正确**: `24–46`

3. **错误**: `DOI:10.xxxx/xxxxx`（缺少空格）
   **正确**: `DOI: 10.xxxx/xxxxx`

---

## 9. 参考标准

### 9.1 ACM标准

- **ACM Reference Format**: Last updated July 11, 2023
- **ACM Digital Library**: <https://dl.acm.org/>

### 9.2 其他标准

- **IEEE Citation Reference**: IEEE标准
- **APA Style**: 美国心理学会格式
- **Chicago Style**: 芝加哥格式

---

## 10. 项目特定规则

### 10.1 引用优先级

1. **原始论文**: 算法的首次提出论文（最高优先级）
2. **经典教材**: CLRS、TAOCP等标准教材
3. **最新研究**: 2020年后的重要进展
4. **Wiki条目**: 作为补充参考

### 10.2 引用频率

- **每个算法**: 至少3个引用（原始论文、经典教材、最新研究）
- **每个定理**: 至少1个引用（证明来源）
- **每个定义**: 如非原创，至少1个引用

---

**文档维护**: 项目改进工作组
**最后更新**: 2025-01-25
**下次审查**: 2025-04-25
