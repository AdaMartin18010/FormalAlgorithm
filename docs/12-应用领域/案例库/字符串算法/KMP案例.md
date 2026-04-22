# 案例：KMP算法在文本编辑器搜索与DNA序列定位中的应用

## 背景

文本编辑器的"查找"功能、IDE 的全局搜索、以及生物信息学中的短序列定位，都需要在一个长文本中快速找到模式串的所有出现位置。KMP（Knuth-Morris-Pratt）算法以 $O(n + m)$ 的线性时间完成这一任务，是这类场景的经典解法。

## 问题定义

- **文本**：长字符串 $T$（如源代码文件、基因组序列）
- **模式**：短字符串 $P$（如搜索关键词、引物序列）
- **目标**：找到 $P$ 在 $T$ 中的所有出现位置

## KMP 的核心优势

| 算法 | 预处理 | 查询 | 特点 |
|------|--------|------|------|
| 暴力匹配 | 无 | $O(nm)$ | 回溯多 |
| **KMP** | **$O(m)$** | **$O(n)$** | **无回溯** |
| BM（Boyer-Moore）| $O(m + |\Sigma|)$ | $O(n)$ 平均 | 跳过字符，通常更快 |
| Rabin-Karp | $O(m)$ | $O(n)$ 平均 | 哈希碰撞风险 |

KMP 的优势在于**最坏情况保证**和**流式处理**（无需回退文本指针）。

## 实际应用

### 文本编辑器

- Vim / Emacs / VS Code 的搜索功能
- 对大型日志文件（GB 级）的实时搜索
- `grep` 工具的实现基础（结合 BM 优化）

### DNA 序列定位

- **引物设计**：在基因组中定位 PCR 引物结合位点
- **限制性酶切位点**：查找特定酶切序列的出现位置
- **序列比对**：KMP 作为局部比对的预处理步骤

### 网络协议解析

- HTTP 报文中的边界定位（如 `\r\n\r\n`）
- 数据包 payload 中的模式匹配（IDS/IPS）

## 前缀函数的应用扩展

KMP 的预处理结果（前缀函数 $\pi$）本身有多种用途：

| 应用 | 方法 |
|------|------|
| 字符串周期检测 | $n - \pi[n-1]$ 为最小周期长度（若整除）|
|  border 枚举 | 递归访问 $\pi[n-1], \pi[\pi[n-1]-1], ...$ |
| 字符串压缩 | 利用周期性质进行 Run-Length 编码 |

## 代码参考

- TypeScript: `examples/algorithms-ts/src/string.ts` → `kmpSearch()`
- Java: `examples/algorithms-java/StringAlgorithms.java` → `kmpSearch()`
- Go: `examples/algorithms-go/string.go` → `KMPSearch()`
- C++: `examples/algorithms-cpp/string.cpp` → `kmpSearch()`
- Rust: `examples/algorithms/src/string_algorithms/kmp.rs`

## 效果评估

- 对 100MB 文本、100 字节模式，KMP 搜索 < 1 秒
- 暴力搜索在周期性文本上可能慢 1000 倍以上
- 在生物信息学中，KMP 是序列比对工具（如 BLAST）的组件之一
