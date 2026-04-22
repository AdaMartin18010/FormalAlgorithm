# 案例：AC自动机在入侵检测系统（IDS）中的应用

## 背景

网络入侵检测系统（如 Snort、Suricata）需要在海量网络流量中实时检测恶意特征：病毒签名、攻击模式、敏感关键词等。这些特征通常有数千至数十万条，AC自动机（Aho-Corasick）以其 $O(n + m + z)$ 的线性时间复杂度（$n$ 为文本长度，$m$ 为模式总长，$z$ 为匹配数），成为多模式匹配的行业标准。

## 问题定义

- **模式库**：恶意特征集合 $P = \{p_1, p_2, ..., p_k\}$（如 "eval(", "cmd.exe", "DROP TABLE"）
- **文本**：网络流量 payload（HTTP 请求、邮件内容、文件传输）
- **目标**：实时检测所有模式在文本中的出现位置

## AC自动机的优势

| 方法 | 预处理 | 查询 | 多模式支持 |
|------|--------|------|-----------|
| 单 KMP × k 次 | $O(km)$ | $O(kn)$ | 低效 |
| 正则表达式引擎 | $O(m)$ | $O(n \cdot state)$ | 回溯爆炸风险 |
| **AC自动机** | **$O(m)$** | **$O(n + z)$** | **天然支持** |

## 实际系统

### Snort / Suricata

- 规则集中包含数万条内容匹配规则
- 使用 AC 自动机的变种进行高速多模式匹配
- 支持大小写不敏感、十六进制内容、PCRE 混合

### 杀毒软件

- 病毒签名库包含数百万条特征
- 对文件进行扫描时，AC 自动机同时匹配所有签名
- 结合哈希过滤减少误报

### 内容安全审计

- 实时检测敏感信息泄露（身份证号、银行卡号、密钥）
- 多模式匹配同时覆盖多种格式变体

## 扩展：双数组 Trie + AC

为减少内存占用，工业实现常使用**双数组 Trie（Double-Array Trie）**：

- BASE / CHECK 数组压缩转移
- 内存占用降至传统指针实现的 1/5 - 1/10
- 扫描速度提升 2-3 倍

## 代码参考

- TypeScript: `examples/algorithms-ts/src/string.ts` → `AhoCorasick`
- Java: `examples/algorithms-java/ACAutomaton.java` ⭐ 新增
- Go: `examples/algorithms-go/ac.go` ⭐ 新增
- C++: `examples/algorithms-cpp/ac_automaton.cpp` ⭐ 新增
- Rust: `examples/algorithms/src/ac_automaton.rs`

## 效果评估

- 对 10 万条模式、1MB 文本，AC 自动机扫描 < 10ms
- Snort 使用 AC 变种后，吞吐量可达 10Gbps 线速
