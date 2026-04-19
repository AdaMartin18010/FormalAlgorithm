append_text = """

### A.24 通信复杂度学习路径

**入门阶段**：
1. 理解 Yao 的两方通信模型和基本定义。
2. 掌握确定性通信复杂度和协议树的概念。
3. 学习 fooling set 和矩形覆盖方法。
4. 分析 $EQ_n$、$DISJ_n$、$IP_n$ 的确定性下界。

**进阶阶段**：
5. 学习非确定性和随机化通信复杂度。
6. 掌握 discrepancy、information complexity 和 corruption bound。
7. 分析 $DISJ_n$ 和 $IP_n$ 的随机化下界。
8. 了解量子通信复杂度的基本概念。

**研究前沿阶段**：
9. 学习 Karchmer-Wigderson 框架与电路下界的联系。
10. 探索 Log-Rank 猜想和直接和问题的最新进展。
11. 研究通信复杂度在流算法、分布式学习和机器学习中的应用。
12. 阅读 Rao & Yehudayoff (2020) 的现代综合教材。

### A.25 文档更新日志

- **v2.0 (2026-04-16)**：全面重写和扩展。新增 Yao 两方模型的严格形式化定义、非确定性通信复杂度的深入分析、随机化通信复杂度（公共硬币/私有硬币模型、Yao's Minimax Principle）、量子通信复杂度、 fooling set / 矩形覆盖 / 秩方法 / discrepancy / corruption bound / 信息复杂度等下界技术的完整推导、经典问题（EQ、DISJ、IP、GT、Index、Gap-Hamming、k-Disjointness）的完整下界分析、多方通信复杂度、扩展实现示例、通信复杂度在流算法/分布式学习/联邦学习中的应用、统一引用格式 `[N] Author. Title. Venue/Publisher, Year.`。
- **v1.0 (2025-01-11)**：基础框架。
"""

with open('docs/04-算法复杂度/05-通信复杂度.md', 'a', encoding='utf-8') as f:
    f.write(append_text)
print("Appended to 05-通信复杂度.md")
