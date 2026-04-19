import re

# 01-命题逻辑.md
with open("docs/06-逻辑系统/01-命题逻辑.md", "r", encoding="utf-8") as f:
    content = f.read()

# Add citations near the beginning of main content
content = content.replace(
    "## 1. 基本概念 (Basic Concepts)",
    "## 1. 基本概念 (Basic Concepts)\n\n命题逻辑的形式化研究可追溯至 Boole 对思维规律的代数分析 [1]，后经 Frege 的概念文字 [2] 和 Russell、Whitehead 的《数学原理》[3] 发展为现代符号逻辑。Hilbert 与 Ackermann 的系统阐述 [4] 以及 Gödel 的完备性定理 [5] 奠定了命题逻辑作为数理逻辑基础系统的地位。"
)

with open("docs/06-逻辑系统/01-命题逻辑.md", "w", encoding="utf-8") as f:
    f.write(content)

# 02-一阶逻辑.md
with open("docs/06-逻辑系统/02-一阶逻辑.md", "r", encoding="utf-8") as f:
    content = f.read()

content = content.replace(
    "## 1. 基本概念 (Basic Concepts)",
    "## 1. 基本概念 (Basic Concepts)\n\n一阶逻辑是数理逻辑的核心分支，其完备性由 Gödel 于 1930 年首次证明 [1]。Church 关于判定问题的奠基工作 [2] 与 Tarski 的形式化真值概念 [3] 共同塑造了一阶逻辑的元理论。Enderton [4] 与 Mendelson [5] 的教材至今仍是该领域的标准参考。"
)

with open("docs/06-逻辑系统/02-一阶逻辑.md", "w", encoding="utf-8") as f:
    f.write(content)

# 03-直觉逻辑.md
with open("docs/06-逻辑系统/03-直觉逻辑.md", "r", encoding="utf-8") as f:
    content = f.read()

content = content.replace(
    "## 1. 基本概念 (Basic Concepts)",
    "## 1. 基本概念 (Basic Concepts)\n\n直觉逻辑源于 Brouwer 对排中律的哲学批判 [1]，Heyting 于 1930 年给出了其形式系统 [2]。Kripke 的语义分析 [3] 与 Kolmogorov 的解释 [4] 为直觉逻辑提供了严格的数学基础，而 Gödel 对其算术性质的研究 [5] 揭示了直觉主义与经典数学之间的深刻联系。"
)

with open("docs/06-逻辑系统/03-直觉逻辑.md", "w", encoding="utf-8") as f:
    f.write(content)

# 04-模态逻辑.md
with open("docs/06-逻辑系统/04-模态逻辑.md", "r", encoding="utf-8") as f:
    content = f.read()

content = content.replace(
    "## 1. 基本概念 (Basic Concepts)",
    "## 1. 基本概念 (Basic Concepts)\n\n模态逻辑的发展始于 Lewis 对严格蕴涵的分析 [1]，而 Kripke 可能世界语义学的引入 [2] 使其成为现代逻辑的重要分支。Gödel 对直觉主义命题演算的解释 [3] 与 McKinsey、Tarski 的代数研究 [4] 奠定了模态逻辑的数学基础。Blackburn 等人的专著 [5] 系统总结了该领域的理论与应用。"
)

with open("docs/06-逻辑系统/04-模态逻辑.md", "w", encoding="utf-8") as f:
    f.write(content)

# 06-线性逻辑.md
with open("docs/06-逻辑系统/06-线性逻辑.md", "r", encoding="utf-8") as f:
    content = f.read()

content = content.replace(
    "## 1. 基本概念 (Basic Concepts)",
    "## 1. 基本概念 (Basic Concepts)\n\n线性逻辑由 Girard 于 1987 年创立 [1]，其核心思想是通过对结构规则的精细控制来追踪资源的消耗。Girard、Lafont 与 Taylor 的《Proofs and Types》[2] 以及 Troelstra 的讲义 [3] 是该领域的经典文献。Wadler 的综述 [4] 与 Abramsky 的游戏语义研究 [5] 进一步揭示了线性逻辑在计算机科学中的广泛应用。"
)

with open("docs/06-逻辑系统/06-线性逻辑.md", "w", encoding="utf-8") as f:
    f.write(content)

# 07-时序逻辑.md
with open("docs/06-逻辑系统/07-时序逻辑.md", "r", encoding="utf-8") as f:
    content = f.read()

content = content.replace(
    "## 1. 基本概念 (Basic Concepts)",
    "## 1. 基本概念 (Basic Concepts)\n\n时序逻辑由 Pnueli 引入程序验证领域 [1]，Emerson 的系统研究 [2] 奠定了分支时序逻辑的理论基础。Clarke、Grumberg 与 Peled 的专著 [3] 以及 Baier 与 Katoen 的教材 [4] 是模型检测领域的权威参考。Huth 与 Ryan 的教材 [5] 则广泛服务于计算机科学中的逻辑教学。"
)

with open("docs/06-逻辑系统/07-时序逻辑.md", "w", encoding="utf-8") as f:
    f.write(content)

print("Main files citations added")
