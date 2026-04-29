# 06-线性逻辑.md
with open("docs/06-逻辑系统/06-线性逻辑.md", "r", encoding="utf-8") as f:
    content = f.read()
content = content.replace(
    "## 基本概念 / Basic Concepts\n",
    "## 基本概念 / Basic Concepts\n\n线性逻辑由 Girard 于 1987 年创立 [1]，其核心思想是通过对结构规则的精细控制来追踪资源的消耗。Girard、Lafont 与 Taylor 的《Proofs and Types》[2] 以及 Troelstra 的讲义 [3] 是该领域的经典文献。Wadler 的综述 [4] 与 Abramsky 的游戏语义研究 [5] 进一步揭示了线性逻辑在计算机科学中的广泛应用。\n"
)
with open("docs/06-逻辑系统/06-线性逻辑.md", "w", encoding="utf-8") as f:
    f.write(content)

# 07-时序逻辑.md
with open("docs/06-逻辑系统/07-时序逻辑.md", "r", encoding="utf-8") as f:
    content = f.read()
content = content.replace(
    "## 1. 基本概念 / Basic Concepts\n",
    "## 1. 基本概念 / Basic Concepts\n\n时序逻辑由 Pnueli 引入程序验证领域 [1]，Emerson 的系统研究 [2] 奠定了分支时序逻辑的理论基础。Clarke、Grumberg 与 Peled 的专著 [3] 以及 Baier 与 Katoen 的教材 [4] 是模型检测领域的权威参考。Huth 与 Ryan 的教材 [5] 则广泛服务于计算机科学中的逻辑教学。\n"
)
with open("docs/06-逻辑系统/07-时序逻辑.md", "w", encoding="utf-8") as f:
    f.write(content)

# 01-命题逻辑-六维补充.md
with open("docs/06-逻辑系统/01-命题逻辑-六维补充.md", "r", encoding="utf-8") as f:
    content = f.read()
if "Boole 对思维规律的代数分析 [1]" not in content:
    content = content.replace(
        "# 命题逻辑 - 六维内容补充\n",
        "# 命题逻辑 - 六维内容补充\n\n命题逻辑作为现代逻辑学的基础，其形式化研究可追溯至 Aristotle 的古典逻辑，并在 19 世纪末由 Frege 和 Peirce 发展为现代符号逻辑 [1][2][3]。Gödel 的完备性定理 [4] 与 Gentzen 的证明论工作 [5] 奠定了其在数理逻辑中的核心地位。\n"
    )
with open("docs/06-逻辑系统/01-命题逻辑-六维补充.md", "w", encoding="utf-8") as f:
    f.write(content)

# 02-谓词逻辑-六维补充.md
with open("docs/06-逻辑系统/02-谓词逻辑-六维补充.md", "r", encoding="utf-8") as f:
    content = f.read()
if "Frege 在 *Begriffsschrift* 中首次系统阐述 [1]" not in content:
    content = content.replace(
        "# 谓词逻辑（一阶逻辑）- 六维内容补充\n",
        "# 谓词逻辑（一阶逻辑）- 六维内容补充\n\n一阶谓词逻辑是数理逻辑的核心系统，由 Frege 在 *Begriffsschrift* 中首次系统阐述 [1]，后经 Hilbert、Ackermann 等人的完善 [2] 成为现代数学的基础语言。Gödel 的完备性定理 [3]、Tarski 的语义学 [4] 与 Church 的不可判定性结果 [5] 共同塑造了其元理论框架。\n"
    )
with open("docs/06-逻辑系统/02-谓词逻辑-六维补充.md", "w", encoding="utf-8") as f:
    f.write(content)

# 03-模态逻辑-六维补充.md
with open("docs/06-逻辑系统/03-模态逻辑-六维补充.md", "r", encoding="utf-8") as f:
    content = f.read()
if "Kripke 的可能世界语义学 [3]" not in content:
    content = content.replace(
        "# 模态逻辑 - 六维补充\n",
        "# 模态逻辑 - 六维补充\n\n模态逻辑通过引入模态算子来表达必然性与可能性 [1][2]，Kripke 的可能世界语义学 [3] 为其提供了严格的数学基础。Blackburn 等人的专著 [4] 与 van Benthem 的教材 [5] 系统总结了该领域的核心理论与应用。\n"
    )
with open("docs/06-逻辑系统/03-模态逻辑-六维补充.md", "w", encoding="utf-8") as f:
    f.write(content)

# 04-高阶逻辑-六维补充.md
with open("docs/06-逻辑系统/04-高阶逻辑-六维补充.md", "r", encoding="utf-8") as f:
    content = f.read()
if "Isabelle/HOL 的实践 [5]" not in content:
    content = content.replace(
        "## 一、高阶逻辑核心概念",
        "高阶逻辑（Higher-Order Logic, HOL）[1] 是允许量词作用于函数和谓词的逻辑系统。Andrews 的教材 [2] 与 Lambek、Scott 的范畴论语义研究 [3] 构成了该领域的理论基础，而 Girard 的《Proofs and Types》[4] 与 Isabelle/HOL 的实践 [5] 则展示了其在证明论和形式化中的核心作用。\n\n## 一、高阶逻辑核心概念"
    )
with open("docs/06-逻辑系统/04-高阶逻辑-六维补充.md", "w", encoding="utf-8") as f:
    f.write(content)

print("All remaining files fixed")
