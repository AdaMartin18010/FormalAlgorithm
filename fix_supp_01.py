import os

# For 01-命题逻辑-六维补充.md: add references and a few citations
with open("docs/06-逻辑系统/01-命题逻辑-六维补充.md", "r", encoding="utf-8") as f:
    content = f.read()

# Add citations in the first section
content = content.replace(
    "模态逻辑是对经典命题/谓词逻辑的扩展",
    "模态逻辑是对经典命题/谓词逻辑的扩展 [1]"
)
# Actually this is the wrong file... 01 is propositional logic
content = content.replace(
    "## 思维导图：命题逻辑概念结构",
    "命题逻辑作为现代逻辑学的基础，其形式化研究可追溯至 Aristotle 的古典逻辑，并在 19 世纪末由 Frege 和 Peirce 发展为现代符号逻辑 [1][2]。\n\n## 思维导图：命题逻辑概念结构"
)

refs = """\n\n---\n\n## 参考文献 / References\n\n1. [1] Frege, G. (1879). *Begriffsschrift, eine der arithmetischen nachgebildete Formelsprache des reinen Denkens*. Louis Nebert.\n2. [2] Russell, B., & Whitehead, A. N. (1910-1913). *Principia Mathematica*. Cambridge University Press.\n3. [3] Gödel, K. (1930). \"Die Vollständigkeit der Axiome des logischen Funktionenkalküls\". *Monatshefte für Mathematik und Physik*, 37(1): 349-360.\n4. [4] Gentzen, G. (1935). \"Untersuchungen über das logische Schließen\". *Mathematische Zeitschrift*, 39(1): 176-210.\n5. [5] Boole, G. (1854). *An Investigation of the Laws of Thought*. Macmillan.\n"""

content = content + refs

with open("docs/06-逻辑系统/01-命题逻辑-六维补充.md", "w", encoding="utf-8") as f:
    f.write(content)

print("01-六维补充 done")
