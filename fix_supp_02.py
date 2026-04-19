# 02-谓词逻辑-六维补充.md
with open("docs/06-逻辑系统/02-谓词逻辑-六维补充.md", "r", encoding="utf-8") as f:
    content = f.read()

content = content.replace(
    "## 思维导图：谓词逻辑概念结构",
    "一阶谓词逻辑是数理逻辑的核心系统，由 Frege 在 *Begriffsschrift* 中首次系统阐述 [1]，后经 Hilbert、Ackermann 等人的完善成为现代数学的基础语言 [2]。\n\n## 思维导图：谓词逻辑概念结构"
)

refs = """\n\n---\n\n## 参考文献 / References\n\n1. [1] Frege, G. (1879). *Begriffsschrift, eine der arithmetischen nachgebildete Formelsprache des reinen Denkens*. Louis Nebert.\n2. [2] Hilbert, D., & Ackermann, W. (1928). *Grundzüge der theoretischen Logik*. Springer.\n3. [3] Gödel, K. (1930). \"Die Vollständigkeit der Axiome des logischen Funktionenkalküls\". *Monatshefte für Mathematik und Physik*, 37(1): 349-360.\n4. [4] Tarski, A. (1936). \"Der Wahrheitsbegriff in den formalisierten Sprachen\". *Studia Philosophica*, 1: 261-405.\n5. [5] Church, A. (1936). \"A Note on the Entscheidungsproblem\". *The Journal of Symbolic Logic*, 1(1): 40-41.\n"""

content = content + refs

with open("docs/06-逻辑系统/02-谓词逻辑-六维补充.md", "w", encoding="utf-8") as f:
    f.write(content)

print("02-六维补充 done")
