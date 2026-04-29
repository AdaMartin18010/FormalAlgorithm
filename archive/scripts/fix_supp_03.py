# 03-模态逻辑-六维补充.md
with open("docs/06-逻辑系统/03-模态逻辑-六维补充.md", "r", encoding="utf-8") as f:
    content = f.read()

content = content.replace(
    "模态逻辑是对经典命题/谓词逻辑的扩展，通过引入模态算子来表达**必然性**和**可能性**等概念。",
    "模态逻辑是对经典命题/谓词逻辑的扩展，通过引入模态算子来表达**必然性**和**可能性**等概念 [1][2]。"
)

refs = """\n\n---\n\n## 参考文献 / References\n\n1. [1] Kripke, S. A. (1963). \"Semantical Analysis of Modal Logic I\". *Zeitschrift für Mathematische Logik und Grundlagen der Mathematik*, 9: 67-96.\n2. [2] Lewis, C. I., & Langford, C. H. (1932). *Symbolic Logic*. Century Company.\n3. [3] Hintikka, J. (1962). *Knowledge and Belief: An Introduction to the Logic of the Two Notions*. Cornell University Press.\n4. [4] Blackburn, P., de Rijke, M., & Venema, Y. (2001). *Modal Logic*. Cambridge University Press.\n5. [5] van Benthem, J. (2010). *Modal Logic for Open Minds*. CSLI Publications.\n"""

content = content + refs

with open("docs/06-逻辑系统/03-模态逻辑-六维补充.md", "w", encoding="utf-8") as f:
    f.write(content)

print("03-六维补充 done")
