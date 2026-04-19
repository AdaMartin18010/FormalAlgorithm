# 04-高阶逻辑-六维补充.md
with open("docs/06-逻辑系统/04-高阶逻辑-六维补充.md", "r", encoding="utf-8") as f:
    content = f.read()

# Add citations in text
content = content.replace(
    "高阶逻辑（Higher-Order Logic, HOL）",
    "高阶逻辑（Higher-Order Logic, HOL）[1]"
)
content = content.replace(
    "Church 的 λ-演算",
    "Church 的 λ-演算 [1]"
)
content = content.replace(
    "Curry-Howard 同构",
    "Curry-Howard 同构 [4]"
)
content = content.replace(
    "Isabelle/HOL",
    "Isabelle/HOL [5]"
)

# Update references section format
old_refs = """## 参考文献

1. Church, A. (1940). A Formulation of the Simple Theory of Types. *Journal of Symbolic Logic*, 5(2), 56-68.
2. Andrews, P. B. (2002). *An Introduction to Mathematical Logic and Type Theory: To Truth Through Proof* (2nd Edition). Springer.
3. Lambek, J. & Scott, P. J. (1986). *Introduction to Higher Order Categorical Logic*. Cambridge University Press.
4. Girard, J.-Y., Taylor, P., & Lafont, Y. (1989). *Proofs and Types*. Cambridge University Press.
5. Nipkow, T., Paulson, L. C., & Wenzel, M. (2002). *Isabelle/HOL: A Proof Assistant for Higher-Order Logic*. Springer."""

new_refs = """## 参考文献 / References

1. [1] Church, A. (1940). A Formulation of the Simple Theory of Types. *Journal of Symbolic Logic*, 5(2), 56-68.
2. [2] Andrews, P. B. (2002). *An Introduction to Mathematical Logic and Type Theory: To Truth Through Proof* (2nd Edition). Springer.
3. [3] Lambek, J. & Scott, P. J. (1986). *Introduction to Higher Order Categorical Logic*. Cambridge University Press.
4. [4] Girard, J.-Y., Taylor, P., & Lafont, Y. (1989). *Proofs and Types*. Cambridge University Press.
5. [5] Nipkow, T., Paulson, L. C., & Wenzel, M. (2002). *Isabelle/HOL: A Proof Assistant for Higher-Order Logic*. Springer."""

content = content.replace(old_refs, new_refs)

with open("docs/06-逻辑系统/04-高阶逻辑-六维补充.md", "w", encoding="utf-8") as f:
    f.write(content)

print("04-六维补充 done")
