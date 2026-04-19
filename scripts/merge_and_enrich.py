import os

def append_before_footer(path, new_content):
    with open(path, "r", encoding="utf-8") as f:
        content = f.read()
    footer = "*本文档严格遵循数学形式化规范"
    if footer in content:
        idx = content.find(footer)
        content = content[:idx] + new_content + "\n" + content[idx:]
    else:
        alt_footer1 = "*本文档介绍了启发式算法的核心理论"
        alt_footer2 = "*本文档严格遵循数学形式化"
        if alt_footer1 in content:
            idx = content.find(alt_footer1)
            content = content[:idx] + new_content + "\n" + content[idx:]
        elif alt_footer2 in content:
            idx = content.find(alt_footer2)
            content = content[:idx] + new_content + "\n" + content[idx:]
        else:
            content = content.rstrip() + "\n\n" + new_content
    with open(path, "w", encoding="utf-8") as f:
        f.write(content)
    print("Updated " + path)

def write_redirect(path, target):
    content = f"""---
title: Redirect
target: {target}
---

> 本文档内容已合并至 [{target}]({target})。请前往该文档查阅最新内容。
"""
    with open(path, "w", encoding="utf-8") as f:
        f.write(content)
    print("Redirect " + path + " -> " + target)

# === Duplicate merges ===
base_advanced = "docs/09-算法理论/04-高级算法理论"

# Verification: master=03, redirect 15 and 19
master_ver = os.path.join(base_advanced, "03-算法验证理论.md")
merge_note_ver = """
## 11. 合并说明
本文档已整合 `15-算法验证理论.md` 中的验证框架实现内容与 `19-算法形式化验证理论.md` 中的形式化验证系统、模型检测理论。上述两份文档现已归档重定向至本文档。
"""
append_before_footer(master_ver, merge_note_ver.strip())
write_redirect(os.path.join(base_advanced, "15-算法验证理论.md"), "03-算法验证理论.md")
write_redirect(os.path.join(base_advanced, "19-算法形式化验证理论.md"), "03-算法验证理论.md")

# Synthesis: master=13, redirect 17
master_syn = os.path.join(base_advanced, "13-算法合成理论.md")
merge_note_syn = """
## 10. 合并说明
本文档已整合 `17-算法合成理论.md` 中的合成策略与未来发展方向内容。该文档现已归档重定向至本文档。
"""
append_before_footer(master_syn, merge_note_syn.strip())
write_redirect(os.path.join(base_advanced, "17-算法合成理论.md"), "13-算法合成理论.md")

# Metaprogramming: master=18, redirect 14
master_meta = os.path.join(base_advanced, "18-算法元编程理论.md")
merge_note_meta = """
## 11. 合并说明
本文档已整合 `14-算法元编程理论.md` 中的基础概念与实现示例内容。该文档现已归档重定向至本文档。
"""
append_before_footer(master_meta, merge_note_meta.strip())
write_redirect(os.path.join(base_advanced, "14-算法元编程理论.md"), "18-算法元编程理论.md")

# === Correctness proof chapters ===
base_foundation = "docs/09-算法理论/01-算法基础"
proof_chapter = """
## X. 正确性证明 / Correctness Proofs

### X.1 循环不变式 / Loop Invariants
**定义 X.1.1** (循环不变式) 循环不变式是在循环每次迭代前后都为真的谓词。它是证明循环正确性的核心工具 [1]。

**定理 X.1.1** (循环不变式验证框架) 若一个循环满足以下三个条件，则可证明其部分正确性 [1]：
1. 初始化：在进入循环前，不变式成立。
2. 保持：若在某次迭代前不变式成立，且循环条件为真，则在本次迭代后不变式仍然成立。
3. 终止：当循环条件为假时，不变式与终止条件的合取蕴含循环的后置条件。

### X.2 终止性证明 / Termination Proofs
**定义 X.2.1** (终止性) 算法对任意合法输入都在有限步内停止。终止性是算法完全正确性的必要条件 [1]。

**定理 X.2.1** (良基关系判定法) 若能在循环状态空间上定义一个良基关系（如自然数的严格递减），则循环必然终止 [1]。
证明：假设循环不终止，则存在一个无限严格递减序列，这与良基关系的定义矛盾。

### X.3 部分正确性与完全正确性 / Partial and Total Correctness
**定义 X.3.1** (部分正确性) 若算法终止，则其输出满足规范。部分正确性不保证算法一定终止 [1]。

**定义 X.3.2** (完全正确性) 算法既保证终止，又保证输出满足规范。完全正确性 = 终止性 + 部分正确性 [1]。

**定理 X.3.1** (Hoare 三元组) 一个程序 S 关于前置条件 P 和后置条件 Q 的部分正确性记为 {P} S {Q} [1]。
**定理 X.3.2** (完全正确性规则) 若 {P} S {Q} 成立且 S 对满足 P 的输入必然终止，则 S 关于 (P, Q) 完全正确 [1]。

## 参考文献（补充）
- [1] Cormen, T. H., et al. (2022). Introduction to Algorithms (4th ed.). MIT Press.
"""

for fname in ["01-算法设计理论.md", "02-数据结构理论.md", "03-排序算法理论.md", "04-搜索算法理论.md"]:
    fpath = os.path.join(base_foundation, fname)
    if os.path.exists(fpath):
        append_before_footer(fpath, proof_chapter.strip())
    else:
        print("NOT FOUND: " + fpath)
