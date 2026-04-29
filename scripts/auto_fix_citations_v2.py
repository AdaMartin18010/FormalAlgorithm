import re
from pathlib import Path

# 主题到引用的映射
topic_refs = {
    "02-递归理论": [
        "[Kleene1952] S. C. Kleene. Introduction to Metamathematics. North-Holland, 1952.",
        "[Rogers1987] H. Rogers. Theory of Recursive Functions and Effective Computability. MIT Press, 1987.",
        "[Soare2016] R. I. Soare. Turing Computability: Theory and Applications. Springer, 2016.",
        "[Gödel1931] K. Gödel. Über formal unentscheidbare Sätze der Principia Mathematica und verwandter Systeme I. Monatshefte für Mathematik und Physik, 38:173-198, 1931.",
    ],
    "03-形式化证明": [
        "[Gentzen1934] G. Gentzen. Untersuchungen über das logische Schließen. Mathematische Zeitschrift, 39:176-210, 1934.",
        "[Prawitz1965] D. Prawitz. Natural Deduction: A Proof-Theoretical Study. Almqvist & Wiksell, 1965.",
        "[SoftwareFoundations] B. Pierce et al. Software Foundations. https://softwarefoundations.cis.upenn.edu, 2024.",
        "[Coq] The Coq Development Team. The Coq Proof Assistant. https://coq.inria.fr.",
        "[Wiedijk2006] F. Wiedijk. The Seventeen Provers of the World. LNAI 3600, Springer, 2006.",
    ],
    "04-算法复杂度": [
        "[CLRS2009] T. H. Cormen et al. Introduction to Algorithms (3rd ed.). MIT Press, 2009.",
        "[Arora2009] S. Arora and B. Barak. Computational Complexity: A Modern Approach. Cambridge University Press, 2009.",
        "[Knuth1997] D. E. Knuth. The Art of Computer Programming, Vol. 1. Addison-Wesley, 1997.",
        "[Graham1994] R. L. Graham, D. E. Knuth, and O. Patashnik. Concrete Mathematics (2nd ed.). Addison-Wesley, 1994.",
    ],
    "05-类型理论": [
        "[Pierce2002] B. C. Pierce. Types and Programming Languages. MIT Press, 2002.",
        "[Barendregt1984] H. P. Barendregt. The Lambda Calculus: Its Syntax and Semantics. North-Holland, 1984.",
        "[MartinLöf1984] P. Martin-Löf. Intuitionistic Type Theory. Bibliopolis, 1984.",
        "[HoTTBook2013] The Univalent Foundations Program. Homotopy Type Theory. IAS, 2013.",
    ],
    "06-逻辑系统": [
        "[Mendelson2015] E. Mendelson. Introduction to Mathematical Logic (6th ed.). CRC Press, 2015.",
        "[Enderton2001] H. B. Enderton. A Mathematical Introduction to Logic (2nd ed.). Academic Press, 2001.",
        "[Kripke1963] S. Kripke. Semantical Analysis of Modal Logic I. Zeitschrift für Mathematische Logik, 8:67-96, 1963.",
        "[Pnueli1977] A. Pnueli. The Temporal Logic of Programs. FOCS, 46-57, 1977.",
    ],
    "07-计算模型": [
        "[Turing1936] A. M. Turing. On Computable Numbers. Proceedings of the LMS, 42:230-265, 1936.",
        "[Church1936] A. Church. An Unsolvable Problem of Elementary Number Theory. American Journal of Mathematics, 58(2):345-363, 1936.",
        "[HopcroftUllman1979] J. E. Hopcroft and J. D. Ullman. Introduction to Automata Theory. Addison-Wesley, 1979.",
        "[Sipser2012] M. Sipser. Introduction to the Theory of Computation (3rd ed.). Cengage Learning, 2012.",
    ],
}

def fix_bibliography(filepath, topic):
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()
    
    if "- 待补充" not in content and "待补充" not in content:
        return 0
    
    refs = topic_refs.get(topic, [])
    if not refs:
        return 0
    
    # 替换参考文献章节中的"- 待补充"
    old = "- 待补充"
    new = "\n".join("- " + r for r in refs)
    
    if old in content:
        content = content.replace(old, new, 1)
        with open(filepath, 'w', encoding='utf-8') as f:
            f.write(content)
        return 1
    
    # 处理"待补充"在其他位置的情况（如正文中的"（待补充）"已被脚本v1处理）
    return 0

total = 0
for topic in topic_refs.keys():
    p = Path("docs") / topic
    if not p.exists():
        continue
    for md in p.rglob("*.md"):
        n = fix_bibliography(md, topic)
        if n > 0:
            total += n
            print(f"Fixed: {md}")

print(f"\n总计修复: {total} 个文件")
