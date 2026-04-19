import re

configs = {
    "docs/07-计算模型/01-图灵机.md": {
        "insert_after": "### 摘要 / Executive Summary\n",
        "insert_text": "\n本文档的核心理论基于图灵机的经典定义与 Church-Turing 论题，主要参考了现代计算理论教材与原始文献 [1][2][3][4][5]。\n",
        "ref_start": "## 7. 参考文献 / References",
        "ref_end": "## 与项目结构主题的对齐 / Alignment with Project Structure",
        "new_refs": "## 7. 参考文献 / References\n\n1. Turing, A. M. (1936). \"On Computable Numbers, with an Application to the Entscheidungsproblem\". *Proceedings of the London Mathematical Society*, 2(42), 230-265.\n2. Gödel, K. (1931). \"Über formal unentscheidbare Sätze der Principia Mathematica und verwandter Systeme I\". *Monatshefte für Mathematik und Physik*, 38(1), 173-198.\n3. Sipser, M. (2013). *Introduction to the Theory of Computation* (3rd ed.). Cengage Learning.\n4. Hopcroft, J. E., Motwani, R., & Ullman, J. D. (2006). *Introduction to Automata Theory, Languages, and Computation*. Pearson.\n5. Soare, R. I. (2016). *Turing Computability: Theory and Applications*. Springer.\n"
    },
    "docs/07-计算模型/01-图灵机-六维补充.md": {
        "insert_after": "> **深度**: 研究生级\n",
        "insert_text": "\n\n> 本文补充内容参考了 Sipser、Hopcroft-Ullman 等经典教材以及 Turing 原始论文 [1][2][3][4][5]。\n",
        "ref_start": None,
        "new_refs": "\n---\n\n## 参考文献 / References\n\n1. Sipser, M. (2013). *Introduction to the Theory of Computation* (3rd ed.). Cengage Learning.\n2. Hopcroft, J. E., Motwani, R., & Ullman, J. D. (2006). *Introduction to Automata Theory, Languages, and Computation*. Pearson.\n3. Turing, A. M. (1936). \"On Computable Numbers, with an Application to the Entscheidungsproblem\". *Proceedings of the London Mathematical Society*, 2(42), 230-265.\n4. Soare, R. I. (2016). *Turing Computability: Theory and Applications*. Springer.\n5. Cooper, S. B. (2004). *Computability Theory*. Chapman & Hall/CRC.\n"
    },
    "docs/07-计算模型/02-λ演算.md": {
        "insert_after": "### 摘要 / Executive Summary\n",
        "insert_text": "\n本文档的 λ 演算理论框架参考了 Church、Turing、Barendregt 等经典文献 [1][2][3][4][5]。\n",
        "ref_start": "## 7. 参考文献 / References",
        "ref_end": "## 与项目结构主题的对齐 / Alignment with Project Structure",
        "new_refs": "## 7. 参考文献 / References\n\n1. Church, A. (1936). \"An Unsolvable Problem of Elementary Number Theory\". *American Journal of Mathematics*, 58(2), 345-363.\n2. Turing, A. M. (1936). \"On Computable Numbers, with an Application to the Entscheidungsproblem\". *Proceedings of the London Mathematical Society*, 2(42), 230-265.\n3. Barendregt, H. P. (1984). *The Lambda Calculus: Its Syntax and Semantics* (Revised ed.). North-Holland.\n4. Sipser, M. (2013). *Introduction to the Theory of Computation* (3rd ed.). Cengage Learning.\n5. Hindley, J. R., & Seldin, J. P. (2008). *Lambda-Calculus and Combinators: An Introduction*. Cambridge University Press.\n"
    }
}
configs.update({
    "docs/07-计算模型/02-λ演算-六维补充.md": {
        "insert_after": "> **深度**: 研究生级\n",
        "insert_text": "\n\n> 本文补充内容参考了 Church 的原始论文、Barendregt 的专著以及现代类型论文献 [1][2][3][4][5]。\n",
        "ref_start": None,
        "new_refs": "\n---\n\n## 参考文献 / References\n\n1. Church, A. (1936). \"An Unsolvable Problem of Elementary Number Theory\". *American Journal of Mathematics*, 58(2), 345-363.\n2. Barendregt, H. P. (1984). *The Lambda Calculus: Its Syntax and Semantics*. North-Holland.\n3. Hindley, J. R., & Seldin, J. P. (2008). *Lambda-Calculus and Combinators: An Introduction*. Cambridge University Press.\n4. Cardelli, L. (1997). \"Type Systems\". *ACM Computing Surveys*, 28(1), 263-264.\n5. Pierce, B. C. (2002). *Types and Programming Languages*. MIT Press.\n"
    },
    "docs/07-计算模型/03-μ递归函数.md": {
        "insert_after": "### 摘要 / Executive Summary\n",
        "insert_text": "\n本文档关于递归函数的形式化定义参考了 Kleene、Gödel、Turing 与 Sipser 的经典著作 [1][2][3][4][5]。\n",
        "ref_start": "## 7. 参考文献 / References",
        "ref_end": "## 与项目结构主题的对齐 / Alignment with Project Structure",
        "new_refs": "## 7. 参考文献 / References\n\n1. Kleene, S. C. (1936). \"General Recursive Functions of Natural Numbers\". *Mathematische Annalen*, 112(1), 727-742.\n2. Gödel, K. (1931). \"Über formal unentscheidbare Sätze der Principia Mathematica und verwandter Systeme I\". *Monatshefte für Mathematik und Physik*, 38(1), 173-198.\n3. Turing, A. M. (1936). \"On Computable Numbers, with an Application to the Entscheidungsproblem\". *Proceedings of the London Mathematical Society*, 2(42), 230-265.\n4. Sipser, M. (2013). *Introduction to the Theory of Computation* (3rd ed.). Cengage Learning.\n5. Odifreddi, P. (1989). *Classical Recursion Theory*. North-Holland.\n"
    },
    "docs/07-计算模型/03-μ递归函数-六维补充.md": {
        "insert_after": "> **深度**: 研究生级\n",
        "insert_text": "\n\n> 本文补充内容参考了 Kleene 的原始论文以及现代递归论专著 [1][2][3][4][5]。\n",
        "ref_start": None,
        "new_refs": "\n---\n\n## 参考文献 / References\n\n1. Kleene, S. C. (1936). \"General Recursive Functions of Natural Numbers\". *Mathematische Annalen*, 112(1), 727-742.\n2. Odifreddi, P. (1989). *Classical Recursion Theory*. North-Holland.\n3. Soare, R. I. (2016). *Turing Computability: Theory and Applications*. Springer.\n4. Cooper, S. B. (2004). *Computability Theory*. Chapman & Hall/CRC.\n5. Nies, A. (2009). *Computability and Randomness*. Oxford University Press.\n"
    }
})
configs.update({
    "docs/07-计算模型/04-寄存器机与RAM模型.md": {
        "insert_after": "### 摘要 / Executive Summary\n",
        "insert_text": "\n本文档关于 RAM 与 RASP 的形式化描述参考了标准计算理论教材与原始论文 [1][2][3][4][5]。\n",
        "ref_start": "## 7. 参考文献 / References",
        "ref_end": "## 与项目结构主题的对齐 / Alignment with Project Structure",
        "new_refs": "## 7. 参考文献 / References\n\n1. Shepherdson, J. C., & Sturgis, H. E. (1963). \"Computability of Recursive Functions\". *Journal of the ACM*, 10(2), 217-255.\n2. Sipser, M. (2013). *Introduction to the Theory of Computation* (3rd ed.). Cengage Learning.\n3. Cook, S. A., & Reckhow, R. A. (1973). \"Time Bounded Random Access Machines\". *Journal of Computer and System Sciences*, 7(4), 354-375.\n4. Hopcroft, J. E., Motwani, R., & Ullman, J. D. (2006). *Introduction to Automata Theory, Languages, and Computation*. Pearson.\n5. Papadimitriou, C. H. (1994). *Computational Complexity*. Addison-Wesley.\n"
    },
    "docs/07-计算模型/04-寄存器机与RAM模型-六维补充.md": {
        "insert_after": "> **深度**: 研究生级\n",
        "insert_text": "\n\n> 本文补充内容参考了计算复杂性专著与随机存取机原始论文 [1][2][3][4][5]。\n",
        "ref_start": None,
        "new_refs": "\n---\n\n## 参考文献 / References\n\n1. Cook, S. A., & Reckhow, R. A. (1973). \"Time Bounded Random Access Machines\". *Journal of Computer and System Sciences*, 7(4), 354-375.\n2. Papadimitriou, C. H. (1994). *Computational Complexity*. Addison-Wesley.\n3. Sipser, M. (2013). *Introduction to the Theory of Computation* (3rd ed.). Cengage Learning.\n4. Arora, S., & Barak, B. (2009). *Computational Complexity: A Modern Approach*. Cambridge University Press.\n5. van Emde Boas, P. (1990). \"Machine Models and Simulations\". *Handbook of Theoretical Computer Science*, vol. A, Elsevier.\n"
    },
    "docs/07-计算模型/05-量子计算模型.md": {
        "insert_after": "### 摘要 / Executive Summary\n",
        "insert_text": "\n本文档关于量子计算模型、BQP 与量子算法的论述参考了 Deutsch、Bernstein-Vazirani、Nielsen-Chuang 与 Shor 等经典文献 [1][2][3][4][5]。\n",
        "ref_start": "## 9. 参考文献 / References",
        "ref_end": "## 与项目结构主题的对齐 / Alignment with Project Structure",
        "new_refs": "## 9. 参考文献 / References\n\n1. Deutsch, D. (1985). \"Quantum Theory, the Church-Turing Principle and the Universal Quantum Computer\". *Proceedings of the Royal Society A*, 400(1818), 97-117.\n2. Bernstein, E., & Vazirani, U. (1997). \"Quantum Complexity Theory\". *SIAM Journal on Computing*, 26(5), 1411-1473.\n3. Nielsen, M. A., & Chuang, I. L. (2010). *Quantum Computation and Quantum Information* (10th Anniversary ed.). Cambridge University Press.\n4. Shor, P. W. (1994). \"Algorithms for Quantum Computation: Discrete Logarithms and Factoring\". *Proceedings 35th Annual Symposium on Foundations of Computer Science*, 124-134.\n5. Grover, L. K. (1996). \"A Fast Quantum Mechanical Algorithm for Database Search\". *Proceedings 28th Annual ACM Symposium on Theory of Computing*, 212-219.\n"
    }
})
configs.update({
    "docs/07-计算模型/06-细胞自动机.md": {
        "insert_after": "### 摘要 / Executive Summary\n",
        "insert_text": "\n本文档关于细胞自动机的形式化定义与图灵完备性分析参考了 von Neumann、Cook、Wolfram 等经典文献 [1][2][3][4][5]。\n",
        "ref_start": "## 6. 参考文献 / References",
        "ref_end": "## 与项目结构主题的对齐 / Alignment with Project Structure",
        "new_refs": "## 6. 参考文献 / References\n\n1. von Neumann, J. (1966). *Theory of Self-Reproducing Automata*. University of Illinois Press.\n2. Wolfram, S. (2002). *A New Kind of Science*. Wolfram Media.\n3. Cook, M. (2004). \"Universality in Elementary Cellular Automata\". *Complex Systems*, 15(1), 1-40.\n4. Berlekamp, E. R., Conway, J. H., & Guy, R. K. (1982). *Winning Ways for Your Mathematical Plays, Vol. 2*. Academic Press.\n5. Sipser, M. (2013). *Introduction to the Theory of Computation* (3rd ed.). Cengage Learning.\n"
    },
    "docs/07-计算模型/07-计算复杂性类.md": {
        "insert_after": "### 摘要 / Executive Summary\n",
        "insert_text": "\n本文档关于计算复杂性类的体系构建参考了 Sipser、Papadimitriou、Arora-Barak 与 Cook 等经典教材与论文 [1][2][3][4][5]。\n",
        "ref_start": "## 6. 参考文献 / References",
        "ref_end": "## 与项目结构主题的对齐 / Alignment with Project Structure",
        "new_refs": "## 6. 参考文献 / References\n\n1. Sipser, M. (2013). *Introduction to the Theory of Computation* (3rd ed.). Cengage Learning.\n2. Papadimitriou, C. H. (1994). *Computational Complexity*. Addison-Wesley.\n3. Arora, S., & Barak, B. (2009). *Computational Complexity: A Modern Approach*. Cambridge University Press.\n4. Cook, S. A. (1971). \"The Complexity of Theorem-Proving Procedures\". *Proceedings 3rd Annual ACM Symposium on Theory of Computing*, 151-158.\n5. Karp, R. M. (1972). \"Reducibility among Combinatorial Problems\". *Complexity of Computer Computations*, Plenum Press, 85-103.\n"
    },
    "docs/07-计算模型/08-计算模型等价性理论.md": {
        "insert_after": "### 摘要 / Executive Summary\n",
        "insert_text": "\n本文档关于计算模型等价性的系统论述参考了 Church、Turing、Cook、Barendregt、Sipser 与 Hamkins 等经典文献 [1][2][3][4][5]。\n",
        "ref_start": "## 7. 参考文献 / References",
        "ref_end": None,
        "new_refs": "## 7. 参考文献 / References\n\n1. Church, A. (1936). \"An Unsolvable Problem of Elementary Number Theory\". *American Journal of Mathematics*, 58(2), 345-363.\n2. Turing, A. M. (1936). \"On Computable Numbers, with an Application to the Entscheidungsproblem\". *Proceedings of the London Mathematical Society*, 2(42), 230-265.\n3. Sipser, M. (2013). *Introduction to the Theory of Computation* (3rd ed.). Cengage Learning.\n4. Barendregt, H. P. (1984). *The Lambda Calculus: Its Syntax and Semantics*. North-Holland.\n5. Hamkins, J. D., & Lewis, A. (2000). \"Infinite Time Turing Machines\". *Journal of Symbolic Logic*, 65(2), 567-604.\n6. Cook, M. (2004). \"Universality in Elementary Cellular Automata\". *Complex Systems*, 15(1), 1-40.\n7. Blum, L., Shub, M., & Smale, S. (1989). \"On a Theory of Computation and Complexity over the Real Numbers\". *Bulletin of the American Mathematical Society*, 21(1), 1-46.\n8. Nielsen, M. A., & Chuang, I. L. (2010). *Quantum Computation and Quantum Information*. Cambridge University Press.\n"
    }
})

def process_file(path, cfg):
    with open(path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # Insert citation notice after specified anchor
    if cfg.get("insert_after") and cfg.get("insert_text"):
        anchor = cfg["insert_after"]
        if anchor in content:
            content = content.replace(anchor, anchor + cfg["insert_text"], 1)
        else:
            print(f"  Warning: insert_after anchor not found in {path}")
    
    # Replace references section
    ref_start = cfg.get("ref_start")
    if ref_start:
        ref_end = cfg.get("ref_end")
        if ref_start in content:
            start_idx = content.index(ref_start)
            if ref_end and ref_end in content:
                end_idx = content.index(ref_end)
            else:
                end_idx = len(content)
            content = content[:start_idx] + cfg["new_refs"] + content[end_idx:]
        else:
            print(f"  Warning: ref_start not found in {path}")
    else:
        # Append references at end
        if cfg.get("new_refs"):
            content = content.rstrip() + cfg["new_refs"]
    
    with open(path, 'w', encoding='utf-8') as f:
        f.write(content)
    print(f"Processed {path}")

import sys
for p, c in configs.items():
    process_file(p, c)
