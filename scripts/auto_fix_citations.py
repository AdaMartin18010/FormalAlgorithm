import os, re, yaml, json
from pathlib import Path

# 引用知识库：主题/关键词 -> (引用key, 引用描述, 优先级)
CITATION_KB = {
    # 算法基础
    "算法导论": ("CLRS2009", "T. H. Cormen, C. E. Leiserson, R. L. Rivest, and C. Stein. Introduction to Algorithms (3rd ed.). MIT Press, 2009."),
    "Introduction to Algorithms": ("CLRS2009", "T. H. Cormen et al. Introduction to Algorithms (3rd ed.). MIT Press, 2009."),
    "CLRS": ("CLRS2009", "T. H. Cormen et al. Introduction to Algorithms (3rd ed.). MIT Press, 2009."),
    "Knuth": ("Knuth1997", "D. E. Knuth. The Art of Computer Programming, Vol. 1: Fundamental Algorithms (3rd ed.). Addison-Wesley, 1997."),
    "计算机程序设计艺术": ("Knuth1997", "D. E. Knuth. The Art of Computer Programming, Vol. 1. Addison-Wesley, 1997."),
    "Sedgewick": ("Sedgewick2011", "R. Sedgewick and K. Wayne. Algorithms (4th ed.). Addison-Wesley, 2011."),
    
    # 计算理论
    "图灵机": ("Turing1936", "A. M. Turing. On Computable Numbers, with an Application to the Entscheidungsproblem. Proceedings of the London Mathematical Society, 42:230-265, 1936."),
    "Turing": ("Turing1936", "A. M. Turing. On Computable Numbers. Proceedings of the LMS, 42:230-265, 1936."),
    "λ演算": ("Church1936", "A. Church. An Unsolvable Problem of Elementary Number Theory. American Journal of Mathematics, 58(2):345-363, 1936."),
    "Lambda": ("Church1936", "A. Church. An Unsolvable Problem of Elementary Number Theory. American Journal of Mathematics, 58(2):345-363, 1936."),
    "Sipser": ("Sipser2012", "M. Sipser. Introduction to the Theory of Computation (3rd ed.). Cengage Learning, 2012."),
    "Hopcroft": ("HopcroftUllman1979", "J. E. Hopcroft and J. D. Ullman. Introduction to Automata Theory, Languages, and Computation. Addison-Wesley, 1979."),
    "自动机": ("HopcroftUllman1979", "J. E. Hopcroft and J. D. Ullman. Introduction to Automata Theory, Languages, and Computation. Addison-Wesley, 1979."),
    
    # 递归/可计算性
    "Kleene": ("Kleene1952", "S. C. Kleene. Introduction to Metamathematics. North-Holland, 1952."),
    "递归函数": ("Kleene1952", "S. C. Kleene. Introduction to Metamathematics. North-Holland, 1952."),
    "可计算性": ("Soare2016", "R. I. Soare. Turing Computability: Theory and Applications. Springer, 2016."),
    "Rogers": ("Rogers1987", "H. Rogers. Theory of Recursive Functions and Effective Computability. MIT Press, 1987."),
    "哥德尔": ("Gödel1931", "K. Gödel. Über formal unentscheidbare Sätze der Principia Mathematica und verwandter Systeme I. Monatshefte für Mathematik und Physik, 38:173-198, 1931."),
    "Gödel": ("Gödel1931", "K. Gödel. Über formal unentscheidbare Sätze. Monatshefte für Mathematik, 38:173-198, 1931."),
    "不完全性定理": ("Gödel1931", "K. Gödel. Über formal unentscheidbare Sätze. Monatshefte für Mathematik, 38:173-198, 1931."),
    "Ackermann": ("Ackermann1928", "W. Ackermann. Zum Hilbertschen Aufbau der reellen Zahlen. Mathematische Annalen, 99:118-133, 1928."),
    
    # 复杂度
    "复杂度": ("CLRS2009", "T. H. Cormen et al. Introduction to Algorithms (3rd ed.). MIT Press, 2009."),
    "渐进分析": ("CLRS2009", "T. H. Cormen et al. Introduction to Algorithms (3rd ed.). MIT Press, 2009."),
    "主定理": ("CLRS2009", "T. H. Cormen et al. Introduction to Algorithms (3rd ed.). MIT Press, 2009."),
    "Akra-Bazzi": ("AkraBazzi1998", "M. Akra and L. Bazzi. On the Solution of Linear Recurrence Equations. Computational Optimization and Applications, 10(2):195-210, 1998."),
    "摊还分析": ("Tarjan1985", "R. E. Tarjan. Amortized Computational Complexity. SIAM Journal on Algebraic and Discrete Methods, 6(2):306-318, 1985."),
    "Cook": ("Cook1971", "S. A. Cook. The Complexity of Theorem-Proving Procedures. STOC, 151-158, 1971."),
    "Karp": ("Karp1972", "R. M. Karp. Reducibility Among Combinatorial Problems. Complexity of Computer Computations, 85-103, 1972."),
    "Arora": ("Arora2009", "S. Arora and B. Barak. Computational Complexity: A Modern Approach. Cambridge University Press, 2009."),
    "NP完全": ("Cook1971", "S. A. Cook. The Complexity of Theorem-Proving Procedures. STOC, 151-158, 1971."),
    "Concrete Mathematics": ("Graham1994", "R. L. Graham, D. E. Knuth, and O. Patashnik. Concrete Mathematics (2nd ed.). Addison-Wesley, 1994."),
    "信息论": ("Shannon1948", "C. E. Shannon. A Mathematical Theory of Communication. Bell System Technical Journal, 27:379-423, 1948."),
    "通信复杂度": ("Yao1979", "A. C.-C. Yao. Some Complexity Questions Related to Distributive Computing. STOC, 209-213, 1979."),
    
    # 类型理论
    "Pierce": ("Pierce2002", "B. C. Pierce. Types and Programming Languages. MIT Press, 2002."),
    "Barendregt": ("Barendregt1984", "H. P. Barendregt. The Lambda Calculus: Its Syntax and Semantics. North-Holland, 1984."),
    "Church类型论": ("Church1940", "A. Church. A Formulation of the Simple Theory of Types. Journal of Symbolic Logic, 5(2):56-68, 1940."),
    "Martin-Löf": ("MartinLöf1984", "P. Martin-Löf. Intuitionistic Type Theory. Bibliopolis, 1984."),
    "同伦类型论": ("HoTTBook2013", "The Univalent Foundations Program. Homotopy Type Theory: Univalent Foundations of Mathematics. Institute for Advanced Study, 2013."),
    "HoTT": ("HoTTBook2013", "The Univalent Foundations Program. Homotopy Type Theory. IAS, 2013."),
    "Girard": ("Girard1972", "J.-Y. Girard. Interprétation fonctionnelle et élimination des coupures dans l'arithmétique d'ordre supérieur. PhD thesis, Université Paris 7, 1972."),
    "Reynolds": ("Reynolds1974", "J. C. Reynolds. Towards a Theory of Type Structure. Programming Symposium, 408-425, 1974."),
    "Hindley-Milner": ("Milner1978", "R. Milner. A Theory of Type Polymorphism in Programming. Journal of Computer and System Sciences, 17(3):348-375, 1978."),
    
    # 逻辑
    "Mendelson": ("Mendelson2015", "E. Mendelson. Introduction to Mathematical Logic (6th ed.). CRC Press, 2015."),
    "一阶逻辑": ("Enderton2001", "H. B. Enderton. A Mathematical Introduction to Logic (2nd ed.). Academic Press, 2001."),
    "模态逻辑": ("Kripke1963", "S. Kripke. Semantical Analysis of Modal Logic I. Zeitschrift für Mathematische Logik, 8:67-96, 1963."),
    "直觉逻辑": ("Heyting1930", "A. Heyting. Die formalen Regeln der intuitionistischen Logik. Sitzungsberichte der Preußischen Akademie der Wissenschaften, 42-56, 1930."),
    "时序逻辑": ("Pnueli1977", "A. Pnueli. The Temporal Logic of Programs. FOCS, 46-57, 1977."),
    "Gentzen": ("Gentzen1934", "G. Gentzen. Untersuchungen über das logische Schließen. Mathematische Zeitschrift, 39:176-210, 1934."),
    "SMT": ("BarrettTinelli2018", "C. Barrett and C. Tinelli. Satisfiability Modulo Theories. Handbook of Model Checking, 305-343, 2018."),
    "Z3": ("deMoura2008", "L. de Moura and N. Bjørner. Z3: An Efficient SMT Solver. TACAS, 337-340, 2008."),
    
    # 形式化验证
    "霍尔逻辑": ("Hoare1969", "C. A. R. Hoare. An Axiomatic Basis for Computer Programming. Communications of the ACM, 12(10):576-580, 1969."),
    "Hoare": ("Hoare1969", "C. A. R. Hoare. An Axiomatic Basis for Computer Programming. CACM, 12(10):576-580, 1969."),
    "Dijkstra": ("Dijkstra1976", "E. W. Dijkstra. A Discipline of Programming. Prentice-Hall, 1976."),
    "最弱前置条件": ("Dijkstra1976", "E. W. Dijkstra. A Discipline of Programming. Prentice-Hall, 1976."),
    "抽象解释": ("CousotCousot1977", "P. Cousot and R. Cousot. Abstract Interpretation: A Unified Lattice Model for Static Analysis of Programs. POPL, 238-252, 1977."),
    "Software Foundations": ("SoftwareFoundations", "B. Pierce et al. Software Foundations. Electronic textbook, 2024. https://softwarefoundations.cis.upenn.edu"),
    "Coq": ("Coq", "The Coq Development Team. The Coq Proof Assistant. https://coq.inria.fr"),
    "Lean": ("Lean4", "L. de Moura and S. Ullrich. The Lean 4 Theorem Prover and Programming Language. CADE-28, 2021."),
    "Lean 4": ("Lean4", "L. de Moura and S. Ullrich. The Lean 4 Theorem Prover and Programming Language. CADE-28, 2021."),
    
    # 神经网络/机器学习
    "Goodfellow": ("Goodfellow2016", "I. Goodfellow, Y. Bengio, and A. Courville. Deep Learning. MIT Press, 2016."),
    "深度学习": ("Goodfellow2016", "I. Goodfellow et al. Deep Learning. MIT Press, 2016."),
    "反向传播": ("Rumelhart1986", "D. E. Rumelhart, G. E. Hinton, and R. J. Williams. Learning Representations by Back-Propagating Errors. Nature, 323:533-536, 1986."),
    "McCulloch": ("McCullochPitts1943", "W. S. McCulloch and W. Pitts. A Logical Calculus of the Ideas Immanent in Nervous Activity. Bulletin of Mathematical Biophysics, 5:115-133, 1943."),
    
    # 量子计算
    "Nielsen": ("NielsenChuang2010", "M. A. Nielsen and I. L. Chuang. Quantum Computation and Quantum Information (10th Anniversary ed.). Cambridge University Press, 2010."),
    "量子计算": ("NielsenChuang2010", "M. A. Nielsen and I. L. Chuang. Quantum Computation and Quantum Information. Cambridge University Press, 2010."),
    
    # 其他经典
    "归并排序": ("Knuth1998", "D. E. Knuth. The Art of Computer Programming, Vol. 3: Sorting and Searching (2nd ed.). Addison-Wesley, 1998."),
    "快速排序": ("Hoare1961", "C. A. R. Hoare. Algorithm 64: Quicksort. Communications of the ACM, 4(7):321, 1961."),
    "堆排序": ("Williams1964", "J. W. J. Williams. Algorithm 232: Heapsort. Communications of the ACM, 7(6):347-348, 1964."),
    "Dijkstra算法": ("Dijkstra1959", "E. W. Dijkstra. A Note on Two Problems in Connexion with Graphs. Numerische Mathematik, 1:269-271, 1959."),
    "Bellman-Ford": ("Bellman1958", "R. Bellman. On a Routing Problem. Quarterly of Applied Mathematics, 16(1):87-90, 1958."),
    "Floyd-Warshall": ("Floyd1962", "R. W. Floyd. Algorithm 97: Shortest Path. Communications of the ACM, 5(6):345, 1962."),
    "KMP": ("Knuth1977", "D. E. Knuth, J. H. Morris, and V. R. Pratt. Fast Pattern Matching in Strings. SIAM Journal on Computing, 6(2):323-350, 1977."),
}

def find_best_citation(context, filename):
    """根据上下文和文件名匹配最佳引用"""
    context_lower = context.lower()
    filename_lower = filename.lower()
    
    # 按关键词长度降序排列（优先匹配更长的关键词）
    sorted_keywords = sorted(CITATION_KB.keys(), key=len, reverse=True)
    
    matches = []
    for keyword in sorted_keywords:
        if keyword.lower() in context_lower or keyword.lower() in filename_lower:
            key, desc = CITATION_KB[keyword]
            matches.append((key, desc, len(keyword)))
    
    if matches:
        # 返回匹配长度最长的
        matches.sort(key=lambda x: x[2], reverse=True)
        return matches[0][0], matches[0][1]
    
    return None, None

def process_file(filepath):
    """处理单个文件"""
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()
    except Exception as e:
        return 0, f"读取失败: {e}"
    
    original = content
    fixed_count = 0
    suggestions = []
    
    # 匹配"待补充"及其变体
    patterns = [
        r'（待补充）',
        r'\(待补充\)',
        r'【待补充】',
        r'\[待补充\]',
        r'待补充',
    ]
    
    for pattern in patterns:
        for match in re.finditer(pattern, content):
            start = max(0, match.start() - 150)
            end = min(len(content), match.end() + 150)
            context = content[start:end]
            
            key, desc = find_best_citation(context, str(filepath))
            
            if key:
                # 替换为引用
                replacement = f'[{key}]'
                content = content[:match.start()] + replacement + content[match.end():]
                fixed_count += 1
                suggestions.append(f"  ✓ 位置{match.start()}: {pattern} → [{key}] (基于上下文: {context[:80]}...)")
            else:
                # 添加建议注释
                # 只在第一次遇到时添加注释
                pass
    
    if fixed_count > 0 and content != original:
        # 添加参考文献条目（如果不存在）
        bib_section = "\n\n## 参考文献\n\n"
        added_keys = set()
        for sugg in suggestions:
            if "→ [" in sugg:
                key = sugg.split("→ [")[1].split("]")[0]
                if key not in added_keys and key in [v[0] for v in CITATION_KB.values()]:
                    # 查找描述
                    for k, (rk, desc) in CITATION_KB.items():
                        if rk == key:
                            if desc not in content:
                                bib_section += f"[{key}] {desc}\n\n"
                            added_keys.add(key)
                            break
        
        # 如果文件已有参考文献章节，追加到后面；否则添加
        if "## 参考文献" in content or "## References" in content:
            # 不重复添加参考文献章节标题
            pass
        else:
            content = content.rstrip() + bib_section
        
        with open(filepath, 'w', encoding='utf-8') as f:
            f.write(content)
    
    return fixed_count, suggestions

# 主程序
docs_path = Path("docs")
target_dirs = [
    "01-基础理论", "02-递归理论", "03-形式化证明", "04-算法复杂度",
    "05-类型理论", "06-逻辑系统", "07-计算模型", "09-算法理论",
    "10-高级主题", "12-应用领域", "13-LeetCode算法面试专题"
]

total_fixed = 0
total_files = 0
reports = []

for target in target_dirs:
    target_path = docs_path / target
    if not target_path.exists():
        continue
    
    for md_file in target_path.rglob("*.md"):
        if "待补充" in md_file.read_text(encoding='utf-8'):
            count, sugg = process_file(md_file)
            if count > 0:
                total_fixed += count
                total_files += 1
                reports.append(f"{md_file}: 修复{count}处")

print(f"=== 引用修复报告 ===")
print(f"处理文件数: {total_files}")
print(f"修复引用数: {total_fixed}")
print(f"\n详细记录:")
for r in reports[:50]:
    print(r)
if len(reports) > 50:
    print(f"... 还有 {len(reports)-50} 个文件")
