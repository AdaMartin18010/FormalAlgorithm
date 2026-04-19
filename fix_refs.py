import re

with open('docs/03-形式化证明/01-证明系统.md', 'r', encoding='utf-8') as f:
    content = f.read()

old_start = '## 7. 参考文献 / References'
new_refs = '''## 7. 参考文献 / References

**引用规范说明 / Citation Guidelines**: 本文档遵循项目引用规范（见 [CITATION_STANDARD.md](../CITATION_STANDARD.md)、[学术引用规范-ACM对齐版.md](../学术引用规范-ACM对齐版.md)）。文内采用 [N] Author. Title. Venue/Publisher, Year. 格式引用。

1. Gentzen, G. "Investigations into Logical Deduction" (Untersuchungen uber das logische Schliessen). *Mathematische Zeitschrift*, 39(1): 176-210, 1935.
2. Hilbert, D., Ackermann, W. *Principles of Mathematical Logic* (Translation of *Grundzuege der theoretischen Logik*, 1928). Chelsea, 1950.
3. Mendelson, E. *Introduction to Mathematical Logic* (6th Edition). CRC Press, 2015.
4. Kleene, S. C. *Introduction to Metamathematics*. North-Holland, 1952.
5. Troelstra, A. S., Schwichtenberg, H. *Basic Proof Theory* (2nd Edition). Cambridge University Press, 2000.
6. Prawitz, D. *Natural Deduction: A Proof-Theoretical Study*. Almqvist & Wiksell, 1965.
7. Haken, A. "The Intractability of Resolution". *Theoretical Computer Science*, 39(2-3): 297-308, 1985.
8. Buss, S. R. "An Introduction to Proof Theory". In *Handbook of Proof Theory* (pp. 1-78). Elsevier, 1998.
9. Urquhart, A. "Hard Examples for Resolution". *Journal of the ACM*, 34(1): 209-219, 1987.
10. Girard, J.-Y., Lafont, Y., Taylor, P. *Proofs and Types*. Cambridge University Press, 1989.

本文档内容已对照 Wikipedia 相关条目（截至2025年1月）进行验证，确保术语定义和理论框架与当前学术标准一致。'''

idx = content.find(old_start)
if idx != -1:
    end_idx = content.find('### 2024-2025', idx)
    if end_idx != -1:
        content = content[:idx] + new_refs + '\n\n' + content[end_idx:]

with open('docs/03-形式化证明/01-证明系统.md', 'w', encoding='utf-8') as f:
    f.write(content)
