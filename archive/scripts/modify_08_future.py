with open("docs/06-逻辑系统/08-高阶逻辑理论.md", "r", encoding="utf-8") as f:
    content = f.read()

extra_future = '''### 高阶依赖类型与逻辑框架

近年来，高阶逻辑与**依赖类型论**（Dependent Type Theory）的融合催生了新的研究方向。在 Martin-Löf 类型论及其扩展（如 Homotopy Type Theory, HoTT）中，高阶量词被推广为依赖乘积 $\\Pi$-类型，而高阶归纳类型则发展为包含路径相等的高阶归纳类型（HITs）。这一框架不仅保留了高阶逻辑的表达能力，还通过单值公理（Univalence Axiom）将逻辑等价与类型等价统一起来，为数学基础提供了全新的范式 [Jacobs1999]。

'''

marker = '## 未来发展方向 / Future Developments'
content = content.replace(marker, extra_future + marker)

with open("docs/06-逻辑系统/08-高阶逻辑理论.md", "w", encoding="utf-8") as f:
    f.write(content)

print("08 future expanded, length:", len(content))
