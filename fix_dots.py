import os
files = [
    "01-命题逻辑.md",
    "02-一阶逻辑.md",
    "03-直觉逻辑.md",
    "04-模态逻辑.md",
    "06-线性逻辑.md",
    "07-时序逻辑.md",
]
for fn in files:
    path = os.path.join("docs/06-逻辑系统", fn)
    with open(path, "r", encoding="utf-8") as f:
        text = f.read()
    idx = text.find("## 参考文献")
    body = text[:idx]
    refs = text[idx:]
    refs = refs.replace(".. *", ". *")
    refs = refs.replace(".. In", ". In")
    refs = refs.replace(".. <", ". <")
    # generic fix for double period before capital or quote
    refs = refs.replace(".. \"", ". \"")
    refs = refs.replace("...", ".")
    with open(path, "w", encoding="utf-8") as f:
        f.write(body + refs)
    print("Fixed", fn)
