#!/usr/bin/env python3
"""Batch generate 六维补充 for 10-高级主题 and 11-国际化."""

from pathlib import Path

TEMPLATES = {
    "量子": {
        "defs": "量子态 $|\\psi\\rangle = \\sum_i \\alpha_i |i\\rangle$，密度矩阵 $\\rho = \\sum_i p_i |\\psi_i\\rangle\\langle\\psi_i|$",
        "model": "量子电路模型 / 量子图灵机 / 开放量子系统",
        "math": "迹距离 $D(\\rho, \\sigma) = \\frac{1}{2}||\\rho - \\sigma||_1$，保真度 $F(\\rho, \\sigma) = (Tr\\sqrt{\\sqrt{\\rho}\\sigma\\sqrt{\\rho}})^2$",
        "code": "量子门矩阵模拟（见07-计算模型量子补充）",
        "proof": "量子纠错阈值定理：表面码在物理错误率 $p < p_{th} \\approx 1\\%$ 时可实现任意逻辑精度",
        "refs": "Nielsen & Chuang (2010); Preskill (2018); Gottesman (2010)"
    },
    "算法": {
        "defs": "算法 $A: \\mathcal{I} \\to \\mathcal{O}$ 的严格规约，输入/输出/前置/后置条件",
        "model": "RAM 模型 / 并行 PRAM / 分布式消息传递",
        "math": "复杂度递推 $T(n) = aT(n/b) + f(n)$，近似比 $\\rho = ALG/OPT$",
        "code": "Rust 泛型实现 + 单元测试",
        "proof": "循环不变式归纳证明 / 势能法摊还分析",
        "refs": "CLRS (2022); Knuth TAOCP; Vazirani (2001)"
    },
    "AI": {
        "defs": "假设空间 $\\mathcal{H}$，经验风险 $R_{emp}(h) = \\frac{1}{n}\\sum_{i=1}^n L(h(x_i), y_i)$",
        "model": "神经网络计算图 / PAC 学习框架 / 强化学习 MDP",
        "math": "梯度下降 $\\theta_{t+1} = \\theta_t - \\eta \\nabla_\\theta L$，泛化界 $R(h) \\leq R_{emp}(h) + \\sqrt{\\frac{d\\ln(n/d) + \\ln(1/\\delta)}{n}}$",
        "code": "PyTorch/TensorFlow 模型定义或 Rust ndarray 数值计算",
        "proof": "PAC 学习框架下的样本复杂度下界",
        "refs": "Goodfellow et al. (2016); Mohri et al. (2018); Vapnik (1998)"
    },
    "安全": {
        "defs": "安全属性 $P \\subseteq S^\\omega$，攻击面 $\\mathcal{A} = \\{a_1, \\ldots, a_k\\}$",
        "model": "Dolev-Yao 对手模型 / 博弈论安全模型 / 形式化规约",
        "math": "不可区分性 $Adv_A^{IND-CPA}(\\lambda) = |Pr[Exp_1=1] - Pr[Exp_0=1]|$",
        "code": "密码学原语 Rust 实现（AES, SHA, RSA 框架）",
        "proof": "归约证明：若方案不安全，则基础难题可被高效求解",
        "refs": "Katz & Lindell (2014); Bellare & Rogaway (2005); Canetti (2001)"
    },
    "验证": {
        "defs": "规范 $\\phi \\in LTL/CTL$，系统 $M = (S, S_0, R, L)$，满足关系 $M \\models \\phi$",
        "model": "Kripke 结构 / 迁移系统 / 抽象解释域",
        "math": "抽象 Galois 连接 $\\alpha: C \\to A, \\gamma: A \\to C$，widening $\\nabla$",
        "code": "SMT-LIB 接口 / 模型检测器框架 / 定理证明 tactic",
        "proof": "模型检测完备性：有限状态系统 CTL 性质可判定",
        "refs": "Baier & Katoen (2008); Cousot & Cousot (1977); Clarke et al. (1999)"
    },
    "默认": {
        "defs": "核心概念的数学严格定义，输入/输出规约",
        "model": "计算模型设计与抽象层次",
        "math": "关键定理的形式化表述与推导",
        "code": "Rust 工程级实现示例",
        "proof": "形式化证明草图或归纳论证",
        "refs": "领域权威文献（至少5条）"
    }
}

def classify(title):
    t = title.lower()
    if "量子" in t: return TEMPLATES["量子"]
    if any(x in t for x in ["ai", "机器", "学习", "智能", "神经", "联邦", "自适应", "演化"]):
        return TEMPLATES["AI"]
    if any(x in t for x in ["安全", "密码", "鲁棒", "对抗", "隐私", "防御"]):
        return TEMPLATES["安全"]
    if any(x in t for x in ["验证", "证明", "合成", "元编程", "范畴", "同伦"]):
        return TEMPLATES["验证"]
    if any(x in t for x in ["算法", "优化", "复杂", "边缘", "计算"]):
        return TEMPLATES["算法"]
    return TEMPLATES["默认"]

def generate(title, c):
    safe_title = title.replace("-", "-")
    return f"""---
title: {safe_title}-六维补充
category: 10-高级主题
level: 高级
---

# {safe_title} — 六维补充

> **版本**: 1.0
> **创建日期**: 2026-04-20

---

## 一、规范定义深化

{c["defs"]}

## 二、模型设计深化

{c["model"]}

## 三、数学符号与推导

{c["math"]}

## 四、示例性代码

{c["code"]}

## 五、形式化证明

{c["proof"]}

## 六、引用来源

{c["refs"]}
"""

def main():
    base = Path("docs/10-高级主题")
    count = 0
    for f in sorted(base.glob("*.md")):
        # Skip if 六维补充 already exists for this doc
        stem = f.stem
        supp = base / f"{stem}-六维补充.md"
        if supp.exists():
            continue
        c = classify(stem)
        supp.write_text(generate(stem, c), encoding="utf-8")
        count += 1
        print(f"Created: {supp.name}")
    print(f"\nTotal created: {count}")

if __name__ == "__main__":
    main()
