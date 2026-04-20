use std::collections::{HashMap, HashSet};

/// 复杂度类节点
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ComplexityClass {
    P,
    NP,
    CoNP,
    PSpace,
    EXP,
    NEXP,
    BPP,
    RP,
    CoRP,
    ZPP,
    BQP,
    NPComplete,
    NPHard,
    L,
    NL,
    CoNL,
    EXPSpace,
    NPSpace,
}

impl ComplexityClass {
    pub fn name(&self) -> &'static str {
        match self {
            ComplexityClass::P => "P",
            ComplexityClass::NP => "NP",
            ComplexityClass::CoNP => "co-NP",
            ComplexityClass::PSpace => "PSPACE",
            ComplexityClass::EXP => "EXP",
            ComplexityClass::NEXP => "NEXP",
            ComplexityClass::BPP => "BPP",
            ComplexityClass::RP => "RP",
            ComplexityClass::CoRP => "co-RP",
            ComplexityClass::ZPP => "ZPP",
            ComplexityClass::BQP => "BQP",
            ComplexityClass::NPComplete => "NP-complete",
            ComplexityClass::NPHard => "NP-hard",
            ComplexityClass::L => "L",
            ComplexityClass::NL => "NL",
            ComplexityClass::CoNL => "co-NL",
            ComplexityClass::EXPSpace => "EXPSPACE",
            ComplexityClass::NPSpace => "NPSPACE",
        }
    }

    pub fn description(&self) -> &'static str {
        match self {
            ComplexityClass::P => "多项式时间确定性可解",
            ComplexityClass::NP => "多项式时间非确定性可解 / 解可验证",
            ComplexityClass::CoNP => "补集属于NP",
            ComplexityClass::PSpace => "多项式空间可解",
            ComplexityClass::EXP => "指数时间确定性可解",
            ComplexityClass::NEXP => "指数时间非确定性可解",
            ComplexityClass::BPP => "有界错误概率多项式时间",
            ComplexityClass::RP => "单侧错误概率多项式时间",
            ComplexityClass::CoRP => "RP的补集类",
            ComplexityClass::ZPP => "零错误概率多项式时间 (RP ∩ co-RP)",
            ComplexityClass::BQP => "有界错误量子多项式时间",
            ComplexityClass::NPComplete => "NP中最难的问题 (NP ∩ NP-hard)",
            ComplexityClass::NPHard => "至少与NP中最难问题一样难",
            ComplexityClass::L => "对数空间确定性可解",
            ComplexityClass::NL => "对数空间非确定性可解",
            ComplexityClass::CoNL => "NL的补集类 (= NL)",
            ComplexityClass::EXPSpace => "指数空间可解",
            ComplexityClass::NPSpace => "非确定性多项式空间 (= PSPACE)",
        }
    }
}

/// 复杂度类关系图
pub struct ComplexityGraph {
    edges: HashMap<ComplexityClass, Vec<(ComplexityClass, &'static str)>>,
}

impl ComplexityGraph {
    pub fn standard() -> Self {
        let mut edges: HashMap<ComplexityClass, Vec<(ComplexityClass, &'static str)>> = HashMap::new();

        // 已知包含关系 (A ⊆ B)
        let inclusions = vec![
            (ComplexityClass::L, ComplexityClass::NL, "⊆ (平凡包含)"),
            (ComplexityClass::NL, ComplexityClass::P, "⊆ (开放问题: NL ⊊ P?)"),
            (ComplexityClass::P, ComplexityClass::NP, "⊆ (P vs NP 开放问题)"),
            (ComplexityClass::P, ComplexityClass::BPP, "⊆ (开放问题: P = BPP?)"),
            (ComplexityClass::NP, ComplexityClass::PSpace, "⊆ (Savitch定理: NP ⊆ PSPACE)"),
            (ComplexityClass::CoNP, ComplexityClass::PSpace, "⊆"),
            (ComplexityClass::BPP, ComplexityClass::PSpace, "⊆"),
            (ComplexityClass::PSpace, ComplexityClass::EXP, "⊆ (空间层次定理)"),
            (ComplexityClass::EXP, ComplexityClass::NEXP, "⊆"),
            (ComplexityClass::EXP, ComplexityClass::EXPSpace, "⊆"),
            (ComplexityClass::RP, ComplexityClass::NP, "⊆"),
            (ComplexityClass::CoRP, ComplexityClass::CoNP, "⊆"),
            (ComplexityClass::ZPP, ComplexityClass::RP, "⊆ (ZPP = RP ∩ co-RP)"),
            (ComplexityClass::ZPP, ComplexityClass::CoRP, "⊆"),
            (ComplexityClass::BQP, ComplexityClass::PSpace, "⊆ (BQP ⊆ PSPACE)"),
            (ComplexityClass::NPComplete, ComplexityClass::NP, "⊆ (定义)"),
            (ComplexityClass::NP, ComplexityClass::NPHard, "⊆ (若P=NP则NP ⊆ NP-hard)"),
        ];

        for (from, to, label) in inclusions {
            edges.entry(from.clone()).or_default().push((to, label));
        }

        Self { edges }
    }

    pub fn generate_dot(&self) -> String {
        let mut dot = String::from("digraph ComplexityClasses {\n");
        dot.push_str("  rankdir=BT;\n");
        dot.push_str("  node [shape=box, style=rounded, fontname=\"Helvetica\"];\n\n");

        let mut nodes = HashSet::new();
        for (from, tos) in &self.edges {
            nodes.insert(from.clone());
            for (to, _) in tos {
                nodes.insert(to.clone());
            }
        }

        for node in &nodes {
            dot.push_str(&format!(
                "  \"{}\" [label=\"{}\\n{}\"];\n",
                node.name(),
                node.name(),
                node.description()
            ));
        }

        dot.push_str("\n");
        for (from, tos) in &self.edges {
            for (to, label) in tos {
                dot.push_str(&format!(
                    "  \"{}\" -> \"{}\" [label=\"{}\"];\n",
                    from.name(),
                    to.name(),
                    label
                ));
            }
        }
        dot.push_str("}\n");
        dot
    }

    pub fn transitive_closure(&self) -> HashMap<ComplexityClass, HashSet<ComplexityClass>> {
        let mut closure: HashMap<ComplexityClass, HashSet<ComplexityClass>> = HashMap::new();

        for (from, tos) in &self.edges {
            let set = closure.entry(from.clone()).or_default();
            for (to, _) in tos {
                set.insert(to.clone());
            }
        }

        let all_nodes: Vec<_> = closure.keys().cloned().collect();
        let mut changed = true;
        while changed {
            changed = false;
            for node in &all_nodes {
                if let Some(neighbors) = closure.get(node).cloned() {
                    for neighbor in neighbors {
                        if let Some(nn) = closure.get(&neighbor).cloned() {
                            let set = closure.entry(node.clone()).or_default();
                            for n in nn {
                                if set.insert(n.clone()) {
                                    changed = true;
                                }
                            }
                        }
                    }
                }
            }
        }
        closure
    }
}

fn main() {
    println!("=== 复杂度类关系图生成器 ===\n");

    let graph = ComplexityGraph::standard();
    println!("{}", graph.generate_dot());

    println!("\n=== 传递闭包 ===\n");
    let closure = graph.transitive_closure();
    for (from, tos) in &closure {
        let names: Vec<_> = tos.iter().map(|c| c.name()).collect();
        println!("{} ⊆ {{ {} }}", from.name(), names.join(", "));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_closure() {
        let graph = ComplexityGraph::standard();
        let closure = graph.transitive_closure();
        assert!(closure[&ComplexityClass::P].contains(&ComplexityClass::NP));
        assert!(closure[&ComplexityClass::NP].contains(&ComplexityClass::PSpace));
    }
}
