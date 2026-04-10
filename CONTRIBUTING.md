# 贡献指南

感谢您对本项目的关注！本文档指导您如何为算法规范与模型设计知识体系做出贡献。

## 项目结构

```
docs/                    # 知识文档
├── 01-基础理论/         # 数学基础
├── 02-递归理论/         # 递归与可计算性
├── ...
└── 习题库/              # 习题集合

examples/algorithms/     # 代码实现
├── src/                 # Rust实现
├── *.go                 # Go实现
├── *.py                 # Python实现
└── *.c                  # C实现
```

## 贡献类型

### 1. 文档改进

- 修正错误或不清晰的内容
- 补充示例或解释
- 添加新的参考文献
- 改进Mermaid图表

### 2. 代码贡献

- 添加新的算法实现
- 优化现有代码性能
- 补充单元测试
- 改进文档注释

### 3. 习题贡献

- 添加新的习题
- 提供习题解答
- 完善题目描述

## 贡献流程

1. **Fork** 项目
2. **创建分支**: `git checkout -b feature/your-feature`
3. **提交更改**: `git commit -am 'Add some feature'`
4. **推送分支**: `git push origin feature/your-feature`
5. **创建 Pull Request**

## 代码规范

### Rust代码
```rust
/// 算法名称
/// 
/// # 复杂度
/// - 时间: O(?)
/// - 空间: O(?)
/// 
/// # 示例
/// ```
/// let result = algorithm_name(input);
/// assert_eq!(result, expected);
/// ```
pub fn algorithm_name(...) -> ... {
    // 实现
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_case() {
        // 测试代码
    }
}
```

### 文档规范
- 使用Markdown格式
- 数学公式使用LaTeX
- 图表使用Mermaid
- 代码块标注语言

## 六维内容标准

每个知识单元应包含：

1. **概念定义** - 形式化定义 + 自然语言解释
2. **属性** - 性质、定理、复杂度
3. **关系** - 概念依赖关系
4. **解释** - 动机、直观、示例
5. **论证** - 非形式化证明
6. **形式证明** - 严格数学证明

## 联系方式

如有疑问，欢迎提交Issue讨论。

---

**许可证**: MIT License
