# 自动化质量检查工具

本目录包含用于维护项目质量的自动化工具。

## 工具列表

| 工具 | 功能 | 使用场景 |
|------|------|----------|
| `citation_checker.py` | 检查学术引用规范性 | 确保定义、定理后有引用 |
| `math_symbol_checker.py` | 检查数学符号规范 | 确保符合ISO 80000-2 |
| `doc_structure_checker.py` | 检查文档结构 | 确保文档包含必要章节 |
| `quality_check.py` | 运行所有检查 | 综合质量报告 |

## 使用方法

### 单独运行

```bash
# 检查引用
python tools/citation_checker.py

# 检查数学符号
python tools/math_symbol_checker.py

# 检查文档结构
python tools/doc_structure_checker.py
```

### 运行全部检查

```bash
python tools/quality_check.py
```

## 输出报告

所有工具都会生成报告到 `docs/质量报告/` 目录：

- `citation-check-report.md` - 引用检查报告
- `math-symbol-check-report.md` - 数学符号检查报告
- `structure-check-report.md` - 文档结构检查报告
- `quality-check-report.md` - 综合质量报告

## CI/CD 集成

工具已集成到GitHub Actions，在以下情况下自动运行：

- 每次推送到 main 分支
- 每个 Pull Request
- 每周日（定时检查）

## 本地开发

### 添加新的检查规则

1. 在相应的检查器中添加规则
2. 更新此 README
3. 测试新规则
4. 提交PR

### 测试工具

```bash
# 测试单个工具
python tools/citation_checker.py

# 查看输出报告
cat docs/质量报告/citation-check-report.md
```

## 依赖

- Python 3.8+
- 标准库（无需额外安装）

## 贡献

欢迎改进这些工具！请遵循：

1. 保持工具独立运行
2. 生成清晰的报告
3. 添加适当的错误处理
4. 更新文档
