#!/bin/bash
# GitHub Release 创建脚本
# 使用方法: ./scripts/create-release.sh v2.0.0

set -e

VERSION=${1:-v2.0.0}
REPO="your-username/FormalAlgorithm"

echo "=========================================="
echo "创建 GitHub Release: $VERSION"
echo "=========================================="

# 1. 检查git状态
echo "[1/6] 检查git状态..."
if [ -n "$(git status --porcelain)" ]; then
    echo "❌ 存在未提交的更改，请先提交"
    git status
    exit 1
fi
echo "✅ Git状态干净"

# 2. 创建标签
echo "[2/6] 创建标签 $VERSION..."
git tag -a "$VERSION" -m "Release $VERSION - International Standard"
echo "✅ 标签创建成功"

# 3. 推送标签到远程
echo "[3/6] 推送标签到远程..."
git push origin "$VERSION"
echo "✅ 标签推送成功"

# 4. 生成发布说明
echo "[4/6] 生成发布说明..."
RELEASE_NOTES="docs/RELEASE_NOTES_$VERSION.md"
cat > "$RELEASE_NOTES" << EOF
# Release $VERSION

## 🎉 主要特性

- 📚 200+ 文档，覆盖12个核心模块
- 📐 222 条学术引用
- 🗺️ 320 概念知识图谱  
- 💻 143 代码测试用例
- 🌍 90%+ 国际课程对齐

## 📦 包含内容

### 文档
- 完整理论体系（基础到高级）
- 形式化定义和证明
- 实际应用案例
- 知识图谱和学习路径

### 代码
- Rust算法实现
- 单元测试和基准测试
- CI/CD配置

### 工具
- 自动化质量检查
- 引用验证
- 数学符号检查

## 🚀 快速开始

\`\`\`bash
git clone https://github.com/$REPO.git
cd FormalAlgorithm
# 阅读文档
cat docs/README.md
# 运行测试
cd examples/algorithms && cargo test
\`\`\`

## 📖 更多信息

- [项目文档](docs/README.md)
- [贡献指南](docs/贡献者指南.md)
- [项目发布说明](docs/FINAL_RELEASE_v2.0.md)

## 🙏 致谢

感谢所有贡献者！

---
*发布日期: $(date +%Y-%m-%d)*
EOF
echo "✅ 发布说明已生成: $RELEASE_NOTES"

# 5. 创建GitHub Release（需要gh CLI）
echo "[5/6] 创建GitHub Release..."
if command -v gh &> /dev/null; then
    gh release create "$VERSION" \
        --title "Release $VERSION" \
        --notes-file "$RELEASE_NOTES" \
        --discussion-category "Announcements"
    echo "✅ GitHub Release创建成功"
else
    echo "⚠️ 未安装GitHub CLI (gh)，请手动创建Release"
    echo "访问: https://github.com/$REPO/releases/new?tag=$VERSION"
fi

# 6. 验证
echo "[6/6] 验证发布..."
echo "标签: $(git tag -l $VERSION)"
echo "最新提交: $(git log -1 --oneline)"

echo ""
echo "=========================================="
echo "✅ Release $VERSION 创建完成！"
echo "=========================================="
