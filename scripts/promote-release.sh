#!/bin/bash
# 社区推广脚本

VERSION="v2.0.0"
REPO_URL="https://github.com/your-username/FormalAlgorithm"

echo "=========================================="
echo "项目推广发布助手"
echo "=========================================="

echo ""
echo "[1/3] 生成推广文案..."

SHORT_PROMO="🎉 开源项目发布：算法规范与模型设计知识体系 v2.0

📚 200+文档 | 📐 222引用 | 🗺️ 320概念 | 💻 143测试
🌍 对标MIT/Stanford/CMU | ⭐ 国际一流水平

🔗 $REPO_URL

#算法 #计算机科学 #开源 #教育"

LONG_PROMO="🎉【重磅发布】算法规范与模型设计知识体系 v2.0

📊 项目规模：
• 200+ 文档，50万+字
• 222 条学术引用
• 320 概念知识图谱
• 143 代码测试用例

🎓 学术对标：MIT、Stanford、CMU等11所大学

✨ 核心特性：
✅ 严格的形式化定义和证明
✅ 完整的算法实现和测试
✅ 自动化质量保障

🔗 $REPO_URL

欢迎Star⭐、Fork🍴、贡献代码💻！

#算法 #数据结构 #开源 #教育"

echo "$SHORT_PROMO" > scripts/promotions/short_promo.txt
echo "$LONG_PROMO" > scripts/promotions/long_promo.txt

echo "✅ 推广文案已生成"

echo ""
echo "[2/3] 生成推广检查清单..."

cat > scripts/promotions/checklist.md << 'EOF'
# 推广检查清单

## 学术渠道
- [ ] ResearchGate发布
- [ ] 知乎回答相关问题
- [ ] 学术会议宣传

## 开发者社区
- [ ] GitHub Trending
- [ ] Reddit r/algorithms
- [ ] Hacker News
- [ ] 掘金
- [ ] SegmentFault

## 社交媒体
- [ ] Twitter/X
- [ ] 微博
- [ ] 技术群分享

## 目标指标
- Star: 100+ (1周) / 500+ (1月)
- Fork: 20+ (1周) / 100+ (1月)
EOF

echo "✅ 检查清单已生成"

echo ""
echo "[3/3] 完成！"
echo ""
echo "推广材料位置:"
echo "  - scripts/promotions/short_promo.txt"
echo "  - scripts/promotions/long_promo.txt"
echo "  - scripts/promotions/checklist.md"
