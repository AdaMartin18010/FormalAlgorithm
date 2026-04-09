#!/bin/bash
# 专家邀请发送脚本模板

set -e

PROJECT_NAME="算法规范与模型设计知识体系"
PROJECT_URL="https://github.com/your-username/FormalAlgorithm"
CONTACT_EMAIL="your-email@example.com"

echo "=========================================="
echo "专家邀请发送准备"
echo "=========================================="

# 示例专家列表（需要填充实际信息）
declare -A EXPERTS=(
    ["doc1"]="专家姓名1"
    ["doc2"]="专家姓名2"
    ["doc3"]="专家姓名3"
)

declare -A EXPERT_EMAILS=(
    ["doc1"]="expert1@university.edu"
    ["doc2"]="expert2@university.edu"
    ["doc3"]="expert3@university.edu"
)

declare -A EXPERT_DOCS=(
    ["doc1"]="docs/01-基础理论/01-形式化定义.md"
    ["doc2"]="docs/05-类型理论/05-依赖类型系统与数理逻辑.md"
    ["doc3"]="docs/09-算法理论/01-算法基础/01-算法设计理论.md"
)

echo "专家列表:"
for key in "${!EXPERTS[@]}"; do
    echo "  - ${EXPERTS[$key]} <${EXPERT_EMAILS[$key]}>"
done

echo ""
echo "生成邀请邮件..."

for key in "${!EXPERTS[@]}"; do
    EXPERT_NAME="${EXPERTS[$key]}"
    EXPERT_EMAIL="${EXPERT_EMAILS[$key]}"
    DOC_PATH="${EXPERT_DOCS[$key]}"
    DOC_NAME=$(basename "$DOC_PATH" .md)
    
    INVITE_FILE="scripts/invitations/invite_${key}_${EXPERT_NAME}.txt"
    
    cat > "$INVITE_FILE" << EOF
主题：邀请您评审【$PROJECT_NAME】项目文档

尊敬的$EXPERT_NAME：

您好！

我是【$PROJECT_NAME】项目的维护团队成员。这是一个开源的算法理论文档项目。

**项目地址**：$PROJECT_URL

## 评审邀请详情

- **评审文档**：$DOC_NAME
- **预计工作量**：2-3小时
- **评审周期**：14-21天

## 评审支持

我们将提供：
1. 完整的评审指南
2. 评审报告模板
3. 项目背景资料
4. 致谢与认可

## 如何参与

如您愿意接受邀请，请回复此邮件。

联系方式：$CONTACT_EMAIL

此致
敬礼

【$PROJECT_NAME】项目团队
$(date +%Y-%m-%d)
EOF

    echo "✅ 已生成: $INVITE_FILE"
done

echo ""
echo "=========================================="
echo "✅ 邀请邮件模板生成完成！"
echo "=========================================="
