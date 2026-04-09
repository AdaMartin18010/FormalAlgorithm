# 项目执行脚本

本目录包含项目发布和运营的可执行脚本。

## 脚本列表

### 1. create-release.sh - 创建GitHub Release

创建版本标签和GitHub Release。

**使用方法:**
```bash
./scripts/create-release.sh v2.0.0
```

**功能:**
- 检查git状态
- 创建带注释的标签
- 推送到远程
- 生成发布说明
- 创建GitHub Release（需要gh CLI）

**前置条件:**
- 所有更改已提交
- 安装了GitHub CLI (gh) - 可选

### 2. send-invitations.sh - 生成专家邀请

生成专家邀请邮件模板。

**使用方法:**
```bash
./scripts/send-invitations.sh
```

**功能:**
- 为每个专家生成邀请邮件
- 保存到 scripts/invitations/ 目录

**需要编辑:**
- 脚本中的专家信息（姓名、邮箱、文档）

### 3. promote-release.sh - 推广发布

生成推广文案和检查清单。

**使用方法:**
```bash
./scripts/promote-release.sh
```

**功能:**
- 生成短/长版本推广文案
- 生成推广检查清单

## 完整发布流程

```bash
# 1. 确保所有更改已提交
git status

# 2. 创建GitHub Release
./scripts/create-release.sh v2.0.0

# 3. 生成专家邀请（编辑后运行）
./scripts/send-invitations.sh

# 4. 生成推广材料
./scripts/promote-release.sh

# 5. 按检查清单执行推广
# 复制文案到各平台发布
```

## 注意事项

- 编辑脚本中的占位符信息（用户名、邮箱等）
- 确保有执行权限: `chmod +x scripts/*.sh`
- Windows用户建议使用Git Bash或WSL
