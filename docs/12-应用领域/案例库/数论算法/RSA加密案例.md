# 案例：RSA加密在HTTPS通信与数字签名中的应用

## 背景

RSA 算法是现代密码学的基石，广泛应用于：

- **HTTPS/TLS**：浏览器与服务器之间的安全通信
- **数字签名**：软件发布、代码签名、文档验证
- **密钥交换**：安全地协商对称加密密钥

## RSA 原理

### 密钥生成

1. 选择两个大素数 $p, q$（通常 1024-2048 位）
2. 计算 $n = p \cdot q$，$\phi(n) = (p-1)(q-1)$
3. 选择公开指数 $e$（通常 65537）
4. 计算私钥 $d \equiv e^{-1} \pmod{\phi(n)}$

**公钥**：$(n, e)$，**私钥**：$(n, d)$

### 加密与解密

- 加密：$c = m^e \mod n$
- 解密：$m = c^d \mod n$

### 数学基础

**欧拉定理**：若 $\gcd(m, n) = 1$，则 $m^{\phi(n)} \equiv 1 \pmod{n}$

因此 $m^{ed} = m^{1 + k\phi(n)} \equiv m \pmod{n}$

## 实际应用

### HTTPS 握手

1. 客户端发送支持的加密套件
2. 服务器返回证书（含 RSA 公钥）
3. 客户端生成随机对称密钥，用服务器公钥加密发送
4. 服务器用私钥解密，获得对称密钥
5. 后续通信使用对称加密（AES）

### 数字签名

1. 对消息 $m$ 计算哈希 $h = H(m)$
2. 用私钥签名：$s = h^d \mod n$
3. 验证：计算 $h' = s^e \mod n$，检查 $h' == H(m)$

**用途**：

- 软件更新签名（Windows Update、App Store）
- 代码签名证书（EV 证书验证开发者身份）
- 区块链交易签名（Bitcoin 使用 ECDSA，但原理类似）

### SSH 密钥认证

- 生成 RSA 密钥对：`ssh-keygen -t rsa -b 4096`
- 公钥放到服务器 `~/.ssh/authorized_keys`
- 私钥用于身份认证

## 性能与安全

| 密钥长度 | 安全级别 | 加密速度 | 用途 |
|---------|---------|---------|------|
| 1024 | ❌ 已弃用 | 快 | 不再使用 |
| 2048 | ✅ 当前标准 | 中等 | 通用 |
| 3072 | ✅ 高安全 | 较慢 | 高安全场景 |
| 4096 | ✅ 极高 | 慢 | 根 CA、长期证书 |

**注意**：RSA 加密速度慢，实际仅用于密钥交换和签名，**数据传输使用对称加密**。

## 后量子密码学

Shor 量子算法可在多项式时间内分解大整数，威胁 RSA 安全性。

**过渡方案**：

- NIST 已标准化后量子算法（CRYSTALS-Kyber、CRYSTALS-Dilithium）
- 混合方案：RSA + 后量子算法同时使用

## 代码参考

- TypeScript: `examples/algorithms-ts/src/number_theory.ts` → `modularExponentiation()`
- Rust: `examples/algorithms/src/number_theory/`
- Go: `examples/algorithms-go/number_theory.go` → `ModPow()`
- Java: `examples/algorithms-java/NumberTheory.java` → `modPow()`

## 效果评估

- RSA-2048 加密 256 位对称密钥约 1-5ms
- 全球每天数十亿次 RSA 操作（HTTPS 握手）
- 数字签名验证是软件供应链安全的核心
