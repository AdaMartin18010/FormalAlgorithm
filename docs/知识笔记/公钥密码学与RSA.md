# 公钥密码学与RSA

> **学科**: 密码学
> **难度**: ★★★★★
> **先修**: 数论基础、模运算、素性测试、概率论
> **学时**: 8学时
> **来源**: Katz-Lindell《Introduction to Modern Cryptography》第8-10章, CLRS第31章
> **版本**: v1.0
> **更新**: 2026-04-09

---

## 一、核心概念

### 1.1 定义

**正式定义**:
公钥加密方案（Public-key Encryption Scheme）是一个三元组 $\Pi = (\text{Gen}, \text{Enc}, \text{Dec})$，其中：

1. **密钥生成算法** $\text{Gen}$：概率算法，输入安全参数 $1^n$，输出密钥对 $(pk, sk)$，其中 $pk$ 为公钥，$sk$ 为私钥
2. **加密算法** $\text{Enc}$：确定性或概率算法，输入公钥 $pk$ 和明文 $m \in \{0,1\}^*$，输出密文 $c \leftarrow \text{Enc}_{pk}(m)$
3. **解密算法** $\text{Dec}$：确定性算法，输入私钥 $sk$ 和密文 $c$，输出明文 $m := \text{Dec}_{sk}(c)$，满足 $\forall (pk, sk) \leftarrow \text{Gen}(1^n), \forall m: \text{Dec}_{sk}(\text{Enc}_{pk}(m)) = m$

**RSA方案的形式化定义**:

- **Gen**: 选择大素数 $p, q$，计算 $N = pq$，选择 $e$ 满足 $\gcd(e, \phi(N)) = 1$，计算 $d = e^{-1} \mod \phi(N)$。输出 $pk = (N, e)$，$sk = (N, d)$
- **Enc**: 对于 $m \in \mathbb{Z}_N^*$，计算 $c = m^e \mod N$
- **Dec**: 计算 $m = c^d \mod N$

**直观解释**:
公钥加密就像邮箱系统：任何人都可以向邮箱（公钥）投递信件（加密），但只有持有钥匙的人（私钥）能打开。RSA的安全性基于"大整数分解问题"的困难性——给定 $N = pq$，从 $N$ 恢复 $p$ 和 $q$ 在计算上是困难的。

**关键要点**:

- **非对称性**: 加密和解密使用不同密钥
- **单向函数**: 公钥到私钥的计算是"陷门"困难的
- **效率权衡**: 比对称加密慢100-1000倍
- **密钥分发优势**: 无需预先共享秘密

### 1.2 属性

| 属性 | 描述 | 备注 |
|------|------|------|
| 非对称性 | 加密用公钥，解密用私钥 | 解决了密钥分发问题 |
| 陷门单向函数 | 正向易计算，逆向困难但有陷门 | RSA基于整数分解 |
| 概率加密 | 相同明文产生不同密文 | 抵抗选择明文攻击 |
| 可公开验证 | 公钥可公开分发 | 需结合PKI确认真伪 |

**性质总结**:

1. **正确性**: 由欧拉定理保证 $(m^e)^d \equiv m^{ed} \equiv m \pmod{N}$
2. **语义安全性**: 需要填充方案（如OAEP）达到IND-CPA/IND-CCA安全
3. **同态性**: RSA具有乘法同态性 $E(m_1) \cdot E(m_2) = E(m_1 \cdot m_2)$

### 1.3 变体

**教科书RSA（Textbook RSA）**:

- 定义: 直接使用 $c = m^e \mod N$ 的原始RSA
- 与标准形式的区别: 缺乏填充，不安全
- 适用场景: 仅用于教学，实际部署禁用

**RSA-OAEP**:

- 定义: Optimal Asymmetric Encryption Padding，带最优非对称加密填充
- 与标准形式的区别: 在加密前应用随机化填充
- 适用场景: 实际部署的标准方案，IND-CCA2安全

**RSA-PSS**:

- 定义: Probabilistic Signature Scheme，用于数字签名
- 与标准形式的区别: 专门的签名填充方案
- 适用场景: 数字签名标准化方案

---

## 二、关系网络

### 2.1 前置知识

| 前置知识 | 重要性 | 掌握程度检验 |
|----------|--------|--------------|
| 模运算与同余 | ⭐⭐⭐⭐⭐ | 能快速计算模幂和模逆元 |
| 欧拉定理与费马小定理 | ⭐⭐⭐⭐⭐ | 能证明RSA的正确性 |
| 素数与互素 | ⭐⭐⭐⭐⭐ | 理解$\phi(N) = (p-1)(q-1)$ |
| 扩展欧几里得算法 | ⭐⭐⭐⭐⭐ | 能计算模逆元 |

### 2.2 相关概念

**紧密相关**:

- 整数分解假设 - RSA安全性的计算基础
- RSA问题（RSAP） - 从$N, e, c = m^e \mod N$恢复$m$
- 陷门置换 - RSA作为单向陷门函数的理论抽象

**一般相关**:

- 离散对数问题 - ElGamal和DSA的基础
- 椭圆曲线密码学 - 提供相同安全性但更短的密钥

### 2.3 后续扩展

学习本主题后，可继续深入：

1. RSA安全性分析 → 计时攻击、故障注入攻击
2. 同态加密 → 全同态加密（FHE）的RSA前身
3. 后量子密码学 → 格密码、多变量密码

### 2.4 思维导图

```
公钥密码学与RSA
├── 理论基础
│   ├── 单向函数
│   ├── 陷门函数
│   ├── 计算复杂性
│   └── 整数分解假设
├── RSA算法
│   ├── 密钥生成 (p, q → N, e, d)
│   ├── 加密 (m^e mod N)
│   ├── 解密 (c^d mod N)
│   └── 签名 (Hash^d mod N)
├── 安全性
│   ├── 教科书RSA攻击
│   ├── 填充方案 (OAEP, PSS)
│   └── 侧信道攻击
├── 实现优化
│   ├── 中国剩余定理 (CRT)
│   ├── 滑动窗口指数
│   └── Montgomery乘法
└── 扩展应用
    ├── 盲签名
    ├── 阈值RSA
    └── RSA-UFO
```

---

## 三、形式化证明

### 3.1 核心定理

**定理 1 (RSA正确性)**: 设 $(N, e, d)$ 为RSA参数，其中 $ed \equiv 1 \pmod{\phi(N)}$。则对于所有 $m \in \mathbb{Z}_N^*$，有 $(m^e)^d \equiv m \pmod{N}$。

**证明**:

已知 $ed \equiv 1 \pmod{\phi(N)}$，即存在整数 $k$ 使得 $ed = 1 + k\phi(N) = 1 + k(p-1)(q-1)$。

计算 $(m^e)^d = m^{ed} = m^{1 + k\phi(N)} = m \cdot (m^{\phi(N)})^k$。

由欧拉定理，对于 $\gcd(m, N) = 1$，有 $m^{\phi(N)} \equiv 1 \pmod{N}$。

因此 $m^{ed} \equiv m \cdot 1^k \equiv m \pmod{N}$。

对于 $\gcd(m, N) \neq 1$ 的情况，设 $m = ap$（不失一般性），则：

- $m \equiv 0 \pmod{p}$，所以 $m^{ed} \equiv 0 \equiv m \pmod{p}$
- 由费马小定理，$m^{q-1} \equiv 1 \pmod{q}$，所以 $m^{ed} = m \cdot (m^{q-1})^{k(p-1)} \equiv m \pmod{q}$

由中国剩余定理，$m^{ed} \equiv m \pmod{N}$。

∎

**证明要点分析**:

1. 利用欧拉定理处理与$N$互素的情况
2. 利用费马小定理和中国剩余定理处理不互素的情况
3. 关键：$ed \equiv 1 \pmod{\phi(N)}$ 保证了指数在模$\phi(N)$下的逆元性质

**定理 2 (RSA到分解的归约)**: 如果在多项式时间内能攻破RSA（从公钥计算私钥），则能在多项式时间内分解$N$。

**证明概要**:

设敌手 $\mathcal{A}$ 能以不可忽略概率计算 $d$ 满足 $ed \equiv 1 \pmod{\phi(N)}$。

给定 $N = pq$，随机选择 $e$ 使得 $\gcd(e, \phi(N)) = 1$。

运行 $\mathcal{A}$ 获得 $d$。则 $ed - 1 = k\phi(N)$ 对于某个 $k$。

选取随机 $a \in \mathbb{Z}_N^*$，计算 $a^{ed-1} \equiv 1 \pmod{N}$。

设 $ed - 1 = 2^s t$（$t$ 为奇数）。计算序列 $a^t, a^{2t}, a^{4t}, \ldots, a^{2^s t} \equiv 1 \pmod{N}$。

若存在 $i$ 使得 $a^{2^i t} \not\equiv \pm 1 \pmod{N}$ 但 $a^{2^{i+1}t} \equiv 1 \pmod{N}$，

则 $\gcd(a^{2^i t} - 1, N)$ 给出 $N$ 的非平凡因子。

重复此过程以高概率成功分解$N$。

∎

### 3.2 辅助引理

**引理 1 (RSA问题的困难性)**: RSA问题是求$e$次根模$N$的问题。若整数分解困难，则RSA问题困难。

*证明概要*: 若存在算法求解RSA问题，则可计算$m = c^{1/e} \mod N$。选择随机$m$，计算$c = m^e \mod N$，运行算法得$m'$。若$m' \neq m$，则$(m')^e \equiv m^e \pmod{N}$，从而$N | (m' - m)(\cdots)$，可能分解$N$。∎

**引理 2 (选择的密文攻击不可行性)**: 教科书RSA在选择密文攻击（CCA）下不安全。

*证明*: 敌手截获 $c = m^e \mod N$，选择随机 $r$，计算 $c' = c \cdot r^e \mod N = (mr)^e \mod N$。

请求解密 $c'$ 得 $m' = mr \mod N$，则 $m = m' \cdot r^{-1} \mod N$。∎

---

## 四、算法/方法详解

### 4.1 算法描述

**RSA密钥生成**:

```
算法: RSA-KeyGen
输入: 安全参数 n (如 2048)
输出: 公钥 pk = (N, e), 私钥 sk = (N, d)

1. 随机选择大素数 p, q，每个约 n/2 位
2. 计算 N = p * q
3. 计算 φ(N) = (p-1) * (q-1)
4. 选择 e 满足 1 < e < φ(N) 且 gcd(e, φ(N)) = 1
   (常用 e = 65537 = 2^16 + 1)
5. 计算 d = e^(-1) mod φ(N)  // 使用扩展欧几里得算法
6. return (pk = (N, e), sk = (N, d))
```

**RSA加密 (教科书版本)**:

```
算法: RSA-Encrypt
输入: 公钥 pk = (N, e), 明文 m ∈ Z_N
输出: 密文 c

1. 确保 0 ≤ m < N
2. c ← m^e mod N  // 使用快速模幂算法
3. return c
```

**RSA解密 (CRT优化)**:

```
算法: RSA-Decrypt-CRT
输入: 私钥 sk = (p, q, d_p, d_q, q_inv), 密文 c
输出: 明文 m

1. m_p ← c^(d_p) mod p  // d_p = d mod (p-1)
2. m_q ← c^(d_q) mod q  // d_q = d mod (q-1)
3. h ← (q_inv * (m_p - m_q)) mod p
4. m ← m_q + h * q
5. return m
```

**流程图**:

```
密钥生成:          加密:              解密:
p,q随机选择        m → m^e mod N      c → c^d mod N
   ↓
N=pq, φ(N)      公钥(N,e)          私钥(N,d)
   ↓
e选择(65537)
   ↓
d = e^(-1) mod φ(N)
```

### 4.2 正确性分析

**RSA的正确性依赖于**：

1. 欧拉定理保证 $(m^e)^d \equiv m \pmod{N}$
2. 模运算的正确实现（防止溢出）
3. 素数的足够大（抵抗分解）

**CRT优化的正确性**:

- $m_p = c^{d_p} \equiv m \pmod{p}$，因为 $c^d \equiv c^{d \mod (p-1)} \equiv c^{d_p} \pmod{p}$
- 同理 $m_q \equiv m \pmod{q}$
- 通过中国剩余定理组合得到唯一 $m \mod N$

### 4.3 复杂度分析

**密钥生成复杂度**:

- 素性测试: $O(n^4)$（使用Miller-Rabin）
- 扩展欧几里得: $O(n^2)$
- 总计: $O(n^4)$（主要开销在素数搜索）

**加密复杂度**:

- 模幂运算: $O(\log e \cdot n^2) = O(n^3)$（对于 $e = 65537$ 为 $O(n^2)$）

**解密复杂度**:

- 朴素实现: $O(n^3)$
- CRT优化: $O(n^3)$ 但常数因子约4倍快

**安全性参数**: 目前推荐 $n = 2048$ 位（NIST）或 $3072$ 位（长期安全）

---

## 五、示例与实例

### 5.1 标准示例

**示例 1: 小型RSA参数演示**

**问题**: 使用 $p = 61, q = 53$ 构造RSA密钥并加密 $m = 65$

**解决过程**:

1. 计算 $N = 61 \times 53 = 3233$
2. 计算 $\phi(N) = (61-1) \times (53-1) = 60 \times 52 = 3120$
3. 选择 $e = 17$（$\gcd(17, 3120) = 1$）
4. 计算 $d = 17^{-1} \mod 3120$
   - 使用扩展欧几里得：$17 \times 2753 - 3120 \times 15 = 1$
   - 所以 $d = 2753$
5. **公钥**: $(N = 3233, e = 17)$
6. **私钥**: $(N = 3233, d = 2753)$

**加密**:
$c = 65^{17} \mod 3233$

- $65^2 = 4225 \equiv 992 \pmod{3233}$
- $65^4 \equiv 992^2 = 984064 \equiv 2553 \pmod{3233}$
- $65^8 \equiv 2553^2 = 6517809 \equiv 1226 \pmod{3233}$
- $65^{16} \equiv 1226^2 = 1503076 \equiv 1735 \pmod{3233}$
- $65^{17} = 65^{16} \times 65 \equiv 1735 \times 65 = 112775 \equiv 2790 \pmod{3233}$

**密文**: $c = 2790$

**解密验证**:
$m = 2790^{2753} \mod 3233 = 65$ ✓

### 5.2 代码实现

**Python实现**:

```python
import random
from typing import Tuple

def is_prime(n: int, k: int = 10) -> bool:
    """Miller-Rabin素性测试"""
    if n < 2: return False
    if n == 2 or n == 3: return True
    if n % 2 == 0: return False

    # 写成 n-1 = 2^r * d
    r, d = 0, n - 1
    while d % 2 == 0:
        r += 1
        d //= 2

    for _ in range(k):
        a = random.randrange(2, n - 1)
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(r - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                break
        else:
            return False
    return True

def generate_prime(bits: int) -> int:
    """生成指定位数的大素数"""
    while True:
        n = random.getrandbits(bits) | 1 | (1 << (bits - 1))
        if is_prime(n):
            return n

def extended_gcd(a: int, b: int) -> Tuple[int, int, int]:
    """扩展欧几里得算法，返回 (g, x, y) 使得 ax + by = gcd(a, b)"""
    if a == 0:
        return b, 0, 1
    g, x1, y1 = extended_gcd(b % a, a)
    x = y1 - (b // a) * x1
    y = x1
    return g, x, y

def mod_inverse(a: int, m: int) -> int:
    """计算模逆元 a^(-1) mod m"""
    g, x, _ = extended_gcd(a % m, m)
    if g != 1:
        raise ValueError("模逆元不存在")
    return (x % m + m) % m

def generate_rsa_keys(bits: int = 2048, e: int = 65537) -> Tuple[Tuple[int, int], Tuple[int, int, int, int, int]]:
    """
    生成RSA密钥对
    返回: ((N, e), (N, d, p, q, q_inv)) - 公钥和私钥(含CRT参数)
    """
    # 生成两个大素数
    p = generate_prime(bits // 2)
    q = generate_prime(bits // 2)
    while q == p:
        q = generate_prime(bits // 2)

    N = p * q
    phi = (p - 1) * (q - 1)

    # 确保 e 与 phi 互素
    while True:
        g, _, _ = extended_gcd(e, phi)
        if g == 1:
            break
        e = random.randrange(3, phi, 2)

    # 计算私钥指数 d
    d = mod_inverse(e, phi)

    # 预计算CRT参数
    d_p = d % (p - 1)
    d_q = d % (q - 1)
    q_inv = mod_inverse(q, p)

    return (N, e), (N, d, p, q, q_inv)

def rsa_encrypt(m: int, pk: Tuple[int, int]) -> int:
    """RSA加密"""
    N, e = pk
    if not 0 <= m < N:
        raise ValueError("消息必须在 [0, N) 范围内")
    return pow(m, e, N)

def rsa_decrypt(c: int, sk: Tuple[int, int, int, int, int]) -> int:
    """RSA解密（使用CRT优化）"""
    N, d, p, q, q_inv = sk

    # CRT优化解密
    d_p = d % (p - 1)
    d_q = d % (q - 1)

    m_p = pow(c, d_p, p)
    m_q = pow(c, d_q, q)

    h = (q_inv * (m_p - m_q)) % p
    m = m_q + h * q

    return m

def rsa_sign(message_hash: int, sk: Tuple[int, int, int, int, int]) -> int:
    """RSA签名（注意：实际应用中应使用填充如PSS）"""
    N, d, p, q, q_inv = sk
    if not 0 <= message_hash < N:
        raise ValueError("哈希值必须在 [0, N) 范围内")
    return pow(message_hash, d, N)

def rsa_verify(message_hash: int, signature: int, pk: Tuple[int, int]) -> bool:
    """RSA签名验证"""
    N, e = pk
    return pow(signature, e, N) == message_hash

# 使用示例
if __name__ == "__main__":
    # 使用小参数便于演示（实际应用应使用2048位或更大）
    print("生成RSA密钥对（512位演示）...")
    pk, sk = generate_rsa_keys(512)
    N, e = pk
    print(f"公钥: N={N:x}, e={e}")

    # 加密消息
    message = 12345678901234567890 % N
    print(f"\n明文: {message}")

    ciphertext = rsa_encrypt(message, pk)
    print(f"密文: {ciphertext}")

    decrypted = rsa_decrypt(ciphertext, sk)
    print(f"解密: {decrypted}")
    print(f"验证: {'成功' if decrypted == message else '失败'}")

    # 签名演示
    hash_val = 0xabcdef1234567890 % N
    sig = rsa_sign(hash_val, sk)
    print(f"\n签名: {sig}")
    print(f"验证: {'成功' if rsa_verify(hash_val, sig, pk) else '失败'}")
```

**Rust实现**:

```rust
use num_bigint::{BigInt, RandBigInt, Sign};
use num_traits::{One, Zero};
use rand::thread_rng;

/// 扩展欧几里得算法
fn extended_gcd(a: &BigInt, b: &BigInt) -> (BigInt, BigInt, BigInt) {
    if b.is_zero() {
        return (a.clone(), BigInt::one(), BigInt::zero());
    }
    let (g, x1, y1) = extended_gcd(b, &(a % b));
    let x = &y1;
    let y = &x1 - (a / b) * &y1;
    (g, x.clone(), y)
}

/// 模逆元
fn mod_inverse(a: &BigInt, m: &BigInt) -> Option<BigInt> {
    let (g, x, _) = extended_gcd(&(a % m), m);
    if g.is_one() {
        Some((x % m + m) % m)
    } else {
        None
    }
}

/// Miller-Rabin素性测试
fn is_prime(n: &BigInt, rounds: usize) -> bool {
    if n <= &BigInt::one() {
        return false;
    }
    if n == &BigInt::from(2) || n == &BigInt::from(3) {
        return true;
    }
    if n % 2 == BigInt::zero() {
        return false;
    }

    // n-1 = 2^r * d
    let mut r = 0;
    let mut d = n - 1;
    while &d % 2 == BigInt::zero() {
        r += 1;
        d /= 2;
    }

    let mut rng = thread_rng();
    for _ in 0..rounds {
        let a = rng.gen_bigint_range(&BigInt::from(2), &(n - 2));
        let mut x = a.modpow(&d, n);
        if x == BigInt::one() || x == n - 1 {
            continue;
        }
        let mut composite = true;
        for _ in 0..(r - 1) {
            x = x.modpow(&BigInt::from(2), n);
            if x == n - 1 {
                composite = false;
                break;
            }
        }
        if composite {
            return false;
        }
    }
    true
}

fn main() {
    // 演示RSA操作（使用小数字）
    let p = BigInt::from(61);
    let q = BigInt::from(53);
    let n = &p * &q;
    let phi = (&p - 1) * (&q - 1);
    let e = BigInt::from(17);
    let d = mod_inverse(&e, &phi).unwrap();

    println!("RSA演示: p={}, q={}", p, q);
    println!("N={}, φ(N)={}", n, phi);
    println!("公钥: (N, e)=({}, {})", n, e);
    println!("私钥: d={}", d);

    let m = BigInt::from(65);
    let c = m.modpow(&e, &n);
    println!("\n明文: {}", m);
    println!("密文: {}", c);

    let decrypted = c.modpow(&d, &n);
    println!("解密: {}", decrypted);
    assert_eq!(m, decrypted);
}
```

### 5.3 反例

**常见错误**:

**错误1: 不安全的素数选择**

```python
# 错误：p和q太接近
p = 2**1024 + 1
q = 2**1024 + 3  # 太接近p
N = p * q
# 攻击者可用Fermat分解法快速分解
```

**错误原因**: 若 $|p-q| < N^{1/4}$，则Fermat分解有效
**正确做法**: 确保$p$和$q$具有不同的位数

**错误2: 共模攻击**

```python
# 错误：同一N，不同的e
m = secret_message
c1 = pow(m, e1, N)
c2 = pow(m, e2, N)
# 若 gcd(e1, e2) = 1，存在 a,b 使得 a*e1 + b*e2 = 1
# 攻击者计算 c1^a * c2^b = m^(a*e1 + b*e2) = m mod N
```

**错误原因**: 同一模数下的不同公钥导致信息泄露
**正确做法**: 每个用户生成独立的$N$

---

## 六、习题

### 6.1 理解题

1. **证明**: 若 $ed \equiv 1 \pmod{\lambda(N)}$，其中 $\lambda(N) = \text{lcm}(p-1, q-1)$（Carmichael函数），则RSA解密仍然正确。

   <details>
   <summary>解答</summary>

   需证 $m^{ed} \equiv m \pmod{N}$ 对所有 $m$ 成立。

   由于 $\lambda(N) | k$ 对某个 $k$ 满足 $ed = 1 + k\lambda(N)$：
   - $m^{ed} = m^{1+k\lambda(N)} = m \cdot (m^{\lambda(N)})^k$
   - 由Carmichael定理，$m^{\lambda(N)} \equiv 1 \pmod{N}$ 当 $\gcd(m, N) = 1$
   - 对于 $\gcd(m, N) \neq 1$，使用中国剩余定理分别验证模$p$和模$q$

   注意 $\lambda(N) = \frac{(p-1)(q-1)}{\gcd(p-1, q-1)}$，比$\phi(N)$更小，可使$d$更小。
   </details>

### 6.2 应用题

1. **实现**: 编写一个使用RSA-OAEP的安全通信程序，包含密钥生成、加密、解密功能。

   <details>
   <summary>解答</summary>

   ```python
   from cryptography.hazmat.primitives.asymmetric import rsa, padding
   from cryptography.hazmat.primitives import hashes

   # 生成密钥
   private_key = rsa.generate_private_key(
       public_exponent=65537,
       key_size=2048,
   )
   public_key = private_key.public_key()

   # OAEP加密
   message = b"Hello, World!"
   ciphertext = public_key.encrypt(
       message,
       padding.OAEP(
           mgf=padding.MGF1(algorithm=hashes.SHA256()),
           algorithm=hashes.SHA256(),
           label=None
       )
   )

   # OAEP解密
   plaintext = private_key.decrypt(
       ciphertext,
       padding.OAEP(
           mgf=padding.MGF1(algorithm=hashes.SHA256()),
           algorithm=hashes.SHA256(),
           label=None
       )
   )
   ```

   </details>

### 6.3 证明题

1. **证明**: 如果RSA签名方案使用Hash-and-Sign范式（先哈希后签名），且哈希函数是抗碰撞的，则该方案在选择消息攻击下存在性不可伪造（EUF-CMA）。

   <details>
   <summary>解答</summary>

   设敌手 $\mathcal{A}$ 能伪造签名。构造归约 $\mathcal{B}$ 破解RSA：

   1. $\mathcal{B}$ 接收RSA挑战 $(N, e, y)$
   2. 模拟签名预言机：对于查询 $m_i$，$\mathcal{B}$ 选择随机 $h_i$，记录 $(m_i, h_i)$，"签名" $\sigma_i = h_i$
   3. 若 $\mathcal{A}$ 输出 $(m^*, \sigma^*)$ 且 $m^*$ 未被查询
   4. 由分叉引理，以一定概率可重绕得到两个不同哈希 $h_1, h_2$ 使得 $h_1^d \equiv h_2^d \pmod{N}$
   5. 则 $(h_1 \cdot h_2^{-1})^d \equiv 1$，可能提取 $e$ 次根

   详细证明见[Coron 2002]。
   </details>

---

## 七、应用场景

### 7.1 经典应用

| 应用场景 | 具体问题 | 使用本主题的原因 |
|----------|----------|------------------|
| TLS握手 | 会话密钥协商 | 传输临时会话密钥 |
| 数字签名 | 代码签名、文档签名 | 提供不可否认性 |
| 密钥封装 | 混合加密系统 | 加密对称密钥 |
| 身份认证 | SSH、PGP | 证明密钥所有权 |

### 7.2 实际案例

**案例**: HTTPS证书链验证

**背景**: 浏览器访问HTTPS网站时验证服务器身份

**应用方式**:

1. 服务器证书包含RSA公钥，由CA私钥签名
2. 浏览器用CA公钥验证证书签名
3. 客户端生成随机预主密钥，用服务器RSA公钥加密传输
4. 双方派生会话密钥进行对称加密

**效果**: 实现身份认证和密钥协商

### 7.3 跨领域联系

**与复杂性理论的联系**:
RSA的安全性基于整数分解不属于P的假设。若P=NP，则RSA不安全（但逆否不成立）。

**与量子计算的联系**:
Shor算法可在多项式时间内分解整数，RSA在量子计算机下不安全。

---

## 八、多维对比

### 8.1 方法对比

| 维度 | RSA-2048 | RSA-3072 | ECC P-256 | ECC P-384 |
|------|----------|----------|-----------|-----------|
| 密钥长度 | 2048位 | 3072位 | 256位 | 384位 |
| 安全级别 | ~112位 | ~128位 | ~128位 | ~192位 |
| 签名大小 | 256字节 | 384字节 | 64字节 | 96字节 |
| 生成速度 | 较慢 | 慢 | 快 | 较快 |
| 抗量子性 | 无 | 无 | 无 | 无 |

### 8.2 决策建议

**何时选择RSA**:

- 需要与遗留系统兼容
- 需要长密钥的历史惯性
- 不需要前向保密

**何时选择ECC**:

- 资源受限环境（移动、IoT）
- 需要更小的密钥和签名
- 新系统设计

---

## 九、扩展阅读

### 9.1 教材章节

| 教材 | 章节 | 页码 | 推荐度 |
|------|------|------|--------|
| Katz & Lindell | Chapter 8-10 | pp. 285-380 | ⭐⭐⭐⭐⭐ |
| CLRS | Chapter 31 | pp. 957-965 | ⭐⭐⭐⭐⭐ |
| Smart | Chapter 3-4 | pp. 45-89 | ⭐⭐⭐⭐☆ |

### 9.2 论文

1. **"A Method for Obtaining Digital Signatures and Public-Key Cryptosystems"** - Rivest, Shamir, Adleman, 1978
   - **要点**: RSA原始论文
   - **链接**: Communications of the ACM

2. **"PKCS #1 v2.2: RSA Cryptography Specifications"** - RSA Laboratories, 2012
   - **要点**: RSA标准规范，含OAEP/PSS

3. **"Twenty Years of Attacks on the RSA Cryptosystem"** - Dan Boneh, 1999
   - **要点**: RSA攻击技术的全面综述

### 9.3 在线资源

- **RSA算法可视化**: <https://cryptool.org/> - 交互式RSA演示
- **Cryptopals挑战**: <https://cryptopals.com/sets/6> - RSA相关挑战
- **NIST SP 800-56B**: <https://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-56Br2.pdf>

---

## 十、专家批注

> **Ron Rivest (RSA共同发明人)**:
> RSA的安全性不在于它不可破解，而在于破解它需要解决一个被认为在计算上不可行的问题——大整数分解。

> **Dan Boneh**:
> 教科书RSA不安全。实际部署必须始终使用适当的填充方案（OAEP用于加密，PSS用于签名）。

---

## 十一、修订历史

| 版本 | 日期 | 修订者 | 修订内容 |
|------|------|--------|----------|
| v1.0 | 2026-04-09 | 系统 | 初始版本 |

---

**标签**: #密码学 #RSA #公钥加密 #整数分解 #数字签名

**相关笔记**:

- [对称加密算法原理](对称加密算法原理.md)
- [椭圆曲线密码学](椭圆曲线密码学.md)
