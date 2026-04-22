# 案例：FFT在数字信号处理与卷积神经网络加速中的应用

## 背景

快速傅里叶变换（FFT）是 20 世纪最重要的算法之一。它将离散傅里叶变换（DFT）从 $O(n^2)$ 加速至 $O(n \log n)$，彻底改变了数字信号处理、图像处理、通信系统和深度学习领域。

## 核心思想

DFT 将时域信号转换为频域表示：

$$X_k = \sum_{j=0}^{n-1} x_j \cdot e^{-2\pi i j k / n}$$

FFT 利用分治策略：

- 将长度为 $n$ 的 DFT 分解为两个长度为 $n/2$ 的 DFT
- 分别计算偶数项和奇数项
- 通过旋转因子（twiddle factor）合并结果

## 多项式乘法与卷积

两个多项式（或向量）的乘积等价于**卷积**：

$$c_k = \sum_{j=0}^{k} a_j \cdot b_{k-j}$$

**卷积定理**：时域卷积 = 频域逐点乘积

$$FFT(a * b) = FFT(a) \cdot FFT(b)$$

因此：

1. 将 $a, b$ 补零至长度 $2n$
2. $FFT \to$ 逐点乘积 $\to IFFT$
3. 总时间：$O(n \log n)$，远快于直接 $O(n^2)$

## 深度学习中的应用

### 卷积神经网络加速

传统 CNN 使用滑动窗口卷积，计算量大。利用 FFT：

- 将滤波器和特征图转换到频域
- 逐通道逐点相乘
- 逆 FFT 得到输出特征图

对大尺寸卷积核（如 $11 \times 11$、$13 \times 13$），FFT 卷积可比直接计算快 2-5 倍。

### 频域网络（FNet）

Google 提出的 FNet 将 Transformer 的自注意力替换为 FFT：

- 将序列视为时域信号
- 通过 FFT + 线性变换 + IFFT 混合信息
- 速度提升 7 倍，精度损失 < 2%

## 数字通信

### OFDM（正交频分复用）

WiFi、4G/5G、数字电视的核心技术：

- 发送端：IFFT 将频域数据符号转换为时域信号
- 接收端：FFT 将时域信号恢复为频域数据
- 子载波间正交，频谱效率极高

## 代码参考

- TypeScript: `examples/algorithms-ts/src/advanced.ts` → `multiplyPolynomials()`（基于复数 FFT）
- Rust: `examples/algorithms/src/fft.rs`
- C++: `examples/algorithms-cpp/advanced.cpp`（可扩展）

## 效果评估

- 对 $10^6$ 点序列，FFT 仅需约 0.1 秒
- 直接 DFT 需约 3 小时
- 现代 GPU 上，批量 FFT 的吞吐量可达 Teraflops 级别
