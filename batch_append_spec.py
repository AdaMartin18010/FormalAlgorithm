#!/usr/bin/env python3
"""Batch append 'Specification Instantiation' section to 12-Application Domain docs."""

import os
import re
from pathlib import Path

SPEC_TEMPLATE = """
## 规约与模型在本领域的实例化

### 算法规范设计
- **意图层**：{intent}
- **规约层**：{specification}
- **算法层**：{algorithm}
- **程序层**：{program}
- **实现层**：{implementation}

### 模型实例化
- **计算模型**：{computational_model}
- **复杂度约束**：{complexity}
- **正确性保证**：{correctness}
- **引用来源**：{references}
"""

DOMAINS = {
    "人工智能": {
        "intent": "构建可学习的智能系统，实现感知、推理与决策自动化",
        "specification": "输入：训练数据集 $D = \\{(x_i, y_i)\\}_{i=1}^n$；输出：假设函数 $h: \\mathcal{X} \\to \\mathcal{Y}$ 使期望风险 $R(h)$ 最小化；约束：泛化误差界、计算资源限制、公平性约束",
        "algorithm": "梯度下降、反向传播、Transformer 自注意力、强化学习策略梯度",
        "program": "神经网络前向/反向传播框架，参数更新规则 $\\theta_{t+1} = \\theta_t - \\eta \\nabla_\\theta L$",
        "implementation": "GPU/TPU 并行加速、混合精度训练、模型压缩与量化",
        "computational_model": "RAM 模型（前向/反向传播）+ PRAM/分布式模型（大规模训练）",
        "complexity": "训练时间 $O(ndT)$（$n$ 样本数，$d$ 维度，$T$ 轮数）；推理时间 $O(L \\cdot d^2)$（$L$ 层数）",
        "correctness": "训练收敛性证明（凸优化情形）、PAC 学习理论保证、A/B 测试验证",
        "references": "Goodfellow et al. (2016) Deep Learning; Vapnik (1998) Statistical Learning Theory; LeCun et al. (2015) Nature Deep Learning Review"
    },
    "区块链": {
        "intent": "构建去中心化、不可篡改的分布式账本系统",
        "specification": "输入：交易序列 $T = [t_1, t_2, \\ldots, t_m]$；输出：共识确认的全局状态 $S_t$；约束：拜占庭容错 $\\leq f$ 节点、活性(liveness)与安全(safety)",
        "algorithm": "PoW 哈希难题、PoS 权益证明、PBFT/BFT 共识、Merkle 树验证",
        "program": "区块哈希链接 $H(B_i) = Hash(H(B_{i-1}), MerkleRoot, nonce)$，智能合约虚拟机执行",
        "implementation": "P2P 网络广播、默克尔树存储优化、闪电网络状态通道",
        "computational_model": "分布式异步消息传递模型、拜占庭容错模型",
        "complexity": "区块验证 $O(|T| \\log |T|)$（Merkle 树）；共识轮次 $O(f^2)$（PBFT）",
        "correctness": "BFT 共识安全性证明（$3f+1$ 节点容忍 $f$ 拜占庭节点）、形式化验证（Coq/Isabelle 验证智能合约）",
        "references": "Nakamoto (2008) Bitcoin Whitepaper; Castro & Liskov (2002) PBFT; Buterin (2014) Ethereum Whitepaper"
    },
    "网络安全": {
        "intent": "保护信息系统免受未授权访问、攻击与数据泄露",
        "specification": "输入：网络流量/系统日志 $L = [l_1, \\ldots, l_n]$；输出：威胁检测标记 $Y \\in \\{0,1\\}^n$ 或加密密文 $C$；约束：误报率 $\\leq \\epsilon$、延迟 $\\leq \\Delta t$、前向安全性",
        "algorithm": "AES/RSA 加解密、SHA 哈希、入侵检测模式匹配、零知识证明",
        "program": "对称加密 $C = E_K(P)$，公钥加密 $C = P^e \\mod n$，数字签名验证 $Verify(PK, M, \\sigma)$",
        "implementation": "硬件安全模块(HSM)、TLS/SSL 协议栈、同态加密库",
        "computational_model": "RAM 模型（加解密）+ 交互式证明模型（零知识证明）",
        "complexity": "AES 加密 $O(n)$ 块操作；RSA 加密 $O(k^3)$（$k$ 密钥长度）；SHA-256 $O(n)$",
        "correctness": "密码学归约证明（IND-CPA/IND-CCA 安全性）、形式化协议验证（Tamarin/ProVerif）",
        "references": "Katz & Lindell (2014) Introduction to Modern Cryptography; Ferguson et al. (2015) Cryptography Engineering; Bellare & Rogaway (2005) Introduction to Modern Cryptography"
    },
    "生物信息学": {
        "intent": "从生物分子数据中提取生物学意义，辅助基因组学与药物发现",
        "specification": "输入：DNA/RNA/蛋白质序列 $S \\in \\{A,C,G,T\\}^n$；输出：比对结果、结构预测或进化树；约束：序列长度可达 $10^9$ bp、错误率容忍",
        "algorithm": "Needleman-Wunsch 全局比对、Smith-Waterman 局部比对、Burrows-Wheeler 变换、隐马尔可夫模型",
        "program": "动态规划比对矩阵 $M[i,j] = \\max\\{M[i-1,j-1]+s(S_i,T_j), M[i-1,j]-d, M[i,j-1]-d\\}$",
        "implementation": "BWA/Bowtie 索引、SAM/BAM 格式、GPU 加速序列比对",
        "computational_model": "RAM 模型（DP 比对）+ 外存模型（大规模基因组索引）",
        "complexity": "全局比对 $O(mn)$；BWT 搜索 $O(m \\log n)$；de Bruijn 图组装 $O(n)$",
        "correctness": "比对最优性证明（DP 归纳）、假阳性率控制（Bonferroni/FDR 校正）",
        "references": "Durbin et al. (1998) Biological Sequence Analysis; Jones & Pevzner (2004) An Introduction to Bioinformatics Algorithms; Trapnell & Salzberg (2009) Nature Reviews Genetics"
    },
    "金融": {
        "intent": "优化资产配置、风险定价与交易执行，提升金融市场效率",
        "specification": "输入：资产价格序列 $P_t = (p_t^{(1)}, \\ldots, p_t^{(d)})$、风险约束 $\\sigma_{max}$；输出：投资组合权重 $w^*$ 或期权定价 $V$；约束：预算 $\\sum w_i = 1$、风险值 $VaR_\\alpha \\leq V_{max}$",
        "algorithm": "马科维茨均值-方差优化、Black-Scholes 定价、蒙特卡洛模拟、高频交易撮合",
        "program": "优化问题 $\\min_w w^T \\Sigma w - \\lambda \\mu^T w$，s.t. $\\sum w_i = 1, w_i \\geq 0$",
        "implementation": "实时行情处理（FPGA 加速）、风险引擎并行计算、监管报告自动化",
        "computational_model": "RAM 模型（优化求解）+ 流计算模型（实时行情处理）",
        "complexity": "均值-方差优化 $O(d^3)$（协方差矩阵求逆）；蒙特卡洛 $O(N \\cdot d \\cdot T)$（$N$ 路径数）",
        "correctness": "无套利定价原理、风险中性测度存在性证明、回溯测试统计显著性",
        "references": "Hull (2018) Options, Futures, and Other Derivatives; Markowitz (1952) Portfolio Selection; Black & Scholes (1973) The Pricing of Options"
    },
    "游戏": {
        "intent": "构建智能对手、路径规划与渲染优化，提升游戏体验与真实感",
        "specification": "输入：游戏状态 $S_t$（玩家位置、NPC 状态、地图信息）；输出：NPC 动作 $a_t$ 或渲染帧；约束：帧率 $\\geq 60$ FPS、响应延迟 $\\leq 16$ ms",
        "algorithm": "A* 寻路、行为树、Minimax/Alpha-Beta 博弈树、蒙特卡洛树搜索(MCTS)",
        "program": "Minimax 递归 $v(s) = \\max_a \\min_{a'} v(s')$，Alpha-Beta 剪枝边界 $\\alpha \\leq v \\leq \\beta$",
        "implementation": "空间哈希加速碰撞检测、LOD 层级细节、ECS 实体组件系统",
        "computational_model": "RAM 模型（AI 决策）+ 实时调度模型（渲染管线）",
        "complexity": "A* 最坏 $O(b^d)$（$b$ 分支因子，$d$ 深度）；Alpha-Beta 最优 $O(b^{d/2})$；MCTS $O(K \\cdot d)$（$K$ 模拟次数）",
        "correctness": "A* 可采纳性（admissible heuristic 保证最优）、博弈树完备性",
        "references": "Russell & Norvig (2020) AIMA; Browne et al. (2012) A Survey of MCTS; Ericson (2004) Real-Time Collision Detection"
    },
    "物联网": {
        "intent": "实现海量设备的连接管理、数据采集与边缘智能决策",
        "specification": "输入：传感器数据流 $\\{x_t^{(i)}\\}_{i=1}^N$（$N$ 设备数）；输出：聚合统计或控制指令；约束：功耗 $\\leq P_{max}$、带宽 $\\leq B$、端到端延迟 $\\leq L$",
        "algorithm": "数据压缩（有损/无损）、轻量级机器学习（TinyML）、一致性哈希路由、时序数据库聚合",
        "program": "滑动窗口聚合 $\\bar{x}_w = \\frac{1}{w}\\sum_{t=w_0}^{w_0+w} x_t$，边缘推理量化模型 $Q(w) = round(w / s) \\times s$",
        "implementation": "MQTT/CoAP 协议栈、边缘计算节点、联邦学习框架",
        "computational_model": "分布式流处理模型（Apache Flink/Spark Streaming）、受限 RAM 模型（微控制器）",
        "complexity": "一致性哈希查找 $O(1)$；滑动窗口聚合均摊 $O(1)$；联邦学习通信轮次 $O(1/\\epsilon)$",
        "correctness": "传感器数据校验和、共识算法安全性（Raft/PBFT 轻量版）、联邦学习收敛性",
        "references": "Stankovic (2014) Research Directions for IoT; Howard et al. (2017) MobileNets; McMahan et al. (2017) Communication-Efficient Learning of Deep Networks"
    },
    "量子": {
        "intent": "利用量子力学原理实现超越经典计算的算法加速",
        "specification": "输入：量子态 $|\\psi\\rangle = \\sum_i \\alpha_i |i\\rangle$；输出：测量结果 $m$ 或酉变换 $U|\\psi\\rangle$；约束：相干时间 $T_2$、门保真度 $\\geq F_{min}$、量子比特数 $\\leq N_{max}$",
        "algorithm": "Shor 因数分解、Grover 搜索、量子相位估计(QPE)、变分量子本征求解器(VQE)",
        "program": "量子电路模型：初始化 $|0\\rangle^{\\otimes n}$，应用酉门序列 $U = U_k \\cdots U_1$，测量计算基",
        "implementation": "超导量子比特控制、离子阱激光操控、量子纠错表面码",
        "computational_model": "量子图灵机 / 量子电路模型",
        "complexity": "Grover 搜索 $O(\\sqrt{N})$（经典 $O(N)$）；Shor 因数分解 $O((\\log n)^3)$（经典次指数）；量子模拟 $O(poly(n))$（经典指数）",
        "correctness": "量子门幺正性保证、量子纠错阈值定理（表面码阈值 $\\approx 1\\%$）、量子优势实验验证",
        "references": "Nielsen & Chuang (2010) Quantum Computation and Quantum Information; Shor (1994) Algorithms for Quantum Computation; Preskill (2018) Quantum Computing in the NISQ era"
    },
    "能源": {
        "intent": "优化能源生产、传输与消费，提升可再生能源利用率与电网稳定性",
        "specification": "输入：可再生能源出力预测 $\\hat{P}_t^{(ren)}$、负荷需求 $D_t$、储能状态 $SOC_t$；输出：调度计划 $G_t^{(disp)}, P_t^{(dis)}$；约束：功率平衡 $\\sum G_t + P_t^{(dis)} = D_t$、储能容量 $SOC_{min} \\leq SOC_t \\leq SOC_{max}$",
        "algorithm": "混合整数线性规划(MILP)、模型预测控制(MPC)、强化学习调度",
        "program": "MPC 优化 $\\min_{u_{t:t+H}} \\sum_{k=t}^{t+H} (c_k^T u_k + x_k^T Q x_k)$，s.t. 动态约束 $x_{k+1} = A x_k + B u_k$",
        "implementation": "SCADA 系统集成、分布式能源管理系统(DERMS)、虚拟电厂聚合平台",
        "computational_model": "连续时间动态系统 + 离散事件调度模型",
        "complexity": "MILP 最坏指数，实际启发式 $O(n^{2.5})$；MPC 每步 $O(H^3 d^3)$（$H$ 时域，$d$ 状态维）",
        "correctness": "Lyapunov 稳定性证明（MPC）、电力潮流计算收敛性、日前调度可行性验证",
        "references": "Wood et al. (2013) Power Generation, Operation, and Control; Camacho & Bordons (2007) Model Predictive Control; Rasmussen et al. (2016) Renewable Energy Integration"
    },
    "医疗健康": {
        "intent": "辅助疾病诊断、药物发现与个性化治疗方案制定",
        "specification": "输入：患者电子健康记录 $EHR = (demo, labs, imaging, genomics)$、医学影像 $I \\in \\mathbb{R}^{H\\times W\\times C}$；输出：诊断概率 $P(disease|EHR)$ 或分割掩膜 $M$；约束：敏感性 $\\geq Se_{min}$、特异性 $\\geq Sp_{min}$、FDA/CE 监管合规",
        "algorithm": "卷积神经网络(CNN)影像分类、U-Net 分割、图神经网络(GNN)药物-靶点交互、生存分析 Cox 模型",
        "program": "CNN 前向传播 $f_\\theta(I) = softmax(W_L \\cdot ReLU(W_{L-1} \\cdots ReLU(W_1 \\ast I)))$",
        "implementation": "DICOM 标准兼容、联邦学习多中心训练、差分隐私保护、临床决策支持系统集成",
        "computational_model": "RAM 模型（推理）+ 分布式训练模型（联邦学习）",
        "complexity": "CNN 推理 $O(HWLK^2)$（$K$ 卷积核大小）；U-Net 分割 $O(HW)$；GNN 消息传递 $O(|E|)$",
        "correctness": "交叉验证 AUC-ROC、临床试验统计效力、医学图像分割 Dice 系数 $\\geq 0.9$",
        "references": "Esteva et al. (2019) Nature Medicine Deep Learning; Ronneberger et al. (2015) U-Net MICCAI; Topol (2019) Deep Medicine"
    },
    "智能制造": {
        "intent": "实现生产过程的自动化、质量监控与供应链优化",
        "specification": "输入：传感器时序数据 $\\{x_t\\}$、订单需求 $D = \\(d_1, \\ldots, d_m\\)$、设备状态 $S_t$；输出：生产调度 $\\pi$ 或质量预测 $\\hat{y}$；约束：交货期 $\\leq T_{due}$、设备利用率 $\\geq U_{min}$、缺陷率 $\\leq \\delta_{max}$",
        "algorithm": "作业车间调度(JSP)、数字孪生仿真、异常检测（Isolation Forest/LSTM-AE）、预测性维护（RUL 估计）",
        "program": "调度约束满足 $\\min_{\\pi} C_{max}(\\pi)$，s.t. $\\pi_j \\geq r_j, p_j \\leq d_j$；LSTM 预测 $h_t = LSTM(x_t, h_{t-1})$",
        "implementation": "OPC-UA 工业协议、MES/ERP 集成、边缘 AI 质检、AGV 路径规划",
        "computational_model": "离散事件仿真模型（数字孪生）+ 实时控制模型（PLC/RT）",
        "complexity": "JSP 强 NP-hard；启发式调度 $O(n^2)$；LSTM 推理 $O(T \\cdot d^2)$（$T$ 序列长，$d$ 隐藏维）",
        "correctness": "调度可行性验证（约束满足）、统计过程控制(SPC) $3\\sigma$ 原则、预测性维护置信区间",
        "references": "Lee et al. (2015) Manufacturing Big Data; Kusiak (2018) Smart Manufacturing; Zhao et al. (2020) Deep Learning for Smart Manufacturing"
    },
    "交通": {
        "intent": "优化交通流、路径规划与物流调度，降低运输成本与环境影响",
        "specification": "输入：路网图 $G=(V,E,w)$、实时交通流量 $f_e(t)$、货运需求 $R=\\{(o_i,d_i,q_i)\\}$；输出：路径集合 $P^*$ 或信号灯配时 $\\theta$；约束：通行时间 $\\leq T_{max}$、载重 $\\leq C_{cap}$、碳排放 $\\leq E_{max}$",
        "algorithm": "Dijkstra/A* 最短路径、Vehicle Routing Problem(VRP) 启发式、深度强化学习信号灯控制",
        "program": "A* 搜索 $f(n) = g(n) + h(n)$（$h(n)$ 为到目标启发式距离）；VRP 节约算法 $s_{ij} = c_{i0} + c_{0j} - c_{ij}$",
        "implementation": "GPS/北斗定位、V2X 车联网通信、仓库自动化(AMR)、无人机最后一公里配送",
        "computational_model": "图模型（路网）+ 实时流模型（交通状态）+ 组合优化模型（调度）",
        "complexity": "Dijkstra $O(|E| + |V|\\log|V|)$；VRP 精确解指数，启发式 $O(n^3)$；信号灯控制每步 $O(|A|)$（$|A|$ 动作空间）",
        "correctness": "路径最优性证明（Dijkstra）、信号灯控制稳定性（Lyapunov）、物流准时交付率",
        "references": "Dantzig & Ramser (1959) The Truck Dispatching Problem; Wiering (2000) Multi-Agent Reinforcement Learning for Traffic Light Control; Vidal et al. (2013) Heuristics for Multi-Attribute VRP"
    },
    "元宇宙": {
        "intent": "构建沉浸式虚拟环境，支持社交、协作与数字资产交互",
        "specification": "输入：用户动作/语音 $U_t$、场景描述 $S$；输出：渲染帧（延迟 $\\leq 20$ ms）、虚拟资产更新；约束：帧率 $\\geq 90$ FPS（VR）、同步延迟 $\\leq 50$ ms、并发用户 $\\leq N_{max}$",
        "algorithm": "3D 渲染管线（光栅化/光线追踪）、物理引擎（刚体/流体模拟）、空间音频、区块链资产确权",
        "program": "光线追踪 $L_o(p, \\omega_o) = L_e(p, \\omega_o) + \\int_\\Omega f(p, \\omega_i, \\omega_o) L_i(p, \\omega_i) |\\cos\\theta_i| d\\omega_i$",
        "implementation": "云渲染串流、边缘节点分布式物理模拟、NFT 智能合约、低延迟音视频同步",
        "computational_model": "实时图形渲染管线 + 分布式模拟模型 + 区块链状态机",
        "complexity": "光栅化 $O(n)$（$n$ 像素数）；光线追踪 $O(k \\cdot n)$（$k$ 每像素光线数）；物理模拟 $O(m^2)$（$m$ 刚体数）",
        "correctness": "渲染一致性（帧同步）、物理模拟能量守恒、智能合约形式化验证",
        "references": "Pharr et al. (2016) Physically Based Rendering; Stephenson (1992) Snow Crash; Ball et al. (2022) The Metaverse: And How It Will Revolutionize Everything"
    },
    "航天": {
        "intent": "保障航天器轨道设计、自主导航与任务规划的可靠性",
        "specification": "输入：初始轨道参数 $(a, e, i, \\Omega, \\omega, M_0)$、任务约束；输出：机动脉冲 $\\Delta v$ 序列或着陆轨迹；约束：燃料 $\\Delta v_{total} \\leq \\Delta v_{budget}$、推力 $T_{max}$、避障距离 $\\geq d_{safe}$",
        "algorithm": "Lambert 轨道转移、凸优化轨迹规划（G-FOLD）、扩展卡尔曼滤波(EKF)导航、SLAM 相对导航",
        "program": "Lambert 问题求解 $\\Delta v = f(r_1, r_2, \\Delta t)$；凸优化 $\\min_{\\mathbf{x}} \\mathbf{c}^T\\mathbf{x}$，s.t. $A\\mathbf{x} \\leq \\mathbf{b}$",
        "implementation": "星载计算机抗辐射加固、深空通信协议(DTN)、自主故障检测与恢复(FDIR)",
        "computational_model": "轨道力学模型（二体/多体问题）+ 嵌入式实时模型",
        "complexity": "Lambert 迭代求解 $O(k)$（$k$ 迭代次数）；凸优化内点法 $O(n^{3.5})$；EKF 更新 $O(d^3)$（$d$ 状态维）",
        "correctness": "轨道力学守恒量验证（能量、角动量）、凸优化 KKT 条件、导航滤波一致性检验（$\\chi^2$ 测试）",
        "references": "Vallado (2013) Fundamentals of Astrodynamics; Acikmese & Ploen (2007) Convex Programming Approach to Powered Desc Guidance; Maybeck (1982) Stochastic Models, Estimation, and Control"
    },
    "环境": {
        "intent": "监测、模拟与优化环境系统，支持气候研究与可持续发展决策",
        "specification": "输入：多源环境监测数据（卫星遥感、地面站、传感器网络）；输出：污染扩散预测、碳足迹评估或资源优化方案；约束：空间分辨率、时间频率、不确定性量化",
        "algorithm": "偏微分方程数值求解（FVM/FDM）、遥感图像语义分割、生命周期评估(LCA)算法、多目标优化",
        "program": "对流扩散方程 $\\frac{\\partial C}{\\partial t} + \\mathbf{u} \\cdot \\nabla C = \\nabla \\cdot (D \\nabla C) + R$",
        "implementation": "GIS 空间分析平台、气候模型并行计算（MPI）、IoT 环境监测网络、区块链碳核算",
        "computational_model": "连续介质模型（PDE）+ 离散网格模型 + 传感器网络模型",
        "complexity": "PDE 求解 $O(N_x N_y N_t)$（$N$ 网格点数）；遥感分割 $O(HW)$；LCA 矩阵运算 $O(n^3)$（$n$ 流程数）",
        "correctness": "数值格式稳定性（CFL 条件）、质量守恒验证、蒙特卡洛不确定性传播",
        "references": "Thomann & Mueller (1987) Principles of Surface Water Quality Modeling; IPCC (2021) Climate Change 2021: The Physical Science Basis; Hauschild & Huijbregts (2015) Life Cycle Impact Assessment"
    },
    "教育": {
        "intent": "个性化学习路径推荐、自动评测与教育内容生成",
        "specification": "输入：学习者知识状态 $\\theta_t$、学习历史 $H_t$、内容库 $C$；输出：推荐内容 $c^*$ 或能力评估 $\\hat{\\theta}$；约束：认知负荷 $\\leq CL_{max}$、学习时长 $\\leq T_{max}$、目标掌握度 $\\geq \\tau$",
        "algorithm": "项目反应理论(IRT)、知识追踪(DKT/BKT)、强化学习推荐、自然语言处理自动评测",
        "program": "IRT 响应概率 $P(X_{ij}=1|\\theta_i, a_j, b_j) = \\frac{1}{1 + e^{-a_j(\\theta_i - b_j)}}$；BKT 贝叶斯更新 $P(L_{t+1}|obs) \\propto P(obs|L_t)P(L_t)$",
        "implementation": "学习管理系统(LMS)集成、自适应测试引擎、LLM 辅助内容生成、学习分析仪表盘",
        "computational_model": "隐马尔可夫模型（知识追踪）+ 推荐系统模型 + NLP 模型",
        "complexity": "IRT 参数估计 EM 算法 $O(n m)$（$n$ 学生数，$m$ 题目数）；DKT 推理 $O(T \\cdot d^2)$；推荐排序 $O(|C| \\log |C|)$",
        "correctness": "IRT 参数可识别性、知识追踪预测 AUC、教育实验随机对照试验(RCT)",
        "references": "van der Linden & Hambleton (1997) Handbook of Modern IRT; Corbett & Anderson (1994) Knowledge Tracing; Piech et al. (2015) Deep Knowledge Tracing"
    },
    "数字人文": {
        "intent": "利用计算技术辅助人文研究，实现文本挖掘、文化遗产数字化与历史分析",
        "specification": "输入：数字化文本语料 $\\mathcal{D}$、图像/3D 模型 $M$、地理空间数据 $G$；输出：主题模型 $\\phi, \\theta$、风格分类或时空可视化；约束： OCR 准确率 $\\geq 95\\%$、多语言支持、版权合规",
        "algorithm": "主题模型(LDA)、词嵌入(Word2Vec/BERT)、风格计量学(stylometry)、GIS 时空分析",
        "program": "LDA 生成过程 $\\theta_d \\sim Dir(\\alpha), \\phi_k \\sim Dir(\\beta), z_{dn} \\sim Mult(\\theta_d), w_{dn} \\sim Mult(\\phi_{z_{dn}})$",
        "implementation": "TEI/XML 文本编码标准、IIIF 图像互操作框架、知识图谱(Linked Open Data)、VR 文化遗产展示",
        "computational_model": "概率图模型（LDA）+ 向量空间模型（词嵌入）+ 时空数据库模型",
        "complexity": "LDA Gibbs 采样 $O(N_{iter} \\cdot D \\cdot \\bar{N}_d \\cdot K)$（$K$ 主题数）；BERT 编码 $O(L^2)$（$L$ 序列长）",
        "correctness": "主题一致性(Coherence Score)、风格分类交叉验证、地理编码精度",
        "references": "Blei et al. (2003) Latent Dirichlet Allocation; Jockers (2013) Macroanalysis; Moretti (2013) Distant Reading"
    },
    "创意产业": {
        "intent": "辅助内容创作、风格迁移与生成式设计",
        "specification": "输入：创作约束（风格参考 $R$、主题 $T$、格式 $F$）；输出：生成内容（图像/音乐/文本）；约束：版权原创性、风格一致性、用户可控性",
        "algorithm": "生成对抗网络(GAN)、扩散模型(Diffusion)、神经风格迁移、变分自编码器(VAE)",
        "program": "扩散模型前向 $q(x_t|x_{t-1}) = \\mathcal{N}(x_t; \\sqrt{1-\\beta_t}x_{t-1}, \\beta_t I)$，反向去噪 $p_\\theta(x_{t-1}|x_t)$",
        "implementation": "GPU 集群训练、实时推理优化(TensorRT/ONNX)、版权检测系统、协作创作平台",
        "computational_model": "生成模型（概率密度估计）+ 优化模型（风格损失最小化）",
        "complexity": "扩散模型采样 $O(T \\cdot d)$（$T$ 扩散步数，$d$ 数据维）；风格迁移 $O(HW)$",
        "correctness": "生成质量评估(FID/IS)、风格损失 $L_{style} = \\sum_l ||G_l^\\phi(y) - G_l^\\phi(s)||_F^2$、A/B 测试用户偏好",
        "references": "Goodfellow et al. (2014) GANs; Ho et al. (2020) Denoising Diffusion Probabilistic Models; Gatys et al. (2016) Image Style Transfer"
    },
    "社会科学": {
        "intent": "量化社会现象、预测群体行为与评估政策效果",
        "specification": "输入：社会调查数据、网络关系 $G=(V,E)$、历史面板数据；输出：因果效应估计 $\\hat{\\tau}$、网络影响力排名或舆情趋势；约束：隐私保护（差分隐私 $\\epsilon \\leq 1$）、代表性偏差控制",
        "algorithm": "因果推断（双重差分DiD、工具变量IV）、社会网络分析（PageRank、社区发现）、情感分析、主题演化",
        "program": "DiD 估计 $\\hat{\\tau} = (\\bar{Y}_{post}^{(t)} - \\bar{Y}_{pre}^{(t)}) - (\\bar{Y}_{post}^{(c)} - \\bar{Y}_{pre}^{(c)})$；PageRank $r_i = \\alpha \\sum_{j\\to i} \\frac{r_j}{d_j} + (1-\\alpha)\\frac{1}{N}$",
        "implementation": "调查数据脱敏处理、社交网络 API 数据采集、政策模拟沙盘、可视化叙事工具",
        "computational_model": "统计推断模型 + 图模型 + 时间序列模型",
        "complexity": "PageRank 幂迭代 $O(k|E|)$（$k$ 迭代次数）；社区发现 Louvain $O(|V| \\log |V|)$；DiD 回归 $O(n)$",
        "正确性": "因果识别假设验证（平行趋势、排他性）、统计显著性（$p < 0.05$）、样本外预测效度",
        "references": "Angrist & Pischke (2009) Mostly Harmless Econometrics; Wasserman & Faust (1994) Social Network Analysis; King et al. (1994) Designing Social Inquiry"
    },
    "认知科学": {
        "intent": "建模人类认知过程，构建类脑计算与智能交互系统",
        "specification": "输入：刺激信号 $S$、被试行为数据 $B$、神经影像数据 $fMRI/EEG$；输出：认知模型参数 $\\theta$ 或脑机接口控制信号；约束：神经解码准确率 $\\geq A_{min}$、实时性 $\\leq \\Delta t$、伦理审批",
        "算法": "贝叶斯认知模型、脉冲神经网络(SNN)、注意力机制、强化学习认知架构",
        "program": "贝叶斯更新 $P(\\theta|D) \\propto P(D|\\theta)P(\\theta)$；SNN 膜电位 $\\tau \\frac{dv}{dt} = -(v - v_{rest}) + RI(t)$",
        "implementation": "神经信号采集设备(EEG/fNIRS)、认知实验平台(PsychoPy)、类脑芯片(TrueNorth/Loihi)、脑机接口外设",
        "computational_model": "脉冲神经网络模型 + 概率图模型 + 强化学习模型",
        "complexity": "SNN 仿真 $O(N \\cdot T)$（$N$ 神经元数，$T$ 时间步）；fMRI 解码 $O(V \\cdot d)$（$V$ 体素数）；贝叶斯推断 MCMC $O(K \\cdot n)$（$K$ 样本数）",
        "正确性": "模型拟合度（BIC/AIC）、神经解码交叉验证、行为实验复现",
        "references": "Griffiths et al. (2010) Probabilistic Models of Cognition; Dayan & Abbott (2001) Theoretical Neuroscience; Rao & Schoner (2022) Brain-Computer Interfaces"
    },
    "数字孪生": {
        "intent": "构建物理实体的实时数字镜像，支持预测性分析与优化决策",
        "specification": "输入：物理实体传感器数据 $\\{x_t\\}$、CAD/CFD 模型 $M_{phys}$；输出：状态估计 $\\hat{s}_t$、剩余寿命预测 $RUL$ 或优化策略 $\\pi^*$；约束：同步延迟 $\\leq \\delta$、模型保真度 $\\geq F_{min}$、数据刷新率 $\\geq f_{min}$",
        "algorithm": "物理信息神经网络(PINN)、卡尔曼滤波/粒子滤波、强化学习控制、有限元分析(FEA)",
        "program": "PINN 损失 $L = L_{data} + \\lambda L_{physics} = \\sum_i ||\\hat{u}(x_i) - u_i||^2 + \\lambda \\sum_j ||\\mathcal{N}[\\hat{u}](x_j)||^2$",
        "implementation": "IoT 边缘采集、数字线程(Digital Thread)平台、实时仿真引擎、AR/VR 可视化交互",
        "computational_model": "连续物理模型（PDE/ODE）+ 离散事件仿真 + 数据驱动模型（神经网络）",
        "complexity": "FEA 求解 $O(N^{1.5})$（$N$ 自由度）；粒子滤波 $O(M \\cdot d^2)$（$M$ 粒子数）；PINN 训练 $O(E \\cdot n)$（$E$ epoch，$n$ 数据点）",
        "正确性": "物理守恒定律验证、模型验证与确认(V&V)、数字孪生-物理实体偏差监控",
        "references": "Grieves & Vickers (2017) Digital Twin; Raissi et al. (2019) Physics-Informed Neural Networks; Lu et al. (2020) Digital Twin driven smart manufacturing"
    }
}

def get_domain_config(filename):
    """Match filename to domain config."""
    for key in DOMAINS:
        if key in filename:
            return DOMAINS[key]
    # Default fallback
    return {
        "intent": f"解决 {filename} 领域的核心计算问题",
        "specification": "输入：问题实例 $I$；输出：解 $S$；约束：时间/空间复杂度要求",
        "algorithm": "适用的核心算法范式",
        "program": "伪代码或实现框架",
        "implementation": "工程实现关键考量",
        "computational_model": "RAM / 分布式 / 量子模型",
        "complexity": "时间/空间复杂度分析",
        "correctness": "形式化验证或测试策略",
        "references": "领域权威文献（至少3条）"
    }

def main():
    base = Path("docs/12-应用领域")
    files = sorted(base.glob("*.md"))
    count = 0
    for f in files:
        name = f.name
        # Skip directories and case libraries
        if "案例库" in name or "案例研究" in name or "README" in name:
            continue
        content = f.read_text(encoding="utf-8")
        if "规约与模型在本领域的实例化" in content:
            continue
        config = get_domain_config(name)
        section = SPEC_TEMPLATE.format(**config)
        with open(f, "a", encoding="utf-8") as fh:
            fh.write("\n" + section)
        count += 1
        print(f"Appended to {name}")
    print(f"\nTotal files processed: {count}")

if __name__ == "__main__":
    main()
