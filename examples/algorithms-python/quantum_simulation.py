"""
quantum_simulation.py - 量子计算模拟
包含：量子门实现、量子电路、Grover搜索算法模拟

作者: FormalAlgorithm
日期: 2026-04-10
"""

import numpy as np
from typing import List, Tuple, Optional, Union, Callable
from abc import ABC, abstractmethod
import math


# ==================== 量子态和基本工具 ====================

class QState:
    """
    量子态类
    
    表示一个n量子比特的量子态，使用状态向量存储
    
    Attributes:
        n_qubits: 量子比特数量
        amplitudes: 复数振幅向量，长度为 2^n_qubits
    """
    
    def __init__(self, n_qubits: int, amplitudes: Optional[np.ndarray] = None):
        """
        初始化量子态
        
        Args:
            n_qubits: 量子比特数量
            amplitudes: 初始振幅，如果为None则初始化为|0...0>
        """
        self.n_qubits = n_qubits
        dim = 2 ** n_qubits
        
        if amplitudes is None:
            # 初始化为 |0...0>
            self.amplitudes = np.zeros(dim, dtype=complex)
            self.amplitudes[0] = 1.0
        else:
            if len(amplitudes) != dim:
                raise ValueError(f"振幅向量长度必须为 {dim}")
            self.amplitudes = amplitudes.astype(complex)
            self._normalize()
    
    def _normalize(self):
        """归一化量子态"""
        norm = np.sqrt(np.sum(np.abs(self.amplitudes) ** 2))
        if norm > 0:
            self.amplitudes /= norm
    
    def __repr__(self):
        """字符串表示"""
        terms = []
        for i, amp in enumerate(self.amplitudes):
            if np.abs(amp) > 1e-10:
                binary = format(i, f'0{self.n_qubits}b')
                terms.append(f"{amp:.4f}|{binary}>")
        return " + ".join(terms) if terms else "0"
    
    def probability(self, state: Optional[int] = None) -> Union[float, np.ndarray]:
        """
        计算测量概率
        
        Args:
            state: 如果指定，返回该基态的概率；否则返回所有基态概率
            
        Returns:
            概率或概率数组
        """
        probs = np.abs(self.amplitudes) ** 2
        if state is not None:
            return probs[state]
        return probs
    
    def measure(self) -> int:
        """
        模拟测量，返回测量的基态
        
        Returns:
            测量的基态索引（0到2^n_qubits-1）
        """
        probs = self.probability()
        return np.random.choice(len(probs), p=probs)
    
    def measure_qubit(self, qubit: int) -> Tuple[int, 'QState']:
        """
        测量单个量子比特
        
        Args:
            qubit: 要测量的量子比特索引
            
        Returns:
            (测量结果0或1, 坍缩后的量子态)
        """
        # 计算测量0和1的概率
        prob_0 = 0.0
        for i in range(len(self.amplitudes)):
            if not (i & (1 << (self.n_qubits - 1 - qubit))):
                prob_0 += np.abs(self.amplitudes[i]) ** 2
        
        # 随机测量
        result = 0 if np.random.random() < prob_0 else 1
        
        # 坍缩
        new_amplitudes = self.amplitudes.copy()
        for i in range(len(new_amplitudes)):
            bit = (i >> (self.n_qubits - 1 - qubit)) & 1
            if bit != result:
                new_amplitudes[i] = 0
        
        new_state = QState(self.n_qubits, new_amplitudes)
        return result, new_state
    
    def apply_gate(self, gate_matrix: np.ndarray, targets: List[int]) -> 'QState':
        """
        应用量子门
        
        Args:
            gate_matrix: 门矩阵
            targets: 目标量子比特索引列表
            
        Returns:
            新的量子态
        """
        # 构建完整的酉矩阵
        full_matrix = self._expand_gate(gate_matrix, targets)
        new_amplitudes = full_matrix @ self.amplitudes
        return QState(self.n_qubits, new_amplitudes)
    
    def _expand_gate(self, gate: np.ndarray, targets: List[int]) -> np.ndarray:
        """
        将门扩展到整个希尔伯特空间
        
        使用张量积将k量子比特门扩展到n量子比特空间
        """
        n = self.n_qubits
        k = len(targets)
        
        # 重新排列比特顺序使得目标比特连续
        # 这是一个简化实现，实际应使用更高效的算法
        dim = 2 ** n
        full_gate = np.eye(dim, dtype=complex)
        
        # 对每个基态应用门
        for i in range(dim):
            # 提取目标比特的状态
            target_bits = 0
            for t, target in enumerate(targets):
                bit = (i >> (n - 1 - target)) & 1
                target_bits |= bit << (k - 1 - t)
            
            # 对其他基态（目标比特相同的部分）应用门
            for j in range(2 ** k):
                new_target_bits = j
                # 构造新的状态索引
                new_i = i
                for t, target in enumerate(targets):
                    old_bit = (target_bits >> (k - 1 - t)) & 1
                    new_bit = (new_target_bits >> (k - 1 - t)) & 1
                    # 清除旧位，设置新位
                    mask = ~(1 << (n - 1 - target))
                    new_i = (new_i & mask) | (new_bit << (n - 1 - target))
                
                full_gate[new_i, i] = gate[new_target_bits, target_bits]
        
        return full_gate
    
    def tensor_product(self, other: 'QState') -> 'QState':
        """
        计算张量积 |self> ⊗ |other>
        
        Args:
            other: 另一个量子态
            
        Returns:
            复合量子态
        """
        new_amplitudes = np.kron(self.amplitudes, other.amplitudes)
        return QState(self.n_qubits + other.n_qubits, new_amplitudes)


# ==================== 量子门 ====================

class QuantumGate:
    """量子门工具类"""
    
    # 单量子比特门
    I = np.eye(2, dtype=complex)  # 恒等门
    
    X = np.array([[0, 1],          # Pauli-X (NOT)
                  [1, 0]], dtype=complex)
    
    Y = np.array([[0, -1j],        # Pauli-Y
                  [1j, 0]], dtype=complex)
    
    Z = np.array([[1, 0],          # Pauli-Z
                  [0, -1]], dtype=complex)
    
    H = np.array([[1, 1],          # Hadamard
                  [1, -1]], dtype=complex) / np.sqrt(2)
    
    S = np.array([[1, 0],          # Phase (S)
                  [0, 1j]], dtype=complex)
    
    T = np.array([[1, 0],          # T gate (π/8)
                  [0, np.exp(1j * np.pi / 4)]], dtype=complex)
    
    @staticmethod
    def RX(theta: float) -> np.ndarray:
        """X轴旋转门"""
        return np.array([[np.cos(theta/2), -1j*np.sin(theta/2)],
                         [-1j*np.sin(theta/2), np.cos(theta/2)]], dtype=complex)
    
    @staticmethod
    def RY(theta: float) -> np.ndarray:
        """Y轴旋转门"""
        return np.array([[np.cos(theta/2), -np.sin(theta/2)],
                         [np.sin(theta/2), np.cos(theta/2)]], dtype=complex)
    
    @staticmethod
    def RZ(theta: float) -> np.ndarray:
        """Z轴旋转门"""
        return np.array([[np.exp(-1j*theta/2), 0],
                         [0, np.exp(1j*theta/2)]], dtype=complex)
    
    @staticmethod
    def U(theta: float, phi: float, lam: float) -> np.ndarray:
        """通用单量子比特门"""
        return np.array([
            [np.cos(theta/2), -np.exp(1j*lam)*np.sin(theta/2)],
            [np.exp(1j*phi)*np.sin(theta/2), np.exp(1j*(phi+lam))*np.cos(theta/2)]
        ], dtype=complex)
    
    # 双量子比特门
    CNOT = np.array([[1, 0, 0, 0],   # 受控非门
                     [0, 1, 0, 0],
                     [0, 0, 0, 1],
                     [0, 0, 1, 0]], dtype=complex)
    
    SWAP = np.array([[1, 0, 0, 0],   # 交换门
                     [0, 0, 1, 0],
                     [0, 1, 0, 0],
                     [0, 0, 0, 1]], dtype=complex)
    
    CZ = np.array([[1, 0, 0, 0],     # 受控Z门
                   [0, 1, 0, 0],
                   [0, 0, 1, 0],
                   [0, 0, 0, -1]], dtype=complex)
    
    @staticmethod
    def CR(k: int) -> np.ndarray:
        """受控相位旋转门 R_k = diag(1, 1, 1, exp(2πi/2^k))"""
        return np.array([[1, 0, 0, 0],
                         [0, 1, 0, 0],
                         [0, 0, 1, 0],
                         [0, 0, 0, np.exp(2j * np.pi / (2**k))]], dtype=complex)
    
    @staticmethod
    def controlled(U: np.ndarray) -> np.ndarray:
        """
        构造受控门 CU
        
        Args:
            U: 单或双量子比特门
            
        Returns:
            受控版本的门
        """
        dim = U.shape[0]
        CU = np.eye(2 * dim, dtype=complex)
        CU[dim:, dim:] = U
        return CU


# ==================== 量子电路 ====================

class QuantumCircuit:
    """
    量子电路类
    
    用于构建和执行量子电路
    """
    
    def __init__(self, n_qubits: int):
        """
        初始化量子电路
        
        Args:
            n_qubits: 量子比特数量
        """
        self.n_qubits = n_qubits
        self.state = QState(n_qubits)
        self.operations = []  # 记录操作历史
        
    def reset(self):
        """重置电路状态"""
        self.state = QState(self.n_qubits)
        self.operations = []
        return self
    
    def apply(self, gate: np.ndarray, targets: Union[int, List[int]]):
        """
        应用量子门
        
        Args:
            gate: 门矩阵
            targets: 目标量子比特（单个或列表）
        """
        if isinstance(targets, int):
            targets = [targets]
        
        self.state = self.state.apply_gate(gate, targets)
        self.operations.append((gate, targets))
        return self
    
    def x(self, target: int):
        """Pauli-X门"""
        return self.apply(QuantumGate.X, [target])
    
    def y(self, target: int):
        """Pauli-Y门"""
        return self.apply(QuantumGate.Y, [target])
    
    def z(self, target: int):
        """Pauli-Z门"""
        return self.apply(QuantumGate.Z, [target])
    
    def h(self, target: int):
        """Hadamard门"""
        return self.apply(QuantumGate.H, [target])
    
    def s(self, target: int):
        """S门 (Phase)"""
        return self.apply(QuantumGate.S, [target])
    
    def t(self, target: int):
        """T门"""
        return self.apply(QuantumGate.T, [target])
    
    def rx(self, target: int, theta: float):
        """X轴旋转门"""
        return self.apply(QuantumGate.RX(theta), [target])
    
    def ry(self, target: int, theta: float):
        """Y轴旋转门"""
        return self.apply(QuantumGate.RY(theta), [target])
    
    def rz(self, target: int, theta: float):
        """Z轴旋转门"""
        return self.apply(QuantumGate.RZ(theta), [target])
    
    def cnot(self, control: int, target: int):
        """CNOT门"""
        return self.apply(QuantumGate.CNOT, [control, target])
    
    def swap(self, qubit1: int, qubit2: int):
        """SWAP门"""
        return self.apply(QuantumGate.SWAP, [qubit1, qubit2])
    
    def cz(self, control: int, target: int):
        """受控Z门"""
        return self.apply(QuantumGate.CZ, [control, target])
    
    def ccnot(self, control1: int, control2: int, target: int):
        """Toffoli门（受控受控非门）"""
        # Toffoli = CCNOT
        toffoli = np.eye(8, dtype=complex)
        toffoli[6, 6] = 0
        toffoli[6, 7] = 1
        toffoli[7, 6] = 1
        toffoli[7, 7] = 0
        return self.apply(toffoli, [control1, control2, target])
    
    def measure(self, shots: int = 1024) -> dict:
        """
        模拟多次测量
        
        Args:
            shots: 测量次数
            
        Returns:
            测量结果统计 {状态: 次数}
        """
        results = {}
        probs = self.state.probability()
        
        for _ in range(shots):
            outcome = np.random.choice(len(probs), p=probs)
            binary = format(outcome, f'0{self.n_qubits}b')
            results[binary] = results.get(binary, 0) + 1
        
        return results
    
    def measure_qubit(self, qubit: int) -> Tuple[int, 'QuantumCircuit']:
        """
        测量单个量子比特
        
        Returns:
            (测量结果, 新的电路)
        """
        result, new_state = self.state.measure_qubit(qubit)
        new_circuit = QuantumCircuit(self.n_qubits)
        new_circuit.state = new_state
        return result, new_circuit
    
    def get_statevector(self) -> np.ndarray:
        """获取当前状态向量"""
        return self.state.amplitudes.copy()
    
    def print_state(self, name: str = ""):
        """打印当前状态"""
        if name:
            print(f"\n{name}:")
        print(f"  |ψ> = {self.state}")
        print(f"  概率分布: {self.state.probability().round(4)}")
        return self


# ==================== Grover算法 ====================

class GroverAlgorithm:
    """
    Grover搜索算法模拟
    
    在未排序数据库中搜索目标元素，提供二次方加速
    
    经典复杂度: O(N)
    量子复杂度: O(√N)
    """
    
    def __init__(self, n_qubits: int, oracle_func: Callable[[int], bool]):
        """
        初始化Grover算法
        
        Args:
            n_qubits: 搜索空间为 2^n_qubits
            oracle_func: 预言机函数，对目标状态返回True
        """
        self.n_qubits = n_qubits
        self.N = 2 ** n_qubits
        self.oracle_func = oracle_func
        self.marked_states = [i for i in range(self.N) if oracle_func(i)]
        
    def _build_oracle(self) -> np.ndarray:
        """
        构建Grover预言机（相位翻转）
        
        对目标状态施加-1相位
        """
        oracle = np.eye(self.N, dtype=complex)
        for state in self.marked_states:
            oracle[state, state] = -1
        return oracle
    
    def _build_diffusion(self) -> np.ndarray:
        """
        构建扩散算子（振幅放大）
        
        关于均匀叠加态的反射
        """
        # H^{⊗n} (2|0><0| - I) H^{⊗n} = 2|s><s| - I
        # 其中 |s> 是均匀叠加态
        s = np.ones(self.N, dtype=complex) / np.sqrt(self.N)
        diffusion = 2 * np.outer(s, s.conj()) - np.eye(self.N, dtype=complex)
        return diffusion
    
    def run(self, iterations: Optional[int] = None) -> QuantumCircuit:
        """
        执行Grover算法
        
        Args:
            iterations: Grover迭代次数，如果为None则使用最优次数
            
        Returns:
            执行后的量子电路
        """
        M = len(self.marked_states)
        if M == 0:
            raise ValueError("没有标记状态")
        
        # 最优迭代次数
        if iterations is None:
            iterations = int(np.round(np.pi / 4 * np.sqrt(self.N / M)))
        
        print(f"Grover算法: N={self.N}, M={M}, 迭代次数={iterations}")
        
        # 创建电路
        circuit = QuantumCircuit(self.n_qubits)
        
        # 1. 初始化均匀叠加态
        for i in range(self.n_qubits):
            circuit.h(i)
        
        oracle = self._build_oracle()
        diffusion = self._build_diffusion()
        
        # 2. Grover迭代
        for _ in range(iterations):
            # 预言机（相位翻转）
            circuit.state = circuit.state.apply_gate(oracle, list(range(self.n_qubits)))
            
            # 扩散算子（振幅放大）
            circuit.state = circuit.state.apply_gate(diffusion, list(range(self.n_qubits)))
        
        return circuit
    
    def search(self, shots: int = 1024) -> dict:
        """
        执行搜索并返回结果
        
        Args:
            shots: 测量次数
            
        Returns:
            测量结果统计
        """
        circuit = self.run()
        results = circuit.measure(shots)
        
        # 排序显示
        sorted_results = dict(sorted(results.items(), key=lambda x: -x[1]))
        return sorted_results


# ==================== 量子傅里叶变换 (QFT) ====================

class QFT:
    """
    量子傅里叶变换模拟
    
    将计算基态 |j> 转换为傅里叶基态
    """
    
    @staticmethod
    def create_circuit(n_qubits: int, inverse: bool = False) -> List[Tuple]:
        """
        创建QFT电路的门序列
        
        Args:
            n_qubits: 量子比特数量
            inverse: 是否创建逆QFT
            
        Returns:
            门操作列表 [(gate, targets), ...]
        """
        operations = []
        
        for i in range(n_qubits):
            qubit = n_qubits - 1 - i  # 从最高位开始
            
            # Hadamard
            operations.append(('H', [qubit]))
            
            # 受控相位旋转
            for j in range(i + 1, n_qubits):
                control = n_qubits - 1 - j
                k = j - i + 1
                if inverse:
                    operations.append((f'CR{-k}', [control, qubit]))
                else:
                    operations.append((f'CR{k}', [control, qubit]))
        
        # 交换顺序（QFT输出是逆序的）
        for i in range(n_qubits // 2):
            operations.append(('SWAP', [i, n_qubits - 1 - i]))
        
        return operations
    
    @staticmethod
    def apply(circuit: QuantumCircuit, inverse: bool = False):
        """
        在电路上应用QFT
        
        Args:
            circuit: 量子电路
            inverse: 是否应用逆QFT
        """
        n = circuit.n_qubits
        
        for i in range(n):
            qubit = n - 1 - i
            circuit.h(qubit)
            
            for j in range(i + 1, n):
                control = n - 1 - j
                k = j - i + 1
                angle = 2 * np.pi / (2 ** k)
                if inverse:
                    angle = -angle
                # 使用受控旋转
                cr_gate = np.array([[1, 0, 0, 0],
                                   [0, 1, 0, 0],
                                   [0, 0, 1, 0],
                                   [0, 0, 0, np.exp(1j * angle)]], dtype=complex)
                circuit.apply(cr_gate, [control, qubit])
        
        # 交换
        for i in range(n // 2):
            circuit.swap(i, n - 1 - i)
        
        return circuit


# ==================== 贝尔态和GHZ态 ====================

def create_bell_state(state_type: str = 'phi+') -> QuantumCircuit:
    """
    创建贝尔态
    
    |Φ+> = (|00> + |11>)/√2
    |Φ-> = (|00> - |11>)/√2
    |Ψ+> = (|01> + |10>)/√2
    |Ψ-> = (|01> - |10>)/√2
    """
    circuit = QuantumCircuit(2)
    
    if state_type in ['phi+', 'phi-']:
        circuit.h(0)
        circuit.cnot(0, 1)
        if state_type == 'phi-':
            circuit.z(0)
    elif state_type in ['psi+', 'psi-']:
        circuit.h(0)
        circuit.x(1)
        circuit.cnot(0, 1)
        if state_type == 'psi-':
            circuit.z(0)
    
    return circuit


def create_ghz_state(n_qubits: int) -> QuantumCircuit:
    """
    创建GHZ态: (|00...0> + |11...1>)/√2
    
    最大的量子纠缠态
    """
    circuit = QuantumCircuit(n_qubits)
    circuit.h(0)
    
    for i in range(n_qubits - 1):
        circuit.cnot(i, i + 1)
    
    return circuit


# ==================== 测试示例 ====================

def test_basic_gates():
    """测试基本量子门"""
    print("\n" + "="*60)
    print("基本量子门测试")
    print("="*60)
    
    # 单量子比特门
    print("\n--- 单量子比特门 ---")
    circuit = QuantumCircuit(1)
    circuit.print_state("初始状态 |0>")
    
    circuit.h(0)
    circuit.print_state("H门后 (|+>)")
    
    circuit.reset().x(0)
    circuit.print_state("X门后 |1>")
    
    circuit.h(0)
    circuit.print_state("H门后 (|->)")
    
    # 双量子比特门
    print("\n--- 双量子比特门 ---")
    circuit2 = QuantumCircuit(2)
    circuit2.h(0).cnot(0, 1)
    circuit2.print_state("Bell态 (|00>+|11>)/√2")
    
    # 测量统计
    print("\n测量统计 (1024次):")
    results = circuit2.measure(1024)
    for state, count in sorted(results.items()):
        print(f"  |{state}>: {count} ({count/10.24:.1f}%)")


def test_grover_algorithm():
    """测试Grover算法"""
    print("\n" + "="*60)
    print("Grover搜索算法测试")
    print("="*60)
    
    # 测试1: 在8个元素中搜索1个目标
    print("\n--- 搜索空间: 8 (3量子比特) ---")
    target = 5  # 二进制 101
    oracle = lambda x: x == target
    
    grover = GroverAlgorithm(n_qubits=3, oracle_func=oracle)
    results = grover.search(shots=1024)
    
    print("测量结果:")
    for state, count in list(results.items())[:5]:
        marker = " <-- 目标!" if int(state, 2) == target else ""
        print(f"  |{state}>: {count} ({count/10.24:.1f}%){marker}")
    
    # 测试2: 在16个元素中搜索多个目标
    print("\n--- 搜索空间: 16 (4量子比特), 多个目标 ---")
    targets = [3, 10]  # 多个目标
    oracle2 = lambda x: x in targets
    
    grover2 = GroverAlgorithm(n_qubits=4, oracle_func=oracle2)
    results2 = grover2.search(shots=2048)
    
    print("测量结果:")
    for state, count in list(results2.items())[:6]:
        state_int = int(state, 2)
        marker = " <-- 目标!" if state_int in targets else ""
        print(f"  |{state}>({state_int}): {count} ({count/20.48:.1f}%){marker}")


def test_qft():
    """测试量子傅里叶变换"""
    print("\n" + "="*60)
    print("量子傅里叶变换测试")
    print("="*60)
    
    # 3量子比特QFT
    n = 3
    print(f"\n--- {n}量子比特 QFT ---")
    
    # 输入状态 |001>
    circuit = QuantumCircuit(n)
    circuit.x(n-1)  # 设置最低位为1
    print(f"输入: |{format(1, f'0{n}b')}>")
    
    # 应用QFT
    QFT.apply(circuit)
    print(f"QFT后状态:")
    print(f"  |ψ> = {circuit.state}")
    
    # 逆QFT
    QFT.apply(circuit, inverse=True)
    print(f"逆QFT后（应恢复原状态）:")
    print(f"  |ψ> = {circuit.state}")


def test_entanglement():
    """测试量子纠缠"""
    print("\n" + "="*60)
    print("量子纠缠测试")
    print("="*60)
    
    # 贝尔态
    print("\n--- 贝尔态 ---")
    for name, stype in [("|Φ+>", "phi+"), ("|Φ->", "phi-"), 
                        ("|Ψ+>", "psi+"), ("|Ψ->", "psi-")]:
        circuit = create_bell_state(stype)
        print(f"{name}: {circuit.state}")
    
    # GHZ态
    print("\n--- GHZ态 ---")
    for n in [3, 4]:
        ghz = create_ghz_state(n)
        print(f"{n}量子比特 GHZ: {ghz.state}")
    
    # 验证纠缠：测量一个量子比特会影响另一个
    print("\n--- 贝尔态测量测试 ---")
    bell = create_bell_state("phi+")
    
    # 多次测量统计
    stats = {'00': 0, '01': 0, '10': 0, '11': 0}
    for _ in range(1000):
        result = bell.measure()
        binary = format(result, '02b')
        stats[binary] += 1
    
    print("贝尔态测量统计 (1000次):")
    for state, count in stats.items():
        print(f"  |{state}>: {count} ({count/10:.1f}%)")
    print("  (注意: |01> 和 |10> 的概率应接近0，证明纠缠)")


def test_quantum_teleportation():
    """测试量子隐形传态协议"""
    print("\n" + "="*60)
    print("量子隐形传态模拟")
    print("="*60)
    
    # 量子隐形传态需要3个量子比特:
    # 0: 要传送的未知态 |ψ>
    # 1, 2: 贝尔对 (Alice和Bob共享)
    
    # 创建要传送的态 |ψ> = a|0> + b|1>
    # 我们选择 |ψ> = (|0> + |1>)/√2
    
    circuit = QuantumCircuit(3)
    
    # 步骤1: 创建贝尔对 (qubit 1和2)
    circuit.h(1).cnot(1, 2)
    print("创建贝尔对后:")
    print(f"  |ψ> = {circuit.state}")
    
    # 步骤2: 准备要传送的态 (在qubit 0上)
    # 例如 |ψ> = cos(π/8)|0> + sin(π/8)|1>
    theta = np.pi / 4
    circuit.ry(0, theta)
    print(f"\n准备传送态 (θ={theta:.4f}):")
    print(f"  |ψ> = {circuit.state}")
    
    # 步骤3: Alice的Bell测量
    circuit.cnot(0, 1).h(0)
    print(f"\nBell测量后:")
    print(f"  |ψ> = {circuit.state}")
    
    # 步骤4: 经典通信和Bob的修正 (模拟)
    # 实际中根据测量结果进行不同操作
    print("\n(经典通信和修正操作...)")
    print("Bob根据Alice的测量结果应用相应的门操作")
    print("最终Bob的量子比特状态应与原状态一致")


if __name__ == "__main__":
    np.random.seed(42)
    
    print("="*60)
    print("        量子计算模拟测试")
    print("="*60)
    
    test_basic_gates()
    test_grover_algorithm()
    test_qft()
    test_entanglement()
    test_quantum_teleportation()
    
    print("\n" + "="*60)
    print("所有量子模拟测试完成!")
    print("="*60)
