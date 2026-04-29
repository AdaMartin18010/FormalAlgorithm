"""
ml_algorithms.py - 基础机器学习算法实现
包含：线性回归、K-Means聚类、决策树

作者: FormalAlgorithm
日期: 2026-04-10
"""

import numpy as np
from typing import List, Tuple, Optional, Union
from collections import Counter
import random


# ==================== 线性回归 (Linear Regression) ====================

class LinearRegression:
    """
    线性回归模型
    
    使用正规方程或梯度下降法求解
    
    Attributes:
        weights: 权重向量
        bias: 偏置项
        method: 求解方法 ('normal' 或 'gradient')
    """
    
    def __init__(self, method: str = 'normal', learning_rate: float = 0.01, 
                 max_iter: int = 1000, tolerance: float = 1e-6):
        """
        初始化线性回归模型
        
        Args:
            method: 求解方法，'normal' 使用正规方程，'gradient' 使用梯度下降
            learning_rate: 梯度下降学习率
            max_iter: 最大迭代次数
            tolerance: 收敛阈值
        """
        self.method = method
        self.learning_rate = learning_rate
        self.max_iter = max_iter
        self.tolerance = tolerance
        self.weights = None
        self.bias = None
        self.cost_history = []
        
    def fit(self, X: np.ndarray, y: np.ndarray) -> 'LinearRegression':
        """
        训练模型
        
        Args:
            X: 特征矩阵，shape (n_samples, n_features)
            y: 目标向量，shape (n_samples,)
            
        Returns:
            self
        """
        n_samples, n_features = X.shape
        
        if self.method == 'normal':
            # 正规方程法: w = (X^T X)^(-1) X^T y
            X_b = np.c_[np.ones((n_samples, 1)), X]  # 添加偏置列
            try:
                theta = np.linalg.inv(X_b.T @ X_b) @ X_b.T @ y
                self.bias = theta[0]
                self.weights = theta[1:]
            except np.linalg.LinAlgError:
                # 使用伪逆处理奇异矩阵
                theta = np.linalg.pinv(X_b.T @ X_b) @ X_b.T @ y
                self.bias = theta[0]
                self.weights = theta[1:]
                
        elif self.method == 'gradient':
            # 梯度下降法
            self.weights = np.zeros(n_features)
            self.bias = 0
            
            for i in range(self.max_iter):
                # 预测
                y_pred = self.predict(X)
                
                # 计算梯度
                dw = (1 / n_samples) * (X.T @ (y_pred - y))
                db = (1 / n_samples) * np.sum(y_pred - y)
                
                # 更新参数
                self.weights -= self.learning_rate * dw
                self.bias -= self.learning_rate * db
                
                # 记录损失
                cost = self._compute_cost(X, y)
                self.cost_history.append(cost)
                
                # 检查收敛
                if i > 0 and abs(self.cost_history[-2] - cost) < self.tolerance:
                    break
        
        return self
    
    def predict(self, X: np.ndarray) -> np.ndarray:
        """预测"""
        return X @ self.weights + self.bias
    
    def _compute_cost(self, X: np.ndarray, y: np.ndarray) -> float:
        """计算均方误差损失"""
        n_samples = len(y)
        y_pred = self.predict(X)
        return (1 / (2 * n_samples)) * np.sum((y_pred - y) ** 2)
    
    def score(self, X: np.ndarray, y: np.ndarray) -> float:
        """
        计算R²分数
        
        Returns:
            R² score，范围(-∞, 1]，越接近1越好
        """
        y_pred = self.predict(X)
        ss_res = np.sum((y - y_pred) ** 2)
        ss_tot = np.sum((y - np.mean(y)) ** 2)
        return 1 - (ss_res / ss_tot)


class RidgeRegression(LinearRegression):
    """
    岭回归（L2正则化线性回归）
    
    用于处理多重共线性问题，防止过拟合
    """
    
    def __init__(self, alpha: float = 1.0, **kwargs):
        """
        Args:
            alpha: 正则化强度，越大正则化越强
        """
        super().__init__(**kwargs)
        self.alpha = alpha
        
    def fit(self, X: np.ndarray, y: np.ndarray) -> 'RidgeRegression':
        """训练岭回归模型"""
        n_samples, n_features = X.shape
        
        # 正规方程: w = (X^T X + αI)^(-1) X^T y
        X_b = np.c_[np.ones((n_samples, 1)), X]
        I = np.eye(n_features + 1)
        I[0, 0] = 0  # 不对偏置项正则化
        
        theta = np.linalg.inv(X_b.T @ X_b + self.alpha * I) @ X_b.T @ y
        self.bias = theta[0]
        self.weights = theta[1:]
        
        return self


# ==================== K-Means 聚类 ====================

class KMeans:
    """
    K-Means聚类算法
    
    将数据划分为K个簇，最小化簇内平方和
    
    Attributes:
        n_clusters: 聚类数量
        max_iter: 最大迭代次数
        tol: 收敛阈值
        centroids: 簇中心
        labels_: 每个样本的簇标签
        inertia_: 簇内平方和
    """
    
    def __init__(self, n_clusters: int = 3, max_iter: int = 300, 
                 tol: float = 1e-4, random_state: Optional[int] = None):
        """
        初始化K-Means
        
        Args:
            n_clusters: 聚类数量K
            max_iter: 最大迭代次数
            tol: 收敛阈值
            random_state: 随机种子
        """
        self.n_clusters = n_clusters
        self.max_iter = max_iter
        self.tol = tol
        self.random_state = random_state
        self.centroids = None
        self.labels_ = None
        self.inertia_ = None
        
    def fit(self, X: np.ndarray) -> 'KMeans':
        """
        训练K-Means模型
        
        Args:
            X: 特征矩阵，shape (n_samples, n_features)
            
        Returns:
            self
        """
        if self.random_state:
            np.random.seed(self.random_state)
            
        n_samples, n_features = X.shape
        
        # 随机初始化聚类中心
        idx = np.random.choice(n_samples, self.n_clusters, replace=False)
        self.centroids = X[idx].copy()
        
        for _ in range(self.max_iter):
            # 分配步骤：将每个样本分配到最近的中心
            distances = self._compute_distances(X)
            self.labels_ = np.argmin(distances, axis=1)
            
            # 更新步骤：重新计算中心
            new_centroids = np.array([X[self.labels_ == k].mean(axis=0) 
                                      for k in range(self.n_clusters)])
            
            # 检查收敛
            if np.all(np.abs(new_centroids - self.centroids) <= self.tol):
                break
                
            self.centroids = new_centroids
        
        # 计算最终inertia
        self.inertia_ = self._compute_inertia(X)
        
        return self
    
    def predict(self, X: np.ndarray) -> np.ndarray:
        """预测样本所属簇"""
        distances = self._compute_distances(X)
        return np.argmin(distances, axis=1)
    
    def fit_predict(self, X: np.ndarray) -> np.ndarray:
        """训练并预测"""
        self.fit(X)
        return self.labels_
    
    def _compute_distances(self, X: np.ndarray) -> np.ndarray:
        """计算每个样本到每个中心的距离"""
        distances = np.zeros((len(X), self.n_clusters))
        for k in range(self.n_clusters):
            distances[:, k] = np.linalg.norm(X - self.centroids[k], axis=1)
        return distances
    
    def _compute_inertia(self, X: np.ndarray) -> float:
        """计算簇内平方和"""
        distances = self._compute_distances(X)
        return np.sum(np.min(distances, axis=1) ** 2)
    
    def transform(self, X: np.ndarray) -> np.ndarray:
        """
        将样本转换到簇中心距离空间
        
        Returns:
            每个样本到各个中心的距离，shape (n_samples, n_clusters)
        """
        return self._compute_distances(X)


class KMeansPlusPlus(KMeans):
    """
    K-Means++ 初始化版本的K-Means
    
    使用K-Means++算法初始化聚类中心，通常能得到更好的聚类结果
    """
    
    def _init_centroids(self, X: np.ndarray):
        """K-Means++初始化"""
        n_samples, n_features = X.shape
        centroids = np.zeros((self.n_clusters, n_features))
        
        # 随机选择第一个中心
        centroids[0] = X[np.random.choice(n_samples)]
        
        for k in range(1, self.n_clusters):
            # 计算每个样本到最近中心的距离平方
            distances = np.zeros(n_samples)
            for i in range(n_samples):
                min_dist = float('inf')
                for j in range(k):
                    dist = np.sum((X[i] - centroids[j]) ** 2)
                    if dist < min_dist:
                        min_dist = dist
                distances[i] = min_dist
            
            # 按概率选择下一个中心
            probabilities = distances / distances.sum()
            centroids[k] = X[np.random.choice(n_samples, p=probabilities)]
        
        return centroids
    
    def fit(self, X: np.ndarray) -> 'KMeansPlusPlus':
        """训练K-Means++模型"""
        if self.random_state:
            np.random.seed(self.random_state)
            
        n_samples, n_features = X.shape
        
        # K-Means++初始化
        self.centroids = self._init_centroids(X)
        
        for _ in range(self.max_iter):
            distances = self._compute_distances(X)
            self.labels_ = np.argmin(distances, axis=1)
            
            new_centroids = np.array([X[self.labels_ == k].mean(axis=0) 
                                      for k in range(self.n_clusters)])
            
            if np.all(np.abs(new_centroids - self.centroids) <= self.tol):
                break
                
            self.centroids = new_centroids
        
        self.inertia_ = self._compute_inertia(X)
        
        return self


# ==================== 决策树 (Decision Tree) ====================

class DecisionTreeClassifier:
    """
    决策树分类器
    
    使用CART算法（基尼指数）或信息增益进行分裂
    
    Attributes:
        max_depth: 最大深度
        min_samples_split: 内部节点再划分所需最小样本数
        min_samples_leaf: 叶子节点最小样本数
        criterion: 分裂标准 ('gini' 或 'entropy')
    """
    
    class Node:
        """决策树节点"""
        def __init__(self):
            self.feature = None      # 分裂特征索引
            self.threshold = None    # 分裂阈值
            self.left = None         # 左子树
            self.right = None        # 右子树
            self.value = None        # 叶子节点的类别
            self.impurity = None     # 节点不纯度
            self.n_samples = 0       # 样本数
            
    def __init__(self, max_depth: int = 10, min_samples_split: int = 2,
                 min_samples_leaf: int = 1, criterion: str = 'gini'):
        """
        初始化决策树
        
        Args:
            max_depth: 树的最大深度
            min_samples_split: 节点分裂所需最小样本数
            min_samples_leaf: 叶子节点最小样本数
            criterion: 分裂标准，'gini'或'entropy'
        """
        self.max_depth = max_depth
        self.min_samples_split = min_samples_split
        self.min_samples_leaf = min_samples_leaf
        self.criterion = criterion
        self.root = None
        self.n_classes = None
        self.classes = None
        self.feature_importances_ = None
        
    def fit(self, X: np.ndarray, y: np.ndarray) -> 'DecisionTreeClassifier':
        """
        训练决策树
        
        Args:
            X: 特征矩阵，shape (n_samples, n_features)
            y: 标签向量，shape (n_samples,)
            
        Returns:
            self
        """
        self.classes = np.unique(y)
        self.n_classes = len(self.classes)
        self.feature_importances_ = np.zeros(X.shape[1])
        
        self.root = self._grow_tree(X, y, depth=0)
        
        # 归一化特征重要性
        if np.sum(self.feature_importances_) > 0:
            self.feature_importances_ /= np.sum(self.feature_importances_)
        
        return self
    
    def _grow_tree(self, X: np.ndarray, y: np.ndarray, depth: int) -> 'DecisionTreeClassifier.Node':
        """递归构建决策树"""
        node = self.Node()
        node.n_samples = len(y)
        
        # 统计类别
        class_counts = Counter(y)
        node.value = max(class_counts, key=class_counts.get)
        
        # 计算不纯度
        if self.criterion == 'gini':
            node.impurity = self._gini(y)
        else:
            node.impurity = self._entropy(y)
        
        # 停止条件
        if (depth >= self.max_depth or 
            len(y) < self.min_samples_split or 
            len(class_counts) == 1):
            return node
        
        # 寻找最佳分裂
        best_gain = -1
        best_feature = None
        best_threshold = None
        
        for feature in range(X.shape[1]):
            thresholds = np.unique(X[:, feature])
            for threshold in thresholds:
                left_mask = X[:, feature] <= threshold
                right_mask = ~left_mask
                
                if (np.sum(left_mask) < self.min_samples_leaf or 
                    np.sum(right_mask) < self.min_samples_leaf):
                    continue
                
                gain = self._information_gain(y, left_mask, right_mask)
                
                if gain > best_gain:
                    best_gain = gain
                    best_feature = feature
                    best_threshold = threshold
        
        if best_feature is None:
            return node
        
        # 记录特征重要性
        self.feature_importances_[best_feature] += best_gain * len(y)
        
        # 分裂
        node.feature = best_feature
        node.threshold = best_threshold
        
        left_mask = X[:, best_feature] <= best_threshold
        right_mask = ~left_mask
        
        node.left = self._grow_tree(X[left_mask], y[left_mask], depth + 1)
        node.right = self._grow_tree(X[right_mask], y[right_mask], depth + 1)
        
        return node
    
    def _gini(self, y: np.ndarray) -> float:
        """计算基尼指数"""
        _, counts = np.unique(y, return_counts=True)
        probs = counts / len(y)
        return 1 - np.sum(probs ** 2)
    
    def _entropy(self, y: np.ndarray) -> float:
        """计算信息熵"""
        _, counts = np.unique(y, return_counts=True)
        probs = counts / len(y)
        return -np.sum(probs * np.log2(probs + 1e-10))
    
    def _information_gain(self, y: np.ndarray, left_mask: np.ndarray, 
                          right_mask: np.ndarray) -> float:
        """计算信息增益"""
        parent_impurity = self._gini(y) if self.criterion == 'gini' else self._entropy(y)
        
        n = len(y)
        n_left, n_right = np.sum(left_mask), np.sum(right_mask)
        
        if self.criterion == 'gini':
            left_impurity = self._gini(y[left_mask])
            right_impurity = self._gini(y[right_mask])
        else:
            left_impurity = self._entropy(y[left_mask])
            right_impurity = self._entropy(y[right_mask])
        
        weighted_impurity = (n_left / n) * left_impurity + (n_right / n) * right_impurity
        
        return parent_impurity - weighted_impurity
    
    def predict(self, X: np.ndarray) -> np.ndarray:
        """预测类别"""
        return np.array([self._predict_single(x) for x in X])
    
    def _predict_single(self, x: np.ndarray):
        """预测单个样本"""
        node = self.root
        while node.left is not None:
            if x[node.feature] <= node.threshold:
                node = node.left
            else:
                node = node.right
        return node.value
    
    def predict_proba(self, X: np.ndarray) -> np.ndarray:
        """预测概率（简化版，返回one-hot）"""
        predictions = self.predict(X)
        probs = np.zeros((len(X), self.n_classes))
        for i, pred in enumerate(predictions):
            class_idx = np.where(self.classes == pred)[0][0]
            probs[i, class_idx] = 1.0
        return probs
    
    def score(self, X: np.ndarray, y: np.ndarray) -> float:
        """计算准确率"""
        predictions = self.predict(X)
        return np.mean(predictions == y)


class RandomForestClassifier:
    """
    随机森林分类器
    
    集成多个决策树进行投票
    """
    
    def __init__(self, n_estimators: int = 10, max_depth: int = 10,
                 min_samples_split: int = 2, max_features: str = 'sqrt',
                 random_state: Optional[int] = None):
        """
        初始化随机森林
        
        Args:
            n_estimators: 树的数量
            max_depth: 单棵树最大深度
            min_samples_split: 节点分裂最小样本数
            max_features: 每次分裂考虑的特征数
            random_state: 随机种子
        """
        self.n_estimators = n_estimators
        self.max_depth = max_depth
        self.min_samples_split = min_samples_split
        self.max_features = max_features
        self.random_state = random_state
        self.trees = []
        self.classes = None
        
    def fit(self, X: np.ndarray, y: np.ndarray) -> 'RandomForestClassifier':
        """训练随机森林"""
        if self.random_state:
            np.random.seed(self.random_state)
            random.seed(self.random_state)
            
        self.classes = np.unique(y)
        n_samples, n_features = X.shape
        
        # 确定max_features
        if self.max_features == 'sqrt':
            max_features = int(np.sqrt(n_features))
        elif self.max_features == 'log2':
            max_features = int(np.log2(n_features))
        elif isinstance(self.max_features, int):
            max_features = self.max_features
        else:
            max_features = n_features
        
        self.trees = []
        for _ in range(self.n_estimators):
            # Bootstrap采样
            indices = np.random.choice(n_samples, n_samples, replace=True)
            X_bootstrap = X[indices]
            y_bootstrap = y[indices]
            
            # 训练决策树
            tree = DecisionTreeClassifier(
                max_depth=self.max_depth,
                min_samples_split=self.min_samples_split
            )
            
            # 特征子采样（在每次分裂时进行，这里简化处理）
            feature_indices = np.random.choice(n_features, max_features, replace=False)
            tree.fit(X_bootstrap[:, feature_indices], y_bootstrap)
            tree.feature_indices = feature_indices  # 保存使用的特征
            
            self.trees.append(tree)
        
        return self
    
    def predict(self, X: np.ndarray) -> np.ndarray:
        """预测"""
        # 收集所有树的预测
        predictions = np.array([tree.predict(X[:, tree.feature_indices]) 
                                for tree in self.trees])
        
        # 投票
        final_predictions = []
        for i in range(X.shape[0]):
            votes = Counter(predictions[:, i])
            final_predictions.append(votes.most_common(1)[0][0])
        
        return np.array(final_predictions)
    
    def score(self, X: np.ndarray, y: np.ndarray) -> float:
        """计算准确率"""
        predictions = self.predict(X)
        return np.mean(predictions == y)


# ==================== 测试示例 ====================

def test_linear_regression():
    """测试线性回归"""
    print("\n" + "="*50)
    print("线性回归测试")
    print("="*50)
    
    # 生成测试数据: y = 2x + 1 + noise
    np.random.seed(42)
    X = np.random.rand(100, 1) * 10
    y = 2 * X.flatten() + 1 + np.random.randn(100) * 0.5
    
    # 训练模型
    model = LinearRegression(method='gradient', learning_rate=0.01, max_iter=1000)
    model.fit(X, y)
    
    print(f"真实参数: 权重=2.0, 偏置=1.0")
    print(f"估计参数: 权重={model.weights[0]:.4f}, 偏置={model.bias:.4f}")
    print(f"R² Score: {model.score(X, y):.4f}")
    
    # 预测
    X_test = np.array([[5.0], [7.0]])
    predictions = model.predict(X_test)
    print(f"预测: X={X_test.flatten()}, y={predictions}")
    
    # 岭回归测试
    print("\n--- 岭回归测试 ---")
    ridge = RidgeRegression(alpha=0.1)
    ridge.fit(X, y)
    print(f"岭回归参数: 权重={ridge.weights[0]:.4f}, 偏置={ridge.bias:.4f}")


def test_kmeans():
    """测试K-Means"""
    print("\n" + "="*50)
    print("K-Means聚类测试")
    print("="*50)
    
    # 生成测试数据（3个簇）
    np.random.seed(42)
    
    # 簇1
    cluster1 = np.random.randn(50, 2) + np.array([0, 0])
    # 簇2
    cluster2 = np.random.randn(50, 2) + np.array([5, 5])
    # 簇3
    cluster3 = np.random.randn(50, 2) + np.array([10, 0])
    
    X = np.vstack([cluster1, cluster2, cluster3])
    
    # 训练K-Means
    kmeans = KMeans(n_clusters=3, random_state=42)
    labels = kmeans.fit_predict(X)
    
    print(f"聚类中心:\n{kmeans.centroids}")
    print(f"簇内平方和 (Inertia): {kmeans.inertia_:.4f}")
    
    # 统计每个簇的样本数
    for k in range(3):
        count = np.sum(labels == k)
        print(f"簇 {k}: {count} 个样本")
    
    # K-Means++ 测试
    print("\n--- K-Means++ 测试 ---")
    kmeans_pp = KMeansPlusPlus(n_clusters=3, random_state=42)
    kmeans_pp.fit(X)
    print(f"K-Means++ Inertia: {kmeans_pp.inertia_:.4f}")


def test_decision_tree():
    """测试决策树"""
    print("\n" + "="*50)
    print("决策树分类测试")
    print("="*50)
    
    # 生成测试数据（XOR问题）
    np.random.seed(42)
    
    X = np.array([
        [0, 0],
        [0, 1],
        [1, 0],
        [1, 1],
        [0.1, 0.1],
        [0.1, 0.9],
        [0.9, 0.1],
        [0.9, 0.9]
    ])
    y = np.array([0, 1, 1, 0, 0, 1, 1, 0])  # XOR
    
    # 训练决策树
    dt = DecisionTreeClassifier(max_depth=3, criterion='gini')
    dt.fit(X, y)
    
    print(f"训练准确率: {dt.score(X, y):.4f}")
    print(f"特征重要性: {dt.feature_importances_}")
    
    # 预测
    X_test = np.array([[0.2, 0.2], [0.8, 0.8], [0.2, 0.8]])
    predictions = dt.predict(X_test)
    print(f"预测: X={X_test.tolist()}, y={predictions}")
    
    # 使用熵的决策树
    print("\n--- 使用信息熵 ---")
    dt_entropy = DecisionTreeClassifier(max_depth=3, criterion='entropy')
    dt_entropy.fit(X, y)
    print(f"熵决策树准确率: {dt_entropy.score(X, y):.4f}")


def test_random_forest():
    """测试随机森林"""
    print("\n" + "="*50)
    print("随机森林分类测试")
    print("="*50)
    
    # 生成更复杂的测试数据
    np.random.seed(42)
    
    # 类别0: 中心在(0,0)
    X0 = np.random.randn(50, 2) + np.array([0, 0])
    y0 = np.zeros(50)
    
    # 类别1: 中心在(3,3)
    X1 = np.random.randn(50, 2) + np.array([3, 3])
    y1 = np.ones(50)
    
    X = np.vstack([X0, X1])
    y = np.hstack([y0, y1])
    
    # 训练随机森林
    rf = RandomForestClassifier(n_estimators=10, max_depth=5, random_state=42)
    rf.fit(X, y)
    
    print(f"训练准确率: {rf.score(X, y):.4f}")
    print(f"森林中树的数量: {len(rf.trees)}")
    
    # 预测
    X_test = np.array([[0.5, 0.5], [3.5, 3.5]])
    predictions = rf.predict(X_test)
    print(f"预测: X={X_test.tolist()}, y={predictions}")


if __name__ == "__main__":
    print("=================== 机器学习算法测试 ===================")
    
    test_linear_regression()
    test_kmeans()
    test_decision_tree()
    test_random_forest()
    
    print("\n" + "="*50)
    print("所有测试完成!")
    print("="*50)
