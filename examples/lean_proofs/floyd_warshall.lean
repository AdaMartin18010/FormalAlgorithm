/-
  floyd_warshall.lean
  Floyd-Warshall 算法最短路径正确性的形式化证明骨架（Lean 4）

  证明目标：若图中不存在负权环，则算法终止后 dist[i][j] 等于从 i 到 j 的
  最短路径权重。
-/

-- 使用自然数索引顶点，权重为整数（允许负权）
abbrev Vertex := Nat
abbrev Weight := Int

-- 无穷大表示
def INF : Weight := 1000000000

-- 根据边列表初始化距离矩阵
def initialDist (n : Vertex) (edges : List (Vertex × Vertex × Weight))
    : Array (Array Weight) := Id.run do
  let mut d := (List.replicate n ((List.replicate n (0 : Weight)).toArray)).toArray
  for i in [0:n] do
    let mut row := d[i]!
    for j in [0:n] do
      row := row.set! j (if i == j then 0 else INF)
    d := d.set! i row
  for (u, v, w) in edges do
    if u < n && v < n then
      d := d.set! u ((d[u]!).set! v (min ((d[u]!)[v]!) w))
  return d

-- Floyd-Warshall 核心三层循环
def floydWarshall (n : Vertex) (dist : Array (Array Weight))
    : Array (Array Weight) := Id.run do
  let mut d := dist
  for k in [0:n] do
    for i in [0:n] do
      let dik := d[i]![k]!
      for j in [0:n] do
        let via := dik + d[k]![j]!
        if via < ((d[i]!)[j]!) then
          d := d.set! i ((d[i]!).set! j via)
  return d

-- 路径的归纳定义
inductive Path (adj : Vertex → Vertex → Option Weight) : Vertex → Vertex → Type where
  | nil {u : Vertex} : Path adj u u
  | cons {u v w : Vertex}
      (p : Path adj u v) (hw : adj v w ≠ none) : Path adj u w

-- 路径权重
def pathWeight (adj : Vertex → Vertex → Option Weight)
    : {u v : Vertex} → Path adj u v → Weight
  | _, _, .nil => 0
  | _, _, @Path.cons _ _ v w p _ =>
    pathWeight adj p + (adj v w).getD 0

-- 最短路径权重（占位定义，完整证明需引入 mathlib 的 infimum 工具）
noncomputable def shortestPathWeight
    (adj : Vertex → Vertex → Option Weight) (u v : Vertex) : Weight :=
  0

-- 循环不变式
def LoopInvariant (k : Vertex) (d : Array (Array Weight)) (n : Vertex) : Prop :=
  ∀ (i j : Vertex), i < n → j < n →
    ((d[i]!)[j]!) = shortestPathWeight
      (λ a b => if ((d[a]!)[b]!) < INF then some ((d[a]!)[b]!) else none) i j

-- 主定理骨架
theorem floyd_warshall_correctness
    (n : Vertex)
    (edges : List (Vertex × Vertex × Weight))
    (no_neg_cycle : ∀ (i : Vertex), i < n →
      ((floydWarshall n (initialDist n edges))[i]!)[i]! ≥ 0)
    : LoopInvariant n (floydWarshall n (initialDist n edges)) n := by
  /-
    完整证明思路：
    1. 对 k 进行数学归纳，证明循环不变式。
    2. 基例 k=0：不允许任何中间顶点，距离矩阵仅含直接边权重。
    3. 归纳步骤：假设对 k 成立，考虑允许使用顶点 k 的情况。
       新最短路径 = min(旧最短路径, 经过 k 的最短路径)。
       经过 k 的路径可拆分为 i→k 与 k→j，两段均只使用 {0,…,k-1} 作为中间顶点，
       其最优权重已由归纳假设给出。
    4. 终止时 k=n，允许所有顶点作为中间点，故矩阵存储全局最短路径。
    5. no_neg_cycle 保证不存在权重为负的环，从而最短路径是良定义的。
  -/
  sorry

-- 示例验证（使用 #eval! 以允许 sorry 公理）
#eval! floydWarshall 4 (initialDist 4 [(0,1,3),(0,3,7),(1,0,8),(1,2,2),(2,0,5),(2,3,1),(3,0,2)])
