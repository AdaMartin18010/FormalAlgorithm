-- Lean 4 列表反转性质证明示例
-- 对应 docs/03-形式化证明/05-证明助手实践.md

namespace ListReverse

-- 定义列表反转（标准库已有 reverse，这里用自定义版本教学）
inductive MyList (α : Type) where
  | nil : MyList α
  | cons : α → MyList α → MyList α

deriving Repr

def myAppend {α : Type} : MyList α → MyList α → MyList α
  | MyList.nil, ys => ys
  | MyList.cons x xs, ys => MyList.cons x (myAppend xs ys)

def myReverse {α : Type} : MyList α → MyList α
  | MyList.nil => MyList.nil
  | MyList.cons x xs => myAppend (myReverse xs) (MyList.cons x MyList.nil)

-- 辅助引理：nil 是 myAppend 的右单位元
theorem append_nil {α : Type} (xs : MyList α) : myAppend xs MyList.nil = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [myAppend]
    rw [ih]

-- 辅助引理：myAppend 满足结合律
theorem append_assoc {α : Type} (xs ys zs : MyList α) :
  myAppend (myAppend xs ys) zs = myAppend xs (myAppend ys zs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [myAppend]
    rw [ih]

-- 定理：reverse 保持 append 的分配律
-- 即 reverse (xs ++ ys) = reverse ys ++ reverse xs
theorem reverse_append_distrib {α : Type} (xs ys : MyList α) :
  myReverse (myAppend xs ys) = myAppend (myReverse ys) (myReverse xs) := by
  induction xs with
  | nil =>
    simp only [myReverse, myAppend]
    rw [append_nil]
  | cons x xs ih =>
    simp only [myReverse, myAppend]
    rw [ih]
    rw [append_assoc]

-- 定理：对合性质（reverse (reverse xs) = xs）
theorem reverse_involutive {α : Type} (xs : MyList α) :
  myReverse (myReverse xs) = xs := by
  induction xs with
  | nil =>
    simp only [myReverse]
  | cons x xs ih =>
    simp only [myReverse]
    rw [reverse_append_distrib]
    simp only [myReverse, myAppend]
    rw [ih]

-- 使用标准库 List 的等价的可运行证明示例
namespace StdList

theorem reverse_append_std {α : Type} (xs ys : List α) :
  (xs ++ ys).reverse = ys.reverse ++ xs.reverse := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

theorem reverse_reverse_std {α : Type} (xs : List α) :
  xs.reverse.reverse = xs := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

end StdList

end ListReverse
