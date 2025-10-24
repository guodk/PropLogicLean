import Mathlib
import PropLogic.Theory.Base
import PropLogic.Theory.Syntax
open PropForm

-- 为简化证明，定义空上下文的推导
def proves (p : PropForm) : Prop := ∅ ⊢ p
notation:45 " ⊢ " p => proves p

-- 定义各个公理作为谓词
def AL1 (P : PropForm → Prop) : Prop :=
  ∀ p q, P (p ⟶ (q ⟶ p))

def AL2 (P : PropForm → Prop) : Prop :=
  ∀ p q r, P ((p ⟶ (q ⟶ r)) ⟶ ((p ⟶ q) ⟶ (p ⟶ r)))

def AL3 (P : PropForm → Prop) : Prop :=
  ∀ p q, P ((⇁ p ⟶ (⇁ q)) ⟶ (q ⟶ p))

def MP_rule (P : PropForm → Prop) : Prop :=
  ∀ p q, P (p ⟶ q) → P p → P q

-- 不含L1的子系统
inductive DeduceNoL1 : Set PropForm → PropForm → Prop
  | L0 : ∀ Γ p, p ∈ Γ → DeduceNoL1 Γ p
  | L2 : ∀ Γ p q r, DeduceNoL1 Γ ((p ⟶ (q ⟶ r)) ⟶ ((p ⟶ q) ⟶ (p ⟶ r)))
  | L3 : ∀ Γ p q, DeduceNoL1 Γ ((⇁ p ⟶ (⇁ q)) ⟶ (q ⟶ p))
  | MP : ∀ Γ p q, DeduceNoL1 Γ (p ⟶ q) → DeduceNoL1 Γ p → DeduceNoL1 Γ q

def provesNoL1 (p : PropForm) : Prop := DeduceNoL1 ∅ p
notation:45 " ⊢₁ " p => provesNoL1 p

-- 不含L2的子系统
inductive DeduceNoL2 : Set PropForm → PropForm → Prop
  | L0 : ∀ Γ p, p ∈ Γ → DeduceNoL2 Γ p
  | L1 : ∀ Γ p q, DeduceNoL2 Γ (p ⟶ (q ⟶ p))
  | L3 : ∀ Γ p q, DeduceNoL2 Γ ((⇁ p ⟶ (⇁ q)) ⟶ (q ⟶ p))
  | MP : ∀ Γ p q, DeduceNoL2 Γ (p ⟶ q) → DeduceNoL2 Γ p → DeduceNoL2 Γ q

def provesNoL2 (p : PropForm) : Prop := DeduceNoL2 ∅ p
notation:45 " ⊢₂ " p => provesNoL2 p

-- 不含L3的子系统
inductive DeduceNoL3 : Set PropForm → PropForm → Prop
  | L0 : ∀ Γ p, p ∈ Γ → DeduceNoL3 Γ p
  | L1 : ∀ Γ p q, DeduceNoL3 Γ (p ⟶ (q ⟶ p))
  | L2 : ∀ Γ p q r, DeduceNoL3 Γ ((p ⟶ (q ⟶ r)) ⟶ ((p ⟶ q) ⟶ (p ⟶ r)))
  | MP : ∀ Γ p q, DeduceNoL3 Γ (p ⟶ q) → DeduceNoL3 Γ p → DeduceNoL3 Γ q

def provesNoL3 (p : PropForm) : Prop := DeduceNoL3 ∅ p
notation:45 " ⊢₃ " p => provesNoL3 p

-- 定义独立性
def L1_Independent : Prop := ¬AL1 provesNoL1
def L2_Independent : Prop := ¬AL2 provesNoL2
def L3_Independent : Prop := ¬AL3 provesNoL3

-- 三值逻辑的值域
inductive TriValue : Type
  | zero : TriValue
  | one : TriValue
  | two : TriValue

open TriValue

-- 为证明L1独立性的三值逻辑模型
def not_L1 : TriValue → TriValue
  | zero => zero
  | one => one
  | two => one

def impl_L1 : TriValue → TriValue → TriValue
  | zero, one => two
  | zero, two => two
  | one, zero => two
  | one, one => two
  | _, _ => zero

-- 变量赋值：var 0 → zero, 其他 → one
def assign_L1 : Nat → TriValue
  | 0 => zero
  | _ => one

-- 公式在模型L1下的赋值函数
def eval_L1 : PropForm → TriValue
  | PropForm.var n => assign_L1 n
  | PropForm.neg p => not_L1 (eval_L1 p)
  | PropForm.impl p q => impl_L1 (eval_L1 p) (eval_L1 q)

-- 模型的可满足性：值为zero表示真
def satisfies_L1 (p : PropForm) : Prop := eval_L1 p = zero

-- 证明模型L1满足L2公理
theorem L1_model_satisfies_L2 : AL2 satisfies_L1 := by
  intro p q r
  simp [satisfies_L1, eval_L1, impl_L1, not_L1]
  -- 通过分情况讨论证明
  cases (eval_L1 p) <;> cases (eval_L1 q) <;> cases (eval_L1 r) <;> simp


-- 证明模型L1满足L3公理
theorem L1_model_satisfies_L3 : AL3 satisfies_L1 := by
  intro p q
  simp [satisfies_L1, eval_L1, impl_L1, not_L1]
  sorry

-- 证明模型L1满足MP规则
theorem L1_model_satisfies_MP : MP_rule satisfies_L1 := by
  intro p q h1 h2
  simp [satisfies_L1] at h1 h2 ⊢
  simp [eval_L1, impl_L1] at h1
  sorry

-- 证明所有可从子系统NoL1推导的公式在模型L1下都满足
theorem sound_L1 : ∀ p, (⊢₁ p) → satisfies_L1 p := by
  intro p h
  sorry

-- L1公理的反例：(var 0) ⟶ ((var 1) ⟶ (var 0))
theorem L1_counterexample : ¬satisfies_L1 ((var 0) ⟶ ((var 1) ⟶ (var 0))) := by
  simp [satisfies_L1, eval_L1, impl_L1, assign_L1]

-- L1独立性的主定理
theorem L1_independence : L1_Independent := by
  intro h
  -- 假设AL1可从子系统推导
  have counter := h (var 0) (var 1)
  -- 由soundness，反例公式应该满足模型
  have satisfied := sound_L1 ((var 0) ⟶ ((var 1) ⟶ (var 0))) counter
  -- 但这与反例矛盾
  exact L1_counterexample satisfied

-- 为L2和L3独立性定义相应的三值逻辑模型
-- （具体实现类似L1）

-- 主要独立性定理（框架）
theorem axiom_independence : L1_Independent ∧ L2_Independent ∧ L3_Independent := by
  constructor
  · exact L1_independence
  constructor
  · -- L2独立性证明（类似L1的方法）
    sorry
  · -- L3独立性证明（类似L1的方法）
    sorry
