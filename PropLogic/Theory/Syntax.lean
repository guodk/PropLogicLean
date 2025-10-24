import Mathlib
import PropLogic.Theory.Base

open PropForm        -- 等价

/- 公理系统：使用Set表示公式集合 -/
inductive Deduce : Set PropForm → PropForm → Prop
  | L0 :∀ Γ p, p ∈ Γ → Deduce Γ p                -- 假设规则
  | L1 :∀ Γ p q, Deduce Γ (p ⟶ (q ⟶ p))             -- 公理1: p → (q → p)
  | L2 :∀ Γ p q r, Deduce Γ ((p ⟶ (q ⟶ r)) ⟶(( p ⟶ q) ⟶ (p ⟶ r))) -- 公理2: (p→(q→r))→((p→q)→(p→r))
  | L3 :∀ Γ p q, Deduce Γ (((⇁ p) ⟶ (⇁ q)) ⟶ (q ⟶ p))
  | MP :∀ Γ p q, Deduce Γ (p ⟶ q) →  Deduce Γ p →  Deduce Γ q

-- 定义符号表示
notation:45 Γ " ⊢ " p => Deduce Γ p

-- 弱化规则：如果Γ ⊢ p，那么Γ ∪ Δ ⊢ p
lemma weakening (Γ Δ : Set PropForm) (p : PropForm) : (Γ ⊢ p) → (Γ ∪ Δ) ⊢ p := by
  intro h
  induction h
  · apply Deduce.L0
    aesop
  · apply Deduce.L1
  · apply Deduce.L2
  · apply Deduce.L3
  · apply Deduce.MP <;> assumption

-- 如果Γ ⊢ p，且 那么Γ包含于Γ',则 Γ' ⊢ p
lemma weakening' (Γ Γ' : Set PropForm) (p : PropForm) :
    (Γ ⊢ p) → (Γ ⊆ Γ') → (Γ' ⊢ p) := by
  intro h hsub
  induction h
  · apply Deduce.L0
    aesop
  · apply Deduce.L1
  · apply Deduce.L2
  · apply Deduce.L3
  · apply Deduce.MP <;> assumption

-- Γ ⊢ (p ⟶ p)
lemma self_impl (Γ : Set PropForm) (p : PropForm) : Γ ⊢ (p ⟶ p) := by
  -- 使用经典的Hilbert证明：通过L1和L2构造p→p的证明
  -- 1. p → ((p → p) → p)     [L1的实例]
  have h1 : Γ ⊢ (p ⟶ ((p ⟶ p) ⟶ p)) := Deduce.L1 Γ p (p ⟶ p)
  -- 2. p → (p → p)          [L1的实例]
  have h2 : Γ ⊢ (p ⟶ (p ⟶ p)) := Deduce.L1 Γ p p
  -- 3. (p → ((p → p) → p)) → ((p → (p → p)) → (p → p))  [L2的实例]
  have h3 : Γ ⊢ ((p ⟶ ((p ⟶ p) ⟶ p)) ⟶ ((p ⟶ (p ⟶ p)) ⟶ (p ⟶ p))) :=
    Deduce.L2 Γ p (p ⟶ p) p
  -- 4. (p → (p → p)) → (p → p)  [从1,3用MP]
  have h4 : Γ ⊢ ((p ⟶ (p ⟶ p)) ⟶ (p ⟶ p)) := Deduce.MP Γ _ _ h3 h1
  -- 5. p → p                 [从2,4用MP]
  exact Deduce.MP Γ _ _ h4 h2

--演绎定理 Γ ∪ {p} ⊢ q ↔ Γ ⊢ (p ⟶ q)
theorem deduction (Γ : Set PropForm) (p q: PropForm) :
    (Γ ∪ {p} ⊢ q) ↔ (Γ ⊢ (p ⟶ q)) := by
  constructor
  · intro h
    induction h with
    | L0 r h =>
      simp at h
      -- 处理两种情况：r = p 或 r ∈ Γ
      cases h with
      | inl h_case =>
        rw [h_case]
        exact self_impl Γ p
      | inr h_case =>
        have h1 : Γ ⊢ r ⟶ p ⟶ r := by exact Deduce.L1 Γ r p
        apply Deduce.MP Γ r (p ⟶ r) h1
        exact Deduce.L0 Γ r h_case
    | L1 r s =>
      -- 公理L1：r → (s → r)
      -- 需要证明 Γ ⊢ p → (r → (s → r))
      have h1 : Γ ⊢ (r ⟶ (s ⟶ r)) := Deduce.L1 Γ r s
      have h2 : Γ ⊢ ((r ⟶ (s ⟶ r)) ⟶ (p ⟶ (r ⟶ (s ⟶ r)))) := Deduce.L1 Γ (r ⟶ (s ⟶ r)) p
      exact Deduce.MP Γ (r ⟶ (s ⟶ r)) (p ⟶ (r ⟶ (s ⟶ r))) h2 h1
    | L2 r s t =>
      -- 公理L2：(r → (s → t)) → ((r → s) → (r → t))
      have h1 : Γ ⊢ ((r ⟶ (s ⟶ t)) ⟶ ((r ⟶ s) ⟶ (r ⟶ t))) := Deduce.L2 Γ r s t
      have h2 : Γ ⊢ (((r ⟶ (s ⟶ t)) ⟶ ((r ⟶ s) ⟶ (r ⟶ t))) ⟶ (p ⟶ ((r ⟶ (s ⟶ t)) ⟶ ((r ⟶ s) ⟶ (r ⟶ t))))) :=
        Deduce.L1 Γ ((r ⟶ (s ⟶ t)) ⟶ ((r ⟶ s) ⟶ (r ⟶ t))) p
      exact Deduce.MP Γ ((r ⟶ (s ⟶ t)) ⟶ ((r ⟶ s) ⟶ (r ⟶ t))) (p ⟶ ((r ⟶ (s ⟶ t)) ⟶ ((r ⟶ s) ⟶ (r ⟶ t)))) h2 h1
    | L3 r s =>
      -- 公理L3：(¬r → ¬s) → (s → r)
      have h1 : Γ ⊢ (((⇁r) ⟶ (⇁s)) ⟶ (s ⟶ r)) := Deduce.L3 Γ r s
      have h2 : Γ ⊢ ((((⇁r) ⟶ (⇁s)) ⟶ (s ⟶ r)) ⟶ (p ⟶ (((⇁r) ⟶ (⇁s)) ⟶ (s ⟶ r)))) :=
        Deduce.L1 Γ (((⇁r) ⟶ (⇁s)) ⟶ (s ⟶ r)) p
      exact Deduce.MP Γ (((⇁r) ⟶ (⇁s)) ⟶ (s ⟶ r)) (p ⟶ (((⇁r) ⟶ (⇁s)) ⟶ (s ⟶ r))) h2 h1
    | MP r s hr hs ih1 ih2 =>
      -- MP规则：从 Γ ∪ {p} ⊢ (r ⟶ s) 和 Γ ∪ {p} ⊢ r 得到 Γ ∪ {p} ⊢ s
      -- 由归纳假设：Γ ⊢ (p ⟶ (r ⟶ s)) 和 Γ ⊢ (p ⟶ r)
      -- 需要证明：Γ ⊢ (p ⟶ s)
      -- 使用L2：(p → (r → s)) → ((p → r) → (p → s))
      have h1 : Γ ⊢ ((p ⟶ (r ⟶ s)) ⟶ ((p ⟶ r) ⟶ (p ⟶ s))) := Deduce.L2 Γ p r s
      have h2 : Γ ⊢ ((p ⟶ r) ⟶ (p ⟶ s)) := Deduce.MP Γ (p ⟶ (r ⟶ s)) ((p ⟶ r) ⟶ (p ⟶ s)) h1 ih1
      exact Deduce.MP Γ (p ⟶ r) (p ⟶ s) h2 ih2
  -- 反向：如果 Γ ⊢ (p ⟶ q)，则 Γ ∪ {p} ⊢ q
  · intro h
    have h1 : Γ ∪ {p} ⊢ (p ⟶ q) := weakening Γ {p} (p ⟶ q) h
    have h2 : Γ ∪ {p} ⊢ p := Deduce.L0 (Γ ∪ {p}) p (Set.mem_union_right Γ (Set.mem_singleton p))
    exact Deduce.MP (Γ ∪ {p}) p q h1 h2

-- 三段论：如果 Γ ⊢ (p ⟶ q) 和 Γ ⊢ (q ⟶ r)，则 Γ ⊢ (p ⟶ r)
theorem transitivity (Γ : Set PropForm) (p q r : PropForm) :
    (Γ ⊢ (p ⟶ q)) → (Γ ⊢ (q ⟶ r)) → (Γ ⊢ (p ⟶ r)) := by
  intro h1 h2
  rw [← deduction]
  have h3 : Γ ∪ {p} ⊢ (p ⟶ q) := weakening Γ {p} (p ⟶ q) h1
  have h4 : Γ ∪ {p} ⊢ (q ⟶ r) := weakening Γ {p} (q ⟶ r) h2
  have h5 : Γ ∪ {p} ⊢ p := Deduce.L0 (Γ ∪ {p}) p (Set.mem_union_right Γ (Set.mem_singleton p))
  have h6 : Γ ∪ {p} ⊢ q := Deduce.MP (Γ ∪ {p}) p q h3 h5
  exact Deduce.MP (Γ ∪ {p}) q r h4 h6

-- 否定前件律 Γ ⊢ (¬q) → (q → p)
lemma neg_impl (Γ : Set PropForm) (p q : PropForm) :
    Γ ⊢ ((⇁q) ⟶ (q ⟶ p)) := by
  have h1 : Γ ⊢ ((⇁p) ⟶ (⇁q)) ⟶ (q ⟶ p) := Deduce.L3 Γ p q
  have h2 := Deduce.L1 Γ (((⇁p) ⟶ (⇁q)) ⟶ (q ⟶ p)) (⇁q)
  have h3 := Deduce.MP _ _ _ h2 h1
  have h4 := Deduce.L2 Γ (⇁q) ((⇁p) ⟶ (⇁q)) (q ⟶ p)
  have h5 := Deduce.MP _ _ _ h4 h3
  have h6 := Deduce.L1 Γ (⇁q) (⇁p)
  exact transitivity Γ (⇁q) ((⇁p) ⟶ (⇁q)) (q ⟶ p) h6 h1

-- 否定肯定律 Γ ⊢ ((¬p) → p) → p
lemma neg_elim (Γ : Set PropForm) (p : PropForm) :
    Γ ⊢ (((⇁p) ⟶ p) ⟶ p) := by
  rw [← deduction]
  have h1 := neg_impl (Γ ∪ {(⇁p) ⟶ p}) (⇁((⇁p) ⟶ p)) p
  have h2 := Deduce.L2 (Γ ∪ {(⇁p) ⟶ p}) (⇁p) p  (⇁((⇁p) ⟶ p))
  have h3 := Deduce.MP _ _ _ h2 h1
  have h4 : Γ ∪ {(⇁p) ⟶ p} ⊢ (⇁p) ⟶ p := by
    apply Deduce.L0
    simp
  have h5 := Deduce.MP _ _ _ h3 h4
  have h6 := Deduce.L3 (Γ ∪ {(⇁p) ⟶ p}) p ((⇁p) ⟶ p)
  have h7 := Deduce.MP _ _ _ h6 h5
  exact Deduce.MP (Γ ∪ {(⇁p) ⟶ p}) ((⇁p) ⟶ p) p h7 h4

-- 反证律
lemma rule_Indirect : ∀ (Γ : Set PropForm) (p q : PropForm),
    (Γ ∪ {⇁p} ⊢ q) →  (Γ∪{⇁p} ⊢ (⇁q)) →  Γ ⊢ p := by
  intro Γ p q h1 h2
  have h3 : Γ ∪ {⇁p} ⊢ ((⇁q) ⟶ (q ⟶ p)) := by exact neg_impl (Γ ∪ {⇁p}) p q
  have h4 : Γ ∪ {⇁p} ⊢ (q ⟶ p) := Deduce.MP (Γ ∪ {⇁p}) (⇁q) (q ⟶ p) h3 h2
  have h5 : Γ ∪ {⇁p} ⊢ p := Deduce.MP (Γ ∪ {⇁p}) q p h4 h1
  rw [deduction] at h5
  have h6 := neg_elim Γ p
  exact Deduce.MP Γ ((⇁p) ⟶ p) p h6 h5

-- 双重否定律：Γ ⊢ ¬¬p → p 及 Γ ∪ {⇁⇁p} ⊢ p
lemma double_negation_aux (Γ : Set PropForm) (p : PropForm) :
    Γ ∪ {⇁⇁p} ⊢ p := by
  apply rule_Indirect _ _ (⇁p)
  · rw [deduction]
    rw [deduction]
    exact neg_impl Γ (⇁p) (⇁p)
  · rw [deduction]
    rw [deduction]
    exact neg_impl Γ (⇁⇁p) (⇁p)

lemma double_negation (Γ : Set PropForm) (p : PropForm) :
    Γ ⊢ ((⇁⇁p) ⟶ p) := by
  rw [← deduction]
  exact double_negation_aux Γ p

-- 归谬律
lemma rule_Reduction_absurdity (Γ : Set PropForm) (p q: PropForm) :
    (Γ ∪ {p} ⊢ q) → (Γ ∪ {p} ⊢ (⇁q)) → Γ ⊢ (⇁p) := by
  intro h1 h2
  rw [deduction] at h1
  have h3 : Γ ∪ {⇁⇁p} ⊢ p ⟶ q := by exact weakening Γ {⇁⇁p} (p ⟶ q) h1
  have h4 : Γ ∪ {⇁⇁p} ⊢ p := by exact double_negation_aux Γ p
  have h5 : Γ ∪ {⇁⇁p} ⊢ q := Deduce.MP (Γ ∪ {⇁⇁p}) p q h3 h4
  rw [deduction] at h2
  have h6 : Γ ∪ {⇁⇁p} ⊢ p ⟶ (⇁q) := by exact weakening Γ {⇁⇁p} (p ⟶ (⇁q)) h2
  have h7 : Γ ∪ {⇁⇁p} ⊢ (⇁q) := Deduce.MP (Γ ∪ {⇁⇁p}) p (⇁q) h6 h4
  exact rule_Indirect Γ (⇁p) q h5 h7

-- 第二双重否定律 Γ ∪ {p} ⊢ ⇁⇁p 及 Γ ⊢ p → ⇁⇁p
lemma reverse_double_negation_aux (Γ : Set PropForm) (p : PropForm) :
    Γ ∪ {p} ⊢ (⇁⇁p) := by
  apply rule_Reduction_absurdity _ _ p
  · constructor
    left
    simp
  · constructor
    right
    simp

lemma reverse_double_negation (Γ : Set PropForm) (p : PropForm) :
    Γ ⊢ (p ⟶ (⇁⇁p)) := by
  rw [← deduction]
  exact reverse_double_negation_aux Γ p

-- 爆炸原理的一个变体
lemma from_contradiction (Γ : Set PropForm) (p q : PropForm) :
    (Γ ⊢ q) → (Γ ⊢ (⇁q)) → (Γ ⊢ p) := by
  intro h1 h2
  -- 从 q 和 ¬q 可以推出任意命题
  -- 使用 q → (¬q → p)
  have h3 : Γ ⊢ (q ⟶ ((⇁q) ⟶ p)) := by
    -- q → (¬p → q)
    have ha : Γ ⊢ (q ⟶ ((⇁p) ⟶ q)) := Deduce.L1 Γ q (⇁p)
    -- (¬p → q) → (¬q → p)
    have h4 : Γ ∪ {(⇁p) ⟶ (⇁⇁q)} ⊢ (⇁q) ⟶ p := by
      rw [deduction]
      exact Deduce.L3 Γ p (⇁q)
    have hb : Γ ⊢ (((⇁p) ⟶ q) ⟶ ((⇁q) ⟶ p)) := by
      refine (deduction Γ ((⇁p) ⟶ q) ((⇁q) ⟶ p)).mp ?_
      have h5 :Γ ∪ {(⇁p) ⟶ q} ⊢ (⇁p) ⟶ (⇁⇁q) := by
        rw [← deduction]
        have h6 : Γ ∪ {(⇁p) ⟶ q} ∪ {⇁p} ⊢ q ⟶ (⇁⇁q) := by
          exact reverse_double_negation (Γ ∪ {(⇁p) ⟶ q} ∪ {⇁p}) q
        apply Deduce.MP (Γ ∪ {(⇁p) ⟶ q} ∪ {⇁p}) q (⇁⇁q) h6
        have h7 : Γ ∪ {(⇁p) ⟶ q} ∪ {⇁p} ⊢ ⇁p :=
          Deduce.L0 (Γ ∪ {(⇁p) ⟶ q} ∪ {⇁p}) (⇁p) (Set.mem_union_right (Γ ∪ {(⇁p) ⟶ q}) (Set.mem_singleton (⇁p)))
        have h8 : Γ ∪ {(⇁p) ⟶ q} ∪ {⇁p} ⊢ (⇁p) ⟶ q := by
          constructor
          left
          right
          simp
        exact Deduce.MP (Γ ∪ {(⇁p) ⟶ q} ∪ {⇁p}) (⇁p) q h8 h7
      #check transitivity
      rw [deduction] at h5
      rw [deduction] at h4
      rw [deduction]
      exact transitivity Γ ((⇁p) ⟶ q) ((⇁p) ⟶ (⇁⇁q)) ((⇁q) ⟶ p) h5 h4
    -- 使用三段论得到 q → (¬q →
    exact transitivity Γ q ((⇁p) ⟶ q) ((⇁q) ⟶ p) ha hb
  have h4 : Γ ⊢ ((⇁q) ⟶ p) := Deduce.MP Γ q ((⇁q) ⟶ p) h3 h1
  exact Deduce.MP Γ (⇁q) p h4 h2
