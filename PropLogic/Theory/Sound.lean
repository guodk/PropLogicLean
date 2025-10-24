import Mathlib
import PropLogic.Theory.Base
import PropLogic.Theory.Semantic
import PropLogic.Theory.Syntax

open PropForm
-- soundness 定理
theorem soundness_L (Γ : Set PropForm) (p : PropForm) :
    (Γ ⊢ p) → (Γ ⊨ p) := by
  intro h
  -- 对推导 h : Γ ⊢ p 进行结构归纳
  induction h with
  -- 情况1：假设规则 L0
  | L0 q h =>
    -- 需要证明：如果 q ∈ Γ，则 Γ ⊨ q
    intro v hv
    -- 由于 q ∈ Γ 且 hv 保证 Γ 中所有公式在 v 下为真
    exact hv q h

  -- 情况2：公理1 - p → (q → p)
  | L1 q r =>
    -- 需要证明：Γ ⊨ (q ⟶ (r ⟶ q))
    intro v hv
    -- 展开蕴含的语义定义
    #check v.keep_impl
    have h1 : (v.val (q ⟶ (r ⟶ q))) = ((v.val q) →ᵇ (v.val r) →ᵇ (v.val q)) := by
      rw [v.keep_impl, v.keep_impl]
    rw [h1]
    -- 通过真值表验证：p → (q → p) 恒为真
    cases h_q : v.val q with
    | true =>
      cases h_r : v.val r with
      | true => aesop
      | false => aesop
    | false =>
      -- 如果 q 为假，则 q → (r → q) 仍为真（因为前件为假）
      simp [implBool]
      aesop

  -- 情况3：公理2 - (p → (q → r)) → ((p → q) → (p → r))
  | L2 q r s =>
    -- 需要证明：Γ ⊨ ((q ⟶ (r ⟶ s)) ⟶ ((q ⟶ r) ⟶ (q ⟶ s)))
    intro v hv
    -- 展开所有蕴含的语义定义
    --rw [v.keep_impl, v.keep_impl, v.keep_impl, v.keep_impl]
    -- 通过对所有变量的真值进行案例分析
    cases h_q : v.val q with
    | true =>
      cases h_r : v.val r with
      | true =>
        cases h_s : v.val s with
        | true =>
          rw [v.keep_impl, v.keep_impl, v.keep_impl, v.keep_impl, v.keep_impl, v.keep_impl]
          simp only [implBool, h_q, h_r, h_s]
        | false =>
          rw [v.keep_impl, v.keep_impl, v.keep_impl, v.keep_impl, v.keep_impl, v.keep_impl]
          simp only [implBool, h_q, h_r, h_s]
      | false =>
        rw [v.keep_impl, v.keep_impl, v.keep_impl, v.keep_impl, v.keep_impl, v.keep_impl]
        cases h_s : v.val s with
        | true =>
          simp only [implBool, h_q, h_r, h_s]
        | false =>
          simp only [implBool, h_q, h_r, h_s]
    | false =>
      rw [v.keep_impl, v.keep_impl, v.keep_impl, v.keep_impl, v.keep_impl, v.keep_impl]
      cases h_r : v.val r with
      | true =>
        cases h_s : v.val s with
        | true =>
          simp only [implBool, h_q, h_r, h_s]
        | false =>
          simp only [implBool, h_q, h_r, h_s]
      | false =>
        cases h_s : v.val s with
        | true =>
          simp only [implBool, h_q, h_r, h_s]
        | false =>
          simp only [implBool, h_q, h_r, h_s]

  -- 情况4：公理3 - (¬p → ¬q) → (q → p)
  | L3 q r =>
    -- 需要证明：Γ ⊨ ((⇁q ⟶ ⇁r) ⟶ (r ⟶ q))
    intro v hv
    -- 展开蕴含和否定的语义定义
    rw [v.keep_impl, v.keep_impl, v.keep_neg, v.keep_impl, v.keep_neg]
    cases h_q : v.val q with
    | true =>
      cases h_r : v.val r with
      | true => aesop
      | false => aesop
    | false =>
      cases h_r : v.val r with
      | true => aesop
      | false => aesop

  -- 情况5：肯定前件规则 MP
  | MP q r h1 h2 ih1 ih2=>
    -- 已知：Γ ⊢ (q ⟶ r) 和 Γ ⊢ q
    -- 归纳假设：ih1 : Γ ⊨ (q ⟶ r) 和 ih2 : Γ ⊨ q
    -- 需要证明：Γ ⊨ r

    intro v hv
    -- 应用归纳假设得到语义真值
    have h1 : v.val (q ⟶ r) = true := ih1 v hv
    have h2 : v.val q = true := ih2 v hv
    -- 利用蕴含的语义定义
    rw [v.keep_impl] at h1
    -- 由于 v.val q = true 且 v.val (q ⟶ r) = true
    -- 根据蕴含的真值表，必有 v.val r = true
    simp [implBool] at h1
    rw [h2] at h1
    cases h_r : v.val r with
    | true => aesop
    | false => aesop
  done

-- 一致集定义 ∀ q, ~ (Γ ├ q /\ Γ ├ ¬q)
def Consistent (Γ : Set PropForm) : Prop :=
  ∀ p : PropForm, ¬ ((Γ ⊢ p) ∧ (Γ ⊢ (⇁p)))

-- 一个命题变元全为真的赋值函数
def vtrue : PropForm → Bool
  | PropForm.var n => true
  | PropForm.neg p => Bool.not (vtrue p)
  | PropForm.impl p q => implBool (vtrue p) (vtrue q)

instance VTrue : valuation where
  val := vtrue
  keep_neg := by
    exact congrFun rfl
  keep_impl := by
    exact fun p ↦ congrFun rfl

-- 公理系统L是一致的（空集是一致的）
theorem empty_consistent : Consistent ∅ := by
  unfold Consistent
  intro p h
  let h1 := h.left
  let h2 := h.right
  apply soundness_L at h1
  apply soundness_L at h2
  let ht1 := h1 VTrue
  let ht2 := h2 VTrue
  have h_false : ∀ q ∈ (∅ : Set PropForm), VTrue.val q = true := by
    intro q hq
    cases hq
  have hq : VTrue.val p = true := ht1 h_false
  have hnq : VTrue.val (⇁p) = true := ht2 h_false
  rw [VTrue.keep_neg] at hnq
  simp [Bool.not] at hnq
  rw [hq] at hnq
  simp at hnq
