import Mathlib
import PropLogic.Theory.Base

open PropForm
-- 布尔蕴含
def implBool (p q : Bool) : Bool :=
  match p, q with
  | true, true => true
  | true, false => false
  | false, true => true
  | false, false => true

-- 布尔等价
def iffBool (p q : Bool) : Bool :=
  match p, q with
  | true, true => true
  | true, false => false
  | false, true => false
  | false, false => true

-- 定义布尔运算的符号
prefix:5 "¬ᵇ" => Bool.not
infixr:8 " →ᵇ " => implBool
infixl:7 " ∨ᵇ " => Bool.or
infixl:6 " ∧ᵇ " => Bool.and
infixl:9 " ↔ᵇ " => iffBool

/- 赋值函数和语义 -/

-- 赋值函数保持否定的性质
def KeepNeg (v : PropForm → Bool) : Prop :=
  ∀ p : PropForm, v (⇁p) = (¬ᵇ (v p))

-- 赋值函数保持蕴含的性质
def KeepImpl (v : PropForm → Bool) : Prop :=
  ∀ p q : PropForm, v (p ⟶ q) = ((v p) →ᵇ (v q))

-- 合法的赋值函数
structure valuation where
  val : PropForm → Bool
  keep_neg : KeepNeg val
  keep_impl : KeepImpl val

-- 重言式定义
def Tautology (p : PropForm) : Prop :=
  ∀ v : valuation, v.val p = true

-- 重言式符号
prefix:80 " ⊨ " => Tautology

-- 语义推论定义
def Semantic_inference (Γ : Set PropForm) (p : PropForm) : Prop :=
  ∀ v : valuation, (∀ q ∈ Γ, v.val q = true) → v.val p = true

infix:50 " ⊨ " => Semantic_inference

-- 语义演绎定理 Γ∪[p] ╞ q <-> Γ ╞ p → q
theorem semantic_deduction (Γ : Set PropForm) (p q: PropForm) :
    (Γ ∪ {p} ⊨ q) ↔ (Γ ⊨ (p ⟶ q)) := by
  constructor
  -- 正向：如果 Γ ∪ {p} ⊨ q，则 Γ ⊨ (p ⟶ q)
  · intro h
    intro v hv
    -- 展开蕴含的语义
    rw [v.keep_impl]
    -- 分情况讨论 v.val p 的值
    cases h_p : v.val p with
    | true =>
      -- 如果 v.val p = true，需要证明 v.val q = true
      have hq : v.val q = true := by
        apply h v
        intro q' hq
        simp at hq
        cases hq with
        | inl h_eq =>
          rw [h_eq, h_p]
        | inr h_mem =>
          exact hv q' h_mem
      rw [hq]
        -- 需要证明 ∀ r ∈ Γ ∪ {p}, v.val r = true
      aesop
    | false =>
      cases h_q : v.val q with
      | true => aesop
      | false => aesop
  -- 反向：如果 Γ ⊨ (p ⟶ q)，则 Γ ∪ {p} ⊨ q
  · intro h
    intro v hv
    -- 从 Γ ⊨ (p ⟶ q) 得到 v.val (p ⟶ q) = true
    have h1 : v.val (p ⟶ q) = true := h v (fun r hr => hv r (Set.mem_union_left {p} hr))
    -- 从 p ∈ Γ ∪ {p} 得到 v.val p = true
    have h2 : v.val p = true := hv p (Set.mem_union_right Γ (Set.mem_singleton p))
    -- 利用蕴含的语义和MP
    rw [v.keep_impl] at h1
    simp [implBool] at h1
    rw [h2] at h1
    aesop
  done


-- 证明析取的语义保持性
lemma valuation_preserves_or (v : valuation) (p q : PropForm) :
    (v.val (p ⩒ q)) = ((v.val p) ∨ᵇ (v.val q)) := by
  -- p ⩒ q = (⇁p) ⟶ q
  simp
  rw [v.keep_impl, v.keep_neg]
  -- 展开布尔运算
  cases h_p : v.val p with
  | true =>
    simp [Bool.not, implBool, Bool.or, h_p]
    aesop
  | false =>
    simp [Bool.not, implBool, Bool.or, h_p]
    aesop
-- 证明合取的语义保持性
lemma valuation_preserves_and (v : valuation) (p q : PropForm) :
    v.val (p ⩑ q) = ((v.val p) ∧ᵇ (v.val q)) := by
  simp
  rw [v.keep_neg, v.keep_impl, v.keep_neg]
  cases h_p : v.val p with
  | true =>
    cases h_q : v.val q with
    | true => aesop
    | false => aesop
  | false =>
    cases h_q : v.val q with
    | true => aesop
    | false => aesop
  done

-- 证明等价的语义保持性
lemma valuation_preserves_iff (v : valuation) (p q : PropForm) :
    v.val (p ⟷ q) = ((v.val p) ↔ᵇ (v.val q)) := by
  simp
  rw [v.keep_neg, v.keep_impl, v.keep_neg, v.keep_impl, v.keep_impl]
  cases h_p : v.val p with
  | true =>
    cases h_q : v.val q with
    | true => aesop
    | false => aesop
  | false =>
    cases h_q : v.val q with
    | true => aesop
    | false => aesop
  done
