import Mathlib

/- 命题逻辑的形式化 -/

/- 语法定义 -/
inductive PropForm : Type
  | var : Nat → PropForm                    -- 命题变量，用Nat表示
  | neg : PropForm → PropForm               -- 否定
  | impl : PropForm → PropForm → PropForm   -- 蕴含
  deriving Countable, Encodable

theorem Count_Form : Countable PropForm := inferInstance

-- 步骤1：证明 PropForm 是无限的
instance : Infinite PropForm :=
  Infinite.of_injective PropForm.var (fun _ _ h => by injection h)

-- 步骤2：从 Countable + Infinite 得到 Denumerable
instance : Denumerable PropForm := by
  exact Denumerable.ofEncodableOfInfinite PropForm

def encode_formula : PropForm → ℕ :=
  Denumerable.eqv PropForm

def decode_formula : ℕ → PropForm :=
  (Denumerable.eqv PropForm).symm

-- 证明它们互为逆函数
theorem encode_decode : ∀ n : ℕ, encode_formula (decode_formula n) = n := by
  intro n
  exact Equiv.apply_symm_apply (Denumerable.eqv PropForm) n

theorem decode_encode : ∀ φ : PropForm, decode_formula (encode_formula φ) = φ := by
  intro φ
  exact Equiv.symm_apply_apply (Denumerable.eqv PropForm) φ

-- 证明 encode 是单射
theorem encode_injective : Function.Injective encode_formula :=
  (Denumerable.eqv PropForm).injective

-- 证明 encode 是满射
theorem encode_surjective : Function.Surjective encode_formula :=
  (Denumerable.eqv PropForm).surjective

-- 证明 encode 是双射
theorem encode_bijective : Function.Bijective encode_formula :=
  (Denumerable.eqv PropForm).bijective

-- 明确存在性陈述
theorem exists_bijection_Nat_PropForm :
    ∃ f : ℕ → PropForm, ∃ g : PropForm → ℕ,
      Function.LeftInverse g f ∧ Function.RightInverse g f := by
  use decode_formula, encode_formula
  constructor
  · intro n
    exact encode_decode n
  · intro φ
    exact decode_encode φ

-- 使用 Function.Bijective 的存在性形式
theorem exists_bijection_Nat_PropForm' :
    ∃ f : PropForm → ℕ, Function.Bijective f := by
  use encode_formula
  exact encode_bijective

open PropForm

-- 定义逻辑运算符的符号
prefix:0 "⇁" => PropForm.neg
infixr:8 " ⟶ " => PropForm.impl
infixl:7 " ⩒ " => fun p q => (⇁p) ⟶ q                    -- 析取
infixl:6 " ⩑ " => fun p q => ⇁(p ⟶ (⇁q))                 -- 合取
infixl:9 " ⟷ " => fun p q => (p ⟶ q) ⩑ (q ⟶ p)          -- 等价

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



-- 如果Γ不一致，可以推出任意公式
lemma boom (Γ : Set PropForm) (h : ¬ Consistent Γ) (p : PropForm) : Γ ⊢ p := by
  unfold Consistent at h
  push_neg at h
  obtain ⟨q, hq1, hq2⟩ := h
  exact from_contradiction Γ p q hq1 hq2

-- 对任意p，Γ∪{p}一致或Γ∪{¬p}一致
lemma no_contra (Γ : Set PropForm) (h : Consistent Γ) (p : PropForm) :
    Consistent (Γ ∪ {p}) ∨ Consistent (Γ ∪ {⇁p}) := by
  by_cases h1 : Consistent (Γ ∪ {⇁p})
  · right; exact h1
  · left
    unfold Consistent at h h1 ⊢
    intro q
    intro ⟨hq1, hq2⟩
    -- 从 Γ ∪ {¬p} 不一致得到任意公式可证
    have hp : Γ ∪ {⇁p} ⊢ p := boom (Γ ∪ {⇁p}) h1 p
    have hnp := boom (Γ ∪ {⇁p}) h1 (⇁p)

    -- 因此 Γ ⊢ p
    have hp' : Γ ⊢ p := by exact rule_Indirect Γ p p hp hnp
    -- 从 Γ ∪ {p} ⊢ q 得到 Γ ⊢ p → q
    rw [deduction] at hq1 hq2
    -- 现在 Γ ⊢ p, Γ ⊢ p → q, Γ ⊢ p → ¬q
    have hq1' : Γ ⊢ q := Deduce.MP Γ p q hq1 hp'
    have hq2' : Γ ⊢ (⇁q) := Deduce.MP Γ p (⇁q) hq2 hp'
    exact h q ⟨hq1', hq2'⟩

-- 构造极大一致扩展

open Classical

-- 使用Denumerable枚举所有公式
-- 递归构造过程（非构造性的）
noncomputable def mapf (Γ : Set PropForm) (n : ℕ) (f : ℕ → PropForm) : Set PropForm :=
  match n with
  | 0 => Γ
  | n + 1 =>
    let Γn := mapf Γ n f
    if Consistent (Γn ∪ {f n}) then Γn ∪ {f n} else Γn

-- 极大一致扩展：所有有限阶段的并集
def maxmapf (Γ : Set PropForm) (f : ℕ → PropForm) : Set PropForm :=
  fun p => ∃ n, p ∈ mapf Γ n f

-- mapf是单调的
lemma mapf_mono (Γ : Set PropForm) (f : ℕ → PropForm) (m n : ℕ) (h : m ≤ n) :
    mapf Γ m f ⊆ mapf Γ n f := by
  revert m
  induction n with
  | zero =>
    intro m h
    cases h
    rfl
  | succ n ih =>
    intro m h
    cases Nat.eq_or_lt_of_le h with
    | inl heq =>
      rw [heq]
    | inr hlt =>
      have : m ≤ n := Nat.le_of_lt_succ hlt
      have : mapf Γ m f ⊆ mapf Γ n f := ih m this
      intro x hx
      have : x ∈ mapf Γ n f := by exact this hx
      unfold mapf
      by_cases hcons : Consistent (mapf Γ n f ∪ {f n})
      · rw [if_pos hcons]
        left
        exact this
      · rw [if_neg hcons]
        exact this

-- 每一步都保持一致性
lemma mapf_consistent (Γ : Set PropForm) (f : ℕ → PropForm) (h : Consistent Γ) (n : ℕ) :
    Consistent (mapf Γ n f) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    unfold mapf
    by_cases hcons : Consistent (mapf Γ n f ∪ {f n})
    · rw [if_pos hcons]
      exact hcons
    · rw [if_neg hcons]
      exact ih

lemma maxmapfI (Γ : Set PropForm) (f : ℕ → PropForm) (h : Consistent Γ) (p : PropForm) :
    ((maxmapf Γ f) ⊢ p) →  ∃ n, (mapf Γ n f) ⊢ p := by
  intro h1
  induction h1 with
  | L0 q hq =>
    -- q ∈ maxmapf Γ f
    unfold maxmapf at hq
    obtain ⟨n, hn⟩ := hq
    use n
    exact Deduce.L0 (mapf Γ n f) q hn
  | L1 q r =>
    use 0
    exact Deduce.L1 (mapf Γ 0 f) q r
  | L2 q r s =>
    use 0
    exact Deduce.L2 (mapf Γ 0 f) q r s
  | L3 q r =>
    use 0
    exact Deduce.L3 (mapf Γ 0 f) q r
  | MP q r hq hr ihq ihr =>
    obtain ⟨n1, hn1⟩ := ihq
    obtain ⟨n2, hn2⟩ := ihr
    let n := max n1 n2
    use n
    have hmn1 : n1 ≤ n := Nat.le_max_left n1 n2
    have hmn2 : n2 ≤ n := Nat.le_max_right n1 n2
    have h1 : mapf Γ n1 f ⊆ mapf Γ n f := mapf_mono Γ f n1 n hmn1
    have h2 : mapf Γ n2 f ⊆ mapf Γ n f := mapf_mono Γ f n2 n hmn2
    have hm1 : (mapf Γ n f) ⊢ (q ⟶ r) := by
      exact weakening' (mapf Γ n1 f) (mapf Γ n f) (q ⟶ r) hn1 h1
    have hm2 : (mapf Γ n f) ⊢ q := by
      exact weakening' (mapf Γ n2 f) (mapf Γ n f) q hn2 h2
    exact Deduce.MP (mapf Γ n f) q r hm1 hm2

-- maxmapf是一致的
lemma maxmapf_consistent (Γ : Set PropForm) (f : ℕ → PropForm) (h : Consistent Γ) :
    Consistent (maxmapf Γ f) := by
  unfold Consistent
  intro p
  intro ⟨h1, h1n⟩
  have hp := maxmapfI Γ f h p h1
  have hnp := maxmapfI Γ f h (⇁p) h1n
  obtain ⟨n1, hn1⟩ := hp
  obtain ⟨n2, hn2⟩ := hnp
  let n := max n1 n2
  have hmn1 : n1 ≤ n := Nat.le_max_left n1 n2
  have hmn2 : n2 ≤ n := Nat.le_max_right n1 n2
  have h1 : mapf Γ n1 f ⊆ mapf Γ n f := mapf_mono Γ f n1 n hmn1
  have h2 : mapf Γ n2 f ⊆ mapf Γ n f := mapf_mono Γ f n2 n hmn2
  have hm1 : (mapf Γ n f) ⊢ p := by
    exact weakening' (mapf Γ n1 f) (mapf Γ n f) p hn1 h1
  have hm2 : (mapf Γ n f) ⊢ (⇁p) := by
    exact weakening' (mapf Γ n2 f) (mapf Γ n f) (⇁p) hn2 h2
  have hcons := mapf_consistent Γ f h n
  exact hcons p ⟨hm1, hm2⟩


-- maxmapf的极大性
lemma maxmapf_maximal (Γ : Set PropForm) (f : ℕ → PropForm) (hsurj : Function.Surjective f)
    (h : Consistent Γ) (p : PropForm) (hcons : Consistent (maxmapf Γ f ∪ {p})) :
    p ∈ maxmapf Γ f := by
  -- 存在n使得f(n) = p
  obtain ⟨n, hn⟩ := hsurj p
  unfold maxmapf
  use n + 1
  unfold mapf
  by_cases hcons' : Consistent (mapf Γ n f ∪ {f n})
  · rw [if_pos hcons']
    rw [hn]
    right
    rfl
  · rw [if_neg hcons']
    subst hn
    exfalso
    have hres : Consistent (mapf Γ n f ∪ {f n}) := by
      unfold Consistent at hcons ⊢
      intro q
      intro ⟨hq1, hq2⟩
      have hqm : (mapf Γ n f) ∪ {f n} ⊆ (maxmapf Γ f) ∪ {f n} := by
        intro x hx
        cases hx with
        | inl hxl =>
          left
          use n
        | inr hxr =>
          right
          exact hxr
      have hq1' : (maxmapf Γ f) ∪ {f n} ⊢ q := weakening' ((mapf Γ n f) ∪ {f n}) ((maxmapf Γ f) ∪ {f n}) q hq1 hqm
      have hq2' : (maxmapf Γ f) ∪ {f n} ⊢ (⇁q) := weakening' ((mapf Γ n f) ∪ {f n}) ((maxmapf Γ f) ∪ {f n}) (⇁q) hq2 hqm
      exact hcons q ⟨hq1', hq2'⟩
    exact hcons' hres

-- 规范赋值
noncomputable def valuemaxf (Γ : Set PropForm) : PropForm → Bool :=
  fun p => if p ∈ Γ then true else false

-- 极大一致集的定义
def MaximalConsistent (Γ : Set PropForm) : Prop :=
  Consistent Γ ∧ ∀ p, Consistent (Γ ∪ {p}) → p ∈ Γ

-- 规范赋值保持否定
lemma valuemaxf_keep_neg (Γ : Set PropForm) (h : MaximalConsistent Γ) :
    KeepNeg (valuemaxf Γ) := by
  intro p
  unfold valuemaxf
  obtain ⟨hcons, hmax⟩ := h
  by_cases hp : p ∈ Γ
  · simp [hp]
    by_cases hnp : (⇁p) ∈ Γ
    · -- 如果p和¬p都在Γ中，矛盾
      exfalso
      have : Γ ⊢ p := Deduce.L0 _ _ hp
      have : Γ ⊢ (⇁p) := Deduce.L0 _ _ hnp
      exact hcons p ⟨‹Γ ⊢ p›, ‹Γ ⊢ (⇁p)›⟩
    · simp [hnp]
  · simp [hp]
    -- 如果p ∉ Γ，则¬p ∈ Γ（由极大性）
    have : (⇁p) ∈ Γ := by
      apply hmax
      -- 需要证明Γ ∪ {¬p}一致
      cases no_contra Γ hcons p with
      | inl h =>
        -- 如果Γ ∪ {p}一致，则p ∈ Γ，矛盾
        have : p ∈ Γ := hmax p h
        contradiction
      | inr h => exact h
    simp [this]

-- 规范赋值保持蕴含
lemma valuemaxf_keep_impl (Γ : Set PropForm) (h : MaximalConsistent Γ) :
    KeepImpl (valuemaxf Γ) := by
  intro p q
  unfold valuemaxf implBool
  obtain ⟨hcons, hmax⟩ := h
  by_cases hp : p ∈ Γ
  · by_cases hpq : (p ⟶ q) ∈ Γ
    · by_cases hq : q ∈ Γ
      · -- 如果p, (p→q), q都在Γ中
        simp [hp, hpq, hq]
      · simp [hp, hpq, hq]
        have : (⇁q) ∈ Γ := by
          apply hmax
          -- 需要证明Γ ∪ {¬q}一致
          cases no_contra Γ hcons q with
          | inl h =>
            -- 如果Γ ∪ {q}一致，则q ∈ Γ，矛盾
            have : q ∈ Γ := hmax q h
            contradiction
          | inr h => exact h
        have h_res := no_contra _ hcons q
        -- 讨论h_res的两种情况
        cases h_res with
        | inl h1 =>
          unfold Consistent at h1
          have hq1 := h1 q
          apply hq1
          constructor
          · exact False.elim (hq (hmax q h1))
          · apply Deduce.L0
            left
            exact this
        | inr h2 =>
          unfold Consistent at h2
          have hq2 := h2 q
          apply hq2
          constructor
          · apply weakening
            apply Deduce.MP _ p
            exact Deduce.L0 Γ (p ⟶ q) hpq
            exact Deduce.L0 Γ p hp
          · apply Deduce.L0
            left
            exact this
    · simp [hp, hpq]
      by_cases hq : q ∈ Γ
      · simp [hp, hpq, hq]
        apply hpq
        apply hmax
        unfold Consistent
        intro r
        intro ⟨hr1, hr2⟩
        have hq' : Γ ⊢ q := by exact Deduce.L0 Γ q hq
        have hpq' : Γ ⊢ (p ⟶ q) := by
          apply Deduce.MP Γ q
          exact Deduce.L1 Γ q p
          exact hq'
        rw [deduction] at hr1 hr2
        have hr : Γ ⊢ r := by exact Deduce.MP Γ (p ⟶ q) r hr1 hpq'
        have hnr : Γ ⊢ (⇁r) := by exact Deduce.MP Γ (p ⟶ q) (⇁r) hr2 hpq'
        exact hcons r ⟨hr, hnr⟩
      · simp [hp, hpq, hq]
  · by_cases hpq : (p ⟶ q) ∈ Γ
    · by_cases hq : q ∈ Γ
      · simp [hp, hpq, hq]
      · simp [hp, hpq, hq]
    · by_cases hq : q ∈ Γ
      · simp [hp, hpq, hq]
        apply hpq
        apply hmax
        unfold Consistent
        intro r
        intro ⟨hr1, hr2⟩
        have hq' : Γ ⊢ q := by exact Deduce.L0 Γ q hq
        have hpq' : Γ ⊢ (p ⟶ q) := by
          apply Deduce.MP Γ q
          exact Deduce.L1 Γ q p
          exact hq'
        rw [deduction] at hr1 hr2
        have hr : Γ ⊢ r := by exact Deduce.MP Γ (p ⟶ q) r hr1 hpq'
        have hnr : Γ ⊢ (⇁r) := by exact Deduce.MP Γ (p ⟶ q) (⇁r) hr2 hpq'
        exact hcons r ⟨hr, hnr⟩
      · simp [hp, hpq, hq]
        have hnq : (⇁p) ∈ Γ := by
          apply hmax
          cases no_contra Γ hcons p with
          | inl h =>
            -- 如果Γ ∪ {q}一致，则q ∈ Γ，矛盾
            have : p ∈ Γ := hmax p h
            contradiction
          | inr h => exact h
        apply hpq
        apply hmax
        unfold Consistent
        intro r
        intro ⟨hr1, hr2⟩
        have hpq' : Γ ⊢ (p ⟶ q) := by
          apply Deduce.MP Γ (⇁p)
          exact neg_impl Γ q p
          exact Deduce.L0 Γ (⇁p) hnq
        rw [deduction] at hr1 hr2
        have hr : Γ ⊢ r := by exact Deduce.MP Γ (p ⟶ q) r hr1 hpq'
        have hnr : Γ ⊢ (⇁r) := by exact Deduce.MP Γ (p ⟶ q) (⇁r) hr2 hpq'
        exact hcons r ⟨hr,  hnr⟩

-- 构造规范赋值函数
noncomputable def canonical_val (Γ : Set PropForm) (h : MaximalConsistent Γ) : valuation where
  val := valuemaxf Γ
  keep_neg := valuemaxf_keep_neg Γ h
  keep_impl := valuemaxf_keep_impl Γ h

-- 真值引理
theorem truth_lemma (Γ : Set PropForm) (h : MaximalConsistent Γ) (p : PropForm) :
    (canonical_val Γ h).val p = true ↔ p ∈ Γ := by
  induction p with
  | var _ =>
    constructor
    · intro h1
      unfold canonical_val valuemaxf at h1
      simp at h1
      exact h1
    · intro h1
      unfold canonical_val valuemaxf
      simp [h1]
  | neg _ _ =>
    constructor
    · intro h1
      unfold canonical_val valuemaxf at h1
      simp at h1
      exact h1
    · intro h1
      unfold canonical_val valuemaxf
      simp [h1]
  | impl _ _ _ _ =>
    constructor
    · intro h1
      unfold canonical_val valuemaxf at h1
      simp at h1
      exact h1
    · intro h1
      unfold canonical_val valuemaxf
      simp [h1]

-- ============================================
-- 第四步：完备性定理
-- ============================================

theorem completeness (Γ : Set PropForm) (p : PropForm) :
    (Γ ⊨ p) → (Γ ⊢ p) := by
  intro h
  by_contra hneg
  -- Γ ∪ {¬p}必定一致
  have hcons : Consistent (Γ ∪ {⇁p}) := by
    unfold Consistent
    intro q ⟨hq1, hq2⟩
    have hp : Γ ⊢ p := by
      exact rule_Indirect Γ p q hq1 hq2
    exact hneg hp

  -- 获取满射函数
  let f := decode_formula
  have hsurj : Function.Surjective f := by
    intro p
    use encode_formula p
    exact decode_encode p

  -- 扩展为极大一致集
  let Γ' := maxmapf (Γ ∪ {⇁p}) f

  have hmax : MaximalConsistent Γ' := by
    constructor
    · exact maxmapf_consistent (Γ ∪ {⇁p}) f hcons
    · intro q hcq
      exact maxmapf_maximal (Γ ∪ {⇁p}) f hsurj hcons q hcq

  -- 构造规范赋值
  let v := canonical_val Γ' hmax

  -- v满足Γ
  have hv : ∀ q ∈ Γ, v.val q = true := by
    intro q hq
    rw [truth_lemma Γ' hmax q]
    unfold Γ'
    unfold maxmapf
    use 0
    unfold mapf
    left
    exact hq

  -- 但v不满足p
  have hnp : v.val p = false := by
    cases heq : v.val p
    · rfl
    · exfalso
      rw [truth_lemma Γ' hmax p] at heq
      -- p ∈ Γ'且 ¬p ∈ Γ'，矛盾
      have : (⇁p) ∈ Γ' := by
        unfold Γ' maxmapf
        use 0
        unfold mapf
        right
        rfl
      have h1 : Γ' ⊢ p := Deduce.L0 _ _ heq
      have h2 : Γ' ⊢ (⇁p) := Deduce.L0 _ _ this
      have := hmax.1 p ⟨h1, h2⟩
      exact this

  -- 矛盾：h说v.val p = true
  have : v.val p = true := h v hv
  rw [hnp] at this
  contradiction
