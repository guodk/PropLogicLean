import Mathlib
import PropLogic.Theory.Base
import PropLogic.Theory.Semantic
import PropLogic.Theory.Syntax
import PropLogic.Theory.Sound
import PropLogic.Theory.CountableForm

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
  done
