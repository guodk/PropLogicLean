import Mathlib
import PropLogic.Theory.Base

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
