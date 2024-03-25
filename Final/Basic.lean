import Mathlib.Analysis.Normed.Ring.Seminorm
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Seminorm related definitions

This file introduces the nonarchimedean property of the norm and the equivalence relation
between two norms.

-/

/-- A function `f : α → β` is nonarchimedean if it satisfies the inequality
  `f (a + b) ≤ max (f a) (f b)` for all `a, b ∈ α`. -/
def Nonarchimedean {α : Type*} [HAdd α α α] {β : Type*} [LinearOrder β] (f : α → β) : Prop :=
∀ r s, f (r + s) ≤ max (f r) (f s)

lemma Nonarchimedean_def {α : Type*} [HAdd α α α] {β : Type*} [LinearOrder β] (f : α → β) :
Nonarchimedean f ↔ ∀ r s, f (r + s) ≤ max (f r) (f s) := by rfl

namespace MulRingNorm

/-- Two multiplicative ring norms `f, g` on `R` are equivalent if there exists a positive constant
  `c` such that for all `x ∈ R`, `(f x)^c = g x`.
  This could be generalised to ring_norm, but MulRingNorm does not extend this. -/
def equiv {R : Type*} [Ring R] (f : MulRingNorm R) (g : MulRingNorm R) :=
  ∃ c : ℝ, 0 < c ∧ (λ x : R ↦ (f x) ^ c) = g

lemma equiv_refl {R : Type*} [Ring R] (f : MulRingNorm R) :
  equiv f f := by refine ⟨1, by linarith, by simp only [Real.rpow_one]⟩

lemma equiv_symm {R : Type*} [Ring R] {f g : MulRingNorm R} (hfg : equiv f g) :
    equiv g f := by
  rcases hfg with ⟨c, hfg1, hfg2⟩
  refine ⟨1 / c, by simp only [hfg1, one_div, inv_pos], ?_⟩
  rw [← hfg2]
  ext x
  simp only [one_div]
  have h1 : c ≠ 0 := by linarith
  rw [← Real.rpow_mul (apply_nonneg f x)]
  simp only [h1, mul_inv_cancel, Ne.def, not_false_iff, Real.rpow_one]

lemma equiv_trans {R : Type*} [Ring R] {f g k : MulRingNorm R} (hfg : equiv f g) (hgk : equiv g k) :
    equiv f k := by
  rcases hfg with ⟨c, hfg1, hfg2⟩
  rcases hgk with ⟨d, hgk1, hgk2⟩
  refine ⟨c * d, by simp only [hfg1, hgk1, mul_pos_iff_of_pos_right], ?_⟩
  rw [← hgk2, ← hfg2]
  ext x
  exact Real.rpow_mul (apply_nonneg f x) c d

end MulRingNorm
