/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.Analysis.Normed.Ring.Seminorm
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Seminorm related definitions
## Tags
ring_norm, equivalent
-/

/-- A function `f : α → β` is nonarchimedean if it satisfies the inequality
  `f (a + b) ≤ max (f a) (f b)` for all `a, b ∈ α`. -/
def is_nonarchimedean {α : Type*} [HAdd α α α] {β : Type*} [LinearOrder β] (f : α → β) : Prop :=
∀ r s, f (r + s) ≤ max (f r) (f s)

lemma is_nonarchimedean_def {α : Type*} [HAdd α α α] {β : Type*} [LinearOrder β] (f : α → β) :
is_nonarchimedean f ↔ ∀ r s, f (r + s) ≤ max (f r) (f s) := by rfl

/-- A function `f : α → β` is `multiplicative` if it satisfies the equality
  `f (a * b) = (f a) * (f b)` for all `a, b ∈ α`. -/
def mul_eq {α : Type*} [HMul α α α] {β : Type*} [HMul β β β] (f : α → β) : Prop :=
∀ r s, f (r * s) = (f r) * (f s)

lemma mul_eq_def {α : Type*} [HMul α α α] {β : Type*} [HMul β β β] (f : α → β) :
mul_eq f ↔ ∀ r s, f (r * s) = (f r) * (f s) := by rfl

namespace mul_ring_norm

/-- Two multiplicative ring norms `f, g` on `R` are equivalent if there exists a positive constant
  `c` such that for all `x ∈ R`, `(f x)^c = g x`.
  This could be generalised to ring_norm, but mul_ring_norm does not extend this. -/
def equiv {R : Type*} [Ring R] (f : MulRingNorm R) (g : MulRingNorm R) :=
  ∃ c : ℝ, 0 < c ∧ (λ x : R ↦ (f x) ^ c) = g

lemma equiv_refl {R : Type*} [Ring R] (f : MulRingNorm R) :
  equiv f f := by refine ⟨1, by linarith, by simp only [Real.rpow_one]⟩

lemma equiv_symm {R : Type*} [Ring R] {f g : MulRingNorm R} (hfg : equiv f g) :
  equiv g f :=
by
  rcases hfg with ⟨c, hfg1, hfg2⟩
  refine ⟨1 / c, by simp only [hfg1, one_div, inv_pos], ?_⟩
  rw [← hfg2]
  ext x
  simp only [one_div]
  have h1 : c ≠ 0 := by linarith
  rw [← Real.rpow_mul (apply_nonneg f x)]
  simp only [h1, mul_inv_cancel, Ne.def, not_false_iff, Real.rpow_one]

lemma equiv_trans {R : Type*} [Ring R] {f g k : MulRingNorm R} (hfg : equiv f g) (hgk : equiv g k) :
  equiv f k :=
by
  rcases hfg with ⟨c, hfg1, hfg2⟩
  rcases hgk with ⟨d, hgk1, hgk2⟩
  refine ⟨c * d, by simp only [hfg1, hgk1, mul_pos_iff_of_pos_right], ?_⟩
  rw [← hgk2]
  rw [← hfg2]
  ext x
  exact Real.rpow_mul (apply_nonneg f x) c d

end mul_ring_norm
