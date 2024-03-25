import Mathlib.Tactic
import Final.Basic

/-!
# Ostrowski's theorem for ℚ

This file states some basic lemmas about norms in ℚ

-/

variable {f : MulRingNorm ℚ}

lemma f_mul_eq : ∀ r s, f (r * s) = (f r) * (f s) := f.map_mul'

-- The norm of -1 is 1
lemma norm_neg_one_eq_one : f (-1) = 1 := by
  have H₁ : f (-1) * f (-1) = 1
  · calc
      f (-1) * f (-1)  = f ((-1) * (-1)) := by simp
                     _ = f 1 := by norm_num
                     _ = 1 := f.map_one'
  have H₂: f (-1) ≥ 0 := apply_nonneg f (-1)
  rw [mul_self_eq_one_iff] at H₁
  cases' H₁ with H₁ H₃
  · exact H₁
  · rw [H₃] at H₂
    have h' : ¬(-1 ≥ (0 : ℝ)) := by norm_num
    contradiction

lemma int_norm_bound_iff_nat_norm_bound :
    (∀ n : ℕ, f n ≤ 1) ↔ (∀ z : ℤ, f z ≤ 1) := by
  constructor
  · intros h z
    obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
    · exact h n
    · have : ↑((-1 : ℤ) * n) = (-1 : ℚ) * n := by norm_cast
      rw [neg_eq_neg_one_mul, this, f_mul_eq, norm_neg_one_eq_one, one_mul]
      exact h n
  · intros h n
    exact_mod_cast (h n)
