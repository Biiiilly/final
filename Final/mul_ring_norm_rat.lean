import Mathlib.Tactic
import Final.Basic
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Normed.Ring.Seminorm
import Mathlib.Data.Nat.Digits

/-!
# Ostrowski's theorem for ℚ

This file states some basic lemmas about mul_ring_norm ℚ

-/

variable {f : MulRingNorm ℚ}

-- TODO: remove this
-- I think this is a missing lemma in mathlib and maybe we can use this for now.
-- (Done)
lemma f_mul_eq : mul_eq f := f.map_mul'

-- The norm of -1 is 1
-- (Done)
lemma norm_neg_one_eq_one : f (-1) = 1 :=
by
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

-- If x is non-zero, then the norm of x is larger than zero.
-- (Done)
lemma norm_pos_of_ne_zero {x : ℚ} (h : x ≠ 0) : f x > 0 :=
lt_of_le_of_ne (apply_nonneg f x) (λ h' ↦ h (f.eq_zero_of_map_eq_zero' x h'.symm))

--TODO: generalise to division rings, get rid of field_simp
-- (Done)
lemma ring_norm.div_eq (p : ℚ) {q : ℚ} (hq : q ≠ 0) : f (p / q) = (f p) / (f q) :=
by
  have H : f q ≠ 0
  · intro fq0
    have := f.eq_zero_of_map_eq_zero' q fq0
    exact hq this
  calc
    f (p / q) = f (p / q) * f q / f q := by field_simp
            _ = f (p / q * q)  / f q  := by simp
            _ = f p / f q := by field_simp


-- This lemma look a bit strange to me.
-- (Done)
lemma int_norm_bound_iff_nat_norm_bound :
  (∀ n : ℕ, f n ≤ 1) ↔ (∀ z : ℤ, f z ≤ 1) :=
by
  constructor
  · intros h z
    obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
    · exact h n
    · have : ↑((-1 : ℤ) * n) = (-1 : ℚ) * n := by norm_cast
      rw [neg_eq_neg_one_mul, this, f_mul_eq, norm_neg_one_eq_one, one_mul]
      exact h n
  · intros h n
    exact_mod_cast (h n)

-- (Done)
lemma mul_eq_pow {a : ℚ} {n : ℕ} : f (a ^ n) = (f a) ^ n :=
by
  induction' n with d hd
  simp only [pow_zero]
  exact f.map_one'
  rw [pow_succ, pow_succ, ←hd, f_mul_eq]

example (s : Finset ℕ) (f g : ℕ → ℝ) (h : ∀ i ∈ s, f i = g i) : (Finset.sum s fun i => f i) = Finset.sum s fun i => g i :=
by
  exact Finset.sum_congr rfl h
