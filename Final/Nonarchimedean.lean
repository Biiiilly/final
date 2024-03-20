import Final.mul_ring_norm_rat
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Normed.Ring.Seminorm
import Mathlib.Data.Nat.Digits

/-!
# Ostrowski's theorem for ℚ

This file states some basic lemmas when the norm is nonarchimedean.

-/

variable {f : MulRingNorm ℚ}

-- If the norm is nonarchimedean, then it's less than one for all naturals.
-- (Done)
lemma nat_norm_le_one (n : ℕ) (harc : is_nonarchimedean f) : f n ≤ 1 :=
by
  induction' n with c hc
  · simp only [Nat.cast_zero, map_zero, zero_le_one]
  · rw [Nat.succ_eq_add_one]
    specialize harc c 1
    rw [map_one] at harc
    simp only [Nat.cast_add, Nat.cast_one]
    exact le_trans harc (max_le hc rfl.ge)

-- If the norm is nonarchimedean, then it's less than one for all integers.
-- (Done)
lemma int_norm_le_one (z : ℤ) (harc : is_nonarchimedean f) : f z ≤ 1 :=
int_norm_bound_iff_nat_norm_bound.mp (λ n ↦ nat_norm_le_one n harc) z

-- If the norm is nonarchimedean, then nontrivial on ℚ implies nontrivial on ℕ.
-- (Not sure whether should be in mathlib or not)
lemma nat_nontriv_of_rat_nontriv (harc : is_nonarchimedean f) (hf : f ≠ 1):
  ∃ n : ℕ, n ≠ 0 ∧ f n < 1 :=
by
  revert hf
  contrapose!
  intro hfnge1
  have hfnateq1 : ∀ n : ℕ, n ≠ 0 → f n = 1
  · intros n hnneq0
    specialize hfnge1 n hnneq0
    have := nat_norm_le_one n harc
    linarith
  ext x
  by_cases h : x = 0
  · simp only [h, map_zero]
  · simp
    rw [← Rat.num_div_den x]
    have hdenomnon0 : (x.den : ℚ) ≠ 0
    · norm_cast
      linarith [x.pos] --probably rw on x.pos
    rw [ring_norm.div_eq (x.num : ℚ) hdenomnon0]
    have H₁ : f x.num = 1
    · have pos_num_f_eq_1 : ∀ a : ℚ , (a.num > 0 → f a.num = 1)
      · intros a num_pos
        have coe_eq : (a.num : ℚ) = (a.num.toNat : ℚ)
        · norm_cast
          exact (Int.toNat_of_nonneg (by linarith)).symm
        rw [coe_eq]
        have a_num_nat_nonzero : a.num.toNat ≠ 0
        · intro H
          rw [Int.toNat_eq_zero] at H
          linarith
        exact hfnateq1 _ a_num_nat_nonzero
      by_cases hsign : x.num ≥ 0
      · apply pos_num_f_eq_1
        rw [Rat.zero_iff_num_zero, ←Ne.def] at h
        exact lt_of_le_of_ne hsign h.symm
      · push_neg at hsign
        rw [←f.toFun_eq_coe]
        rw [←f.neg' x.num]
        rw [f.toFun_eq_coe]
        norm_cast
        rw [←Rat.num_neg_eq_neg_num]
        apply pos_num_f_eq_1
        rw [Rat.num_neg_eq_neg_num]
        exact neg_pos.mpr hsign
    simp [h]
    rw [H₁]
    rw [hfnateq1 x.den (by linarith [x.pos])]
    norm_num at hdenomnon0 ⊢
    simp [hdenomnon0]


-- I couldn't find this lemma in mathlib. A similar version in mathlib is `one_le_prod_of_one_le`.
lemma real.one_le_prod_of_one_le {l : List ℝ} (hl : ∀ x : ℝ, x ∈ l → 1 ≤ x) : 1 ≤ l.prod :=
by
  induction' l with a l ih
  · simp [List.prod_nil]
  · simp only [List.prod_cons]
    have goal := (ih $ λ a ha ↦ hl a $ List.mem_cons_of_mem _ ha)
    have goal1 := (hl _ $ List.mem_cons_self _ _)
    nlinarith

-- Show that there is a prime with norm < 1
-- (Not sure whether should be in mathlib or not)
lemma ex_prime_norm_lt_one (harc : is_nonarchimedean f)
  (h : f ≠ 1) : ∃ (p : ℕ), Fact (Nat.Prime p) ∧ (f p < 1) :=
by
  by_contra x
  simp at x
  obtain ⟨n, hn1, hn2⟩ := nat_nontriv_of_rat_nontriv harc h
  rw [← Nat.prod_factors hn1] at hn2
  have exp : ∀ q : ℕ, q ∈ Nat.factors n → 1 ≤ f q
  · intros q hq
    letI : Fact (Nat.Prime q) := {out := Nat.prime_of_mem_factors hq}
    specialize x q
    exact (x this)
  simp only [Nat.cast_list_prod] at hn2
  let g : MonoidHom ℚ ℝ :=
  { toFun   := f,
    map_one' := f.map_one',
    map_mul' := f.map_mul' }
  have hf_mh: f.toFun = g.toFun := rfl
  rw [← f.toFun_eq_coe, hf_mh, g.toFun_eq_coe, map_list_prod] at hn2
  simp only [List.map_map] at hn2
  have h : ∀ x, (x ∈ (List.map (g ∘ @Nat.cast ℚ Rat.instNatCastRat) n.factors)) → 1 ≤ x
  · intros x hx
    simp only [List.mem_map, Function.comp_apply] at hx
    rcases hx with ⟨a, ha1, ha2⟩
    letI : Fact (Nat.Prime a) := {out := Nat.prime_of_mem_factors ha1}
    specialize exp a ha1
    rw [← ha2]
    convert exp
  suffices goal : (1 : ℝ) ≤ (List.map (g ∘ @Nat.cast ℚ Rat.instNatCastRat) n.factors).prod
  · linarith
  · exact real.one_le_prod_of_one_le h

-- (Not sure whether should be in mathlib or not)
lemma prime_triv_nat_triv (H : ∀ p : ℕ , p.Prime → f p = 1)
  (n : ℕ) (n_pos : n ≠ 0) : f n = 1 :=
by
  induction' n using Nat.strong_induction_on with n hn
  by_cases nge2 : n < 2
  · interval_cases n
    · exfalso
      apply n_pos
      rfl
    · exact f.map_one'
  · push_neg at hn
    have : n ≠ 1
    · intro H
      rw [H] at nge2
      apply nge2
      norm_num
    obtain ⟨p, p_prime, p_div⟩ := Nat.exists_prime_and_dvd this
    obtain ⟨k, hk⟩ := p_div
    rw [hk, Nat.cast_mul, f_mul_eq, H p p_prime, one_mul]
    have k_pos : k ≠ 0
    · intro k_zero
      apply n_pos
      rw [hk]
      rw [k_zero]
      rw [mul_zero]
    have kltn : k < n
    · have := Nat.Prime.two_le p_prime
      rw [hk]
      have ineq1 : 2*k ≤ p*k
      · exact mul_le_mul_right' this k
      have ineq2 : k < 2 * k
      · nth_rewrite 1 [←one_mul k]
        have : 0 < k
        · exact zero_lt_iff.mpr k_pos
        apply (mul_lt_mul_right this).mpr
        norm_num
      exact lt_of_lt_of_le ineq2 ineq1
    exact hn k kltn k_pos
