/-
Copyright (c) 2024 Jiale Miao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiale Miao
-/
import Final.Nonarchimedean
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Ostrowski's theorem for ℚ

## References
* https://kconrad.math.uconn.edu/blurbs/gradnumthy/ostrowskinumbfield.pdf

## Tags
ring_norm, ostrowski
-/

open scoped BigOperators

section Real

/-- The usual absolute value on ℚ. -/
def mul_ring_norm.Real : MulRingNorm ℚ :=
{ toFun     := λ x : ℚ ↦ |x|
  map_zero' := by simp only [Rat.cast_zero, abs_zero]
  add_le'   := norm_add_le
  neg'      := norm_neg
  eq_zero_of_map_eq_zero' :=
  by simp only [abs_eq_zero, Rat.cast_eq_zero, imp_self, forall_const]
  map_one' := by simp [algebraMap.coe_one, abs_one]
  map_mul' := by exact fun x y => Rat.normedField.proof_21 x y
}

@[simp] lemma mul_ring_norm_eq_abs (r : ℚ) : mul_ring_norm.Real r = |r| :=
by
  simp only [Rat.cast_abs]
  rfl

end Real

section padic

/-- The p-adic norm on ℚ. -/
def mul_ring_norm.padic (p : ℕ) [hp : Fact (Nat.Prime p)] : MulRingNorm ℚ :=
{ toFun    := λ x : ℚ ↦ (padicNorm p x: ℝ)
  map_zero' := by simp only [padicNorm.zero, Rat.cast_zero]
  add_le'   := by
    simp
    norm_cast
    exact padicNorm.triangle_ineq
  neg'      := by simp only [padicNorm.neg, eq_self_iff_true, forall_const],
  eq_zero_of_map_eq_zero' := by
    simp
    norm_cast
    exact @padicNorm.zero_of_padicNorm_eq_zero p _
  map_one' := by simp [padicNorm.one]
  map_mul' := by simp only [padicNorm.mul, Rat.cast_mul, eq_self_iff_true, forall_const]
}

@[simp] lemma mul_ring_norm_eq_padic_norm (p : ℕ) [Fact (Nat.Prime p)] (r : ℚ) :
  mul_ring_norm.padic p r = padicNorm p r := rfl

lemma mul_ring_norm.padic_is_nonarchimedean (p : ℕ) [hp : Fact (Nat.Prime p)] :
  is_nonarchimedean (@mul_ring_norm.padic p hp) :=
by
  simp only [is_nonarchimedean_def, mul_ring_norm_eq_padic_norm]
  exact_mod_cast @padicNorm.nonarchimedean p _


end padic

variable {f : MulRingNorm ℚ}

section non_archimedean

-- Show that 𝔞 is an ideal
-- Maybe this should be inserted into the final proof.
def 𝔞 (harc : is_nonarchimedean f) : Ideal ℤ :=
{ carrier := {a : ℤ | f a < 1},
  add_mem' := @λ a b ha hb ↦ by simp only [Set.mem_setOf_eq, Int.cast_add] at ha hb ⊢; linarith [(harc a b), (max_lt ha hb)],
  zero_mem' := by simp only [Set.mem_setOf_eq, Int.cast_zero, map_zero, zero_lt_one],
  smul_mem' := @λ a b hb ↦ by
    simp [Algebra.id.smul_eq_mul, Set.mem_setOf_eq, Int.cast_mul,
    map_mul]
    simp only [Set.mem_setOf_eq] at hb
    refine Right.mul_lt_one_of_le_of_lt_of_nonneg ?ha hb ?b0
    · exact int_norm_le_one a harc
    · exact apply_nonneg f ↑b}

--Maybe this should be inserted into the final proof.
lemma a_proper (harc : is_nonarchimedean f) : 𝔞 harc ≠ (⊤ : Ideal ℤ) :=
by
  rw [Ideal.ne_top_iff_one]
  dsimp only [𝔞, Submodule.mem_mk, Set.mem_setOf_eq, Int.cast_one, not_lt]
  simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq,
    Int.cast_one, map_one, lt_self_iff_false, not_false_eq_true]

-- Show that it contains pZ
-- Maybe this should be inserted into the final proof.
lemma a_contains_prime_ideal (harc : is_nonarchimedean f) (h_nontriv : f ≠ 1) :
  ∃ (p : ℕ), Fact (Nat.Prime p) ∧ 𝔞 harc ≥ Ideal.span {(p : ℤ)} :=
by
  obtain ⟨p, hp, hbound⟩ := ex_prime_norm_lt_one harc h_nontriv
  refine ⟨p, hp, ?_⟩
  apply Ideal.span_le.mpr
  simp only [Set.singleton_subset_iff, SetLike.mem_coe]
  exact hbound

-- Show that it's in Fact equal to pZ (since pZ is a maximal ideal)
-- Maybe this should be inserted into the final proof.
lemma a_eq_prime_ideal (harc : is_nonarchimedean f) (h_nontriv : f ≠ 1) :
  ∃ (p : ℕ), Fact (Nat.Prime p) ∧ 𝔞 harc = Ideal.span {(p : ℤ)} :=
by
  obtain ⟨p, hp, hinc⟩ := a_contains_prime_ideal harc h_nontriv
  refine ⟨p, hp, ((PrincipalIdealRing.isMaximal_of_irreducible
    (Nat.prime_iff_prime_int.mp hp.1).irreducible).eq_of_le (a_proper harc) hinc).symm⟩

-- I will try to see whether there is a similar version of this (hopefully)
lemma mult_finite {a : ℤ} {p : ℕ} (hp : Nat.Prime p) (ha : a ≠ 0) :
  multiplicity.Finite (p : ℤ) a :=
by
  apply multiplicity.finite_int_iff.mpr
  simp only [Int.natAbs_ofNat, ne_eq, hp.ne_one, not_false_eq_true, ha, and_self]

-- the equality at the end of the next lemma
lemma rearrange {p v : ℝ} (m : ℕ) (hp : p > 0) (hlogp : Real.log p ≠ 0) (hv : v > 0) :
  v ^ m = (p ^ m)⁻¹ ^ (-Real.log v / Real.log p) :=
by
  have : p ^ m = p ^ (m : ℝ) := by norm_cast
  rw [←Real.rpow_neg_one, this, ←(Real.rpow_mul (le_of_lt hp)),
    ←(Real.rpow_mul (le_of_lt hp)), neg_div, mul_neg, mul_neg, mul_one, neg_mul, neg_neg,
      mul_div, ←Real.log_rpow hv, Real.rpow_def_of_pos hp, mul_div_left_comm,
        div_self hlogp, mul_one, Real.exp_log]
  · norm_cast
  · norm_cast
    exact pow_pos hv m

-- f a = (f p)^m = ring_norm a
lemma int_val_eq (harc : is_nonarchimedean f) (h_nontriv : f ≠ 1) :
  ∃ (p : ℕ) (hp : Fact (Nat.Prime p)) (s : ℝ) (hs : s > 0),
    ∀ (a : ℤ), f a = (@mul_ring_norm.padic p hp a)^s :=
by
  obtain ⟨p, hp, h_aeq⟩ := a_eq_prime_ideal harc h_nontriv
  refine ⟨p, hp, ?_⟩
  cases' hp with hp
  have fpgt0 := @norm_pos_of_ne_zero f _ (Nat.cast_ne_zero.mpr (ne_of_gt hp.pos))
  let s := (-Real.log (f p : ℝ) / Real.log p)
  have hs : s > 0
  · refine div_pos ?_ (@Real.log_pos p (by exact_mod_cast hp.one_lt))
    · refine neg_pos.mpr ((Real.log_neg_iff fpgt0).mpr ?_)
      have p_mem_a : (p : ℤ) ∈ Ideal.span ({(p : ℤ)} : Set ℤ) := by rw [Ideal.mem_span_singleton]
      rw [←h_aeq] at p_mem_a
      exact p_mem_a
  refine ⟨s, hs, ?_⟩
  intro a
  by_cases ha : a = 0
  · simp_rw [ha, Int.cast_zero, map_zero]
    symm
    apply (Real.zero_rpow)
    linarith
  obtain ⟨b, hapb, hndiv⟩ := multiplicity.exists_eq_pow_mul_and_not_dvd (mult_finite hp ha)
  let m := (multiplicity (p : ℤ) a).get (mult_finite hp ha)
  have : f a = (f p) ^ m
  · rw [hapb]
    have hb : ↑b ∉ 𝔞 harc
    · rw [h_aeq]
      intro hmem
      rw [Ideal.mem_span_singleton'] at hmem
      obtain ⟨k, hk⟩ := hmem
      apply hndiv
      rw [dvd_iff_exists_eq_mul_left]
      refine ⟨k, hk.symm⟩
    dsimp only [𝔞] at hb
    simp only [Int.cast_id, Submodule.mem_mk, Set.mem_setOf_eq, not_lt] at hb
    suffices h'' : f ((p : ℚ) ^ m * (b : ℚ)) = (f (p : ℚ)) ^ m
    · convert h''
      norm_cast
    simp only [AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq, not_lt] at hb
    rw [f_mul_eq, le_antisymm (int_norm_le_one b harc) hb, mul_one, mul_eq_pow]
  rw [this]
  simp only [mul_ring_norm_eq_padic_norm, ne_eq, Int.cast_eq_zero, ha, not_false_eq_true,
    padicNorm.eq_zpow_of_nonzero, padicValRat.of_int, zpow_neg, zpow_coe_nat, Rat.cast_inv,
    Rat.cast_pow, Rat.cast_coe_nat]
  unfold padicValInt padicValNat
  simp [ha, hp.ne_one, Int.natAbs_pos.2 ha, multiplicity.Int.natAbs p a]
  have hppos : (p : ℝ) > 0 := Nat.cast_pos.mpr (hp.pos)
  apply rearrange m hppos _ fpgt0
  rw [Real.log_ne_zero]
  have goal : 2 ≤ (p : ℝ)
  · norm_cast
    exact Nat.Prime.two_le hp
  constructor
  · linarith
  · constructor
    · linarith
    · linarith

lemma cast_pow_sub (r : ℝ) (a b : ℤ) : r ^ (a - b) = r ^ ((a : ℝ) - (b : ℝ)) := by norm_cast

lemma cast_pow (r : ℝ) (a : ℕ) : r ^ a = r ^ (a : ℝ) := by norm_cast

example (q : ℚ) : q.den ≠ 0 :=
by
  exact q.den_nz

-- Extend this to ℚ using div_eq
lemma rat_val_eq (harc : is_nonarchimedean f) (h_nontriv : f ≠ 1) :
  ∃ (p : ℕ) (hp : Fact (Nat.Prime p)) (s : ℝ) (hs : s > 0),
    ∀ (a : ℚ), f a = (@mul_ring_norm.padic p hp a)^s :=
by
  obtain ⟨p, hp, s, hs, h_int⟩ := int_val_eq harc h_nontriv
  refine ⟨p, hp, s, hs, ?_⟩
  intro a
  by_cases ha : a = 0
  · rw [ha, map_zero, map_zero]
    have hs' : s ≠ 0 := by linarith
    exact (Real.zero_rpow hs').symm
  have hcast : f (a.den) = (@mul_ring_norm.padic p hp a.den) ^ s := h_int a.den
  rw [←Rat.num_div_den a, ring_norm.div_eq, h_int, hcast]
  simp only [ha, mul_ring_norm_eq_padic_norm, Rat.num_div_den, padicNorm.eq_zpow_of_nonzero,
    Ne.def, not_false_iff, zpow_neg, Rat.cast_inv, Rat.cast_zpow, Rat.cast_coe_nat]
  unfold padicValRat
  rw [cast_pow_sub, Real.rpow_sub]
  unfold padicNorm
  simp only [Int.cast_eq_zero, Rat.num_ne_zero_of_ne_zero ha, ↓reduceIte, padicValRat.of_int,
    zpow_neg, zpow_coe_nat, Rat.cast_inv, Rat.cast_pow, Rat.cast_coe_nat, Nat.cast_eq_zero,
    Rat.den_nz a, padicValRat.of_nat, Int.cast_ofNat, Real.rpow_nat_cast, inv_div]
  rw [Real.inv_rpow, Real.inv_rpow]
  simp only [inv_div_inv]
  rw [←Real.div_rpow]
  · cases' hp with hp
    rw [cast_pow]
    exact Real.rpow_nonneg (le_of_lt (Nat.cast_pos.mpr hp.pos)) _
  · cases' hp with hp
    rw [cast_pow]
    exact Real.rpow_nonneg (le_of_lt (Nat.cast_pos.mpr hp.pos)) _
  · cases' hp with hp
    rw [cast_pow]
    exact Real.rpow_nonneg (le_of_lt (Nat.cast_pos.mpr hp.pos)) _
  · cases' hp with hp
    rw [cast_pow]
    exact Real.rpow_nonneg (le_of_lt (Nat.cast_pos.mpr hp.pos)) _
  · cases' hp with hp
    exact (Nat.cast_pos.mpr hp.pos)
  · norm_cast
    exact Rat.den_nz a


example (s : ℝ) (h : 0 < s) : s ≠ 0 :=
by
  exact Ne.symm (ne_of_lt h)

-- Finish: hence f and padic are equivalent
lemma f_equiv_padic (harc : is_nonarchimedean f) (h_nontriv : f ≠ 1) :
 ∃ (p : ℕ) (hp : Fact (Nat.Prime p)), mul_ring_norm.equiv f (@mul_ring_norm.padic p hp) :=
by
  obtain ⟨p, hp, s, hs, h⟩ := rat_val_eq harc h_nontriv
  refine ⟨p, hp, 1 / s, ?_⟩
  refine ⟨one_div_pos.mpr hs, ?_⟩
  ext a
  rw [h, ←Real.rpow_mul]
  simp only [mul_ring_norm_eq_padic_norm, one_div, ne_eq, Ne.symm (ne_of_lt hs), not_false_eq_true,
    mul_inv_cancel, Real.rpow_one]
  unfold mul_ring_norm.padic
  simp only [apply_nonneg]

end non_archimedean

section archimedean

-- This should be the same as `Sum_le`
lemma Sum_le' (n : ℕ) (ι : Finset.Iio n → ℚ) :
  f (∑ i : Finset.Iio n, ι i) ≤ ∑ i : Finset.Iio n, f (ι i) :=
by
  sorry

--First limit
lemma limit1 {N : ℝ} (hN : 0 < N) : Filter.Tendsto (λ n : ℕ ↦ N ^ (1 / (n : ℝ))) Filter.atTop (nhds 1) :=
by
  rw [←Real.exp_log hN]
  simp_rw [←Real.exp_mul]
  refine Real.tendsto_exp_nhds_zero_nhds_one.comp ?_
  simp_rw [mul_one_div]
  apply tendsto_const_div_atTop_nhds_zero_nat

--Second limit
lemma limit2 (c : ℝ) (hc : 0 < c) : Filter.Tendsto (λ n : ℕ ↦ (1 + (n : ℝ)*c)^(1 / (n : ℝ))) Filter.atTop (nhds 1) :=
by
  have cne0 : c ≠ 0 := ne_of_gt hc
  have : (λ n : ℕ ↦ (1+(n : ℝ)*c)^(1 / (n : ℝ)))
    = (λ (x : ℝ) ↦ x ^ (1 / ((1 / c) * x  + (- 1) / c))) ∘ (λ y : ℝ ↦ 1 + c*y) ∘ (@Nat.cast ℝ Real.natCast)
  · ext n
    simp
    rw [mul_add, ←mul_assoc]
    simp
    rw [div_eq_mul_inv, add_comm c⁻¹, add_assoc, neg_mul, one_mul,
      add_right_neg, add_zero, inv_mul_cancel cne0, one_mul, mul_comm]
  rw [this]
  have : 1 / c ≠ 0 := one_div_ne_zero cne0
  refine (tendsto_rpow_div_mul_add 1 (1 / c) (-1 / c) this.symm).comp ?_
  have goal : Filter.Tendsto (λ y : ℝ ↦ 1 + c*y) Filter.atTop Filter.atTop
  · apply Filter.tendsto_atTop_add_const_left
    apply Filter.Tendsto.const_mul_atTop hc
    intros _ hx
    exact hx
  refine Filter.Tendsto.comp goal ?_
  exact tendsto_nat_cast_atTop_atTop

--Potentially useful
example : Filter.Tendsto (λ n : ℕ ↦((n : ℝ))^(1 / (n : ℝ))) Filter.atTop (nhds 1) :=
by
  have hf : (λ n : ℕ ↦ (n : ℝ)^(1 / (n : ℝ))) = λ n : ℕ ↦ (((λ x : ℝ ↦ x^(1 / x)) ∘ Nat.cast) n)
  · ext
    simp only [one_div, Function.comp_apply]
  rw [hf]
  apply Filter.Tendsto.comp _ tendsto_nat_cast_atTop_atTop
  exact tendsto_rpow_div

lemma pow_mul_pow_le_max_pow {a b : ℝ} {m n : ℕ} (ha : 0 ≤ a) (hb : 0 ≤ b) : a^m * b^n ≤ max a b ^ (m + n) :=
by
  rw [pow_add]
  apply mul_le_mul
  · exact pow_le_pow_left ha (le_max_left a b) m
  · exact pow_le_pow_left hb (le_max_right a b) n
  · exact pow_nonneg hb n
  · apply pow_nonneg
    rw [le_max_iff]
    left
    exact ha

lemma map_sum_le {R : Type*} [Ring R] (f : MulRingNorm R) (n : ℕ) {ι : ℕ → R} :
  f (∑ i in Finset.range n, ι i) ≤ ∑ i in Finset.range n, f (ι i) :=
by
  induction' n with n hn
  · simp only [Nat.zero_eq, Finset.range_zero, Finset.sum_empty, map_zero, le_refl]
  · rw [Finset.sum_range_succ]
    rw [Finset.sum_range_succ]
    calc
      f (∑ x in Finset.range n, ι x + ι n) ≤
        f (∑ i in Finset.range n, ι i) + f (ι n) := by exact map_add_le_add f (∑ x in Finset.range n, ι x) (ι n)
                                        _  ≤ (∑ i in Finset.range n, f (ι i)) + f (ι n) := add_le_add_right hn _

lemma inter_ineq {n : ℕ} (x y : ℚ) (hf : ∀ m : ℕ, f m ≤ 1) :
  f (x + y)^(n : ℝ) ≤ (n + 1 : ℝ) * max (f x) (f y)^n :=
by
  norm_cast
  rw [←mul_eq_pow, add_pow]
  apply le_trans (map_sum_le f (n + 1))
  suffices goal_1 : ∑ i in Finset.range (n + 1), f (x ^ i * y^(n - i) * (n.choose i))
    = ∑ i in Finset.range (n + 1), f (x ^ i) * f (y ^ (n - i)) * f (n.choose i)
  · rw [goal_1]
    calc
      ∑ i in Finset.range (n + 1), f (x ^ i) * f (y ^ (n - i)) * f (n.choose i)
        ≤ ∑ i in Finset.range (n + 1), f (x ^ i) * f (y ^ (n - i)) :=
          by
            apply Finset.sum_le_sum
            intros i hi
            conv =>
              rhs
              rw [←mul_one (f (x ^ i) * f (y ^ (n - i)))]
            exact mul_le_mul_of_nonneg_left (hf _) (mul_nonneg (apply_nonneg f _) (apply_nonneg f _))
      _ ≤ ∑ i in Finset.range (n + 1), max (f x) (f y) ^ n :=
          by
            apply Finset.sum_le_sum
            intros i hi
            have : i + (n - i) = n
            · rw [add_comm]
              apply Nat.sub_add_cancel
              simp at hi
              linarith
            conv =>
              rhs
              rw [←this]
            repeat
              rw [mul_eq_pow]
            exact pow_mul_pow_le_max_pow (apply_nonneg f x) (apply_nonneg f y)
      _ = ↑(n + 1) * max (f x) (f y) ^ n := by simp
  · congr
    ext
    rw [f_mul_eq, f_mul_eq]

lemma root_ineq {n : ℕ} (x y : ℚ) (hn : n ≠ 0) (hf : ∀ m : ℕ, f m ≤ 1) :
  f (x + y) ≤ (n + 1 : ℝ) ^ (1 / (n : ℝ)) * max (f x) (f y) :=
by
  refine le_of_pow_le_pow_left hn ?_ ?_
  · apply mul_nonneg
    · apply Real.rpow_nonneg
      norm_cast
      linarith
    · rw [le_max_iff]
      left
      exact apply_nonneg f x
  · rw [mul_pow]
    have : 0 ≤ (n : ℝ) + 1
    · norm_cast
      linarith
    nth_rewrite 2 [←Real.rpow_nat_cast]
    rw [←Real.rpow_mul this, one_div]
    have : (n : ℝ) ≠ 0
    · norm_cast
    rw [inv_mul_cancel this, Real.rpow_one, ←Real.rpow_nat_cast]
    exact inter_ineq x y hf

-- A norm is non-archimedean iff it's bounded on the Naturals
lemma non_archimedean_iff_Nat_norm_bound : (∀ n : ℕ, f n ≤ 1) ↔ is_nonarchimedean f :=
by
  constructor
  · intros H x y
    have lim : Filter.Tendsto (λ n : ℕ ↦ (n + 1 : ℝ) ^ (1 / (n : ℝ)) * max (f x) (f y)) Filter.atTop (nhds (max (f x) (f y)))
    · nth_rewrite 2 [←one_mul (max (f x) (f y))]
      apply Filter.Tendsto.mul_const (max (f x) (f y))
      suffices goal_1 : (λ k : ℕ ↦ ((k : ℝ) + 1) ^ (1 / (k : ℝ))) = (λ k : ℕ ↦ (1 + (k : ℝ) * 1) ^ (1 / (k : ℝ)))
      · rw [goal_1]
        exact limit2 1 (Real.zero_lt_one)
      · ext k
        simp
        rw [add_comm]
    apply ge_of_tendsto lim _
    simp only [Filter.eventually_atTop, ge_iff_le]
    use 1
    intros b hb
    have : b ≠ 0 := Nat.one_le_iff_ne_zero.mp hb
    exact root_ineq x y this H
  · intros hf n
    exact nat_norm_le_one n hf

lemma aux1 {n₀ : ℕ} (hf : ∃ n : ℕ, 1 < f n) (dn₀ : n₀ = Nat.find hf) : 1 < n₀ :=
by
  have hn₀ := Nat.find_spec hf
  rw [←dn₀] at hn₀
  by_contra
  rw [lt_iff_not_ge] at hn₀
  interval_cases n₀
  · apply hn₀
    simp only [Nat.cast_zero, map_zero, ge_iff_le, zero_le_one]
  · apply hn₀
    simp [f.map_one']

lemma list.map_with_index_append' {α M : Type*} [AddCommMonoid M]
  (K L : List α) (f : ℕ → α → M) :
  (K ++ L).mapIdx f = K.mapIdx f ++ L.mapIdx (λ i a ↦ f (i + K.length) a) :=
by
  induction' K with a J IH generalizing f
  · simp only [List.nil_append, List.length_nil, add_zero]
    exact rfl
  · specialize IH (λ i ↦ f (i + 1))
    simp only [List.cons_append, List.mapIdx_cons, IH, add_assoc, List.length]

-- This should be the same as `list.map_with_index_sum_to_finset_sum`
lemma list.map_with_index_sum_to_finset_sum' {β A : Type*} [AddCommMonoid A] {f : ℕ → β → A}
  {L : List β}  [Inhabited β] : (L.mapIdx f).sum = ∑ i : Finset.Iio L.length,
    f i ((L.nthLe i (Finset.mem_Iio.1 i.2))) :=
by
  sorry

lemma list.map_with_index_sum_to_finset_sum {β A : Type*} [AddCommMonoid A] {f : ℕ → β → A}
  {L : List β}  [Inhabited β] : (L.mapIdx f).sum = ∑ i in Finset.range L.length,
    f i ((List.get? L i).orElse default).get! :=
by
  refine List.reverseRecOn L ?_ ?_
  · simp
  · intros M a IH
    simp [List.mapIdx_append, IH]
    rw [Finset.sum_range_succ]
    congr 1
    · apply Finset.sum_congr rfl
      intros x hx
      congr 2
      rw [Finset.mem_range] at hx
      -- rw [List.nth_append hx]
      sorry
    · simp only [List.get?_concat_length, Option.some_orElse']
      exact rfl

-- This is lemma 1.1
lemma aux2 {n₀ : ℕ} {α : ℝ} (hf : ∃ n : ℕ, 1 < f n)
  (dn₀ : n₀ = Nat.find hf) (dα : α = Real.log (f n₀) / Real.log n₀) :
    ∀ n : ℕ, f n ≤ n ^ α :=
by
  have : f n₀ = n₀ ^ α
  · rw [dα, Real.log_div_log]
    apply Eq.symm
    apply Real.rpow_logb
    · norm_cast
      exact lt_trans zero_lt_one (aux1 hf dn₀)
    · apply ne_of_gt
      norm_cast
      exact aux1 hf dn₀
    · have hn₀ := Nat.find_spec hf
      rw [←dn₀] at hn₀
      exact lt_trans zero_lt_one hn₀
  have hα : 0 < α
  · rw [dα]
    apply div_pos
    · apply Real.log_pos
      rw [dn₀]
      exact Nat.find_spec hf
    · apply Real.log_pos
      norm_cast
      exact aux1 hf dn₀
  let C : ℝ := ((n₀ : ℝ) ^ α) / ((n₀ : ℝ) ^ α - 1)
  have dc : C = ((n₀ : ℝ) ^ α) / ((n₀ : ℝ) ^ α - 1) := rfl
  have hC : 0 < C
  · rw [dc]
    rw [← this]
    have hn₀ := Nat.find_spec hf
    rw [←dn₀] at hn₀
    apply div_pos
    linarith
    linarith
  suffices : ∀ n : ℕ, f n ≤ C * ((n : ℝ) ^ α)
  · intro n
    have limit' : Filter.Tendsto (λ N : ℕ ↦ C ^ (1 / (N : ℝ))) Filter.atTop (nhds 1)
    · exact limit1 hC
    have limit'' : Filter.Tendsto
      (λ N : ℕ ↦ (C ^ (1 / (N : ℝ))) * (n ^ α)) Filter.atTop (nhds (n ^ α))
    · have := Filter.Tendsto.mul_const ((n : ℝ) ^ α) limit'
      simp at this
      simp
      exact this
    have stupid : (0 : ℝ) ≤ n := by norm_cast; exact zero_le n
    have aux : ∀ N : ℕ, (f (n)) ^ (N : ℝ) ≤ C * ((n ^ α) ^ (N : ℝ))
    · intro N
      rw [←Real.rpow_mul stupid]
      nth_rewrite 2 [mul_comm]
      rw [Real.rpow_mul stupid]
      norm_cast
      rw [←mul_eq_pow]
      specialize this (n ^ N)
      norm_cast
    have aux1 : ∀ N : ℕ, 0 < N → f (n) ≤ (C ^ (1 / (N : ℝ))) * (n ^ α)
    · intros N hN
      have hN₁ : N ≠ 0 := by linarith
      refine le_of_pow_le_pow_left hN₁ ?_ ?_
      · apply mul_nonneg
        · apply le_of_lt
          exact Real.rpow_pos_of_pos hC _
        · exact Real.rpow_nonneg stupid _
      { rw [mul_pow]
        rw [←Real.rpow_nat_cast]
        rw [←Real.rpow_nat_cast]
        rw [←Real.rpow_nat_cast]
        rw [←Real.rpow_mul (le_of_lt hC), one_div]
        have : (N : ℝ) ≠ 0
        · norm_cast
        rw [inv_mul_cancel this, Real.rpow_one]
        exact aux N }
    apply ge_of_tendsto limit'' _
    simp only [Filter.eventually_atTop, ge_iff_le]
    use 1
    intros b hb
    have : 0 < b := (by linarith)
    exact aux1 b this
  intro n
  by_cases h : n = 0
  · subst h
    simp [hα]
    nlinarith [hC, Real.zero_rpow_nonneg α]
  have length_lt_one : 0 ≤ ((n₀.digits n).length : ℝ) - 1 -- Not sure whether this is useful or not
  · norm_num
    sorry -- should be easy `digits_ne_nil_iff_ne_zero` might be useful
  conv_lhs =>
    rw [←Nat.ofDigits_digits n₀ n]
  rw [Nat.ofDigits_eq_sum_mapIdx]
  rw [list.map_with_index_sum_to_finset_sum']
  simp only [Finset.univ_eq_attach, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow]
  apply le_trans (Sum_le' (n₀.digits n).length _)
  have aux' : 2 ≤ n₀ := by linarith [aux1 hf dn₀]
  have aux'' : 2 ≤ (n₀ : ℝ) := by norm_cast
  suffices goal_1 : ∑ i : Finset.Iio (n₀.digits n).length,
    f (((((n₀.digits n).nthLe i (Finset.mem_Iio.1 i.2))) : ℚ)
      * (n₀ : ℚ) ^ (i : ℕ)) = ∑ i : Finset.Iio (n₀.digits n).length,
        f (((n₀.digits n).nthLe i (Finset.mem_Iio.1 i.2)))
          * (f n₀) ^ (i : ℕ)
  · rw [goal_1]
    have coef_ineq : ∀ i : Finset.Iio (n₀.digits n).length,
      f (((n₀.digits n).nthLe i (Finset.mem_Iio.1 i.2))) ≤ 1
    · intro i
      have : ((n₀.digits n).nthLe i (Finset.mem_Iio.1 i.2)) < n₀
      · have aux'' : ((n₀.digits n).nthLe i (Finset.mem_Iio.1 i.2)) ∈ n₀.digits n
        · exact (Nat.digits n₀ n).nthLe_mem ↑i (Finset.mem_Iio.mp i.property)
        exact Nat.digits_lt_base aux' aux''
      apply le_of_not_gt
      subst dn₀
      rw [gt_iff_lt]
      exact Nat.find_min hf this
    rw [this]
    have goal1 : ∑ i : (Finset.Iio (n₀.digits n).length),
      f ((n₀.digits n).nthLe ↑i (Finset.mem_Iio.1 i.2)) * (n₀ ^ α) ^ (i : ℕ) ≤
        ∑ i : (Finset.Iio (n₀.digits n).length), ((n₀ : ℝ) ^ α) ^ (i : ℕ)
    · sorry
    apply le_trans goal1
    have goal2 : (∑ i : (Finset.Iio (n₀.digits n).length), ((n₀ : ℝ) ^ α) ^ (i : ℕ)) =
    (((n₀ : ℝ) ^ (α * ((n₀.digits n).length - 1))) *
      ∑ i : (Finset.Iio (n₀.digits n).length), ((n₀ : ℝ) ^ (-α)) ^ (i : ℕ))
    · sorry
    rw [goal2]
    have goal3 : ((n₀ : ℝ) ^ (α * (((n₀.digits n).length - 1))))
      * (∑ i : (Finset.Iio (n₀.digits n).length), ((n₀ : ℝ) ^ (-α)) ^ (i : ℕ))
        ≤ ((n₀ : ℝ) ^ (α * (((n₀.digits n).length - 1)))) *
          (∑'i : ℕ, (1 / ((n₀ : ℝ) ^ α)) ^ i)
    · rw [mul_le_mul_left]
      · -- apply sum_le_tsum (Finset.Iio (n₀.digits n).length)
        simp only [Finset.univ_eq_attach, one_div, inv_pow]
        have goal : ∑ i in Finset.attach (Finset.Iio (List.length (Nat.digits n₀ n))),
          ((n₀ : ℝ) ^ (-α)) ^ (i : ℕ) = ∑ i in Finset.Iio (List.length (Nat.digits n₀ n)),
            (((n₀ : ℝ) ^ α) ^ i)⁻¹
        ·
          sorry
        rw [goal]
        refine sum_le_tsum _ ?_ ?_
        · intro i hi
          apply le_of_lt
          apply inv_pos_of_pos
          apply pow_pos _ i
          apply Real.rpow_pos_of_pos _ α
          linarith
        · have aux : (fun i => (((n₀ : ℝ) ^ α) ^ i)⁻¹) = (fun i => (((n₀ : ℝ) ^ (-α)) ^ i))
          · ext i
            rw [Real.rpow_neg (by linarith)]
            field_simp
          rw [aux]
          refine summable_geometric_of_lt_one ?_ ?_
          ·
            sorry
          · rw [Real.rpow_neg (by linarith)]
            field_simp
            rw [one_div_lt_of_neg]
            · sorry
            · sorry
            · sorry
        --have hf : Summable f := sorry
        --have hf₁ : ∀ i ∉ (Finset.attach (Finset.Iio (List.length (Nat.digits n₀ n)))), 0 ≤ f i := sorry
        -- refine sum_le_tsum (Finset.attach (Finset.Iio (List.length (Nat.digits n₀ n)))) hf₁ _
      ·
        sorry
    apply le_trans goal3
    have goal4 : ∑'i : ℕ, (1 / ((n₀ : ℝ) ^ α)) ^ i = C
    · rw [tsum_geometric_of_abs_lt_one]
      · field_simp
      · rw [abs_lt]
        constructor
        · suffices goal : 0 < 1 / (n₀ : ℝ) ^ α
          · linarith
          rw [one_div_pos]
          apply Real.rpow_pos_of_pos _ α
          linarith
        · rw [one_div_lt]
          · field_simp
            exact Real.one_lt_rpow (by linarith) hα
          · apply Real.rpow_pos_of_pos _ α
            linarith
          · linarith
    rw [goal4]
    rw [mul_comm]
    suffices : (n₀ : ℝ) ^ (α * (((n₀.digits n).length - 1))) ≤ (n : ℝ) ^ α
    · nlinarith
    have goal : (n₀ : ℝ) ^ (((n₀.digits n).length : ℝ) - 1) ≤ (n : ℝ)
    · have h' := Nat.base_pow_length_digits_le n₀ n aux' h
      have h'' : (n₀ : ℝ) ^ ((n₀.digits n).length : ℝ) ≤ (n₀ : ℝ) * (n : ℝ)
      · norm_cast
      have aux'' : 0 < (n₀ : ℝ) := by norm_cast;linarith
      have stupid : (n₀ : ℝ) ≠ 0 := by norm_cast;linarith
      have h''' : 0 ≤ (n₀ : ℝ) ^ (-(1 : ℝ))
      · rw [Real.rpow_neg_one]
        have stupid2 : 0 ≤ (n₀ : ℝ)⁻¹ * n₀ := by simp [inv_mul_cancel stupid]
        exact nonneg_of_mul_nonneg_left stupid2 aux''
      have h'''' := mul_le_mul_of_nonneg_left h'' h'''
      rw [←Real.rpow_add aux'' _ _] at h''''
      rw [add_comm] at h''''
      rw [←mul_assoc] at h''''
      apply le_trans h''''
      rw [Real.rpow_neg_one]
      rw [inv_mul_cancel stupid]
      linarith
    have stupid : (0 : ℝ) ≤ n₀ := sorry -- easy
    rw [mul_comm]
    rw [Real.rpow_mul stupid]
    have stupid2 : 0 ≤ (n₀ : ℝ) ^ (((n₀.digits n).length : ℝ) - 1) := sorry --easy
    exact Real.rpow_le_rpow stupid2 goal (le_of_lt hα)
  · congr
    ext
    rw [f_mul_eq, mul_eq_pow]

-- This is lemma 1.2 (this looks hard btw)
lemma aux3 {n₀ : ℕ} {α : ℝ} (hf : ∃ n : ℕ, 1 < f n)
  (dn₀ : n₀ = Nat.find hf) (dα : α = Real.log (f n₀) / Real.log n₀) :
    ∀ n : ℕ, (n ^ α : ℝ) ≤ f n :=
by
  have hα₀ : 0 < α
  · rw [dα]
    apply div_pos
    · apply Real.log_pos
      rw [dn₀]
      exact Nat.find_spec hf
    · apply Real.log_pos
      norm_cast
      exact aux1 hf dn₀
  have hα : 0 ≤ α := by linarith
  have hn₀ : 2 ≤ n₀ := by linarith [aux1 hf dn₀]
  have : f n₀ = n₀ ^ α := sorry -- same proof as above
  let C : ℝ := (1 - (1 - 1 / n₀) ^ α)
  have hC : 0 ≤ C
  · dsimp only [C]
    have hn₀1 : (2 : ℝ) ≤ (n₀ : ℝ) := by norm_cast
    field_simp
    apply Real.rpow_le_one _ _ hα
    · apply le_of_lt
      apply div_pos
      · linarith
      · linarith
    · rw [div_le_one]
      · linarith
      · linarith
  suffices : ∀ n : ℕ, C * ((n : ℝ) ^ α) ≤ f n
  · sorry -- This should be almost the same as above
  intros n
  by_cases hn : n = 0
  · subst hn
    simp only [CharP.cast_eq_zero, map_zero]
    rw [Real.zero_rpow]
    · rw [mul_zero]
    linarith
  have length_lt_one : 1 ≤ (n₀.digits n).length
  · by_contra goal
    simp only [not_le, Nat.lt_one_iff] at goal
    rw [List.length_eq_zero, Nat.digits_eq_nil_iff_eq_zero] at goal
    contradiction
  have h₁ : f ((n₀ : ℚ) ^ ((n₀.digits n).length))
    - f (((n₀ : ℚ) ^ ((n₀.digits n).length)) - n) ≤ f n
  · have goal := abs_sub_map_le_sub f ((n₀ : ℚ) ^ ((n₀.digits n).length)) (((n₀ : ℚ) ^ ((n₀.digits n).length)) - n)
    simp only [map_pow, sub_sub_cancel] at goal
    apply le_trans _ goal
    rw [map_pow]
    exact le_abs_self _
  apply le_trans' h₁
  rw [mul_eq_pow, this]
  have h := aux2 hf dn₀ dα
  specialize h ((n₀ ^ ((n₀.digits n).length)) - n)
  have hn₁ : n ≤ n₀ ^ (n₀.digits n).length := by linarith [@Nat.lt_base_pow_length_digits n₀ n hn₀]
  have h₂ : ((n₀ : ℝ) ^ α) ^ (n₀.digits n).length - ((n₀ ^ (n₀.digits n).length - n) : ℚ) ^ α ≤
  ((n₀ : ℝ) ^ α) ^ (n₀.digits n).length - f ((n₀ : ℚ) ^ (n₀.digits n).length - (n : ℚ))
  · rw [sub_le_sub_iff_left]
    simp only [Rat.cast_sub, Rat.cast_pow, Rat.cast_coe_nat]
    push_cast [hn₁] at h
    exact h
  apply le_trans' h₂
  simp only [Rat.cast_sub, Rat.cast_pow, Rat.cast_coe_nat]
  have h₃ : ((n₀ : ℝ) ^ α) ^ (n₀.digits n).length - ((n₀ : ℝ) ^ (n₀.digits n).length - (n₀ : ℝ) ^ ((n₀.digits n).length - 1)) ^ α ≤
    ((n₀ : ℝ) ^ α) ^ (n₀.digits n).length - ((n₀ : ℝ) ^ (n₀.digits n).length - (n : ℝ)) ^ α
  · rw [sub_le_sub_iff_left]
    apply Real.rpow_le_rpow _ _ hα
    · norm_cast
      linarith
    · suffices goal : (n₀ : ℝ) ^ List.length (Nat.digits n₀ n)  ≤
                        (n₀ : ℝ) ^ List.length (Nat.digits n₀ n) + ((n : ℝ) - (n₀ : ℝ) ^ (List.length (Nat.digits n₀ n) - 1))
      · linarith
      simp only [le_add_iff_nonneg_right, sub_nonneg]
      norm_cast
      rw [← Nat.pow_div length_lt_one]
      · simp only [pow_one]
        exact Nat.div_le_of_le_mul (Nat.base_pow_length_digits_le n₀ n hn₀ hn)
      linarith
  apply le_trans' h₃
  have h₄ : ((n₀ : ℝ) ^ α) ^ (n₀.digits n).length -
    ((n₀ : ℝ) ^ (n₀.digits n).length - (n₀ : ℝ) ^ ((n₀.digits n).length - 1)) ^ α
      = (((n₀ : ℝ) ^ α) ^ (n₀.digits n).length) * (1 - (1 - 1 / n₀) ^ α)
  · rw [mul_sub]
    rw [mul_one]
    rw [sub_right_inj]
    rw [←Real.rpow_nat_cast]
    rw [←Real.rpow_nat_cast]
    rw [←Real.rpow_nat_cast]
    rw [←Real.rpow_mul]  -- This looks stupid here, as I am looking for (a ^ b) ^ c = (a ^ c) ^ b
    · nth_rewrite 2 [mul_comm]
      rw [Real.rpow_mul]
      · rw [←Real.mul_rpow]
        · rw [mul_sub]
          rw [mul_one]
          rw [Nat.cast_sub length_lt_one]
          rw [Real.rpow_sub]
          · ring_nf
            simp only [algebraMap.coe_one, Real.rpow_one]
          norm_cast
          linarith [aux1 hf dn₀]
        · norm_cast
          linarith [Nat.one_le_pow ((n₀.digits n).length)
            n₀ (by linarith [aux1 hf dn₀])]
        · simp only [sub_nonneg]
          rw [one_div_le]
          · simp only [div_self, Ne.def, one_ne_zero, not_false_iff, Nat.one_le_cast]
            linarith [aux1 hf dn₀]
          · norm_cast
            linarith [aux1 hf dn₀]
          · linarith
      norm_cast
      exact Nat.zero_le n₀
    norm_cast
    exact Nat.zero_le n₀
  rw [h₄]
  nth_rewrite 2 [mul_comm]
  apply mul_le_mul_of_nonneg_left _ hC
  suffices goal : (n : ℝ )^ α ≤ ((n₀ : ℝ) ^ (n₀.digits n).length) ^ α
  · rw [←Real.rpow_nat_cast] at goal ⊢
    rw [←Real.rpow_mul] -- This looks stupid here, as I am looking for (a ^ b) ^ c = (a ^ c) ^ b
    · rw [mul_comm]
      rw [Real.rpow_mul]
      · exact goal
      norm_cast
      exact Nat.zero_le n₀
    norm_cast
    exact Nat.zero_le n₀
  apply Real.rpow_le_rpow
  · norm_cast
    exact Nat.zero_le n
  · norm_cast
  · exact hα

lemma archimedean_case (hf : ¬ is_nonarchimedean f) : mul_ring_norm.equiv f mul_ring_norm.Real :=
by
  rw [←non_archimedean_iff_Nat_norm_bound] at hf
  simp only [not_forall, not_le] at hf
  let n₀ : ℕ := Nat.find hf
  have dn₀ : n₀ = Nat.find hf := rfl
  let α : ℝ := Real.log (f n₀) / Real.log n₀
  have hα : α =  Real.log (f n₀) / Real.log n₀ := rfl
  have h₃ : ∀ (n : ℕ), f (n : ℚ) = (n : ℝ) ^ α
  · intro n
    linarith [aux3 hf dn₀ hα n, aux2 hf dn₀ hα n]
  have h₄ : ∀ (n : ℕ), f (n : ℚ) = |(n : ℝ)| ^ α
  · intro n
    rw [Nat.abs_cast n]
    exact h₃ n
  apply mul_ring_norm.equiv_symm _
  refine ⟨α, ?_, ?_⟩
  · rw [hα]
    apply div_pos
    · apply Real.log_pos
      exact Nat.find_spec hf
    · apply Real.log_pos
      norm_cast
      exact aux1 hf dn₀
  · ext x
    rw [mul_ring_norm_eq_abs]
    rw [←Rat.num_div_den x]
    norm_cast
    rw [←Rat.coe_int_div_eq_divInt]
    rw [abs_div]
    push_cast
    rw [ring_norm.div_eq]
    · rw [Real.div_rpow]
      · congr
        · cases' x.num with b b
          · simp only [Int.ofNat_eq_coe, Int.cast_ofNat]
            exact (h₄ b).symm
          · simp only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one, neg_add_rev]
            rw [←abs_neg]
            rw [←map_neg_eq_map]
            simp only [neg_add_rev, neg_neg]
            norm_cast
            exact (h₃ (b + 1)).symm
        · exact (h₄ x.den).symm
      · exact norm_nonneg ((x.num) : ℝ)
      · exact norm_nonneg ((x.den) : ℝ)
    · norm_cast
      exact Rat.den_nz x

end archimedean

/-- Ostrowski's Theorem -/
theorem rat_ring_norm_p_adic_or_Real (f : MulRingNorm ℚ) (hf_nontriv : f ≠ 1) :
  (mul_ring_norm.equiv f mul_ring_norm.Real) ∨
  ∃ (p : ℕ) (hp : Fact (Nat.Prime p)), mul_ring_norm.equiv f (@mul_ring_norm.padic p hp) :=
by
    by_cases bdd : ∀ z : ℕ, f z ≤ 1
    · right /- p-adic case -/
      rw [non_archimedean_iff_Nat_norm_bound] at bdd
      exact f_equiv_padic bdd hf_nontriv
    · left
      rw [non_archimedean_iff_Nat_norm_bound] at bdd
      exact archimedean_case bdd /- Euclidean case -/
