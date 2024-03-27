import Final.Nonarchimedean
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.Analysis.SpecialFunctions.Log.Base


/-!
# Ostrowski's theorem for ℚ

## References
* https://kconrad.math.uconn.edu/blurbs/gradnumthy/ostrowskinumbfield.pdf
* https://proofwiki.org/wiki/Ostrowski%27s_Theorem

-/

open scoped BigOperators

section Real

/-- The usual absolute value on ℚ. -/
def MulRingNorm.Real : MulRingNorm ℚ :=
{ toFun     := λ x : ℚ ↦ |x|
  map_zero' := by simp only [Rat.cast_zero, abs_zero]
  add_le'   := norm_add_le
  neg'      := norm_neg
  eq_zero_of_map_eq_zero' := by simp only [abs_eq_zero, Rat.cast_eq_zero, imp_self, forall_const]
  map_one' := by simp [algebraMap.coe_one, abs_one]
  map_mul' := by exact fun x y => Rat.normedField.proof_21 x y
}

@[simp] lemma MulRingNorm_eq_abs (r : ℚ) : MulRingNorm.Real r = |r| := by simp only [Rat.cast_abs]; rfl

end Real

section padic

/-- The p-adic norm on ℚ. -/
def MulRingNorm.padic (p : ℕ) [hp : Fact (Nat.Prime p)] : MulRingNorm ℚ :=
{ toFun    := λ x : ℚ ↦ (padicNorm p x: ℝ)
  map_zero' := by simp only [padicNorm.zero, Rat.cast_zero]
  add_le'   := by
    simp only
    norm_cast
    exact padicNorm.triangle_ineq
  neg'      := by simp only [padicNorm.neg, eq_self_iff_true, forall_const]
  eq_zero_of_map_eq_zero' := by
    simp only
    norm_cast
    exact @padicNorm.zero_of_padicNorm_eq_zero p _
  map_one' := by simp only [ne_eq, one_ne_zero, not_false_eq_true, padicNorm.eq_zpow_of_nonzero,
    padicValRat.one, neg_zero, zpow_zero, Rat.cast_one]
  map_mul' := by simp only [padicNorm.mul, Rat.cast_mul, eq_self_iff_true, forall_const]
}

@[simp] lemma MulRingNorm_eq_padicNorm (p : ℕ) [Fact (Nat.Prime p)] (r : ℚ) :
  MulRingNorm.padic p r = padicNorm p r := rfl

lemma MulRingNorm.padic_nonarchimedean (p : ℕ) [hp : Fact (Nat.Prime p)] :
    Nonarchimedean (@MulRingNorm.padic p hp) := by
  simp only [Nonarchimedean_def, MulRingNorm_eq_padicNorm]
  exact_mod_cast @padicNorm.nonarchimedean p _

end padic

variable {f : MulRingNorm ℚ}

section non_archimedean

-- Show that 𝔞 is an ideal
def 𝔞 (harc : Nonarchimedean f) : Ideal ℤ :=
{ carrier := {a : ℤ | f a < 1},
  add_mem' := @λ a b ha hb ↦ by simp only [Set.mem_setOf_eq, Int.cast_add] at ha hb ⊢; linarith [(harc a b), (max_lt ha hb)],
  zero_mem' := by simp only [Set.mem_setOf_eq, Int.cast_zero, map_zero, zero_lt_one],
  smul_mem' := @λ a b hb ↦ by
    simp only [smul_eq_mul, Set.mem_setOf_eq, Int.cast_mul, map_mul]
    simp only [Set.mem_setOf_eq] at hb
    exact Right.mul_lt_one_of_le_of_lt_of_nonneg (int_norm_le_one a harc) hb (apply_nonneg f ↑b) }

lemma a_proper (harc : Nonarchimedean f) : 𝔞 harc ≠ (⊤ : Ideal ℤ) := by
  rw [Ideal.ne_top_iff_one]
  dsimp only [𝔞, Submodule.mem_mk, Set.mem_setOf_eq, Int.cast_one, not_lt]
  simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq,
    Int.cast_one, map_one, lt_self_iff_false, not_false_eq_true]

-- Show that it contains pZ
lemma a_contains_primeIdeal (harc : Nonarchimedean f) (h_nontriv : f ≠ 1) :
    ∃ (p : ℕ), Fact (Nat.Prime p) ∧ 𝔞 harc ≥ Ideal.span {(p : ℤ)} := by
  obtain ⟨p, hp, hbound⟩ := ex_prime_norm_lt_one harc h_nontriv
  refine ⟨p, hp, ?_⟩
  apply Ideal.span_le.mpr
  simp only [Set.singleton_subset_iff, SetLike.mem_coe]
  exact hbound

-- Show that it's in Fact equal to pZ (since pZ is a maximal ideal)
lemma a_eq_primeIdeal (harc : Nonarchimedean f) (h_nontriv : f ≠ 1) :
    ∃ (p : ℕ), Fact (Nat.Prime p) ∧ 𝔞 harc = Ideal.span {(p : ℤ)} := by
  obtain ⟨p, hp, hinc⟩ := a_contains_primeIdeal harc h_nontriv
  refine ⟨p, hp, ((PrincipalIdealRing.isMaximal_of_irreducible
    (Nat.prime_iff_prime_int.mp hp.1).irreducible).eq_of_le (a_proper harc) hinc).symm⟩

-- the equality at the end of the next lemma
lemma rearrange {p v : ℝ} (m : ℕ) (hp : p > 0) (hlogp : Real.log p ≠ 0) (hv : v > 0) :
    v ^ m = (p ^ m)⁻¹ ^ (-Real.log v / Real.log p) := by
  have : p ^ m = p ^ (m : ℝ) := by norm_cast
  rw [← Real.rpow_neg_one, this, ← (Real.rpow_mul (le_of_lt hp)),
    ← (Real.rpow_mul (le_of_lt hp)), neg_div, mul_neg, mul_neg, mul_one, neg_mul, neg_neg,
      mul_div, ← Real.log_rpow hv, Real.rpow_def_of_pos hp, mul_div_left_comm,
        div_self hlogp, mul_one, Real.exp_log]
  · norm_cast
  · norm_cast
    exact pow_pos hv m

-- f a = (f p)^m = ring_norm a
lemma int_val_eq (harc : Nonarchimedean f) (h_nontriv : f ≠ 1) :
    ∃ (p : ℕ) (hp : Fact (Nat.Prime p)) (s : ℝ) (_ : s > 0),
      ∀ (a : ℤ), f a = (@MulRingNorm.padic p hp a)^s := by
  obtain ⟨p, hp, h_aeq⟩ := a_eq_primeIdeal harc h_nontriv
  let hp₀ := hp
  refine ⟨p, hp, ?_⟩
  cases' hp with hp
  have fpgt0 := map_pos_of_ne_zero f (Nat.cast_ne_zero.mpr (ne_of_gt hp.pos))
  let s := (- Real.log (f p : ℝ) / Real.log p)
  have hs : s > 0
  · refine div_pos ?_ (@Real.log_pos p (by exact_mod_cast hp.one_lt))
    · refine neg_pos.mpr ((Real.log_neg_iff fpgt0).mpr ?_)
      have p_mem_a : (p : ℤ) ∈ Ideal.span ({(p : ℤ)} : Set ℤ) := by rw [Ideal.mem_span_singleton]
      rw [← h_aeq] at p_mem_a
      exact p_mem_a
  refine ⟨s, hs, ?_⟩
  intro a
  by_cases ha : a = 0
  · simp_rw [ha, Int.cast_zero, map_zero]
    symm
    apply (Real.zero_rpow)
    linarith
  obtain ⟨b, hapb, hndiv⟩ := multiplicity.exists_eq_pow_mul_and_not_dvd ((@padicValRat.finite_int_prime_iff _ hp₀ _).2 ha)
  let m := (multiplicity (p : ℤ) a).get ((@padicValRat.finite_int_prime_iff _ hp₀ _).2 ha)
  have : f a = (f p) ^ m
  · rw [hapb]
    have hb : b ∉ 𝔞 harc
    · rw [h_aeq]
      intro hmem
      obtain ⟨k, hk⟩ := Ideal.mem_span_singleton'.1 hmem
      apply hndiv
      rw [dvd_iff_exists_eq_mul_left]
      refine ⟨k, hk.symm⟩
    dsimp only [𝔞] at hb
    simp only [Int.cast_id, Submodule.mem_mk, Set.mem_setOf_eq, not_lt] at hb
    suffices h'' : f ((p : ℚ) ^ m * (b : ℚ)) = (f (p : ℚ)) ^ m
    · convert h''
      norm_cast
    simp only [AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq, not_lt] at hb
    rw [f_mul_eq, le_antisymm (int_norm_le_one b harc) hb, mul_one, map_pow]
  rw [this]
  simp only [MulRingNorm_eq_padicNorm, ne_eq, Int.cast_eq_zero, ha, not_false_eq_true,
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

-- Extend this to ℚ using div_eq
lemma rat_val_eq (harc : Nonarchimedean f) (h_nontriv : f ≠ 1) :
    ∃ (p : ℕ) (hp : Fact (Nat.Prime p)) (s : ℝ) (_ : s > 0),
      ∀ (a : ℚ), f a = (@MulRingNorm.padic p hp a) ^ s := by
  obtain ⟨p, hp, s, hs, h_int⟩ := int_val_eq harc h_nontriv
  refine ⟨p, hp, s, hs, ?_⟩
  intro a
  by_cases ha : a = 0
  · rw [ha, map_zero, map_zero]
    have hs' : s ≠ 0 := by linarith
    exact (Real.zero_rpow hs').symm
  have hcast : f (a.den) = (@MulRingNorm.padic p hp a.den) ^ s := h_int a.den
  rw [← Rat.num_div_den a, map_div₀, h_int, hcast]
  simp only [ha, MulRingNorm_eq_padicNorm, Rat.num_div_den, padicNorm.eq_zpow_of_nonzero,
    Ne.def, not_false_iff, zpow_neg, Rat.cast_inv, Rat.cast_zpow, Rat.cast_coe_nat]
  unfold padicValRat
  rw [(Real.rpow_int_cast _ _).symm]
  push_cast
  rw [Real.rpow_sub]
  unfold padicNorm
  simp only [Int.cast_eq_zero, Rat.num_ne_zero_of_ne_zero ha, ↓reduceIte, padicValRat.of_int,
    zpow_neg, zpow_coe_nat, Rat.cast_inv, Rat.cast_pow, Rat.cast_coe_nat, Nat.cast_eq_zero,
    Rat.den_nz a, padicValRat.of_nat, Int.cast_ofNat, Real.rpow_nat_cast, inv_div]
  rw [Real.inv_rpow, Real.inv_rpow]
  simp only [inv_div_inv]
  rw [← Real.div_rpow]
  repeat
    rw [(Real.rpow_nat_cast _ _).symm]
    exact Real.rpow_nonneg (le_of_lt (Nat.cast_pos.mpr hp.1.pos)) _
  exact (Nat.cast_pos.mpr hp.1.pos)

-- Finish: hence f and padic are equivalent
lemma f_equiv_padic (harc : Nonarchimedean f) (h_nontriv : f ≠ 1) :
    ∃ (p : ℕ) (hp : Fact (Nat.Prime p)), MulRingNorm.equiv f (@MulRingNorm.padic p hp) := by
  obtain ⟨p, hp, s, hs, h⟩ := rat_val_eq harc h_nontriv
  refine ⟨p, hp, 1 / s, ?_⟩
  refine ⟨one_div_pos.mpr hs, ?_⟩
  ext a
  rw [h, ←Real.rpow_mul]
  simp only [MulRingNorm_eq_padicNorm, one_div, ne_eq, Ne.symm (ne_of_lt hs), not_false_eq_true,
    mul_inv_cancel, Real.rpow_one]
  unfold MulRingNorm.padic
  simp only [apply_nonneg]

end non_archimedean

section archimedean

lemma map_sum_le {R : Type*} [Ring R] (f : MulRingNorm R) (n : ℕ) {ι : ℕ → R} :
    f (∑ i in Finset.range n, ι i) ≤ ∑ i in Finset.range n, f (ι i) := by
  induction' n with n hn
  · simp only [Nat.zero_eq, Finset.range_zero, Finset.sum_empty, map_zero, le_refl]
  · rw [Finset.sum_range_succ, Finset.sum_range_succ]
    calc
      f (∑ x in Finset.range n, ι x + ι n) ≤
        f (∑ i in Finset.range n, ι i) + f (ι n) := by exact map_add_le_add f (∑ x in Finset.range n, ι x) (ι n)
                                        _  ≤ (∑ i in Finset.range n, f (ι i)) + f (ι n) := add_le_add_right hn _

lemma map_sum_le' (n : ℕ) (ι : Finset.Iio n → ℚ) :
    f (∑ i : Finset.Iio n, ι i) ≤ ∑ i : Finset.Iio n, f (ι i) := by
  simp only [Finset.univ_eq_attach]
  refine Finset.le_sum_of_subadditive ⇑f ?h_one ?h_mul (Finset.attach (Finset.Iio n)) fun i => ι i
  · exact map_zero f
  · exact fun x y => map_add_le_add f x y

--First limit
lemma limit1 {N : ℝ} (hN : 0 < N) : Filter.Tendsto (λ n : ℕ ↦ N ^ (1 / (n : ℝ))) Filter.atTop (nhds 1) := by
  rw [←Real.exp_log hN]
  simp_rw [←Real.exp_mul]
  refine Real.tendsto_exp_nhds_zero_nhds_one.comp ?_
  simp_rw [mul_one_div]
  apply tendsto_const_div_atTop_nhds_zero_nat

--Second limit
lemma limit2 (c : ℝ) (hc : 0 < c) : Filter.Tendsto (λ n : ℕ ↦ (1 + (n : ℝ) * c) ^ (1 / (n : ℝ))) Filter.atTop (nhds 1) := by
  have : (λ n : ℕ ↦ (1+(n : ℝ)*c)^(1 / (n : ℝ)))
    = (λ (x : ℝ) ↦ x ^ (1 / ((1 / c) * x  + (- 1) / c))) ∘ (λ y : ℝ ↦ 1 + c*y) ∘ (@Nat.cast ℝ Real.natCast)
  · ext n
    simp only [one_div, Function.comp_apply]
    rw [mul_add, ←mul_assoc, mul_one, div_eq_mul_inv, add_comm c⁻¹, add_assoc, neg_mul, one_mul,
      add_right_neg, add_zero, inv_mul_cancel (ne_of_gt hc), one_mul, mul_comm]
  rw [this]
  refine (tendsto_rpow_div_mul_add 1 (1 / c) (-1 / c) (one_div_ne_zero (ne_of_gt hc)).symm).comp ?_
  have goal : Filter.Tendsto (λ y : ℝ ↦ 1 + c*y) Filter.atTop Filter.atTop
  · apply Filter.tendsto_atTop_add_const_left
    apply Filter.Tendsto.const_mul_atTop hc
    intros _ hx
    exact hx
  refine Filter.Tendsto.comp goal ?_
  exact tendsto_nat_cast_atTop_atTop

lemma pow_mul_pow_le_max_pow {a b : ℝ} {m n : ℕ} (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ m * b ^ n ≤ max a b ^ (m + n) := by
  rw [pow_add]
  apply mul_le_mul
  · exact pow_le_pow_left ha (le_max_left a b) m
  · exact pow_le_pow_left hb (le_max_right a b) n
  · exact pow_nonneg hb n
  · apply pow_nonneg
    rw [le_max_iff]
    left
    exact ha

lemma inter_ineq {n : ℕ} (x y : ℚ) (hf : ∀ m : ℕ, f m ≤ 1) :
    f (x + y) ^ (n : ℝ) ≤ (n + 1 : ℝ) * max (f x) (f y) ^ n := by
  norm_cast
  rw [← map_pow, add_pow]
  apply le_trans (map_sum_le f (n + 1))
  suffices goal_1 : ∑ i in Finset.range (n + 1), f (x ^ i * y ^ (n - i) * (n.choose i))
    = ∑ i in Finset.range (n + 1), f (x ^ i) * f (y ^ (n - i)) * f (n.choose i)
  · rw [goal_1]
    calc
      ∑ i in Finset.range (n + 1), f (x ^ i) * f (y ^ (n - i)) * f (n.choose i)
        ≤ ∑ i in Finset.range (n + 1), f (x ^ i) * f (y ^ (n - i)) :=
          by
            apply Finset.sum_le_sum
            intros i _
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
              rw [map_pow]
            exact pow_mul_pow_le_max_pow (apply_nonneg f x) (apply_nonneg f y)
      _ = ↑(n + 1) * max (f x) (f y) ^ n := by simp
  · congr
    ext
    rw [f_mul_eq, f_mul_eq]

lemma root_ineq {n : ℕ} (x y : ℚ) (hn : n ≠ 0) (hf : ∀ m : ℕ, f m ≤ 1) :
    f (x + y) ≤ (n + 1 : ℝ) ^ (1 / (n : ℝ)) * max (f x) (f y) := by
  refine le_of_pow_le_pow_left hn ?_ ?_
  · apply mul_nonneg
    · apply Real.rpow_nonneg
      norm_cast
      linarith
    · rw [le_max_iff]
      left
      exact apply_nonneg f x
  · rw [mul_pow]
    have : 0 ≤ (n : ℝ) + 1 := by norm_cast; linarith
    nth_rewrite 2 [← Real.rpow_nat_cast]
    rw [← Real.rpow_mul this, one_div, inv_mul_cancel (by norm_cast), Real.rpow_one, ←Real.rpow_nat_cast]
    exact inter_ineq x y hf

-- A norm is non-archimedean iff it's bounded on the Naturals
lemma Nonarchimedean_iff_natNorm_bounded : (∀ n : ℕ, f n ≤ 1) ↔ Nonarchimedean f := by
  constructor
  · intros H x y
    have lim : Filter.Tendsto (λ n : ℕ ↦ (n + 1 : ℝ) ^ (1 / (n : ℝ)) * max (f x) (f y)) Filter.atTop (nhds (max (f x) (f y)))
    · nth_rewrite 2 [←one_mul (max (f x) (f y))]
      apply Filter.Tendsto.mul_const (max (f x) (f y))
      suffices goal_1 : (λ k : ℕ ↦ ((k : ℝ) + 1) ^ (1 / (k : ℝ))) = (λ k : ℕ ↦ (1 + (k : ℝ) * 1) ^ (1 / (k : ℝ)))
      · rw [goal_1]
        exact limit2 1 (Real.zero_lt_one)
      · ext k
        simp only [one_div, mul_one, add_comm]
    apply ge_of_tendsto lim _
    simp only [Filter.eventually_atTop, ge_iff_le]
    use 1
    intros b hb
    exact root_ineq x y (Nat.one_le_iff_ne_zero.mp hb) H
  · intros hf n
    exact nat_norm_le_one n hf

lemma aux1 {n₀ : ℕ} (hf : ∃ n : ℕ, 1 < f n) (dn₀ : n₀ = Nat.find hf) : 1 < n₀ := by
  have hn₀ := Nat.find_spec hf
  rw [← dn₀] at hn₀
  by_contra
  rw [lt_iff_not_ge] at hn₀
  interval_cases n₀
  · apply hn₀
    simp only [Nat.cast_zero, map_zero, ge_iff_le, zero_le_one]
  · apply hn₀
    simp only [Nat.cast_one, map_one, ge_iff_le, le_refl]

lemma List.mapIdx_append' {α M : Type*} [AddCommMonoid M] (K L : List α) (f : ℕ → α → M) :
    (K ++ L).mapIdx f = K.mapIdx f ++ L.mapIdx (λ i a ↦ f (i + K.length) a) := by
  induction' K with a J IH generalizing f
  · simp only [List.nil_append, List.length_nil, add_zero]
    exact rfl
  · specialize IH (λ i ↦ f (i + 1))
    simp only [List.cons_append, List.mapIdx_cons, IH, add_assoc, List.length]

lemma List.mapIdx_sum_to_finset_sum {β A : Type*} [AddCommMonoid A] {f : ℕ → β → A}
  {L : List β} [Inhabited β] : (L.mapIdx f).sum = ∑ i : Finset.Iio L.length,
    f i ((L.nthLe i (Finset.mem_Iio.1 i.2))) := by
  let g := λ i ↦ (f i ((L.get? i).get!))
  have goal : ∑ i : Finset.Iio L.length, f i ((L.nthLe i (Finset.mem_Iio.1 i.2))) =
    ∑ i : Finset.Iio L.length, g i
  · simp only [Finset.univ_eq_attach]
    apply Finset.sum_congr rfl
    intro x _
    have hx₁ := x.2
    simp only [Finset.mem_Iio] at hx₁
    congr
    rw [List.get?_eq_get hx₁]
    rfl
  rw [goal]
  simp only [Finset.univ_eq_attach]
  rw [Finset.sum_attach]
  dsimp only [g]
  refine List.reverseRecOn L ?_ ?_
  · simp only [List.mapIdx_nil, List.sum_nil, List.length_nil]
    rfl
  · intro M a IH
    simp only [List.mapIdx_append', List.mapIdx_cons, zero_add, List.mapIdx_nil, List.sum_append, IH,
      List.sum_cons, List.sum_nil, add_zero, List.length_append, List.length_singleton, Nat.Iio_eq_range, Finset.sum_range_succ]
    congr 1
    · apply Finset.sum_congr rfl
      intro x hx
      congr 2
      rw [Finset.mem_range] at hx
      exact (List.get?_append hx).symm
    · simp only [List.get?_concat_length]
      exact rfl

-- This is lemma 4
lemma lemma4 {n₀ : ℕ} {α : ℝ} (hf : ∃ n : ℕ, 1 < f n) (dn₀ : n₀ = Nat.find hf) (dα : α = Real.log (f n₀) / Real.log n₀) :
    ∀ n : ℕ, f n ≤ n ^ α := by
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
  · rw [dc, ← this]
    have hn₀ := Nat.find_spec hf
    rw [← dn₀] at hn₀
    apply div_pos
    linarith
    linarith
  suffices : ∀ n : ℕ, f n ≤ C * ((n : ℝ) ^ α)
  · intro n
    have limit'' : Filter.Tendsto
      (λ N : ℕ ↦ (C ^ (1 / (N : ℝ))) * (n ^ α)) Filter.atTop (nhds (n ^ α))
    · have := Filter.Tendsto.mul_const ((n : ℝ) ^ α) (limit1 hC)
      simp only [one_div, one_mul] at this
      simp only [one_div]
      exact this
    have stupid : (0 : ℝ) ≤ n := by norm_cast; exact zero_le n
    have aux : ∀ N : ℕ, (f (n)) ^ (N : ℝ) ≤ C * ((n ^ α) ^ (N : ℝ))
    · intro N
      rw [← Real.rpow_mul stupid]
      nth_rewrite 2 [mul_comm]
      rw [Real.rpow_mul stupid]
      norm_cast
      rw [← map_pow]
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
      · rw [mul_pow, ← Real.rpow_nat_cast,
          ← Real.rpow_nat_cast, ← Real.rpow_nat_cast,
            ← Real.rpow_mul (le_of_lt hC), one_div, inv_mul_cancel (by norm_cast), Real.rpow_one]
        exact aux N
    apply ge_of_tendsto limit'' _
    simp only [Filter.eventually_atTop, ge_iff_le]
    use 1
    intros b hb
    exact aux1 b (by linarith)
  intro n
  by_cases h : n = 0
  · subst h
    simp only [CharP.cast_eq_zero, map_zero]
    nlinarith [hC, Real.zero_rpow_nonneg α]
  conv_lhs =>
    rw [← Nat.ofDigits_digits n₀ n]
  rw [Nat.ofDigits_eq_sum_mapIdx]
  rw [List.mapIdx_sum_to_finset_sum]
  simp only [Finset.univ_eq_attach, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow]
  apply le_trans (map_sum_le' (n₀.digits n).length _)
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
    · simp only [Finset.univ_eq_attach]
      refine GCongr.sum_le_sum ?_
      intro i _
      specialize coef_ineq i
      have goal : ((n₀ : ℝ) ^ α) ^ (i : ℕ) = 1 * ((n₀ : ℝ) ^ α) ^ (i : ℕ) := by simp only [one_mul]
      nth_rewrite 2 [goal]
      refine mul_le_mul_of_nonneg_right coef_ineq ?_
      apply le_of_lt
      apply pow_pos
      exact Real.rpow_pos_of_pos (by linarith) α
    apply le_trans goal1
    have goal2 : (∑ i : (Finset.Iio (n₀.digits n).length), ((n₀ : ℝ) ^ α) ^ (i : ℕ)) =
    (((n₀ : ℝ) ^ (α * ((n₀.digits n).length - 1))) *
      ∑ i : (Finset.Iio (n₀.digits n).length), ((n₀ : ℝ) ^ (-α)) ^ (i : ℕ))
    · rw [Finset.mul_sum]
      simp only [Finset.univ_eq_attach, Finset.sum_attach]
      field_simp
      rw [Finset.sum_attach (Finset.Iio (List.length (Nat.digits n₀ n)))
        (λ x ↦ (n₀ : ℝ) ^ (α * ↑(List.length (Nat.digits n₀ (n / n₀))))
          * ((n₀ : ℝ) ^ (-α)) ^ (x : ℕ)), Nat.Iio_eq_range]
      nth_rewrite 1 [←Finset.sum_flip]
      refine Finset.sum_congr (by field_simp) ?_
      · intro x hx
        simp only [Finset.mem_range] at hx
        have hx₁ : x ≤ List.length (Nat.digits n₀ (n / n₀))
        · have goal : (List.length (Nat.digits n₀ (n / n₀)) + 1) = List.length (Nat.digits n₀ n) := by field_simp
          rw [← goal] at hx
          linarith
        rw [← Real.rpow_nat_cast]
        push_cast [hx₁]
        rw [@Real.rpow_sub ((n₀ : ℝ) ^ α)]
        · rw [← Real.rpow_nat_cast, ← Real.rpow_mul (by linarith), div_eq_mul_inv, Real.rpow_neg, Real.inv_rpow]
          · apply le_of_lt
            exact Real.rpow_pos_of_pos (by linarith) α
          · linarith
        · exact Real.rpow_pos_of_pos (by linarith) α
    rw [goal2]
    have goal3 : ((n₀ : ℝ) ^ (α * (((n₀.digits n).length - 1))))
      * (∑ i : (Finset.Iio (n₀.digits n).length), ((n₀ : ℝ) ^ (-α)) ^ (i : ℕ))
        ≤ ((n₀ : ℝ) ^ (α * (((n₀.digits n).length - 1)))) *
          (∑'i : ℕ, (1 / ((n₀ : ℝ) ^ α)) ^ i)
    · rw [mul_le_mul_left]
      · simp only [Finset.univ_eq_attach, one_div, inv_pow]
        have goal : ∑ i in Finset.attach (Finset.Iio (List.length (Nat.digits n₀ n))),
          ((n₀ : ℝ) ^ (-α)) ^ (i : ℕ) = ∑ i in Finset.Iio (List.length (Nat.digits n₀ n)),
            (((n₀ : ℝ) ^ α) ^ i)⁻¹
        · rw [Finset.sum_attach]
          refine Finset.sum_congr rfl ?_
          · intro x _
            rw [← inv_pow, Real.rpow_neg (by linarith)]
        rw [goal]
        refine sum_le_tsum _ ?_ ?_
        · intro i _
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
          · apply le_of_lt
            refine Real.rpow_pos_of_pos ?_ (-α)
            linarith
          · rw [Real.rpow_neg (by linarith)]
            field_simp
            rw [one_div_lt]
            · field_simp
              exact Real.one_lt_rpow (by linarith) hα
            · exact Real.rpow_pos_of_pos (by linarith) α
            · linarith
      · exact Real.rpow_pos_of_pos (by linarith) _
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
    rw [goal4, mul_comm]
    suffices : (n₀ : ℝ) ^ (α * (((n₀.digits n).length - 1))) ≤ (n : ℝ) ^ α
    · nlinarith
    have goal : (n₀ : ℝ) ^ (((n₀.digits n).length : ℝ) - 1) ≤ (n : ℝ)
    · have h' := Nat.base_pow_length_digits_le n₀ n aux' h
      have h'' : (n₀ : ℝ) ^ ((n₀.digits n).length : ℝ) ≤ (n₀ : ℝ) * (n : ℝ) := by norm_cast
      have aux'' : 0 < (n₀ : ℝ) := by norm_cast; linarith
      have stupid : (n₀ : ℝ) ≠ 0 := by norm_cast; linarith
      have h''' : 0 ≤ (n₀ : ℝ) ^ (-(1 : ℝ))
      · rw [Real.rpow_neg_one]
        have stupid2 : 0 ≤ (n₀ : ℝ)⁻¹ * n₀ := by simp [inv_mul_cancel stupid]
        exact nonneg_of_mul_nonneg_left stupid2 aux''
      have h'''' := mul_le_mul_of_nonneg_left h'' h'''
      rw [← Real.rpow_add aux'' _ _, add_comm, ←mul_assoc] at h''''
      apply le_trans h''''
      rw [Real.rpow_neg_one, inv_mul_cancel stupid]
      linarith
    rw [mul_comm, Real.rpow_mul (by linarith)]
    have stupid2 : 0 ≤ (n₀ : ℝ) ^ (((n₀.digits n).length : ℝ) - 1) := by
      apply le_of_lt
      exact @Real.rpow_pos_of_pos (n₀ : ℝ) (by linarith) _
    exact Real.rpow_le_rpow stupid2 goal (le_of_lt hα)
  · congr
    ext
    rw [f_mul_eq, map_pow]

-- This is lemma 5
lemma lemma5 {n₀ : ℕ} {α : ℝ} (hf : ∃ n : ℕ, 1 < f n) (dn₀ : n₀ = Nat.find hf) (dα : α = Real.log (f n₀) / Real.log n₀) :
    ∀ n : ℕ, (n ^ α : ℝ) ≤ f n := by
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
  have : f n₀ = n₀ ^ α
  · rw [dα, Real.log_div_log]
    apply Eq.symm
    apply Real.rpow_logb
    · norm_cast
      exact lt_trans zero_lt_one (aux1 hf dn₀)
    · apply ne_of_gt
      norm_cast
    · have hn₀ := Nat.find_spec hf
      rw [←dn₀] at hn₀
      exact lt_trans zero_lt_one hn₀
  let C : ℝ := (1 - (1 - 1 / n₀) ^ α)
  have hC : 0 < C
  · dsimp only [C]
    have hn₀1 : (2 : ℝ) ≤ (n₀ : ℝ) := by norm_cast
    field_simp
    apply Real.rpow_lt_one _ _ hα₀
    · apply le_of_lt
      apply div_pos
      · linarith
      · linarith
    · rw [div_lt_one]
      · linarith
      · linarith
  suffices : ∀ n : ℕ, C * ((n : ℝ) ^ α) ≤ f n
  · intro n
    have limit'' : Filter.Tendsto
      (λ N : ℕ ↦ (C ^ (1 / (N : ℝ))) * (n ^ α)) Filter.atTop (nhds (n ^ α))
    · have := Filter.Tendsto.mul_const ((n : ℝ) ^ α) (limit1 hC)
      simp only [one_div, one_mul] at this
      simp only [one_div]
      exact this
    have stupid : (0 : ℝ) ≤ n := by norm_cast; exact zero_le n
    have aux : ∀ N : ℕ, C * ((n ^ α) ^ (N : ℝ)) ≤ (f n) ^ (N : ℝ)
    · intro N
      rw [← Real.rpow_mul stupid]
      nth_rewrite 2 [mul_comm]
      rw [Real.rpow_mul stupid]
      norm_cast
      rw [← map_pow]
      specialize this (n ^ N)
      norm_cast
    have aux1 : ∀ N : ℕ, 0 < N → (C ^ (1 / (N : ℝ))) * (n ^ α) ≤ f (n)
    · intros N hN
      have hN₁ : N ≠ 0 := by linarith
      refine le_of_pow_le_pow_left hN₁ ?_ ?_
      · exact apply_nonneg f _
      · rw [mul_pow, ← Real.rpow_nat_cast, ← Real.rpow_nat_cast,
          ← Real.rpow_nat_cast, ← Real.rpow_mul (le_of_lt hC), one_div,
            inv_mul_cancel (by norm_cast), Real.rpow_one]
        exact aux N
    apply le_of_tendsto limit'' _
    simp only [Filter.eventually_atTop, ge_iff_le]
    use 1
    intros b hb
    exact aux1 b (by linarith)
  intros n
  by_cases hn : n = 0
  · subst hn
    simp only [CharP.cast_eq_zero, map_zero]
    rw [Real.zero_rpow]
    · rw [mul_zero]
    linarith
  have length_lt_one : 1 ≤ (n₀.digits n).length
  · by_contra goal
    simp only [not_le, Nat.lt_one_iff, List.length_eq_zero, Nat.digits_eq_nil_iff_eq_zero] at goal
    contradiction
  have h₁ : f ((n₀ : ℚ) ^ ((n₀.digits n).length))
    - f (((n₀ : ℚ) ^ ((n₀.digits n).length)) - n) ≤ f n
  · have goal := abs_sub_map_le_sub f ((n₀ : ℚ) ^ ((n₀.digits n).length)) (((n₀ : ℚ) ^ ((n₀.digits n).length)) - n)
    simp only [map_pow, sub_sub_cancel] at goal
    apply le_trans _ goal
    rw [map_pow]
    exact le_abs_self _
  apply le_trans' h₁
  rw [map_pow, this]
  have h := lemma4 hf dn₀ dα
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
  · rw [mul_sub, mul_one, sub_right_inj, ← Real.rpow_nat_cast,
      ← Real.rpow_nat_cast, ← Real.rpow_nat_cast, ←Real.rpow_mul]
    · nth_rewrite 2 [mul_comm]
      rw [Real.rpow_mul]
      · rw [←Real.mul_rpow]
        · rw [mul_sub, mul_one, Nat.cast_sub length_lt_one, Real.rpow_sub]
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
  apply mul_le_mul_of_nonneg_left _ (le_of_lt hC)
  suffices goal : (n : ℝ )^ α ≤ ((n₀ : ℝ) ^ (n₀.digits n).length) ^ α
  · rw [← Real.rpow_nat_cast] at goal ⊢
    rw [← Real.rpow_mul]
    · rw [mul_comm, Real.rpow_mul]
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

lemma archimedean_case (hf : ¬ Nonarchimedean f) : MulRingNorm.equiv f MulRingNorm.Real :=
by
  rw [← Nonarchimedean_iff_natNorm_bounded] at hf
  simp only [not_forall, not_le] at hf
  let n₀ : ℕ := Nat.find hf
  have dn₀ : n₀ = Nat.find hf := rfl
  let α : ℝ := Real.log (f n₀) / Real.log n₀
  have hα : α =  Real.log (f n₀) / Real.log n₀ := rfl
  have h₃ : ∀ (n : ℕ), f (n : ℚ) = (n : ℝ) ^ α
  · intro n
    linarith [lemma5 hf dn₀ hα n, lemma4 hf dn₀ hα n]
  have h₄ : ∀ (n : ℕ), f (n : ℚ) = |(n : ℝ)| ^ α
  · intro n
    rw [Nat.abs_cast n]
    exact h₃ n
  apply MulRingNorm.equiv_symm _
  refine ⟨α, ?_, ?_⟩
  · rw [hα]
    apply div_pos
    · apply Real.log_pos
      exact Nat.find_spec hf
    · apply Real.log_pos
      norm_cast
      exact aux1 hf dn₀
  · ext x
    rw [MulRingNorm_eq_abs, ← Rat.num_div_den x]
    norm_cast
    rw [← Rat.coe_int_div_eq_divInt, abs_div]
    push_cast
    rw [map_div₀]
    · rw [Real.div_rpow]
      · congr
        · cases' x.num with b b
          · simp only [Int.ofNat_eq_coe, Int.cast_ofNat]
            exact (h₄ b).symm
          · simp only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one, neg_add_rev]
            rw [← abs_neg, ← map_neg_eq_map]
            simp only [neg_add_rev, neg_neg]
            norm_cast
            exact (h₃ (b + 1)).symm
        · exact (h₄ x.den).symm
      · exact norm_nonneg ((x.num) : ℝ)
      · exact norm_nonneg ((x.den) : ℝ)

end archimedean

/-- Ostrowski's Theorem -/
theorem RatRingNorm_padic_or_real {f : MulRingNorm ℚ} (hf_nontriv : f ≠ 1) :
  (MulRingNorm.equiv f MulRingNorm.Real) ∨
  ∃ (p : ℕ) (hp : Fact (Nat.Prime p)), MulRingNorm.equiv f (@MulRingNorm.padic p hp) :=
by
    by_cases bdd : ∀ z : ℕ, f z ≤ 1
    · right /- p-adic case -/
      rw [Nonarchimedean_iff_natNorm_bounded] at bdd
      exact f_equiv_padic bdd hf_nontriv
    · left
      rw [Nonarchimedean_iff_natNorm_bounded] at bdd
      exact archimedean_case bdd /- Euclidean case -/
