/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.OutCrossInt
public import Zeta5Irr.LocalEstimates.OutNodeDiff
public import Zeta5Irr.LocalEstimates.OutEllN
public import Zeta5Irr.LocalFunctional.LocalVpGAdd
public import Zeta5Irr.LocalFunctional.SmallHarmVal
public import Zeta5Irr.LocalFunctional.DerivProdEval

/-!
# The outer range: the residue valuation within a class

Let `p ≥ 7` be a prime, fix the parameters `N = 3 n` and `K = 40 n` with `2 K < p²` and
`2 N < p`, let `1 ≤ a ≤ m°`, and let `0 ≤ i, j < ℓ_K(a) - 2`. Then the diagonal entry of the
integral part of the outer form on the separating basis satisfies
`v_p^G(Φ₀(P_a q_{a,i}, P_a q_{a,j})) ≥ min(0, i + j + 6 δ_a - ℓ_K(a) - 4)`.

Write `ℓ = ℓ_K(a)`, `δ = δ_a`, `S = {N + 1, …, K}` and `A = D_N⁵ P_a² q_{a,i} q_{a,j}`. The entry
is `μ₀(A /ₘ D_S) + ∑_{j' ∈ S} A(-j'²) / D_S'(-j'²) · ν_{j'}(X)`. The first summand lies in
`ℤ_p`. A node `j' ∈ S` outside the class of `±a` is a root of `P_a`, so its residue vanishes.
For a node `j' ≡ ±a (mod p)`:

* `q_{a,i} q_{a,j} = (t + a²)^{i + j}` has value `(a² - j'²)^{i + j}`, divisible by `p^{i + j}`;
* if `δ = 1`, that is `a ≤ N`, the factor `a² - j'²` of `D_N(-j'²)` is divisible by `p`, so
  `p^{5 δ}` divides `D_N(-j'²)⁵`;
* `D_S'(-j'²) = ∏_{j'' ∈ S, j'' ≠ j'} (j''² - j'²)`; a factor with `j'' ≢ ±a` is prime to `p`,
  since `j''² ≡ j'² ≡ a²` would force `j'' ≡ ±a`, and a factor with `j'' ≡ ±a` has valuation
  exactly `1`. There are `ℓ_K(a) - ℓ_N(a) - 1 = ℓ - δ - 1` of the latter;
* `v_p^G(ν_{j'}) ≥ -5`, since `v_p(H_{j'}^{(5)}) ≥ -5` and `4`, `2 j'` are below `p²`.

Collecting, the residue at `j'` has `v_p^G ≥ (i + j) + 5 δ - (ℓ - δ - 1) - 5`, and the
ultrametric inequality gives the bound.

## Main results

* `Zeta5Irr.min_le_vpG_outerIntegralForm_complClassFactor_mul_outerBasis`:
  `v_p^G(Φ₀(P_a q_{a,i}, P_a q_{a,j})) ≥ min(0, i + j + 6 δ_a - ℓ_K(a) - 4)`.

## Implementation notes

* Of the source's hypotheses only `p ≥ 7`, `2 K < p²`, `2 N < p`, `1 ≤ a ≤ m°` and
  `i, j < ℓ_K(a) - 2` are used. The conditions `K ∈ 40 ℤ_{>0}`, `p ≤ K < 3 p` and
  `5 N ≤ 2 p - 2` are not needed, so the result is stated without them: the bound
  `v_p(H_{j'}^{(5)}) ≥ -5` only needs `j' < p²`, which follows from `2 K < p²`.
* For `a ≥ 1` the local polynomial `q_{a,i}` is `Zeta5Irr.outerBasis`.
* The valuation of the residue is computed in `ℤ`: the numerator `A(-j'²)` and the denominator
  `D_S'(-j'²)` are integers, and their `p`-adic valuations are `padicValInt`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.10 (The outer range: the entry valuations).
-/

@[expose] public section

namespace Zeta5Irr

open Finset Polynomial

variable {p : ℕ} [Fact p.Prime]

/-- If `p ^ k ∣ m`, then `v_p(m) ≥ k`. -/
private theorem le_addValuation_intCast_of_pow_dvd {m : ℤ} {k : ℕ} (h : (p : ℤ) ^ k ∣ m) :
    ((k : ℤ) : WithTop ℤ) ≤ Padic.addValuation (m : ℚ_[p]) := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rw [Padic.addValuation.apply (by exact_mod_cast hm), Padic.valuation_intCast,
    WithTop.coe_le_coe]
  exact_mod_cast by simpa [hm] using (padicValInt_dvd_iff (p := p) k m).mp h

/-- For `0 < n < p²`, `v_p(1 / n) ≥ -1`. -/
private theorem neg_one_le_addValuation_inv_natCast {n : ℕ} (hn : n ≠ 0) (hlt : n < p ^ 2) :
    ((-1 : ℤ) : WithTop ℤ) ≤ Padic.addValuation ((n : ℚ_[p])⁻¹) := by
  have h0 : ((n : ℚ_[p]))⁻¹ ≠ 0 := by simp [hn]
  rw [Padic.addValuation.apply h0, Padic.valuation_inv, Padic.valuation_natCast,
    WithTop.coe_le_coe]
  have : padicValNat p n ≤ 1 :=
    (padicValNat_le_nat_log n).trans (Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow hn hlt))
  omega

/-- For `p ≥ 7`, `2 K < p²` and `1 ≤ j ≤ K`, the pole value has `v_p^G(ν_j) ≥ -5`. -/
private theorem neg_five_le_vpG_map_poleValue (hp7 : 7 ≤ p) {K j : ℕ} (hK : 2 * K < p ^ 2)
    (hj1 : 1 ≤ j) (hjK : j ≤ K) :
    ((-5 : ℤ) : WithTop ℤ) ≤ vpG ((poleValue j).map (Rat.castHom ℚ_[p])) := by
  have hj4 : ((0 : ℕ) : ℤ) ≤ Padic.addValuation ((j : ℚ_[p]) ^ 4) := by
    have := le_addValuation_intCast_of_pow_dvd (p := p) (m := (j : ℤ) ^ 4) (k := 0) (by simp)
    simpa using this
  refine (le_gaussAddVal_iff _).mpr fun k ↦ ?_
  rw [coeff_map]
  rcases k with _ | _ | k
  · have hc : (poleValue j).coeff 0 =
        -((j : ℚ) ^ 4 * harmonicFive j) - ((4 : ℕ) : ℚ)⁻¹ + ((2 * j : ℕ) : ℚ)⁻¹ := by
      rw [coeff_zero_poleValue]
      push_cast
      ring
    rw [hc]
    simp only [map_add, map_sub, map_neg, map_mul, map_pow, map_inv₀, map_natCast]
    have hlog : Nat.log p K ≤ 1 := by
      rcases Nat.eq_zero_or_pos K with hK0 | hK0
      · simp [hK0]
      exact Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow (by omega) (show K < p ^ 2 by omega))
    have hH := le_addValuation_harmonicFive (p := p) hjK
    have h4 := neg_one_le_addValuation_inv_natCast (p := p) (n := 4) (by norm_num) (by nlinarith)
    have h2j := neg_one_le_addValuation_inv_natCast (p := p) (n := 2 * j) (by omega) (by omega)
    refine AddValuation.map_le_add _ (?_ : _ ≤ Padic.addValuation (_ - _)) ?_
    · rw [sub_eq_add_neg]
      refine AddValuation.map_le_add _ ?_ ?_
      · rw [AddValuation.map_neg, AddValuation.map_mul]
        calc ((-5 : ℤ) : WithTop ℤ)
            ≤ ((0 : ℤ) : WithTop ℤ) + ((-5 * Nat.log p K : ℤ) : WithTop ℤ) := by
              rw [← WithTop.coe_add, WithTop.coe_le_coe]
              omega
          _ ≤ _ := add_le_add (by exact_mod_cast hj4) hH
      · rw [AddValuation.map_neg]
        exact le_trans (by exact_mod_cast (by norm_num : (-5 : ℤ) ≤ -1)) h4
    · exact le_trans (by exact_mod_cast (by norm_num : (-5 : ℤ) ≤ -1)) h2j
  · rw [coeff_one_poleValue]
    simp only [eq_ratCast, Rat.cast_pow, Rat.cast_natCast]
    exact le_trans (by exact_mod_cast (by norm_num : (-5 : ℤ) ≤ 0)) hj4
  · rw [coeff_eq_zero_of_natDegree_lt ((natDegree_poleValue_le j).trans_lt (by omega)),
      map_zero, AddValuation.map_zero]
    exact le_top

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent in
/-- If `j ≡ ±a (mod p)`, then `p ∣ a² - j²`. -/
private theorem dvd_neg_sq_add_sq {a : ℤ} {j : ℕ}
    (h : (j : ZMod p) = (a : ZMod p) ∨ (j : ZMod p) = -(a : ZMod p)) :
    (p : ℤ) ∣ -(j : ℤ) ^ 2 + a ^ 2 := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rcases h with h | h <;> rw [h] <;> ring

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent in
/-- If `j' ≡ ±a` and `j ≢ ±a (mod p)`, then `p ∤ j² - j'²`. -/
private theorem not_dvd_neg_sq_sub_neg_sq {a : ℤ} {j j' : ℕ}
    (h : (j' : ZMod p) = (a : ZMod p) ∨ (j' : ZMod p) = -(a : ZMod p))
    (h' : ¬((j : ZMod p) = (a : ZMod p) ∨ (j : ZMod p) = -(a : ZMod p))) :
    ¬(p : ℤ) ∣ -(j' : ℤ) ^ 2 - -(j : ℤ) ^ 2 := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  intro h0
  apply h'
  have hsq : (j : ZMod p) ^ 2 = (a : ZMod p) ^ 2 := by
    rcases h with h | h <;> rw [h] at h0 <;> linear_combination h0
  exact sq_eq_sq_iff_eq_or_eq_neg.mp hsq

/-- `ℓ_K(a) = δ_a + #{N < j ≤ K | j ≡ ±a (mod p)}` for `N ≤ K`, `2 N < p` and `1 ≤ a ≤ m°`. -/
theorem ellA_eq_outerDelta_add_card_filter {N K a : ℕ} (hNK : N ≤ K) (hN : 2 * N < p)
    (ha : 1 ≤ a) (ha' : a ≤ mStar p) :
    ellA p K a = outerDelta N a + #((Icc (N + 1) K).filter fun j : ℕ ↦
      (j : ZMod p) = ((a : ℤ) : ZMod p) ∨ (j : ZMod p) = -((a : ℤ) : ZMod p)) := by
  rw [← ellA_eq_outerDelta hN ha ha', ← card_residuePoleIndices_add_ellA p _ hNK,
    Finset.Icc_add_one_left_eq_Ioc, add_comm]
  rfl

/-- For distinct naturals `j ≠ j'`, `-j'² - -j² ≠ 0`. -/
private theorem neg_sq_sub_neg_sq_ne_zero {j j' : ℕ} (h : j ≠ j') :
    -(j' : ℤ) ^ 2 - -(j : ℤ) ^ 2 ≠ 0 := by
  intro h0
  apply h
  have : (j : ℤ) ^ 2 = (j' : ℤ) ^ 2 := by linarith
  exact_mod_cast (sq_eq_sq₀ (by positivity) (by positivity)).mp this

/-- For a node `j' ∈ S = {N + 1, …, K}` with `j' ≡ ±a (mod p)`, the valuation of
`D_S'(-j'²) = ∏_{j'' ∈ S, j'' ≠ j'} (j''² - j'²)` is the number of other nodes of the class. -/
theorem padicValInt_prod_erase_neg_sq_sub_neg_sq {N K a j' : ℕ} (hK : 2 * K < p ^ 2)
    (ha : 1 ≤ a) (ha' : a ≤ mStar p) (hj' : j' ∈ Icc (N + 1) K)
    (hcls : (j' : ZMod p) = ((a : ℤ) : ZMod p) ∨ (j' : ZMod p) = -((a : ℤ) : ZMod p)) :
    padicValInt p (∏ j'' ∈ (Icc (N + 1) K).erase j', (-(j' : ℤ) ^ 2 - -(j'' : ℤ) ^ 2)) =
      #((Icc (N + 1) K).filter fun j'' : ℕ ↦
        (j'' : ZMod p) = ((a : ℤ) : ZMod p) ∨ (j'' : ZMod p) = -((a : ℤ) : ZMod p)) - 1 := by
  have hj'S := mem_Icc.mp hj'
  rw [padicValInt_prod_of_ne_zero _ _ fun j'' hj'' ↦
      neg_sq_sub_neg_sq_ne_zero (mem_erase.mp hj'').1,
    ← sum_filter_add_sum_filter_not _ (fun j'' : ℕ ↦
      (j'' : ZMod p) = ((a : ℤ) : ZMod p) ∨ (j'' : ZMod p) = -((a : ℤ) : ZMod p))]
  rw [sum_eq_zero (s := filter (fun x : ℕ ↦ ¬ _) _) ?_, add_zero,
    sum_congr rfl (g := fun _ ↦ 1) ?_, sum_const, smul_eq_mul, mul_one, filter_erase,
    card_erase_of_mem (mem_filter.mpr ⟨hj', hcls⟩)]
  · intro j'' hj''
    obtain ⟨hj''S, hc''⟩ := mem_filter.mp hj''
    obtain ⟨hne, hmem⟩ := mem_erase.mp hj''S
    have h1 := mem_Icc.mp hmem
    rw [show -(j' : ℤ) ^ 2 - -(j'' : ℤ) ^ 2 = (j'' : ℤ) ^ 2 - (j' : ℤ) ^ 2 by ring]
    exact padicValInt_sq_sub_sq_eq_one hK ha ha' (by exact_mod_cast hne) (by omega)
      (by omega) (by omega) (by omega) ((natCast_eq_or_eq_neg_iff_intModEq _ _ _).mp hc'')
      ((natCast_eq_or_eq_neg_iff_intModEq _ _ _).mp hcls)
  · intro j'' hj''
    exact padicValInt.eq_zero_of_not_dvd (not_dvd_neg_sq_sub_neg_sq hcls (mem_filter.mp hj'').2)

/-- For `j' ≡ ±a (mod p)` and `i, j < ℓ_K(a) - 2`, `p ^ (i + j + 5 δ_a)` divides
`(D_N⁵ P_a² q_{a,i} q_{a,j})(-j'²)`. -/
theorem pow_dvd_eval_poleProductRange_pow_mul_outerBasis {N K a i j j' : ℕ} (ha : 1 ≤ a)
    (hi : i < ellA p K a - 2) (hj : j < ellA p K a - 2)
    (hcls : (j' : ZMod p) = ((a : ℤ) : ZMod p) ∨ (j' : ZMod p) = -((a : ℤ) : ZMod p)) :
    (p : ℤ) ^ (i + j + 5 * outerDelta N a) ∣ (poleProductRange N ℤ ^ 5 *
      (complClassFactor ℤ p a N K * outerBasis ℤ p K a i) *
      (complClassFactor ℤ p a N K * outerBasis ℤ p K a j)).eval (-(j' : ℤ) ^ 2) := by
  have hpa : (p : ℤ) ∣ -(j' : ℤ) ^ 2 + (a : ℤ) ^ 2 := dvd_neg_sq_add_sq hcls
  have h1 : (p : ℤ) ^ (5 * outerDelta N a) ∣
      (∏ k ∈ Icc 1 N, (-(j' : ℤ) ^ 2 + (k : ℤ) ^ 2)) ^ 5 := by
    by_cases haN : a ≤ N
    · rw [outerDelta_of_le (by exact_mod_cast haN), mul_one]
      exact pow_dvd_pow_of_dvd (hpa.trans (dvd_prod_of_mem
        (fun k : ℕ ↦ -(j' : ℤ) ^ 2 + (k : ℤ) ^ 2) (mem_Icc.mpr ⟨ha, haN⟩))) 5
    · rw [outerDelta_of_lt (by exact_mod_cast not_le.mp haN), mul_zero, pow_zero]
      exact one_dvd _
  rw [show (p : ℤ) ^ (i + j + 5 * outerDelta N a) =
      (p : ℤ) ^ (5 * outerDelta N a) * (p : ℤ) ^ i * (p : ℤ) ^ j by ring,
    outerBasis_of_lt hi, outerBasis_of_lt hj]
  simp only [eval_mul, eval_pow, eval_poleProductRange, eval_add, eval_X, eval_C, Int.cast_id]
  exact mul_dvd_mul (mul_dvd_mul h1 (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hpa i) _))
    (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hpa j) _)

/-- `D_S'(-j'²) = ∏_{j'' ∈ S, j'' ≠ j'} (-j'² - -j''²)` for a node `j' ∈ S`. -/
private theorem eval_derivative_poleProduct_neg_sq_eq_intCast {S : Finset ℕ} {j' : ℕ}
    (hj' : j' ∈ S) :
    (derivative (poleProduct S ℚ)).eval (-((j' : ℚ) ^ 2)) =
      ((∏ j'' ∈ S.erase j', (-(j' : ℤ) ^ 2 - -(j'' : ℤ) ^ 2) : ℤ) : ℚ) := by
  rw [eval_derivative_poleProduct_neg_sq hj']
  push_cast
  exact prod_congr rfl fun _ _ ↦ by ring

/-- If `v_p^G(f) ≥ b` and `B ≤ v_p(α) - v_p(β) + b` whenever `α ≠ 0`, then
`v_p^G((α / β) • f) ≥ B`. -/
theorem le_vpG_intCast_div_smul {α β : ℤ} (hβ : β ≠ 0) {f : ℚ_[p][X]} {b B : ℤ}
    (hf : (b : WithTop ℤ) ≤ vpG f)
    (hB : α ≠ 0 → B ≤ padicValInt p α - padicValInt p β + b) :
    (B : WithTop ℤ) ≤ vpG (((α : ℚ) / (β : ℚ)) • f) := by
  rcases eq_or_ne α 0 with rfl | hα
  · simp
  have hsm : ∀ (c : ℚ) (f : ℚ_[p][X]), c • f = C (c : ℚ_[p]) * f := fun c f ↦ by
    rw [← smul_eq_C_mul, Rat.cast_smul_eq_qsmul]
  have hx0 : ((α : ℚ_[p]) / (β : ℚ_[p])) ≠ 0 := by simp [hα, hβ]
  unfold vpG at hf ⊢
  rw [hsm, gaussAddVal_C_mul, Rat.cast_div, Rat.cast_intCast, Rat.cast_intCast,
    Padic.addValuation.apply hx0, div_eq_mul_inv,
    Padic.valuation_mul (by simpa using hα) (by simpa using hβ), Padic.valuation_inv,
    Padic.valuation_intCast, Padic.valuation_intCast]
  calc (B : WithTop ℤ)
      ≤ (((padicValInt p α : ℤ) + -(padicValInt p β : ℤ) : ℤ) : WithTop ℤ) + (b : WithTop ℤ) := by
        rw [← WithTop.coe_add, WithTop.coe_le_coe]
        linarith [hB hα]
    _ ≤ _ := add_le_add_right hf _

/-- The constant `μ₀(f)` of an integer polynomial `f` has `v_p^G(μ₀(f)) ≥ 0`. -/
theorem zero_le_vpG_C_truncatedMomentFunctional_map_intCast (hp7 : 7 ≤ p) (f : ℤ[X]) :
    ((0 : ℤ) : WithTop ℤ) ≤ vpG (C (truncatedMomentFunctional p (f.map (Int.castRingHom ℚ)))) := by
  rw [vpG, gaussAddVal_C]
  rcases eq_or_ne (truncatedMomentFunctional p (f.map (Int.castRingHom ℚ))) 0 with h0 | h0
  · simp [h0]
  rw [Padic.addValuation.apply h0, WithTop.coe_le_coe]
  exact (Padic.norm_le_one_iff_val_nonneg _).mp
    (norm_truncatedMomentFunctional_map_intCast_le_one hp7 f)

/-- **The residue valuation within a class.** Let `p ≥ 7` be a prime with `2 K < p²` and
`2 N < p`, where `N = 3 n` and `K = 40 n`, let `1 ≤ a ≤ m°` and `0 ≤ i, j < ℓ_K(a) - 2`. Then
`v_p^G(Φ₀(P_a q_{a,i}, P_a q_{a,j})) ≥ min(0, i + j + 6 δ_a - ℓ_K(a) - 4)`. -/
@[zeta5irr "lem_out_resid_val"]
theorem min_le_vpG_outerIntegralForm_complClassFactor_mul_outerBasis (hp7 : 7 ≤ p) {n : ℕ}
    (hK : 2 * poleBound n < p ^ 2) (hN : 2 * innerDegree n < p) {a : ℕ} (ha : 1 ≤ a)
    (ha' : a ≤ mStar p) {i j : ℕ} (hi : i < ellA p (poleBound n) a - 2)
    (hj : j < ellA p (poleBound n) a - 2) :
    ((min 0 ((i + j + 6 * outerDelta (innerDegree n) a : ℤ) - ellA p (poleBound n) a - 4) : ℤ) :
        WithTop ℤ) ≤
      vpG (outerIntegralForm p n
        (complClassFactor ℚ p a (innerDegree n) (poleBound n) *
          outerBasis ℚ p (poleBound n) a i)
        (complClassFactor ℚ p a (innerDegree n) (poleBound n) *
          outerBasis ℚ p (poleBound n) a j)) := by
  rw [outerIntegralForm, truncatedPoleFunctional_apply]
  set N := innerDegree n with hNdef
  set K := poleBound n with hKdef
  set S := Icc (N + 1) K with hS
  have hNK : N ≤ K := by simp only [hNdef, hKdef, innerDegree, poleBound]; omega
  set F : ℤ[X] := poleProductRange N ℤ ^ 5 *
    (complClassFactor ℤ p a N K * outerBasis ℤ p K a i) *
    (complClassFactor ℤ p a N K * outerBasis ℤ p K a j) with hF
  have hmap : poleProductRange N ℚ ^ 5 *
      (complClassFactor ℚ p a N K * outerBasis ℚ p K a i) *
      (complClassFactor ℚ p a N K * outerBasis ℚ p K a j) = F.map (Int.castRingHom ℚ) := by
    simp only [hF, Polynomial.map_mul, Polynomial.map_pow, map_poleProductRange,
      map_complClassFactor, map_outerBasis]
  refine le_trans (le_min ?_ ?_) (min_le_vpG_add _ _)
  · have hμ := zero_le_vpG_C_truncatedMomentFunctional_map_intCast hp7 (F /ₘ poleProduct S ℤ)
    rw [map_divByMonic _ (monic_poleProduct S ℤ), map_poleProduct, ← hmap] at hμ
    exact le_trans (WithTop.coe_le_coe.mpr (min_le_left _ _)) hμ
  refine le_trans (Finset.le_inf fun j' hj' ↦ ?_) (finset_inf_le_gaussAddVal_sum _ _ _)
  by_cases hcls : (j' : ZMod p) = ((a : ℤ) : ZMod p) ∨ (j' : ZMod p) = -((a : ℤ) : ZMod p)
  swap
  · rw [eval_mul, eval_mul, eval_mul, eval_neg_sq_complClassFactor hj' hcls]
    simp
  have hα : (F.map (Int.castRingHom ℚ)).eval (-((j' : ℚ) ^ 2)) =
      ((F.eval (-(j' : ℤ) ^ 2) : ℤ) : ℚ) := by
    rw [show -((j' : ℚ) ^ 2) = ((-(j' : ℤ) ^ 2 : ℤ) : ℚ) by push_cast; ring,
      eval_intCast_map, eq_intCast, Int.cast_id]
  rw [hmap, hα, eval_derivative_poleProduct_neg_sq_eq_intCast hj']
  have hcount := ellA_eq_outerDelta_add_card_filter (p := p) hNK hN ha ha'
  have hvβ := padicValInt_prod_erase_neg_sq_sub_neg_sq hK ha ha' hj' hcls
  have hC1 : 0 < #((Icc (N + 1) K).filter fun j'' : ℕ ↦
      (j'' : ZMod p) = ((a : ℤ) : ZMod p) ∨ (j'' : ZMod p) = -((a : ℤ) : ZMod p)) :=
    card_pos.mpr ⟨j', mem_filter.mpr ⟨hj', hcls⟩⟩
  refine le_vpG_intCast_div_smul (prod_ne_zero_iff.mpr fun j'' hj'' ↦
    neg_sq_sub_neg_sq_ne_zero (mem_erase.mp hj'').1)
    (neg_five_le_vpG_map_poleValue hp7 hK
      ((Nat.le_add_left 1 N).trans (mem_Icc.mp hj').1) (mem_Icc.mp hj').2) fun hα0 ↦ ?_
  have hvα : i + j + 5 * outerDelta N a ≤ padicValInt p (F.eval (-(j' : ℤ) ^ 2)) :=
    ((padicValInt_dvd_iff (p := p) _ _).mp
      (pow_dvd_eval_poleProductRange_pow_mul_outerBasis (N := N) ha hi hj hcls)).resolve_left hα0
  rw [hvβ]
  omega

end Zeta5Irr
