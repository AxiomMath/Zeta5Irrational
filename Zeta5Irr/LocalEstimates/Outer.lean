/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.GammaOut
public import Zeta5Irr.LocalEstimates.DetPerturb
public import Zeta5Irr.LocalEstimates.OutEntryVal
public import Zeta5Irr.LocalEstimates.OutBasisChange
public import Zeta5Irr.LocalEstimates.OutConjEntry
public import Zeta5Irr.LocalEstimates.OutConjInt
public import Zeta5Irr.LocalEstimates.OutConjRank
public import Zeta5Irr.LocalEstimates.OutZerocountLow
public import Zeta5Irr.LocalEstimates.OutZerocountHigh

/-!
# The outer range: the valuation of `Δ_K`

Let `K = 40 n` and let `p` be a prime with `p ≥ 7`, `p ≤ K < 3 p`, `p² > 2 K` and `2 N < p`,
where `N = 3 n`. Then `v_p^G(Δ_K) ≥ γ_p^out`.

Put `𝒜 = C^out G_K^∘ (C^out)ᵀ` and `𝓛 = C^out 𝓛_p (C^out)ᵀ`. Since `G_K = G_K^∘ + p⁻¹ 𝓛_p`,
`C^out G_K (C^out)ᵀ = 𝒜 + p⁻¹ 𝓛`. With rows and columns indexed by the pairs `(a, i)`, the
entries of `𝒜` satisfy `v_p^G(𝒜_{(a,i),(c,j)}) ≥ w_{a,i} + w_{c,j}` for nonpositive
half-integer weights `w_{a,i}`, while `𝓛` has entries in `ℤ_p` and rank at most `r_p`. The
determinant bound for a perturbed matrix gives
`v_p^G(det (𝒜 + p⁻¹ 𝓛)) ≥ 2 ∑ w_{a,i} - min(r_p, z)`, `z` being the number of vanishing
weights; the weight sum and the zero count evaluate the right-hand side to `γ_p^out` in both
cases `K < 2 p` and `K ≥ 2 p`. Finally `v_p^G(det (C^out G_K (C^out)ᵀ)) = v_p^G(Δ_K)`.

## Main results

* `Zeta5Irr.sum_sigma_residuePoleIndices`: a sum over the pairs `(a, i)` splits into the class
  `a = 0` and the classes `1 ≤ a ≤ m°`.
* `Zeta5Irr.exists_outerLocalWeight_eq_intCast_div_two`: every weight `w_{a,i}` is a
  half-integer.
* `Zeta5Irr.outerExponent_le_vpG_gramDet`: `v_p^G(Δ_K) ≥ γ_p^out`.

## Implementation notes

* The pairs `(a, i)` are identified with `Fin h` by an arbitrary bijection, which exists since
  both sets have `h` elements; the determinant bound is applied to the reindexed matrices, and
  reindexing changes neither the determinant nor the rank.
* The rank of `𝓛` is taken over `ℚ_p`, after reading its constant entries in `ℚ_p`.
* The source's hypothesis `5 N ≤ 2 p - 2` is not used, so the result is stated without it;
  `K ∈ 40 ℤ_{>0}` is built in through `K = 40 n` (and `n > 0` follows from `p ≤ K`).
* The bound is stated in `ℤ ∪ {+∞}`, where the Gauss valuation takes its values.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.12 (The outer range: the conjugated decomposition).
-/

@[expose] public section

namespace Zeta5Irr

open Finset Polynomial

/-- A sum over the row pairs `(a, i)` of the outer coefficient matrix, split into the class
`a = 0` and the classes `1 ≤ a ≤ m°`. -/
theorem sum_sigma_residuePoleIndices {M : Type*} [AddCommMonoid M] (p N K : ℕ)
    (f : ℕ → ℕ → M) :
    ∑ ai : Σ a : Fin (mStar p + 1), Fin #(residuePoleIndices p (a : ℕ) N K),
        f ai.1 ai.2 =
      ∑ i ∈ range #(residuePoleIndices p 0 N K), f 0 i +
        ∑ a ∈ Icc 1 (mStar p), ∑ i ∈ range #(residuePoleIndices p a N K), f a i := by
  have h1 (a : Fin (mStar p + 1)) :
      ∑ y : Fin #(residuePoleIndices p (a : ℕ) N K), f a y =
        ∑ i ∈ range #(residuePoleIndices p (a : ℕ) N K), f a i :=
    Fin.sum_univ_eq_sum_range (fun i ↦ f a i) _
  simp only [Fintype.sum_sigma, h1]
  rw [Fin.sum_univ_eq_sum_range
    (fun a ↦ ∑ i ∈ range #(residuePoleIndices p (a : ℕ) N K), f a i), sum_range_succ',
    add_comm, ← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
  simp [add_comm 1]

/-- Each weight `w_{a,i}` of the outer range is a half-integer. -/
theorem exists_outerLocalWeight_eq_intCast_div_two (p N K : ℕ) (a : ℤ) (i : ℕ) :
    ∃ z : ℤ, outerLocalWeight p N K a i = z / 2 := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [outerLocalWeight_zero, outerWeightZero]
    split_ifs
    · exact ⟨-1, by norm_num⟩
    · exact ⟨4 * i - 4, by push_cast; ring⟩
  · obtain ⟨z, hz⟩ := exists_int_two_mul_outerWeight p K N a i
    exact ⟨z, by rw [outerLocalWeight_of_ne_zero ha, ← hz]; ring⟩

/-- Every weight `w_{a,i}` of the outer range is nonpositive. -/
theorem outerLocalWeight_nonpos {p N K : ℕ} (hNK : N ≤ K) (hm : mA p K - mA p N ≤ 2) (a : ℕ)
    {i : ℕ} (hi : i < #(residuePoleIndices p (a : ℤ) N K)) :
    outerLocalWeight p N K a i ≤ 0 := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [Nat.cast_zero, card_residuePoleIndices_zero p hNK] at hi
    rw [Nat.cast_zero, outerLocalWeight_zero]
    exact outerWeightZero_nonpos hm hi
  · rw [outerLocalWeight_of_ne_zero (by exact_mod_cast ha)]
    exact outerWeight_nonpos _ _ _ _ _

/-- The sum of the weights `w_{a,i}`, split into the class `a = 0` and the classes
`1 ≤ a ≤ m°`. -/
theorem sum_sigma_outerLocalWeight (p N K : ℕ) :
    ∑ ai : Σ a : Fin (mStar p + 1), Fin #(residuePoleIndices p (a : ℕ) N K),
        outerLocalWeight p N K (ai.1 : ℕ) ai.2 =
      ∑ i ∈ range #(residuePoleIndices p 0 N K), outerWeightZero (mA p K) (mA p N) i +
        ∑ a ∈ Icc 1 (mStar p), ∑ i ∈ range #(residuePoleIndices p a N K),
          outerWeight p K N a i := by
  rw [sum_sigma_residuePoleIndices p N K fun a i ↦ outerLocalWeight p N K a i]
  simp only [Nat.cast_zero, outerLocalWeight_zero]
  exact congrArg _ (sum_congr rfl fun a ha ↦ sum_congr rfl fun i _ ↦
    outerLocalWeight_of_ne_zero (by grind) i)

/-- The number of vanishing weights `w_{a,i}`, split into the class `a = 0` and the classes
`1 ≤ a ≤ m°`. -/
theorem sum_sigma_ite_outerLocalWeight_eq_zero (p N K : ℕ) :
    ∑ ai : Σ a : Fin (mStar p + 1), Fin #(residuePoleIndices p (a : ℕ) N K),
        (if outerLocalWeight p N K (ai.1 : ℕ) ai.2 = 0 then 1 else 0 : ℕ) =
      #{i ∈ range #(residuePoleIndices p 0 N K) | outerWeightZero (mA p K) (mA p N) i = 0} +
        ∑ a ∈ Icc 1 (mStar p),
          #{i ∈ range #(residuePoleIndices p a N K) | outerWeight p K N a i = 0} := by
  rw [sum_sigma_residuePoleIndices p N K
    fun a i ↦ if outerLocalWeight p N K a i = 0 then 1 else 0]
  simp only [card_filter, Nat.cast_zero, outerLocalWeight_zero]
  exact congrArg _ (sum_congr rfl fun a ha ↦ sum_congr rfl fun i _ ↦ by
    rw [outerLocalWeight_of_ne_zero (by grind) i])

/-- `γ_p^out = 2 ∑ w_{a,i} - min(r_p, z)`, `z` being the number of vanishing weights. -/
theorem intCast_outerExponent_eq_two_mul_sum_sub_min {p N K : ℕ} (hodd : Odd p) (hpK : p ≤ K)
    (hK3 : K < 3 * p) (hN : 2 * N < p) :
    ((outerExponent p N K : ℤ) : ℝ) =
      2 * ((∑ ai : Σ a : Fin (mStar p + 1), Fin #(residuePoleIndices p (a : ℕ) N K),
        outerLocalWeight p N K (ai.1 : ℕ) ai.2 : ℚ) : ℝ) -
      min (outerRankBound K N p : ℝ)
        ((∑ ai : Σ a : Fin (mStar p + 1), Fin #(residuePoleIndices p (a : ℕ) N K),
          if outerLocalWeight p N K (ai.1 : ℕ) ai.2 = 0 then 1 else 0 : ℕ) : ℝ) := by
  rw [sum_sigma_outerLocalWeight, sum_sigma_ite_outerLocalWeight_eq_zero]
  rcases lt_or_ge K (2 * p) with hlt | hle
  · have hs := neg_two_mul_sum_outerWeight_of_lt_two_mul ℚ hodd hpK hlt hN
    have hc := card_filter_outerWeight_eq_zero_of_lt_two_mul ℚ hodd hpK hlt hN
    simp only [natDegree_residuePoleProduct] at hs hc
    rw [hc, outerExponent_of_lt hlt]
    generalize (∑ i ∈ _, _ + _ : ℚ) = S at hs ⊢
    have hs' : (S : ℝ) = -(7 * ((K : ℝ) - p) - 6 * smallClassCount p N K + 1) / 2 := by
      have := congrArg (fun q : ℚ ↦ (q : ℝ)) hs
      push_cast at this
      linarith
    rw [hs', Nat.cast_add, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  · have hs := neg_two_mul_sum_outerWeight_of_two_mul_le ℚ hodd hle hK3 hN
    have hc := card_filter_outerWeight_eq_zero_of_two_mul_le ℚ hodd hle hK3 hN
    simp only [natDegree_residuePoleProduct] at hs hc
    rw [hc, outerExponent_of_le hle]
    generalize (∑ i ∈ _, _ + _ : ℚ) = S at hs ⊢
    have hs' : (S : ℝ) =
        -(7 * ((K : ℝ) - p) - 3 - 12 * N - 5 * smallClassCount p N K) / 2 := by
      have := congrArg (fun q : ℚ ↦ (q : ℝ)) hs
      push_cast at this
      linarith
    rw [hs']
    push_cast
    ring

variable {p : ℕ} [Fact p.Prime]

/-- Over `ℚ_p`, the Gram matrix splits as `G_K = G_K^∘ + p⁻¹ 𝓛_p`. -/
theorem map_gramMatrix_eq_add (n : ℕ) :
    (gramMatrix n).map (Polynomial.map (Rat.castHom ℚ_[p])) =
      outerIntegralGramMatrix p n + (p : ℚ_[p])⁻¹ • outerCorrectionMatrix p n := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hcast : (Rat.castHom ℚ_[p]) = algebraMap ℚ ℚ_[p] := by ext; simp
  rw [outerCorrectionMatrix, smul_smul, inv_mul_cancel₀ hp0, one_smul, hcast, add_sub_cancel]

/-- Over `ℚ_p`, `C^out G_K (C^out)ᵀ = 𝒜 + p⁻¹ 𝓛`, where `𝓛 = C^out 𝓛_p (C^out)ᵀ` has the
`p`-adic integer entries `z`. -/
theorem map_outerCoeffMatrix_mul_gramMatrix_mul_transpose_eq_add {n N K : ℕ}
    {z : (Σ a : Fin (mStar p + 1), Fin #(residuePoleIndices p (a : ℕ) N K)) →
      (Σ a : Fin (mStar p + 1), Fin #(residuePoleIndices p (a : ℕ) N K)) → ℤ_[p]}
    (hz : ∀ ai cj, (outerCoeffMatrix ℚ_[p][X] p N K (matrixOrder n) * outerCorrectionMatrix p n *
      (outerCoeffMatrix ℚ_[p][X] p N K (matrixOrder n)).transpose) ai cj = C (z ai cj : ℚ_[p])) :
    (outerCoeffMatrix ℚ[X] p N K (matrixOrder n) * gramMatrix n *
      (outerCoeffMatrix ℚ[X] p N K (matrixOrder n)).transpose).map
        (Polynomial.map (Rat.castHom ℚ_[p])) =
      outerCoeffMatrix ℚ_[p][X] p N K (matrixOrder n) * outerIntegralGramMatrix p n *
        (outerCoeffMatrix ℚ_[p][X] p N K (matrixOrder n)).transpose +
      (Matrix.of z).map fun x ↦ C ((p : ℚ_[p])⁻¹ * x) := by
  rw [show (Polynomial.map (Rat.castHom ℚ_[p]) : ℚ[X] → ℚ_[p][X]) =
      mapRingHom (Rat.castHom ℚ_[p]) from rfl, Matrix.map_mul, Matrix.map_mul,
    Matrix.transpose_map, map_outerCoeffMatrix,
    show ((gramMatrix n).map (mapRingHom (Rat.castHom ℚ_[p]))) =
      (gramMatrix n).map (Polynomial.map (Rat.castHom ℚ_[p])) from rfl, map_gramMatrix_eq_add,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  ext ai cj : 1
  rw [Matrix.smul_apply, hz, Matrix.map_apply, Matrix.of_apply, smul_eq_C_mul, ← C_mul]

/-- After reindexing by `e`, `v_p^G(Δ_K) = v_p^G(det (𝒜 + p⁻¹ 𝓛))`. -/
theorem vpG_map_gramDet_eq {n : ℕ} (hodd : Odd p) (hpK : p ≤ poleBound n)
    (e : (Σ a : Fin (mStar p + 1),
      Fin #(residuePoleIndices p (a : ℕ) (innerDegree n) (poleBound n))) ≃ Fin (matrixOrder n))
    {z : (Σ a : Fin (mStar p + 1),
        Fin #(residuePoleIndices p (a : ℕ) (innerDegree n) (poleBound n))) →
      (Σ a : Fin (mStar p + 1),
        Fin #(residuePoleIndices p (a : ℕ) (innerDegree n) (poleBound n))) → ℤ_[p]}
    (hz : ∀ ai cj, (outerCoeffMatrix ℚ_[p][X] p (innerDegree n) (poleBound n) (matrixOrder n) *
      outerCorrectionMatrix p n *
      (outerCoeffMatrix ℚ_[p][X] p (innerDegree n) (poleBound n) (matrixOrder n)).transpose)
        ai cj = C (z ai cj : ℚ_[p])) :
    vpG ((gramDet n).map (Rat.castHom ℚ_[p])) =
      vpG ((outerCoeffMatrix ℚ_[p][X] p (innerDegree n) (poleBound n) (matrixOrder n) *
        outerIntegralGramMatrix p n *
        (outerCoeffMatrix ℚ_[p][X] p (innerDegree n) (poleBound n) (matrixOrder n)).transpose
        ).submatrix e.symm e.symm +
        ((Matrix.of z).submatrix e.symm e.symm).map fun x ↦ C ((p : ℚ_[p])⁻¹ * x)).det := by
  rw [← vpG_map_det_outerCoeffMatrix_mul_gramMatrix_mul_transpose hodd hpK,
    show ((outerCoeffMatrix ℚ[X] p (innerDegree n) (poleBound n) (matrixOrder n) * gramMatrix n *
      (outerCoeffMatrix ℚ[X] p (innerDegree n) (poleBound n) (matrixOrder n)).transpose).det).map
        (Rat.castHom ℚ_[p]) =
      ((outerCoeffMatrix ℚ[X] p (innerDegree n) (poleBound n) (matrixOrder n) * gramMatrix n *
      (outerCoeffMatrix ℚ[X] p (innerDegree n) (poleBound n) (matrixOrder n)).transpose).map
        (Polynomial.map (Rat.castHom ℚ_[p]))).det from
      RingHom.map_det (mapRingHom (Rat.castHom ℚ_[p])) _,
    map_outerCoeffMatrix_mul_gramMatrix_mul_transpose_eq_add hz,
    ← Matrix.det_submatrix_equiv_self e.symm]
  rfl

/-- After reindexing by `e`, the constant correction `𝓛` has rank at most `r_p` over `ℚ_p`. -/
theorem rank_map_submatrix_le_outerRankBound (n : ℕ)
    (e : (Σ a : Fin (mStar p + 1),
      Fin #(residuePoleIndices p (a : ℕ) (innerDegree n) (poleBound n))) ≃ Fin (matrixOrder n))
    {z : (Σ a : Fin (mStar p + 1),
        Fin #(residuePoleIndices p (a : ℕ) (innerDegree n) (poleBound n))) →
      (Σ a : Fin (mStar p + 1),
        Fin #(residuePoleIndices p (a : ℕ) (innerDegree n) (poleBound n))) → ℤ_[p]}
    (hz : ∀ ai cj, (outerCoeffMatrix ℚ_[p][X] p (innerDegree n) (poleBound n) (matrixOrder n) *
      outerCorrectionMatrix p n *
      (outerCoeffMatrix ℚ_[p][X] p (innerDegree n) (poleBound n) (matrixOrder n)).transpose)
        ai cj = C (z ai cj : ℚ_[p])) :
    (((Matrix.of z).submatrix e.symm e.symm).map ((↑) : ℤ_[p] → ℚ_[p])).rank ≤
      outerRankBound (poleBound n) (innerDegree n) p := by
  set Cq := outerCoeffMatrix ℚ_[p][X] p (innerDegree n) (poleBound n) (matrixOrder n)
  have h1 : ((Matrix.of z).submatrix e.symm e.symm).map ((↑) : ℤ_[p] → ℚ_[p]) =
      ((Cq * outerCorrectionMatrix p n * Cq.transpose).map constantCoeff).submatrix
        e.symm e.symm := by
    ext r s
    change ((z (e.symm r) (e.symm s) : ℤ_[p]) : ℚ_[p]) =
      constantCoeff ((Cq * outerCorrectionMatrix p n * Cq.transpose) (e.symm r) (e.symm s))
    rw [hz, constantCoeff_apply, coeff_C_zero]
  rw [h1, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, map_outerCoeffMatrix]
  exact (Matrix.rank_submatrix_le _ _ _).trans
    (rank_outerCoeffMatrix_mul_outerCorrectionMatrix_mul_transpose_le n)

/-- The entries of `𝒜 = C^out G_K^∘ (C^out)ᵀ` satisfy
`v_p^G(𝒜_{(a,i),(c,j)}) ≥ w_{a,i} + w_{c,j}`. -/
theorem outerLocalWeight_add_le_vpG_conj (hp7 : 7 ≤ p) {n : ℕ} (hpK : p ≤ poleBound n)
    (hK3 : poleBound n < 3 * p) (hK2 : 2 * poleBound n < p ^ 2)
    (hN : 2 * innerDegree n < p)
    (ai cj : Σ a : Fin (mStar p + 1),
      Fin #(residuePoleIndices p (a : ℕ) (innerDegree n) (poleBound n))) :
    (((outerLocalWeight p (innerDegree n) (poleBound n) (ai.1 : ℕ) ai.2 : ℝ) +
        (outerLocalWeight p (innerDegree n) (poleBound n) (cj.1 : ℕ) cj.2 : ℝ) : ℝ) :
        WithTop ℝ) ≤
      (vpG ((outerCoeffMatrix ℚ_[p][X] p (innerDegree n) (poleBound n) (matrixOrder n) *
        outerIntegralGramMatrix p n *
        (outerCoeffMatrix ℚ_[p][X] p (innerDegree n) (poleBound n) (matrixOrder n)).transpose)
          ai cj)).map ((↑) : ℤ → ℝ) := by
  have h1 := outerLocalWeight_add_le_vpG_outerIntegralForm hp7 hpK hK3 hK2 hN
    (Nat.lt_succ_iff.mp ai.1.2) (Nat.lt_succ_iff.mp cj.1.2) ai.2.2 cj.2.2
  rw [outerCoeffMatrix_mul_outerIntegralGramMatrix_mul_transpose_apply (by omega) hpK]
  generalize vpG (p := p) _ = v at h1 ⊢
  induction v with
  | top => simp
  | coe v =>
    rw [WithTop.map_coe, WithTop.coe_le_coe] at h1 ⊢
    exact_mod_cast h1

/-- **The outer range** (§5.12). Let `K = 40 n` and let `p` be a prime with `p ≥ 7`,
`p ≤ K < 3 p`, `p² > 2 K` and `2 N < p`, where `N = 3 n`. Then `v_p^G(Δ_K) ≥ γ_p^out`. -/
@[zeta5irr "prop_outer"]
theorem outerExponent_le_vpG_gramDet (hp7 : 7 ≤ p) {n : ℕ} (hpK : p ≤ poleBound n)
    (hK3 : poleBound n < 3 * p) (hK2 : 2 * poleBound n < p ^ 2)
    (hN : 2 * innerDegree n < p) :
    (outerExponent p (innerDegree n) (poleBound n) : WithTop ℤ) ≤
      vpG ((gramDet n).map (Rat.castHom ℚ_[p])) := by
  classical
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  set N := innerDegree n with hNdef
  set K := poleBound n with hKdef
  set h := matrixOrder n
  let e := Fintype.equivFinOfCardEq (card_outerCoeffMatrix_rows_eq_matrixOrder hodd n)
  set Cq := outerCoeffMatrix ℚ_[p][X] p N K h
  choose z hz using
    exists_outerCoeffMatrix_mul_outerCorrectionMatrix_mul_transpose_apply_eq_C
      (by omega : 5 ≤ p) n N K
  have hNK : N ≤ K := by simp only [hNdef, hKdef, innerDegree, poleBound]; omega
  have hmN : mA p N = 0 := mA_eq_zero_of_two_mul_lt (by omega)
  have hmK : mA p K < 3 := (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)
  let wq : (Σ a : Fin (mStar p + 1), Fin #(residuePoleIndices p (a : ℕ) N K)) → ℚ :=
    fun ai ↦ outerLocalWeight p N K (ai.1 : ℕ) ai.2
  let w : Fin h → ℝ := fun r ↦ (wq (e.symm r) : ℝ)
  have hw_nonpos (r : Fin h) : w r ≤ 0 :=
    Rat.cast_nonpos.2 (outerLocalWeight_nonpos hNK (by omega) _ (e.symm r).2.2)
  have hw_half (r : Fin h) : ∃ m : ℤ, w r = m / 2 := by
    obtain ⟨m, hm⟩ := exists_outerLocalWeight_eq_intCast_div_two p N K ((e.symm r).1 : ℕ)
      (e.symm r).2
    exact ⟨m, by simp only [w, wq, hm]; push_cast; ring⟩
  have key := two_mul_sum_sub_min_le_vpG_det_add
    ((Cq * outerIntegralGramMatrix p n * Cq.transpose).submatrix e.symm e.symm)
    ((Matrix.of z).submatrix e.symm e.symm) w hw_nonpos hw_half
    (fun r s ↦ outerLocalWeight_add_le_vpG_conj hp7 hpK hK3 hK2 hN (e.symm r) (e.symm s)) _
    (rank_map_submatrix_le_outerRankBound n e hz)
  have hγ : ((outerExponent p N K : ℤ) : ℝ) =
      2 * ∑ r, w r - min (outerRankBound K N p : ℝ) (#{r | w r = 0} : ℝ) := by
    have hsum : ∑ r, w r = ((∑ ai, wq ai : ℚ) : ℝ) := by
      rw [Rat.cast_sum]
      exact Equiv.sum_comp e.symm (fun ai ↦ (wq ai : ℝ))
    have hcard : #{r | w r = 0} = ∑ ai, if wq ai = 0 then 1 else 0 := by
      rw [card_filter]
      simp only [w, Rat.cast_eq_zero]
      exact Equiv.sum_comp e.symm (fun ai ↦ if wq ai = 0 then 1 else 0)
    rw [hsum, hcard]
    exact intCast_outerExponent_eq_two_mul_sum_sub_min hodd hpK hK3 hN
  rw [vpG_map_gramDet_eq hodd hpK e hz]
  rw [← hγ, intCast_le_map_intCast_iff] at key
  exact key

end Zeta5Irr
