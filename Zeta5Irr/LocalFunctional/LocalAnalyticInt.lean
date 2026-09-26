/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.BTUnique
public import Zeta5Irr.LocalFunctional.KappaInt
public import Zeta5Irr.LocalFunctional.LocalSeriesConv
public import Zeta5Irr.LocalFunctional.TauAnNorm
public import Zeta5Irr.LocalFunctional.TauTateMul
public import Zeta5Irr.LocalFunctional.Tauext
public import Mathlib.Data.Finset.Slice
public import Mathlib.RingTheory.PiTensorProduct

/-!
# Integrality of `τ^an` on quotients of `∑ p^j U_j` by `E_R`

Let `p ≥ 5` be a prime, `R ⊆ ℤ` finite, and `U_j ∈ ℤ_p[z]` for `j ≥ 0` with `deg U_0 ≤ p + 1`.
Suppose `q ∈ 𝒜 = ℚ_p⟨z⟩` and `b ∈ ℚ_p[z]` with `deg b < #R` satisfy
`∑_{j ≥ 0} p^j U_j = q E_R + b` in `𝒜`, where `E_R = ∏_{r ∈ R} (z - r)`. Then
`τ^an(q) ∈ ℤ_p`.

Dividing each `U_j` by the monic polynomial `E_R` gives `U_j = q_j E_R + b_j` with
`q_j, b_j ∈ ℤ_p[z]` and `deg b_j < #R`. The partial sums `Q_J = ∑_{j < J} p^j q_j` converge in
`𝒜` to some `q'`; comparing coefficients of index `≥ #R` in the limit of
`∑_{j < J} p^j U_j = Q_J E_R + ∑_{j < J} p^j b_j` shows that `q E_R + b - q' E_R` is a
polynomial of degree `< #R`, so `q = q'` by uniqueness of the quotient. As `τ^an` is continuous,
`τ^an(q) = lim τ^an(Q_J)`. Finally `τ^an(q_0) = ∑_{d ≤ p + 1} (q_0)_d κ_d ∈ ℤ_p` since
`κ_d ∈ ℤ_p` for `d ≤ p + 1`, while for `j ≥ 1`, `|p^j τ^an(q_j)|_p ≤ p^{-j} · p ≤ 1`; hence
every `τ^an(Q_J)` lies in the closed set `ℤ_p`, and so does the limit.

## Main results

* `Zeta5Irr.norm_tauAn_le_one_of_tendsto`: `|τ^an(q)|_p ≤ 1`.
* `Zeta5Irr.exists_padicInt_eq_tauAn_of_tendsto`: `τ^an(q)` is the image of a `p`-adic
  integer.

## Implementation notes

* The hypothesis `∑_{j ≥ 0} p^j U_j = q E_R + b` in `𝒜` is stated as convergence of the
  partial sums `∑_{j < J} p^j U_j` to `q E_R + b` in the Gauss norm, the form in which
  convergence in `𝒜` is expressed throughout.
* The source's hypotheses that `R` is nonempty and that `r - r'` is a `p`-adic unit for distinct
  `r, r' ∈ R` are not needed. The source uses the latter to show that the quotient of `U_j` by
  `E_R` is integral; here this follows directly from Euclidean division over `ℤ_p` by the monic
  polynomial `E_R ∈ ℤ_p[z]`, which commutes with the inclusion `ℤ_p[z] → ℚ_p[z]`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.4 (Completion at a prime).
-/

@[expose] public section

namespace Zeta5Irr

open PowerSeries Filter Topology Finset

variable {p : ℕ} [Fact p.Prime]

/-- `τ^an` commutes with subtraction on `ℚ_p⟨z⟩`. -/
theorem tauAn_sub (hp5 : 5 ≤ p) {f g : ℚ_[p]⟦X⟧} (hf : f ∈ tateAlgebra p)
    (hg : g ∈ tateAlgebra p) : tauAn (f - g) = tauAn f - tauAn g :=
  tauAn_eq_of_hasSum <| by
    simpa [sub_mul] using
      (hasSum_coeff_mul_kappa_tauAn hp5 hf).sub (hasSum_coeff_mul_kappa_tauAn hp5 hg)

/-- `τ^an` is continuous for the Gauss norm on `ℚ_p⟨z⟩`. -/
theorem tendsto_tauAn_of_tendsto_tateNorm (hp5 : 5 ≤ p) {F : ℕ → ℚ_[p]⟦X⟧} {f : ℚ_[p]⟦X⟧}
    (hF : ∀ J, F J ∈ tateAlgebra p) (hf : f ∈ tateAlgebra p)
    (h : Tendsto (fun J => tateNorm (F J - f)) atTop (𝓝 0)) :
    Tendsto (fun J => tauAn (F J)) atTop (𝓝 (tauAn f)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun J => ?_) (by simpa using h.const_mul (p : ℝ))
  rw [← tauAn_sub hp5 (hF J) hf]
  exact norm_tauAn_le hp5 (sub_mem (hF J) hf)

/-- For `V_j ∈ ℤ_p[z]` with `deg V_0 ≤ p + 1`, every partial sum `∑_{j < J} p^j V_j` satisfies
`|τ^an(∑_{j < J} p^j V_j)|_p ≤ 1`. -/
theorem norm_tauAn_sum_pow_smul_le_one (hp5 : 5 ≤ p) (V : ℕ → Polynomial ℤ_[p])
    (hV0 : (V 0).natDegree ≤ p + 1) (J : ℕ) :
    ‖tauAn (∑ j ∈ range J, (p : ℚ_[p]) ^ j •
      (((V j).map PadicInt.Coe.ringHom : Polynomial ℚ_[p]) : ℚ_[p]⟦X⟧))‖ ≤ 1 := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hterm : ∀ j, ‖tauAn ((p : ℚ_[p]) ^ j •
      (((V j).map PadicInt.Coe.ringHom : Polynomial ℚ_[p]) : ℚ_[p]⟦X⟧))‖ ≤ 1 := by
    intro j
    rw [tauAn_smul, norm_mul, norm_pow, Padic.norm_p]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [pow_zero, one_mul, tauAn_coe_polynomial]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun d hd => ?_
      have hdeg : d ≤ p + 1 :=
        ((Polynomial.le_natDegree_of_mem_supp d hd).trans Polynomial.natDegree_map_le).trans hV0
      rw [norm_mul, Polynomial.coeff_map]
      exact (mul_le_mul ((V 0).coeff d).norm_le_one (norm_kappa_le_one hp5 hdeg) (norm_nonneg _)
        zero_le_one).trans_eq (mul_one 1)
    · calc ((p : ℝ)⁻¹) ^ j * ‖tauAn (((V j).map PadicInt.Coe.ringHom : Polynomial ℚ_[p]) :
            ℚ_[p]⟦X⟧)‖
          ≤ (p : ℝ)⁻¹ * (p * 1) := by
            refine mul_le_mul (pow_le_of_le_one (by positivity) (inv_le_one_of_one_le₀ hp.le)
              hj.ne') ((norm_tauAn_le hp5 (coe_mem_tateAlgebra _)).trans ?_) (norm_nonneg _)
              (by positivity)
            exact mul_le_mul_of_nonneg_left (tateNorm_map_coe_le_one _) (by positivity)
        _ = 1 := by field_simp
  have tauAn_add : ∀ {f g : ℚ_[p]⟦X⟧}, f ∈ tateAlgebra p → g ∈ tateAlgebra p →
      tauAn (f + g) = tauAn f + tauAn g := fun hf hg =>
    tauAn_eq_of_hasSum <| by
      simpa [add_mul] using
        (hasSum_coeff_mul_kappa_tauAn hp5 hf).add (hasSum_coeff_mul_kappa_tauAn hp5 hg)
  induction J with
  | zero => simp
  | succ J ih =>
    rw [sum_range_succ, tauAn_add (sum_mem fun j _ => Subalgebra.smul_mem _
      (coe_mem_tateAlgebra _) _) (Subalgebra.smul_mem _ (coe_mem_tateAlgebra _) _)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih (hterm J))

/-- Euclidean division by `E_R` over `ℤ_p`, summed: `∑_{j < J} p^j U_j = Q_J E_R + B_J` where
`Q_J = ∑_{j < J} p^j (U_j /ₘ E_R)` and `B_J = ∑_{j < J} p^j (U_j %ₘ E_R)`. -/
theorem sum_pow_smul_map_coe_eq_divByMonic_add_modByMonic (R : Finset ℤ)
    (U : ℕ → Polynomial ℤ_[p]) (J : ℕ) :
    ∑ j ∈ range J, (p : ℚ_[p]) ^ j •
      (((U j).map PadicInt.Coe.ringHom : Polynomial ℚ_[p]) : ℚ_[p]⟦X⟧) =
    (∑ j ∈ range J, (p : ℚ_[p]) ^ j • (((U j /ₘ intPoleProduct R ℤ_[p]).map
      PadicInt.Coe.ringHom : Polynomial ℚ_[p]) : ℚ_[p]⟦X⟧)) *
        (intPoleProduct R ℚ_[p] : ℚ_[p]⟦X⟧) +
      ∑ j ∈ range J, (p : ℚ_[p]) ^ j • (((U j %ₘ intPoleProduct R ℤ_[p]).map
        PadicInt.Coe.ringHom : Polynomial ℚ_[p]) : ℚ_[p]⟦X⟧) := by
  have hUj : ∀ j, (((U j).map PadicInt.Coe.ringHom : Polynomial ℚ_[p]) : ℚ_[p]⟦X⟧) =
      (((U j /ₘ intPoleProduct R ℤ_[p]).map PadicInt.Coe.ringHom : Polynomial ℚ_[p]) :
        ℚ_[p]⟦X⟧) * (intPoleProduct R ℚ_[p] : ℚ_[p]⟦X⟧) +
        (((U j %ₘ intPoleProduct R ℤ_[p]).map PadicInt.Coe.ringHom : Polynomial ℚ_[p]) :
          ℚ_[p]⟦X⟧) := by
    intro j
    rw [← map_intPoleProduct R ℤ_[p] PadicInt.Coe.ringHom, ← Polynomial.coe_mul,
      ← Polynomial.coe_add, ← Polynomial.map_mul, ← Polynomial.map_add]
    congr 2
    linear_combination (Polynomial.modByMonic_add_div (U j) (intPoleProduct R ℤ_[p])).symm
  simp only [hUj, smul_add, sum_add_distrib, sum_mul, smul_mul_assoc]

/-- The coefficients of index `≥ #R` of `∑_{j < J} p^j (U_j %ₘ E_R)` vanish. -/
theorem coeff_sum_pow_smul_map_modByMonic_eq_zero (R : Finset ℤ) (U : ℕ → Polynomial ℤ_[p])
    (J : ℕ) {n : ℕ} (hn : #R ≤ n) :
    coeff n (∑ j ∈ range J, (p : ℚ_[p]) ^ j • (((U j %ₘ intPoleProduct R ℤ_[p]).map
      PadicInt.Coe.ringHom : Polynomial ℚ_[p]) : ℚ_[p]⟦X⟧)) = 0 := by
  refine (map_sum _ _ _).trans (sum_eq_zero fun j _ => ?_)
  rw [map_smul, Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_degree_lt, smul_zero]
  calc _ ≤ (U j %ₘ intPoleProduct R ℤ_[p]).degree := Polynomial.degree_map_le
    _ < (intPoleProduct R ℤ_[p]).degree :=
      Polynomial.degree_modByMonic_lt _ (monic_intPoleProduct R ℤ_[p])
    _ = #R := degree_intPoleProduct R ℤ_[p]
    _ ≤ n := by exact_mod_cast hn

/-- If `S_J = Q_J e + B_J` in `ℚ_p⟨z⟩` with `S_J → g`, `Q_J → q'` and the coefficients of index
`≥ N` of every `B_J` vanishing, then so do those of `g - q' e`. -/
theorem coeff_sub_mul_eq_zero_of_tendsto {S Q B : ℕ → ℚ_[p]⟦X⟧} {g q' e : ℚ_[p]⟦X⟧} {N : ℕ}
    (hS : ∀ J, S J ∈ tateAlgebra p) (hQ : ∀ J, Q J ∈ tateAlgebra p) (hg : g ∈ tateAlgebra p)
    (hq' : q' ∈ tateAlgebra p) (he : e ∈ tateAlgebra p) (hSQB : ∀ J, S J = Q J * e + B J)
    (hB : ∀ J n, N ≤ n → coeff n (B J) = 0)
    (hSlim : Tendsto (fun J => tateNorm (S J - g)) atTop (𝓝 0))
    (hQlim : Tendsto (fun J => tateNorm (Q J - q')) atTop (𝓝 0)) {n : ℕ} (hn : N ≤ n) :
    coeff n (g - q' * e) = 0 := by
  have hbound : ∀ J, ‖coeff n (g - q' * e)‖ ≤
      tateNorm (S J - g) + tateNorm (Q J - q') * tateNorm e := by
    intro J
    have hDJ : g - q' * e = -(S J - g) + (Q J - q') * e + B J := by
      rw [hSQB]
      ring
    have h1 := le_tateNorm (sub_mem (hS J) hg) n
    have h2 := (le_tateNorm (mul_mem_tateAlgebra (sub_mem (hQ J) hq') he) n).trans
      (tateNorm_mul_le (sub_mem (hQ J) hq') he)
    rw [hDJ, map_add, map_add, hB J n hn, add_zero, map_neg]
    exact (norm_add_le _ _).trans (add_le_add (by rwa [norm_neg]) h2)
  exact norm_le_zero_iff.mp <| ge_of_tendsto' (by simpa using hSlim.add (hQlim.mul_const _)) hbound

/-- **Integrality of the quotient.** If `∑_{j ≥ 0} p^j U_j = q E_R + b` in `ℚ_p⟨z⟩` with
`deg b < #R`, then `q = ∑_{j ≥ 0} p^j (U_j /ₘ E_R)`. -/
theorem tendsto_tateNorm_sum_pow_smul_divByMonic_sub (R : Finset ℤ) (U : ℕ → Polynomial ℤ_[p])
    {q : ℚ_[p]⟦X⟧} (hq : q ∈ tateAlgebra p) {b : Polynomial ℚ_[p]} (hb : b.degree < #R)
    (h : Tendsto (fun J => tateNorm (∑ j ∈ range J, (p : ℚ_[p]) ^ j •
      (((U j).map PadicInt.Coe.ringHom : Polynomial ℚ_[p]) : ℚ_[p]⟦X⟧) -
        (q * (intPoleProduct R ℚ_[p] : ℚ_[p]⟦X⟧) + (b : ℚ_[p]⟦X⟧)))) atTop (𝓝 0)) :
    Tendsto (fun J => tateNorm (∑ j ∈ range J, (p : ℚ_[p]) ^ j • (((U j /ₘ intPoleProduct R
      ℤ_[p]).map PadicInt.Coe.ringHom : Polynomial ℚ_[p]) : ℚ_[p]⟦X⟧) - q)) atTop (𝓝 0) := by
  obtain ⟨q', hq'mem, hq'⟩ :=
    exists_tendsto_tateNorm_sum_pow_smul_sub (p := p) fun j => U j /ₘ intPoleProduct R ℤ_[p]
  have hmem : ∀ (V : ℕ → Polynomial ℤ_[p]) J, ∑ j ∈ range J, (p : ℚ_[p]) ^ j •
      (((V j).map PadicInt.Coe.ringHom : Polynomial ℚ_[p]) : ℚ_[p]⟦X⟧) ∈ tateAlgebra p :=
    fun _ _ => sum_mem fun _ _ => Subalgebra.smul_mem _ (coe_mem_tateAlgebra _) _
  have hE := coe_mem_tateAlgebra (p := p) (intPoleProduct R ℚ_[p])
  have hD := fun n (hn : #R ≤ n) => coeff_sub_mul_eq_zero_of_tendsto (hmem U) (hmem _)
    (add_mem (mul_mem_tateAlgebra hq hE) (coe_mem_tateAlgebra b)) hq'mem hE
    (sum_pow_smul_map_coe_eq_divByMonic_add_modByMonic R U)
    (fun J _ => coeff_sum_pow_smul_map_modByMonic_eq_zero R U J) h hq' hn
  set D := q * (intPoleProduct R ℚ_[p] : ℚ_[p]⟦X⟧) + (b : ℚ_[p]⟦X⟧) -
    q' * (intPoleProduct R ℚ_[p] : ℚ_[p]⟦X⟧) with hDdef
  have hDb : D = (trunc #R D : ℚ_[p]⟦X⟧) := by
    ext n
    rw [Polynomial.coeff_coe, coeff_trunc]
    split_ifs with hn
    · rfl
    · exact hD n (not_lt.mp hn)
  obtain rfl : q = q' := eq_of_mul_intPoleProduct_add_eq R hq hq'mem hb (degree_trunc_lt D #R) <| by
    rw [← hDb, hDdef]
    ring
  exact hq'

/-- **Integrality of `τ^an(q)`.** Let `p ≥ 5` be a prime, `R ⊆ ℤ` finite and `U_j ∈ ℤ_p[z]` with
`deg U_0 ≤ p + 1`. If `q ∈ ℚ_p⟨z⟩` and `b ∈ ℚ_p[z]` with `deg b < #R` satisfy
`∑_{j ≥ 0} p^j U_j = q E_R + b` in `ℚ_p⟨z⟩`, then `|τ^an(q)|_p ≤ 1`. -/
@[zeta5irr "lem_local_analytic_int"]
theorem norm_tauAn_le_one_of_tendsto (hp5 : 5 ≤ p) (R : Finset ℤ) (U : ℕ → Polynomial ℤ_[p])
    (hU0 : (U 0).natDegree ≤ p + 1) {q : ℚ_[p]⟦X⟧} (hq : q ∈ tateAlgebra p)
    {b : Polynomial ℚ_[p]} (hb : b.degree < #R)
    (h : Tendsto (fun J => tateNorm (∑ j ∈ range J, (p : ℚ_[p]) ^ j •
      (((U j).map PadicInt.Coe.ringHom : Polynomial ℚ_[p]) : ℚ_[p]⟦X⟧) -
        (q * (intPoleProduct R ℚ_[p] : ℚ_[p]⟦X⟧) + (b : ℚ_[p]⟦X⟧)))) atTop (𝓝 0)) :
    ‖tauAn q‖ ≤ 1 := by
  have hU0' : (U 0 /ₘ intPoleProduct R ℤ_[p]).natDegree ≤ p + 1 := by
    rw [Polynomial.natDegree_divByMonic _ (monic_intPoleProduct R ℤ_[p])]
    omega
  refine le_of_tendsto' (tendsto_tauAn_of_tendsto_tateNorm hp5
    (fun J => sum_mem fun _ _ => Subalgebra.smul_mem _ (coe_mem_tateAlgebra _) _) hq
    (tendsto_tateNorm_sum_pow_smul_divByMonic_sub R U hq hb h)).norm fun J => ?_
  exact norm_tauAn_sum_pow_smul_le_one hp5 (fun j => U j /ₘ intPoleProduct R ℤ_[p]) hU0' J

/-- **Integrality of `τ^an(q)`.** Let `p ≥ 5` be a prime, `R ⊆ ℤ` finite and `U_j ∈ ℤ_p[z]` with
`deg U_0 ≤ p + 1`. If `q ∈ ℚ_p⟨z⟩` and `b ∈ ℚ_p[z]` with `deg b < #R` satisfy
`∑_{j ≥ 0} p^j U_j = q E_R + b` in `ℚ_p⟨z⟩`, then `τ^an(q) ∈ ℤ_p`. -/
@[zeta5irr "lem_local_analytic_int"]
theorem exists_padicInt_eq_tauAn_of_tendsto (hp5 : 5 ≤ p) (R : Finset ℤ)
    (U : ℕ → Polynomial ℤ_[p]) (hU0 : (U 0).natDegree ≤ p + 1) {q : ℚ_[p]⟦X⟧}
    (hq : q ∈ tateAlgebra p) {b : Polynomial ℚ_[p]} (hb : b.degree < #R)
    (h : Tendsto (fun J => tateNorm (∑ j ∈ range J, (p : ℚ_[p]) ^ j •
      (((U j).map PadicInt.Coe.ringHom : Polynomial ℚ_[p]) : ℚ_[p]⟦X⟧) -
        (q * (intPoleProduct R ℚ_[p] : ℚ_[p]⟦X⟧) + (b : ℚ_[p]⟦X⟧)))) atTop (𝓝 0)) :
    ∃ x : ℤ_[p], (x : ℚ_[p]) = tauAn q :=
  ⟨⟨_, norm_tauAn_le_one_of_tendsto hp5 R U hU0 hq hb h⟩, rfl⟩

end Zeta5Irr
