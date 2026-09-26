/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.IntPoleProduct
public import Zeta5Irr.LocalFunctional.TauTate
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Uniqueness of the quotient in division by `E_R` in `ℚ_p⟨z⟩`

Let `R ⊆ ℤ` be finite and let `E_R = ∏_{r ∈ R} (z - r)`. If `q, q' ∈ ℚ_p⟨z⟩` and
`b, b' ∈ ℚ_p[z]` have `deg b, deg b' < #R` and `q E_R + b = q' E_R + b'` in `ℚ_p[[z]]`, then
`q = q'`. Equivalently, if `g ∈ ℚ_p⟨z⟩` and `g E_R` is a polynomial of degree `< #R`, then
`g = 0`.

The proof is by the ultrametric inequality: if `g ≠ 0`, let `e` be the largest index at which
`|g_e|_p` attains `‖g‖`. The coefficient of `z^{e + #R}` of `g E_R` is
`g_e + ∑_{i < #R} a_i g_{e + #R - i}`, where the `a_i` are the lower coefficients of `E_R`,
integers and hence of norm `≤ 1`; every term of the sum has norm `< ‖g‖`, so this coefficient
is nonzero.

## Main results

* `Zeta5Irr.eq_zero_of_mem_tateAlgebra_of_coeff_mul_eq_zero`: if `g ∈ ℚ_p⟨z⟩`, `E` is a monic
  polynomial with coefficients of norm `≤ 1`, and all coefficients of `g E` of index
  `≥ deg E` vanish, then `g = 0`.
* `Zeta5Irr.eq_of_mul_intPoleProduct_add_eq`: the uniqueness of the quotient `q` in
  `q E_R + b` with `deg b < #R`.

## Implementation notes

The source assumes `R` nonempty; this is not needed, since for `R = ∅` the hypothesis
`deg b < 0` forces `b = 0` and `E_∅ = 1`. The argument works for any monic divisor whose
coefficients have norm at most `1`, and is stated in that generality first.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.4 (Completion at a prime).
-/

@[expose] public section

namespace Zeta5Irr

open PowerSeries Filter Topology Finset

variable {p : ℕ} [Fact p.Prime]

/-- If `g ∈ ℚ_p⟨z⟩` and `E` is a monic polynomial whose coefficients have norm at most `1`,
and every coefficient of `g E` of index at least `deg E` vanishes, then `g = 0`. -/
theorem eq_zero_of_mem_tateAlgebra_of_coeff_mul_eq_zero {g : ℚ_[p]⟦X⟧}
    (hg : g ∈ tateAlgebra p) {E : Polynomial ℚ_[p]} (hE : E.Monic)
    (hE1 : ∀ i, ‖E.coeff i‖ ≤ 1)
    (h : ∀ n, E.natDegree ≤ n → coeff n (g * (E : ℚ_[p]⟦X⟧)) = 0) : g = 0 := by
  by_contra hg0
  obtain ⟨d₀, hd₀⟩ : ∃ d, coeff d g ≠ 0 := by
    by_contra! H
    exact hg0 (PowerSeries.ext fun n => by simpa using H n)
  set ε := ‖coeff d₀ g‖ with hε
  have hεpos : 0 < ε := norm_pos_iff.mpr hd₀
  obtain ⟨N, hN⟩ : ∃ N, ∀ d, N ≤ d → ‖coeff d g‖ < ε := by
    have := (mem_tateAlgebra_iff.mp hg).eventually (gt_mem_nhds hεpos)
    simpa using this
  have hd₀N : d₀ < N := by
    by_contra! H
    exact (hN d₀ H).false
  have hne : (range N).Nonempty := ⟨d₀, mem_range.mpr hd₀N⟩
  set M := (range N).sup' hne fun d => ‖coeff d g‖ with hM
  have hεM : ε ≤ M := le_sup' (fun d => ‖coeff d g‖) (mem_range.mpr hd₀N)
  have hle : ∀ d, ‖coeff d g‖ ≤ M := by
    intro d
    rcases lt_or_ge d N with hd | hd
    · exact le_sup' (fun d => ‖coeff d g‖) (mem_range.mpr hd)
    · exact (hN d hd).le.trans hεM
  obtain ⟨d₁, hd₁, hd₁M⟩ := exists_mem_eq_sup' hne fun d => ‖coeff d g‖
  set S := (range N).filter fun d => ‖coeff d g‖ = M with hS
  have hSne : S.Nonempty := ⟨d₁, mem_filter.mpr ⟨hd₁, hd₁M.symm⟩⟩
  set e := S.max' hSne with he
  have heS : e ∈ S := max'_mem S hSne
  have heM : ‖coeff e g‖ = M := (mem_filter.mp heS).2
  have hgt : ∀ m, e < m → ‖coeff m g‖ < M := by
    intro m hm
    rcases lt_or_ge m N with hmN | hmN
    · refine lt_of_le_of_ne (hle m) fun hmM => ?_
      have : m ∈ S := mem_filter.mpr ⟨mem_range.mpr hmN, hmM⟩
      exact absurd (le_max' S m this) (not_le.mpr hm)
    · exact (hN m hmN).trans_le hεM
  set t := E.natDegree
  have hcoeff := h (e + t) le_add_self
  have het : (e, t) ∈ antidiagonal (e + t) := HasAntidiagonal.mem_antidiagonal.mpr rfl
  rw [coeff_mul, ← add_sum_erase _ _ het] at hcoeff
  have hEt : E.coeff t = 1 := hE.coeff_natDegree
  simp only [Polynomial.coeff_coe, hEt, mul_one] at hcoeff
  have hrest : ‖∑ x ∈ (antidiagonal (e + t)).erase (e, t), coeff x.1 g * E.coeff x.2‖ < M := by
    obtain ⟨x, hx, hxle⟩ := IsUltrametricDist.exists_norm_finsetSum_le
      ((antidiagonal (e + t)).erase (e, t)) fun x : ℕ × ℕ => coeff x.1 g * E.coeff x.2
    rcases ((antidiagonal (e + t)).erase (e, t)).eq_empty_or_nonempty with H | H
    · rw [H, sum_empty, norm_zero]
      exact hεpos.trans_le hεM
    refine hxle.trans_lt ?_
    obtain ⟨hxne, hxa⟩ := mem_erase.mp (hx H)
    rw [HasAntidiagonal.mem_antidiagonal] at hxa
    rw [norm_mul]
    rcases le_or_gt x.1 e with h1 | h1
    · have h2 : t < x.2 := by
        refine lt_of_le_of_ne (by omega) fun h2 => hxne ?_
        exact Prod.ext (by omega) h2.symm
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt h2, norm_zero, mul_zero]
      exact hεpos.trans_le hεM
    · calc ‖coeff x.1 g‖ * ‖E.coeff x.2‖ ≤ ‖coeff x.1 g‖ * 1 :=
            mul_le_mul_of_nonneg_left (hE1 _) (norm_nonneg _)
        _ < M := by rw [mul_one]; exact hgt _ h1
  have : coeff e g = -∑ x ∈ (antidiagonal (e + t)).erase (e, t), coeff x.1 g * E.coeff x.2 :=
    eq_neg_of_add_eq_zero_left hcoeff
  rw [this, norm_neg] at heM
  exact hrest.ne heM

/-- **Uniqueness of the quotient in division by `E_R`.** Let `R ⊆ ℤ` be finite, `q, q' ∈ ℚ_p⟨z⟩`
and `b, b' ∈ ℚ_p[z]` with `deg b < #R` and `deg b' < #R`. If `q E_R + b = q' E_R + b'` in
`ℚ_p[[z]]`, then `q = q'`. -/
@[zeta5irr "lem_BT_unique"]
theorem eq_of_mul_intPoleProduct_add_eq (R : Finset ℤ) {q q' : ℚ_[p]⟦X⟧}
    (hq : q ∈ tateAlgebra p) (hq' : q' ∈ tateAlgebra p) {b b' : Polynomial ℚ_[p]}
    (hb : b.degree < #R) (hb' : b'.degree < #R)
    (h : q * (intPoleProduct R ℚ_[p] : ℚ_[p]⟦X⟧) + b =
      q' * (intPoleProduct R ℚ_[p] : ℚ_[p]⟦X⟧) + b') :
    q = q' := by
  set E := intPoleProduct R ℚ_[p] with hEdef
  have hgE : (q - q') * (E : ℚ_[p]⟦X⟧) = ((b' - b : Polynomial ℚ_[p]) : ℚ_[p]⟦X⟧) := by
    rw [Polynomial.coe_sub, sub_mul]
    linear_combination h
  refine sub_eq_zero.mp <| eq_zero_of_mem_tateAlgebra_of_coeff_mul_eq_zero
    (sub_mem hq hq') (monic_intPoleProduct R ℚ_[p]) (fun i => ?_) fun n hn => ?_
  · rw [← map_intPoleProduct R ℤ (Int.castRingHom ℚ_[p]), Polynomial.coeff_map]
    exact Padic.norm_int_le_one _
  · rw [hgE, Polynomial.coeff_coe]
    refine Polynomial.coeff_eq_zero_of_degree_lt ?_
    rw [natDegree_intPoleProduct] at hn
    calc (b' - b).degree ≤ max b'.degree b.degree := Polynomial.degree_sub_le _ _
      _ < n := max_lt (hb'.trans_le (by exact_mod_cast hn)) (hb.trans_le (by exact_mod_cast hn))

end Zeta5Irr
