/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.InHalfweight
public import Zeta5Irr.LocalEstimates.InBasisChange
public import Zeta5Irr.LocalEstimates.InDetWeights
public import Zeta5Irr.LocalEstimates.GammaIn

/-!
# The inner range: the weights

Let `M ≥ 40`, let `K = 40 n ≥ 200 M²` and let `p` be a prime with `K / M < p ≤ K / 3`. Then
`v_p^G(Δ_K) ≥ γ_p^in`.

Let `B` be the matrix of the pairings `B_{(a,i),(c,j)} = Φ(Ψ_{a,i}, Ψ_{c,j})`, indexed by the
pairs `(a, i)` with `0 ≤ a ≤ m°` and `0 ≤ i < L_a`. Every entry satisfies
`v_p^G(B_{(a,i),(c,j)}) ≥ w_{a,i} + w_{c,j}`, so the determinant bound from row and column
weights gives `v_p^G(det B) ≥ 2 ∑_{a,i} w_{a,i} = γ_p^in`. The basis change does not move the
Gauss valuation, `v_p^G(det B) = v_p^G(Δ_K)`.

## Main results

* `Zeta5Irr.innerExponent_le_vpG_gramDet`: `v_p^G(Δ_K) ≥ γ_p^in`.

## Implementation notes

* `γ_p^in` is rational and `v_p^G(Δ_K) ∈ ℤ ∪ {+∞}`; the two are compared in `ℚ ∪ {+∞}`, after
  mapping `ℤ ∪ {+∞}` into it, as in `Zeta5Irr.two_mul_sum_le_vpG_det`.
* The hypothesis `K ∈ 40 ℤ_{>0}` is built into `K = 40 n`, and the inequalities
  `K / M < p ≤ K / 3` are stated in `ℚ`, as in `Zeta5Irr.vpG_map_det_innerBasisGramMatrix`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.6 (The inner range: the weights).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial Finset

/-- **The inner lower bound** (§5.6). Let `M ≥ 40`, let `K = 40 n ≥ 200 M²` and let `p` be a
prime with `K / M < p ≤ K / 3`. Then `v_p^G(Δ_K) ≥ γ_p^in`. -/
@[zeta5irr "prop_inner"]
theorem innerExponent_le_vpG_gramDet {p : ℕ} [Fact p.Prime] {n M : ℕ} (hM : 40 ≤ M)
    (hK : 200 * M ^ 2 ≤ poleBound n) (hpl : (poleBound n : ℚ) / M < p)
    (hpu : (p : ℚ) ≤ poleBound n / 3) :
    ((innerExponent n p M : ℚ) : WithTop ℚ) ≤
      (vpG ((gramDet n).map (Rat.castHom ℚ_[p]))).map ((↑) : ℤ → ℚ) := by
  have hplR : (poleBound n : ℝ) / M < p := by
    have := (Rat.cast_lt (K := ℝ)).2 hpl; push_cast at this; exact this
  have hpuR : (p : ℝ) ≤ poleBound n / 3 := by
    have := (Rat.cast_le (K := ℝ)).2 hpu; push_cast at this; exact this
  rw [← vpG_map_det_innerBasisGramMatrix hM hK hpl hpu, ← Polynomial.coe_mapRingHom,
    RingHom.map_det]
  let w : (Σ a : Fin (mStar p + 1), Fin (rowPolyExponent n p M a)) → ℚ :=
    fun ai => innerWeight n p M ai.1 ai.2
  have hsum : innerExponent n p M = 2 * ∑ r, w r := by
    rw [innerExponent, Fintype.sum_sigma, ← Fin.sum_univ_eq_sum_range]
    congr 1
    refine sum_congr rfl fun a _ => ?_
    rw [← Fin.sum_univ_eq_sum_range]
  rw [hsum]
  refine two_mul_sum_le_vpG_det _ w fun ai cj => ?_
  obtain ⟨a, i⟩ := ai
  obtain ⟨c, j⟩ := cj
  have hlt : ∀ b k : ℕ, k < rowPolyExponent n p M b → (k : ℤ) < classDimAt n p M b :=
    fun b k hk => Int.lt_toNat.1 (rowPolyExponent_eq_toNat_classDimAt n p M b ▸ hk)
  have h := innerWeight_add_innerWeight_le_vpG_innerForm hM hK hplR hpuR
    (Nat.lt_succ_iff.1 a.2) (Nat.lt_succ_iff.1 c.2) (hlt a i i.2) (hlt c j j.2)
  have hc : algebraMap ℚ ℚ_[p] = Rat.castHom ℚ_[p] := Subsingleton.elim _ _
  simpa [w, hc] using h

end Zeta5Irr
