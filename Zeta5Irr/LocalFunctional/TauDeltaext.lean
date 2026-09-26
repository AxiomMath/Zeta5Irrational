/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.TauDelta
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# The extension `δ_R^ext` of the near-pole decomposition to power series

Let `R ⊆ ℤ` be finite and `f ∈ ℚ_p⟦z⟧`, with truncations `f^{[D]} = ∑_{d ≤ D} f_d z^d`. The
extended near-pole decomposition of `f` is the limit
`δ_R^ext(f) = lim_{D → ∞} δ_R(f^{[D]}) ∈ 𝓑_R`, taken in the normed space `𝓑_R` when it
exists, and `0` otherwise.

## Main definitions

* `Zeta5Irr.deltaExt R f`: the extended near-pole decomposition `δ_R^ext(f) ∈ 𝓑_R`.

## Main results

* `Zeta5Irr.deltaExt_eq_of_tendsto`: if `δ_R(f^{[D]}) → l`, then `δ_R^ext(f) = l`.
* `Zeta5Irr.deltaExt_of_not_exists_tendsto`: if `δ_R(f^{[D]})` does not converge, then
  `δ_R^ext(f) = 0`.
* `Zeta5Irr.tendsto_deltaExt`: if `δ_R(f^{[D]})` converges, it converges to `δ_R^ext(f)`.
* `Zeta5Irr.deltaExt_coe`: `δ_R^ext` extends `δ_R`, i.e. `δ_R^ext(U) = δ_R(U)` for
  `U ∈ ℚ_p[z]`.

## Implementation notes

The truncation `f^{[D]} = ∑_{d ≤ D} f_d z^d` is `PowerSeries.trunc (D + 1) f`, since
`PowerSeries.trunc n` keeps the coefficients of degree `< n`. The limit is `limUnder` along
`Filter.atTop`, guarded by the existence of the limit so that the junk value is `0`; since
`𝓑_R` is Hausdorff, the limit is unique when it exists.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.4 (Completion at a prime).
-/

@[expose] public section

namespace Zeta5Irr

open Filter Topology PowerSeries

variable {p : ℕ} [Fact p.Prime]

open Classical in
/-- The extended near-pole decomposition `δ_R^ext(f) = lim_{D → ∞} δ_R(f^{[D]}) ∈ 𝓑_R` of a
power series `f ∈ ℚ_p⟦z⟧`, where `f^{[D]} = ∑_{d ≤ D} f_d z^d`; it is `0` when the limit does
not exist. -/
@[zeta5irr "def_tau_deltaext"]
noncomputable def deltaExt (R : Finset ℤ) (f : ℚ_[p]⟦X⟧) : BT p R :=
  if ∃ l, Tendsto (fun D : ℕ => deltaR R (trunc (D + 1) f)) atTop (𝓝 l) then
    limUnder atTop (fun D : ℕ => deltaR R (trunc (D + 1) f))
  else 0

variable {R : Finset ℤ} {f : ℚ_[p]⟦X⟧}

/-- If the near-pole decompositions `δ_R(f^{[D]})` of the truncations of `f` converge to `l`,
then `δ_R^ext(f) = l`. -/
@[zeta5irr "def_tau_deltaext"]
theorem deltaExt_eq_of_tendsto {l : BT p R}
    (h : Tendsto (fun D : ℕ => deltaR R (trunc (D + 1) f)) atTop (𝓝 l)) :
    deltaExt R f = l := by
  have hl : ∃ l, Tendsto (fun D : ℕ => deltaR R (trunc (D + 1) f)) atTop (𝓝 l) := ⟨l, h⟩
  simp only [deltaExt, hl, ↓reduceIte]
  exact h.limUnder_eq

/-- If the near-pole decompositions `δ_R(f^{[D]})` of the truncations of `f` do not converge,
then `δ_R^ext(f) = 0`. -/
@[zeta5irr "def_tau_deltaext"]
theorem deltaExt_of_not_exists_tendsto
    (h : ¬∃ l, Tendsto (fun D : ℕ => deltaR R (trunc (D + 1) f)) atTop (𝓝 l)) :
    deltaExt R f = 0 := by
  simp only [deltaExt, h, ↓reduceIte]

/-- If the near-pole decompositions `δ_R(f^{[D]})` of the truncations of `f` converge, then
they converge to `δ_R^ext(f)`. -/
theorem tendsto_deltaExt
    (h : ∃ l, Tendsto (fun D : ℕ => deltaR R (trunc (D + 1) f)) atTop (𝓝 l)) :
    Tendsto (fun D : ℕ => deltaR R (trunc (D + 1) f)) atTop (𝓝 (deltaExt R f)) := by
  obtain ⟨l, hl⟩ := h
  rwa [deltaExt_eq_of_tendsto hl]

/-- `δ_R^ext` extends `δ_R`: for a polynomial `U ∈ ℚ_p[z]`, `δ_R^ext(U) = δ_R(U)`. -/
@[simp]
theorem deltaExt_coe (U : Polynomial ℚ_[p]) : deltaExt R (U : ℚ_[p]⟦X⟧) = deltaR R U := by
  refine deltaExt_eq_of_tendsto <| tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop U.natDegree] with D hD
  rw [trunc_coe_eq_self (Nat.lt_succ_of_le hD)]

/-- `δ_R^ext(0) = 0`. -/
@[simp]
theorem deltaExt_zero : deltaExt R (0 : ℚ_[p]⟦X⟧) = 0 := by
  have h := deltaR_smul (R := R) (0 : ℚ_[p]) (0 : Polynomial ℚ_[p])
  rw [zero_smul, zero_smul] at h
  simpa [h] using deltaExt_coe (R := R) (0 : Polynomial ℚ_[p])

end Zeta5Irr
