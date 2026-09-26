/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.TauDeltaext
public import Zeta5Irr.LocalFunctional.Tauext

/-!
# Scaling of `τ_Y^ext ∘ δ_R^ext`

Let `p` be a prime, `R ⊆ ℤ` finite, `Y ∈ ℚ_p[X]`, `c ∈ ℚ_p` and `f` a power series over `ℚ_p`.
Then `τ_Y^ext(δ_R^ext(c f)) = c τ_Y^ext(δ_R^ext(f))`.

Truncation is `ℚ_p`-linear, so `(c f)^{[D]} = c f^{[D]}`, and `δ_R` is `ℚ_p`-linear, so
`δ_R((c f)^{[D]}) = c δ_R(f^{[D]})` for every `D`. Scalar multiplication on `𝓑_R` is continuous,
so `δ_R^ext(c f) = c δ_R^ext(f)`; and `τ_Y^ext` is `ℚ_p`-homogeneous.

## Main results

* `Zeta5Irr.trunc_smul`: `(c f)^{[n]} = c f^{[n]}` for truncations of power series.
* `Zeta5Irr.deltaExt_smul`: `δ_R^ext(c f) = c δ_R^ext(f)`.
* `Zeta5Irr.tauExt_deltaExt_smul`: `τ_Y^ext(δ_R^ext(c f)) = c τ_Y^ext(δ_R^ext(f))`.

## Implementation notes

The source states the result for `f` in the Tate algebra `𝒜 = ℚ_p⟨z⟩`, where the limit
defining `δ_R^ext(f)` exists. The statement here holds for every power series `f`: for `c ≠ 0`
the truncation limits for `f` and `c f` exist together, and when neither exists both sides
take the junk value `0`; for `c = 0` both sides are `0`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.5 (The inner range: the entry valuations).
-/

@[expose] public section

namespace Zeta5Irr

open Filter Topology PowerSeries

variable {p : ℕ} [Fact p.Prime]

/-- Truncation of power series is homogeneous: `trunc n (c • f) = c • trunc n f`. -/
theorem trunc_smul {S : Type*} [CommSemiring S] (n : ℕ) (c : S) (f : S⟦X⟧) :
    trunc n (c • f) = c • trunc n f := by
  rw [PowerSeries.smul_eq_C_mul, trunc_C_mul, Polynomial.smul_eq_C_mul]

variable {R : Finset ℤ}

/-- `δ_R^ext` is `ℚ_p`-homogeneous: `δ_R^ext(c f) = c δ_R^ext(f)` for every power series `f`. -/
theorem deltaExt_smul (c : ℚ_[p]) (f : ℚ_[p]⟦X⟧) :
    deltaExt R (c • f) = c • deltaExt R f := by
  have hseq : (fun D : ℕ => deltaR R (trunc (D + 1) (c • f))) =
      fun D : ℕ => c • deltaR R (trunc (D + 1) f) := by
    funext D
    rw [trunc_smul, deltaR_smul]
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  by_cases h : ∃ l, Tendsto (fun D : ℕ => deltaR R (trunc (D + 1) f)) atTop (𝓝 l)
  · refine deltaExt_eq_of_tendsto ?_
    rw [hseq]
    exact (tendsto_deltaExt h).const_smul c
  · rw [deltaExt_of_not_exists_tendsto h, smul_zero]
    refine deltaExt_of_not_exists_tendsto ?_
    rintro ⟨l, hl⟩
    refine h ⟨c⁻¹ • l, ?_⟩
    rw [hseq] at hl
    simpa [smul_smul, inv_mul_cancel₀ hc] using hl.const_smul c⁻¹

/-- **Scaling of `τ_Y^ext ∘ δ_R^ext`.** For a prime `p`, a finite set `R ⊆ ℤ`, `Y ∈ ℚ_p[X]`,
`c ∈ ℚ_p` and a power series `f` over `ℚ_p` (in the source, `f ∈ ℚ_p⟨z⟩`),
`τ_Y^ext(δ_R^ext(c f)) = c τ_Y^ext(δ_R^ext(f))`. -/
@[zeta5irr "lem_in_scale"]
theorem tauExt_deltaExt_smul (Y : Polynomial ℚ_[p]) (c : ℚ_[p]) (f : ℚ_[p]⟦X⟧) :
    tauExt R Y (deltaExt R (c • f)) = c • tauExt R Y (deltaExt R f) := by
  rw [deltaExt_smul, tauExt_smul]

end Zeta5Irr
