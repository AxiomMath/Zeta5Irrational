/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Completion.Qn
public import Zeta5Irr.PrimeSum.QIntegral

/-!
# Integrality of `Q_n`

For every integer `n ≥ 200000`, the polynomial `Q_n = Q_{40n, 200}` has integer coefficients.
Indeed the pair `(K, M) = (40 n, 200)` satisfies the hypotheses of the integrality of
`Q_{K,M}`: `M = 200 ≥ 40`, `K = 40 n` is a positive multiple of `40`, and
`K = 40 n ≥ 40 · 200000 = 200 · 200²`.

## Main results

* `Zeta5Irr.Qn_mem_lifts`: for `n ≥ 200000`, `Q_n ∈ ℤ[X]`.

## Implementation notes

* Membership `Q_n ∈ ℤ[X]` is stated as membership of `Q_n ∈ ℝ[X]` in the image
  `Polynomial.lifts (Int.castRingHom ℝ)` of `ℤ[X]`. By `Polynomial.mem_lifts` this is the
  existence of `P ∈ ℤ[X]` whose image in `ℝ[X]` is `Q_n`, which is the form in which an integer
  polynomial is evaluated at a rational point when clearing denominators.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §11 (Completion of the irrationality proof).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

/-- **Integrality of `Q_n`.** For every integer `n ≥ 200000`, `Q_n ∈ ℤ[X]`: the polynomial
`Q_n ∈ ℝ[X]` is the image of an integer polynomial. -/
@[zeta5irr "lem_final_int"]
theorem Qn_mem_lifts {n : ℕ} (hn : 200000 ≤ n) : Qn n ∈ lifts (Int.castRingHom ℝ) := by
  refine lifts_iff_coeff_lifts _ |>.2 fun i => ?_
  obtain ⟨z, hz⟩ := exists_coeff_normalizedPoly_eq_intCast (n := n) (M := 200) (by norm_num)
    (by simp only [poleBound]; omega) i
  exact ⟨z, hz.symm⟩

end Zeta5Irr
