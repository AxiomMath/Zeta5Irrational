/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.OutLInt

/-!
# Vanishing of the low entries of the correction matrix of the outer range

Let `p` be a prime and fix the parameters `N = 3 n`, `K = 40 n` and `h = 37 n`. The entry
`(𝓛_p)_{kl}` of the correction matrix `𝓛_p = p (G_K - G_K^∘)` vanishes as soon as
`k + l < K - 6 N + 2 p - 3`.

Indeed `(𝓛_p)_{kl} = p ∑_{e ≥ 2p - 3} [t ^ e] P_{kl} · μ(t ^ e)`, where `P_{kl}` is the quotient
of `A = D_N ^ 5 t ^ (k + l)` by the monic polynomial `D_S`, `S = {N + 1, …, K}`. Since
`deg P_{kl} = (5 N + k + l) - (K - N) = k + l + 6 N - K < 2 p - 3` (or `P_{kl} = 0`), no
coefficient of `P_{kl}` of degree `≥ 2 p - 3` is nonzero, and the sum is empty.

## Main results

* `Zeta5Irr.outerCorrectionMatrix_apply_eq_zero`: `(𝓛_p)_{kl} = 0` whenever
  `k + l < K - 6 N + 2 p - 3`.

## Implementation notes

* The hypotheses `p ≥ 7` and `K > 0` of the source are not needed: the argument uses only
  that the degree bound `deg P_{kl} < 2 p - 3` holds, and `2 p - 3 > 0` for every prime `p`.
* The inequality `k + l < K - 6 N + 2 p - 3` is stated in `ℤ`, so that no truncated
  subtraction occurs.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.7: the outer range, the integral part and its
  correction.
-/

@[expose] public section

namespace Zeta5Irr

open Finset Polynomial

variable {p : ℕ} [Fact p.Prime]

/-- **Vanishing of the low entries of `𝓛_p`.** If `k + l < K - 6 N + 2 p - 3`, then
`(𝓛_p)_{kl} = 0`. -/
@[zeta5irr "lem_out_L_vanish"]
theorem outerCorrectionMatrix_apply_eq_zero (n : ℕ) (k l : Fin (matrixOrder n))
    (hkl : ((k : ℕ) + l : ℤ) < poleBound n - 6 * innerDegree n + 2 * p - 3) :
    outerCorrectionMatrix p n k l = 0 := by
  rw [outerCorrectionMatrix_apply_eq_C, momentFunctional_sub_truncatedMomentFunctional,
    sum_eq_zero, mul_zero, C_0]
  intro e he
  rw [mem_filter, mem_support_iff] at he
  obtain ⟨he0, hpe⟩ := he
  have hdeg := le_natDegree_of_ne_zero he0
  rw [natDegree_divByMonic _ (monic_poleProduct _ ℚ), natDegree_poleProduct, Nat.card_Icc,
    ((monic_poleProductRange _ ℚ).pow 5).natDegree_mul (monic_X_pow _), natDegree_pow,
    natDegree_poleProductRange, natDegree_X_pow] at hdeg
  have hp := (Fact.out : p.Prime).two_le
  unfold poleBound innerDegree at hkl hdeg
  omega

end Zeta5Irr
