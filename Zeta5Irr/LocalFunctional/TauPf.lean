/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.DerivProdEval
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar

/-!
# Division by `∏ (x - ρ)` with a Lagrange remainder

Let `F` be a field, let `v : ι → F` be injective on a finite set `s` of indices and write
`E = ∏_{j ∈ s} (X - v j)`. If `A = P E + B` with `deg B < #s`, then the remainder `B` is the
Lagrange interpolant of `A` on the nodes `v i`, and explicitly
`A = P E + ∑_{i ∈ s} (A(v i) / E'(v i)) ∏_{j ∈ s \ {i}} (X - v j)`.

Indeed `B` and `A` agree at every node, since `E` vanishes there, so `B` is the Lagrange
interpolant of the values `A(v i)`; and `E'(v i) = ∏_{j ∈ s \ {i}} (v i - v j)` turns each
Lagrange basis polynomial into `(1 / E'(v i)) ∏_{j ∈ s \ {i}} (X - v j)`.

## Main results

* `Zeta5Irr.eq_mul_prod_add_sum_eval_div_derivative`: the identity above.

## Implementation notes

The source takes a finite set `R ⊆ F` of pairwise distinct elements; here the nodes are an
indexed family `v : ι → F` injective on `s`, which recovers the source with `ι = F`, `v = id`.
The set `R \ {ρ}` is written `s.erase i`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.1 (the functional `τ_X`).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial Finset

/-- If `A = P E + B` with `E = ∏_{j ∈ s} (X - v j)`, the nodes `v j` distinct and
`deg B < #s`, then `A = P E + ∑_{i ∈ s} (A(v i) / E'(v i)) ∏_{j ∈ s \ {i}} (X - v j)`. -/
@[zeta5irr "lem_tau_pf"]
theorem eq_mul_prod_add_sum_eval_div_derivative {F ι : Type*} [Field F] [DecidableEq ι]
    {s : Finset ι} {v : ι → F} (hv : Set.InjOn v s) {A P B : F[X]}
    (hA : A = P * ∏ j ∈ s, (X - C (v j)) + B) (hB : B.degree < #s) :
    A = P * ∏ j ∈ s, (X - C (v j)) + ∑ i ∈ s, C (A.eval (v i) /
        (derivative (∏ j ∈ s, (X - C (v j)))).eval (v i)) * ∏ j ∈ s.erase i, (X - C (v j)) := by
  have hBA : ∀ i ∈ s, B.eval (v i) = A.eval (v i) := by
    intro i hi
    have : (∏ j ∈ s, (X - C (v j))).eval (v i) = 0 := by
      rw [eval_prod]; exact prod_eq_zero hi (by simp)
    simp [hA, this]
  nth_rw 1 [hA]
  congr 1
  rw [Lagrange.eq_interpolate_of_eval_eq _ hv hB hBA]
  simp only [Lagrange.interpolate_apply, Lagrange.basis, Lagrange.basisDivisor]
  refine sum_congr rfl fun i hi => ?_
  rw [eval_derivative_prod_X_sub_C s v hi, prod_mul_distrib, ← map_prod, ← mul_assoc, ← map_mul,
    div_eq_mul_inv, prod_inv_distrib]

end Zeta5Irr
