/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.Qbinom
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.SimpleRing.Principal

/-!
# The integral binomial expansion

Let `p` be a prime, `d ≥ 0`, and let `A ∈ ℚ_p[x]` have degree at most `d` and satisfy
`A(ℤ_p) ⊆ ℤ_p`. Then there are `a_0, …, a_d ∈ ℤ_p` with `A = ∑_{k=0}^{d} a_k (x choose k)`.

The coefficients are the iterated forward differences `a_k = (Δ^k A)(0)`, where
`(Δ Q)(x) = Q(x + 1) - Q(x)`. Since `(Δ^k A)(0) = ∑_j (-1)^(k-j) (k choose j) A(j)` is an integer
combination of values of `A` at natural numbers, it lies in `ℤ_p`. By Newton's forward difference
formula, `A(n) = ∑_k (n choose k) (Δ^k A)(0)` for every natural number `n`, and `Δ^k A = 0` for
`k > d`; so `A` and `∑_{k ≤ d} a_k (x choose k)` agree at infinitely many points and are equal.

## Main results

* `Zeta5Irr.exists_eq_sum_smul_qbinom`: the integral binomial expansion.

## Implementation notes

The binomial polynomial `(x choose k)` is `Zeta5Irr.qbinom k ∈ ℚ[x]`, viewed in `ℚ_p[x]` through
`Polynomial.map (algebraMap ℚ ℚ_[p])`. The hypothesis `A(ℤ_p) ⊆ ℤ_p` is stated as
`‖A(x)‖ ≤ 1` for `x ∈ ℤ_p`, which is how `ℤ_[p]` sits inside `ℚ_[p]`. The coefficients are given
as a sequence `ℕ → ℤ_[p]`, of which only `a_0, …, a_d` enter.

The blueprint's argument first expands `A` in the `ℚ_p`-basis `(x choose k)` and then identifies
the coefficients with `(Δ^k A)(0)`; here the coefficients are defined as `(Δ^k A)(0)` directly and
the expansion is verified by comparing values at the natural numbers, using Mathlib's
`shift_eq_sum_fwdDiff_iter` and `Polynomial.fwdDiff_iter_eq_zero_of_degree_lt`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.6 (Small primes).
-/

@[expose] public section

open Polynomial fwdDiff

namespace Zeta5Irr

/-- **The integral binomial expansion.** A polynomial `A ∈ ℚ_p[x]` of degree at most `d` with
`A(ℤ_p) ⊆ ℤ_p` is a `ℤ_p`-linear combination `∑_{k=0}^{d} a_k (x choose k)`. -/
@[zeta5irr "lem_small_binom_int"]
theorem exists_eq_sum_smul_qbinom {p : ℕ} [Fact p.Prime] {d : ℕ} {A : ℚ_[p][X]}
    (hA : A.natDegree ≤ d) (hint : ∀ x : ℤ_[p], ‖A.eval (x : ℚ_[p])‖ ≤ 1) :
    ∃ a : ℕ → ℤ_[p],
      A = ∑ k ∈ Finset.range (d + 1), (a k : ℚ_[p]) • (qbinom k).map (algebraMap ℚ ℚ_[p]) := by
  have hmem : ∀ k : ℕ, (fwdDiff (1 : ℚ_[p]))^[k] A.eval 0 ∈ PadicInt.subring p := by
    intro k
    rw [fwdDiff_iter_eq_sum_shift]
    refine Subring.sum_mem _ fun j _ => zsmul_mem ?_ _
    rw [PadicInt.mem_subring_iff, zero_add, nsmul_one]
    simpa using hint (j : ℤ_[p])
  refine ⟨fun k => ⟨_, hmem k⟩, ?_⟩
  refine eq_of_infinite_eval_eq _ _ (Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => (n : ℚ_[p])) Nat.cast_injective fun n => ?_)
  simp only [Set.mem_ofPred_eq, eval_finsetSum, eval_smul, eval_map_algebraMap]
  have hcast : ((n : ℚ) : ℚ_[p]) = (n : ℚ_[p]) := Rat.cast_natCast n
  simp_rw [← hcast, ← eq_ratCast (algebraMap ℚ ℚ_[p]), aeval_algebraMap_apply, coe_aeval_eq_eval,
    eval_natCast_qbinom, eq_ratCast, Rat.cast_natCast]
  have key := shift_eq_sum_fwdDiff_iter (h := (1 : ℚ_[p])) A.eval n 0
  rw [zero_add, nsmul_one] at key
  rw [key]
  have hz : ∀ k, d < k → (fwdDiff (1 : ℚ_[p]))^[k] A.eval 0 = 0 := fun k hk => by
    rw [fwdDiff_iter_eq_zero_of_degree_lt (by omega)]; rfl
  rw [Finset.sum_subset (Finset.range_subset_range.2 (show n + 1 ≤ n + d + 1 by omega)) ?_,
    Finset.sum_subset (Finset.range_subset_range.2 (show d + 1 ≤ n + d + 1 by omega)) ?_]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [nsmul_eq_mul, smul_eq_mul, mul_comm]
  · intro k _ hk
    rw [hz k (by simpa using hk), zero_smul]
  · intro k _ hk
    rw [Nat.choose_eq_zero_of_lt (by simpa using hk), zero_smul]

end Zeta5Irr
