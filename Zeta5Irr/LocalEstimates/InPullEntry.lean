/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.InForm
public import Zeta5Irr.LocalEstimates.InPull
public import Zeta5Irr.LocalFunctional.Pullback

/-!
# The inner entries as values of `τ_X`

Let `N = 3 n` and `K = 40 n`. The entry `Φ(Ψ_{a,i}, Ψ_{c,j})` of the inner Gram matrix is
`μ_X(D_N ^ 5 Ψ_{a,i} Ψ_{c,j}; S)` with `S = {N + 1, …, K}`. By the pullback identity along
`t = -x ^ 2`, it equals `τ_X(g_{a,i,c,j}; {r ∈ ℤ : N < |r| ≤ K})`, where `g_{a,i,c,j}` is the
pulled-back integrand, since `S ∪ (-S) = {r ∈ ℤ : N < |r| ≤ K}` and `#S = K - N`.

## Main results

* `Zeta5Irr.innerForm_rowPoly_eq_tauX`: `Φ(Ψ_{a,i}, Ψ_{c,j}) = τ_X(g_{a,i,c,j}; {N < |r| ≤ K})`.

## Implementation notes

* The set `{r ∈ ℤ : N < |r| ≤ K}` is written as the finset of `r ∈ [-K, K]` with `N < |r|`.
* The hypotheses that `p` is an odd prime, `M ≥ 40`, `a, c ≤ m°`, `i < L_a` and `j < L_c` are
  not needed: the identity holds for all natural parameters.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.5 (The inner range: the entry valuations).
-/

@[expose] public section

namespace Zeta5Irr

open Finset Polynomial

/-- For `N < K` natural numbers, the symmetrisation `S ∪ (-S)` of `S = {N + 1, …, K}` is
`{r ∈ ℤ : N < |r| ≤ K}`. -/
theorem image_Icc_union_image_neg_Icc (N K : ℕ) :
    (Icc (N + 1) K).image (fun j : ℕ ↦ (j : ℤ)) ∪ (Icc (N + 1) K).image (fun j : ℕ ↦ -(j : ℤ)) =
      {r ∈ Icc (-(K : ℤ)) K | (N : ℤ) < |r|} := by
  ext r
  simp only [mem_union, mem_image, mem_Icc, mem_filter, lt_abs]
  constructor
  · rintro (⟨j, ⟨h1, h2⟩, rfl⟩ | ⟨j, ⟨h1, h2⟩, rfl⟩) <;> omega
  · rintro ⟨⟨h1, h2⟩, h3 | h3⟩
    · exact Or.inl ⟨r.toNat, ⟨by omega, by omega⟩, by omega⟩
    · exact Or.inr ⟨(-r).toNat, ⟨by omega, by omega⟩, by omega⟩

/-- **The entries of the inner range.** With `N = 3 n` and `K = 40 n`,
`Φ(Ψ_{a,i}, Ψ_{c,j}) = τ_X(g_{a,i,c,j}; {r ∈ ℤ : N < |r| ≤ K})`. -/
@[zeta5irr "lem_in_pull_entry"]
theorem innerForm_rowPoly_eq_tauX (n p M a i c j : ℕ) :
    innerForm n (rowPoly n p M a i) (rowPoly n p M c j) =
      tauX {r ∈ Icc (-(poleBound n : ℤ)) (poleBound n) | (innerDegree n : ℤ) < |r|}
        (pulledIntegrand n p M a i c j) := by
  rw [innerForm, rationalFunctional_eq_tauX (by simp), image_Icc_union_image_neg_Icc,
    pulledIntegrand_def, Nat.card_Icc, Nat.add_sub_add_right]
  congr 1
  simp only [mul_comp, pow_comp]
  ring

end Zeta5Irr
