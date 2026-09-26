/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.InPull
public import Zeta5Irr.LocalFunctional.TauDist

/-!
# The local summand `Ω_{a,i,c,j}(σ)` of an entry

Let `p` be an odd prime, `M ≥ 40`, `K = 40 n`, `N = 3 n`, `0 ≤ a, c ≤ m°`, `0 ≤ i < L_a`,
`0 ≤ j < L_c` and `0 ≤ σ < p`. Split the pole set `{r ∈ ℤ : N < |r| ≤ K}` according to the
residue of `r` modulo `p`, rescaled by `r ↦ (r - σ) / p`:
`R^{(σ)} = {(r - σ) / p : N < |r| ≤ K, r ≡ σ (mod p)} ⊆ ℤ` and
`Σ^{(σ)} = {(r - σ) / p : N < |r| ≤ K, r ≢ σ (mod p)} ⊆ ℚ_p`. The local summand is
`Ω_{a,i,c,j}(σ) = p^{-4} τ_{Y_p}^ext(δ_{R^{(σ)}}^ext(p^{-2(K-N)} g_{a,i,c,j}(σ + pz)
  ∏_{s' ∈ Σ^{(σ)}} ε_{s'})) ∈ ℚ_p[X]`,
where `g_{a,i,c,j}` is the pulled-back integrand. Since the pole set has `2(K - N)` elements,
`Ω_{a,i,c,j}(σ)` is the `σ`-th summand of the distributed functional
`𝒯_p(g_{a,i,c,j}; {r ∈ ℤ : N < |r| ≤ K})`.

## Main definitions

* `Zeta5Irr.poleAnnulus N K`: the set `{r ∈ ℤ : N < |r| ≤ K}`.
* `Zeta5Irr.innerNearPoles p n σ`: the set `R^{(σ)} ⊆ ℤ`.
* `Zeta5Irr.innerFarPoles p n σ`: the set `Σ^{(σ)} ⊆ ℚ_p`.
* `Zeta5Irr.innerSummand n p M a i c j σ`: the local summand `Ω_{a,i,c,j}(σ) ∈ ℚ_p[X]`.

## Main results

* `Zeta5Irr.mem_poleAnnulus`, `Zeta5Irr.card_poleAnnulus`: `r ∈ {N < |r| ≤ K}` iff
  `N < |r| ≤ K`, and for `N ≤ K` this set has `2 (K - N)` elements.
* `Zeta5Irr.mem_innerNearPoles`, `Zeta5Irr.mem_innerFarPoles`: membership in `R^{(σ)}` and
  `Σ^{(σ)}`.
* `Zeta5Irr.sum_innerSummand`: `∑_{σ=0}^{p-1} Ω_{a,i,c,j}(σ) = 𝒯_p(g_{a,i,c,j}; {N < |r| ≤ K})`.

## Implementation notes

* The sets `R^{(σ)}` and `Σ^{(σ)}` are those that the distributed functional attaches to the
  residue `σ` and the pole set `{N < |r| ≤ K}`, so they are abbreviations for them.
* The hypotheses that `p` is odd, `M ≥ 40`, `a, c ≤ m°`, `i < L_a`, `j < L_c` and `σ < p` are
  not needed to define `Ω_{a,i,c,j}(σ)`; they are carried by the lemmas which use them.
  The parameter of the extended functional is `Y_p = p^5 X + C_p`.
* The substitution `g(σ + pz)` is `g.comp (σ + p X)` in `ℚ[X]`, mapped to `ℚ_p[z]` and regarded
  as a power series; the scalars `p^{-2(K-N)}` and `p^{-4}` act by scalar multiplication.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.5 (The inner range: the entry valuations).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial
open scoped Finset

/-- The set `{r ∈ ℤ : N < |r| ≤ K}` of integers whose absolute value lies in `(N, K]`. -/
def poleAnnulus (N K : ℕ) : Finset ℤ :=
  {r ∈ Finset.Icc (-(K : ℤ)) K | (N : ℤ) < |r|}

/-- `r ∈ {N < |r| ≤ K}` iff `N < |r|` and `|r| ≤ K`. -/
@[simp]
theorem mem_poleAnnulus {N K : ℕ} {r : ℤ} : r ∈ poleAnnulus N K ↔ (N : ℤ) < |r| ∧ |r| ≤ K := by
  simp only [poleAnnulus, Finset.mem_filter, Finset.mem_Icc, ← abs_le]
  exact and_comm

/-- `{N < |r| ≤ K}` is the union of `[-K, -N - 1]` and `[N + 1, K]`. -/
theorem poleAnnulus_eq_union (N K : ℕ) :
    poleAnnulus N K = Finset.Icc (-(K : ℤ)) (-N - 1) ∪ Finset.Icc ((N : ℤ) + 1) K := by
  ext r
  simp only [mem_poleAnnulus, Finset.mem_union, Finset.mem_Icc, lt_abs, abs_le]
  omega

/-- For `N ≤ K` and any predicate `P`, the elements of `{N < |r| ≤ K}` satisfying `P`, together
with those of `{0 < |r| ≤ N}`, are those of `{0 < |r| ≤ K}`. -/
theorem card_filter_poleAnnulus_add_card_filter {N K : ℕ} (h : N ≤ K) (P : ℤ → Prop)
    [DecidablePred P] :
    #{r ∈ poleAnnulus N K | P r} + #{r ∈ Finset.Icc (-(N : ℤ)) N | 0 < |r| ∧ P r} =
      #{r ∈ Finset.Icc (-(K : ℤ)) K | 0 < |r| ∧ P r} := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext r
    simp only [Finset.mem_union, Finset.mem_filter, mem_poleAnnulus, Finset.mem_Icc, lt_abs,
      abs_le]
    by_cases hr : P r <;> simp only [hr, and_true, and_false, or_false]
    omega
  · rw [Finset.disjoint_left]
    intro r h1 h2
    simp only [Finset.mem_filter, mem_poleAnnulus, Finset.mem_Icc, lt_abs, abs_le] at h1 h2
    omega

/-- For `N ≤ K`, the set `{N < |r| ≤ K}` has `2 (K - N)` elements. -/
theorem card_poleAnnulus {N K : ℕ} (h : N ≤ K) : (poleAnnulus N K).card = 2 * (K - N) := by
  rw [poleAnnulus_eq_union, Finset.card_union_of_disjoint]
  · simp only [Int.card_Icc]
    omega
  · rw [Finset.disjoint_left]
    intro r h₁ h₂
    simp only [Finset.mem_Icc] at h₁ h₂
    omega

variable (p : ℕ)

/-- The set `R^{(σ)} = {(r - σ) / p : r ∈ ℤ, N < |r| ≤ K, r ≡ σ (mod p)} ⊆ ℤ`, where `K = 40 n`
and `N = 3 n`. -/
@[zeta5irr "def_in_summand"]
abbrev innerNearPoles (n σ : ℕ) : Finset ℤ :=
  distNearPoles p (poleAnnulus (innerDegree n) (poleBound n)) σ

/-- `m ∈ R^{(σ)}` iff `m = (r - σ) / p` for some `r` with `N < |r| ≤ K` and
`r ≡ σ (mod p)`. -/
theorem mem_innerNearPoles {n σ : ℕ} {m : ℤ} :
    m ∈ innerNearPoles p n σ ↔ ∃ r : ℤ, ((innerDegree n : ℤ) < |r| ∧ |r| ≤ poleBound n) ∧
      r ≡ σ [ZMOD p] ∧ (r - σ) / p = m := by
  simp only [innerNearPoles, mem_distNearPoles, mem_poleAnnulus]

variable [Fact p.Prime]

/-- The set `Σ^{(σ)} = {(r - σ) / p : r ∈ ℤ, N < |r| ≤ K, r ≢ σ (mod p)} ⊆ ℚ_p`, where
`K = 40 n` and `N = 3 n`. -/
@[zeta5irr "def_in_summand"]
noncomputable abbrev innerFarPoles (n σ : ℕ) : Finset ℚ_[p] :=
  distFarPoles p (poleAnnulus (innerDegree n) (poleBound n)) σ

/-- `s ∈ Σ^{(σ)}` iff `s = (r - σ) / p` for some `r` with `N < |r| ≤ K` and
`r ≢ σ (mod p)`. -/
theorem mem_innerFarPoles {n σ : ℕ} {s : ℚ_[p]} :
    s ∈ innerFarPoles p n σ ↔ ∃ r : ℤ, ((innerDegree n : ℤ) < |r| ∧ |r| ≤ poleBound n) ∧
      ¬r ≡ σ [ZMOD p] ∧ ((r - σ : ℤ) : ℚ_[p]) / p = s := by
  simp only [innerFarPoles, mem_distFarPoles, mem_poleAnnulus]

/-- The local summand
`Ω_{a,i,c,j}(σ) = p^{-4} τ_{Y_p}^ext(δ_{R^{(σ)}}^ext(p^{-2(K-N)} g_{a,i,c,j}(σ + pz)
∏_{s' ∈ Σ^{(σ)}} ε_{s'})) ∈ ℚ_p[X]`, where `K = 40 n` and `N = 3 n`. -/
@[zeta5irr "def_in_summand"]
noncomputable def innerSummand (n M a i c j σ : ℕ) : ℚ_[p][X] :=
  ((p : ℚ_[p]) ^ 4)⁻¹ •
    tauExt (innerNearPoles p n σ) (Yp p) (deltaExt (innerNearPoles p n σ)
      (((p : ℚ_[p]) ^ (2 * (poleBound n - innerDegree n)))⁻¹ •
        (((((pulledIntegrand n p M a i c j).comp (C (σ : ℚ) + C (p : ℚ) * X)).map
          (algebraMap ℚ ℚ_[p]) : ℚ_[p][X]) : PowerSeries ℚ_[p]) *
          ∏ s ∈ innerFarPoles p n σ, farEps s)))

/-- The local summands add up to the distributed functional:
`∑_{σ=0}^{p-1} Ω_{a,i,c,j}(σ) = 𝒯_p(g_{a,i,c,j}; {r ∈ ℤ : N < |r| ≤ K})`. -/
theorem sum_innerSummand (n M a i c j : ℕ) :
    ∑ σ ∈ Finset.range p, innerSummand p n M a i c j σ =
      tauDist p (poleAnnulus (innerDegree n) (poleBound n)) (pulledIntegrand n p M a i c j) := by
  rw [tauDist, card_poleAnnulus (innerDegree_le_poleBound n), Finset.smul_sum]
  rfl

end Zeta5Irr
