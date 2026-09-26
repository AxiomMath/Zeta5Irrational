/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.EllA
public import Zeta5Irr.LocalEstimates.InMstar
public import Zeta5Irr.LocalEstimates.OutXi

/-!
# The separating basis `q_{a,i}` of the outer range

For a prime `p`, an index `1 ≤ a ≤ m°` and `0 ≤ i < ℓ_K(a) - δ_a`, the source defines
`q_{a,i}(t) = (t + a²)^i` if `i < ℓ_K(a) - 2`, and
`q_{a,i}(t) = Ξ_a(t) (t + a²)^{i - ℓ_K(a) + 2}` if `i ≥ ℓ_K(a) - 2`,
where `Ξ_a(t) = ∏_{p < j ≤ K, j ≡ ±a (mod p)} (t + j²)`. These polynomials are monic, and for
`p` odd, `1 ≤ a ≤ m°` and `p ≤ K` the polynomial `q_{a,i}` has degree exactly `i`: among
`1 ≤ j ≤ p` exactly the two integers `a` and `p - a` are `≡ ±a (mod p)`, so `Ξ_a` has degree
`ℓ_K(a) - 2`.

## Main definitions

* `Zeta5Irr.outerBasis`: the polynomial `q_{a,i}` over a commutative ring `R`.

## Main results

* `Zeta5Irr.outerBasis_of_lt`, `Zeta5Irr.outerBasis_of_le`: the two branches of the definition.
* `Zeta5Irr.outerBasis_monic`: `q_{a,i}` is monic.
* `Zeta5Irr.map_outerBasis`: `q_{a,i}` commutes with ring homomorphisms.
* `Zeta5Irr.ellA_self_eq_two`: for `p` odd and `1 ≤ a ≤ m°`, `ℓ_p(a) = 2`: exactly two
  `1 ≤ j ≤ p` satisfy `j ≡ ±a (mod p)`.
* `Zeta5Irr.natDegree_outXi_add_two`: for `p` odd, `1 ≤ a ≤ m°` and `p ≤ K`,
  `deg Ξ_a + 2 = ℓ_K(a)`.
* `Zeta5Irr.natDegree_outerBasis`: under the same hypotheses, `deg q_{a,i} = i`.

## Implementation notes

* The source takes `p` prime, `1 ≤ a ≤ m°` and `0 ≤ i < ℓ_K(a) - δ_a`. None of these is needed
  to define the polynomial, so `p`, `K`, `i` are arbitrary natural numbers and `a` an arbitrary
  integer; the lemmas which need the range conditions take them as hypotheses.
* The exponent `i - ℓ_K(a) + 2` of the second branch is written `i + 2 - ℓ_K(a)` with natural
  subtraction; on that branch `ℓ_K(a) ≤ i + 2`, so the two agree.
* The source uses `K = 40 n`; here `K` is an arbitrary natural number, as for `Ξ_a`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.8: the outer range, the separating basis.
-/

@[expose] public section

namespace Zeta5Irr

open Finset Polynomial

variable (R : Type*) [CommRing R]

/-- The separating basis of the outer range: `q_{a,i}(t) = (t + a²)^i` if `i < ℓ_K(a) - 2`,
and `q_{a,i}(t) = Ξ_a(t) (t + a²)^{i - ℓ_K(a) + 2}` otherwise. -/
@[zeta5irr "def_out_q"]
noncomputable def outerBasis (p K : ℕ) (a : ℤ) (i : ℕ) : R[X] :=
  if i < ellA p K a - 2 then (X + C ((a : R) ^ 2)) ^ i
  else outXi R p K a * (X + C ((a : R) ^ 2)) ^ (i + 2 - ellA p K a)

variable {R}

/-- The first branch: `q_{a,i} = (X + a²)^i` when `i < ℓ_K(a) - 2`. -/
theorem outerBasis_of_lt {p K : ℕ} {a : ℤ} {i : ℕ} (h : i < ellA p K a - 2) :
    outerBasis R p K a i = (X + C ((a : R) ^ 2)) ^ i := by
  simp [outerBasis, h]

/-- The second branch: `q_{a,i} = Ξ_a (X + a²)^{i - ℓ_K(a) + 2}` when `ℓ_K(a) - 2 ≤ i`. -/
theorem outerBasis_of_le {p K : ℕ} {a : ℤ} {i : ℕ} (h : ellA p K a - 2 ≤ i) :
    outerBasis R p K a i = outXi R p K a * (X + C ((a : R) ^ 2)) ^ (i + 2 - ellA p K a) := by
  simp [outerBasis, h.not_gt]

/-- The separating basis polynomial `q_{a,i}` is monic. -/
@[zeta5irr "lem_out_q_monic"]
theorem outerBasis_monic (p K : ℕ) (a : ℤ) (i : ℕ) : (outerBasis R p K a i).Monic := by
  unfold outerBasis
  split_ifs
  · exact (monic_X_add_C _).pow _
  · exact (outXi_monic p K a).mul ((monic_X_add_C _).pow _)

/-- The separating basis commutes with ring homomorphisms. -/
theorem map_outerBasis {S : Type*} [CommRing S] (f : R →+* S) (p K : ℕ) (a : ℤ) (i : ℕ) :
    (outerBasis R p K a i).map f = outerBasis S p K a i := by
  unfold outerBasis outXi
  split_ifs <;> simp [Polynomial.map_prod]

/-- `ℓ_p(a) = 2`: among `1 ≤ j ≤ p`, the integers `≡ ±a (mod p)` are exactly `a` and `p - a`,
for `p` odd and `1 ≤ a ≤ m°`. -/
theorem ellA_self_eq_two {p : ℕ} (hp : Odd p) {a : ℤ} (ha : 1 ≤ a) (ha' : a ≤ mStar p) :
    ellA p p a = 2 := by
  have h2 := two_mul_mStar_add_one hp
  have hm : (2 * a + 1 : ℤ) ≤ p := by omega
  have : ((Icc (1 : ℤ) p).filter fun j ↦ j ≡ a [ZMOD p] ∨ j ≡ -a [ZMOD p]) = {a, p - a} := by
    ext j
    rw [mem_filter, mem_insert, mem_singleton, mem_Icc]
    constructor
    · rintro ⟨hj, h | h⟩
      · left
        have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (Int.ModEq.dvd h) (by omega)
        omega
      · right
        have h' : j ≡ p - a [ZMOD p] := h.trans (Int.modEq_iff_dvd.mpr ⟨1, by ring⟩)
        have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (Int.ModEq.dvd h') (by omega)
        omega
    · rintro (rfl | rfl)
      · exact ⟨by omega, .inl rfl⟩
      · exact ⟨by omega, .inr (Int.modEq_iff_dvd.mpr ⟨-1, by ring⟩)⟩
  rw [ellA, this, card_pair (by omega)]

/-- For `p` odd, `1 ≤ a ≤ m°` and `p ≤ K`, the residue-class polynomial `Ξ_a` has degree
`ℓ_K(a) - 2`, in the form `deg Ξ_a + 2 = ℓ_K(a)`. -/
theorem natDegree_outXi_add_two [Nontrivial R] {p K : ℕ} (hp : Odd p) {a : ℤ} (ha : 1 ≤ a)
    (ha' : a ≤ mStar p) (hK : p ≤ K) :
    (outXi R p K a).natDegree + 2 = ellA p K a := by
  rw [← ellA_self_eq_two hp ha ha', ← card_residuePoleIndices_add_ellA p a hK,
    outXi_eq_residuePoleProduct, natDegree_residuePoleProduct]

/-- If `deg Ξ_a + 2 = ℓ_K(a)`, then `q_{a,i}` has degree `i`. -/
theorem natDegree_outerBasis_of_natDegree_outXi [Nontrivial R] {p K : ℕ} {a : ℤ}
    (h : (outXi R p K a).natDegree + 2 = ellA p K a) (i : ℕ) :
    (outerBasis R p K a i).natDegree = i := by
  unfold outerBasis
  split_ifs with hi
  · exact natDegree_pow_X_add_C i _
  · rw [(outXi_monic p K a).natDegree_mul ((monic_X_add_C _).pow _),
      natDegree_pow_X_add_C]
    omega

/-- For `p` odd, `1 ≤ a ≤ m°` and `p ≤ K`, the separating basis polynomial `q_{a,i}` has
degree `i`. -/
@[zeta5irr "lem_out_q_monic"]
theorem natDegree_outerBasis [Nontrivial R] {p K : ℕ} (hp : Odd p) {a : ℤ} (ha : 1 ≤ a)
    (ha' : a ≤ mStar p) (hK : p ≤ K) (i : ℕ) :
    (outerBasis R p K a i).natDegree = i :=
  natDegree_outerBasis_of_natDegree_outXi (natDegree_outXi_add_two hp ha ha' hK) i

end Zeta5Irr
