/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.InMonicTriangular
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.ReduceModChar

/-!
# The distributing basis of `R[X]_d` attached to a coprime factorization

Let `R` be a commutative ring and `Π = ∏ₖ Πₖ` a product of monic polynomials over `R` which are
pairwise coprime in `R[X]`, and write `dₖ = deg Πₖ`, `d = deg Π = ∑ₖ dₖ` and
`Θₖ = ∏_{k' ≠ k} Πₖ' = Π / Πₖ`. If for every `k` and every `i < dₖ` the polynomial `q_{k,i}` is
monic of degree exactly `i`, then the polynomials `Θₖ q_{k,i}` form a basis of the `R`-module
`R[X]_d` of polynomials of degree less than `d`.

This is the Chinese remainder theorem made explicit: the map
`(rₖ)ₖ ↦ ∑ₖ Θₖ rₖ` from `∏ₖ R[X]_{dₖ}` to `R[X]_d` is bijective. Injectivity holds because
`Πₖ` divides every `Θₖ'` with `k' ≠ k` and is coprime to `Θₖ`, so a relation `∑ₖ Θₖ rₖ = 0`
forces `Πₖ ∣ rₖ`, whence `rₖ = 0` by degree. Surjectivity follows from a relation
`∑ₖ μₖ Θₖ = 1`: for `f ∈ R[X]_d` the polynomial `∑ₖ Θₖ (μₖ f mod Πₖ)` lies in `R[X]_d` and
differs from `f` by a multiple of `Π`, hence equals `f`. Composing with the bases `q_{k,i}` of
the `R[X]_{dₖ}` (`Zeta5Irr.exists_basis_degreeLT_of_monic`) gives the basis.

Over a local ring `R`, for instance `ℤ_p`, coprimality of monic polynomials in `R[X]` can be
tested on their images over the residue field: the resultant of two monic polynomials is
compatible with reduction, and it is a unit exactly when the polynomials are coprime.

## Main definitions

* `Polynomial.prodComplMul`: multiplication by `Θₖ`, as an `R`-linear map `R[X]_{dₖ} → R[X]_d`.

## Main results

* `Polynomial.isCoprime_of_isCoprime_map_residue`: monic polynomials over a local ring whose
  reductions over the residue field are coprime are coprime.
* `Polynomial.Monic.eq_zero_of_dvd_of_degree_lt`: a polynomial divisible by a monic polynomial
  of larger degree is zero.
* `Polynomial.bijective_sum_prodComplMul`: the map `(rₖ)ₖ ↦ ∑ₖ Θₖ rₖ` is a bijection
  `∏ₖ R[X]_{dₖ} → R[X]_d` for pairwise coprime monic `Πₖ`.
* `Polynomial.exists_basis_degreeLT_prod_compl_mul`: the family `Θₖ q_{k,i}` is a basis of
  `R[X]_d` for pairwise coprime monic `Πₖ`.
* `Zeta5Irr.exists_basis_degreeLT_prod_compl_mul_of_isLocalRing`: the same over a local ring,
  under the hypothesis that the reductions of the `Πₖ` over the residue field are pairwise
  coprime.
* `Zeta5Irr.isUnit_det_coeff_prod_compl_mul`: over a local ring, the square coefficient matrix
  of the basis `Θₖ q_{k,i}` has unit determinant.

## Implementation notes

* The source works over `ℤ_p` with the reduction `ℤ_p → ℤ_p/pℤ_p`; the statement here holds
  over any commutative local ring `R` with the reduction `R → R/𝔪` to the residue field, and
  is stated so. The source's comaximality argument by Nakayama's lemma is replaced by the
  resultant criterion for coprimality.
* The source gives `Π` together with the factorization `Π = ∏ₖ Πₖ` and sets `Θₖ = Π / Πₖ`.
  Here `Π` is the product `∏ₖ Πₖ` itself and `Θₖ` is the product of the `Πₖ'` over the
  complement of `{k}`, which is the quotient `Π / Πₖ`. The source's hypothesis `d ≥ 1` is not
  needed.
* The general statements `Polynomial.bijective_sum_prodComplMul` and
  `Polynomial.exists_basis_degreeLT_prod_compl_mul` assume `R` nontrivial, which is used for
  division with remainder by a monic polynomial; a local ring is nontrivial.
* The index set of the factorization is an arbitrary finite type `ι`, and the basis is indexed
  by the dependent pairs `(k, i)` with `i < dₖ`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.4 (The inner range: the distributing basis).
-/

@[expose] public section

open Function Module Polynomial IsLocalRing

namespace Polynomial

section LocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- Two monic polynomials over a local ring are coprime as soon as their reductions over the
residue field are coprime. -/
theorem isCoprime_of_isCoprime_map_residue {f g : R[X]} (hf : f.Monic) (hg : g.Monic)
    (h : IsCoprime (f.map (residue R)) (g.map (residue R))) : IsCoprime f g := by
  rw [← isUnit_resultant_iff_isCoprime hf]
  rw [← isUnit_resultant_iff_isCoprime (hf.map _), hf.natDegree_map, hg.natDegree_map,
    resultant_map_map] at h
  exact (isUnit_map_iff (residue R) _).1 h

end LocalRing

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- For monic `Πₖ`, multiplication by `Θₖ = ∏_{k' ≠ k} Πₖ'` maps `R[X]_{dₖ}` into `R[X]_d`,
where `dₖ = deg Πₖ` and `d = deg ∏ₖ Πₖ`. -/
theorem prod_compl_mul_mem_degreeLT {P : ι → R[X]} (hP : ∀ k, (P k).Monic) (k : ι)
    {r : R[X]} (hr : r ∈ degreeLT R (P k).natDegree) :
    (∏ k' ∈ {k}ᶜ, P k') * r ∈ degreeLT R (∏ k, P k).natDegree := by
  rw [mem_degreeLT] at hr ⊢
  have hΘ : (∏ k' ∈ {k}ᶜ, P k').Monic := monic_prod_of_monic _ _ fun k' _ ↦ hP k'
  have hprod : (∏ k, P k).natDegree = (∏ k' ∈ {k}ᶜ, P k').natDegree + (P k).natDegree := by
    rw [← Finset.prod_compl_mul_prod {k}, Finset.prod_singleton,
      hΘ.natDegree_mul (hP k)]
  by_cases hr0 : r = 0
  · simp [hr0]
  refine degree_le_natDegree.trans_lt ?_
  rw [hΘ.natDegree_mul' (by simpa [hΘ.leadingCoeff] using hr0), hprod]
  have := (natDegree_lt_iff_degree_lt hr0).2 hr
  exact_mod_cast Nat.add_lt_add_left this _

/-- The `R`-linear map `R[X]_{dₖ} → R[X]_d` given by multiplication by `Θₖ = ∏_{k' ≠ k} Πₖ'`,
where `dₖ = deg Πₖ` and `d = deg ∏ₖ Πₖ`. -/
noncomputable def prodComplMul {P : ι → R[X]} (hP : ∀ k, (P k).Monic) (k : ι) :
    degreeLT R (P k).natDegree →ₗ[R] degreeLT R (∏ k, P k).natDegree :=
  (LinearMap.mulLeft R (∏ k' ∈ {k}ᶜ, P k')).restrict fun _ hr ↦
    prod_compl_mul_mem_degreeLT hP k hr

/-- The value of `prodComplMul` at `r` is the product `Θₖ r`. -/
@[simp]
theorem coe_prodComplMul_apply {P : ι → R[X]} (hP : ∀ k, (P k).Monic) (k : ι)
    (r : degreeLT R (P k).natDegree) :
    (prodComplMul hP k r : R[X]) = (∏ k' ∈ {k}ᶜ, P k') * r :=
  rfl

/-- If a monic polynomial `p` divides a polynomial `f` of smaller degree, then `f = 0`. This is
the contrapositive of `Polynomial.Monic.not_dvd_of_degree_lt`, with the degree of `p` written as
`p.natDegree`. -/
theorem Monic.eq_zero_of_dvd_of_degree_lt [Nontrivial R] {p f : R[X]} (hp : p.Monic)
    (hdvd : p ∣ f) (hf : f.degree < p.natDegree) : f = 0 :=
  of_not_not fun h ↦ hp.not_dvd_of_degree_lt h (by rwa [degree_eq_natDegree hp.ne_zero]) hdvd

/-- For pairwise coprime monic polynomials `Πₖ`, with `dₖ = deg Πₖ`, `d = deg ∏ₖ Πₖ` and
`Θₖ = ∏_{k' ≠ k} Πₖ'`, the map `(rₖ)ₖ ↦ ∑ₖ Θₖ rₖ` is a bijection `∏ₖ R[X]_{dₖ} → R[X]_d`. -/
theorem bijective_sum_prodComplMul [Nontrivial R] {P : ι → R[X]} (hP : ∀ k, (P k).Monic)
    (hcop : Pairwise (IsCoprime on P)) :
    Function.Bijective (∑ k, (prodComplMul hP k).comp (LinearMap.proj k) :
      (∀ k, degreeLT R (P k).natDegree) →ₗ[R] degreeLT R (∏ k, P k).natDegree) := by
  have hprod : (∏ k, P k).Monic := monic_prod_of_monic _ _ fun k _ ↦ hP k
  have hΦ (x : ∀ k, degreeLT R (P k).natDegree) :
      ((∑ k, (prodComplMul hP k).comp (LinearMap.proj k) : _ →ₗ[R] _) x : R[X]) =
        ∑ k, (∏ k' ∈ {k}ᶜ, P k') * x k := by
    simp
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ _root_.funext fun k ↦ ?_, fun f ↦ ?_⟩
  · have hx' := congrArg Subtype.val hx
    rw [hΦ, ← Finset.add_sum_erase _ _ (Finset.mem_univ k)] at hx'
    have hrest : P k ∣ ∑ j ∈ Finset.univ.erase k, (∏ k' ∈ {j}ᶜ, P k') * x j :=
      Finset.dvd_sum fun j hj ↦ dvd_mul_of_dvd_left
        (Finset.dvd_prod_of_mem P <| by simpa using (Finset.ne_of_mem_erase hj).symm) _
    have hk : P k ∣ (∏ k' ∈ {k}ᶜ, P k') * x k :=
      (dvd_add_left hrest).1 (by rw [hx']; exact dvd_zero _)
    have hcopk : IsCoprime (P k) (∏ k' ∈ {k}ᶜ, P k') :=
      IsCoprime.prod_right fun j hj ↦ hcop (Ne.symm (by simpa using hj))
    exact Subtype.ext ((hP k).eq_zero_of_dvd_of_degree_lt
      (hcopk.dvd_of_dvd_mul_left hk) (mem_degreeLT.1 (x k).2))
  obtain ⟨f, hf⟩ := f
  cases isEmpty_or_nonempty ι with
  | inl _ =>
    refine ⟨0, Subtype.ext ?_⟩
    have := mem_degreeLT.1 hf
    simp only [Finset.univ_eq_empty, Finset.prod_empty, natDegree_one, CharP.cast_eq_zero] at this
    rw [map_zero, ZeroMemClass.coe_zero, eq_comm]
    by_contra h
    exact (zero_le_degree_iff.2 h).not_gt this
  | inr _ =>
    obtain ⟨μ, hμ⟩ := (exists_sum_eq_one_iff_pairwise_coprime' (s := P)).2 hcop
    refine ⟨fun k ↦ ⟨(μ k * f) %ₘ P k, mem_degreeLT.2 <|
      (degree_modByMonic_lt _ (hP k)).trans_le degree_le_natDegree⟩, Subtype.ext ?_⟩
    rw [hΦ]
    dsimp only
    set g := ∑ k, (∏ k' ∈ {k}ᶜ, P k') * ((μ k * f) %ₘ P k)
    have hg : g ∈ degreeLT R (∏ k, P k).natDegree :=
      Submodule.sum_mem _ fun k _ ↦ prod_compl_mul_mem_degreeLT hP k <| mem_degreeLT.2 <|
        (degree_modByMonic_lt _ (hP k)).trans_le degree_le_natDegree
    have hdiff : f - g = (∏ k, P k) * ∑ k, (μ k * f) /ₘ P k := by
      rw [Finset.mul_sum]
      conv_lhs => rw [← mul_one f, ← hμ, Finset.mul_sum]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [← Finset.prod_compl_mul_prod {k}, Finset.prod_singleton]
      linear_combination (-(∏ k' ∈ {k}ᶜ, P k')) * modByMonic_add_div (μ k * f) (P k)
    have h0 := hprod.eq_zero_of_dvd_of_degree_lt (hdiff ▸ dvd_mul_right _ _)
      (mem_degreeLT.1 (sub_mem hf hg))
    exact (sub_eq_zero.1 h0).symm

/-- **The distributing basis.** For pairwise coprime monic polynomials `Πₖ`, with
`dₖ = deg Πₖ`, `d = deg ∏ₖ Πₖ` and `Θₖ = ∏_{k' ≠ k} Πₖ'`, and polynomials `q_{k,i}` monic of
degree exactly `i` for `i < dₖ`, the family `Θₖ q_{k,i}` is a basis of the polynomials of degree
less than `d`. -/
theorem exists_basis_degreeLT_prod_compl_mul [Nontrivial R] {P : ι → R[X]}
    (hP : ∀ k, (P k).Monic) (hcop : Pairwise (IsCoprime on P))
    (q : (k : ι) → Fin (P k).natDegree → R[X]) (hq : ∀ k i, (q k i).Monic)
    (hqdeg : ∀ k i, (q k i).natDegree = i) :
    ∃ b : Basis (Σ k, Fin (P k).natDegree) R (degreeLT R (∏ k, P k).natDegree),
      ∀ k i, (b ⟨k, i⟩ : R[X]) = (∏ k' ∈ {k}ᶜ, P k') * q k i := by
  choose B hB using fun k ↦ Zeta5Irr.exists_basis_degreeLT_of_monic (q k) (hq k) (hqdeg k)
  refine ⟨(Pi.basis B).map (LinearEquiv.ofBijective _ (bijective_sum_prodComplMul hP hcop)),
    fun k i ↦ ?_⟩
  rw [Basis.map_apply, Pi.basis_apply, LinearEquiv.ofBijective_apply, LinearMap.sum_apply,
    Finset.sum_eq_single k]
  · simp [hB]
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

end Polynomial

namespace Zeta5Irr

variable {R : Type*} [CommRing R] [IsLocalRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The distributing basis** (§5.4). Let `R` be a local ring (in the source, `ℤ_p`) and
`Πₖ` monic polynomials over `R` whose reductions over the residue field are pairwise coprime.
Put `dₖ = deg Πₖ`, `Π = ∏ₖ Πₖ`, `d = deg Π` and `Θₖ = Π / Πₖ = ∏_{k' ≠ k} Πₖ'`, and let
`q_{k,i}` be monic of degree exactly `i` for `i < dₖ`. Then the family `Θₖ q_{k,i}` is a basis
of the `R`-module of polynomials of degree less than `d`. -/
@[zeta5irr "lem_in_crt_basis"]
theorem exists_basis_degreeLT_prod_compl_mul_of_isLocalRing {P : ι → R[X]}
    (hP : ∀ k, (P k).Monic)
    (hcop : Pairwise fun k k' ↦ IsCoprime ((P k).map (residue R)) ((P k').map (residue R)))
    (q : (k : ι) → Fin (P k).natDegree → R[X]) (hq : ∀ k i, (q k i).Monic)
    (hqdeg : ∀ k i, (q k i).natDegree = i) :
    ∃ b : Basis (Σ k, Fin (P k).natDegree) R (degreeLT R (∏ k, P k).natDegree),
      ∀ k i, (b ⟨k, i⟩ : R[X]) = (∏ k' ∈ {k}ᶜ, P k') * q k i :=
  exists_basis_degreeLT_prod_compl_mul hP
    (fun _ _ h ↦ isCoprime_of_isCoprime_map_residue (hP _) (hP _) (hcop h)) q hq hqdeg


/-- **The distributing basis is unimodular.** Let `R` be a local ring and `Πₖ` monic
polynomials of degrees `dₖ` over `R` whose reductions over the residue field are pairwise
coprime, and let `q_{k,i}` be monic of degree exactly `i`. For any identification `e` of the
pairs `(k, i)`, `i < dₖ`, with `Fin D`, the square matrix of the coefficients of the
polynomials `Θₖ q_{k,i} = (∏_{k' ≠ k} Πₖ') q_{k,i}` in the monomials `t^{e(j)}` has unit
determinant. -/
theorem isUnit_det_coeff_prod_compl_mul {d : ι → ℕ} {P : ι → R[X]} (hP : ∀ k, (P k).Monic)
    (hdeg : ∀ k, (P k).natDegree = d k)
    (hcop : Pairwise fun k k' ↦ IsCoprime ((P k).map (residue R)) ((P k').map (residue R)))
    (q : ι → ℕ → R[X]) (hq : ∀ k i, (q k i).Monic) (hqdeg : ∀ k i, (q k i).natDegree = i)
    {D : ℕ} (e : (Σ k, Fin (d k)) ≃ Fin D) :
    IsUnit (Matrix.of fun (ai aj : Σ k, Fin (d k)) ↦
      ((∏ k' ∈ {ai.1}ᶜ, P k') * q ai.1 ai.2).coeff (e aj)).det := by
  have hD : (∏ k, P k).natDegree = D := by
    rw [natDegree_prod_of_monic _ _ fun k _ ↦ hP k, ← Fintype.card_fin D, ← Fintype.card_congr e,
      Fintype.card_sigma]
    simp only [hdeg, Fintype.card_fin]
  obtain ⟨b, hb⟩ := exists_basis_degreeLT_prod_compl_mul_of_isLocalRing hP hcop
    (fun k i ↦ q k i) (fun _ _ ↦ hq _ _) (fun _ _ ↦ hqdeg _ _)
  let τ : (Σ k, Fin (d k)) ≃ Σ k, Fin (P k).natDegree :=
    Equiv.sigmaCongrRight fun k ↦ finCongr (hdeg k).symm
  generalize hD' : (∏ k, P k).natDegree = D' at b hb
  obtain rfl : D' = D := hD'.symm.trans hD
  let s : Basis _ R (degreeLT R D') :=
    ((Pi.basisFun R (Fin D')).map (degreeLTEquiv R _).symm).reindex e.symm
  let b₁ := b.reindex τ.symm
  have hs : ∀ f ai, s.repr f ai = (f : R[X]).coeff (e ai) := fun f ai ↦ by
    simp [s, degreeLTEquiv]
  have hM : (Matrix.of fun (ai aj : Σ k, Fin (d k)) ↦
      ((∏ k' ∈ {ai.1}ᶜ, P k') * q ai.1 ai.2).coeff (e aj)) = (s.toMatrix b₁).transpose := by
    ext ai aj
    rw [Matrix.transpose_apply, Basis.toMatrix_apply, hs, Matrix.of_apply]
    have hb₁ : (b₁ ai : R[X]) = (∏ k' ∈ {ai.1}ᶜ, P k') * q ai.1 ai.2 := by
      simpa [b₁, τ] using hb ai.1 (finCongr (hdeg ai.1).symm ai.2)
    rw [hb₁]
  rw [hM, Matrix.det_transpose, ← Basis.det_apply]
  exact s.isUnit_det b₁

end Zeta5Irr
