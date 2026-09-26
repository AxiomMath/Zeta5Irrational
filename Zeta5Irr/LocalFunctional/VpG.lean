/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Presheaf

/-!
# The Gauss valuation `v_p^G` of a polynomial over `ℚ_p`

For a polynomial `A ∈ ℚ_p[X]`, the Gauss valuation `v_p^G(A)` is the minimum of the `p`-adic
valuations of the coefficients of `A`, with `v_p^G(0) = +∞`. This is the additive counterpart
of the Gauss norm `Polynomial.gaussNorm`.

We define the construction for an arbitrary additive valuation `v` on a ring `R`: the Gauss
valuation of `A ∈ R[X]` is the infimum of `v (A.coeff i)` over the support of `A`. The
`p`-adic case is the specialisation to `Padic.addValuation`.

## Main definitions

* `Zeta5Irr.gaussAddVal v A`: the minimum of `v` over the coefficients of `A`, `⊤` if `A = 0`.
* `Zeta5Irr.vpG A`: the Gauss valuation `v_p^G(A) ∈ ℤ ∪ {+∞}` of `A ∈ ℚ_p[X]`.

## Main results

* `Zeta5Irr.le_gaussAddVal_iff`: `c ≤ gaussAddVal v A ↔ ∀ i, c ≤ v (A.coeff i)`.
* `Zeta5Irr.gaussAddVal_eq_top_iff`: for a valuation with trivial support (e.g. on a field),
  `gaussAddVal v A = ⊤ ↔ A = 0`.
* `Zeta5Irr.min_le_gaussAddVal_add`: the ultrametric inequality.
* `Zeta5Irr.gaussAddVal_C_mul`: `gaussAddVal v (C a * A) = v a + gaussAddVal v A`.
* `Zeta5Irr.coe_le_map_intCast_iff`: a lower bound in `WithTop ℚ` (or `WithTop ℝ`) for an
  element of `WithTop ℤ` is the lower bound given by its ceiling.
* `Zeta5Irr.padicValRat_prod_of_ne_zero`, `Zeta5Irr.padicValInt_prod_of_ne_zero`: `v_p` of a
  finite product of nonzero numbers is the sum of the `v_p`.
* `Zeta5Irr.vpG_map_C_sq_mul_of_norm_eq_one`: `v_p^G(d² G) = v_p^G(G)` for a `p`-adic unit
  `d ∈ ℚ`.
* `Zeta5Irr.vpG_nonneg_of_mem_lifts`: a polynomial in `ℤ_p[X]` has `v_p^G ≥ 0`.

## Implementation notes

* The value group is `WithTop ℤ`, so that `v_p^G(0) = +∞` is a genuine value and the order,
  `min` and `+` of `ℤ ∪ {+∞}` are available; this is the value group of `Padic.addValuation`.
* Since `v 0 = ⊤`, taking the infimum over the support of `A` or over any finite set of indices
  containing it gives the same value; `le_gaussAddVal_iff` quantifies over all indices.
* The blueprint uses the same formula for polynomials in any single variable over `ℚ_p`; this
  is `vpG` applied to the polynomial in that variable.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.4: completion at a prime.
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

section General

variable {R Γ : Type*} [Ring R] [LinearOrderedAddCommMonoidWithTop Γ]

/-- The Gauss valuation of a polynomial with respect to an additive valuation `v`: the minimum
of `v` over the coefficients of `A`, equal to `⊤` when `A = 0`. -/
def gaussAddVal (v : AddValuation R Γ) (A : R[X]) : Γ :=
  A.support.inf fun i => v (A.coeff i)

variable (v : AddValuation R Γ)

/-- `c ≤ gaussAddVal v A` iff `c ≤ v (A.coeff i)` for every index `i`. -/
theorem le_gaussAddVal_iff {A : R[X]} {c : Γ} :
    c ≤ gaussAddVal v A ↔ ∀ i, c ≤ v (A.coeff i) := by
  unfold gaussAddVal
  rw [Finset.le_inf_iff]
  refine ⟨fun h i => ?_, fun h i _ => h i⟩
  by_cases hi : A.coeff i = 0
  · simp [hi]
  · exact h i (mem_support_iff.mpr hi)

/-- The Gauss valuation is at most the valuation of every coefficient. -/
theorem gaussAddVal_le (A : R[X]) (i : ℕ) : gaussAddVal v A ≤ v (A.coeff i) :=
  (le_gaussAddVal_iff v).mp le_rfl i

/-- If `A ≠ 0`, the Gauss valuation is attained at some coefficient in the support. -/
theorem exists_gaussAddVal_eq {A : R[X]} (hA : A ≠ 0) :
    ∃ i ∈ A.support, gaussAddVal v A = v (A.coeff i) :=
  Finset.exists_mem_eq_inf _ (support_nonempty.mpr hA) _

/-- The Gauss valuation of the zero polynomial is `⊤`. -/
@[simp]
theorem gaussAddVal_zero : gaussAddVal v (0 : R[X]) = ⊤ := by
  simp [gaussAddVal]

/-- The Gauss valuation of a constant polynomial is the valuation of the constant. -/
@[simp]
theorem gaussAddVal_C (a : R) : gaussAddVal v (C a) = v a := by
  refine le_antisymm (by simpa using gaussAddVal_le v (C a) 0) ((le_gaussAddVal_iff v).mpr ?_)
  intro i
  rcases eq_or_ne i 0 with rfl | hi
  · simp
  · simp [coeff_C, hi]

/-- The Gauss valuation is invariant under negation. -/
@[simp]
theorem gaussAddVal_neg (A : R[X]) : gaussAddVal v (-A) = gaussAddVal v A := by
  simp [gaussAddVal, AddValuation.map_neg]

/-- The ultrametric inequality for the Gauss valuation. -/
theorem min_le_gaussAddVal_add (A B : R[X]) :
    min (gaussAddVal v A) (gaussAddVal v B) ≤ gaussAddVal v (A + B) := by
  refine (le_gaussAddVal_iff v).mpr fun i => ?_
  rw [coeff_add]
  exact le_trans (min_le_min (gaussAddVal_le v A i) (gaussAddVal_le v B i)) (v.map_add _ _)

/-- The Gauss valuation of a finite sum is at least the minimum of the Gauss valuations. -/
@[zeta5irr "lem_in_vpG_sum"]
theorem finset_inf_le_gaussAddVal_sum {ι : Type*} (s : Finset ι) (f : ι → R[X]) :
    s.inf (fun j => gaussAddVal v (f j)) ≤ gaussAddVal v (∑ j ∈ s, f j) := by
  refine (le_gaussAddVal_iff v).mpr fun i => ?_
  rw [finsetSum_coeff]
  exact AddValuation.map_le_sum v fun j hj => (Finset.inf_le hj).trans (gaussAddVal_le v (f j) i)

/-- Multiplying by a constant adds its valuation. -/
theorem gaussAddVal_C_mul (a : R) (A : R[X]) :
    gaussAddVal v (C a * A) = v a + gaussAddVal v A := by
  by_cases hA : A = 0
  · subst hA
    simp
  obtain ⟨i, -, hi⟩ := exists_gaussAddVal_eq v hA
  refine le_antisymm ?_ ((le_gaussAddVal_iff v).mpr fun j => ?_)
  · calc gaussAddVal v (C a * A) ≤ v ((C a * A).coeff i) := gaussAddVal_le v _ i
      _ = v a + gaussAddVal v A := by rw [coeff_C_mul, v.map_mul, hi]
  · rw [coeff_C_mul, v.map_mul]
    exact add_le_add_right (gaussAddVal_le v A j) _

/-- For a valuation whose only zero is `0` (e.g. any valuation on a field), the Gauss valuation
is `⊤` exactly at the zero polynomial. -/
theorem gaussAddVal_eq_top_iff (hv : ∀ x, v x = ⊤ → x = 0) {A : R[X]} :
    gaussAddVal v A = ⊤ ↔ A = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ gaussAddVal_zero v⟩
  ext i
  exact hv _ (top_le_iff.mp (h ▸ gaussAddVal_le v A i))

end General

section WithTopCast

variable {α : Type*} [Ring α] [LinearOrder α] [FloorRing α]

/-- A lower bound `x ≤ z` in `WithTop α` (for `α` an ordered ring with a floor, such as `ℚ` or
`ℝ`), for `z ∈ WithTop ℤ`, is the integer lower bound `⌈x⌉ ≤ z` in `WithTop ℤ`. -/
theorem coe_le_map_intCast_iff (x : α) (z : WithTop ℤ) :
    (x : WithTop α) ≤ z.map ((↑) : ℤ → α) ↔ ((⌈x⌉ : ℤ) : WithTop ℤ) ≤ z := by
  induction z using WithTop.recTopCoe with
  | top => simp
  | coe k => simp [WithTop.coe_le_coe, Int.ceil_le]

/-- For an integer `m` and `z ∈ WithTop ℤ`, `m ≤ z` holds in `WithTop α` iff it holds in
`WithTop ℤ`. -/
theorem intCast_le_map_intCast_iff [IsOrderedRing α] (m : ℤ) (z : WithTop ℤ) :
    ((m : α) : WithTop α) ≤ z.map ((↑) : ℤ → α) ↔ (m : WithTop ℤ) ≤ z := by
  rw [coe_le_map_intCast_iff, Int.ceil_intCast]

/-- A lower bound `x ≤ z` in `WithTop α`, for `z ∈ WithTop ℤ`, from an integer lower bound
`m ≤ z` with `x ≤ m`. -/
theorem coe_le_map_intCast_of_le {x : α} {m : ℤ} {z : WithTop ℤ} (hx : x ≤ m)
    (hm : (m : WithTop ℤ) ≤ z) : (x : WithTop α) ≤ z.map ((↑) : ℤ → α) :=
  (coe_le_map_intCast_iff x z).2 ((WithTop.coe_le_coe.2 (Int.ceil_le.2 hx)).trans hm)

end WithTopCast

section Padic

variable {p : ℕ} [Fact p.Prime]

/-- The `p`-adic valuation of a finite product of nonzero rationals is the sum of the
valuations. -/
theorem padicValRat_prod_of_ne_zero {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValRat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValRat p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      padicValRat.mul (hf a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.2 fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)]

/-- The `p`-adic valuation of a finite product of nonzero integers is the sum of the
valuations. -/
theorem padicValInt_prod_of_ne_zero {ι : Type*} (s : Finset ι) (f : ι → ℤ)
    (hf : ∀ i ∈ s, f i ≠ 0) : padicValInt p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValInt p (f i) := by
  have h := padicValRat_prod_of_ne_zero (p := p) s (fun i ↦ (f i : ℚ)) fun i hi ↦
    Int.cast_ne_zero.2 (hf i hi)
  simp only [← Int.cast_prod, padicValRat.of_int] at h
  exact_mod_cast h

/-- The Gauss valuation `v_p^G(A)` of a polynomial `A ∈ ℚ_p[X]`: the minimum of the `p`-adic
valuations of the coefficients of `A`, with `v_p^G(0) = +∞`. -/
@[zeta5irr "def_vpG"]
noncomputable abbrev vpG (A : ℚ_[p][X]) : WithTop ℤ :=
  gaussAddVal Padic.addValuation A

/-- `v_p^G(A) = +∞` iff `A = 0`. -/
theorem vpG_eq_top_iff {A : ℚ_[p][X]} : vpG A = ⊤ ↔ A = 0 :=
  gaussAddVal_eq_top_iff _ fun _ => AddValuation.top_iff _ |>.mp

/-- A `p`-adic number of norm `1` has valuation `0`. -/
theorem addValuation_eq_zero_of_norm_eq_one {x : ℚ_[p]} (h : ‖x‖ = 1) :
    Padic.addValuation x = 0 := by
  have hx : x ≠ 0 := fun h0 ↦ by simp [h0] at h
  rw [Padic.norm_eq_zpow_neg_valuation hx] at h
  have h1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have := zpow_right_injective₀ (by positivity) h1.ne' (h.trans (zpow_zero _).symm)
  rw [Padic.addValuation.apply hx]
  exact_mod_cast neg_eq_zero.mp this

/-- Multiplying a rational polynomial by the square of a `p`-adic unit `d ∈ ℚ` does not change
its Gauss valuation: `v_p^G(d² G) = v_p^G(G)`. -/
theorem vpG_map_C_sq_mul_of_norm_eq_one {d : ℚ} (hd : ‖(d : ℚ_[p])‖ = 1) (G : ℚ[X]) :
    vpG ((C (d ^ 2) * G).map (Rat.castHom ℚ_[p])) = vpG (G.map (Rat.castHom ℚ_[p])) := by
  rw [Polynomial.map_mul, map_C, vpG, vpG, gaussAddVal_C_mul, map_pow, AddValuation.map_pow,
    eq_ratCast, addValuation_eq_zero_of_norm_eq_one hd]
  simp

/-- A polynomial with coefficients in `ℤ_p` has nonnegative Gauss valuation. -/
theorem vpG_nonneg_of_mem_lifts {T : ℚ_[p][X]}
    (hT : T ∈ lifts (PadicInt.Coe.ringHom (p := p))) : 0 ≤ vpG T := by
  obtain ⟨T', rfl⟩ := (mem_lifts T).mp hT
  refine (le_gaussAddVal_iff _).mpr fun k ↦ ?_
  rw [coeff_map]
  by_cases hk : PadicInt.Coe.ringHom (T'.coeff k) = 0
  · rw [hk, AddValuation.map_zero]
    exact le_top
  · rw [Padic.addValuation.apply hk]
    exact WithTop.coe_le_coe.mpr ((Padic.norm_le_one_iff_val_nonneg _).mp
      (PadicInt.norm_def.symm.trans_le (T'.coeff k).norm_le_one))

end Padic

section PadicValuation

variable {p : ℕ} [Fact p.Prime]

/-- `v_p(p^k) = k`. -/
theorem addValuation_prime_zpow (k : ℤ) : Padic.addValuation ((p : ℚ_[p]) ^ k) = k := by
  have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [Padic.addValuation.apply (zpow_ne_zero _ hp), Padic.valuation_zpow, Padic.valuation_p,
    mul_one]

/-- For `y ∈ ℚ_p` and `k ∈ ℤ`, `k ≤ v_p(y)` if and only if `‖y‖ ≤ p^{-k}`. -/
theorem intCast_le_padicAddValuation_iff {y : ℚ_[p]} {k : ℤ} :
    (k : WithTop ℤ) ≤ Padic.addValuation y ↔ ‖y‖ ≤ (p : ℝ) ^ (-k) := by
  rcases eq_or_ne y 0 with rfl | hy
  · rw [AddValuation.map_zero, norm_zero]
    exact iff_of_true le_top (by positivity)
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  rw [Padic.addValuation.apply hy, WithTop.coe_le_coe, Padic.norm_eq_zpow_neg_valuation hy,
    zpow_le_zpow_iff_right₀ hp, neg_le_neg_iff]

/-- A `p`-adic number has nonnegative additive valuation if and only if it lies in `ℤ_p`. -/
theorem zero_le_addValuation_iff_norm_le_one (x : ℚ_[p]) :
    (0 : WithTop ℤ) ≤ Padic.addValuation x ↔ ‖x‖ ≤ 1 := by
  simpa using intCast_le_padicAddValuation_iff (y := x) (k := 0)

end PadicValuation

end Zeta5Irr
