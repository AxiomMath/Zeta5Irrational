/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.TauTate

/-!
# The space of near-pole decompositions `𝓑_R`

For a finite set `R ⊆ ℤ`, the space of near-pole decompositions is
`𝓑_R = 𝒜 ⊕ ⨁_{r ∈ R} ℚ_p`, where `𝒜 = ℚ_p⟨z⟩` is the Tate algebra. Its elements are pairs
`(f, (c_r)_{r ∈ R})`, thought of as the function `f + ∑_{r ∈ R} c_r / (z - r)`, and it carries
the maximum norm `‖(f, (c_r))‖ = max (‖f‖, max_{r ∈ R} |c_r|_p)`.

## Main definitions

* `Zeta5Irr.tateAlgebra.normedAddCommGroup`, `Zeta5Irr.tateAlgebra.normedSpace`: the Gauss norm
  makes `ℚ_p⟨z⟩` a normed `ℚ_p`-vector space; the norm is ultrametric.
* `Zeta5Irr.BT p R`: the space `𝓑_R = ℚ_p⟨z⟩ ⊕ ℚ_p^R` with the maximum norm.
* `Zeta5Irr.BT.mk f c`: the element `(f, (c_r)_{r ∈ R})` of `𝓑_R`.
* `Zeta5Irr.BT.fst x`, `Zeta5Irr.BT.res x r`: the Tate-algebra component `f` and the residue
  `c_r` of `x = (f, (c_r))`.

## Main results

* `Zeta5Irr.tateAlgebra.norm_def`: the norm of `f ∈ ℚ_p⟨z⟩` is its Gauss norm.
* `Zeta5Irr.BT.norm_eq`: `‖x‖ = max ‖x.fst‖ (⨆ r, |x.res r|_p)`.
* `Zeta5Irr.BT.norm_mk`: `‖(f, (c_r))‖ = max ‖f‖ (⨆ r, |c_r|_p)`.

## Implementation notes

* `𝓑_R` is the `L^∞` product `WithLp ∞ (ℚ_p⟨z⟩ × (R → ℚ_p))`, so that it inherits the
  normed `ℚ_p`-vector space structure of the maximum norm. The direct sum over the finite set
  `R` is the function space `R → ℚ_p`, whose norm is already the maximum of the `|c_r|_p`.
* Stating the maximum norm requires a norm on `ℚ_p⟨z⟩`; it is provided here as the Gauss norm
  `Zeta5Irr.tateNorm`, restricted to the subalgebra `ℚ_p⟨z⟩` on which it is a genuine norm.
* The maximum over `r ∈ R` is written as `⨆ r`; for `R = ∅` this is `0`, which agrees with the
  convention that the maximum norm of `(f, ())` is `‖f‖`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.4 (Completion at a prime).
-/

@[expose] public section

namespace Zeta5Irr

open PowerSeries

variable {p : ℕ} [Fact p.Prime]

namespace tateAlgebra

/-- The Gauss norm on `ℚ_p⟨z⟩`, as an additive group norm. -/
noncomputable def addGroupNorm : AddGroupNorm (tateAlgebra p) where
  toFun f := tateNorm (f : ℚ_[p]⟦X⟧)
  map_zero' := tateNorm_zero
  add_le' f g := (tateNorm_add_le_max f.2 g.2).trans <|
    max_le_add_of_nonneg (tateNorm_nonneg _) (tateNorm_nonneg _)
  neg' f := tateNorm_neg (f : ℚ_[p]⟦X⟧)
  eq_zero_of_map_eq_zero' f hf := Subtype.ext <| (tateNorm_eq_zero_iff f.2).mp hf

/-- The Gauss norm makes `ℚ_p⟨z⟩` a normed additive group. -/
noncomputable instance normedAddCommGroup : NormedAddCommGroup (tateAlgebra p) :=
  addGroupNorm.toNormedAddCommGroup

/-- The norm of an element of `ℚ_p⟨z⟩` is its Gauss norm `sup_d |f_d|_p`. -/
theorem norm_def (f : tateAlgebra p) : ‖f‖ = tateNorm (f : ℚ_[p]⟦X⟧) :=
  rfl

/-- The Gauss norm makes `ℚ_p⟨z⟩` a normed `ℚ_p`-vector space. -/
noncomputable instance normedSpace : NormedSpace ℚ_[p] (tateAlgebra p) where
  norm_smul_le a f := by
    rw [norm_def, norm_def, Subalgebra.coe_smul, tateNorm_smul]

/-- The Gauss norm on `ℚ_p⟨z⟩` is ultrametric. -/
instance isUltrametricDist : IsUltrametricDist (tateAlgebra p) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun f g =>
    tateNorm_add_le_max f.2 g.2

end tateAlgebra

variable (p) in
/-- The space of near-pole decompositions `𝓑_R = ℚ_p⟨z⟩ ⊕ ⨁_{r ∈ R} ℚ_p` for a finite set
`R ⊆ ℤ`, with the maximum norm `‖(f, (c_r))‖ = max (‖f‖, max_{r ∈ R} |c_r|_p)`. An element
`(f, (c_r)_{r ∈ R})` stands for `f + ∑_{r ∈ R} c_r / (z - r)`. -/
@[zeta5irr "def_BT"]
abbrev BT (R : Finset ℤ) : Type :=
  WithLp ⊤ (tateAlgebra p × (R → ℚ_[p]))

namespace BT

variable {R : Finset ℤ}

/-- The element `(f, (c_r)_{r ∈ R})` of `𝓑_R`. -/
@[zeta5irr "def_BT"]
abbrev mk (f : tateAlgebra p) (c : R → ℚ_[p]) : BT p R :=
  WithLp.toLp ⊤ (f, c)

/-- The Tate-algebra component `f` of `(f, (c_r)) ∈ 𝓑_R`. -/
@[zeta5irr "def_BT"]
abbrev fst (x : BT p R) : tateAlgebra p :=
  x.ofLp.1

/-- The residue `c_r` at `r ∈ R` of `(f, (c_r)) ∈ 𝓑_R`. -/
@[zeta5irr "def_BT"]
abbrev res (x : BT p R) (r : R) : ℚ_[p] :=
  x.ofLp.2 r

/-- The Tate-algebra component of `(f, (c_r))` is `f`. -/
@[simp]
theorem fst_mk (f : tateAlgebra p) (c : R → ℚ_[p]) : (mk f c).fst = f :=
  rfl

/-- The residue at `r` of `(f, (c_r))` is `c_r`. -/
@[simp]
theorem res_mk (f : tateAlgebra p) (c : R → ℚ_[p]) (r : R) : (mk f c).res r = c r :=
  rfl

/-- Every `x ∈ 𝓑_R` is the pair of its Tate-algebra component and its residues. -/
@[simp]
theorem mk_fst_res (x : BT p R) : mk x.fst x.res = x :=
  rfl

/-- Two elements of `𝓑_R` with the same Tate-algebra component and the same residues are
equal. -/
theorem ext {x y : BT p R} (h₁ : x.fst = y.fst) (h₂ : ∀ r, x.res r = y.res r) : x = y := by
  rw [← mk_fst_res x, ← mk_fst_res y, h₁, funext h₂]

/-- The maximum norm on `𝓑_R`: `‖x‖ = max (‖f‖, max_{r ∈ R} |c_r|_p)`. -/
@[zeta5irr "def_BT"]
theorem norm_eq (x : BT p R) : ‖x‖ = max ‖x.fst‖ (⨆ r, ‖x.res r‖) := by
  rw [WithLp.prod_norm_eq_sup]
  congr 1
  refine le_antisymm ?_ (Real.iSup_le (fun r => norm_le_pi_norm x.ofLp.2 r) (norm_nonneg _))
  refine (pi_norm_le_iff_of_nonneg ?_).mpr fun r => ?_
  · exact Real.iSup_nonneg fun r => norm_nonneg _
  · exact le_ciSup (f := fun r => ‖x.res r‖) (Finite.bddAbove_range _) r

/-- The maximum norm of `(f, (c_r)_{r ∈ R})` is `max (‖f‖, max_{r ∈ R} |c_r|_p)`. -/
theorem norm_mk (f : tateAlgebra p) (c : R → ℚ_[p]) : ‖mk f c‖ = max ‖f‖ (⨆ r, ‖c r‖) :=
  norm_eq _

end BT

end Zeta5Irr
