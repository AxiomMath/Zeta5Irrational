/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Measure.VStar
public import Zeta5Irr.Measure.VParenNeg
public import Zeta5Irr.Measure.VMonoLeft
public import Zeta5Irr.Measure.VMonoRight

/-!
# The floor `V_*` is a lower bound for the external field

For every `t ≥ 0`, the external field satisfies `V_* ≤ V(t)`. On `[q₋, q₊]` this follows from
the closed form of `V` by bounding each term in the direction that decreases it: the logarithms
by monotonicity, the arctangents by monotonicity, and the factor `2 √t` in front of the bracket
by `2 √q₊`, which is legitimate because the lower bound of the bracket is negative. On `[0, q₋]`
the field is nonincreasing and on `[q₊, ∞)` it is nondecreasing, so these cases reduce to the
endpoints `q₋` and `q₊`.

## Main results

* `Zeta5Irr.externalFieldFloor_le_of_mem_Icc`: `V_* ≤ V(t)` for `q₋ ≤ t ≤ q₊`.
* `Zeta5Irr.externalFieldFloor_le`: `V_* ≤ V(t)` for every `t ≥ 0`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.6 (The interval bound and the partition of `[0,2]`).
-/

@[expose] public section

namespace Zeta5Irr

open Real Set

/-- On the bracket `[q₋, q₊]` around the minimum, the external field is at least `V_*`. -/
theorem externalFieldFloor_le_of_mem_Icc {t : ℝ}
    (ht : t ∈ Icc (externalFieldMinLower : ℝ) externalFieldMinUpper) :
    externalFieldFloor ≤ externalField t := by
  obtain ⟨hlt, hut⟩ := ht
  have hqm : (0 : ℝ) < externalFieldMinLower := by exact_mod_cast externalFieldMinLower_pos
  have ht0 : 0 < t := hqm.trans_le hlt
  have ha : (0 : ℝ) < innerRatio := by norm_num [innerRatio]
  rw [externalField_eq ht0, externalFieldFloor]
  set a : ℝ := (innerRatio : ℝ)
  set qm : ℝ := (externalFieldMinLower : ℝ)
  set qp : ℝ := (externalFieldMinUpper : ℝ)
  have hs : 0 < √t := sqrt_pos.2 ht0
  have hsm : 0 < √qm := sqrt_pos.2 hqm
  have hsp : √t ≤ √qp := sqrt_le_sqrt hut
  have hsm' : √qm ≤ √t := sqrt_le_sqrt hlt
  have h1 : log (1 + qm) ≤ log (1 + t) := log_le_log (by linarith) (by linarith)
  have h2 : log (t + a ^ 2) ≤ log (qp + a ^ 2) := log_le_log (by positivity) (by linarith)
  have h3 : arctan (√qp)⁻¹ ≤ arctan (1 / √t) := by
    rw [one_div]
    exact arctan_mono (inv_anti₀ hs hsp)
  have h4 : arctan (a / √t) ≤ arctan (a / √qm) :=
    arctan_mono (div_le_div_of_nonneg_left ha.le hsm hsm')
  have hneg := pi_add_arctan_sub_six_mul_arctan_neg
  rw [one_div] at hneg
  set B : ℝ := π + arctan (√qp)⁻¹ - 6 * arctan (a / √qm)
  have hB : B ≤ π + arctan (1 / √t) - 6 * arctan (a / √t) := by
    simp only [B]
    linarith
  have h5 : 2 * √qp * B ≤ 2 * √t * (π + arctan (1 / √t) - 6 * arctan (a / √t)) :=
    calc 2 * √qp * B ≤ 2 * √t * B := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hB (by positivity)
  nlinarith

/-- **The floor of the external field.** For every `t ≥ 0`, `V_* ≤ V(t)`. -/
@[zeta5irr "lem_V_star_lower"]
theorem externalFieldFloor_le {t : ℝ} (ht : 0 ≤ t) : externalFieldFloor ≤ externalField t := by
  have hqm : (0 : ℝ) ≤ externalFieldMinLower := by exact_mod_cast externalFieldMinLower_pos.le
  have hlu : (externalFieldMinLower : ℝ) ≤ externalFieldMinUpper := by
    exact_mod_cast externalFieldMinLower_lt_upper.le
  rcases le_total t externalFieldMinLower with h | h
  · exact (externalFieldFloor_le_of_mem_Icc ⟨le_rfl, hlu⟩).trans
      (antitoneOn_externalField ⟨ht, h⟩ ⟨hqm, le_rfl⟩ h)
  rcases le_total t externalFieldMinUpper with h' | h'
  · exact externalFieldFloor_le_of_mem_Icc ⟨h, h'⟩
  · exact (externalFieldFloor_le_of_mem_Icc ⟨hlu, le_rfl⟩).trans
      (monotoneOn_externalField le_rfl h' h')

end Zeta5Irr
