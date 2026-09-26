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
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The table `𝒯` of the outer integral

The outer integral is computed by splitting the interval `[1/3, 37/20]` into eleven
consecutive subintervals `[l, r]`, on each of which the integrand is governed by an affine
function with coefficients `b` and `c`. The table `𝒯` lists the eleven quadruples
`(l, r, b, c)` of rational numbers:

| `l` | `r` | `b` | `c` |
|---|---|---|---|
| `1/3` | `43/120` | `279/40` | `-9` |
| `43/120` | `37/100` | `451/40` | `-21` |
| `37/100` | `13/30` | `377/40` | `-16` |
| `13/30` | `37/80` | `429/40` | `-19` |
| `37/80` | `1/2` | `17/4` | `-5` |
| `1/2` | `43/80` | `51/10` | `-3` |
| `43/80` | `37/60` | `231/20` | `-15` |
| `37/60` | `13/20` | `97/10` | `-12` |
| `13/20` | `37/40` | `42/5` | `-10` |
| `37/40` | `1` | `1` | `-2` |
| `1` | `37/20` | `37/20` | `-1` |

## Main definitions

* `Zeta5Irr.outerTable`: the table `𝒯`, as a list of quadruples `(l, r, b, c)`.

## Main results

* `Zeta5Irr.outerTable_length`: `𝒯` has eleven rows.
* `Zeta5Irr.outerTable_isChain`: the right endpoint of each row is the left endpoint of the
  next, so the rows tile an interval.
* `Zeta5Irr.outerTable_head_left`, `Zeta5Irr.outerTable_getLast_right`: that interval is
  `[1/3, 37/20]`.
* `Zeta5Irr.outerTable_left_lt_right`: every row is a nondegenerate interval, `l < r`.

## Implementation notes

* The source prints `𝒯` in two columns, read column by column. It is formalized as a
  `List` in the order of increasing `l`, since consecutive rows tile the interval of
  integration and the outer integral is a sum along this order.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §7.4: the outer integral.
-/

@[expose] public section

namespace Zeta5Irr

/-- The table `𝒯` of the outer integral: eleven quadruples `(l, r, b, c)` of rationals,
listed in order of increasing `l`. -/
@[zeta5irr "def_ex_outer_table"]
def outerTable : List (ℚ × ℚ × ℚ × ℚ) :=
  [(1/3, 43/120, 279/40, -9),
   (43/120, 37/100, 451/40, -21),
   (37/100, 13/30, 377/40, -16),
   (13/30, 37/80, 429/40, -19),
   (37/80, 1/2, 17/4, -5),
   (1/2, 43/80, 51/10, -3),
   (43/80, 37/60, 231/20, -15),
   (37/60, 13/20, 97/10, -12),
   (13/20, 37/40, 42/5, -10),
   (37/40, 1, 1, -2),
   (1, 37/20, 37/20, -1)]

/-- The table `𝒯` has eleven rows. -/
theorem outerTable_length : outerTable.length = 11 := rfl

/-- The rows of `𝒯` are consecutive: the right endpoint `r` of each row is the left
endpoint `l` of the next. -/
theorem outerTable_isChain : outerTable.IsChain (fun p q => p.2.1 = q.1) := by
  simp only [outerTable, List.isChain_cons_cons, List.isChain_singleton]
  norm_num

/-- The first row of `𝒯` starts at `1/3`. -/
theorem outerTable_head_left : (outerTable.head (by simp [outerTable])).1 = 1 / 3 := rfl

/-- The last row of `𝒯` ends at `37/20`. -/
theorem outerTable_getLast_right :
    (outerTable.getLast (by simp [outerTable])).2.1 = 37 / 20 := rfl

/-- Every row `(l, r, b, c)` of `𝒯` satisfies `l < r`. -/
theorem outerTable_left_lt_right : ∀ p ∈ outerTable, p.1 < p.2.1 := by
  simp only [outerTable, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq]
  norm_num

end Zeta5Irr
