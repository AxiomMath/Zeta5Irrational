/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.La

/-!
# The class vanishing orders `θ_{a,i}(s)`

For an odd prime `p`, an integer `M ≥ 40`, indices `0 ≤ a, s ≤ m°` and an integer
`0 ≤ i < L_a`, the class vanishing order is
`θ_{a,i}(s) = i` if `s = a`, and `θ_{a,i}(s) = L_s` if `s ≠ a`,
where `L_0 = 4 M + 10` is the reserved zero-class dimension and, for `1 ≤ s ≤ m°`,
`L_s = T - b_s + ε_s` is the class dimension. It is the order of vanishing at `t = -s²` of the
row polynomial `Ψ_{a,i}`.

## Main definitions

* `Zeta5Irr.classVanishingOrder`: the class vanishing order `θ_{a,i}(s)`.

## Main results

* `Zeta5Irr.classVanishingOrder_self`: `θ_{a,i}(a) = i`.
* `Zeta5Irr.classVanishingOrder_of_ne`: `θ_{a,i}(s) = L_s` for `s ≠ a`.
* `Zeta5Irr.classVanishingOrder_le`: `θ_{a,i}(s) ≤ L_s` when `i ≤ L_a`.

## Implementation notes

* The class dimensions `L_s` with `s ≥ 1` are integers (the common dimension `T` is an
  integer), so `L_s` and `θ_{a,i}(s)` are integer valued. The zero-class dimension `L₀` is
  cast from `ℕ`.
* The integers `K = 40 n`, `h = 37 n` and `N = 3 n` are functions of `n`, so `θ` takes `n`
  as an argument along with `p` and `M`.
* The hypotheses that `p` is an odd prime, `M ≥ 40`, `a, s ≤ m°` and `i < L_a` are not needed
  to define `θ_{a,i}(s)`; they are carried by the lemmas which use them.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.4 (The inner range: the distributing basis).
-/

@[expose] public section

namespace Zeta5Irr

/-- The class vanishing order `θ_{a,i}(s)`: it equals `i` if `s = a` and `L_s` otherwise. -/
@[zeta5irr "def_in_ord"]
def classVanishingOrder (n p M a i s : ℕ) : ℤ :=
  if s = a then i else classDimAt n p M s

/-- `θ_{a,i}(a) = i`. -/
@[simp]
theorem classVanishingOrder_self (n p M a i : ℕ) : classVanishingOrder n p M a i a = i := by
  simp [classVanishingOrder]

/-- `θ_{a,i}(s) = L_s` for `s ≠ a`. -/
theorem classVanishingOrder_of_ne (n p M a i : ℕ) {s : ℕ} (hs : s ≠ a) :
    classVanishingOrder n p M a i s = classDimAt n p M s := by
  simp [classVanishingOrder, hs]

/-- If `i ≤ L_a` then `θ_{a,i}(s) ≤ L_s` for every `s`. -/
theorem classVanishingOrder_le {n p M a i : ℕ} (hi : (i : ℤ) ≤ classDimAt n p M a) (s : ℕ) :
    classVanishingOrder n p M a i s ≤ classDimAt n p M s := by
  by_cases hs : s = a
  · subst hs
    simpa using hi
  · simp [classVanishingOrder_of_ne _ _ _ _ _ hs]

end Zeta5Irr
