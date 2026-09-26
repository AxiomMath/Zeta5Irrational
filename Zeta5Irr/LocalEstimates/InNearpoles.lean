/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.InMstar
public import Zeta5Irr.LocalEstimates.EllA

/-!
# Counting the nonzero integers `|r| ≤ A` in a residue class `±s`

Let `p` be an odd prime, `A ≥ 0`, `1 ≤ s ≤ m° = (p - 1) / 2` and `σ ∈ {s, p - s}`. Then the
number of integers `r` with `0 < |r| ≤ A` and `r ≡ σ (mod p)` is `ℓ_A(s)`.

Indeed, `r ↦ |r|` maps this set into `{1 ≤ j ≤ A : j ≡ ±s}`, the set counted by `ℓ_A(s)`, since
`σ ≡ ±s`. It is surjective: a `j` in the target is congruent to `σ` or to `-σ`, and then `j` or
`-j` is a preimage. It is injective: if `r` and `-r` both lie in the source then `2σ ≡ 0`, hence
`p ∣ 2s`, which is impossible as `2 ≤ 2s ≤ p - 1`.

## Main results

* `Zeta5Irr.card_filter_modEq_erase_Icc_eq_ellA`: the count equals `ℓ_A(s)` whenever
  `σ ≡ ±s (mod p)` and `p ∤ 2s`.
* `Zeta5Irr.card_filter_modEq_erase_Icc_eq_ellA_of_le_mStar`: the statement of the source, for
  `1 ≤ s ≤ m°` and `σ ∈ {s, p - s}`.

## Implementation notes

* The set `{r ∈ ℤ : 0 < |r| ≤ A}` is written `(Finset.Icc (-A) A).erase 0`.
* The source assumes `p` is an odd prime. Neither primality nor oddness is used: the bounds
  `1 ≤ s ≤ (p - 1) / 2` alone force `0 < 2s < p`, hence `p ∤ 2s`, which is all the argument needs.
  The general form only asks that `σ ≡ ±s (mod p)` and `p ∤ 2s`.
* The proof uses the single map `r ↦ |r|` in place of the source's split into signs.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.5 (The inner range: the entry valuations).
-/

@[expose] public section

namespace Zeta5Irr

open Finset

/-- If `σ ≡ ±s (mod p)` and `p ∤ 2s`, the number of integers `r` with `0 < |r| ≤ A` and
`r ≡ σ (mod p)` equals `ℓ_A(s)`. -/
theorem card_filter_modEq_erase_Icc_eq_ellA {p A : ℕ} {s σ : ℤ}
    (hσ : σ ≡ s [ZMOD p] ∨ σ ≡ -s [ZMOD p]) (hs : ¬ (p : ℤ) ∣ 2 * s) :
    #{r ∈ (Icc (-(A : ℤ)) A).erase 0 | r ≡ σ [ZMOD p]} = ellA p A s := by
  unfold ellA
  refine card_bij (fun r _ => |r|) ?_ ?_ ?_
  · intro r hr
    simp only [mem_filter, mem_erase, mem_Icc] at hr
    obtain ⟨⟨hr0, hlo, hhi⟩, hrσ⟩ := hr
    simp only [mem_filter, mem_Icc]
    rcases le_or_gt 0 r with h | h
    · rw [abs_of_nonneg h]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      rcases hσ with h' | h'
      exacts [.inl (hrσ.trans h'), .inr (hrσ.trans h')]
    · rw [abs_of_neg h]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      rcases hσ with h' | h'
      · exact .inr (hrσ.trans h').neg
      · exact .inl (by simpa using (hrσ.trans h').neg)
  · intro r₁ hr₁ r₂ hr₂ h
    simp only [mem_filter, mem_erase, mem_Icc] at hr₁ hr₂
    rcases abs_eq_abs.mp h with h | h
    · exact h
    · exfalso
      apply hs
      have h₁ := hr₁.2
      have h₂ := hr₂.2
      rw [h] at h₁
      have h2σ : (p : ℤ) ∣ 2 * σ := by
        have := (h₂.add h₁).dvd
        simpa [two_mul] using this
      rcases hσ with h' | h'
      · have := dvd_add h2σ (h'.mul_left 2).dvd
        convert this using 1
        ring
      · have := dvd_add h2σ (h'.mul_left 2).dvd
        rw [← dvd_neg]
        convert this using 1
        ring
  · intro j hj
    simp only [mem_filter, mem_Icc] at hj
    obtain ⟨⟨h1, hA⟩, hj⟩ := hj
    have key : j ≡ σ [ZMOD p] ∨ -j ≡ σ [ZMOD p] := by
      rcases hσ with h' | h' <;> rcases hj with h | h
      · exact .inl (h.trans h'.symm)
      · exact .inr ((by simpa using h.neg : -j ≡ s [ZMOD p]).trans h'.symm)
      · exact .inr (h.neg.trans h'.symm)
      · exact .inl (h.trans h'.symm)
    rcases key with h | h
    · refine ⟨j, ?_, abs_of_pos (by omega)⟩
      simp only [mem_filter, mem_erase, mem_Icc]
      exact ⟨⟨by omega, by omega, by omega⟩, h⟩
    · refine ⟨-j, ?_, by rw [abs_neg, abs_of_pos (by omega)]⟩
      simp only [mem_filter, mem_erase, mem_Icc]
      exact ⟨⟨by omega, by omega, by omega⟩, h⟩

/-- Let `1 ≤ s ≤ m° = (p - 1) / 2` and `σ ∈ {s, p - s}`. Then the number of integers `r` with
`0 < |r| ≤ A` and `r ≡ σ (mod p)` equals `ℓ_A(s)`. -/
@[zeta5irr "lem_in_nearpoles"]
theorem card_filter_modEq_erase_Icc_eq_ellA_of_le_mStar {p A s : ℕ} {σ : ℤ} (hs₁ : 1 ≤ s)
    (hs : s ≤ mStar p) (hσ : σ = s ∨ σ = p - s) :
    #{r ∈ (Icc (-(A : ℤ)) A).erase 0 | r ≡ σ [ZMOD p]} = ellA p A s := by
  refine card_filter_modEq_erase_Icc_eq_ellA ?_ ?_
  · rcases hσ with rfl | rfl
    · exact .inl rfl
    · exact .inr (Int.modEq_iff_dvd.mpr ⟨-1, by ring⟩)
  · have h2 : 2 * s < p := by rw [mStar] at hs; omega
    intro hdvd
    have hle := Int.le_of_dvd (by omega) hdvd
    omega

end Zeta5Irr
