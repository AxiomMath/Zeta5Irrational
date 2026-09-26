/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Measure.PotGridMono
public import Zeta5Irr.Measure.PotInterval

/-!
# The intervals `J_{j,d,k}` cover `[0, 2]`

The grid `0 = A₀ < A₁ < ⋯ < A₃₅ = 2` cuts `[0, 2]` into the intervals `[Aⱼ, Aⱼ₊₁]`, and for each
`j` the dyadic intervals `[k / 2^d, (k + 1) / 2^d]` with `(j, d, k)` in the refinement table `𝒯`
cover `[0, 1]`: sorted by left endpoint they start at `0`, end at `1`, and each one's right
endpoint is the next one's left endpoint. Rescaling `[0, 1]` onto `[Aⱼ, Aⱼ₊₁]`, every point of
`[0, 2]` lies in some interval `J_{j,d,k}` with `(j, d, k) ∈ 𝒯`.

## Main results

* `Zeta5Irr.exists_mem_potTable_mem_potInterval`: every `t ∈ [0, 2]` lies in some `J_{j,d,k}`
  with `(j, d, k) ∈ 𝒯`.
* `Zeta5Irr.exists_mem_potTable_of_le_of_le`: for each `j < 35` the dyadic intervals attached to
  `j` cover `[0, 1]`.

## Implementation notes

* The finite check is not carried out on the `684` triples of `𝒯` but on its `116` rows
  `(j, d, a, b)`, each standing for the dyadic intervals `k = a, …, b`, whose union is the
  single interval `[a / 2^d, (b + 1) / 2^d]`. All depths satisfy `d ≤ 10`, so every endpoint is
  an integer multiple of `2⁻¹⁰`, and the check is decided on natural numbers: every `j` has a
  row starting at `0` (`Zeta5Irr.potTableBlocks_exists_zero`), and every row not reaching `1`
  is followed by a row of the same `j` starting at its right end
  (`Zeta5Irr.potTableBlocks_chain`). Covering then follows by taking, below a given point, the
  row with the largest left endpoint.
* The step from the grid to its consecutive intervals is the general fact
  `Zeta5Irr.exists_castSucc_le_and_le_succ_of_monotone` about monotone maps on `Fin (n + 2)`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.6: the interval bound and the partition of `[0, 2]`.
-/

@[expose] public section

namespace Zeta5Irr

/-- If `f : Fin (n + 2) → α` is monotone and `f 0 ≤ t ≤ f (n + 1)`, then `t` lies in one of the
consecutive intervals `[f i, f (i + 1)]`. -/
theorem exists_castSucc_le_and_le_succ_of_monotone {α : Type*} [LinearOrder α] {n : ℕ}
    {f : Fin (n + 2) → α} (hf : Monotone f) {t : α} (h₀ : f 0 ≤ t)
    (h₁ : t ≤ f (Fin.last (n + 1))) :
    ∃ i : Fin (n + 1), f i.castSucc ≤ t ∧ t ≤ f i.succ := by
  classical
  set s := Finset.univ.filter fun i => t ≤ f i
  have hs : s.Nonempty := ⟨Fin.last _, by simpa [s] using h₁⟩
  have hmem : t ≤ f (s.min' hs) := by simpa [s] using s.min'_mem hs
  induction h : s.min' hs using Fin.cases with
  | zero => exact ⟨0, h₀, (h ▸ hmem).trans (hf (Fin.zero_le _))⟩
  | succ i =>
    refine ⟨i, le_of_lt ?_, h ▸ hmem⟩
    by_contra hlt
    have := s.min'_le i.castSucc (by simpa [s] using hlt)
    rw [h] at this
    exact absurd this (not_le.2 Fin.castSucc_lt_succ)

/-- For each grid index `j < 35`, some row `(j, d, 0, b)` of the refinement table starts at the
left end `0` of `[0, 1]`. -/
theorem potTableBlocks_exists_zero : ∀ j < 35, ∃ B ∈ potTableBlocks, B.1 = j ∧ B.2.2.1 = 0 := by
  decide +kernel

/-- The chain condition on the rows of the refinement table, measured in units of `2⁻¹⁰`: every
row `(j, d, a, b)` has `d ≤ 10` and `a ≤ b`, and unless its union
`[a / 2^d, (b + 1) / 2^d]` reaches `1`, some row `(j, d', a', b')` starts where it ends,
`a' / 2^d' = (b + 1) / 2^d`. -/
theorem potTableBlocks_chain : ∀ B ∈ potTableBlocks, B.2.1 ≤ 10 ∧ B.2.2.1 ≤ B.2.2.2 ∧
    ((B.2.2.2 + 1) * 2 ^ (10 - B.2.1) < 1024 → ∃ C ∈ potTableBlocks, C.1 = B.1 ∧
      C.2.2.1 * 2 ^ (10 - C.2.1) = (B.2.2.2 + 1) * 2 ^ (10 - B.2.1)) := by
  decide +kernel

set_option maxRecDepth 4000 in
/-- For each grid index `j < 35`, the dyadic intervals `[k / 2^d, (k + 1) / 2^d]` with
`(j, d, k) ∈ 𝒯` cover `[0, 1]`; stated after scaling by `2¹⁰`, so that the interval attached to
`(j, d, k)` is `[k 2^(10 - d), (k + 1) 2^(10 - d)]`. -/
theorem exists_mem_potTable_of_le_of_le {j : ℕ} (hj : j < 35) {x : ℝ} (hx₀ : 0 ≤ x)
    (hx₁ : x ≤ 1024) : ∃ d k, (j, d, k) ∈ potTable ∧ d ≤ 10 ∧
      (k * 2 ^ (10 - d) : ℝ) ≤ x ∧ x ≤ ((k + 1) * 2 ^ (10 - d) : ℝ) := by
  classical
  set S := potTableBlocks.toFinset.filter
    fun B => B.1 = j ∧ ((B.2.2.1 * 2 ^ (10 - B.2.1) : ℕ) : ℝ) ≤ x
  obtain ⟨B₀, hB₀, hB₀j, hB₀a⟩ := potTableBlocks_exists_zero j hj
  have hS : S.Nonempty := ⟨B₀, by simp [S, hB₀, hB₀j, hB₀a, hx₀]⟩
  obtain ⟨⟨j', d, a, b⟩, hBS, hmax⟩ :=
    S.exists_max_image (fun B => B.2.2.1 * 2 ^ (10 - B.2.1)) hS
  simp only [S, Finset.mem_filter, List.mem_toFinset] at hBS
  obtain ⟨hB, rfl, hax⟩ := hBS
  obtain ⟨hd, hab, hchain⟩ := potTableBlocks_chain _ hB
  simp only at hd hab hchain hax
  -- `x` lies below the right end of the block
  have hxb : x ≤ ((b + 1) * 2 ^ (10 - d) : ℕ) := by
    by_contra! hlt
    have hR : (b + 1) * 2 ^ (10 - d) < 1024 := by
      have : (((b + 1) * 2 ^ (10 - d) : ℕ) : ℝ) < 1024 := hlt.trans_le hx₁
      exact_mod_cast this
    obtain ⟨C, hC, hCj, hCa⟩ := hchain hR
    have hCS : C ∈ S := by
      simp only [S, Finset.mem_filter, List.mem_toFinset]
      exact ⟨hC, hCj, by rw [hCa]; exact hlt.le⟩
    have h := hmax C hCS
    simp only at h
    rw [hCa] at h
    have := Nat.le_of_mul_le_mul_right h (by positivity)
    omega
  have hs : (0 : ℝ) < 2 ^ (10 - d) := by positivity
  set y := x / 2 ^ (10 - d) with hy
  have hay : (a : ℝ) ≤ y := by
    rw [hy, le_div_iff₀ hs]; exact_mod_cast hax
  have hyb : y ≤ b + 1 := by
    rw [hy, div_le_iff₀ hs]; exact_mod_cast hxb
  have hy₀ : 0 ≤ y := (Nat.cast_nonneg a).trans hay
  refine ⟨d, min ⌊y⌋₊ b, mem_potTable.2 ⟨a, b, hB, ?_, min_le_right _ _⟩, hd, ?_, ?_⟩
  · exact le_min (Nat.le_floor hay) hab
  · rw [← le_div_iff₀ hs]
    exact (Nat.cast_le.2 (min_le_left _ _)).trans (Nat.floor_le hy₀)
  · rw [← div_le_iff₀ hs]
    rcases le_total ⌊y⌋₊ b with h | h
    · rw [min_eq_left h]; exact (Nat.lt_floor_add_one y).le
    · rw [min_eq_right h]; exact hyb

set_option maxRecDepth 4000 in
/-- **The table intervals cover `[0, 2]`.** For every `t` with `0 ≤ t ≤ 2` there is
`(j, d, k) ∈ 𝒯` with `t ∈ J_{j,d,k}`. -/
@[zeta5irr "lem_pot_partition"]
theorem exists_mem_potTable_mem_potInterval {t : ℝ} (ht₀ : 0 ≤ t) (ht₂ : t ≤ 2) :
    ∃ (j : Fin 35) (d k : ℕ), ((j : ℕ), d, k) ∈ potTable ∧ t ∈ potInterval j d k := by
  have hmono : Monotone fun i => (potGrid i : ℝ) :=
    fun i i' h => Rat.cast_le.2 (strictMono_potGrid.monotone h)
  obtain ⟨j, hj₀, hj₁⟩ := exists_castSucc_le_and_le_succ_of_monotone (n := 34) hmono
    (by simpa using ht₀) (by simpa [show Fin.last 35 = 35 from rfl] using ht₂)
  set A := (potGrid j.castSucc : ℝ)
  set Δ := (potGrid j.succ : ℝ) - A with hΔ
  have hΔ₀ : 0 < Δ := sub_pos.2 (Rat.cast_lt.2 (strictMono_potGrid Fin.castSucc_lt_succ))
  obtain ⟨d, k, hk, hd, hkx, hxk⟩ := exists_mem_potTable_of_le_of_le j.isLt
    (x := 1024 * (t - A) / Δ) (by have := sub_nonneg.2 hj₀; positivity)
    (by rw [div_le_iff₀ hΔ₀]; linarith)
  have h1024 : (2 : ℝ) ^ d * 2 ^ (10 - d) = 1024 := by
    rw [← pow_add, Nat.add_sub_cancel' hd]; norm_num
  have hs : (0 : ℝ) < 2 ^ (10 - d) := by positivity
  have e : A + Δ * (1024 * (t - A) / Δ) / 1024 = t := by field_simp; ring
  refine ⟨j, d, k, hk, mem_potInterval.2 ⟨?_, ?_⟩⟩
  · calc potIntervalLeft j d k = A + Δ * (k * 2 ^ (10 - d)) / 1024 := by
          rw [potIntervalLeft, ← h1024]; field_simp; simp only [Δ, A]; ring
      _ ≤ A + Δ * (1024 * (t - A) / Δ) / 1024 := by gcongr
      _ = t := e
  · calc t = A + Δ * (1024 * (t - A) / Δ) / 1024 := e.symm
      _ ≤ A + Δ * ((k + 1) * 2 ^ (10 - d)) / 1024 := by gcongr
      _ = potIntervalRight j d k := by
          rw [potIntervalRight, ← h1024]; field_simp; simp only [Δ, A]; ring
end Zeta5Irr
