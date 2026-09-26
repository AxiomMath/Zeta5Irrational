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

/-!
# Piecewise continuous functions on a compact interval

Let `u < v` be reals. A function `f` on `[u, v]` is *piecewise continuous* if it is bounded on
`[u, v]` and there is a partition `u = u₀ < u₁ < ⋯ < u_r = v` with `r ≥ 1` such that, on each
open piece `(u_{k-1}, u_k)`, `f` agrees with a function continuous on the closed piece
`[u_{k-1}, u_k]`.

## Main definitions

* `Zeta5Irr.PiecewiseContinuousOn`: `f` is piecewise continuous on `[u, v]`.

## Main results

* `Zeta5Irr.exists_partition_notMem_Ioo`: a partition of `[u, v]` avoiding a finite set in the
  interiors of its pieces.
* `Zeta5Irr.PiecewiseContinuousOn.lt`: a piecewise continuous function lives on a
  nondegenerate interval, `u < v`.
* `Zeta5Irr.PiecewiseContinuousOn.mul_comp_inv`: `y ↦ y f(1/y)` is piecewise continuous on
  `[1/v, 1/u]` if `f` is on `[u, v]`, `0 < u`.
* `Zeta5Irr.PiecewiseContinuousOn.exists_bound`: a piecewise continuous function is bounded on
  `[u, v]`.
* `Zeta5Irr.PiecewiseContinuousOn.intervalIntegrable`: a piecewise continuous function is
  interval integrable on `[u, v]`.

## Implementation notes

* The function is a total function `ℝ → ℝ`; only its values on `[u, v]` matter.
* The partition is a strictly monotone map `Fin (r + 1) → ℝ`, and the `k`-th piece (for
  `k : Fin r`) is `[p k.castSucc, p k.succ]`.
* The condition `u < v` of the source is not a hypothesis: it follows from the existence of a
  strictly monotone partition with `r ≥ 1`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.6: piecewise continuity.
-/

@[expose] public section

namespace Zeta5Irr

open Set Filter MeasureTheory

/-- A function interval integrable on each piece `[q (k - 1), q k]` of `q : Fin (r + 1) → ℝ` is
interval integrable on `[q 0, q r]`. -/
theorem intervalIntegrable_of_fin_pieces {f : ℝ → ℝ} {r : ℕ} (q : Fin (r + 1) → ℝ)
    (h : ∀ k : Fin r, IntervalIntegrable f volume (q k.castSucc) (q k.succ)) :
    IntervalIntegrable f volume (q 0) (q (Fin.last r)) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have h1 := ih (q ∘ Fin.castSucc) fun k => by simpa using h k.castSucc
    have h2 := h (Fin.last r)
    simp only [Function.comp_apply, Fin.castSucc_zero] at h1
    rw [Fin.succ_last] at h2
    exact h1.trans h2

/-- No element of a finite linearly ordered set `s` lies strictly between two consecutive
terms of its increasing enumeration `s.orderEmbOfFin`. -/
theorem notMem_Ioo_orderEmbOfFin {α : Type*} [LinearOrder α] {s : Finset α} {k : ℕ}
    (h : s.card = k) {i : ℕ} (hi : i + 1 < k) {t : α} (ht : t ∈ s) :
    t ∉ Ioo (s.orderEmbOfFin h ⟨i, by omega⟩) (s.orderEmbOfFin h ⟨i + 1, hi⟩) := by
  rintro ⟨h₁, h₂⟩
  rw [← Finset.mem_coe, ← Finset.range_orderEmbOfFin s h] at ht
  obtain ⟨j, rfl⟩ := ht
  have h₁' := (s.orderEmbOfFin h).lt_iff_lt.1 h₁
  have h₂' := (s.orderEmbOfFin h).lt_iff_lt.1 h₂
  rw [Fin.lt_def] at h₁' h₂'
  simp only at h₁' h₂'
  omega

/-- For `u < v` and a finite set `s`, there is a partition `u = z 0 < z 1 < ⋯ < z r = v` with
`1 ≤ r ≤ #s + 1` such that no point of `s` lies strictly inside a piece: sort the points of `s`
in `(u, v)` together with `u` and `v`. -/
theorem exists_partition_notMem_Ioo {u v : ℝ} (huv : u < v) (s : Finset ℝ) :
    ∃ (r : ℕ) (z : Fin (r + 1) → ℝ), 0 < r ∧ r ≤ s.card + 1 ∧ StrictMono z ∧ z 0 = u ∧
      z (Fin.last r) = v ∧ ∀ k : Fin r, ∀ t ∈ s, t ∉ Ioo (z k.castSucc) (z k.succ) := by
  classical
  set s' : Finset ℝ := insert u (insert v (s.filter (· ∈ Ioo u v)))
  have hus : u ∈ s' := Finset.mem_insert_self _ _
  have hvs : v ∈ s' := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hs : ∀ x ∈ s', x ∈ Icc u v := by
    intro x hx
    simp only [s', Finset.mem_insert, Finset.mem_filter] at hx
    rcases hx with rfl | rfl | ⟨-, hx⟩
    exacts [⟨le_rfl, huv.le⟩, ⟨huv.le, le_rfl⟩, Ioo_subset_Icc_self hx]
  have hcard : 2 ≤ s'.card := by
    have : ({u, v} : Finset ℝ) ⊆ s' := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      exacts [hus, hvs]
    simpa [Finset.card_pair huv.ne] using Finset.card_le_card this
  have hcard' : s'.card ≤ s.card + 2 :=
    (Finset.card_insert_le _ _).trans (Nat.add_le_add_right ((Finset.card_insert_le _ _).trans
      (Nat.add_le_add_right (Finset.card_filter_le s _) 1)) 1)
  obtain ⟨r, hr⟩ : ∃ r, s'.card = r + 1 := ⟨s'.card - 1, by omega⟩
  have hmem : ∀ i, s'.orderEmbOfFin hr i ∈ Icc u v := fun i => hs _ (s'.orderEmbOfFin_mem hr i)
  refine ⟨r, s'.orderEmbOfFin hr, by omega, by omega, (s'.orderEmbOfFin hr).strictMono, ?_, ?_,
    fun k t ht htk => ?_⟩
  · rw [show (0 : Fin (r + 1)) = ⟨0, by omega⟩ from rfl, Finset.orderEmbOfFin_zero hr (by omega)]
    exact le_antisymm (s'.min'_le _ hus) (hs _ (s'.min'_mem _)).1
  · rw [show Fin.last r = ⟨r + 1 - 1, by omega⟩ from Fin.ext (by simp),
      Finset.orderEmbOfFin_last hr (by omega)]
    exact le_antisymm (hs _ (s'.max'_mem _)).2 (s'.le_max' _ hvs)
  · refine notMem_Ioo_orderEmbOfFin hr (i := k) (by omega) ?_ htk
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_filter.2
      ⟨ht, (hmem _).1.trans_lt htk.1, htk.2.trans_le (hmem _).2⟩))

/-- A function `f` is *piecewise continuous* on `[u, v]` if it is bounded on `[u, v]` and there
is a partition `u = p 0 < p 1 < ⋯ < p r = v`, `r ≥ 1`, such that on each open piece
`(p (k - 1), p k)` the function `f` agrees with a function continuous on the closed piece
`[p (k - 1), p k]`. -/
@[zeta5irr "def_norm_pwc"]
def PiecewiseContinuousOn (f : ℝ → ℝ) (u v : ℝ) : Prop :=
  ∃ (r : ℕ) (p : Fin (r + 1) → ℝ), 0 < r ∧ StrictMono p ∧ p 0 = u ∧ p (Fin.last r) = v ∧
    (∃ C, ∀ t ∈ Icc u v, |f t| ≤ C) ∧
    ∀ k : Fin r, ∃ g : ℝ → ℝ, ContinuousOn g (Icc (p k.castSucc) (p k.succ)) ∧
      EqOn f g (Ioo (p k.castSucc) (p k.succ))

namespace PiecewiseContinuousOn

variable {f : ℝ → ℝ} {u v : ℝ}

/-- A piecewise continuous function is defined on a nondegenerate interval: `u < v`. -/
theorem lt (hf : PiecewiseContinuousOn f u v) : u < v := by
  obtain ⟨r, p, hr, hp, h0, hr', -⟩ := hf
  rw [← h0, ← hr']
  exact hp (Fin.pos_iff_ne_zero.mpr (by simp [Fin.ext_iff]; omega))

/-- A piecewise continuous function is bounded on `[u, v]`. -/
theorem exists_bound (hf : PiecewiseContinuousOn f u v) : ∃ C, ∀ t ∈ Icc u v, |f t| ≤ C :=
  hf.choose_spec.choose_spec.2.2.2.2.1

/-- A piecewise continuous function on `[u, v]` is interval integrable there. -/
theorem intervalIntegrable (hf : PiecewiseContinuousOn f u v) :
    IntervalIntegrable f volume u v := by
  obtain ⟨r, p, -, hp, rfl, rfl, -, hg⟩ := hf
  refine intervalIntegrable_of_fin_pieces p fun k => ?_
  obtain ⟨g, hgc, hfg⟩ := hg k
  have hlt := hp k.castSucc_lt_succ
  refine (hgc.intervalIntegrable_of_Icc hlt.le).congr_ae ?_
  rw [uIoc_of_le hlt.le, EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [Measure.ae_ne volume (p k.succ)] with x hx hxI
  exact (hfg ⟨hxI.1, lt_of_le_of_ne hxI.2 hx⟩).symm

/-- If `f` is piecewise continuous on `[u, v]` with `0 < u`, then `y ↦ y f(1/y)` is piecewise
continuous on `[1/v, 1/u]`, with the reversed and inverted partition. -/
theorem mul_comp_inv (hu : 0 < u) (hf : PiecewiseContinuousOn f u v) :
    PiecewiseContinuousOn (fun y => y * f y⁻¹) v⁻¹ u⁻¹ := by
  have huv := hf.lt
  obtain ⟨r, p, hr, hp, h0, hr', ⟨C, hC⟩, hg⟩ := hf
  have hpos : ∀ i, 0 < p i := fun i => hu.trans_le (h0 ▸ hp.monotone (Fin.zero_le i))
  -- `y ↦ y⁻¹` maps `[b⁻¹, a⁻¹]` onto `[a, b]` and `(b⁻¹, a⁻¹)` onto `(a, b)` for `0 < a`
  have hIcc : ∀ {a b y : ℝ}, 0 < a → a ≤ b → y ∈ Icc b⁻¹ a⁻¹ → 0 < y ∧ y⁻¹ ∈ Icc a b :=
    fun {a b y} ha hab hy => by
      have hy0 : 0 < y := (inv_pos.2 (ha.trans_le hab)).trans_le hy.1
      exact ⟨hy0, (le_inv_comm₀ ha hy0).2 hy.2, (inv_le_comm₀ hy0 (ha.trans_le hab)).2 hy.1⟩
  have hIoo : ∀ {a b y : ℝ}, 0 < a → a ≤ b → y ∈ Ioo b⁻¹ a⁻¹ → y⁻¹ ∈ Ioo a b :=
    fun {a b y} ha hab hy => by
      have hy0 : 0 < y := (inv_pos.2 (ha.trans_le hab)).trans hy.1
      exact ⟨(lt_inv_comm₀ ha hy0).2 hy.2, (inv_lt_comm₀ hy0 (ha.trans_le hab)).2 hy.1⟩
  refine ⟨r, fun i => (p i.rev)⁻¹, hr, fun i j hij => inv_strictAnti₀ (hpos _)
    (hp (Fin.rev_lt_rev.2 hij)), by simp [hr'], by simp [h0], ⟨u⁻¹ * C, fun t ht => ?_⟩,
    fun k => ?_⟩
  · obtain ⟨ht0, ht⟩ := hIcc hu huv.le ht
    rw [abs_mul, abs_of_pos ht0]
    exact mul_le_mul ((le_inv_comm₀ hu ht0).1 ht.1) (hC _ ht) (abs_nonneg _) (inv_pos.2 hu).le
  obtain ⟨g, hgc, hfg⟩ := hg k.rev
  have hlt := hp k.rev.castSucc_lt_succ
  refine ⟨fun y => y * g y⁻¹, ?_, fun y hy => ?_⟩
  · simp only [Fin.rev_castSucc, Fin.rev_succ]
    refine continuousOn_id.mul (hgc.comp (continuousOn_inv₀.mono fun y hy => ?_) fun y hy => ?_)
    · exact (hIcc (hpos _) hlt.le hy).1.ne'
    · exact (hIcc (hpos _) hlt.le hy).2
  · simp only [Fin.rev_castSucc, Fin.rev_succ] at hy
    simp only [hfg (hIoo (hpos _) hlt.le hy)]

end PiecewiseContinuousOn

end Zeta5Irr
