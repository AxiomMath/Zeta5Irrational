/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.GammaIn
public import Zeta5Irr.LocalEstimates.LaNonneg
public import Zeta5Irr.PrimeSum.NormGamhatLip
public import Zeta5Irr.PrimeSum.NormStepRiemann
public import Zeta5Irr.PrimeSum.NormBlockSum
public import Zeta5Irr.PrimeSum.NormAllocNear
public import Zeta5Irr.PrimeSum.NormZeroblock
public import Zeta5Irr.PrimeSum.NormPwc

/-!
# The inner asymptotics

Let `M ≥ 40` be an integer, let `K = 40 n` with `K ≥ 200 M²`, and let `p` be an odd prime with
`K / M < p ≤ K / 3`. Write `x = K / p`. Then the inner exponent is approximated by `p Γ(x)`:
`|γ_p^in - p Γ(K / p)| ≤ 10⁴ M²`.

The proof compares `γ_p^in` with `p Γ̂(x, ϖ)`, where `ϖ = ϖ_p(K, M)` is the allocation density,
so that `T = ⌊2ϖ⌋` and `E = m° {2ϖ}`. The zero block contributes at most `100 M²`. For the
blocks `1 ≤ a ≤ m°`, the block sums and the exact contribution of the extras reduce the sum to
`∑_a G(a/p) + E (2T - q̃(x) - 5) + E - min(E, 𝒜_p(K))`, where
`G(z) = (T - b(x, z)) (T + b(x, z) - ℓ(x, z) - 5)`. Since `ℓ(x, ·)` and `ℓ(α x, ·)` are constant
on `(0, 1/2)` off one point each, `∑_a G(a/p)` is within `O(M²)` of `p ∫₀^{1/2} G`, and likewise
`𝒜_p(K) = ∑_a (ℓ(x, a/p) - q̃(x))` is within `O(1)` of `p ñ(x)`. This gives
`|γ_p^in - p Γ̂(x, ϖ)| = O(M²)`. Finally `|ϖ - H x| ≤ 12 M / p`, the Lipschitz bound for
`Γ̂(x, ·)` and `Γ̂(x, H x) = Γ(x)` give `p |Γ̂(x, ϖ) - Γ(x)| ≤ 144 M²`.

## Main results

* `Zeta5Irr.ell_eq_ell_of_notMem`: `ℓ(y, ·)` is constant on every interval in `(0, 1/2)`
  avoiding the break point of `S(y)`.
* `Zeta5Irr.abs_sum_sub_integral_le_of_eq_of_notMem`: the Riemann sum estimate for a bounded
  function which is constant between the points of a finite set.
* `Zeta5Irr.sum_ellA_sub_basePoleCount`: `∑_{a=1}^{m°} (ℓ_K(a) - q̃(K/p)) = 𝒜_p(K)`.
* `Zeta5Irr.abs_innerExponent_sub_le`: `|γ_p^in - p Γ(K/p)| ≤ 10⁴ M²`.

## Implementation notes

* The source assumes `p` prime. Only its oddness is used (through `m° = (p - 1) / 2`), so the
  main result assumes `Odd p`; a prime `p > K / M ≥ 200 M` is odd.
* The hypotheses `K / M < p ≤ K / 3` are stated in `ℕ` as `K < M p` and `3 p ≤ K`, and
  `K ∈ 40 ℤ_{>0}` is `K = 40 n` with `n > 0` forced by `K ≥ 200 M²`.
* The step estimate of the source, stated for a partition `0 = z₀ < ⋯ < z_r = 1/2`, is applied
  through `Zeta5Irr.abs_sum_sub_integral_le_of_eq_of_notMem`, which builds the partition from
  the break points, so that coincident or extreme break points need no case analysis. The
  intermediate constants are cruder than the source's; the final constant `10⁴` is the
  source's.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.3 (The inner asymptotics).
-/

@[expose] public section

namespace Zeta5Irr

open Finset MeasureTheory

/-- On `(0, 1/2)`, the pole count `ℓ(y, ·)` is constant on every interval `[u, v]` avoiding the
break point of `S(y)`, which is `{y}` if `{y} < 1/2` and `1 - {y}` otherwise. -/
theorem ell_eq_ell_of_notMem (y : ℝ) {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) (hv : v < 1 / 2)
    (h : (if Int.fract y < 1 / 2 then Int.fract y else 1 - Int.fract y) ∉ Set.Icc u v) :
    ell y u = ell y v := by
  rw [ell_eq_floor_two_mul_add_indicator y hu (huv.trans_lt hv),
    ell_eq_floor_two_mul_add_indicator y (hu.trans_le huv) hv]
  have key : u ∈ normUpperSet y ↔ v ∈ normUpperSet y := by
    rw [mem_normUpperSet, mem_normUpperSet]
    split_ifs at h with hf
    · simp only [Set.mem_Icc, not_and_or, not_le] at h
      simp only [hf, true_and, not_le.2 hf, false_and, or_false]
      rcases h with h | h
      · constructor <;> rintro ⟨-, h'⟩ <;> linarith
      · exact ⟨fun _ => ⟨by linarith, h.le⟩, fun _ => ⟨hu, by linarith⟩⟩
    · simp only [Set.mem_Icc, not_and_or, not_le] at h
      simp only [hf, false_and, not_lt.1 hf, true_and, false_or]
      rcases h with h | h
      · exact ⟨fun _ => ⟨by linarith, hv⟩, fun _ => ⟨h.le, by linarith⟩⟩
      · constructor <;> rintro ⟨h', -⟩ <;> linarith
  by_cases hu' : u ∈ normUpperSet y
  · rw [Set.indicator_of_mem hu', Set.indicator_of_mem (key.1 hu'), Pi.one_apply, Pi.one_apply]
  · rw [Set.indicator_of_notMem hu', Set.indicator_of_notMem (mt key.2 hu')]

/-- **Riemann sums of functions constant between the points of a finite set.** Let `s` be a
finite set of reals and let `G` be bounded by `C ≥ 0` on `(0, 1/2)` and constant on every
interval `[u, v] ⊆ (0, 1/2)` containing no point of `s`. Then
`|∑_{a=1}^{(p-1)/2} G(a/p) - p ∫_0^{1/2} G| ≤ 2 (#s + 1) C`. -/
theorem abs_sum_sub_integral_le_of_eq_of_notMem (p : ℕ) (s : Finset ℝ) {C : ℝ} (hC : 0 ≤ C)
    {G : ℝ → ℝ}
    (hG : ∀ u v, 0 < u → u ≤ v → v < 1 / 2 → (∀ t ∈ s, t ∉ Set.Icc u v) → G u = G v)
    (hGC : ∀ x ∈ Set.Ioo (0 : ℝ) (1 / 2), |G x| ≤ C) :
    |∑ a ∈ Icc 1 ((p - 1) / 2), G (a / p) - p * ∫ x in (0 : ℝ)..1 / 2, G x| ≤
      2 * (#s + 1) * C := by
  obtain ⟨r, z, -, hrs, hz, hz0, hzr, hzs⟩ :=
    exists_partition_notMem_Ioo (show (0 : ℝ) < 1 / 2 by norm_num) s
  have hzmem : ∀ j, z j ∈ Set.Icc (0 : ℝ) (1 / 2) := fun j =>
    ⟨hz0 ▸ hz.monotone (Fin.zero_le j), hzr ▸ hz.monotone (Fin.le_last j)⟩
  have hG' : ∀ k : Fin r, ∀ x ∈ Set.Ioo (z k.castSucc) (z k.succ),
      G x = G ((z k.castSucc + z k.succ) / 2) := by
    intro k x hx
    have key : ∀ u v, z k.castSucc < u → u ≤ v → v < z k.succ → G u = G v := by
      intro u v hu huv hv
      exact hG u v ((hzmem _).1.trans_lt hu) huv (hv.trans_le (hzmem _).2) fun t ht htuv =>
        hzs k t ht ⟨hu.trans_le htuv.1, htuv.2.trans_lt hv⟩
    rcases le_total x ((z k.castSucc + z k.succ) / 2) with h | h
    · exact key _ _ hx.1 h (by linarith [hx.2, hx.1])
    · exact (key _ _ (by linarith [hx.2, hx.1]) h hx.2).symm
  have hmain := abs_sum_step_sub_integral_le p r z hz hz0 hzr _ hC hG' hGC
  refine hmain.trans (mul_le_mul_of_nonneg_right ?_ hC)
  have : (r : ℝ) ≤ #s + 1 := by exact_mod_cast hrs
  linarith

/-- Summed over `1 ≤ a ≤ m°`, the excess `ℓ_K(a) - q̃(K/p)` of the pole count over the base
count is the number `𝒜_p(K)` of large classes. -/
theorem sum_ellA_sub_basePoleCount (K p : ℕ) :
    ∑ a ∈ Icc 1 (mStar p), ((ellA p K a : ℝ) - basePoleCount ((K : ℝ) / p)) =
      largeClassCount K p := by
  rw [largeClassCount_eq_card_nat, card_filter, basePoleCount_natCast_div]
  push_cast
  refine sum_congr rfl fun a ha => ?_
  have ha := mem_Icc.1 ha
  rcases ellA_eq_or_eq_add_one (K := K) ha.1 ha.2 with h | h <;> simp [h]

/-- For `1 ≤ a ≤ m°`, the pole count `ℓ_A(a)` is `ℓ(A / p, a / p)`. -/
theorem ellA_eq_ell_of_mem_Icc {p a : ℕ} (A : ℕ) (ha : a ∈ Icc 1 (mStar p)) :
    (ellA p A a : ℝ) = ell ((A : ℝ) / p) ((a : ℝ) / p) := by
  have ha := mem_Icc.1 ha
  have hap : 2 * (a : ℤ) < p := by rw [mStar_def] at ha; omega
  simpa using congrArg (Int.cast : ℤ → ℝ)
    (ellA_eq_ell_div (p := p) (A := A) (a := (a : ℤ)) (by omega) hap)

/-- The number `𝒜_p(K)` of large classes is within `8` of `p ñ(K / p)`. -/
theorem abs_largeClassCount_sub_le (K p : ℕ) :
    |(largeClassCount K p : ℝ) - p * baseHalfFract ((K : ℝ) / p)| ≤ 8 := by
  set x : ℝ := (K : ℝ) / p
  have hA : ∑ a ∈ Icc 1 ((p - 1) / 2), ((ell x (a / p) : ℝ) - basePoleCount x) =
      largeClassCount K p := by
    rw [← sum_ellA_sub_basePoleCount, ← mStar_def]
    exact sum_congr rfl fun a ha => by rw [ellA_eq_ell_of_mem_Icc _ ha]
  have hint : ∫ z in (0 : ℝ)..1 / 2, ((ell x z : ℝ) - basePoleCount x) = baseHalfFract x := by
    rw [intervalIntegral.integral_sub (intervalIntegrable_ell_right x 0 (1 / 2))
      intervalIntegrable_const, integral_ell_right, intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  have h := abs_sum_sub_integral_le_of_eq_of_notMem p
    {if Int.fract x < 1 / 2 then Int.fract x else 1 - Int.fract x} (C := 2) (by norm_num)
    (G := fun z => (ell x z : ℝ) - basePoleCount x)
    (fun u v hu huv hv hs => by rw [ell_eq_ell_of_notMem x hu huv hv (hs _ (mem_singleton_self _))])
    fun z _ => abs_le.2 ⟨by linarith [lt_ell x z, basePoleCount_le x],
      by linarith [ell_le x z, sub_one_lt_basePoleCount x]⟩
  rw [hA, hint, card_singleton] at h
  norm_num at h
  exact h

/-- For `0 ≤ T ≤ 3 M` and `0 ≤ x ≤ M`, the integrand of `Γ̂` satisfies
`|(T - b(x, z)) (T + b(x, z) - ℓ(x, z) - 5)| ≤ 32 M²`. -/
theorem abs_weightedPoleCount_bracket_le {x T M : ℝ} (z : ℝ) (hT1 : 0 ≤ T) (hT2 : T ≤ 3 * M)
    (hx : 0 ≤ x) (hxM : x ≤ M) (hM : 3 ≤ M) :
    |(T - weightedPoleCount x z) * (T + weightedPoleCount x z - ell x z - 5)| ≤ 32 * M ^ 2 := by
  have hα : (innerRatio : ℝ) = 3 / 40 := by norm_num [innerRatio]
  have hl₁ := lt_ell x z
  have hl₂ := ell_le x z
  have hw₁ := lt_ell ((innerRatio : ℝ) * x) z
  have hw₂ := ell_le ((innerRatio : ℝ) * x) z
  rw [weightedPoleCount_def, abs_mul]
  rw [hα] at hw₁ hw₂ ⊢
  calc _ ≤ (4 * M) * (8 * M) := mul_le_mul (abs_le.2 ⟨by linarith, by linarith⟩)
        (abs_le.2 ⟨by linarith, by linarith⟩) (abs_nonneg _) (by linarith)
    _ = 32 * M ^ 2 := by ring

/-- For `0 ≤ T ≤ 3 M` and `0 ≤ x ≤ M`, the Riemann sum of the integrand of `Γ̂` over the points
`a / p`, `1 ≤ a ≤ (p - 1) / 2`, is within `192 M²` of `p` times its integral over `(0, 1/2)`. -/
theorem abs_sum_bracket_sub_integral_le (p : ℕ) {x T M : ℝ} (hT1 : 0 ≤ T) (hT2 : T ≤ 3 * M)
    (hx : 0 ≤ x) (hxM : x ≤ M) (hM : 3 ≤ M) :
    |∑ a ∈ Icc 1 ((p - 1) / 2), (T - weightedPoleCount x (a / p)) *
        (T + weightedPoleCount x (a / p) - ell x (a / p) - 5) -
      p * ∫ z in (0 : ℝ)..1 / 2,
        (T - weightedPoleCount x z) * (T + weightedPoleCount x z - ell x z - 5)| ≤
      192 * M ^ 2 := by
  set bp : ℝ → ℝ := fun y => if Int.fract y < 1 / 2 then Int.fract y else 1 - Int.fract y
  have hcard : (#({bp x, bp ((innerRatio : ℝ) * x)} : Finset ℝ) : ℝ) ≤ 2 := by
    exact_mod_cast card_le_two
  refine (abs_sum_sub_integral_le_of_eq_of_notMem p {bp x, bp ((innerRatio : ℝ) * x)}
    (by positivity)
    (G := fun z => (T - weightedPoleCount x z) * (T + weightedPoleCount x z - ell x z - 5))
    (fun u v hu huv hv hs => ?_)
    fun z _ => abs_weightedPoleCount_bracket_le z hT1 hT2 hx hxM hM).trans ?_
  · simp only [weightedPoleCount_def]
    rw [ell_eq_ell_of_notMem x hu huv hv (hs _ (mem_insert_self _ _)),
      ell_eq_ell_of_notMem _ hu huv hv (hs _ (mem_insert_of_mem (mem_singleton_self _)))]
  · calc _ ≤ (2 * (2 + 1) : ℝ) * (32 * M ^ 2) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 192 * M ^ 2 := by ring

/-- The blocks `1 ≤ a ≤ m°` with the common dimension `T`, summed, are within `192 M²` of
`p ∫₀^{1/2} (T - b(x, z)) (T + b(x, z) - ℓ(x, z) - 5) dz` for `x = K / p`. -/
theorem abs_sum_innerClassOrder_bracket_sub_integral_le (n : ℕ) {p : ℕ} {T M : ℝ}
    (hT1 : 0 ≤ T) (hT2 : T ≤ 3 * M) (hxM : (poleBound n : ℝ) / p ≤ M) (hM : 3 ≤ M) :
    |∑ a ∈ Icc 1 (mStar p), (T - innerClassOrder p (innerDegree n) a) *
        (T + innerClassOrder p (innerDegree n) a - ellA p (poleBound n) a - 5) -
      p * ∫ z in (0 : ℝ)..1 / 2, (T - weightedPoleCount ((poleBound n : ℝ) / p) z) *
        (T + weightedPoleCount ((poleBound n : ℝ) / p) z - ell ((poleBound n : ℝ) / p) z - 5)| ≤
      192 * M ^ 2 := by
  set x : ℝ := (poleBound n : ℝ) / p with hx
  have hαx : (innerRatio : ℝ) * x = (innerDegree n : ℝ) / p := by
    rw [hx, show (innerRatio : ℝ) = 3 / 40 by norm_num [innerRatio]]
    simp only [poleBound, innerDegree]; push_cast; ring
  convert abs_sum_bracket_sub_integral_le p hT1 hT2
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hxM hM using 3
  rw [← mStar_def]
  refine sum_congr rfl fun a ha => ?_
  have hb : (innerClassOrder p (innerDegree n) a : ℝ) = weightedPoleCount x (a / p) := by
    rw [innerClassOrder_def, weightedPoleCount_def, hαx]
    push_cast
    rw [ellA_eq_ell_of_mem_Icc _ ha]
  rw [hb, ellA_eq_ell_of_mem_Icc _ ha, ← hx]

/-- For odd `p`, `2 ϖ_p(K, M) = (h - L₀ + 3 (N - m_N)) / m°`. -/
theorem two_mul_allocationDensity {n p M : ℕ} (hp : Odd p) :
    2 * allocationDensity n M p = ((matrixOrder n : ℝ) - zeroClassDim M +
      3 * ((innerDegree n : ℝ) - mA p (innerDegree n))) / (mStar p : ℝ) := by
  have hm : ((2 * mStar p + 1 : ℕ) : ℝ) = p := by rw [two_mul_mStar_add_one hp]
  push_cast at hm
  rw [allocationDensity, ← hm]
  ring

/-- For odd `p`, the common dimension is `T = ⌊2 ϖ_p(K, M)⌋`. -/
theorem commonClassDim_eq_floor_two_mul_allocationDensity {n p M : ℕ} (hp : Odd p) :
    commonClassDim n p M = ⌊2 * allocationDensity n M p⌋ := by
  rw [two_mul_allocationDensity hp, commonClassDim_eq_floor (k := ℝ)]

/-- For odd `p > 1`, the number of extras `E = m° {2 ϖ}` is within `1/2` of `p {2 ϖ} / 2`. -/
theorem abs_extraCount_sub_le {p : ℕ} (hp : Odd p) (hp1 : 1 < p) (n M : ℕ) :
    |(extraCount n p M : ℝ) - p * (Int.fract (2 * allocationDensity n M p) / 2)| ≤ 1 / 2 := by
  have hm : ((2 * mStar p + 1 : ℕ) : ℝ) = p := by rw [two_mul_mStar_add_one hp]
  push_cast at hm
  have hm0 : (mStar p : ℝ) ≠ 0 := by
    have := two_mul_mStar_add_one hp
    exact_mod_cast (by omega : mStar p ≠ 0)
  have hE : (extraCount n p M : ℝ) = mStar p * Int.fract (2 * allocationDensity n M p) := by
    rw [← Int.self_sub_floor, ← commonClassDim_eq_floor_two_mul_allocationDensity hp,
      two_mul_allocationDensity hp, extraCount_def]
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_add, Int.cast_natCast, Int.cast_ofNat]
    field_simp
  set f := Int.fract (2 * allocationDensity n M p)
  rw [hE, show (mStar p : ℝ) * f - p * (f / 2) = -(f / 2) by linear_combination (f / 2) * hm,
    abs_neg, abs_of_nonneg (by positivity)]
  linarith [Int.fract_lt_one (2 * allocationDensity n M p)]

/-- Under the hypotheses of the inner asymptotics, `1 ≤ ϖ_p(K, M) ≤ 3 M / 2`. -/
theorem allocationDensity_mem_Icc {n p M : ℕ} (hM : 40 ≤ M) (hK : 200 * M ^ 2 ≤ poleBound n)
    (hpl : poleBound n < M * p) (hpu : 3 * p ≤ poleBound n) :
    allocationDensity n M p ∈ Set.Icc 1 (3 / 2 * (M : ℝ)) := by
  have h200 : 200 * M < p := Nat.lt_of_mul_lt_mul_left (a := M) (by nlinarith)
  have hM' : (40 : ℝ) ≤ M := by exact_mod_cast hM
  have h200' : 200 * (M : ℝ) < p := by exact_mod_cast h200
  have hp0 : (0 : ℝ) < p := by linarith
  have hnear := abs_allocationDensity_sub_le hM (by omega) hpl.le
  have h12 : 12 * (M : ℝ) / p ≤ 12 / 200 := by rw [div_le_iff₀ hp0]; linarith
  have hx3 : 3 ≤ (poleBound n : ℝ) / p := by rw [le_div_iff₀ hp0]; exact_mod_cast hpu
  have hxM : (poleBound n : ℝ) / p ≤ M := by rw [div_le_iff₀ hp0]; exact_mod_cast hpl.le
  rw [mul_div_assoc, show (heightRatio : ℝ) = 23 / 20 by norm_num [heightRatio], abs_le] at hnear
  constructor <;> linarith

/-- Under the hypotheses of the inner asymptotics, `0 ≤ T ≤ 3 M`. -/
theorem commonClassDim_mem_Icc {n p M : ℕ} (hp : Odd p) (hM : 40 ≤ M)
    (hK : 200 * M ^ 2 ≤ poleBound n) (hpl : poleBound n < M * p) (hpu : 3 * p ≤ poleBound n) :
    (commonClassDim n p M : ℝ) ∈ Set.Icc 0 (3 * (M : ℝ)) := by
  obtain ⟨h₁, h₂⟩ := allocationDensity_mem_Icc hM hK hpl hpu
  rw [commonClassDim_eq_floor_two_mul_allocationDensity hp]
  exact ⟨by linarith [Int.lt_floor_add_one (2 * allocationDensity n M p)],
    by linarith [Int.floor_le (2 * allocationDensity n M p)]⟩

/-- The inner exponent splits as the zero block, the blocks `1 ≤ a ≤ m°` with the common
dimension `T`, and the closed contribution `E (2T - q̃(K/p) - 5) + E - min(E, 𝒜_p(K))` of the
extras. -/
theorem innerExponent_eq_sum_commonClassDim_bracket {n p M : ℕ} (hM : 40 ≤ M)
    (hK : 200 * M ^ 2 ≤ poleBound n) (hpl : (poleBound n : ℚ) / M < p)
    (hpu : (p : ℚ) ≤ poleBound n / 3) (hp : 3 ≤ p) :
    (innerExponent n p M : ℝ) =
      ((2 * ∑ i ∈ range (zeroClassDim M), innerWeight n p M 0 i : ℚ) : ℝ) +
      ∑ a ∈ Icc 1 (mStar p), ((commonClassDim n p M : ℝ) - innerClassOrder p (innerDegree n) a) *
        ((commonClassDim n p M : ℝ) + innerClassOrder p (innerDegree n) a -
          ellA p (poleBound n) a - 5) +
      (extraCount n p M *
          (2 * commonClassDim n p M - basePoleCount ((poleBound n : ℝ) / p) - 5) +
        extraCount n p M - min (extraCount n p M : ℝ) (largeClassCount (poleBound n) p)) := by
  have hγ : innerExponent n p M = 2 * ∑ i ∈ range (zeroClassDim M), innerWeight n p M 0 i +
      ∑ a ∈ Icc 1 (mStar p), ((classDim n p M a : ℚ) - innerClassOrder p (innerDegree n) a) *
        ((classDim n p M a : ℚ) + innerClassOrder p (innerDegree n) a -
          ellA p (poleBound n) a - 5) := by
    rw [innerExponent_eq, mul_add]
    congr 1
    rw [mul_sum]
    refine sum_congr rfl fun a ha => two_mul_sum_innerWeight
      (by have := (mem_Icc.1 ha).1; omega) ?_
    exact (two_le_innerClassDim hM hK hpl hpu (mem_Icc.1 ha).1 (mem_Icc.1 ha).2).trans'
      (by norm_num)
  have hX := sum_classDim_bracket n M hp
  rw [sum_sub_distrib] at hX
  rw [hγ, ← hX]
  push_cast
  ring

private lemma abs_extras_sub_le {p E f B A ñ M : ℝ} (hp : 0 ≤ p)
    (hE : |E - p * (f / 2)| ≤ 1 / 2) (hA : |A - p * ñ| ≤ 8) (hB : |B| ≤ 8 * M) :
    |E * B + E - min E A - p * (f / 2 * B + max (f / 2 - ñ) 0)| ≤ 4 * M + 10 := by
  have hmin : |min E A - p * min (f / 2) ñ| ≤ 9 := by
    rw [mul_min_of_nonneg _ _ hp]
    refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le ?_ ?_) <;> linarith
  have hpos : p * max (f / 2 - ñ) 0 = p * (f / 2) - p * min (f / 2) ñ := by
    rcases le_total (f / 2) ñ with h | h
    · rw [max_eq_right (by linarith), min_eq_left h]; ring
    · rw [max_eq_left (by linarith), min_eq_right h]; ring
  have hEB : |(E - p * (f / 2)) * B| ≤ 1 / 2 * (8 * M) := by
    rw [abs_mul]; exact mul_le_mul hE hB (abs_nonneg _) (by norm_num)
  rw [show E * B + E - min E A - p * (f / 2 * B + max (f / 2 - ñ) 0) =
    (E - p * (f / 2)) * B + (E - p * (f / 2)) - (min E A - p * min (f / 2) ñ) by
      rw [mul_add, hpos]; ring]
  refine (abs_sub _ _).trans ?_
  linarith [abs_add_le ((E - p * (f / 2)) * B) (E - p * (f / 2))]

/-- The Lipschitz bound for `Γ̂(x, ·)` at `H x` gives `p |Γ̂(x, σ) - Γ(x)| ≤ 144 M²` when
`|σ - H x| ≤ 12 M / p`. -/
theorem abs_mul_innerLimitingGammaHat_sub_le {M x σ p : ℝ} (hx : 3 ≤ x) (hxM : x ≤ M)
    (hp : 0 < p) (hσ : σ ∈ Set.Icc 1 (2 * M)) (hσx : |σ - (heightRatio : ℝ) * x| ≤ 12 * M / p) :
    |p * innerLimitingGammaHat x σ - p * innerLimitingGamma x| ≤ 144 * M ^ 2 := by
  have hH : (heightRatio : ℝ) = 23 / 20 := by norm_num [heightRatio]
  have hlip := abs_innerLimitingGammaHat_sub_le hx hxM hσ (σ' := (heightRatio : ℝ) * x)
    ⟨by rw [hH]; linarith, by rw [hH]; linarith⟩
  rw [innerLimitingGammaHat_heightRatio_mul] at hlip
  have := hp.ne'
  rw [← mul_sub, abs_mul, abs_of_pos hp]
  calc _ ≤ p * (12 * M * (12 * M / p)) :=
        mul_le_mul_of_nonneg_left (hlip.trans (mul_le_mul_of_nonneg_left hσx (by linarith)))
          hp.le
    _ = 144 * M ^ 2 := by field_simp; ring

/-- **The inner asymptotics.** For an integer `M ≥ 40`, `K = 40 n ≥ 200 M²` and an odd `p` with
`K / M < p ≤ K / 3`, the inner exponent satisfies `|γ_p^in - p Γ(K/p)| ≤ 10⁴ M²`. -/
@[zeta5irr "lem_gin_asymp"]
theorem abs_innerExponent_sub_le {n p M : ℕ} (hp : Odd p) (hM : 40 ≤ M)
    (hK : 200 * M ^ 2 ≤ poleBound n) (hpl : poleBound n < M * p) (hpu : 3 * p ≤ poleBound n) :
    |(innerExponent n p M : ℝ) - p * innerLimitingGamma ((poleBound n : ℝ) / p)| ≤
      10 ^ 4 * M ^ 2 := by
  have h200 : 200 * M < p := Nat.lt_of_mul_lt_mul_left (a := M) (by nlinarith)
  have hM' : (40 : ℝ) ≤ M := by exact_mod_cast hM
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hM0Q : (0 : ℚ) < M := by exact_mod_cast (by omega : 0 < M)
  have hplQ : (poleBound n : ℚ) / M < p := by
    have : (poleBound n : ℚ) < M * p := by exact_mod_cast hpl
    rw [div_lt_iff₀ hM0Q]; linarith
  have hpuQ : (p : ℚ) ≤ poleBound n / 3 := by
    have : 3 * (p : ℚ) ≤ poleBound n := by exact_mod_cast hpu
    rw [le_div_iff₀ (by norm_num)]; linarith
  have hZ0 : |((2 * ∑ i ∈ range (zeroClassDim M), innerWeight n p M 0 i : ℚ) : ℝ)| ≤
      100 * M ^ 2 := by
    exact_mod_cast abs_two_mul_sum_innerWeight_zero_le hM hK hplQ
  have hx3 : 3 ≤ (poleBound n : ℝ) / p := by rw [le_div_iff₀ hp0]; exact_mod_cast hpu
  have hxM : (poleBound n : ℝ) / p ≤ M := by rw [div_le_iff₀ hp0]; exact_mod_cast hpl.le
  obtain ⟨hϖ1, hϖ2⟩ := allocationDensity_mem_Icc hM hK hpl hpu
  obtain ⟨hT1, hT2⟩ := commonClassDim_mem_Icc hp hM hK hpl hpu
  have hnear := abs_allocationDensity_sub_le hM (by omega) hpl.le
  have hS := abs_sum_innerClassOrder_bracket_sub_integral_le n hT1 hT2 hxM (by linarith)
  have hB : |2 * (commonClassDim n p M : ℝ) - basePoleCount ((poleBound n : ℝ) / p) - 5| ≤
      8 * M :=
    abs_le.2 ⟨by linarith [basePoleCount_le ((poleBound n : ℝ) / p)],
      by linarith [basePoleCount_nonneg (zero_le_three.trans hx3)]⟩
  have hX := abs_extras_sub_le hp0.le (abs_extraCount_sub_le hp (by omega) n M)
    (abs_largeClassCount_sub_le (poleBound n) p) hB
  have hΓ := abs_mul_innerLimitingGammaHat_sub_le hx3 hxM hp0 ⟨hϖ1, by linarith⟩
    (by rwa [mul_div_assoc] at hnear)
  rw [innerLimitingGammaHat_def, ← commonClassDim_eq_floor_two_mul_allocationDensity hp] at hΓ
  rw [innerExponent_eq_sum_commonClassDim_bracket hM hK hplQ hpuQ (by omega)]
  obtain ⟨h₁, h₂⟩ := abs_le.1 hZ0
  obtain ⟨h₃, h₄⟩ := abs_le.1 hS
  obtain ⟨h₅, h₆⟩ := abs_le.1 hX
  obtain ⟨h₇, h₈⟩ := abs_le.1 hΓ
  have hMM : (M : ℝ) ≤ M ^ 2 := le_self_pow₀ (by linarith) (by norm_num)
  exact abs_le.2 ⟨by linarith, by linarith⟩

end Zeta5Irr
