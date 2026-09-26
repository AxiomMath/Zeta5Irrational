/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.DegreePositivity.PowIntegrable
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

/-!
# The integral of `(y² + c²)^{-m}` over `(0, ∞)`

For a real `c > 0` and a natural number `m ≥ 1`,
`∫_0^∞ dy / (y² + c²)^m = π / (2 c^{2m-1}) · 4^{-(m-1)} · binom(2m-2, m-1)`.

The proof is by induction on `m`. The case `m = 1` is the arctangent integral. Integrating
`((y² + c²)^m)⁻¹ · 1` by parts against `y` and writing `y² = (y² + c²) - c²` gives the
recursion `2 m c² I_{m+1} = (2m - 1) I_m` for `I_m = ∫_0^∞ dy / (y² + c²)^m`, and the
closed form satisfies the same recursion by `(n+1) binom(2n+2, n+1) = 2 (2n+1) binom(2n, n)`.

## Main results

* `Zeta5Irr.integral_Ioi_inv_sq_add_sq`: `∫_0^∞ dy / (y² + c²) = π / (2c)` for `c > 0`.
* `Zeta5Irr.integral_Ioi_inv_sq_add_sq_pow_succ`: the recursion
  `2 m c² I_{m+1} = (2m - 1) I_m` for `c ≠ 0` and `m ≥ 1`.
* `Zeta5Irr.integral_Ioi_inv_sq_add_sq_pow`: the closed form of `I_m`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2 (the weight, positivity, and the degree).
-/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace Zeta5Irr

/-- For `c > 0`, `∫_0^∞ dy / (y² + c²) = π / (2c)`. -/
theorem integral_Ioi_inv_sq_add_sq {c : ℝ} (hc : 0 < c) :
    ∫ y in Ioi (0 : ℝ), (y ^ 2 + c ^ 2)⁻¹ = Real.pi / (2 * c) := by
  have h := integral_comp_mul_left_Ioi' (fun x : ℝ => (1 + x ^ 2)⁻¹) 0 (inv_pos.2 hc)
  rw [mul_zero, integral_Ioi_inv_one_add_sq, Real.arctan_zero, sub_zero, smul_eq_mul] at h
  have hfun : (fun y : ℝ => (y ^ 2 + c ^ 2)⁻¹) =
      fun y => (c ^ 2)⁻¹ * (1 + (c⁻¹ * y) ^ 2)⁻¹ := by
    ext y
    rw [← mul_inv]
    congr 1
    field_simp
    ring
  rw [hfun, integral_const_mul]
  have h' : ∫ x in Ioi (0 : ℝ), (1 + (c⁻¹ * x) ^ 2)⁻¹ = c * (Real.pi / 2) := by
    rw [← h]
    field_simp
  rw [h']
  field_simp

/-- The derivative of `y ↦ ((y² + c²)^m)⁻¹` is `y ↦ -2 m y ((y² + c²)^{m+1})⁻¹`. -/
theorem hasDerivAt_inv_sq_add_sq_pow {c : ℝ} (hc : c ≠ 0) {m : ℕ} (hm : 1 ≤ m) (x : ℝ) :
    HasDerivAt (fun y : ℝ => ((y ^ 2 + c ^ 2) ^ m)⁻¹)
      (-(2 * m * x) * ((x ^ 2 + c ^ 2) ^ (m + 1))⁻¹) x := by
  have hx : x ^ 2 + c ^ 2 ≠ 0 := by positivity
  have h1 : HasDerivAt (fun y : ℝ => (y ^ 2 + c ^ 2) ^ m)
      (m * (x ^ 2 + c ^ 2) ^ (m - 1) * (2 * x)) x := by
    convert ((hasDerivAt_pow 2 x).add_const (c ^ 2)).pow m using 1
    push_cast
    ring
  convert h1.inv (pow_ne_zero _ hx) using 1
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  rw [Nat.add_sub_cancel]
  field_simp
  ring

/-- For `c ≠ 0` and `m ≥ 1`, `y / (y² + c²)^m → 0` as `y → ∞`. -/
theorem tendsto_inv_sq_add_sq_pow_mul_atTop {c : ℝ} (hc : c ≠ 0) {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun y : ℝ => ((y ^ 2 + c ^ 2) ^ m)⁻¹ * y) atTop (𝓝 0) := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hlim : Tendsto (fun y : ℝ => ((c ^ 2) ^ (m - 1))⁻¹ * y⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul ((c ^ 2) ^ (m - 1))⁻¹
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [eventually_ge_atTop 0] with y hy
    positivity
  · filter_upwards [eventually_gt_atTop 0] with y hy
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
    have hck : (c ^ 2) ^ k ≤ (y ^ 2 + c ^ 2) ^ k :=
      pow_le_pow_left₀ hc2.le (le_add_of_nonneg_left (sq_nonneg y)) k
    rw [Nat.add_sub_cancel, ← div_eq_inv_mul, ← mul_inv, ← one_div,
      div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    calc y * ((c ^ 2) ^ k * y) = y ^ 2 * (c ^ 2) ^ k := by ring
      _ ≤ (y ^ 2 + c ^ 2) ^ (k + 1) := by
        rw [pow_succ (y ^ 2 + c ^ 2) k, mul_comm (y ^ 2)]
        exact mul_le_mul hck (le_add_of_nonneg_right hc2.le) (sq_nonneg y) (by positivity)

/-- **Reduction formula.** For `c ≠ 0` and `m ≥ 1`,
`2 m c² ∫_0^∞ dy / (y² + c²)^{m+1} = (2m - 1) ∫_0^∞ dy / (y² + c²)^m`. -/
theorem integral_Ioi_inv_sq_add_sq_pow_succ {c : ℝ} (hc : c ≠ 0) {m : ℕ} (hm : 1 ≤ m) :
    2 * m * c ^ 2 * ∫ y in Ioi (0 : ℝ), ((y ^ 2 + c ^ 2) ^ (m + 1))⁻¹ =
      (2 * m - 1) * ∫ y in Ioi (0 : ℝ), ((y ^ 2 + c ^ 2) ^ m)⁻¹ := by
  have hpos : ∀ y : ℝ, 0 < y ^ 2 + c ^ 2 := fun y => by positivity
  set u : ℝ → ℝ := fun y => ((y ^ 2 + c ^ 2) ^ m)⁻¹
  set u' : ℝ → ℝ := fun y => -(2 * m * y) * ((y ^ 2 + c ^ 2) ^ (m + 1))⁻¹
  have hIm := integrableOn_inv_sq_add_sq_pow hc hm
  have hIm1 := integrableOn_inv_sq_add_sq_pow hc (Nat.le_succ_of_le hm)
  have hkey : ∀ y : ℝ, u' y * y =
      -(2 * m) * ((y ^ 2 + c ^ 2) ^ m)⁻¹ + 2 * m * c ^ 2 * ((y ^ 2 + c ^ 2) ^ (m + 1))⁻¹ := by
    intro y
    have := (hpos y).ne'
    simp only [u']
    field_simp
    ring
  have huv' : IntegrableOn (u * fun _ => (1 : ℝ)) (Ioi 0) := by
    simpa [Pi.mul_def, u] using hIm
  have hu'v : IntegrableOn (u' * fun y => y) (Ioi 0) := by
    rw [show (u' * fun y => y) = _ from funext hkey]
    exact (hIm.const_mul _).add (hIm1.const_mul _)
  have hzero : Tendsto (u * fun y => y) (𝓝[>] 0) (𝓝 0) := by
    have hcont : Continuous (u * fun y => y) :=
      (Continuous.inv₀ (by fun_prop) fun y => pow_ne_zero _ (hpos y).ne').mul continuous_id
    simpa [u] using (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  have hinf : Tendsto (u * fun y => y) atTop (𝓝 0) := tendsto_inv_sq_add_sq_pow_mul_atTop hc hm
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul (u := u) (u' := u')
    (fun x _ => hasDerivAt_inv_sq_add_sq_pow hc hm x) (fun x _ => hasDerivAt_id' x) huv' hu'v
    hzero hinf
  simp only [mul_one, sub_zero, zero_sub, hkey, u] at hibp
  rw [integral_add (hIm.const_mul _) (hIm1.const_mul _), integral_const_mul,
    integral_const_mul] at hibp
  linear_combination hibp

/-- **The integral of a pure power.** For every real `c > 0` and every natural number `m ≥ 1`,
`∫_0^∞ dy / (y² + c²)^m = π / (2 c^{2m-1}) · 4^{-(m-1)} · binom(2m-2, m-1)`. -/
@[zeta5irr "lem_w_pow_int"]
theorem integral_Ioi_inv_sq_add_sq_pow {c : ℝ} (hc : 0 < c) {m : ℕ} (hm : 1 ≤ m) :
    ∫ y in Ioi (0 : ℝ), ((y ^ 2 + c ^ 2) ^ m)⁻¹ =
      Real.pi / (2 * c ^ (2 * m - 1)) * (1 / 4 ^ (m - 1)) * ((2 * m - 2).choose (m - 1) : ℝ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  have h2 : ∀ k : ℕ, 2 * (k + 1) - 2 = 2 * k := fun k => by omega
  have h1 : ∀ k : ℕ, 2 * (k + 1) - 1 = 2 * k + 1 := fun k => by omega
  simp only [h1, h2, Nat.add_sub_cancel]
  clear hm
  induction k with
  | zero => simp [integral_Ioi_inv_sq_add_sq hc]
  | succ k ih =>
    have hrec := integral_Ioi_inv_sq_add_sq_pow_succ hc.ne' (m := k + 1) (by omega)
    rw [ih] at hrec
    have hB := Nat.succ_mul_centralBinom_succ k
    rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at hB
    have hB'' : (((2 * (k + 1)).choose (k + 1) : ℕ) : ℝ) =
        2 * (2 * k + 1) * ((2 * k).choose k : ℕ) / (k + 1) := by
      rw [eq_div_iff (by positivity), mul_comm]
      exact_mod_cast hB
    apply mul_left_cancel₀ (show (2 * ((k + 1 : ℕ) : ℝ) * c ^ 2) ≠ 0 by positivity)
    rw [hrec, hB'', show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring, pow_add, pow_succ (4 : ℝ)]
    push_cast
    field_simp
    ring

end Zeta5Irr
