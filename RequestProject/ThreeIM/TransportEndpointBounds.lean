module

public import RequestProject.ThreeIM.TransportScale
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! # Finite endpoint values and uniform separation from the marked roots -/

@[expose] public section

namespace ThreeIM

set_option autoImplicit false

theorem transportScale_endpoint {ε s : ℝ} (hε : 0 < ε) (hs : 0 < s) :
    transportScale ε ((2 * Real.log (s / ε) : ℝ) : ℂ) = (s : ℂ) := by
  have he : ((2 * Real.log (s / ε) : ℝ) : ℂ) / 2 =
      (Real.log (s / ε) : ℂ) := by push_cast; ring
  rw [transportScale, he, ← Complex.ofReal_exp, Real.exp_log (div_pos hs hε)]
  push_cast
  field_simp [hε.ne']

theorem transport_endpoint_coordinate_bounds {α W h : ℂ} {r s : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hr : r ≤ ‖α‖ / 4)
    (hW : ‖W - 2 * α‖ ≤ r / 2) (hh : ‖h‖ ≤ s / 2) :
    s * ‖α‖ / 2 ≤ ‖(s : ℂ) * W * (1 + h)‖ ∧
      ‖(s : ℂ) * W * (1 + h)‖ ≤ 6 * s * ‖α‖ ∧
      ‖(s : ℂ) * W * h‖ ≤ 3 * s * ‖α‖ := by
  have hWupper : ‖W‖ ≤ 3 * ‖α‖ := by
    have ht := norm_add_le (W - 2 * α) (2 * α)
    rw [sub_add_cancel, norm_mul] at ht
    norm_num at ht
    linarith [norm_nonneg α]
  have hWlower : ‖α‖ ≤ ‖W‖ := by
    have ht := norm_sub_le W (W - 2 * α)
    rw [sub_sub_cancel, norm_mul] at ht
    norm_num at ht
    linarith [norm_nonneg α]
  have hsumupper : ‖(1 : ℂ) + h‖ ≤ 2 := by
    have ht := norm_add_le (1 : ℂ) h
    rw [norm_one] at ht
    linarith
  have hsumlower : (1 / 2 : ℝ) ≤ ‖(1 : ℂ) + h‖ := by
    have ht := norm_sub_le ((1 : ℂ) + h) h
    rw [add_sub_cancel_right, norm_one] at ht
    linarith
  have hh1 : ‖h‖ ≤ 1 := by linarith
  have hmulupper : s * ‖W‖ ≤ 3 * s * ‖α‖ := by
    nlinarith [mul_le_mul_of_nonneg_left hWupper hs]
  have hmullower : s * ‖α‖ ≤ s * ‖W‖ :=
    mul_le_mul_of_nonneg_left hWlower hs
  have hmulnonneg : 0 ≤ s * ‖W‖ := mul_nonneg hs (norm_nonneg W)
  simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hsumlower hmulnonneg]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hsumupper hmulnonneg]
  · nlinarith [mul_le_mul_of_nonneg_left hh1 hmulnonneg]

theorem transport_endpoint_uniform_root_separation
    {a : Fin 3 → ℂ} (ha : Function.Injective a) (j : Fin 3)
    {x : ℂ} {c : ℝ} (hc : 0 < c) (hlower : c ≤ ‖x‖)
    (hupper : ‖x‖ ≤ min ‖a (j + 1) - a j‖ ‖a (j + 2) - a j‖ / 2) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ i : Fin 3, γ ≤ ‖x + a j - a i‖ := by
  have hj1 : j + 1 ≠ j := by fin_cases j <;> decide
  have hj2 : j + 2 ≠ j := by fin_cases j <;> decide
  have h1 : 0 < ‖a (j + 1) - a j‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (ha.ne hj1))
  have h2 : 0 < ‖a (j + 2) - a j‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (ha.ne hj2))
  let d : ℝ := min ‖a (j + 1) - a j‖ ‖a (j + 2) - a j‖
  have hd : 0 < d := lt_min h1 h2
  refine ⟨min c (d / 2), lt_min hc (by positivity), fun i => ?_⟩
  have hi : i = j ∨ i = j + 1 ∨ i = j + 2 := by
    fin_cases j <;> fin_cases i <;> decide
  rcases hi with hi | hi | hi
  · rw [hi, add_sub_cancel_right]
    exact (min_le_left _ _).trans hlower
  · rw [hi]
    have ht := norm_sub_le x (x + a j - a (j + 1))
    have he : x - (x + a j - a (j + 1)) = a (j + 1) - a j := by ring
    rw [he] at ht
    have hmin : d ≤ ‖a (j + 1) - a j‖ := min_le_left _ _
    have hγ : min c (d / 2) ≤ d / 2 := min_le_right _ _
    linarith
  · rw [hi]
    have ht := norm_sub_le x (x + a j - a (j + 2))
    have he : x - (x + a j - a (j + 2)) = a (j + 2) - a j := by ring
    rw [he] at ht
    have hmin : d ≤ ‖a (j + 2) - a j‖ := min_le_right _ _
    have hγ : min c (d / 2) ≤ d / 2 := min_le_right _ _
    linarith

end ThreeIM
