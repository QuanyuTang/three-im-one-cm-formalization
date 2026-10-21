module

public import RequestProject.ThreeIM.Basic

/-!
# A bounded spherical derivative bounds the cubic auxiliary quotient

If the first value is large compared with all three marked values, and
the second is at most a fixed multiple of the first, then the cubic
auxiliary quotient is bounded. These are pointwise complex inequalities.
-/

@[expose] public section

open Complex

namespace ThreeIM

theorem cubic_quotient_inverse_coordinates (a : Fin 3 → ℂ) {z : ℂ}
    (hz : z ≠ 0) (hne : ∀ j, z ≠ a j) (w d : ℂ) :
    (z - w) * d / cubicP a z =
      (1 - w / z) * (d / z ^ 2) /
        ((1 - a 0 / z) * (1 - a 1 / z) * (1 - a 2 / z)) := by
  have hf (j : Fin 3) : 1 - a j / z = (z - a j) / z := by field_simp
  have h0 := sub_ne_zero.mpr (hne 0)
  have h1 := sub_ne_zero.mpr (hne 1)
  have h2 := sub_ne_zero.mpr (hne 2)
  rw [hf 0, hf 1, hf 2]
  unfold cubicP
  field_simp

theorem norm_inverse_cubic_factor_le_two {a z : ℂ}
    (hz : 1 ≤ ‖z‖) (ha : 2 * ‖a‖ ≤ ‖z‖) : ‖(1 - a / z)⁻¹‖ ≤ 2 := by
  have hzpos : 0 < ‖z‖ := by linarith
  have hq : ‖a / z‖ ≤ 1 / 2 := by
    rw [norm_div, div_le_iff₀ hzpos]
    linarith
  have hlow : 1 / 2 ≤ ‖1 - a / z‖ := by
    have hh := norm_sub_norm_le (1 : ℂ) (a / z)
    simp only [norm_one] at hh
    linarith
  rw [norm_inv, inv_eq_one_div, div_le_iff₀ (by linarith : 0 < ‖1 - a / z‖)]
  linarith

theorem norm_cubic_quotient_product_le {a : Fin 3 → ℂ} {z w d : ℂ} {M K : ℝ}
    (hz : 1 ≤ ‖z‖) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (ha : ∀ j, 2 * ‖a j‖ ≤ ‖z‖) (hw : ‖w‖ ≤ K * ‖z‖)
    (hd : 2 * ‖d‖ ≤ M * (1 + ‖z‖ ^ 2)) :
    ‖(z - w) * d / cubicP a z‖ ≤ 8 * (1 + K) * M := by
  have hzpos : 0 < ‖z‖ := by linarith
  have hz0 : z ≠ 0 := norm_pos_iff.mp hzpos
  have hne (j : Fin 3) : z ≠ a j := by
    intro heq
    have hh := ha j
    rw [← heq] at hh
    linarith
  have hfirst : ‖1 - w / z‖ ≤ 1 + K := by
    have hq : ‖w / z‖ ≤ K := by
      rw [norm_div, div_le_iff₀ hzpos]
      exact hw
    have hh := norm_sub_le (1 : ℂ) (w / z)
    simp only [norm_one] at hh
    linarith
  have hderiv : ‖d / z ^ 2‖ ≤ M := by
    rw [norm_div, norm_pow, div_le_iff₀ (by positivity : 0 < ‖z‖ ^ 2)]
    have hsq : 1 ≤ ‖z‖ ^ 2 := by nlinarith
    have hscale := mul_le_mul_of_nonneg_left hsq hM
    nlinarith
  have hf (j : Fin 3) : ‖(1 - a j / z)⁻¹‖ ≤ 2 :=
    norm_inverse_cubic_factor_le_two hz (ha j)
  have hden : ‖((1 - a 0 / z) * (1 - a 1 / z) * (1 - a 2 / z))⁻¹‖ ≤ 8 := by
    calc
      _ = ‖(1 - a 0 / z)⁻¹‖ * ‖(1 - a 1 / z)⁻¹‖ * ‖(1 - a 2 / z)⁻¹‖ := by
        simp only [norm_inv, norm_mul, mul_inv_rev]
        ring
      _ ≤ 2 * 2 * 2 := by
        exact mul_le_mul (mul_le_mul (hf 0) (hf 1) (norm_nonneg _) (by norm_num))
          (hf 2) (norm_nonneg _) (by norm_num)
      _ = 8 := by norm_num
  rw [cubic_quotient_inverse_coordinates a hz0 hne w d, div_eq_mul_inv,
    norm_mul, norm_mul]
  calc
    _ ≤ ((1 + K) * M) * 8 :=
      mul_le_mul (mul_le_mul hfirst hderiv (norm_nonneg _) (by linarith)) hden
        (norm_nonneg _) (mul_nonneg (by linarith) hM)
    _ = 8 * (1 + K) * M := by ring

end ThreeIM
