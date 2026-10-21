module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Numerical room in the original finite-disk parameter -/

@[expose] public section

set_option autoImplicit false

namespace ThreeIM

/-- The exact local parameter of the original finite-disk argument;
Delta is the gap between its two radii. -/
noncomputable def finiteDiskBudget (R Δ M : ℝ) : ℝ :=
  1000000 * (1 + R) ^ 3 * (1 + Δ⁻¹) ^ 4 * (1 + M) ^ 3

theorem finiteDiskBudget_ge_million {R Δ M : ℝ}
    (hR : 0 ≤ R) (hΔ : 0 < Δ) (hM : 0 ≤ M) : 1000000 ≤ finiteDiskBudget R Δ M := by
  have h1 : (1 : ℝ) ≤ (1 + R) ^ 3 := one_le_pow₀ (by linarith)
  have h2 : (1 : ℝ) ≤ (1 + Δ⁻¹) ^ 4 :=
    one_le_pow₀ (by have := inv_pos.mpr hΔ; linarith)
  have h3 : (1 : ℝ) ≤ (1 + M) ^ 3 := one_le_pow₀ (by linarith)
  unfold finiteDiskBudget
  calc
    (1000000 : ℝ) = 1000000 * 1 * 1 * 1 := by ring
    _ ≤ _ := by gcongr

private theorem linear_monomial_le_budget {R Δ M : ℝ}
    (hR : 0 ≤ R) (hΔ : 0 < Δ) (hM : 1 ≤ M) :
    1000000 * (R ^ 3 * M) * (Δ⁻¹) ^ 4 ≤ finiteDiskBudget R Δ M := by
  have hMpow : M ≤ (1 + M) ^ 3 := by
    have hpow := pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + M) (by decide : 1 ≤ 3)
    simp only [pow_one] at hpow
    linarith
  unfold finiteDiskBudget
  calc
    1000000 * (R ^ 3 * M) * (Δ⁻¹) ^ 4 = 1000000 * R ^ 3 * (Δ⁻¹) ^ 4 * M := by ring
    _ ≤ _ := by gcongr <;> linarith

private theorem quadratic_monomial_le_budget {R Δ M : ℝ}
    (hR : 0 ≤ R) (hΔ : 0 < Δ) (hM : 1 ≤ M) :
    1000000 * (R ^ 3 * M ^ 2) * (Δ⁻¹) ^ 4 ≤ finiteDiskBudget R Δ M := by
  have hMpow : M ^ 2 ≤ (1 + M) ^ 3 :=
    (pow_le_pow_left₀ (by linarith) (by linarith : M ≤ 1 + M) 2).trans
      (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + M) (by decide : 2 ≤ 3))
  unfold finiteDiskBudget
  calc
    1000000 * (R ^ 3 * M ^ 2) * (Δ⁻¹) ^ 4 =
        1000000 * R ^ 3 * (Δ⁻¹) ^ 4 * M ^ 2 := by ring
    _ ≤ _ := by gcongr <;> linarith

private theorem scaled_monomial_le_of_budget {B X t c k : ℝ} {n : ℕ}
    (hX : 0 ≤ X) (ht : 1 ≤ t) (hn : n ≤ 4) (hk : 0 < k)
    (hck : c * k ≤ 1000000) (hbudget : 1000000 * X * t ^ 4 ≤ B) :
    c * X * t ^ n ≤ B / k := by
  apply (le_div_iff₀ hk).mpr
  apply le_trans _ hbudget
  calc
    c * X * t ^ n * k = (c * k) * X * t ^ n := by ring
    _ ≤ 1000000 * X * t ^ 4 :=
      mul_le_mul (mul_le_mul_of_nonneg_right hck hX) (pow_le_pow_right₀ ht hn)
        (pow_nonneg (by linarith) _) (by positivity)

/-- The actual real-part bound fits inside the margin used by the
q-independent cluster count. -/
theorem finiteDiskBudget_re_margin {R Δ M : ℝ}
    (hR : 1 ≤ R) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hM : 1 ≤ M) :
    784 * (R ^ 3 * M) * (Δ⁻¹) ^ 2 ≤ finiteDiskBudget R Δ M / 1000 := by
  have ht : 1 ≤ Δ⁻¹ := (one_le_inv₀ hΔ).mpr hΔ1
  exact scaled_monomial_le_of_budget (by positivity) ht (by decide)
    (by norm_num) (by norm_num) (linear_monomial_le_budget (by linarith) hΔ hM)

/-- The combined local derivatives need only this weaker margin to leave
ample space in the regular-disk logarithmic-derivative estimate. -/
theorem finiteDiskBudget_derivative_margin {R Δ M : ℝ}
    (hR : 1 ≤ R) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hM : 1 ≤ M) :
    100672 * (R ^ 3 * M) * (Δ⁻¹) ^ 3 ≤ finiteDiskBudget R Δ M / 4 := by
  have ht : 1 ≤ Δ⁻¹ := (one_le_inv₀ hΔ).mpr hΔ1
  exact scaled_monomial_le_of_budget (by positivity) ht (by decide)
    (by norm_num) (by norm_num) (linear_monomial_le_budget (by linarith) hΔ hM)

/-- A coarse logarithm estimate already fits; refined winding bounds are
unnecessary for this control-circle step. -/
theorem finiteDiskBudget_circle_exponent_margin {R Δ M : ℝ}
    (hR : 1 ≤ R) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hM : 1 ≤ M) :
    21600 * (R ^ 3 * M ^ 2) * (Δ⁻¹) ^ 3 ≤ finiteDiskBudget R Δ M / 40 := by
  have ht : 1 ≤ Δ⁻¹ := (one_le_inv₀ hΔ).mpr hΔ1
  exact scaled_monomial_le_of_budget (by positivity) ht (by decide)
    (by norm_num) (by norm_num) (quadratic_monomial_le_budget (by linarith) hΔ hM)

theorem finiteDiskBudget_circle_sum_margin {R Δ M : ℝ}
    (hR : 1 ≤ R) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hM : 1 ≤ M) :
    7200 * (R ^ 2 * M ^ 2) * (Δ⁻¹) ^ 3 ≤ finiteDiskBudget R Δ M / 100 := by
  have ht : 1 ≤ Δ⁻¹ := (one_le_inv₀ hΔ).mpr hΔ1
  have hmono : R ^ 2 * M ^ 2 ≤ R ^ 3 * M ^ 2 :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hR (by decide : 2 ≤ 3)) (sq_nonneg M)
  have hbase : 1000000 * (R ^ 2 * M ^ 2) * (Δ⁻¹) ^ 4 ≤ finiteDiskBudget R Δ M := by
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmono (by norm_num))
      (by positivity)).trans (quadratic_monomial_le_budget (by linarith) hΔ hM)
  exact scaled_monomial_le_of_budget (by positivity) ht (by decide)
    (by norm_num) (by norm_num) hbase

end ThreeIM
