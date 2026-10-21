module

public import RequestProject.ThreeIM.ClusterBudgetConstants
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # The actual control-circle parameters fit the original budget -/

@[expose] public section

set_option autoImplicit false

namespace ThreeIM

/-- The explicit distance and logarithmic factor-band parameters have all
the numerical margins required by the control-circle maximum principle.
The case N=0, including an empty actual divisor set, is retained. -/
theorem controlCircle_parameters {R Δ M N : ℝ}
    (hR : 1 ≤ R) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hM : 1 ≤ M)
    (hN : 0 ≤ N) (hbound : N ≤ 8 * R * M * Δ⁻¹) :
    let δ := Δ / (100 * (N + 1))
    let C := Real.log (3 * R / δ)
    let B := finiteDiskBudget R Δ M
    0 < δ ∧ δ ≤ 1 ∧ 0 ≤ C ∧ Real.exp (-C) ≤ δ ∧ 2 * R ≤ Real.exp C ∧
      C * N ≤ B / 40 ∧ N / δ ≤ B / 100 ∧
      Real.exp (B / 1000 + C * N) + N / δ ≤ Real.exp B := by
  let δ := Δ / (100 * (N + 1))
  let C := Real.log (3 * R / δ)
  let B := finiteDiskBudget R Δ M
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    apply (div_le_one (show 0 < 100 * (N + 1) by positivity)).mpr
    linarith
  have ht : 1 ≤ Δ⁻¹ := (one_le_inv₀ hΔ).mpr hΔ1
  have hunit : 1 ≤ R * M * Δ⁻¹ := by
    calc
      (1 : ℝ) ≤ R := hR
      _ ≤ R * M := le_mul_of_one_le_right (by positivity) hM
      _ ≤ R * M * Δ⁻¹ := le_mul_of_one_le_right (by positivity) ht
  have hplus : N + 1 ≤ 9 * R * M * Δ⁻¹ := by nlinarith
  have hsum : N / δ ≤ 7200 * (R ^ 2 * M ^ 2) * (Δ⁻¹) ^ 3 := by
    calc
      N / δ = 100 * N * (N + 1) * Δ⁻¹ := by
        dsimp [δ]
        rw [div_div_eq_mul_div, div_eq_mul_inv]
        ring
      _ ≤ 100 * (8 * R * M * Δ⁻¹) * (9 * R * M * Δ⁻¹) * Δ⁻¹ := by gcongr
      _ = _ := by ring
  have hsumB : N / δ ≤ B / 100 :=
    hsum.trans (finiteDiskBudget_circle_sum_margin hR hΔ hΔ1 hM)
  have hratio : 0 < 3 * R / δ := by positivity
  have hratio1 : 1 ≤ 3 * R / δ := (one_le_div hδ).mpr (by linarith)
  have hC : 0 ≤ C := Real.log_nonneg hratio1
  have hbandlo : Real.exp (-C) ≤ δ := by
    dsimp [C]
    rw [Real.exp_neg, Real.exp_log hratio]
    simpa only [inv_div] using (div_le_self hδ.le (show 1 ≤ 3 * R by linarith))
  have hbandhi : 2 * R ≤ Real.exp C := by
    dsimp [C]
    rw [Real.exp_log hratio]
    apply (le_div_iff₀ hδ).mpr
    nlinarith [mul_le_mul_of_nonneg_left hδ1 (show 0 ≤ 2 * R by positivity)]
  have hexponent : C * N ≤ B / 40 := by
    calc
      C * N ≤ (3 * R / δ) * N :=
        mul_le_mul_of_nonneg_right (Real.log_le_self hratio.le) hN
      _ = 3 * R * (N / δ) := by ring
      _ ≤ 3 * R * (7200 * (R ^ 2 * M ^ 2) * (Δ⁻¹) ^ 3) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 21600 * (R ^ 3 * M ^ 2) * (Δ⁻¹) ^ 3 := by ring
      _ ≤ B / 40 := finiteDiskBudget_circle_exponent_margin hR hΔ hΔ1 hM
  have hB : 4 ≤ B := by
    have hm := finiteDiskBudget_ge_million (by linarith : 0 ≤ R) hΔ (by linarith : 0 ≤ M)
    dsimp [B]
    linarith
  have hfirst : Real.exp (B / 1000 + C * N) ≤ Real.exp (B / 30) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hsecond : N / δ ≤ Real.exp (B / 30) := by
    calc
      N / δ ≤ B / 100 := hsumB
      _ ≤ Real.exp (B / 100) :=
        (by linarith : B / 100 ≤ B / 100 + 1).trans (Real.add_one_le_exp _)
      _ ≤ Real.exp (B / 30) := Real.exp_le_exp.mpr (by linarith)
  have htwo : 2 * Real.exp (B / 30) ≤ Real.exp B := by
    have hgap : 2 ≤ Real.exp (B - B / 30) :=
      (by linarith : (2 : ℝ) ≤ (B - B / 30) + 1).trans (Real.add_one_le_exp _)
    calc
      2 * Real.exp (B / 30) ≤ Real.exp (B - B / 30) * Real.exp (B / 30) :=
        mul_le_mul_of_nonneg_right hgap (Real.exp_pos _).le
      _ = Real.exp B := by rw [← Real.exp_add]; congr 1; ring
  exact ⟨hδ, hδ1, hC, hbandlo, hbandhi, hexponent, hsumB,
    (add_le_add hfirst hsecond).trans (by linarith)⟩

end ThreeIM
