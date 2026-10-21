module

public import RequestProject.ThreeIM.SelectedRadii

/-! # The original finite-disk parameter along the selected radii -/

@[expose] public section

open Filter Set MeasureTheory Topology

namespace ThreeIM

set_option autoImplicit false

/-- The exact parameter of the original finite-disk inverse-branch lemma. -/
noncomputable def selectedBranchParameter (r R M : ℝ) : ℝ :=
  1000000 * (1 + R) ^ 3 * (1 + (R - r)⁻¹) ^ 4 * (1 + M) ^ 3

theorem selectedBranchParameter_ge_million {r R M : ℝ} (hr : 1 ≤ r)
    (hR : r < R) (hM : 0 ≤ M) : 1000000 ≤ selectedBranchParameter r R M := by
  have hR0 : 0 < R := by linarith
  have hd : 0 < R - r := sub_pos.2 hR
  have hfirst : (1 : ℝ) ≤ (1 + R) ^ 3 := one_le_pow₀ (by linarith)
  have hsecond : (1 : ℝ) ≤ (1 + (R - r)⁻¹) ^ 4 :=
    one_le_pow₀ (by have := inv_pos.2 hd; linarith)
  have hthird : (1 : ℝ) ≤ (1 + M) ^ 3 := one_le_pow₀ (by linarith)
  unfold selectedBranchParameter
  calc
    (1000000 : ℝ) = 1000000 * 1 * 1 * 1 := by ring
    _ ≤ 1000000 * (1 + R) ^ 3 * (1 + (R - r)⁻¹) ^ 4 * (1 + M) ^ 3 := by gcongr

theorem selectedBranchParameter_ge_radius {r R M : ℝ} (hr : 1 ≤ r)
    (hR : r < R) (hM : 0 ≤ M) : r ≤ selectedBranchParameter r R M := by
  have hR0 : 0 < R := by linarith
  have hd : 0 < R - r := sub_pos.2 hR
  have hbase : 1 ≤ 1 + R := by linarith
  have hinv : (1 : ℝ) ≤ (1 + (R - r)⁻¹) ^ 4 :=
    one_le_pow₀ (by have := inv_pos.2 hd; linarith)
  have hMpow : (1 : ℝ) ≤ (1 + M) ^ 3 := one_le_pow₀ (by linarith)
  unfold selectedBranchParameter
  calc
    r ≤ (1 + R) ^ 3 := by
      have hp : (1 + R) ^ 1 ≤ (1 + R) ^ 3 := pow_le_pow_right₀ hbase (by decide)
      simp only [pow_one] at hp
      linarith
    _ ≤ 1000000 * (1 + R) ^ 3 :=
      le_mul_of_one_le_left (by positivity) (by norm_num)
    _ ≤ 1000000 * (1 + R) ^ 3 * (1 + (R - r)⁻¹) ^ 4 :=
      le_mul_of_one_le_right (by positivity) hinv
    _ ≤ 1000000 * (1 + R) ^ 3 * (1 + (R - r)⁻¹) ^ 4 * (1 + M) ^ 3 :=
      le_mul_of_one_le_right (by positivity) hMpow

theorem selectedBranchParameter_le {r R M L C : ℝ} (hr : 1 ≤ r)
    (hL : 1 ≤ L) (hC : 0 ≤ C) (hM : 0 ≤ M) (hMC : M ≤ C * L)
    (hlo : 1 / (2 * L) ≤ R - r) (hhi : R - r ≤ 1 / L) :
    selectedBranchParameter r R M ≤
      (1000000 * (3 : ℝ) ^ 7 * (1 + C) ^ 3) * r ^ 3 * L ^ 7 := by
  have hLp : 0 < L := by linarith
  have hd : 0 < R - r := lt_of_lt_of_le (by positivity) hlo
  have hR0 : 0 < R := by linarith
  have hLI : 1 / L ≤ 1 := by
    simpa only [one_div, inv_one] using inv_anti₀ (show (0 : ℝ) < 1 by norm_num) hL
  have hDI : (R - r)⁻¹ ≤ 2 * L := by
    have hi := inv_anti₀ (show 0 < 1 / (2 * L) by positivity) hlo
    simpa only [one_div, inv_inv] using hi
  have hfirst : 1 + R ≤ 3 * r := by linarith
  have hsecond : 1 + (R - r)⁻¹ ≤ 3 * L := by linarith
  have hthird : 1 + M ≤ (1 + C) * L := by nlinarith
  unfold selectedBranchParameter
  calc
    1000000 * (1 + R) ^ 3 * (1 + (R - r)⁻¹) ^ 4 * (1 + M) ^ 3 ≤
        1000000 * (3 * r) ^ 3 * (3 * L) ^ 4 * ((1 + C) * L) ^ 3 := by
      gcongr
    _ = (1000000 * (3 : ℝ) ^ 7 * (1 + C) ^ 3) * r ^ 3 * L ^ 7 := by ring

theorem selectedBranchParameter_pow26_le {r R M L C : ℝ} (hr : 1 ≤ r)
    (hL : 1 ≤ L) (hC : 0 ≤ C) (hM : 0 ≤ M) (hMC : M ≤ C * L)
    (hlo : 1 / (2 * L) ≤ R - r) (hhi : R - r ≤ 1 / L) :
    selectedBranchParameter r R M ^ 26 ≤
      (1000000 * (3 : ℝ) ^ 7 * (1 + C) ^ 3) ^ 26 * r ^ 78 * L ^ 182 := by
  have hb := selectedBranchParameter_le hr hL hC hM hMC hlo hhi
  have hLp : 0 < L := by linarith
  have hd : r < R := by
    have hp : 0 < 1 / (2 * L) := by positivity
    linarith
  have hB0 : 0 ≤ selectedBranchParameter r R M :=
    (by linarith : (0 : ℝ) ≤ r).trans (selectedBranchParameter_ge_radius hr hd hM)
  calc
    selectedBranchParameter r R M ^ 26 ≤
        ((1000000 * (3 : ℝ) ^ 7 * (1 + C) ^ 3) * r ^ 3 * L ^ 7) ^ 26 := by
      gcongr
    _ = (1000000 * (3 : ℝ) ^ 7 * (1 + C) ^ 3) ^ 26 * r ^ 78 * L ^ 182 := by
      simp only [mul_pow, ← pow_mul]

theorem selectedBranchParameter_tendsto_atTop {r R M L : ℕ → ℝ}
    (hr : Tendsto r atTop atTop) (hr1 : ∀ n, 1 ≤ r n) (hL : ∀ n, 1 ≤ L n)
    (hM : ∀ n, 0 ≤ M n) (hlo : ∀ n, 1 / (2 * L n) ≤ R n - r n) :
    Tendsto (fun n => selectedBranchParameter (r n) (R n) (M n)) atTop atTop := by
  apply tendsto_atTop_mono _ hr
  intro n
  apply selectedBranchParameter_ge_radius (hr1 n) _ (hM n)
  have hLp : 0 < L n := by linarith [hL n]
  have hp : 0 < 1 / (2 * L n) := by positivity
  linarith [hlo n]

theorem selectedBranchParameter_counting_error_tendsto_zero
    {f g : ℂ → ℂ} {r R M : ℕ → ℝ} {C : ℝ}
    (hr2 : ∀ n, 2 ≤ r n) (hC : 0 ≤ C) (hM : ∀ n, 0 ≤ M n)
    (hMC : ∀ n, M n ≤ C * pairL f g (r n))
    (hlo : ∀ n, 1 / (2 * pairL f g (r n)) ≤ R n - r n)
    (hhi : ∀ n, R n - r n ≤ 1 / pairL f g (r n))
    (hL : ∀ n, 1 ≤ pairL f g (r n))
    (hratio : Tendsto (fun n => pairT f g (r n) /
      (r n ^ 78 * pairL f g (r n) ^ 182 * Real.log (r n))) atTop atTop) :
    Tendsto (fun n => selectedBranchParameter (r n) (R n) (M n) ^ 26 *
      Real.log (r n) / pairT f g (r n)) atTop (𝓝 0) := by
  let K : ℝ := (1000000 * (3 : ℝ) ^ 7 * (1 + C) ^ 3) ^ 26
  have hsmall : Tendsto (fun n => r n ^ 78 * pairL f g (r n) ^ 182 * Real.log (r n) /
      pairT f g (r n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, inv_div] using tendsto_inv_atTop_zero.comp hratio
  have hlim : Tendsto (fun n => K * (r n ^ 78 * pairL f g (r n) ^ 182 * Real.log (r n) /
      pairT f g (r n))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hsmall.const_mul K
  apply squeeze_zero' _ _ hlim
  · apply Eventually.of_forall
    intro n
    have hr1 : 1 ≤ r n := by linarith [hr2 n]
    have ht : 0 ≤ pairT f g (r n) := le_max_of_le_left
      (show 0 ≤ charT f (r n) from ValueDistribution.characteristic_nonneg hr1)
    exact div_nonneg (mul_nonneg (pow_nonneg (by
      have hLp : 0 < pairL f g (r n) := by linarith [hL n]
      have hrr : r n < R n := by
        have hpos : 0 < 1 / (2 * pairL f g (r n)) := by positivity
        linarith [hlo n]
      exact (by linarith : (0 : ℝ) ≤ r n).trans
        (selectedBranchParameter_ge_radius hr1 hrr (hM n))) _) (Real.log_nonneg hr1)) ht
  · apply Eventually.of_forall
    intro n
    have hr1 : 1 ≤ r n := by linarith [hr2 n]
    have ht : 0 ≤ pairT f g (r n) := le_max_of_le_left
      (show 0 ≤ charT f (r n) from ValueDistribution.characteristic_nonneg hr1)
    have hb := selectedBranchParameter_pow26_le hr1 (hL n) hC (hM n) (hMC n) (hlo n) (hhi n)
    have hbd := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hb (Real.log_nonneg hr1)) ht
    simpa only [K, mul_assoc, mul_div_assoc] using hbd

end ThreeIM
