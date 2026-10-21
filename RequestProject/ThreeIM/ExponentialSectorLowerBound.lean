module

public import RequestProject.ThreeIM.ExponentialSectorArc
public import RequestProject.ThreeIM.ExponentialSectorGeometry
public import RequestProject.ThreeIM.ExponentialSectorAnnuli

/-!
# Exponential identities exclude bounded dilates on a right-hand disk

This is the angular-integration part of Lemma 8.5.  An exact identity
`A D = κ exp` and a bound on `A` force a linear proximity lower bound on
every radius in expanding annuli.  A logarithmic estimate outside a set
of finite measure gives a contradiction.  The fixed angular interval is
constructed from the disk, with no angular or nonexceptional-radius
assumption added to the conclusion.
-/

@[expose] public section

open Filter Set Topology Real Complex Metric ValueDistribution

namespace ThreeIM

theorem log_lower_of_product_exp {κ A D t : ℂ} {M : ℝ}
    (hκ : κ ≠ 0) (hM : 0 < M) (hA : ‖A‖ ≤ M)
    (hAD : A * D = κ * Complex.exp t) :
    t.re + Real.log ‖κ‖ - Real.log M ≤ log⁺ ‖D‖ := by
  have hk : 0 < ‖κ‖ := norm_pos_iff.mpr hκ
  have hD : D ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hAD
    exact (mul_ne_zero hκ (Complex.exp_ne_zero t)) hAD.symm
  have hd : 0 < ‖D‖ := norm_pos_iff.mpr hD
  have heq := congrArg norm hAD
  simp only [norm_mul, Complex.norm_exp] at heq
  have hnorm : ‖κ‖ * Real.exp t.re ≤ M * ‖D‖ := by
    rw [← heq]
    exact mul_le_mul_of_nonneg_right hA (norm_nonneg D)
  have hlog := Real.log_le_log (by positivity : 0 < ‖κ‖ * Real.exp t.re) hnorm
  rw [Real.log_mul (ne_of_gt hk) (Real.exp_ne_zero _), Real.log_exp,
    Real.log_mul (ne_of_gt hM) (ne_of_gt hd)] at hlog
  have hpos : Real.log ‖D‖ ≤ log⁺ ‖D‖ := le_max_right _ _
  linarith

theorem eventually_linear_log_lower_of_product_exp {κ : ℂ} (hκ : κ ≠ 0)
    {M σ : ℝ} (hM : 0 < M) (hσ : 0 < σ)
    {r : ℕ → ℝ} (hr : Tendsto r atTop atTop) :
    ∀ᶠ n in atTop, ∀ A D t : ℂ, σ * r n ≤ t.re → ‖A‖ ≤ M →
      A * D = κ * Complex.exp t → (σ / 2) * r n ≤ log⁺ ‖D‖ := by
  have hg := (hr.const_mul_atTop (show 0 < σ / 2 by positivity)).eventually
    (eventually_ge_atTop (Real.log M - Real.log ‖κ‖))
  filter_upwards [hg] with n hn
  intro A D t ht hA hAD
  have hb := log_lower_of_product_exp hκ hM hA hAD
  linarith

theorem circleMap_scale_radius (r ρ θ : ℝ) :
    (r : ℂ) * circleMap 0 ρ θ = circleMap 0 (r * ρ) θ := by
  simp only [circleMap, zero_add, ofReal_mul]
  ring

theorem false_of_exp_identity_bounded_on_dilates
    {D A : ℂ → ℂ} (hD : Meromorphic D) {κ : ℂ} (hκ : κ ≠ 0)
    {C M : ℝ} (hM : 0 < M)
    (hupper : OutsideFiniteMeasure fun ρ => proximity D ⊤ ρ ≤ C * Real.log (Real.exp 1 + ρ))
    {z : ℂ} (hz : 0 < z.re) {ε : ℝ} (hε : 0 < ε)
    {r : ℕ → ℝ} (hr : Tendsto r atTop atTop)
    (hbound : ∀ᶠ n in atTop, ∀ ζ ∈ ball z ε, ‖A ((r n : ℂ) * ζ)‖ ≤ M)
    (hid : ∀ᶠ n in atTop, ∀ ζ ∈ ball z ε,
      A ((r n : ℂ) * ζ) * D ((r n : ℂ) * ζ) = κ * Complex.exp ((r n : ℂ) * ζ)) :
    False := by
  obtain ⟨α, β, u, v, hα, hαβ, hu, huv, hv, hrect⟩ :=
    exists_annular_sector_in_ball hz hε
  let σ : ℝ := z.re / 2
  have hσ : 0 < σ := by dsimp [σ]; positivity
  let c : ℝ := (σ / 2) * (v - u) / (2 * π)
  have hvu : 0 < v - u := sub_pos.mpr huv
  have hc : 0 < c := by dsimp [c]; positivity
  apply false_of_log_upper_and_linear_annulus_lower hupper hα hαβ hc hr
  filter_upwards [hbound, hid, hr.eventually (eventually_gt_atTop (0 : ℝ)),
    eventually_linear_log_lower_of_product_exp hκ hM hσ hr]
    with n hnBound hnId hrn hnLog
  intro R hRlo hRhi
  have hRα : α ≤ R / r n := (le_div_iff₀ hrn).mpr hRlo
  have hRβ : R / r n ≤ β := (div_le_iff₀ hrn).mpr hRhi
  have hscale (θ : ℝ) : (r n : ℂ) * circleMap 0 (R / r n) θ = circleMap 0 R θ := by
    rw [circleMap_scale_radius, mul_div_cancel₀ _ (ne_of_gt hrn)]
  have hlog : ∀ θ ∈ Icc u v, (σ / 2) * r n ≤ log⁺ ‖D (circleMap 0 R θ)‖ := by
    intro θ hθ
    obtain ⟨hball, hre⟩ := hrect (R / r n) ⟨hRα, hRβ⟩ θ hθ
    have hRe : σ * r n ≤ ((r n : ℂ) * circleMap 0 (R / r n) θ).re := by
      simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
      have hh := mul_le_mul_of_nonneg_left hre.le hrn.le
      dsimp only [σ] at *
      nlinarith
    have hl := hnLog (A ((r n : ℂ) * circleMap 0 (R / r n) θ))
      (D ((r n : ℂ) * circleMap 0 (R / r n) θ))
      ((r n : ℂ) * circleMap 0 (R / r n) θ) hRe (hnBound _ hball) (hnId _ hball)
    simpa only [hscale] using hl
  have hp := proximity_ge_arc_bound hD hu huv.le hv hlog
  calc
    c * r n = ((σ / 2) * r n) * (v - u) / (2 * π) := by dsimp [c]; ring
    _ ≤ proximity D ⊤ R := hp

end ThreeIM
