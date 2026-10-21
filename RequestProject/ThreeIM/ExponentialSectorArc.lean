module

public import RequestProject.ThreeIM.Basic

/-!
# Proximity lower bounds from a fixed angular arc

Integrating a uniform lower bound on an angular interval yields a lower
bound for the circle average. The complementary angles contribute a
nonnegative amount. This supplies the integration step in Lemma 8.5.
-/

@[expose] public section

open Filter Set Topology Real Complex MeasureTheory ValueDistribution

namespace ThreeIM

theorem circleAverage_ge_arc_bound {H : ℂ → ℝ} {ρ u v M : ℝ}
    (hI : CircleIntegrable H 0 ρ) (hNN : ∀ z, 0 ≤ H z)
    (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 2 * π)
    (hbound : ∀ θ ∈ Icc u v, M ≤ H (circleMap 0 ρ θ)) :
    M * (v - u) / (2 * π) ≤ circleAverage H 0 ρ := by
  have hπ : (0 : ℝ) < 2 * π := by positivity
  have h01 : IntervalIntegrable (fun θ => H (circleMap 0 ρ θ)) volume 0 (2 * π) := hI
  have hsub : uIcc u v ⊆ uIcc 0 (2 * π) := by
    rw [uIcc_of_le huv, uIcc_of_le hπ.le]
    exact Icc_subset_Icc hu hv
  have huvI := h01.mono_set hsub
  have hsmall := intervalIntegral.integral_mono_on huv
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => M) volume u v) huvI hbound
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hsmall
  have hbig := intervalIntegral.integral_mono_interval hu huv hv
    (f := fun θ => H (circleMap 0 ρ θ))
    (Eventually.of_forall fun θ => hNN (circleMap 0 ρ θ)) h01
  have htotal := hsmall.trans hbig
  rw [circleAverage_def, smul_eq_mul]
  calc
    M * (v - u) / (2 * π) = ((v - u) * M) / (2 * π) := by ring
    _ ≤ (∫ θ in (0 : ℝ)..2 * π, H (circleMap 0 ρ θ)) / (2 * π) :=
      div_le_div_of_nonneg_right htotal hπ.le
    _ = _ := by ring

theorem proximity_ge_arc_bound {F : ℂ → ℂ} (hF : Meromorphic F) {ρ u v M : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 2 * π)
    (hbound : ∀ θ ∈ Icc u v, M ≤ log⁺ ‖F (circleMap 0 ρ θ)‖) :
    M * (v - u) / (2 * π) ≤ proximity F ⊤ ρ := by
  rw [proximity_top]
  exact circleAverage_ge_arc_bound
    (circleIntegrable_posLog_norm_meromorphicOn (fun z _ => hF z))
    (fun _ => posLog_nonneg) hu huv hv hbound

end ThreeIM
