module

public import RequestProject.ThreeIM.SphereHurwitz

/-!
# Eventual domains of spherical affine rescalings

Centers tending to an interior point and scales tending to zero send every
fixed closed disk into the original domain eventually. This supplies the
local holomorphy and omission hypotheses for spherical Hurwitz.
-/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

theorem eventually_rescale_closedBall_subset {U : Set ℂ} (hU : IsOpen U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) {z : ℕ → ℂ} {ρ : ℕ → ℝ}
    (hz : Tendsto z atTop (𝓝 z₀)) (hρ : Tendsto ρ atTop (𝓝 0)) (R : ℝ) :
    ∀ᶠ n in atTop, ∀ w ∈ closedBall (0 : ℂ) R, z n + (ρ n : ℂ) * w ∈ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU z₀ hz₀
  let M : ℝ := |R| + 1
  have hM : 0 < M := by dsimp only [M]; positivity
  have hzev : ∀ᶠ n in atTop, ‖z n - z₀‖ < ε / 2 := by
    simpa only [mem_ball, dist_eq_norm] using hz.eventually (ball_mem_nhds z₀ (half_pos hε))
  have hρnorm : Tendsto (fun n => ‖(ρ n : ℂ)‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Complex.ofReal_zero, norm_zero] using
      ((Complex.continuous_ofReal.tendsto 0).comp hρ).norm
  have hρev : ∀ᶠ n in atTop, ‖(ρ n : ℂ)‖ < (ε / 2) / M :=
    hρnorm.eventually (gt_mem_nhds (div_pos (half_pos hε) hM))
  filter_upwards [hzev, hρev] with n hnz hnρ w hw
  apply hball
  rw [mem_ball, dist_eq_norm]
  have hwM : ‖w‖ ≤ M :=
    (mem_closedBall_zero_iff.1 hw).trans (by dsimp only [M]; linarith [le_abs_self R])
  have hρM : ‖(ρ n : ℂ)‖ * M < ε / 2 := (lt_div_iff₀ hM).1 hnρ
  calc ‖z n + (ρ n : ℂ) * w - z₀‖ = ‖(z n - z₀) + (ρ n : ℂ) * w‖ := by congr 1; ring
    _ ≤ ‖z n - z₀‖ + ‖(ρ n : ℂ) * w‖ := norm_add_le _ _
    _ = ‖z n - z₀‖ + ‖(ρ n : ℂ)‖ * ‖w‖ := by rw [norm_mul]
    _ ≤ ‖z n - z₀‖ + ‖(ρ n : ℂ)‖ * M := by gcongr
    _ < ε := by linarith

theorem eventually_sphereHolomorphic_rescale {F : ℕ → ℂ → OnePoint ℂ}
    {U : Set ℂ} (hU : IsOpen U) (hF : ∀ n, SphereHolomorphicOn (F n) U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) {z : ℕ → ℂ} {ρ : ℕ → ℝ}
    (hz : Tendsto z atTop (𝓝 z₀)) (hρ : Tendsto ρ atTop (𝓝 0)) (R : ℝ) :
    ∀ᶠ n in atTop, SphereHolomorphicOn (fun w => F n (z n + (ρ n : ℂ) * w))
      (ball (0 : ℂ) R) := by
  filter_upwards [eventually_rescale_closedBall_subset hU hz₀ hz hρ R] with n hn
  exact sphereHolomorphicOn_mono ((hF n).comp_affine (z n) (ρ n : ℂ)) isOpen_ball
    (fun w hw => hn w (ball_subset_closedBall hw))

theorem rescale_locally_eventually_holo_omits {F : ℕ → ℂ → OnePoint ℂ}
    {U : Set ℂ} (hU : IsOpen U) (hF : ∀ n, SphereHolomorphicOn (F n) U)
    {a : OnePoint ℂ} (ha : ∀ n w, w ∈ U → F n w ≠ a)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) {z : ℕ → ℂ} {ρ : ℕ → ℝ}
    (hz : Tendsto z atTop (𝓝 z₀)) (hρ : Tendsto ρ atTop (𝓝 0)) :
    ∀ w : ℂ, ∃ V : Set ℂ, IsOpen V ∧ w ∈ V ∧
      ∀ᶠ n in atTop, SphereHolomorphicOn (fun x => F n (z n + (ρ n : ℂ) * x)) V ∧
        ∀ x ∈ V, F n (z n + (ρ n : ℂ) * x) ≠ a := by
  intro w
  let R : ℝ := ‖w‖ + 1
  refine ⟨ball 0 R, isOpen_ball, ?_, ?_⟩
  · rw [mem_ball_zero_iff]
    dsimp only [R]
    linarith
  · filter_upwards [eventually_sphereHolomorphic_rescale hU hF hz₀ hz hρ R,
      eventually_rescale_closedBall_subset hU hz₀ hz hρ R] with n hn hd
    exact ⟨hn, fun x hx => ha n _ (hd x (ball_subset_closedBall hx))⟩

end ThreeIM
