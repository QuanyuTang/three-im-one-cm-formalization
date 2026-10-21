module

public import RequestProject.ThreeIM.TransportInitialCoordinates

/-!
# The initial analytic bootstrap bounds follow from the actual model

First choose a fixed sufficiently large real starting point. The stable
model is close to 2 alpha there and exp(-a) is small. Local uniform
convergence then supplies both initial coordinate bounds and analyticity.
-/

@[expose] public section

open Filter Set Metric Topology

namespace ThreeIM

set_option autoImplicit false

theorem norm_transport_initial_model_error (α : ℂ) (a : ℝ) :
    ‖2 * α * (1 - Complex.exp (-(a : ℂ) / 2)) - 2 * α‖ =
      ‖2 * α‖ * Real.exp (-a / 2) := by
  have he : 2 * α * (1 - Complex.exp (-(a : ℂ) / 2)) - 2 * α =
      -(2 * α) * Complex.exp (-(a : ℂ) / 2) := by ring
  rw [he, norm_mul, norm_neg, Complex.norm_exp]
  simp

theorem TransportTangentConvergence.exists_initial_analytic_bounds
    {F G : ℕ → ℂ → ℂ} {ε : ℕ → ℝ} {c α : ℂ}
    (h : TransportTangentConvergence F G ε c α)
    {r₀ b₀ θ₀ : ℝ} (hr₀ : 0 < r₀) (hb₀ : 0 < b₀) (hθ₀ : 0 < θ₀) :
    ∃ a : ℝ, 1 ≤ a ∧ Real.exp (-a) ≤ θ₀ ∧ ∀ᶠ n in atTop,
      AnalyticAt ℂ (transportInitialW (F n) (G n) c (ε n)) (a : ℂ) ∧
      AnalyticAt ℂ (transportInitialH (F n) (G n) c (ε n)) (a : ℂ) ∧
      ‖transportInitialW (F n) (G n) c (ε n) (a : ℂ) - 2 * α‖ ≤ r₀ / 4 ∧
      ‖transportInitialH (F n) (G n) c (ε n) (a : ℂ)‖ ≤ b₀ / 2 := by
  have hdiv : Tendsto (fun t : ℝ => t / 2) atTop atTop :=
    tendsto_id.atTop_div_const (by norm_num)
  have hdec : Tendsto (fun t : ℝ => Real.exp (-t / 2)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_div] using Real.tendsto_exp_neg_atTop_nhds_zero.comp hdiv
  have herr : Tendsto (fun t : ℝ => ‖2 * α‖ * Real.exp (-t / 2)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := ‖2 * α‖)).mul hdec
  obtain ⟨a, ha, hθ, he⟩ := ((eventually_ge_atTop (1 : ℝ)).and
    ((Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds hθ₀)).and
      (herr.eventually (gt_mem_nhds (show (0 : ℝ) < r₀ / 8 by positivity))))).exists
  let M : ℂ := 2 * α * (1 - Complex.exp (-(a : ℂ) / 2))
  have hM : ‖M - 2 * α‖ < r₀ / 8 := by
    dsimp only [M]
    rw [norm_transport_initial_model_error]
    exact he
  have hWp : Tendsto (fun n => transportInitialW (F n) (G n) c (ε n) (a : ℂ))
      atTop (𝓝 M) := h.initialW_converges.tendsto_at (mem_univ (a : ℂ))
  have hHp := h.initialH_converges.tendsto_at (mem_univ (a : ℂ))
  have hWclose := Metric.tendsto_nhds.mp hWp (r₀ / 8) (by positivity)
  have hHclose := Metric.tendsto_nhds.mp hHp (b₀ / 2) (by positivity)
  let R : ℝ := ‖(a : ℂ)‖ + 1
  have hR : 0 < R := by dsimp only [R]; positivity
  have haR : (a : ℂ) ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff]
    dsimp only [R]
    linarith
  refine ⟨a, ha, hθ.le, ?_⟩
  filter_upwards [h.initial_holomorphic hR, hWclose, hHclose] with n hn hnW hnH
  refine ⟨hn.1.analyticOnNhd isOpen_ball _ haR,
    hn.2.analyticOnNhd isOpen_ball _ haR, ?_, ?_⟩
  · have hWdist : ‖transportInitialW (F n) (G n) c (ε n) (a : ℂ) - M‖ < r₀ / 8 := by
      simpa only [dist_eq_norm] using hnW
    calc
      ‖transportInitialW (F n) (G n) c (ε n) (a : ℂ) - 2 * α‖ =
        ‖(transportInitialW (F n) (G n) c (ε n) (a : ℂ) - M) + (M - 2 * α)‖ := by
          congr 1
          ring
      _ ≤ ‖transportInitialW (F n) (G n) c (ε n) (a : ℂ) - M‖ + ‖M - 2 * α‖ :=
        norm_add_le _ _
      _ ≤ r₀ / 4 := by linarith
  · have hHdist : ‖transportInitialH (F n) (G n) c (ε n) (a : ℂ)‖ < b₀ / 2 := by
      simpa only [dist_zero_right] using hnH
    exact hHdist.le

end ThreeIM
