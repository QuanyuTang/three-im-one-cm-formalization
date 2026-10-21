module

public import RequestProject.ThreeIM.AffineCovariance
public import RequestProject.ThreeIM.SphereRescaling
public import RequestProject.ThreeIM.LocallyUniformCongruence

/-!
# Honest spherical convergence after affine rescaling

Original sphere maps and sphere germs of their raw affine composites agree
only on the eventual source domain. Local eventual congruence gives the
correct compact convergence without asserting equality on the whole plane.
-/

@[expose] public section

open Filter Set Metric Topology

namespace ThreeIM

theorem spherical_affine_limits {F : ℕ → ℂ → ℂ} {H : ℂ → OnePoint ℂ}
    {U : Set ℂ} (hU : IsOpen U) (hF : ∀ n, MeromorphicOn (F n) U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) {z : ℕ → ℂ} {ρ : ℕ → ℝ}
    (hz : Tendsto z atTop (𝓝 z₀)) (hρ : Tendsto ρ atTop (𝓝 0))
    (hρne : ∀ n, ρ n ≠ 0)
    (hconv : TendstoLocallyUniformlyOn
      (fun n w => sphereGermValue (F n) (z n + (ρ n : ℂ) * w)) H atTop univ) :
    TendstoLocallyUniformlyOn
      (fun n => sphereGermValue (fun w => F n (z n + (ρ n : ℂ) * w))) H atTop univ := by
  apply tendstoLocallyUniformlyOn_congr_locally_eventually hconv
  intro w _
  let R : ℝ := ‖w‖ + 1
  have hw : w ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff]
    dsimp only [R]
    linarith
  refine ⟨ball 0 R, mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hw), ?_⟩
  filter_upwards [eventually_rescale_closedBall_subset hU hz₀ hz hρ R] with n hn x hx
  exact (sphereGermValue_comp_affine (ρ n : ℂ) (z n) x
    (by exact_mod_cast hρne n) (hF n _ (hn x (ball_subset_closedBall hx)))).symm

end ThreeIM
