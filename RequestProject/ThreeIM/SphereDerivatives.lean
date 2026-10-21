module

public import RequestProject.ThreeIM.SphereLimits

/-! # Spherical and finite-chart derivative limits with eventual holomorphy -/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

theorem tendsto_sphericalDeriv_of_eventually {F : ℕ → ℂ → OnePoint ℂ}
    {G : ℂ → OnePoint ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : ∀ᶠ n in atTop, SphereHolomorphicOn (F n) U)
    (hconv : TendstoLocallyUniformlyOn F G atTop U)
    {z : ℂ} (hz : z ∈ U) :
    Tendsto (fun n => sphericalDeriv (F n) z) atTop (𝓝 (sphericalDeriv G z)) := by
  classical
  have hG := sphereHolomorphicOn_of_eventually hU hF hconv
  let F' (n : ℕ) : ℂ → OnePoint ℂ := if SphereHolomorphicOn (F n) U then F n else G
  have heq : F' =ᶠ[atTop] F := hF.mono fun n hn => by simp only [F', if_pos hn]
  have hF' : ∀ n, SphereHolomorphicOn (F' n) U := by
    intro n
    dsimp only [F']
    split_ifs with hn
    · exact hn
    · exact hG
  have hc' : TendstoLocallyUniformlyOn F' G atTop U :=
    hconv.congr_inseparable (heq.mono fun n hn x _ => .of_eq (congrFun hn x).symm)
  have hd := tendsto_sphericalDeriv_of_tendstoLocallyUniformlyOn hU hF' hc' hz
  exact hd.congr' (heq.mono fun n hn => congrArg (fun H => sphericalDeriv H z) hn)

theorem exists_finite_chart_deriv_convergence_eventually {F : ℕ → ℂ → OnePoint ℂ}
    {G : ℂ → OnePoint ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : ∀ᶠ n in atTop, SphereHolomorphicOn (F n) U)
    (hconv : TendstoLocallyUniformlyOn F G atTop U)
    {z : ℂ} (hz : z ∈ U) (hne : G z ≠ OnePoint.infty) :
    ∃ r : ℝ, 0 < r ∧ closedBall z r ⊆ U ∧
      (∀ w ∈ closedBall z r, G w ≠ OnePoint.infty) ∧
      (∀ᶠ n in atTop, ∀ w ∈ closedBall z r, F n w ≠ OnePoint.infty) ∧
      (∀ᶠ n in atTop, DifferentiableOn ℂ (fun w => chartFiniteMap (F n w)) (ball z r)) ∧
      TendstoLocallyUniformlyOn (fun n => deriv (fun w => chartFiniteMap (F n w)))
        (deriv (fun w => chartFiniteMap (G w))) atTop (ball z r) := by
  obtain ⟨r, hr, hrU, hGf, hFf, hFd, hc⟩ :=
    exists_finite_chart_convergence_eventually hU hF hconv hz hne
  exact ⟨r, hr, hrU, hGf, hFf, hFd,
    (hc.tendstoLocallyUniformlyOn.mono ball_subset_closedBall).deriv hFd isOpen_ball⟩

end ThreeIM
