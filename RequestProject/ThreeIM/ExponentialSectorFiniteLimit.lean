module

public import RequestProject.ThreeIM.ExponentialSectorBounded
public import RequestProject.ThreeIM.SphereLimits

/-!
# A finite spherical limit gives a bound on one fixed disk

The finite-chart bound is deduced from spherical locally uniform
convergence.  Applying it twice excludes a common finite point of two
spherical limits of exponential dilates.
-/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

theorem eventually_bound_finite_chart_of_sphere_limit
    {S : ℕ → ℂ → OnePoint ℂ} {F : ℂ → OnePoint ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hS : ∀ n, SphereHolomorphicOn (S n) U)
    (hconv : TendstoLocallyUniformlyOn S F atTop U)
    {z : ℂ} (hz : z ∈ U) (hne : F z ≠ OnePoint.infty) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ M : ℝ,
      ∀ᶠ n in atTop, ∀ w ∈ ball z ε, ‖chartFiniteMap (S n w)‖ ≤ M := by
  obtain ⟨ε, hε, hεU, hFfin, _, _, hchart⟩ :=
    exists_finite_chart_convergence hU hS hconv hz hne
  have hF : SphereHolomorphicOn F U :=
    sphereHolomorphicOn_of_eventually hU (Eventually.of_forall hS) hconv
  have hcontinuous : ContinuousOn (fun w => chartFiniteMap (F w)) (closedBall z ε) := by
    intro w hw
    exact (analyticAt_chartFiniteMap_of_ne_infty hF (hεU hw) (hFfin w hw)).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_closedBall z ε).exists_bound_of_continuousOn hcontinuous
  refine ⟨ε, hε, C + 1, ?_⟩
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hchart 1 one_pos] with n hn w hw
  have hw' : w ∈ closedBall z ε := ball_subset_closedBall hw
  have hd : ‖chartFiniteMap (S n w) - chartFiniteMap (F w)‖ < 1 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hn w hw'
  have htriangle := norm_add_le
    (chartFiniteMap (S n w) - chartFiniteMap (F w)) (chartFiniteMap (F w))
  rw [sub_add_cancel] at htriangle
  linarith [hC w hw']

theorem ExponentialPair.spherical_dilate_limit_not_both_finite
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ} (h : ExponentialPair a f g κ)
    {r : ℕ → ℝ} (hr : Tendsto r atTop atTop)
    {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hzU : z ∈ U) (hz : 0 < z.re)
    {F G : ℂ → OnePoint ℂ}
    (hFc : TendstoLocallyUniformlyOn
      (fun n w => sphereGermValue f ((r n : ℂ) * w)) F atTop U)
    (hGc : TendstoLocallyUniformlyOn
      (fun n w => sphereGermValue g ((r n : ℂ) * w)) G atTop U)
    (hFfin : F z ≠ OnePoint.infty) (hGfin : G z ≠ OnePoint.infty) : False := by
  have hfs (n : ℕ) : SphereHolomorphicOn
      (fun w => sphereGermValue f ((r n : ℂ) * w)) U := by
    apply sphereHolomorphicOn_mono _ hU (subset_univ U)
    simpa only [preimage_univ, zero_add] using
      (sphereHolomorphicOn_sphereGermValue isOpen_univ h.pair.nonconst_f.1).comp_affine
        0 (r n : ℂ)
  have hgs (n : ℕ) : SphereHolomorphicOn
      (fun w => sphereGermValue g ((r n : ℂ) * w)) U := by
    apply sphereHolomorphicOn_mono _ hU (subset_univ U)
    simpa only [preimage_univ, zero_add] using
      (sphereHolomorphicOn_sphereGermValue isOpen_univ h.pair.nonconst_g.1).comp_affine
        0 (r n : ℂ)
  obtain ⟨εf, hεf, Mf, hMf⟩ :=
    eventually_bound_finite_chart_of_sphere_limit hU hfs hFc hzU hFfin
  obtain ⟨εg, hεg, Mg, hMg⟩ :=
    eventually_bound_finite_chart_of_sphere_limit hU hgs hGc hzU hGfin
  apply h.not_bounded_canonical_dilates hz (lt_min hεf hεg) hr
  refine ⟨max Mf Mg, ?_⟩
  filter_upwards [hMf, hMg] with n hnf hng w hw
  exact ⟨(hnf w (ball_subset_ball (min_le_left _ _) hw)).trans (le_max_left _ _),
    (hng w (ball_subset_ball (min_le_right _ _) hw)).trans (le_max_right _ _)⟩

end ThreeIM
