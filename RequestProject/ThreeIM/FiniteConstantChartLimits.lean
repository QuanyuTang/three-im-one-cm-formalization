module

public import RequestProject.ThreeIM.SphereLimits

/-! # Whole-disk finite charts at a finite constant spherical limit -/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

set_option autoImplicit false

theorem finite_constant_spherical_limit_eventually_ne_infty
    {F : ℕ → ℂ → OnePoint ℂ} (a : ℂ)
    (hconv : TendstoLocallyUniformlyOn F (fun _ => (a : OnePoint ℂ)) atTop univ)
    (R : ℝ) : ∀ᶠ n in atTop, ∀ z ∈ closedBall (0 : ℂ) R, F n z ≠ OnePoint.infty := by
  have hu := (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp hconv
    (closedBall (0 : ℂ) R) (subset_univ _) (isCompact_closedBall _ _)
  have hδ : 0 < dist (a : OnePoint ℂ) OnePoint.infty := dist_pos.mpr (OnePoint.coe_ne_infty a)
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu _ hδ] with n hn z hz heq
  have hd := hn z hz
  rw [heq] at hd
  exact lt_irrefl _ hd

theorem finite_constant_chart_eventually_holomorphic
    {F : ℕ → ℂ → OnePoint ℂ} (a : ℂ)
    (hseq : ∀ R > 0, ∀ᶠ n in atTop, SphereHolomorphicOn (F n) (ball 0 R))
    (hconv : TendstoLocallyUniformlyOn F (fun _ => (a : OnePoint ℂ)) atTop univ)
    {R : ℝ} (hR : 0 < R) :
    ∀ᶠ n in atTop, DifferentiableOn ℂ (fun z => chartFiniteMap (F n z)) (ball 0 R) := by
  filter_upwards [hseq R hR, finite_constant_spherical_limit_eventually_ne_infty a hconv R]
    with n hn hfin
  exact SphereHolomorphicOn.differentiableOn_chartFiniteMap hn
    (fun z hz => hfin z (ball_subset_closedBall hz))

theorem finite_constant_chart_locallyUniformly
    {F : ℕ → ℂ → OnePoint ℂ} (a : ℂ)
    (hseq : ∀ R > 0, ∀ᶠ n in atTop, SphereHolomorphicOn (F n) (ball 0 R))
    (hconv : TendstoLocallyUniformlyOn F (fun _ => (a : OnePoint ℂ)) atTop univ) :
    TendstoLocallyUniformlyOn (fun n z => chartFiniteMap (F n z)) (fun _ => a) atTop univ := by
  intro e he z _
  let R : ℝ := ‖z‖ + 1
  have hR : 0 < R := by dsimp only [R]; positivity
  have hz : z ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff]
    dsimp only [R]
    linarith
  obtain ⟨r, hr, _, _, _, _, hchart⟩ := exists_finite_chart_convergence_eventually
    isOpen_ball (hseq R hR) (hconv.mono (subset_univ (ball 0 R))) hz (OnePoint.coe_ne_infty a)
  have hc : TendstoLocallyUniformlyOn (fun n w => chartFiniteMap (F n w))
      (fun _ => a) atTop (ball z r) :=
    hchart.tendstoLocallyUniformlyOn.mono ball_subset_closedBall
  obtain ⟨V, hV, hev⟩ := hc e he z (mem_ball_self hr)
  rw [nhdsWithin_eq_nhds.mpr (isOpen_ball.mem_nhds (mem_ball_self hr))] at hV
  exact ⟨V, mem_nhdsWithin_of_mem_nhds hV, hev⟩

end ThreeIM
