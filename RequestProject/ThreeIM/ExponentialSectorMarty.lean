module

public import RequestProject.ThreeIM.SphereDerivatives
public import RequestProject.ThreeIM.SphereHolomorphicBridge

/-!
# The local derivative bound for a normal spherical family

The finite-chart formulas and locally uniform derivative convergence also
apply at moving centers. This supplies the direction of Marty's criterion
needed for the sector estimate, with no sharing or exponential hypothesis.
-/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

theorem sphericalDeriv_eq_chartFiniteMap {F : ℂ → OnePoint ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hF : SphereHolomorphicOn F U) {z : ℂ} (hz : z ∈ U)
    (hne : F z ≠ OnePoint.infty) :
    sphericalDeriv F z =
      2 * ‖deriv (fun w => chartFiniteMap (F w)) z‖ / (1 + ‖chartFiniteMap (F z)‖ ^ 2) := by
  have hc : ContinuousAt F z := hF.continuousOn.continuousAt (hU.mem_nhds hz)
  have heq : ∀ᶠ w in 𝓝 z, F w = ((chartFiniteMap (F w) : ℂ) : OnePoint ℂ) := by
    filter_upwards [hc.eventually_ne hne] with w hw
    cases hval : F w with
    | infty => exact (hw hval).elim
    | coe c => rfl
  exact sphericalDeriv_eq_of_eventuallyEq_coe heq
    (analyticAt_chartFiniteMap_of_ne_infty hF hz hne).differentiableAt

theorem tendsto_sphericalDeriv_at_moving {F : ℕ → ℂ → OnePoint ℂ}
    {G : ℂ → OnePoint ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : ∀ᶠ n in atTop, SphereHolomorphicOn (F n) U)
    (hconv : TendstoLocallyUniformlyOn F G atTop U)
    {z : ℂ} (hz : z ∈ U) {w : ℕ → ℂ} (hw : Tendsto w atTop (𝓝 z)) :
    Tendsto (fun n => sphericalDeriv (F n) (w n)) atTop (𝓝 (sphericalDeriv G z)) := by
  have hG := sphereHolomorphicOn_of_eventually hU hF hconv
  have finite_case : ∀ (Fn : ℕ → ℂ → OnePoint ℂ) (g : ℂ → OnePoint ℂ),
      (∀ᶠ n in atTop, SphereHolomorphicOn (Fn n) U) →
      TendstoLocallyUniformlyOn Fn g atTop U → g z ≠ OnePoint.infty →
      Tendsto (fun n => sphericalDeriv (Fn n) (w n)) atTop (𝓝 (sphericalDeriv g z)) := by
    intro Fn g hFn hcfg hgz
    have hg := sphereHolomorphicOn_of_eventually hU hFn hcfg
    obtain ⟨r, hr, hrU, _, hfin, hdiff, hchart⟩ :=
      exists_finite_chart_convergence_eventually hU hFn hcfg hz hgz
    have hloc := hchart.tendstoLocallyUniformlyOn.mono ball_subset_closedBall
    have hdloc := hloc.deriv hdiff isOpen_ball
    have hwa : Tendsto w atTop (𝓝[ball z r] z) := by
      rw [nhdsWithin_eq_nhds.mpr (isOpen_ball.mem_nhds (mem_ball_self hr))]
      exact hw
    have hga := analyticAt_chartFiniteMap_of_ne_infty hg hz hgz
    have hval := hloc.tendsto_comp hga.continuousAt.continuousWithinAt (mem_ball_self hr) hwa
    have hder := hdloc.tendsto_comp hga.deriv.continuousAt.continuousWithinAt (mem_ball_self hr) hwa
    have hform : ∀ᶠ n in atTop, sphericalDeriv (Fn n) (w n) =
        2 * ‖deriv (fun x => chartFiniteMap (Fn n x)) (w n)‖ /
          (1 + ‖chartFiniteMap (Fn n (w n))‖ ^ 2) := by
      filter_upwards [hFn, hfin, hw.eventually (ball_mem_nhds z hr)] with n hn hnf hnw
      exact sphericalDeriv_eq_chartFiniteMap hU hn (hrU (ball_subset_closedBall hnw))
        (hnf (w n) (ball_subset_closedBall hnw))
    have hlim := (hder.norm.const_mul 2).div ((hval.norm.pow 2).const_add 1) (by positivity)
    rw [← sphericalDeriv_eq_chartFiniteMap hU hg hz hgz] at hlim
    exact hlim.congr' (hform.mono fun n hn => hn.symm)
  by_cases hne : G z ≠ OnePoint.infty
  · exact finite_case F G hF hconv hne
  · have hzi : G z = OnePoint.infty := not_ne_iff.mp hne
    have hFi : ∀ᶠ n in atTop, SphereHolomorphicOn (fun x => inversionGL • F n x) U :=
      hF.mono fun n hn => hn.gl_smul inversionGL
    have huc : UniformContinuous (fun p : OnePoint ℂ => inversionGL • p) :=
      CompactSpace.uniformContinuous_of_continuous (continuous_gl_smul inversionGL)
    have hci := huc.comp_tendstoLocallyUniformlyOn hconv
    have hgi : inversionGL • G z ≠ OnePoint.infty := by
      rw [hzi, inversionGL_smul_infty]
      exact OnePoint.coe_ne_infty 0
    have hi := finite_case (fun n x => inversionGL • F n x)
      (fun x => inversionGL • G x) hFi hci hgi
    rw [sphericalDeriv_inversionGL_smul G z] at hi
    exact hi.congr fun n => sphericalDeriv_inversionGL_smul (F n) (w n)

theorem exists_sphericalDeriv_bound_of_isNormalAt {𝓕 : Set (ℂ → OnePoint ℂ)}
    {U : Set ℂ} (hU : IsOpen U) (hol : ∀ F ∈ 𝓕, SphereHolomorphicOn F U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hnormal : IsNormalAt 𝓕 z₀) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ M : ℝ,
      ∀ F ∈ 𝓕, ∀ z ∈ ball z₀ ε, sphericalDeriv F z ≤ M := by
  classical
  by_contra hbad
  push_neg at hbad
  have hsel (n : ℕ) : ∃ F ∈ 𝓕, ∃ z ∈ ball z₀ (1 / ((n : ℝ) + 1)),
      (n : ℝ) < sphericalDeriv F z := by
    exact hbad (1 / ((n : ℝ) + 1)) (by positivity) (n : ℝ)
  choose F hF z hz hd using hsel
  have hzconv : Tendsto z atTop (𝓝 z₀) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun n => dist_nonneg) (fun n => (mem_ball.mp (hz n)).le)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨V, hVz, hNV⟩ := hnormal
  obtain ⟨W, hWsub, hWo, hzW⟩ :=
    _root_.mem_nhds_iff.mp (inter_mem (hU.mem_nhds hz₀) hVz)
  obtain ⟨ψ, hψ, g, hc⟩ := (hNV.mono fun _ hw => (hWsub hw).2)
    (fun n => ⟨F n, hF n⟩)
  have hhol : ∀ᶠ n in atTop, SphereHolomorphicOn (F (ψ n)) W :=
    Eventually.of_forall fun n => sphereHolomorphicOn_mono (hol _ (hF (ψ n)))
      hWo (fun _ hw => (hWsub hw).1)
  have hlim := tendsto_sphericalDeriv_at_moving hWo hhol hc hzW
    (hzconv.comp hψ.tendsto_atTop)
  have hbound : ∀ᶠ n in atTop, sphericalDeriv (F (ψ n)) (z (ψ n)) < sphericalDeriv g z₀ + 1 :=
    hlim.eventually (eventually_lt_nhds (lt_add_one (sphericalDeriv g z₀)))
  have hnat : ∀ᶠ n : ℕ in atTop, sphericalDeriv g z₀ + 1 < (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop _)
  obtain ⟨n, hbn, hnn⟩ := (hbound.and hnat).exists
  have hψn : (n : ℝ) ≤ (ψ n : ℝ) := by exact_mod_cast hψ.id_le n
  have hlarge := hd (ψ n)
  linarith

end ThreeIM
