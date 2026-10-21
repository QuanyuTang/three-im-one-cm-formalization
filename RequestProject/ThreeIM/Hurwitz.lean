module

public import RequestProject.ThreeIM.Basic

/-!
# Persistence of an omitted value under holomorphic convergence

The local Hurwitz argument uses the maximum modulus principle for reciprocals.
A finite, nonzero analytic germ has a small circle avoiding its zeros. Uniform
convergence bounds the reciprocals on that circle and hence at the center.
-/

@[expose] public section

open Filter Set Metric Topology

namespace ThreeIM

/-- A uniformly convergent sequence of zero-free holomorphic maps cannot
acquire a zero at a point where its analytic limit has a nonzero germ. -/
theorem uniform_limit_ne_zero_of_finite_germ {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    {z : ℂ} {R : ℝ} (hR : 0 < R)
    (hF : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) (ball z R) ∧
      ContinuousOn (F n) (closedBall z R) ∧ ∀ w ∈ closedBall z R, F n w ≠ 0)
    (hconv : TendstoUniformlyOn F f atTop (closedBall z R))
    (hf : AnalyticAt ℂ f z) (hfinite : meromorphicOrderAt f z ≠ ⊤) :
    f z ≠ 0 := by
  have hnz : ∀ᶠ w in 𝓝[≠] z, f w ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hf.meromorphicAt).1 hfinite
  obtain ⟨ρ, hρ, hρa, hρnz⟩ : ∃ ρ > 0,
      AnalyticOnNhd ℂ f (closedBall z ρ) ∧
        ∀ w ∈ closedBall z ρ, w ≠ z → f w ≠ 0 := by
    obtain ⟨ρ, hρ, hball⟩ := nhds_basis_closedBall.mem_iff.mp
      (hf.eventually_analyticAt.and (eventually_nhdsWithin_iff.mp hnz))
    refine ⟨ρ, hρ, ?_, ?_⟩
    · intro w hw
      exact (hball hw).1
    · intro w hw hwz
      exact (hball hw).2 (by simpa only [mem_compl_iff, mem_singleton_iff] using hwz)
  let r : ℝ := min ρ R
  have hr : 0 < r := lt_min hρ hR
  have hrρ : closedBall z r ⊆ closedBall z ρ := closedBall_subset_closedBall (min_le_left _ _)
  have hrR : closedBall z r ⊆ closedBall z R := closedBall_subset_closedBall (min_le_right _ _)
  have hcircle : (sphere z r).Nonempty := NormedSpace.sphere_nonempty.mpr hr.le
  have hfc : ContinuousOn (fun w => ‖f w‖) (sphere z r) :=
    (hρa.continuousOn.mono (sphere_subset_closedBall.trans hrρ)).norm
  obtain ⟨x, hx, hxmin⟩ := (isCompact_sphere z r).exists_isMinOn hcircle hfc
  have hM : 0 < ‖f x‖ := norm_pos_iff.2
    (hρnz x (hrρ (sphere_subset_closedBall hx)) (ne_of_mem_sphere hx hr.ne'))
  have hboundary : ∀ᶠ n in atTop, ∀ w ∈ sphere z r,
      ‖f x‖ / 2 ≤ ‖F n w‖ := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv (‖f x‖ / 2) (half_pos hM)]
      with n hn w hw
    have hclose := hn w (hrR (sphere_subset_closedBall hw))
    have hmin : ‖f x‖ ≤ ‖f w‖ := hxmin hw
    have hnorm := norm_sub_norm_le (f w) (F n w)
    rw [dist_eq_norm] at hclose
    linarith
  have hcenter : ∀ᶠ n in atTop, ‖f x‖ / 2 ≤ ‖F n z‖ := by
    filter_upwards [hF, hboundary] with n hn hb
    have hFn : DiffContOnCl ℂ (F n) (ball z r) := by
      refine ⟨hn.1.mono (ball_subset_ball (min_le_right _ _)), ?_⟩
      rw [closure_ball z hr.ne']
      exact hn.2.1.mono hrR
    have hnz' : ∀ w ∈ closure (ball z r), F n w ≠ 0 := by
      rw [closure_ball z hr.ne']
      exact fun w hw => hn.2.2 w (hrR hw)
    have hInv : ∀ w ∈ frontier (ball z r), ‖(F n w)⁻¹‖ ≤ (‖f x‖ / 2)⁻¹ := by
      intro w hw
      have hws : w ∈ sphere z r := by simpa only [frontier_ball z hr.ne'] using hw
      rw [norm_inv]
      exact inv_anti₀ (half_pos hM) (hb w hws)
    have hmax : ‖(F n z)⁻¹‖ ≤ (‖f x‖ / 2)⁻¹ :=
      Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
        (hFn.inv hnz') hInv (subset_closure (mem_ball_self hr))
    rw [norm_inv] at hmax
    exact (inv_le_inv₀ (norm_pos_iff.2 (hn.2.2 z (mem_closedBall_self hR.le)))
      (half_pos hM)).1 hmax
  have hlim : Tendsto (fun n => ‖F n z‖) atTop (𝓝 ‖f z‖) :=
    (hconv.tendsto_at (mem_closedBall_self hR.le)).norm
  have hpos : ‖f x‖ / 2 ≤ ‖f z‖ := ge_of_tendsto hlim hcenter
  intro hz
  rw [hz, norm_zero] at hpos
  linarith

/-- The local form for locally uniform convergence on any open domain. -/
theorem locallyUniform_limit_ne_zero_of_finite_germ {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    {U : Set ℂ} (hU : IsOpen U)
    (hF : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) U ∧ ∀ w ∈ U, F n w ≠ 0)
    (hconv : TendstoLocallyUniformlyOn F f atTop U) {z : ℂ} (hz : z ∈ U)
    (hfinite : meromorphicOrderAt f z ≠ ⊤) : f z ≠ 0 := by
  have hfd : DifferentiableOn ℂ f U :=
    hconv.differentiableOn (hF.mono fun _ h => h.1) hU
  obtain ⟨R, hR, hRU⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hz)
  apply uniform_limit_ne_zero_of_finite_germ hR
  · filter_upwards [hF] with n hn
    exact ⟨hn.1.mono (ball_subset_closedBall.trans hRU),
      hn.1.continuousOn.mono hRU, fun w hw => hn.2 w (hRU hw)⟩
  · exact (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hconv
      (closedBall z R) hRU (isCompact_closedBall z R)
  · exact hfd.analyticAt (hU.mem_nhds hz)
  · exact hfinite

/-- Hurwitz's omitted-zero dichotomy. On an open preconnected domain a
locally uniform limit of eventually zero-free holomorphic maps either omits
zero or is identically zero. -/
theorem hurwitz_zero_free {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hpre : IsPreconnected U)
    (hF : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) U ∧ ∀ w ∈ U, F n w ≠ 0)
    (hconv : TendstoLocallyUniformlyOn F f atTop U) :
    (∀ z ∈ U, f z ≠ 0) ∨ EqOn f (fun _ => 0) U := by
  classical
  by_cases hzero : EqOn f (fun _ => 0) U
  · exact Or.inr hzero
  · refine Or.inl fun z hz => ?_
    have hfd : DifferentiableOn ℂ f U :=
      hconv.differentiableOn (hF.mono fun _ h => h.1) hU
    apply locallyUniform_limit_ne_zero_of_finite_germ hU hF hconv hz
    intro htop
    have hpunct : f =ᶠ[𝓝[≠] z] (fun _ => 0) := by
      filter_upwards [meromorphicOrderAt_eq_top_iff.1 htop] with w hw
      simpa only [sub_zero] using hw
    have ha : AnalyticAt ℂ f z := hfd.analyticAt (hU.mem_nhds hz)
    have heq : f =ᶠ[𝓝 z] (fun _ => 0) :=
      (ha.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE continuousAt_const).1 hpunct
    apply hzero
    exact (hfd.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq
      analyticOnNhd_const hpre hz heq

end ThreeIM
