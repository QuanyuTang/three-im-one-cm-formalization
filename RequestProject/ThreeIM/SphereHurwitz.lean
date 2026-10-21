module

public import RequestProject.ThreeIM.Hurwitz
public import RequestProject.ThreeIM.SphereHolomorphicBridge
public import RequestProject.ThreeIM.SphereLimits

/-!
# Omitted values of nonconstant spherical limits

Holomorphy and omission are required only eventually near each point, as for
rescaled functions on exhausting disks. Finite-chart convergence and Hurwitz
then preserve an omitted value in a nonconstant entire spherical limit.
-/

@[expose] public section

open Filter Set Metric Topology Matrix NoWanderingDomains

namespace ThreeIM

theorem sphere_limit_omits_zero {F : ℕ → ℂ → OnePoint ℂ} {G : ℂ → OnePoint ℂ}
    (hG : SphereHolomorphicOn G univ)
    (hnc : ¬ ∃ p : OnePoint ℂ, ∀ z, G z = p)
    (hloc : ∀ z : ℂ, ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
      ∀ᶠ n in atTop, SphereHolomorphicOn (F n) U ∧
        ∀ w ∈ U, F n w ≠ ((0 : ℂ) : OnePoint ℂ))
    (hconv : TendstoLocallyUniformlyOn F G atTop univ) :
    ∀ z, G z ≠ ((0 : ℂ) : OnePoint ℂ) := by
  intro z hzero
  obtain ⟨U, hU, hzU, hF⟩ := hloc z
  have hne : G z ≠ OnePoint.infty := by
    rw [hzero]
    exact OnePoint.coe_ne_infty 0
  obtain ⟨r, hr, hrU, _, hfin, hd, hchart⟩ :=
    exists_finite_chart_convergence_eventually hU (hF.mono fun _ h => h.1)
      (hconv.mono (subset_univ U)) hzU hne
  have hdata : ∀ᶠ n in atTop,
      DifferentiableOn ℂ (fun w => chartFiniteMap (F n w)) (ball z r) ∧
        ContinuousOn (fun w => chartFiniteMap (F n w)) (closedBall z r) ∧
        ∀ w ∈ closedBall z r, chartFiniteMap (F n w) ≠ 0 := by
    filter_upwards [hF, hfin, hd] with n hn hnf hnd
    refine ⟨hnd, fun w hw => ?_, fun w hw h0 => ?_⟩
    · exact (analyticAt_chartFiniteMap_of_ne_infty hn.1 (hrU hw) (hnf w hw)).continuousAt.continuousWithinAt
    · apply hn.2 w (hrU hw)
      cases hv : F n w with
      | infty => exact (hnf w hw hv).elim
      | coe c =>
        have hc : c = 0 := by simpa only [hv, chartFiniteMap] using h0
        simp only [hc]
  have hmer := isNonconstMeroOn_chartFiniteMap hG hnc
  have hfinite : meromorphicOrderAt (fun w => chartFiniteMap (G w)) z ≠ ⊤ := by
    simpa only [sub_zero] using hmer.2 z (mem_univ z) 0
  have hnonzero := uniform_limit_ne_zero_of_finite_germ hr hdata hchart
    (analyticAt_chartFiniteMap_of_ne_infty hG (mem_univ z) hne) hfinite
  exact hnonzero (by simp only [hzero, chartFiniteMap])

/-- The same persistence result in any specified Möbius coordinate sending
the omitted target to zero. -/
theorem sphere_limit_omits_of_mobius_zero {F : ℕ → ℂ → OnePoint ℂ}
    {G : ℂ → OnePoint ℂ} {a : OnePoint ℂ} (A : GL (Fin 2) ℂ)
    (hAa : A • a = ((0 : ℂ) : OnePoint ℂ))
    (hG : SphereHolomorphicOn G univ)
    (hnc : ¬ ∃ p : OnePoint ℂ, ∀ z, G z = p)
    (hloc : ∀ z : ℂ, ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
      ∀ᶠ n in atTop, SphereHolomorphicOn (F n) U ∧ ∀ w ∈ U, F n w ≠ a)
    (hconv : TendstoLocallyUniformlyOn F G atTop univ) : ∀ z, G z ≠ a := by
  have hGn : ¬ ∃ p : OnePoint ℂ, ∀ z, A • G z = p := by
    rintro ⟨p, hp⟩
    apply hnc
    exact ⟨G 0, fun z => MulAction.injective A ((hp z).trans (hp 0).symm)⟩
  have hloc' : ∀ z : ℂ, ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
      ∀ᶠ n in atTop, SphereHolomorphicOn (fun w => A • F n w) U ∧
        ∀ w ∈ U, A • F n w ≠ ((0 : ℂ) : OnePoint ℂ) := by
    intro z
    obtain ⟨U, hU, hzU, hF⟩ := hloc z
    refine ⟨U, hU, hzU, hF.mono fun n hn => ⟨hn.1.gl_smul A, ?_⟩⟩
    intro w hw hh
    exact hn.2 w hw (MulAction.injective A (hh.trans hAa.symm))
  have huc : UniformContinuous (fun p : OnePoint ℂ => A • p) :=
    CompactSpace.uniformContinuous_of_continuous (continuous_gl_smul A)
  have hconv' : TendstoLocallyUniformlyOn (fun n w => A • F n w)
      (fun w => A • G w) atTop univ := huc.comp_tendstoLocallyUniformlyOn hconv
  have hzero := sphere_limit_omits_zero (hG.gl_smul A) hGn hloc' hconv'
  intro z hz
  exact hzero z (by rw [hz]; exact hAa)

end ThreeIM
