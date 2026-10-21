module

public import RequestProject.ThreeIM.SphereGlobalNormality
public import RequestProject.ThreeIM.SphereHurwitz
public import RequestProject.ThreeIM.LocallyUniformCongruence

/-!
# Euclidean limits of holomorphic functions with a finite marked value

Holomorphy is needed only eventually on each fixed neighborhood. Hurwitz
excludes poles in a nonconstant spherical limit. A finite marked value
excludes the constant-infinity alternative. Finite-chart convergence then
agrees locally with the original analytic functions themselves.
-/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

set_option autoImplicit false

theorem holomorphic_spherical_limit_is_finite {F : ℕ → ℂ → ℂ}
    {L : ℂ → OnePoint ℂ}
    (hloc : ∀ z : ℂ, ∃ Ω : Set ℂ, IsOpen Ω ∧ z ∈ Ω ∧
      ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) Ω)
    (hconv : TendstoLocallyUniformlyOn (fun n => sphereGermValue (F n)) L atTop univ)
    {z₀ : ℂ} (hz₀ : L z₀ ≠ OnePoint.infty) : ∀ z, L z ≠ OnePoint.infty := by
  classical
  have hlocSphere : ∀ z : ℂ, ∃ Ω : Set ℂ, IsOpen Ω ∧ z ∈ Ω ∧
      ∀ᶠ n in atTop, SphereHolomorphicOn (sphereGermValue (F n)) Ω ∧
        ∀ w ∈ Ω, sphereGermValue (F n) w ≠ OnePoint.infty := by
    intro z
    obtain ⟨Ω, hΩ, hzΩ, hev⟩ := hloc z
    refine ⟨Ω, hΩ, hzΩ, hev.mono fun n hn => ⟨?_, ?_⟩⟩
    · exact sphereHolomorphicOn_sphereGermValue hΩ
        (fun w hw => (hn.analyticOnNhd hΩ w hw).meromorphicAt)
    · intro w hw
      rw [sphereGermValue_eq_coe_of_analytic (hn.analyticOnNhd hΩ w hw)]
      exact OnePoint.coe_ne_infty _
  have hL : SphereHolomorphicOn L univ := sphereHolomorphicOn_univ_of_locally_eventually
    hconv (fun z => by
      obtain ⟨Ω, hΩ, hzΩ, hev⟩ := hlocSphere z
      exact ⟨Ω, hΩ, hzΩ, hev.mono fun n hn => hn.1⟩)
  by_cases hnc : ¬ ∃ p : OnePoint ℂ, ∀ w, L w = p
  · exact sphere_limit_omits_of_mobius_zero inversionGL inversionGL_smul_infty hL hnc
      hlocSphere hconv
  · obtain ⟨p, hp⟩ := not_not.mp hnc
    intro z hz
    apply hz₀
    exact (hp z₀).trans ((hp z).symm.trans hz)

theorem euclidean_limit_of_finite_holomorphic_spherical_limit {F : ℕ → ℂ → ℂ}
    {L : ℂ → OnePoint ℂ}
    (hloc : ∀ z : ℂ, ∃ Ω : Set ℂ, IsOpen Ω ∧ z ∈ Ω ∧
      ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) Ω)
    (hconv : TendstoLocallyUniformlyOn (fun n => sphereGermValue (F n)) L atTop univ)
    {z₀ : ℂ} (hz₀ : L z₀ ≠ OnePoint.infty) :
    Differentiable ℂ (fun w => chartFiniteMap (L w)) ∧
      TendstoLocallyUniformlyOn F (fun w => chartFiniteMap (L w)) atTop univ := by
  have hfinite := holomorphic_spherical_limit_is_finite hloc hconv hz₀
  have hlocSphere : ∀ z : ℂ, ∃ Ω : Set ℂ, IsOpen Ω ∧ z ∈ Ω ∧
      ∀ᶠ n in atTop, SphereHolomorphicOn (sphereGermValue (F n)) Ω := by
    intro z
    obtain ⟨Ω, hΩ, hzΩ, hev⟩ := hloc z
    exact ⟨Ω, hΩ, hzΩ, hev.mono fun n hn => sphereHolomorphicOn_sphereGermValue hΩ
      (fun w hw => (hn.analyticOnNhd hΩ w hw).meromorphicAt)⟩
  have hL := sphereHolomorphicOn_univ_of_locally_eventually hconv hlocSphere
  refine ⟨fun z => (analyticAt_chartFiniteMap_of_ne_infty hL (mem_univ z) (hfinite z)).differentiableAt, ?_⟩
  intro e he z _
  obtain ⟨Ω, hΩ, hzΩ, hFΩ⟩ := hloc z
  have hFs : ∀ᶠ n in atTop, SphereHolomorphicOn (sphereGermValue (F n)) Ω :=
    hFΩ.mono fun n hn => sphereHolomorphicOn_sphereGermValue hΩ
      (fun w hw => (hn.analyticOnNhd hΩ w hw).meromorphicAt)
  obtain ⟨r, hr, hrΩ, _, _, _, hchart⟩ := exists_finite_chart_convergence_eventually
    hΩ hFs (hconv.mono (subset_univ Ω)) hzΩ (hfinite z)
  have hc : TendstoLocallyUniformlyOn
      (fun n w => chartFiniteMap (sphereGermValue (F n) w)) (fun w => chartFiniteMap (L w))
      atTop (ball z r) := hchart.tendstoLocallyUniformlyOn.mono ball_subset_closedBall
  have hraw : TendstoLocallyUniformlyOn F (fun w => chartFiniteMap (L w)) atTop (ball z r) := by
    apply tendstoLocallyUniformlyOn_congr_locally_eventually hc
    intro w _
    refine ⟨ball z r, self_mem_nhdsWithin, ?_⟩
    filter_upwards [hFΩ] with n hn x hx
    change chartFiniteMap (sphereGermValue (F n) x) = F n x
    rw [sphereGermValue_eq_coe_of_analytic (hn.analyticOnNhd hΩ x (hrΩ (ball_subset_closedBall hx)))]
    rfl
  obtain ⟨V, hV, hev⟩ := hraw e he z (mem_ball_self hr)
  rw [nhdsWithin_eq_nhds.mpr (isOpen_ball.mem_nhds (mem_ball_self hr))] at hV
  exact ⟨V, mem_nhdsWithin_of_mem_nhds hV, hev⟩

theorem holomorphic_spherical_limit_of_fixed_value {F : ℕ → ℂ → ℂ}
    {L : ℂ → OnePoint ℂ}
    (hloc : ∀ z : ℂ, ∃ Ω : Set ℂ, IsOpen Ω ∧ z ∈ Ω ∧
      ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) Ω)
    (hconv : TendstoLocallyUniformlyOn (fun n => sphereGermValue (F n)) L atTop univ)
    (z₀ v : ℂ) (hvalue : ∀ᶠ n in atTop, F n z₀ = v) :
    L z₀ = (v : OnePoint ℂ) ∧ Differentiable ℂ (fun w => chartFiniteMap (L w)) ∧
      TendstoLocallyUniformlyOn F (fun w => chartFiniteMap (L w)) atTop univ := by
  obtain ⟨Ω, hΩ, hzΩ, hFΩ⟩ := hloc z₀
  have heq : ∀ᶠ n in atTop, sphereGermValue (F n) z₀ = (v : OnePoint ℂ) := by
    filter_upwards [hFΩ, hvalue] with n hn hnv
    rw [sphereGermValue_eq_coe_of_analytic (hn.analyticOnNhd hΩ z₀ hzΩ), hnv]
  have hL0 : L z₀ = (v : OnePoint ℂ) :=
    tendsto_nhds_unique_of_eventuallyEq (hconv.tendsto_at (mem_univ z₀)) tendsto_const_nhds heq
  exact ⟨hL0, euclidean_limit_of_finite_holomorphic_spherical_limit hloc hconv
    (hL0 ▸ OnePoint.coe_ne_infty v)⟩

end ThreeIM
