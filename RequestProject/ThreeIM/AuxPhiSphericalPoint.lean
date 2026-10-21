module

public import RequestProject.ThreeIM.AuxPhiSphericalDiagonal

/-!
# A diagonal nonconstant spherical limit forces Phi to be locally one

Cancellation of the common difference is performed before taking limits.
The limiting quotient may be a function, rather than a constant. At every
ordinary regular point it equals one. A regular neighborhood then makes it
locally constant, contradicting a hypothesis that its one-points are simple.
-/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

set_option autoImplicit false

theorem auxPhi_spherical_diagonal_limit_eq_one_at_regular
    {F G uₙ vₙ : ℕ → ℂ → ℂ} {H : ℂ → OnePoint ℂ} {φ : ℂ → ℂ}
    (a : Fin 3 → ℂ) (hH : SphereHolomorphicOn H univ)
    (hHnc : ¬ ∃ p : OnePoint ℂ, ∀ z, H z = p)
    (hFconv : TendstoLocallyUniformlyOn (fun n => sphereGermValue (F n)) H atTop univ)
    (hGconv : TendstoLocallyUniformlyOn (fun n => sphereGermValue (G n)) H atTop univ)
    (hRatio : TendstoLocallyUniformlyOn (fun n w => uₙ n w / vₙ n w) φ atTop univ)
    (hloc : ∀ z : ℂ, ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
      ∀ᶠ n in atTop, AuxiliaryPairOn U (F n) (G n) (uₙ n) (vₙ n) a)
    {z₀ : ℂ} (hderiv : deriv (fun w => chartFiniteMap (H w)) z₀ ≠ 0)
    (hP : cubicP a (chartFiniteMap (H z₀)) ≠ 0) : φ z₀ = 1 := by
  let h : ℂ → ℂ := fun z => chartFiniteMap (H z)
  have hfinite : H z₀ ≠ OnePoint.infty :=
    sphere_ne_infty_of_chartFinite_deriv_ne_zero hH hHnc hderiv
  obtain ⟨U, hU, hzU, hseq⟩ := hloc z₀
  have hFH : ∀ᶠ n in atTop, SphereHolomorphicOn (sphereGermValue (F n)) U :=
    hseq.mono fun n hn => sphereHolomorphicOn_sphereGermValue hU hn.pair.nonconst_f.1
  have hGH : ∀ᶠ n in atTop, SphereHolomorphicOn (sphereGermValue (G n)) U :=
    hseq.mono fun n hn => sphereHolomorphicOn_sphereGermValue hU hn.pair.nonconst_g.1
  obtain ⟨rF, hrF, hrFU, _, _, hFd, hcF⟩ := exists_finite_chart_convergence_eventually
    hU hFH (hFconv.mono (subset_univ U)) hzU hfinite
  obtain ⟨rG, hrG, _, _, _, hGd, hcG⟩ := exists_finite_chart_convergence_eventually
    hU hGH (hGconv.mono (subset_univ U)) hzU hfinite
  let r := min rF rG
  let B : Set ℂ := ball z₀ r
  have hr : 0 < r := lt_min hrF hrG
  have hBo : IsOpen B := isOpen_ball
  have hzB : z₀ ∈ B := by simpa only [B, mem_ball, dist_self] using hr
  have hBF : B ⊆ ball z₀ rF := ball_subset_ball (min_le_left rF rG)
  have hBG : B ⊆ ball z₀ rG := ball_subset_ball (min_le_right rF rG)
  have hBU : B ⊆ U := hBF.trans (ball_subset_closedBall.trans hrFU)
  let C : ℕ → ℂ → ℂ := fun n z => chartFiniteMap (sphereGermValue (F n) z)
  let D : ℕ → ℂ → ℂ := fun n z => chartFiniteMap (sphereGermValue (G n) z)
  have hCd : ∀ᶠ n in atTop, DifferentiableOn ℂ (C n) B :=
    hFd.mono fun n hn => hn.mono hBF
  have hDd : ∀ᶠ n in atTop, DifferentiableOn ℂ (D n) B :=
    hGd.mono fun n hn => hn.mono hBG
  have hCc : TendstoLocallyUniformlyOn C h atTop B :=
    hcF.tendstoLocallyUniformlyOn.mono (hBF.trans ball_subset_closedBall)
  have hDc : TendstoLocallyUniformlyOn D h atTop B :=
    hcG.tendstoLocallyUniformlyOn.mono (hBG.trans ball_subset_closedBall)
  have hdata : ∀ᶠ n in atTop, NormalizedPair B (C n) (D n) a ∧
      (auxPhi a (C n) (D n) =ᶠ[codiscreteWithin B] fun w => uₙ n w / vₙ n w) ∧
      ContinuousAt (fun w => uₙ n w / vₙ n w) z₀ := by
    filter_upwards [hseq] with n hn
    have hnB := hn.restrict hBU
    have heF : F n =ᶠ[codiscreteWithin B] C n :=
      chartFinite_sphereGerm_eq_codiscreteWithin hnB.pair.nonconst_f.1
    have heG : G n =ᶠ[codiscreteWithin B] D n :=
      chartFinite_sphereGerm_eq_codiscreteWithin hnB.pair.nonconst_g.1
    have haux := auxiliary_congr_codiscreteWithin hBo heF heG a
    refine ⟨hnB.pair.congr_codiscreteWithin hBo heF heG,
      haux.2.2.2.symm.trans hnB.phi_eq, ?_⟩
    exact (hnB.holo_u.continuousOn.continuousAt (hBo.mem_nhds hzB)).div
      (hnB.holo_v.continuousOn.continuousAt (hBo.mem_nhds hzB)) (hnB.nonzero_v z₀ hzB)
  exact auxPhi_diagonal_limit_eq_one hBo hzB a hCd hDd hCc hDc hderiv hP
    (hdata.mono fun n hn => hn.1) (hdata.mono fun n hn => hn.2.1)
    (hdata.mono fun n hn => hn.2.2) (hRatio.tendsto_at (mem_univ z₀))

theorem auxPhi_spherical_diagonal_limit_impossible_of_simple_ones
    {F G uₙ vₙ : ℕ → ℂ → ℂ} {H : ℂ → OnePoint ℂ} {φ : ℂ → ℂ}
    (a : Fin 3 → ℂ) (hH : SphereHolomorphicOn H univ)
    (hHnc : ¬ ∃ p : OnePoint ℂ, ∀ z, H z = p)
    (hFconv : TendstoLocallyUniformlyOn (fun n => sphereGermValue (F n)) H atTop univ)
    (hGconv : TendstoLocallyUniformlyOn (fun n => sphereGermValue (G n)) H atTop univ)
    (hRatio : TendstoLocallyUniformlyOn (fun n w => uₙ n w / vₙ n w) φ atTop univ)
    (hsimple : ∀ z, φ z = 1 → deriv φ z ≠ 0)
    (hloc : ∀ z : ℂ, ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
      ∀ᶠ n in atTop, AuxiliaryPairOn U (F n) (G n) (uₙ n) (vₙ n) a) : False := by
  have hnc := isNonconstMeroOn_chartFiniteMap hH hHnc
  obtain ⟨z₀, hderiv, hP⟩ := exists_regular_cubic_point hnc a
  have hfinite := sphere_ne_infty_of_chartFinite_deriv_ne_zero hH hHnc hderiv
  have ha := analyticAt_chartFiniteMap_of_ne_infty hH (mem_univ z₀) hfinite
  have hnearD := ha.deriv.continuousAt.eventually_ne hderiv
  have hnearP := ((auxiliary_continuous_cubicP a).continuousAt.comp ha.continuousAt).eventually_ne hP
  have heq : φ =ᶠ[𝓝 z₀] (fun _ => (1 : ℂ)) := by
    filter_upwards [hnearD, hnearP] with w hwD hwP
    exact auxPhi_spherical_diagonal_limit_eq_one_at_regular a hH hHnc hFconv hGconv
      hRatio hloc hwD hwP
  have hzero : deriv φ z₀ = 0 := by simpa only [deriv_const] using heq.deriv_eq
  exact hsimple z₀ heq.eq_of_nhds hzero

end ThreeIM
