module

public import RequestProject.ThreeIM.AuxiliaryPair
public import RequestProject.ThreeIM.AuxPhiDiagonalLimit
public import RequestProject.ThreeIM.RepresentativePairs
public import RequestProject.ThreeIM.SphereLimits

/-!
# Phi at a common nonconstant spherical limit

An ordinary point is selected in the genuine limiting sphere map. The
corrected finite charts of the approximating functions, rather than their
raw values at exceptional points, supply the holomorphic diagonal limit.
-/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

theorem sphere_ne_infty_of_chartFinite_deriv_ne_zero {H : ℂ → OnePoint ℂ}
    (hH : SphereHolomorphicOn H univ)
    (hHnc : ¬ ∃ p : OnePoint ℂ, ∀ z, H z = p) {z : ℂ}
    (hderiv : deriv (fun w => chartFiniteMap (H w)) z ≠ 0) : H z ≠ OnePoint.infty := by
  have hm := meromorphicOn_chartFiniteMap hH z (mem_univ z)
  have hc := (differentiableAt_of_deriv_ne_zero hderiv).continuousAt
  have hlim : Tendsto (fun w => (chartFiniteMap (H w) : OnePoint ℂ))
      (𝓝[≠] z) (𝓝 (chartFiniteMap (H z) : OnePoint ℂ)) :=
    (OnePoint.continuous_coe.tendsto _).comp (hc.tendsto.mono_left nhdsWithin_le_nhds)
  have hvalue := tendsto_nhds_unique (tendsto_sphereGermValue hm) hlim
  rw [sphereGermValue_chartFiniteMap hH hHnc z] at hvalue
  intro hinfty
  exact (OnePoint.coe_ne_infty _) (hvalue.symm.trans hinfty)

theorem auxPhi_spherical_diagonal_limit_eq_one
    {F G uₙ vₙ : ℕ → ℂ → ℂ} {H : ℂ → OnePoint ℂ} {c : ℂ} (a : Fin 3 → ℂ)
    (hH : SphereHolomorphicOn H univ)
    (hHnc : ¬ ∃ p : OnePoint ℂ, ∀ z, H z = p)
    (hFconv : TendstoLocallyUniformlyOn (fun n => sphereGermValue (F n)) H atTop univ)
    (hGconv : TendstoLocallyUniformlyOn (fun n => sphereGermValue (G n)) H atTop univ)
    (hRatio : TendstoLocallyUniformlyOn (fun n w => uₙ n w / vₙ n w)
      (fun _ => c) atTop univ)
    (hloc : ∀ z : ℂ, ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
      ∀ᶠ n in atTop, AuxiliaryPairOn U (F n) (G n) (uₙ n) (vₙ n) a) : c = 1 := by
  let h : ℂ → ℂ := fun z => chartFiniteMap (H z)
  have hh : IsNonconstMeroOn h univ := isNonconstMeroOn_chartFiniteMap hH hHnc
  obtain ⟨z₀, hderiv, hP⟩ := exists_regular_cubic_point hh a
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

end ThreeIM
