module

public import RequestProject.ThreeIM.RepresentativePairs
public import RequestProject.ThreeIM.SphereLimits

/-!
# Prescribed auxiliary coefficients persist under spherical limits

Both limits are honest nonconstant sphere-holomorphic maps. Their finite
charts are used only on a common ordinary disk. All changes from the raw
meromorphic functions to these charts are made through punctured germs.
Cleared equations pass to the limit there, and meromorphic identity extends
the resulting auxiliary equations to the plane. No growth bound is used.
-/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

set_option autoImplicit false

theorem spherical_auxiliary_limits
    {F G uₙ vₙ : ℕ → ℂ → ℂ} {H K : ℂ → OnePoint ℂ} (a : Fin 3 → ℂ)
    (hH : SphereHolomorphicOn H univ) (hK : SphereHolomorphicOn K univ)
    (hHnc : ¬ ∃ p : OnePoint ℂ, ∀ z, H z = p)
    (hKnc : ¬ ∃ p : OnePoint ℂ, ∀ z, K z = p)
    (hFconv : TendstoLocallyUniformlyOn (fun n => sphereGermValue (F n)) H atTop univ)
    (hGconv : TendstoLocallyUniformlyOn (fun n => sphereGermValue (G n)) K atTop univ)
    {u v : ℂ → ℂ} (hu : Differentiable ℂ u) (hv : Differentiable ℂ v)
    (huconv : TendstoLocallyUniformlyOn uₙ u atTop univ)
    (hvconv : TendstoLocallyUniformlyOn vₙ v atTop univ)
    (hloc : ∀ z : ℂ, ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
      ∀ᶠ n in atTop, IsNonconstMeroOn (F n) U ∧ IsNonconstMeroOn (G n) U ∧
        ContinuousOn (uₙ n) U ∧ ContinuousOn (vₙ n) U ∧
        (auxU a (F n) (G n) =ᶠ[codiscreteWithin U] uₙ n) ∧
        (auxV a (F n) (G n) =ᶠ[codiscreteWithin U] vₙ n)) :
    (auxU a (fun z => chartFiniteMap (H z)) (fun z => chartFiniteMap (K z))
      =ᶠ[codiscrete ℂ] u) ∧
    (auxV a (fun z => chartFiniteMap (H z)) (fun z => chartFiniteMap (K z))
      =ᶠ[codiscrete ℂ] v) := by
  let h : ℂ → ℂ := fun z => chartFiniteMap (H z)
  let k : ℂ → ℂ := fun z => chartFiniteMap (K z)
  have hh : IsNonconstMeroOn h univ := isNonconstMeroOn_chartFiniteMap hH hHnc
  have hk : IsNonconstMeroOn k univ := isNonconstMeroOn_chartFiniteMap hK hKnc
  have hne (f : ℂ → ℂ) (hf : IsNonconstMeroOn f univ) :
      ∀ᶠ z in 𝓝[≠] (0 : ℂ), f z ≠ 0 := by
    apply (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hf.1 0 (mem_univ 0))).mp
    simpa only [sub_zero] using hf.2 0 (mem_univ 0) 0
  obtain ⟨z₀, hhz, hkz⟩ := ((hne h hh).and (hne k hk)).exists
  have hHfin : H z₀ ≠ OnePoint.infty := by
    intro he
    apply hhz
    simp only [h, he, chartFiniteMap]
  have hKfin : K z₀ ≠ OnePoint.infty := by
    intro he
    apply hkz
    simp only [k, he, chartFiniteMap]
  obtain ⟨U, hU, hzU, hseq⟩ := hloc z₀
  have hFH : ∀ᶠ n in atTop, SphereHolomorphicOn (sphereGermValue (F n)) U :=
    hseq.mono fun n hn => sphereHolomorphicOn_sphereGermValue hU hn.1.1
  have hGH : ∀ᶠ n in atTop, SphereHolomorphicOn (sphereGermValue (G n)) U :=
    hseq.mono fun n hn => sphereHolomorphicOn_sphereGermValue hU hn.2.1.1
  obtain ⟨rF, hrF, hrFU, _, _, hFd, hcF⟩ := exists_finite_chart_convergence_eventually
    hU hFH (hFconv.mono (subset_univ U)) hzU hHfin
  obtain ⟨rG, hrG, hrGU, _, _, hGd, hcG⟩ := exists_finite_chart_convergence_eventually
    hU hGH (hGconv.mono (subset_univ U)) hzU hKfin
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
  have hDc : TendstoLocallyUniformlyOn D k atTop B :=
    hcG.tendstoLocallyUniformlyOn.mono (hBG.trans ball_subset_closedBall)
  have hclear : ∀ᶠ n in atTop,
      (∀ z ∈ B, (C n z - D n z) * deriv (C n) z = uₙ n z * cubicP a (C n z)) ∧
      (∀ z ∈ B, (C n z - D n z) * deriv (D n) z = vₙ n z * cubicP a (D n z)) := by
    filter_upwards [hseq, hCd, hDd] with n hn hnC hnD
    have hfB : IsNonconstMeroOn (F n) B :=
      ⟨fun z hz => hn.1.1 z (hBU hz), fun z hz c => hn.1.2 z (hBU hz) c⟩
    have hgB : IsNonconstMeroOn (G n) B :=
      ⟨fun z hz => hn.2.1.1 z (hBU hz), fun z hz c => hn.2.1.2 z (hBU hz) c⟩
    have heF : F n =ᶠ[codiscreteWithin B] C n :=
      chartFinite_sphereGerm_eq_codiscreteWithin hfB.1
    have heG : G n =ᶠ[codiscreteWithin B] D n :=
      chartFinite_sphereGerm_eq_codiscreteWithin hgB.1
    have hCn := hfB.congr_codiscreteWithin hBo heF
    have hDn := hgB.congr_codiscreteWithin hBo heG
    have haux := auxiliary_congr_codiscreteWithin hBo heF heG a
    have hUraw : auxU a (F n) (G n) =ᶠ[codiscreteWithin B] uₙ n :=
      hn.2.2.2.2.1.filter_mono (Filter.codiscreteWithin.mono hBU)
    have hVraw : auxV a (F n) (G n) =ᶠ[codiscreteWithin B] vₙ n :=
      hn.2.2.2.2.2.filter_mono (Filter.codiscreteWithin.mono hBU)
    have hCca := hnC.analyticOnNhd hBo
    have hDca := hnD.analyticOnNhd hBo
    have hdiff : ContinuousOn (fun z => C n z - D n z) B :=
      hnC.continuousOn.sub hnD.continuousOn
    exact ⟨auxiliary_cleared_eqOn a hBo hCca hCn hdiff (hn.2.2.1.mono hBU)
        (haux.1.symm.trans hUraw),
      auxiliary_cleared_eqOn a hBo hDca hDn hdiff (hn.2.2.2.1.mono hBU)
        (haux.2.1.symm.trans hVraw)⟩
  have hlimit := auxiliary_cleared_limit hBo a hCd hDd hCc hDc
    (huconv.mono (subset_univ B)) (hvconv.mono (subset_univ B))
    (hclear.mono fun n hn => hn.1) (hclear.mono fun n hn => hn.2)
  have hhB : IsNonconstMeroOn h B :=
    ⟨fun z _ => hh.1 z (mem_univ z), fun z _ c => hh.2 z (mem_univ z) c⟩
  have hkB : IsNonconstMeroOn k B :=
    ⟨fun z _ => hk.1 z (mem_univ z), fun z _ c => hk.2 z (mem_univ z) c⟩
  have hBmem : ∀ᶠ z in codiscreteWithin B, z ∈ B := Filter.self_mem_codiscreteWithin B
  have hids := auxiliary_identities_of_cleared a hhB hkB
    (hBmem.mono fun z hz => hlimit.1 z hz)
    (hBmem.mono fun z hz => hlimit.2 z hz)
  have hUm : Meromorphic (auxU a h k) := fun z => by
    have := hh.1 z (mem_univ z)
    have := hk.1 z (mem_univ z)
    have := (hh.1 z (mem_univ z)).deriv
    unfold auxU cubicP
    fun_prop
  have hVm : Meromorphic (auxV a h k) := fun z => by
    have := hh.1 z (mem_univ z)
    have := hk.1 z (mem_univ z)
    have := (hk.1 z (mem_univ z)).deriv
    unfold auxV cubicP
    fun_prop
  exact ⟨auxiliary_globalize_identity hUm (fun z => (hu.analyticAt z).meromorphicAt)
      (auxiliary_local_of_codiscreteWithin hBo hids.1 hzB),
    auxiliary_globalize_identity hVm (fun z => (hv.analyticAt z).meromorphicAt)
      (auxiliary_local_of_codiscreteWithin hBo hids.2.1 hzB)⟩

end ThreeIM
