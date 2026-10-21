module

public import RequestProject.ThreeIM.AuxiliaryPair
public import RequestProject.ThreeIM.RepresentativePairs
public import RequestProject.ThreeIM.MarkedMultiplicity
public import RequestProject.ThreeIM.MarkedOrderPersistence
public import RequestProject.ThreeIM.SphereDerivatives

/-! # Marked simple derivatives in honest finite charts -/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

set_option autoImplicit false

theorem AuxiliaryPairOn.marked_finite_chart_derivative
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {f g u v : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : AuxiliaryPairOn Ω f g u v a) {z : ℂ} (hz : z ∈ Ω)
    {j : Fin 3} {m : ℕ} (hm : 2 ≤ m)
    (hmf : mult f (a j : Sphere) z = 1) (hmg : mult g (a j : Sphere) z = m) :
    sphereGermValue f z = (a j : OnePoint ℂ) ∧
      sphereGermValue g z = (a j : OnePoint ℂ) ∧
      deriv (fun w => chartFiniteMap (sphereGermValue f w)) z ≠ 0 ∧
      deriv (fun w => chartFiniteMap (sphereGermValue f w)) z =
        (∏ i ∈ Finset.univ.erase j, (a j - a i)) * u z := by
  have hfv := (mult_finite_pos_iff_sphereGermValue_eq
    (hp.pair.nonconst_f.1 z hz) (hp.pair.nonconst_f.2 z hz (a j))).1
      (by rw [hmf]; decide)
  have hgv := (mult_finite_pos_iff_sphereGermValue_eq
    (hp.pair.nonconst_g.1 z hz) (hp.pair.nonconst_g.2 z hz (a j))).1
      (by rw [hmg]; omega)
  have hfS := sphereHolomorphicOn_sphereGermValue hΩ hp.pair.nonconst_f.1
  have hgS := sphereHolomorphicOn_sphereGermValue hΩ hp.pair.nonconst_g.1
  have hfA := analyticAt_chartFiniteMap_of_ne_infty hfS hz
    (by rw [hfv]; exact OnePoint.coe_ne_infty _)
  have hgA := analyticAt_chartFiniteMap_of_ne_infty hgS hz
    (by rw [hgv]; exact OnePoint.coe_ne_infty _)
  have heF := chartFinite_sphereGerm_eq_codiscreteWithin hp.pair.nonconst_f.1
  have heG := chartFinite_sphereGerm_eq_codiscreteWithin hp.pair.nonconst_g.1
  have heFp := auxiliary_local_of_codiscreteWithin hΩ heF hz
  have heGp := auxiliary_local_of_codiscreteWithin hΩ heG hz
  have hmf' : mult (fun w => chartFiniteMap (sphereGermValue f w)) (a j : Sphere) z = 1 :=
    (mult_congr_punctured heFp (a j : Sphere)).symm.trans hmf
  have hmg' : mult (fun w => chartFiniteMap (sphereGermValue g w)) (a j : Sphere) z = m :=
    (mult_congr_punctured heGp (a j : Sphere)).symm.trans hmg
  have haux := auxiliary_congr_codiscreteWithin hΩ heF heG a
  have hU := auxiliary_local_of_codiscreteWithin hΩ (haux.1.symm.trans hp.u_eq) hz
  exact ⟨hfv, hgv, marked_derivative_of_mult hp.pair.injective hm hfA hgA
    hmf' hmg' (hp.holo_u.continuousOn.continuousAt (hΩ.mem_nhds hz)) hU⟩

theorem marked_spherical_limit_nonconstant
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {z : ℂ} (hz : z ∈ Ω)
    {F G uₙ vₙ : ℕ → ℂ → ℂ} {a : Fin 3 → ℂ} {j : Fin 3} {m : ℕ} (hm : 2 ≤ m)
    (hseq : ∀ᶠ n in atTop, AuxiliaryPairOn Ω (F n) (G n) (uₙ n) (vₙ n) a)
    (hmf : ∀ n, mult (F n) (a j : Sphere) z = 1)
    (hmg : ∀ n, mult (G n) (a j : Sphere) z = m)
    {H : ℂ → OnePoint ℂ} (hH : SphereHolomorphicOn H Ω)
    (hFconv : TendstoLocallyUniformlyOn (fun n => sphereGermValue (F n)) H atTop Ω)
    {u : ℂ → ℂ} (huconv : TendstoLocallyUniformlyOn uₙ u atTop Ω) (hu0 : u z ≠ 0) :
    H z = (a j : OnePoint ℂ) ∧
      deriv (fun w => chartFiniteMap (H w)) z =
        (∏ i ∈ Finset.univ.erase j, (a j - a i)) * u z ∧
      deriv (fun w => chartFiniteMap (H w)) z ≠ 0 ∧
      (¬ ∃ p : OnePoint ℂ, ∀ w, H w = p) := by
  have hmarked := hseq.mono fun n hn =>
    hn.marked_finite_chart_derivative hΩ hz hm (hmf n) (hmg n)
  have hHvalue : H z = (a j : OnePoint ℂ) :=
    tendsto_nhds_unique_of_eventuallyEq (hFconv.tendsto_at hz) tendsto_const_nhds
      (hmarked.mono fun n hn => hn.1)
  have hFH := hseq.mono fun n hn =>
    sphereHolomorphicOn_sphereGermValue hΩ hn.pair.nonconst_f.1
  obtain ⟨r, hr, _, _, _, _, hderiv⟩ := exists_finite_chart_deriv_convergence_eventually
    hΩ hFH hFconv hz (by rw [hHvalue]; exact OnePoint.coe_ne_infty _)
  have hzB : z ∈ ball z r := mem_ball_self hr
  obtain ⟨n, hn⟩ := hseq.exists
  have hprod := prod_erase_ne_zero hn.pair.injective j
  have hlimit : Tendsto
      (fun n => (∏ i ∈ Finset.univ.erase j, (a j - a i)) * uₙ n z)
      atTop (𝓝 ((∏ i ∈ Finset.univ.erase j, (a j - a i)) * u z)) :=
    tendsto_const_nhds.mul (huconv.tendsto_at hz)
  have hformula := tendsto_nhds_unique_of_eventuallyEq (hderiv.tendsto_at hzB) hlimit
    (hmarked.mono fun n hn => hn.2.2.2)
  have hne : deriv (fun w => chartFiniteMap (H w)) z ≠ 0 := by
    rw [hformula]
    exact mul_ne_zero hprod hu0
  refine ⟨hHvalue, hformula, hne, ?_⟩
  rintro ⟨p, hp⟩
  apply hne
  have hc : (fun w => chartFiniteMap (H w)) = fun _ => chartFiniteMap p :=
    funext fun w => congrArg chartFiniteMap (hp w)
  rw [hc, deriv_const]

end ThreeIM
