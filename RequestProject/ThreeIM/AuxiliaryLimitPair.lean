module

public import RequestProject.ThreeIM.AuxiliaryMarkedPoint
public import RequestProject.ThreeIM.SphericalCMLimits

/-! # Sharing and marked defects determine the limiting normalized pair -/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

set_option autoImplicit false

theorem normalizedPair_of_spherical_limits_and_defect
    {F G : ℕ → ℂ → ℂ} {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hf : IsNonconstMeroOn f univ) (hg : IsNonconstMeroOn g univ)
    (ha : Function.Injective a)
    (hF : TendstoLocallyUniformlyOn (fun n => sphereGermValue (F n))
      (sphereGermValue f) atTop univ)
    (hG : TendstoLocallyUniformlyOn (fun n => sphereGermValue (G n))
      (sphereGermValue g) atTop univ)
    (hloc : ∀ z : ℂ, ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
      ∀ᶠ n in atTop, NormalizedPair U (F n) (G n) a)
    {b : Sphere} {z₀ : ℂ} (hdef : IsDefect f g b z₀) :
    NormalizedPair univ f g a := by
  refine ⟨hf, hg, ?_, ha, ?_, ?_⟩
  · intro z _ htop
    have heq : f =ᶠ[𝓝[≠] z] g :=
      (meromorphicOrderAt_eq_top_iff.1 htop).mono fun w hw => sub_eq_zero.1 hw
    have hglobal := auxiliary_globalize_identity
      (fun w => hf.1 w (mem_univ w)) (fun w => hg.1 w (mem_univ w)) heq
    exact hdef.2.2 (mult_congr_punctured
      (auxiliary_local_of_codiscreteWithin isOpen_univ hglobal (mem_univ z₀)) b)
  · intro j
    apply sharesIMOn_of_spherical_limits hf hg (a j : Sphere) hF hG
    intro z
    obtain ⟨U, hU, hzU, hev⟩ := hloc z
    exact ⟨U, hU, hzU, hev.mono fun n hn => ⟨hn.nonconst_f, hn.nonconst_g, hn.im j⟩⟩
  · apply sharesCMOn_top_of_spherical_limits hf hg hF hG
    intro z
    obtain ⟨U, hU, hzU, hev⟩ := hloc z
    exact ⟨U, hU, hzU, hev.mono fun n hn => ⟨hn.nonconst_f, hn.nonconst_g, hn.cm_top⟩⟩

theorem marked_mult_ge_of_spherical_limit
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {z : ℂ} (hz : z ∈ Ω)
    {G : ℕ → ℂ → ℂ} {K : ℂ → OnePoint ℂ} (hK : SphereHolomorphicOn K univ)
    (hKnc : ¬ ∃ p : OnePoint ℂ, ∀ w, K w = p)
    (hG : TendstoLocallyUniformlyOn (fun n => sphereGermValue (G n)) K atTop Ω)
    (hseq : ∀ᶠ n in atTop, IsNonconstMeroOn (G n) Ω)
    {b : ℂ} {m : ℕ} (hm : 0 < m) (hmarked : ∀ n, mult (G n) (b : Sphere) z = m) :
    K z = (b : OnePoint ℂ) ∧ m ≤ mult (fun w => chartFiniteMap (K w)) (b : Sphere) z := by
  have hvalues : ∀ᶠ n in atTop, sphereGermValue (G n) z = (b : OnePoint ℂ) := by
    filter_upwards [hseq] with n hn
    exact (mult_finite_pos_iff_sphereGermValue_eq (hn.1 z hz) (hn.2 z hz b)).1
      (by rw [hmarked n]; exact hm)
  have hKvalue : K z = (b : OnePoint ℂ) :=
    tendsto_nhds_unique_of_eventuallyEq (hG.tendsto_at hz) tendsto_const_nhds hvalues
  have hGH := hseq.mono fun n hn => sphereHolomorphicOn_sphereGermValue hΩ hn.1
  obtain ⟨r, hr, hrΩ, _, _, hGd, hcG⟩ := exists_finite_chart_convergence_eventually
    hΩ hGH hG hz (by rw [hKvalue]; exact OnePoint.coe_ne_infty _)
  have hzB : z ∈ ball z r := mem_ball_self hr
  let C : ℕ → ℂ → ℂ := fun n w => chartFiniteMap (sphereGermValue (G n) w)
  have horder : ∀ᶠ n in atTop,
      (m : ℤ) ≤ meromorphicOrderAt (fun w => C n w - b) z := by
    filter_upwards [hseq] with n hn
    have heq := chartFinite_sphereGerm_eq_codiscreteWithin hn.1
    have hmult : mult (C n) (b : Sphere) z = m :=
      (mult_congr_punctured (auxiliary_local_of_codiscreteWithin hΩ heq hz)
        (b : Sphere)).symm.trans (hmarked n)
    exact le_of_eq (order_sub_eq_nat_of_mult_pos (C n) b z hm hmult).symm
  have hkc := isNonconstMeroOn_chartFiniteMap hK hKnc
  exact ⟨hKvalue, marked_mult_ge_of_locallyUniformlyOn isOpen_ball hzB hGd
    (hcG.tendstoLocallyUniformlyOn.mono ball_subset_closedBall) b m horder
    (hkc.2 z (mem_univ z) b)⟩

end ThreeIM
