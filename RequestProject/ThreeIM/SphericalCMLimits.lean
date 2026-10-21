module

public import RequestProject.ThreeIM.SphereInverseChart
public import RequestProject.ThreeIM.SphericalIMLimits
public import RequestProject.ThreeIM.SphereCMPersistence

/-! # Persistence of original CM pole sharing under spherical convergence -/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

theorem pole_mult_eq_of_spherical_limits_at_poles {F G : ℕ → ℂ → ℂ} {f g : ℂ → ℂ}
    (hf : IsNonconstMeroOn f univ) (hg : IsNonconstMeroOn g univ)
    (hF : TendstoLocallyUniformlyOn (fun n => sphereGermValue (F n))
      (sphereGermValue f) atTop univ)
    (hG : TendstoLocallyUniformlyOn (fun n => sphereGermValue (G n))
      (sphereGermValue g) atTop univ)
    {z : ℂ} (hnegf : meromorphicOrderAt f z < 0) (hnegg : meromorphicOrderAt g z < 0)
    (hloc : ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
      ∀ᶠ n in atTop, IsNonconstMeroOn (F n) U ∧ IsNonconstMeroOn (G n) U ∧
        SharesCMOn U (F n) (G n) ⊤) : mult f ⊤ z = mult g ⊤ z := by
  have hsf := sphereHolomorphicOn_sphereGermValue isOpen_univ hf.1
  have hsg := sphereHolomorphicOn_sphereGermValue isOpen_univ hg.1
  have hfnc : ¬ ∃ p : OnePoint ℂ, ∀ w, inversionGL • sphereGermValue f w = p := by
    rintro ⟨p, hp⟩
    exact sphereGermValue_nonconstant hf ⟨sphereGermValue f 0,
      fun w => MulAction.injective inversionGL ((hp w).trans (hp 0).symm)⟩
  have hgnc : ¬ ∃ p : OnePoint ℂ, ∀ w, inversionGL • sphereGermValue g w = p := by
    rintro ⟨p, hp⟩
    exact sphereGermValue_nonconstant hg ⟨sphereGermValue g 0,
      fun w => MulAction.injective inversionGL ((hp w).trans (hp 0).symm)⟩
  have huc : UniformContinuous (fun p : OnePoint ℂ => inversionGL • p) :=
    CompactSpace.uniformContinuous_of_continuous (continuous_gl_smul inversionGL)
  have hff : inversionGL • sphereGermValue f z ≠ OnePoint.infty := by
    rw [(sphereGermValue_eq_infty_iff f z).2 hnegf, inversionGL_smul_infty]
    exact OnePoint.coe_ne_infty 0
  have hgf : inversionGL • sphereGermValue g z ≠ OnePoint.infty := by
    rw [(sphereGermValue_eq_infty_iff g z).2 hnegg, inversionGL_smul_infty]
    exact OnePoint.coe_ne_infty 0
  have hseq : ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
      ∀ᶠ n in atTop,
        SphereHolomorphicOn (fun w => inversionGL • sphereGermValue (F n) w) U ∧
        SphereHolomorphicOn (fun w => inversionGL • sphereGermValue (G n) w) U ∧
        (∀ w ∈ U, mult (fun x => chartFiniteMap (inversionGL • sphereGermValue (F n) x))
            ((0 : ℂ) : Sphere) w =
          mult (fun x => chartFiniteMap (inversionGL • sphereGermValue (G n) x))
            ((0 : ℂ) : Sphere) w) ∧
        ∀ w ∈ U,
          meromorphicOrderAt (fun x => chartFiniteMap (inversionGL • sphereGermValue (F n) x)) w ≠ ⊤ ∧
          meromorphicOrderAt (fun x => chartFiniteMap (inversionGL • sphereGermValue (G n) x)) w ≠ ⊤ := by
    obtain ⟨U, hU, hzU, hev⟩ := hloc
    refine ⟨U, hU, hzU, hev.mono fun n hn => ?_⟩
    refine ⟨(sphereHolomorphicOn_sphereGermValue hU hn.1.1).gl_smul inversionGL,
      (sphereHolomorphicOn_sphereGermValue hU hn.2.1.1).gl_smul inversionGL, ?_, ?_⟩
    · intro w hw
      rw [inverseChart_sphereGermValue_mult (hn.1.1 w hw),
        inverseChart_sphereGermValue_mult (hn.2.1.1 w hw)]
      exact hn.2.2 w hw
    · intro w hw
      exact ⟨inverseChart_sphereGermValue_finite (hn.1.1 w hw)
          (by simpa only [sub_zero] using hn.1.2 w hw 0),
        inverseChart_sphereGermValue_finite (hn.2.1.1 w hw)
          (by simpa only [sub_zero] using hn.2.1.2 w hw 0)⟩
  have ho := sphere_chart_orders_eq_of_spherical_cm (hsf.gl_smul inversionGL)
    (hsg.gl_smul inversionGL) hfnc hgnc (huc.comp_tendstoLocallyUniformlyOn hF)
    (huc.comp_tendstoLocallyUniformlyOn hG) hff hgf hseq
  have hnat := congrArg (fun o : WithTop ℤ => o.untop₀.toNat) ho
  simpa only [inverseChart_sphereGermValue_order (hf.1 z (mem_univ z)),
    inverseChart_sphereGermValue_order (hg.1 z (mem_univ z)), mult_top] using hnat

theorem sharesCMOn_top_of_spherical_limits {F G : ℕ → ℂ → ℂ} {f g : ℂ → ℂ}
    (hf : IsNonconstMeroOn f univ) (hg : IsNonconstMeroOn g univ)
    (hF : TendstoLocallyUniformlyOn (fun n => sphereGermValue (F n))
      (sphereGermValue f) atTop univ)
    (hG : TendstoLocallyUniformlyOn (fun n => sphereGermValue (G n))
      (sphereGermValue g) atTop univ)
    (hloc : ∀ z : ℂ, ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
      ∀ᶠ n in atTop, IsNonconstMeroOn (F n) U ∧ IsNonconstMeroOn (G n) U ∧
        SharesCMOn U (F n) (G n) ⊤) : SharesCMOn univ f g ⊤ := by
  have him := sharesIMOn_of_spherical_limits hf hg ⊤ hF hG (fun z => by
    obtain ⟨U, hU, hzU, hev⟩ := hloc z
    exact ⟨U, hU, hzU, hev.mono fun n hn => ⟨hn.1, hn.2.1, hn.2.2.sharesIMOn⟩⟩)
  intro z _
  by_cases hpos : 0 < mult f ⊤ z
  · exact pole_mult_eq_of_spherical_limits_at_poles hf hg hF hG
      ((mult_top_pos_iff_order_neg f z).1 hpos)
      ((mult_top_pos_iff_order_neg g z).1 ((him z (mem_univ z)).1 hpos)) (hloc z)
  · have hzero : mult f ⊤ z = 0 := Nat.eq_zero_of_not_pos hpos
    have hgzero : mult g ⊤ z = 0 := Nat.eq_zero_of_not_pos
      (fun hgpos => hpos ((him z (mem_univ z)).2 hgpos))
    exact hzero.trans hgzero.symm

end ThreeIM
