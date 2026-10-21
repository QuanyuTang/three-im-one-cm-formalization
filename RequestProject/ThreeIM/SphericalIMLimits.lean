module

public import RequestProject.ThreeIM.SphereIMPersist

/-! # Spherical IM persistence in the original meromorphic-germ predicates -/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

theorem sharesIMOn_of_spherical_limits {F G : ℕ → ℂ → ℂ} {f g : ℂ → ℂ}
    (hf : IsNonconstMeroOn f univ) (hg : IsNonconstMeroOn g univ) (b : Sphere)
    (hF : TendstoLocallyUniformlyOn (fun n => sphereGermValue (F n))
      (sphereGermValue f) atTop univ)
    (hG : TendstoLocallyUniformlyOn (fun n => sphereGermValue (G n))
      (sphereGermValue g) atTop univ)
    (hloc : ∀ z : ℂ, ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
      ∀ᶠ n in atTop, IsNonconstMeroOn (F n) U ∧ IsNonconstMeroOn (G n) U ∧
        SharesIMOn U (F n) (G n) b) : SharesIMOn univ f g b := by
  apply (sharesIMOn_iff_sphereGerm_fibers hf hg b).2
  have hsf := sphereHolomorphicOn_sphereGermValue isOpen_univ hf.1
  have hsg := sphereHolomorphicOn_sphereGermValue isOpen_univ hg.1
  have hp := sphere_limit_shared_fiber_iff hsf hsg (sphereGermValue_nonconstant hf)
    (sphereGermValue_nonconstant hg) hF hG (fun z => by
      obtain ⟨U, hU, hzU, hev⟩ := hloc z
      refine ⟨U, hU, hzU, hev.mono fun n hn => ?_⟩
      exact ⟨sphereHolomorphicOn_sphereGermValue hU hn.1.1,
        sphereHolomorphicOn_sphereGermValue hU hn.2.1.1,
        (sharesIMOn_iff_sphereGerm_fibers hn.1 hn.2.1 b).1 hn.2.2⟩)
  exact fun z _ => hp z

end ThreeIM
