module

public import RequestProject.ThreeIM.SphereHolomorphicBridge

/-! # The four honest sphere fibers of an original normalized pair -/

@[expose] public section

open Filter Set Topology NoWanderingDomains

namespace ThreeIM

def normalizedSphereTargets (a : Fin 3 → ℂ) : Fin 4 → OnePoint ℂ :=
  ![(a 0 : OnePoint ℂ), (a 1 : OnePoint ℂ), (a 2 : OnePoint ℂ), OnePoint.infty]

theorem normalizedSphereTargets_injective {a : Fin 3 → ℂ} (ha : Function.Injective a) :
    Function.Injective (normalizedSphereTargets a) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [normalizedSphereTargets, ha.eq_iff]

theorem NormalizedPair.sphere_shares {Ω : Set ℂ} {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair Ω f g a) :
    ∀ z ∈ Ω, ∀ i, (sphereGermValue f z = normalizedSphereTargets a i ↔
      sphereGermValue g z = normalizedSphereTargets a i) := by
  intro z hz i
  fin_cases i
  · exact (sharesIMOn_iff_sphereGerm_fibers hp.nonconst_f hp.nonconst_g (a 0 : Sphere)).1
      (hp.im 0) z hz
  · exact (sharesIMOn_iff_sphereGerm_fibers hp.nonconst_f hp.nonconst_g (a 1 : Sphere)).1
      (hp.im 1) z hz
  · exact (sharesIMOn_iff_sphereGerm_fibers hp.nonconst_f hp.nonconst_g (a 2 : Sphere)).1
      (hp.im 2) z hz
  · exact (sharesIMOn_iff_sphereGerm_fibers hp.nonconst_f hp.nonconst_g ⊤).1
      hp.cm_top.sharesIMOn z hz

end ThreeIM
