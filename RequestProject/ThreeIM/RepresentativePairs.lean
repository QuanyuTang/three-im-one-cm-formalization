module

public import RequestProject.ThreeIM.AuxiliaryLimits
public import RequestProject.ThreeIM.SphereHolomorphicBridge

/-! # Original sharing pairs are invariant under punctured-germ representatives -/

@[expose] public section

open Filter Set Topology NoWanderingDomains

namespace ThreeIM

theorem mult_congr_punctured {f F : ℂ → ℂ} {z : ℂ}
    (h : f =ᶠ[𝓝[≠] z] F) (b : Sphere) : mult f b z = mult F b z := by
  induction b using WithTop.recTopCoe with
  | top => simp only [mult_top, meromorphicOrderAt_congr h]
  | coe c =>
    simp only [mult_coe]
    have hc : (fun w => f w - c) =ᶠ[𝓝[≠] z] (fun w => F w - c) := by
      filter_upwards [h] with w hw
      rw [hw]
    rw [meromorphicOrderAt_congr hc]

theorem IsNonconstMeroOn.congr_codiscreteWithin {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {f F : ℂ → ℂ} (hf : IsNonconstMeroOn f Ω) (heq : f =ᶠ[codiscreteWithin Ω] F) :
    IsNonconstMeroOn F Ω := by
  have he : ∀ z ∈ Ω, f =ᶠ[𝓝[≠] z] F :=
    fun z hz => auxiliary_local_of_codiscreteWithin hΩ heq hz
  refine ⟨fun z hz => (hf.1 z hz).congr (he z hz), fun z hz c => ?_⟩
  have hc : (fun w => f w - c) =ᶠ[𝓝[≠] z] (fun w => F w - c) := by
    filter_upwards [he z hz] with w hw
    rw [hw]
  rw [← meromorphicOrderAt_congr hc]
  exact hf.2 z hz c

theorem NormalizedPair.congr_codiscreteWithin {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {f g F G : ℂ → ℂ} {a : Fin 3 → ℂ} (hp : NormalizedPair Ω f g a)
    (hf : f =ᶠ[codiscreteWithin Ω] F) (hg : g =ᶠ[codiscreteWithin Ω] G) :
    NormalizedPair Ω F G a where
  nonconst_f := hp.nonconst_f.congr_codiscreteWithin hΩ hf
  nonconst_g := hp.nonconst_g.congr_codiscreteWithin hΩ hg
  distinct z hz := by
    have hfz := auxiliary_local_of_codiscreteWithin hΩ hf hz
    have hgz := auxiliary_local_of_codiscreteWithin hΩ hg hz
    have he : (fun w => f w - g w) =ᶠ[𝓝[≠] z] (fun w => F w - G w) := by
      filter_upwards [hfz, hgz] with w hwF hwG
      rw [hwF, hwG]
    rw [← meromorphicOrderAt_congr he]
    exact hp.distinct z hz
  injective := hp.injective
  im j z hz := by
    rw [← mult_congr_punctured (auxiliary_local_of_codiscreteWithin hΩ hf hz),
      ← mult_congr_punctured (auxiliary_local_of_codiscreteWithin hΩ hg hz)]
    exact hp.im j z hz
  cm_top z hz := by
    rw [← mult_congr_punctured (auxiliary_local_of_codiscreteWithin hΩ hf hz),
      ← mult_congr_punctured (auxiliary_local_of_codiscreteWithin hΩ hg hz)]
    exact hp.cm_top z hz

theorem chartFinite_sphereGerm_eq_codiscreteWithin {Ω : Set ℂ} {f : ℂ → ℂ}
    (hf : MeromorphicOn f Ω) :
    f =ᶠ[codiscreteWithin Ω] (fun w => chartFiniteMap (sphereGermValue f w)) := by
  filter_upwards [MeromorphicOn.eventually_codiscreteWithin_analyticAt f hf] with w hw
  rw [sphereGermValue_eq_coe_of_analytic hw]
  rfl

end ThreeIM
