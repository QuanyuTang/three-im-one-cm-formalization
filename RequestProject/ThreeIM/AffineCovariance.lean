module

public import RequestProject.ThreeIM.Covariance
public import RequestProject.ThreeIM.SphereGerm

/-! # Source changes on arbitrary domains and honest affine rescalings -/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

theorem NormalizedPair.comp_source {Ω Ω' : Set ℂ} {f g h : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair Ω' f g a) (hh : ∀ z ∈ Ω, AnalyticAt ℂ h z)
    (hh' : ∀ z ∈ Ω, deriv h z ≠ 0) (hmaps : MapsTo h Ω Ω') :
    NormalizedPair Ω (f ∘ h) (g ∘ h) a where
  nonconst_f := ⟨fun z hz => (hp.nonconst_f.1 (h z) (hmaps hz)).comp_analyticAt (hh z hz),
    fun z hz c => by
      change meromorphicOrderAt ((fun w => f w - c) ∘ h) z ≠ ⊤
      rw [meromorphicOrderAt_comp_of_deriv_ne_zero (hh z hz) (hh' z hz)]
      exact hp.nonconst_f.2 (h z) (hmaps hz) c⟩
  nonconst_g := ⟨fun z hz => (hp.nonconst_g.1 (h z) (hmaps hz)).comp_analyticAt (hh z hz),
    fun z hz c => by
      change meromorphicOrderAt ((fun w => g w - c) ∘ h) z ≠ ⊤
      rw [meromorphicOrderAt_comp_of_deriv_ne_zero (hh z hz) (hh' z hz)]
      exact hp.nonconst_g.2 (h z) (hmaps hz) c⟩
  distinct z hz := by
    change meromorphicOrderAt ((fun w => f w - g w) ∘ h) z ≠ ⊤
    rw [meromorphicOrderAt_comp_of_deriv_ne_zero (hh z hz) (hh' z hz)]
    exact hp.distinct (h z) (hmaps hz)
  injective := hp.injective
  im j z hz := by
    rw [mult_comp_of_deriv_ne_zero (hh z hz) (hh' z hz),
      mult_comp_of_deriv_ne_zero (hh z hz) (hh' z hz)]
    exact hp.im j (h z) (hmaps hz)
  cm_top z hz := by
    rw [mult_comp_of_deriv_ne_zero (hh z hz) (hh' z hz),
      mult_comp_of_deriv_ne_zero (hh z hz) (hh' z hz)]
    exact hp.cm_top (h z) (hmaps hz)

theorem affine_tendsto_nhdsNE (c z₀ z : ℂ) (hc : c ≠ 0) :
    Tendsto (fun w : ℂ => z₀ + c * w) (𝓝[≠] z) (𝓝[≠] (z₀ + c * z)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · exact ((continuous_const.add (continuous_const.mul continuous_id)).tendsto z).mono_left
      nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with w hw
    intro heq
    exact hw (mul_left_cancel₀ hc (add_left_cancel heq))

theorem codiscreteWithin_comp_source {Ω Ω' : Set ℂ} {p : ℂ → Prop} {h : ℂ → ℂ}
    (hp : ∀ᶠ z in codiscreteWithin Ω', p z) (hmaps : MapsTo h Ω Ω')
    (ht : ∀ z ∈ Ω, Tendsto h (𝓝[≠] z) (𝓝[≠] (h z))) :
    ∀ᶠ z in codiscreteWithin Ω, p (h z) := by
  rw [Filter.Eventually, mem_codiscreteWithin_iff_forall_mem_nhdsNE] at hp ⊢
  intro z hz
  filter_upwards [ht z hz (hp (h z) (hmaps hz))] with w hw
  rcases hw with hw | hw
  · exact Or.inl hw
  · exact Or.inr fun hwΩ => hw (hmaps hwΩ)

theorem sphereGermValue_comp_affine {f : ℂ → ℂ} (c z₀ z : ℂ) (hc : c ≠ 0)
    (hf : MeromorphicAt f (z₀ + c * z)) :
    sphereGermValue (fun w => f (z₀ + c * w)) z = sphereGermValue f (z₀ + c * z) := by
  have ha : AnalyticAt ℂ (fun w : ℂ => z₀ + c * w) z := by fun_prop
  exact tendsto_nhds_unique (tendsto_sphereGermValue (hf.comp_analyticAt (g := fun w : ℂ => z₀ + c * w) (x := z) ha))
    ((tendsto_sphereGermValue hf).comp (affine_tendsto_nhdsNE c z₀ z hc))

theorem aux_affine_comp_codiscreteWithin {Ω Ω' : Set ℂ} {f g : ℂ → ℂ}
    (hf : MeromorphicOn f Ω') (hg : MeromorphicOn g Ω') (a : Fin 3 → ℂ)
    (c z₀ : ℂ) (hc : c ≠ 0) (hmaps : MapsTo (fun w => z₀ + c * w) Ω Ω') :
    (auxU a (fun w => f (z₀ + c * w)) (fun w => g (z₀ + c * w))
      =ᶠ[codiscreteWithin Ω] fun w => c * auxU a f g (z₀ + c * w)) ∧
    (auxV a (fun w => f (z₀ + c * w)) (fun w => g (z₀ + c * w))
      =ᶠ[codiscreteWithin Ω] fun w => c * auxV a f g (z₀ + c * w)) ∧
    (auxPhi a (fun w => f (z₀ + c * w)) (fun w => g (z₀ + c * w))
      =ᶠ[codiscreteWithin Ω] fun w => auxPhi a f g (z₀ + c * w)) := by
  have hF := codiscreteWithin_comp_source
    (MeromorphicOn.eventually_codiscreteWithin_analyticAt f hf) hmaps
    (fun w _ => affine_tendsto_nhdsNE c z₀ w hc)
  have hG := codiscreteWithin_comp_source
    (MeromorphicOn.eventually_codiscreteWithin_analyticAt g hg) hmaps
    (fun w _ => affine_tendsto_nhdsNE c z₀ w hc)
  have hd (w : ℂ) : deriv (fun x : ℂ => z₀ + c * x) w = c := by
    simpa only [id_eq, mul_one] using (((hasDerivAt_id w).const_mul c).const_add z₀).deriv
  have hu : auxU a (fun w => f (z₀ + c * w)) (fun w => g (z₀ + c * w))
      =ᶠ[codiscreteWithin Ω] fun w => c * auxU a f g (z₀ + c * w) := by
    filter_upwards [hF] with w hw
    exact (auxU_comp (a := a) (f := f) (g := g) (h := fun x : ℂ => z₀ + c * x) (z := w) hw.differentiableAt (by fun_prop)).trans (by rw [hd])
  have hv : auxV a (fun w => f (z₀ + c * w)) (fun w => g (z₀ + c * w))
      =ᶠ[codiscreteWithin Ω] fun w => c * auxV a f g (z₀ + c * w) := by
    filter_upwards [hG] with w hw
    exact (auxV_comp (a := a) (f := f) (g := g) (h := fun x : ℂ => z₀ + c * x) (z := w) hw.differentiableAt (by fun_prop)).trans (by rw [hd])
  refine ⟨hu, hv, ?_⟩
  filter_upwards [hu, hv] with w huw hvw
  simp only [auxPhi, huw, hvw, mul_div_mul_left _ _ hc]

end ThreeIM
