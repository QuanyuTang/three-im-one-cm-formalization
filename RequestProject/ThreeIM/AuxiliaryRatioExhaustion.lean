module

public import RequestProject.ThreeIM.AuxiliaryRatioNormality

/-! # Eventual local normality for independently convergent auxiliary quotients -/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

set_option autoImplicit false

theorem NormalizedPair.restrict {Ω D : Set ℂ} {F G : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair Ω F G a) (hDΩ : D ⊆ Ω) : NormalizedPair D F G a where
  nonconst_f := ⟨fun z hz => hp.nonconst_f.1 z (hDΩ hz),
    fun z hz c => hp.nonconst_f.2 z (hDΩ hz) c⟩
  nonconst_g := ⟨fun z hz => hp.nonconst_g.1 z (hDΩ hz),
    fun z hz c => hp.nonconst_g.2 z (hDΩ hz) c⟩
  distinct := fun z hz => hp.distinct z (hDΩ hz)
  injective := hp.injective
  im := fun j z hz => hp.im j z (hDΩ hz)
  cm_top := fun z hz => hp.cm_top z (hDΩ hz)

private theorem ratio_tlu_reindex {X : Type*} [UniformSpace X]
    {F : ℕ → ℂ → X} {f : ℂ → X} {Ω : Set ℂ}
    (h : TendstoLocallyUniformlyOn F f atTop Ω) {i : ℕ → ℕ}
    (hi : Tendsto i atTop atTop) :
    TendstoLocallyUniformlyOn (fun n => F (i n)) f atTop Ω := by
  intro e he z hz
  obtain ⟨t, ht, hev⟩ := h e he z hz
  exact ⟨t, ht, hi.eventually hev⟩

theorem auxiliary_pairs_isNormalAt_of_ratio_limit_eventually
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {F G uₙ vₙ : ℕ → ℂ → ℂ} {a : Fin 3 → ℂ}
    (hseq : ∀ᶠ n in atTop, AuxiliaryPairOn Ω (F n) (G n) (uₙ n) (vₙ n) a)
    {u v φ : ℂ → ℂ} (hu : ContinuousOn u Ω) (hv : ContinuousOn v Ω)
    (hφ : ContinuousOn φ Ω)
    (huconv : TendstoLocallyUniformlyOn uₙ u atTop Ω)
    (hvconv : TendstoLocallyUniformlyOn vₙ v atTop Ω)
    (hφconv : TendstoLocallyUniformlyOn (fun n w => uₙ n w / vₙ n w) φ atTop Ω)
    (hsimple : ∀ z ∈ Ω, φ z = 1 → deriv φ z ≠ 0) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    IsNormalAt (range (fun n => sphereGermValue (F n))) z₀ := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hseq
  have hseqN : ∀ n, AuxiliaryPairOn Ω (F (n + N)) (G (n + N))
      (uₙ (n + N)) (vₙ (n + N)) a := fun n => hN (n + N) (Nat.le_add_left N n)
  exact isNormalAt_range_of_normal_tail (fun n => sphereGermValue (F n)) N
    (auxiliary_pairs_isNormalAt_of_ratio_limit hΩ hseqN hu hv hφ
      (ratio_tlu_reindex huconv (tendsto_add_atTop_nat N))
      (ratio_tlu_reindex hvconv (tendsto_add_atTop_nat N))
      (ratio_tlu_reindex hφconv (tendsto_add_atTop_nat N)) hsimple hz₀)

theorem auxiliary_pairs_isNormal_of_vanishing_coefficients_locally
    {F G uₙ vₙ : ℕ → ℂ → ℂ} {a : Fin 3 → ℂ}
    (hloc : ∀ z : ℂ, ∃ Ω : Set ℂ, IsOpen Ω ∧ z ∈ Ω ∧
      ∀ᶠ n in atTop, AuxiliaryPairOn Ω (F n) (G n) (uₙ n) (vₙ n) a)
    (huconv : TendstoLocallyUniformlyOn uₙ (fun _ => 0) atTop univ)
    (hvconv : TendstoLocallyUniformlyOn vₙ (fun _ => 0) atTop univ)
    {φ : ℂ → ℂ} (hφ : Continuous φ)
    (hφconv : TendstoLocallyUniformlyOn (fun n w => uₙ n w / vₙ n w) φ atTop univ)
    (hsimple : ∀ z, φ z = 1 → deriv φ z ≠ 0) :
    IsNormal (range (fun n => sphereGermValue (F n))) univ := by
  apply sphere_isNormal_of_forall_isNormalAt
  intro z
  obtain ⟨Ω, hΩ, hzΩ, hev⟩ := hloc z
  exact auxiliary_pairs_isNormalAt_of_ratio_limit_eventually hΩ hev continuousOn_const
    continuousOn_const hφ.continuousOn (huconv.mono (subset_univ Ω))
    (hvconv.mono (subset_univ Ω)) (hφconv.mono (subset_univ Ω)) (fun w _ => hsimple w) hzΩ

theorem auxiliary_pairs_companion_isNormal_of_locally_eventually
    {F G uₙ vₙ : ℕ → ℂ → ℂ} {a : Fin 3 → ℂ}
    (hloc : ∀ z : ℂ, ∃ Ω : Set ℂ, IsOpen Ω ∧ z ∈ Ω ∧
      ∀ᶠ n in atTop, AuxiliaryPairOn Ω (F n) (G n) (uₙ n) (vₙ n) a)
    (hF : IsNormal (range (fun n => sphereGermValue (F n))) univ) :
    IsNormal (range (fun n => sphereGermValue (G n))) univ := by
  apply sphere_isNormal_of_forall_isNormalAt
  intro z
  obtain ⟨Ω, hΩ, hzΩ, hev⟩ := hloc z
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  have hseqN : ∀ n, AuxiliaryPairOn Ω (F (n + N)) (G (n + N))
      (uₙ (n + N)) (vₙ (n + N)) a := fun n => hN (n + N) (Nat.le_add_left N n)
  have hFT : IsNormal (range (fun n => sphereGermValue (F (n + N)))) Ω := by
    intro Q
    have hsub : ∀ n, (Q n : ℂ → OnePoint ℂ) ∈ range (fun n => sphereGermValue (F n)) := by
      intro n
      obtain ⟨k, hk⟩ := (Q n).property
      exact ⟨k + N, hk⟩
    obtain ⟨ψ, hψ, H, hc⟩ := hF (fun n => ⟨Q n, hsub n⟩)
    exact ⟨ψ, hψ, H, hc.mono (subset_univ Ω)⟩
  have hFG := sphere_companion_isNormalAt
    (fun n => sphereGermValue (F (n + N))) (fun n => sphereGermValue (G (n + N)))
    hΩ (fun n => sphereHolomorphicOn_sphereGermValue hΩ (hseqN n).pair.nonconst_f.1)
    (fun n => sphereHolomorphicOn_sphereGermValue hΩ (hseqN n).pair.nonconst_g.1)
    (normalizedSphereTargets a) (normalizedSphereTargets_injective (hseqN 0).pair.injective)
    (fun n => (hseqN n).pair.sphere_shares) hzΩ ⟨Ω, hΩ.mem_nhds hzΩ, hFT⟩
  exact isNormalAt_range_of_normal_tail (fun n => sphereGermValue (G n)) N hFG

end ThreeIM
