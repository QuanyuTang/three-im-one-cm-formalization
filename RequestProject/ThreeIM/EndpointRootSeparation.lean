module

public import RequestProject.ThreeIM.EndpointFiniteAnchors

/-! # A bounded endpoint cannot stay apart from every shared target

This consumer obtains its own joint spherical subsequence from the proved
normality theorem. The bounded center values represent honest germs; no
compactness or limiting auxiliary identity is supplied by the caller.
-/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

set_option autoImplicit false

private theorem root_separation_tlu_subsequence {X Y : Type*}
    [TopologicalSpace X] [UniformSpace Y]
    {F : ℕ → X → Y} {f : X → Y} {Ω : Set X}
    (h : TendstoLocallyUniformlyOn F f atTop Ω) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    TendstoLocallyUniformlyOn (fun n => F (φ n)) f atTop Ω := by
  intro e he z hz
  obtain ⟨t, ht, hev⟩ := h e he z hz
  exact ⟨t, ht, hφ.tendsto_atTop.eventually hev⟩

theorem auxiliary_endpoint_root_separation_false
    {r : ℕ → ℝ} (hr : Tendsto r atTop atTop)
    {F G uₙ vₙ : ℕ → ℂ → ℂ} {a : Fin 3 → ℂ}
    (hseq : ∀ n, AuxiliaryPairOn (ball 0 (r n)) (F n) (G n) (uₙ n) (vₙ n) a)
    {u : ℂ → ℂ} (hu : Differentiable ℂ u) (hu0 : ∀ z, u z ≠ 0)
    (huconv : TendstoLocallyUniformlyOn uₙ u atTop univ)
    (hvconv : TendstoLocallyUniformlyOn vₙ (fun _ => 0) atTop univ)
    {vF vG : ℕ → ℂ} {MF MG γ : ℝ}
    (hFvalues : ∀ᶠ n in atTop, sphereGermValue (F n) 0 = (vF n : OnePoint ℂ))
    (hGvalues : ∀ᶠ n in atTop, sphereGermValue (G n) 0 = (vG n : OnePoint ℂ))
    (hFbound : ∀ᶠ n in atTop, ‖vF n‖ ≤ MF)
    (hGbound : ∀ᶠ n in atTop, ‖vG n‖ ≤ MG)
    (hγ : 0 < γ) (hsep : ∀ᶠ n in atTop, ∀ j : Fin 3, γ ≤ ‖vF n - a j‖) : False := by
  classical
  have hn := auxiliary_endpoint_isNormal hr hseq hu.continuous hu0 huconv hvconv
  obtain ⟨φ, hφ, H, hFconv⟩ := hn.1
    (fun n => ⟨sphereGermValue (F n), mem_range_self n⟩)
  obtain ⟨ψ, hψ, K, hGconv⟩ := hn.2
    (fun n => ⟨sphereGermValue (G (φ n)), mem_range_self (φ n)⟩)
  let σ : ℕ → ℕ := φ ∘ ψ
  have hσ : StrictMono σ := hφ.comp hψ
  have hFσ : TendstoLocallyUniformlyOn (fun n => sphereGermValue (F (σ n)))
      H atTop univ := root_separation_tlu_subsequence hFconv hψ
  have hGσ : TendstoLocallyUniformlyOn (fun n => sphereGermValue (G (σ n)))
      K atTop univ := hGconv
  obtain ⟨c, d, _hc, _hd, hH, _hK, hPc⟩ := auxiliary_endpoint_bounded_values_cubic
    (hr.comp hσ.tendsto_atTop) (fun n => hseq (σ n)) hu hu0
    (root_separation_tlu_subsequence huconv hσ)
    (root_separation_tlu_subsequence hvconv hσ) hFσ hGσ
    (hσ.tendsto_atTop.eventually hFvalues) (hσ.tendsto_atTop.eventually hGvalues)
    (hσ.tendsto_atTop.eventually hFbound) (hσ.tendsto_atTop.eventually hGbound)
  have hcenter := hFσ.tendsto_at (mem_univ (0 : ℂ))
  rw [hH 0] at hcenter
  have hcoe : Tendsto (fun n => (vF (σ n) : OnePoint ℂ)) atTop (𝓝 (c : OnePoint ℂ)) :=
    hcenter.congr' (hσ.tendsto_atTop.eventually hFvalues)
  have hc : Tendsto (fun n => vF (σ n)) atTop (𝓝 c) :=
    OnePoint.isOpenEmbedding_coe.tendsto_nhds_iff.mpr hcoe
  have hj : ∃ j : Fin 3, c = a j := by
    simp only [cubicP, mul_eq_zero, sub_eq_zero] at hPc
    rcases hPc with (h0 | h1) | h2
    · exact ⟨0, h0⟩
    · exact ⟨1, h1⟩
    · exact ⟨2, h2⟩
  obtain ⟨j, hcj⟩ := hj
  have hnorm := (hc.sub_const (a j)).norm
  have hbound : ∀ᶠ n in atTop, γ ≤ ‖vF (σ n) - a j‖ :=
    (hσ.tendsto_atTop.eventually hsep).mono fun n hn => hn j
  have hle := ge_of_tendsto hnorm hbound
  rw [hcj, sub_self, norm_zero] at hle
  exact (not_le_of_gt hγ) hle

end ThreeIM
