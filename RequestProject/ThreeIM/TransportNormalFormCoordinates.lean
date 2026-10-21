module

public import RequestProject.ThreeIM.TransportReconstruction

/-!
# Meromorphic normal forms for the actual transport coordinates

The coordinates are defined on the original domain even before absence of
poles is known. Their identities are identities of punctured germs. At an
initial point, analytic reconstructed germs identify their actual normal
form values without inspecting arbitrary raw representative values.
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

set_option autoImplicit false

noncomputable def transportNormalF (Ω : Set ℂ) (F : ℂ → ℂ) (c : ℂ) : ℂ → ℂ :=
  toMeromorphicNFOn (fun z => F z - c) Ω

noncomputable def transportNormalW (Ω : Set ℂ) (F G τ : ℂ → ℂ) (c : ℂ) : ℂ → ℂ :=
  toMeromorphicNFOn (fun z =>
    (transportNormalF Ω F c z - transportNormalF Ω G c z) / τ z) Ω

noncomputable def transportNormalH (Ω : Set ℂ) (F G : ℂ → ℂ) (c : ℂ) : ℂ → ℂ :=
  toMeromorphicNFOn (fun z => transportNormalF Ω G c z /
    (transportNormalF Ω F c z - transportNormalF Ω G c z)) Ω

theorem transport_normal_form_coordinates (Ω : Set ℂ) (F G τ : ℂ → ℂ) (c : ℂ) :
    MeromorphicNFOn (transportNormalF Ω F c) Ω ∧
      MeromorphicNFOn (transportNormalF Ω G c) Ω ∧
      MeromorphicNFOn (transportNormalW Ω F G τ c) Ω ∧
      MeromorphicNFOn (transportNormalH Ω F G c) Ω :=
  ⟨meromorphicNFOn_toMeromorphicNFOn _ _, meromorphicNFOn_toMeromorphicNFOn _ _,
    meromorphicNFOn_toMeromorphicNFOn _ _, meromorphicNFOn_toMeromorphicNFOn _ _⟩

theorem transport_normal_form_germs {Ω : Set ℂ} {F G τ : ℂ → ℂ} (c : ℂ)
    (hF : MeromorphicOn F Ω) (hG : MeromorphicOn G Ω) (hτ : MeromorphicOn τ Ω)
    {z : ℂ} (hz : z ∈ Ω) :
    (transportNormalF Ω F c =ᶠ[𝓝[≠] z] fun w => F w - c) ∧
      (transportNormalF Ω G c =ᶠ[𝓝[≠] z] fun w => G w - c) ∧
      (transportNormalW Ω F G τ c =ᶠ[𝓝[≠] z] fun w =>
        (transportNormalF Ω F c w - transportNormalF Ω G c w) / τ w) ∧
      (transportNormalH Ω F G c =ᶠ[𝓝[≠] z] fun w =>
        transportNormalF Ω G c w /
          (transportNormalF Ω F c w - transportNormalF Ω G c w)) := by
  have hFs : MeromorphicOn (fun w => F w - c) Ω :=
    fun w hw => (hF w hw).sub (MeromorphicAt.const c w)
  have hGs : MeromorphicOn (fun w => G w - c) Ω :=
    fun w hw => (hG w hw).sub (MeromorphicAt.const c w)
  have hn := transport_normal_form_coordinates Ω F G τ c
  have hW : MeromorphicOn (fun w =>
      (transportNormalF Ω F c w - transportNormalF Ω G c w) / τ w) Ω :=
    fun w hw => ((hn.1.meromorphicOn w hw).sub (hn.2.1.meromorphicOn w hw)).div (hτ w hw)
  have hH : MeromorphicOn (fun w => transportNormalF Ω G c w /
      (transportNormalF Ω F c w - transportNormalF Ω G c w)) Ω :=
    fun w hw => (hn.2.1.meromorphicOn w hw).div
      ((hn.1.meromorphicOn w hw).sub (hn.2.1.meromorphicOn w hw))
  exact ⟨hFs.toMeromorphicNFOn_eq_self_on_nhdsNE hz,
    hGs.toMeromorphicNFOn_eq_self_on_nhdsNE hz,
    hW.toMeromorphicNFOn_eq_self_on_nhdsNE hz,
    hH.toMeromorphicNFOn_eq_self_on_nhdsNE hz⟩

theorem transport_normal_form_initial_match
    {Ω : Set ℂ} {F G τ W₀ h₀ : ℂ → ℂ} {c z : ℂ}
    (hF : MeromorphicOn F Ω) (hG : MeromorphicOn G Ω) (hτΩ : MeromorphicOn τ Ω)
    (hz : z ∈ Ω) (hτ : AnalyticAt ℂ τ z) (hτ0 : τ z ≠ 0)
    (hW : AnalyticAt ℂ W₀ z) (hW0 : W₀ z ≠ 0) (hh : AnalyticAt ℂ h₀ z)
    (hFr : (fun w => F w - c) =ᶠ[𝓝[≠] z] fun w => τ w * W₀ w * (1 + h₀ w))
    (hGr : (fun w => G w - c) =ᶠ[𝓝[≠] z] fun w => τ w * W₀ w * h₀ w) :
    AnalyticAt ℂ (transportNormalW Ω F G τ c) z ∧
      AnalyticAt ℂ (transportNormalH Ω F G c) z ∧
      (transportNormalW Ω F G τ c =ᶠ[𝓝 z] W₀) ∧
      (transportNormalH Ω F G c =ᶠ[𝓝 z] h₀) := by
  have hn := transport_normal_form_coordinates Ω F G τ c
  have hg := transport_normal_form_germs c hF hG hτΩ hz
  have hf := hg.1.trans hFr
  have hgr := hg.2.1.trans hGr
  have hτne : ∀ᶠ w in 𝓝[≠] z, τ w ≠ 0 :=
    (hτ.continuousAt.eventually_ne hτ0).filter_mono nhdsWithin_le_nhds
  have hWne : ∀ᶠ w in 𝓝[≠] z, W₀ w ≠ 0 :=
    (hW.continuousAt.eventually_ne hW0).filter_mono nhdsWithin_le_nhds
  have hWeq : transportNormalW Ω F G τ c =ᶠ[𝓝[≠] z] W₀ := by
    filter_upwards [hg.2.2.1, hf, hgr, hτne] with w hw hfw hgw hτw
    rw [hw, hfw, hgw]
    field_simp [hτw] <;> ring
  have hHeq : transportNormalH Ω F G c =ᶠ[𝓝[≠] z] h₀ := by
    filter_upwards [hg.2.2.2, hf, hgr, hτne, hWne] with w hw hfw hgw hτw hWw
    rw [hw, hfw, hgw]
    have hden : τ w * W₀ w * (1 + h₀ w) - τ w * W₀ w * h₀ w = τ w * W₀ w := by ring
    rw [hden]
    field_simp [hτw, hWw]
  have hWfull := ((hn.2.2.1 hz).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
    hW.meromorphicNFAt).mp hWeq
  have hHfull := ((hn.2.2.2 hz).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
    hh.meromorphicNFAt).mp hHeq
  exact ⟨(analyticAt_congr hWfull).mpr hW, (analyticAt_congr hHfull).mpr hh, hWfull, hHfull⟩

end ThreeIM
