module

public import RequestProject.ThreeIM.SphereGerm
public import NoWanderingDomains.Sphere.SphereHolomorphic
public import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# The chart-holomorphic sphere map of a meromorphic germ

This interface verifies that the corrected sphere representation of the
original meromorphic functions satisfies the actual local chart definition
used by the normal-families library. No normality assumption is added.
-/

@[expose] public section

open Filter Set Topology
open NoWanderingDomains

namespace ThreeIM

theorem sphereHolomorphicOn_sphereGermValue {f : ℂ → ℂ} {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hf : MeromorphicOn f Ω) :
    SphereHolomorphicOn (sphereGermValue f) Ω := by
  classical
  intro z hz
  by_cases hn : meromorphicOrderAt f z < 0
  · obtain ⟨H, hHa, _, hne, heq⟩ := sphereGermValue_infty_chart (hf z hz) hn
    have hgood : ∀ᶠ w in 𝓝 z,
        w ∈ Ω ∧ AnalyticAt ℂ H w ∧
          sphereGermValue f w ≠ ((0 : ℂ) : OnePoint ℂ) ∧
          sphereGermValue f w =
            (if H w = 0 then OnePoint.infty else (((H w)⁻¹ : ℂ) : OnePoint ℂ)) := by
      filter_upwards [hΩ.mem_nhds hz, hHa.eventually_analyticAt, hne, heq]
        with w hw ha h0 he
      exact ⟨hw, ha, h0, he⟩
    obtain ⟨V, hV, hVo, hzV⟩ := eventually_nhds_iff.mp hgood
    refine ⟨V, hVo, hzV, fun w hw => (hV w hw).1, Or.inr ⟨?_, ?_⟩⟩
    · exact fun w hw => (hV w hw).2.2.1
    · have hH : DifferentiableOn ℂ H V := fun w hw =>
        (hV w hw).2.1.differentiableAt.differentiableWithinAt
      apply hH.congr
      intro w hw
      rw [(hV w hw).2.2.2]
      by_cases h0 : H w = 0
      · simp only [h0, ↓reduceIte]
        rfl
      · simp only [h0, ↓reduceIte]
        exact inv_inv (H w)
  · obtain ⟨H, hHa, heq⟩ := sphereGermValue_finite_chart (hf z hz) (le_of_not_gt hn)
    have hgood : ∀ᶠ w in 𝓝 z,
        w ∈ Ω ∧ AnalyticAt ℂ H w ∧ sphereGermValue f w = (H w : OnePoint ℂ) := by
      filter_upwards [hΩ.mem_nhds hz, hHa.eventually_analyticAt, heq] with w hw ha he
      exact ⟨hw, ha, he⟩
    obtain ⟨V, hV, hVo, hzV⟩ := eventually_nhds_iff.mp hgood
    refine ⟨V, hVo, hzV, fun w hw => (hV w hw).1, Or.inl ⟨?_, ?_⟩⟩
    · intro w hw
      rw [(hV w hw).2.2]
      exact OnePoint.coe_ne_infty _
    · have hH : DifferentiableOn ℂ H V := fun w hw =>
        (hV w hw).2.1.differentiableAt.differentiableWithinAt
      apply hH.congr
      intro w hw
      rw [(hV w hw).2.2]
      rfl

theorem chartFiniteMap_eq_inv_chartInftyMap (p : OnePoint ℂ) :
    chartFiniteMap p = (chartInftyMap p)⁻¹ := by
  cases p with
  | infty => exact inv_zero.symm
  | coe c => exact (inv_inv c).symm

/-- The finite reading of a sphere-holomorphic map is meromorphic even though
its totalized value at an infinity point is zero. -/
theorem meromorphicOn_chartFiniteMap {F : ℂ → OnePoint ℂ} {Ω : Set ℂ}
    (hF : SphereHolomorphicOn F Ω) :
    MeromorphicOn (fun w => chartFiniteMap (F w)) Ω := by
  intro z hz
  obtain ⟨V, hVo, hzV, _, hcase⟩ := hF z hz
  rcases hcase with ⟨_, hd⟩ | ⟨_, hd⟩
  · exact (hd.analyticAt (hVo.mem_nhds hzV)).meromorphicAt
  · have hread : (fun w => chartFiniteMap (F w)) =
        (fun w => (chartInftyMap (F w))⁻¹) :=
      funext fun w => chartFiniteMap_eq_inv_chartInftyMap (F w)
    rw [hread]
    exact (hd.analyticAt (hVo.mem_nhds hzV)).meromorphicAt.inv

theorem analyticAt_chartFiniteMap_of_ne_infty {F : ℂ → OnePoint ℂ}
    {Ω : Set ℂ} (hF : SphereHolomorphicOn F Ω) {z : ℂ} (hz : z ∈ Ω)
    (hne : F z ≠ OnePoint.infty) :
    AnalyticAt ℂ (fun w => chartFiniteMap (F w)) z := by
  obtain ⟨V, hVo, hzV, _, hcase⟩ := hF z hz
  rcases hcase with ⟨_, hd⟩ | ⟨h0, hd⟩
  · exact (hd.analyticAt (hVo.mem_nhds hzV))
  · have hread : (fun w => chartFiniteMap (F w)) =
        (fun w => (chartInftyMap (F w))⁻¹) :=
      funext fun w => chartFiniteMap_eq_inv_chartInftyMap (F w)
    rw [hread]
    apply (hd.analyticAt (hVo.mem_nhds hzV)).inv
    cases hv : F z with
    | infty => exact (hne hv).elim
    | coe c =>
      change c⁻¹ ≠ 0
      apply inv_ne_zero
      intro hc
      subst c
      exact h0 z hzV hv

/-- Nonconstancy of a genuine sphere map excludes every locally constant
finite germ of its meromorphic representative. The constant-infinity case
is excluded by the same hypothesis, rather than by a chart convention. -/
theorem isNonconstMeroOn_chartFiniteMap {F : ℂ → OnePoint ℂ}
    (hF : SphereHolomorphicOn F univ)
    (hnc : ¬ ∃ p : OnePoint ℂ, ∀ z, F z = p) :
    IsNonconstMeroOn (fun w => chartFiniteMap (F w)) univ := by
  let f : ℂ → ℂ := fun w => chartFiniteMap (F w)
  have hm : MeromorphicOn f univ := meromorphicOn_chartFiniteMap hF
  refine ⟨hm, fun z _ c htop => ?_⟩
  have hd : MeromorphicOn (fun w => f w - c) univ := hm.sub (MeromorphicOn.const c)
  have hall : ∀ x : ℂ, meromorphicOrderAt (fun w => f w - c) x = ⊤ := by
    by_contra hne
    push_neg at hne
    obtain ⟨x, hx⟩ := hne
    exact ((hd.exists_meromorphicOrderAt_ne_top_iff_forall isConnected_univ).1
      ⟨⟨x, mem_univ x⟩, hx⟩ ⟨z, mem_univ z⟩) htop
  have hmaps : MapsTo F univ {((c : ℂ) : OnePoint ℂ), OnePoint.infty} := by
    intro x _
    by_cases hxi : F x = OnePoint.infty
    · simp only [mem_insert_iff, mem_singleton_iff]
      exact Or.inr hxi
    · have ha := analyticAt_chartFiniteMap_of_ne_infty hF (mem_univ x) hxi
      have heq : f =ᶠ[𝓝[≠] x] (fun _ => c) := by
        filter_upwards [meromorphicOrderAt_eq_top_iff.1 (hall x)] with w hw
        exact sub_eq_zero.1 hw
      have hfx : f x = c := tendsto_nhds_unique
        (ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
        (tendsto_const_nhds.congr' heq.symm)
      have hx : F x = (c : OnePoint ℂ) := by
        cases hv : F x with
        | infty => exact (hxi hv).elim
        | coe v =>
          have hvc : v = c := by simpa only [f, hv, chartFiniteMap] using hfx
          rw [hvc]
      exact Or.inl hx
  have hdisc : IsDiscrete ({((c : ℂ) : OnePoint ℂ), OnePoint.infty} : Set (OnePoint ℂ)) :=
    ((Set.finite_singleton _).insert _).isDiscrete
  apply hnc
  exact ⟨F 0, fun x => isPreconnected_univ.constant_of_mapsTo hdisc hF.continuousOn hmaps
    (mem_univ x) (mem_univ 0)⟩

/-- The meromorphic representative of a nonconstant sphere-holomorphic map
recovers every honest sphere value, including at infinity. -/
theorem sphereGermValue_chartFiniteMap {F : ℂ → OnePoint ℂ}
    (hF : SphereHolomorphicOn F univ)
    (hnc : ¬ ∃ p : OnePoint ℂ, ∀ z, F z = p) (z : ℂ) :
    sphereGermValue (fun w => chartFiniteMap (F w)) z = F z := by
  let f : ℂ → ℂ := fun w => chartFiniteMap (F w)
  have hf : IsNonconstMeroOn f univ := isNonconstMeroOn_chartFiniteMap hF hnc
  have hfnz : ∀ᶠ w in 𝓝[≠] z, f w ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hf.1 z (mem_univ z))).1
      (by simpa only [sub_zero] using hf.2 z (mem_univ z) 0)
  have heq : (fun w => (f w : OnePoint ℂ)) =ᶠ[𝓝[≠] z] F := by
    filter_upwards [hfnz] with w hw
    cases hv : F w with
    | infty => exact (hw (by simp only [f, hv, chartFiniteMap])).elim
    | coe c => simp only [f, hv, chartFiniteMap]
  apply tendsto_nhds_unique (tendsto_sphereGermValue (hf.1 z (mem_univ z)))
  exact (hF.continuousOn.continuousAt (isOpen_univ.mem_nhds (mem_univ z))).tendsto
    |>.mono_left nhdsWithin_le_nhds |>.congr' heq.symm

end ThreeIM
