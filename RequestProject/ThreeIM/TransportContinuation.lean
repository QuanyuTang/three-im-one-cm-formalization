module

public import RequestProject.ThreeIM.TransportAnalytic
public import RequestProject.ThreeIM.TransportODE
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Continuation of the stable transport region through meromorphic germs

The maps in the transport lemma already exist meromorphically on a domain
containing the real segment. No ODE existence theorem or path lifting is
needed to continue their regular representatives. What must be excluded is
an endpoint pole, or departure from the bootstrap region.

For meromorphic normal forms, the set of regular points with fixed bounded
values is closed along the segment: at a new cluster point, a bounded
approach rules out a pole and the normal form is then analytic. Continuous
induction and the previously proved stable bootstrap extend the improved
bounds to the whole segment. The ODE hypotheses below are required only at
regular points inside the proposed bootstrap region. Global absence of
poles is a conclusion, not an assumption.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace ThreeIM

private theorem transport_tendsto_ofReal_punctured {S : Set ℝ} {t : ℝ}
    (ht : t ∉ S) :
    Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[S] t) (𝓝[≠] (t : ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · exact Complex.continuous_ofReal.continuousAt.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx
    intro hxt
    exact ht ((Complex.ofReal_injective hxt) ▸ hx)

/-- A bounded region of regular normal-form values is closed along a closed
real segment. At a new cluster point the proof excludes a pole using the
bounded approach, rather than assuming a continuous endpoint value. -/
theorem transport_isClosed_bounded_regular_region
    {Ω : Set ℂ} {W h : ℂ → ℂ} {a b R B : ℝ} {c : ℂ}
    (hW : MeromorphicNFOn W Ω) (hh : MeromorphicNFOn h Ω)
    (hsegment : ∀ t ∈ Icc a b, (t : ℂ) ∈ Ω) :
    IsClosed {t : ℝ | t ∈ Icc a b ∧ AnalyticAt ℂ W (t : ℂ) ∧
      AnalyticAt ℂ h (t : ℂ) ∧ ‖W (t : ℂ) - c‖ ≤ R ∧ ‖h (t : ℂ)‖ ≤ B} := by
  let S : Set ℝ := {t | t ∈ Icc a b ∧ AnalyticAt ℂ W (t : ℂ) ∧
    AnalyticAt ℂ h (t : ℂ) ∧ ‖W (t : ℂ) - c‖ ≤ R ∧ ‖h (t : ℂ)‖ ≤ B}
  change IsClosed S
  apply isClosed_iff_clusterPt.mpr
  intro t hcluster
  by_cases ht : t ∈ S
  · exact ht
  haveI : NeBot (𝓝[S] t) := hcluster
  have hlim : Tendsto (fun x : ℝ => x) (𝓝[S] t) (𝓝 t) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hmem : ∀ᶠ x in 𝓝[S] t, x ∈ S := self_mem_nhdsWithin
  have htab : t ∈ Icc a b :=
    isClosed_Icc.mem_of_tendsto hlim (hmem.mono fun _ hx => hx.1)
  have hγ := transport_tendsto_ofReal_punctured ht
  have hWbound : ∀ᶠ (x : ℝ) in 𝓝[S] t, ‖W (x : ℂ)‖ ≤ R + ‖c‖ := by
    filter_upwards [hmem] with x hx
    have htriangle := norm_add_le (W (x : ℂ) - c) c
    rw [sub_add_cancel] at htriangle
    linarith [hx.2.2.2.1]
  have hhbound : ∀ᶠ (x : ℝ) in 𝓝[S] t, ‖h (x : ℂ)‖ ≤ B :=
    hmem.mono fun _ hx => hx.2.2.2.2
  have hWa : AnalyticAt ℂ W (t : ℂ) :=
    (hW (hsegment t htab)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
      (transport_order_nonneg_of_bounded_approach hγ hWbound)
  have hha : AnalyticAt ℂ h (t : ℂ) :=
    (hh (hsegment t htab)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
      (transport_order_nonneg_of_bounded_approach hγ hhbound)
  have hWlim : Tendsto (fun x : ℝ => ‖W (x : ℂ) - c‖) (𝓝[S] t)
      (𝓝 ‖W (t : ℂ) - c‖) :=
    ((hWa.continuousAt.sub_const c).norm.comp
      Complex.continuous_ofReal.continuousAt).mono_left nhdsWithin_le_nhds
  have hhlim : Tendsto (fun x : ℝ => ‖h (x : ℂ)‖) (𝓝[S] t) (𝓝 ‖h (t : ℂ)‖) :=
    (hha.continuousAt.norm.comp
      Complex.continuous_ofReal.continuousAt).mono_left nhdsWithin_le_nhds
  exact ⟨htab, hWa, hha,
    le_of_tendsto hWlim (hmem.mono fun _ hx => hx.2.2.2.1),
    le_of_tendsto hhlim hhbound⟩

/-- The stable transport bootstrap for meromorphic normal-form coordinates.
Analyticity is assumed only at the initial point. The equations and error
bounds are needed only at regular points in the outer bootstrap region.
They force regularity, the improved bounds, and nonvanishing of `W` on the
entire real segment. This removes the global-continuity premise of
`transport_bootstrap` in the setting actually used by the manuscript. -/
theorem transport_meromorphic_continuation
    {Ω : Set ℂ} {W h : ℂ → ℂ} {E v : ℝ → ℂ} {a b r₀ b₀ : ℝ} {α : ℂ}
    (hab : a ≤ b) (hr₀ : 0 < r₀) (hb₀ : 0 < b₀) (hrα : r₀ < ‖α‖)
    (hW : MeromorphicNFOn W Ω) (hh : MeromorphicNFOn h Ω)
    (hsegment : ∀ t ∈ Icc a b, (t : ℂ) ∈ Ω)
    (hWa : AnalyticAt ℂ W (a : ℂ)) (hha : AnalyticAt ℂ h (a : ℂ))
    (hode : ∀ t ∈ Icc a b, AnalyticAt ℂ W (t : ℂ) → AnalyticAt ℂ h (t : ℂ) →
      ‖W (t : ℂ) - 2 * α‖ ≤ r₀ → ‖h (t : ℂ)‖ ≤ b₀ →
      HasDerivAt (fun x : ℝ => W (x : ℂ))
        ((-(1 / 2 : ℝ)) • (W (t : ℂ) - 2 * α) + E t) t)
    (hderiv : ∀ t ∈ Icc a b, AnalyticAt ℂ W (t : ℂ) → AnalyticAt ℂ h (t : ℂ) →
      ‖W (t : ℂ) - 2 * α‖ ≤ r₀ → ‖h (t : ℂ)‖ ≤ b₀ →
      HasDerivAt (fun x : ℝ => h (x : ℂ)) (v t) t)
    (herror : ∀ t ∈ Icc a b, AnalyticAt ℂ W (t : ℂ) → AnalyticAt ℂ h (t : ℂ) →
      ‖W (t : ℂ) - 2 * α‖ ≤ r₀ → ‖h (t : ℂ)‖ ≤ b₀ → ‖E t‖ ≤ r₀ / 4)
    (hne : ∀ t ∈ Icc a b, AnalyticAt ℂ W (t : ℂ) → AnalyticAt ℂ h (t : ℂ) →
      ‖W (t : ℂ) - 2 * α‖ ≤ r₀ → ‖h (t : ℂ)‖ ≤ b₀ → h (t : ℂ) ≠ 0)
    (hlog : ∀ t ∈ Icc a b, AnalyticAt ℂ W (t : ℂ) → AnalyticAt ℂ h (t : ℂ) →
      ‖W (t : ℂ) - 2 * α‖ ≤ r₀ → ‖h (t : ℂ)‖ ≤ b₀ →
      (v t / h (t : ℂ)).re ≤ 0)
    (hWinit : ‖W (a : ℂ) - 2 * α‖ ≤ r₀ / 4)
    (hhinit : ‖h (a : ℂ)‖ ≤ b₀ / 2) :
    ∀ t ∈ Icc a b, AnalyticAt ℂ W (t : ℂ) ∧ AnalyticAt ℂ h (t : ℂ) ∧
      ‖W (t : ℂ) - 2 * α‖ ≤ r₀ / 2 ∧ ‖h (t : ℂ)‖ ≤ b₀ / 2 ∧
      ‖h (t : ℂ)‖ ≤ ‖h (a : ℂ)‖ ∧ W (t : ℂ) ≠ 0 := by
  let S : Set ℝ := {t | t ∈ Icc a b ∧ AnalyticAt ℂ W (t : ℂ) ∧
    AnalyticAt ℂ h (t : ℂ) ∧
    ‖W (t : ℂ) - 2 * α‖ ≤ r₀ / 2 ∧ ‖h (t : ℂ)‖ ≤ b₀ / 2}
  have hSclosed : IsClosed S := transport_isClosed_bounded_regular_region hW hh hsegment
  have haS : a ∈ S :=
    ⟨⟨le_rfl, hab⟩, hWa, hha, by linarith, hhinit⟩
  have hstep : ∀ x ∈ Ico a b, Icc a x ⊆ S → S ∈ 𝓝[>] x := by
    intro x hx hprefix
    have hxS := hprefix (right_mem_Icc.mpr hx.1)
    let R : Set ℝ := {s | AnalyticAt ℂ W (s : ℂ) ∧ AnalyticAt ℂ h (s : ℂ) ∧
      ‖W (s : ℂ) - 2 * α‖ ≤ r₀ ∧ ‖h (s : ℂ)‖ ≤ b₀}
    have hWregular : ∀ᶠ (s : ℝ) in 𝓝 x, AnalyticAt ℂ W (s : ℂ) :=
      Complex.continuous_ofReal.continuousAt.eventually hxS.2.1.eventually_analyticAt
    have hhregular : ∀ᶠ (s : ℝ) in 𝓝 x, AnalyticAt ℂ h (s : ℂ) :=
      Complex.continuous_ofReal.continuousAt.eventually hxS.2.2.1.eventually_analyticAt
    have hWlt : ‖W (x : ℂ) - 2 * α‖ < r₀ := by
      have := hxS.2.2.2.1
      linarith
    have hhlt : ‖h (x : ℂ)‖ < b₀ := by
      have := hxS.2.2.2.2
      linarith
    have hWsmall : ∀ᶠ (s : ℝ) in 𝓝 x, ‖W (s : ℂ) - 2 * α‖ < r₀ :=
      ((hxS.2.1.continuousAt.sub_const (2 * α)).norm.comp
        Complex.continuous_ofReal.continuousAt).eventually (gt_mem_nhds hWlt)
    have hhsmall : ∀ᶠ (s : ℝ) in 𝓝 x, ‖h (s : ℂ)‖ < b₀ :=
      (hxS.2.2.1.continuousAt.norm.comp
        Complex.continuous_ofReal.continuousAt).eventually (gt_mem_nhds hhlt)
    have hR : R ∈ 𝓝[>] x := by
      apply Filter.mem_of_superset
        ((hWregular.and (hhregular.and (hWsmall.and hhsmall))).filter_mono nhdsWithin_le_nhds)
      intro s hs
      exact ⟨hs.1, hs.2.1, hs.2.2.1.le, hs.2.2.2.le⟩
    obtain ⟨u, hxu, hU⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hR
    apply mem_nhdsGT_iff_exists_Ioo_subset.mpr
    refine ⟨min u b, lt_min hxu hx.2, ?_⟩
    intro t ht
    have htab : t ∈ Icc a b :=
      ⟨hx.1.trans ht.1.le, ht.2.le.trans (min_le_right _ _)⟩
    have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl htab.2
    have hregular : ∀ s ∈ Icc a t, s ∈ R := by
      intro s hs
      rcases le_or_gt s x with hsx | hsx
      · have hsS := hprefix ⟨hs.1, hsx⟩
        exact ⟨hsS.2.1, hsS.2.2.1, by have := hsS.2.2.2.1; linarith,
          by have := hsS.2.2.2.2; linarith⟩
      · exact hU ⟨hsx, hs.2.trans_lt (ht.2.trans_le (min_le_left _ _))⟩
    have hWcont : ContinuousOn (fun s : ℝ => W (s : ℂ)) (Icc a t) := by
      intro s hs
      exact ((hregular s hs).1.continuousAt.comp
        Complex.continuous_ofReal.continuousAt).continuousWithinAt
    have hhcont : ContinuousOn (fun s : ℝ => h (s : ℂ)) (Icc a t) := by
      intro s hs
      exact ((hregular s hs).2.1.continuousAt.comp
        Complex.continuous_ofReal.continuousAt).continuousWithinAt
    have htrap := transport_bootstrap (W := fun s : ℝ => W (s : ℂ))
      (h := fun s : ℝ => h (s : ℂ)) (a := a) (b := t) hr₀ hb₀ hWcont hhcont
      (fun s hs hw hb => hode s (hsub hs) (hregular s hs).1 (hregular s hs).2.1 hw hb)
      (fun s hs hw hb => hderiv s (hsub hs) (hregular s hs).1 (hregular s hs).2.1 hw hb)
      (fun s hs hw hb => herror s (hsub hs) (hregular s hs).1 (hregular s hs).2.1 hw hb)
      (fun s hs hw hb => hne s (hsub hs) (hregular s hs).1 (hregular s hs).2.1 hw hb)
      (fun s hs hw hb => hlog s (hsub hs) (hregular s hs).1 (hregular s hs).2.1 hw hb)
      hWinit hhinit
    have htt : t ∈ Icc a t := right_mem_Icc.mpr htab.1
    exact ⟨htab, (hregular t htt).1, (hregular t htt).2.1, htrap t htt⟩
  have hall : Icc a b ⊆ S :=
    (hSclosed.inter isClosed_Icc).Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset haS hstep
  have hregular : ∀ s ∈ Icc a b, AnalyticAt ℂ W (s : ℂ) ∧ AnalyticAt ℂ h (s : ℂ) ∧
      ‖W (s : ℂ) - 2 * α‖ ≤ r₀ ∧ ‖h (s : ℂ)‖ ≤ b₀ := by
    intro s hs
    have hsS := hall hs
    exact ⟨hsS.2.1, hsS.2.2.1, by have := hsS.2.2.2.1; linarith,
      by have := hsS.2.2.2.2; linarith⟩
  have hdecay := norm_le_initial_of_re_log_deriv_nonpos
    (h := fun s : ℝ => h (s : ℂ)) (a := a) (b := b)
    (fun s hs => hderiv s hs (hregular s hs).1 (hregular s hs).2.1
      (hregular s hs).2.2.1 (hregular s hs).2.2.2)
    (fun s hs => hne s (Ico_subset_Icc_self hs)
      (hregular s (Ico_subset_Icc_self hs)).1 (hregular s (Ico_subset_Icc_self hs)).2.1
      (hregular s (Ico_subset_Icc_self hs)).2.2.1 (hregular s (Ico_subset_Icc_self hs)).2.2.2)
    (fun s hs => hlog s (Ico_subset_Icc_self hs)
      (hregular s (Ico_subset_Icc_self hs)).1 (hregular s (Ico_subset_Icc_self hs)).2.1
      (hregular s (Ico_subset_Icc_self hs)).2.2.1 (hregular s (Ico_subset_Icc_self hs)).2.2.2)
  intro t ht
  have htS := hall ht
  have hnonzero : W (t : ℂ) ≠ 0 := by
    intro hzero
    have hbound := htS.2.2.2.1
    rw [hzero, zero_sub, norm_neg, norm_mul] at hbound
    norm_num at hbound
    linarith [norm_nonneg α]
  exact ⟨htS.2.1, htS.2.2.1, htS.2.2.2.1, htS.2.2.2.2, hdecay t ht, hnonzero⟩

end ThreeIM
