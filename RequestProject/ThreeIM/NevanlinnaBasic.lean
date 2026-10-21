module

public import RequestProject.ThreeIM.Growth

/-!
# Basic facts of Nevanlinna theory for meromorphic functions on `ℂ`

Generic facts used throughout: a nonconstant meromorphic function is analytic and nonzero off
discrete sets, `N(r, 1/F) ≤ T(r, F) + O(1)` (first main theorem) and `T(r, h) ≥ 1` for large `r`.
-/

@[expose] public section

open Filter Set Topology ValueDistribution Real MeasureTheory

namespace ThreeIM

/-- Codiscrete in `ℂ` means eventually in every punctured neighbourhood. -/
lemma codiscrete_iff_nhdsNE {p : ℂ → Prop} :
    (∀ᶠ z in codiscrete ℂ, p z) ↔ ∀ x, ∀ᶠ z in 𝓝[≠] x, p z := by
  rw [Filter.Eventually, mem_codiscrete]
  simp only [disjoint_principal_right, compl_compl]
  rfl

lemma IsNonconstMeroOn.meromorphic {h : ℂ → ℂ} (hh : IsNonconstMeroOn h univ) : Meromorphic h :=
  fun x => hh.1 x (mem_univ x)

/-- A meromorphic function on `ℂ` with finite order everywhere is nonzero off a discrete set. -/
lemma eventually_ne_zero_of_order_ne_top {F : ℂ → ℂ} (hF : Meromorphic F)
    (h : ∀ z, meromorphicOrderAt F z ≠ ⊤) : ∀ᶠ z in codiscrete ℂ, F z ≠ 0 := by
  refine codiscrete_iff_nhdsNE.2 fun x => ?_
  rcases (hF x).eventually_eq_zero_or_eventually_ne_zero with h0 | h0
  · exact absurd (meromorphicOrderAt_eq_top_iff.2 h0) (h x)
  · exact h0

/-- A meromorphic function on `ℂ` is analytic off a discrete set. -/
lemma eventually_analyticAt_of_meromorphic {F : ℂ → ℂ} (hF : Meromorphic F) :
    ∀ᶠ z in codiscrete ℂ, AnalyticAt ℂ F z :=
  MeromorphicOn.eventually_codiscreteWithin_analyticAt F (fun x _ => hF x)

/-- First main theorem: `N(r, 1/F) ≤ T(r, F) + O(1)`. -/
lemma logCounting_zero_le_charT {F : ℂ → ℂ} (hF : Meromorphic F) :
    ∃ K : ℝ, ∀ r : ℝ, 1 ≤ r → logCounting F 0 r ≤ charT F r + K := by
  refine ⟨max |log ‖F 0‖| |log ‖meromorphicTrailingCoeffAt F 0‖|, fun r hr => ?_⟩
  have h2 := characteristic_sub_characteristic_inv_le (R := r) hF
  have h3 : logCounting F⁻¹ ⊤ r ≤ characteristic F⁻¹ ⊤ r := by
    unfold characteristic
    simp only [Pi.add_apply]
    have := proximity_nonneg (f := F⁻¹) (a := ⊤) r
    simp only [Pi.zero_apply] at this
    linarith
  rw [logCounting_inv] at h3
  unfold charT
  rw [abs_le] at h2
  linarith [h2.1]

/-- A nonconstant meromorphic function on `ℂ` has `T(r, h) ≥ 1` for large `r`
(indeed `T(r, h) ≥ log r - O(1)`). -/
lemma one_le_charT_eventually {h : ℂ → ℂ} (hh : IsNonconstMeroOn h univ) :
    ∃ r₀ : ℝ, ∀ r ≥ r₀, 1 ≤ charT h r := by
  have hm := hh.meromorphic
  obtain ⟨z₁, hz₁a, hz₁0⟩ : ∃ z₁, AnalyticAt ℂ h z₁ ∧ z₁ ≠ 0 := by
    have h1 := eventually_analyticAt_of_meromorphic hm
    have h2 : ∀ᶠ z in 𝓝[≠] (1 : ℂ), z ≠ 0 :=
      nhdsWithin_le_nhds (isOpen_ne.mem_nhds one_ne_zero)
    exact ((codiscrete_iff_nhdsNE.1 h1 1).and h2).exists
  set v := h z₁
  set F : ℂ → ℂ := fun w => h w - v with hF
  have hFm : Meromorphic F := fun x => (hm x).sub (MeromorphicAt.const v x)
  have hFm' : MeromorphicOn F univ := fun x _ => hFm x
  have hFpos : 0 < meromorphicOrderAt F z₁ := by
    rw [← tendsto_zero_iff_meromorphicOrderAt_pos (hFm z₁)]
    have hc : ContinuousAt F z₁ := (hz₁a.sub analyticAt_const).continuousAt
    have : F z₁ = 0 := by simp [F, v]
    rw [← this]
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have hFtop : meromorphicOrderAt F z₁ ≠ ⊤ := hh.2 z₁ (mem_univ z₁) v
  have hD1 : 1 ≤ (MeromorphicOn.divisor F univ)⁺ z₁ := by
    rw [Function.locallyFinsuppWithin.posPart_apply, MeromorphicOn.divisor_apply hFm' (mem_univ z₁)]
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hFtop
    rw [← hn] at hFpos ⊢
    have : (0 : ℤ) < n := by exact_mod_cast hFpos
    simp only [WithTop.untop₀_coe]
    exact le_sup_of_le_left (by omega)
  obtain ⟨K, hK⟩ := logCounting_zero_le_charT hFm
  have hshift := fun r : ℝ => abs_characteristic_sub_characteristic_shift_le (r := r) (a₀ := v) hm
  refine ⟨max (max 1 ‖z₁‖) (exp (1 + K + log⁺ ‖v‖ + log 2 + log ‖z₁‖)), fun r hr => ?_⟩
  have hr1 : 1 ≤ r := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hr)
  have hrz : ‖z₁‖ ≤ r := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hr)
  have hre : exp (1 + K + log⁺ ‖v‖ + log 2 + log ‖z₁‖) ≤ r := le_trans (le_max_right _ _) hr
  have hsum := logCounting_ge_sum _ (posPart_nonneg _) hr1 {z₁}
    (by intro z hz; rw [Finset.mem_singleton] at hz; subst hz; exact ⟨hD1, hrz, hz₁0⟩)
  rw [Finset.sum_singleton] at hsum
  have hN : logCounting F 0 r = Function.locallyFinsuppWithin.logCounting
      (MeromorphicOn.divisor F univ)⁺ r := by rw [logCounting_zero]
  have e1 := hK r hr1
  have e2 := hshift r
  rw [abs_le] at e2
  have hz₁pos : 0 < ‖z₁‖ := norm_pos_iff.2 hz₁0
  have hlog : log (r * ‖z₁‖⁻¹) = log r - log ‖z₁‖ := by
    rw [Real.log_mul (by linarith) (inv_ne_zero hz₁pos.ne'), Real.log_inv]; ring
  have hlr : 1 + K + log⁺ ‖v‖ + log 2 + log ‖z₁‖ ≤ log r := by
    rw [Real.le_log_iff_exp_le (by linarith)]; exact hre
  unfold charT at e1 ⊢
  linarith

end ThreeIM
