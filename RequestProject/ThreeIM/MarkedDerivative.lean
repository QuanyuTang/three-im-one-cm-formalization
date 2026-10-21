module

public import RequestProject.ThreeIM.Local

/-! # A simple shared point determines its auxiliary coefficient -/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

/-- Value of `U` at a common `a_j`-point where `f` is simple: `U → (f' - g')/P'(a_j)`. -/
theorem tendsto_auxU_at_simple_analytic {f g : ℂ → ℂ} {t₀ : ℂ} {a : Fin 3 → ℂ} (ha : Function.Injective a)
    {j : Fin 3} (hf : AnalyticAt ℂ f t₀) (hg : AnalyticAt ℂ g t₀) (hf0 : f t₀ = a j)
    (hg0 : g t₀ = a j) (hf' : deriv f t₀ ≠ 0) :
    Tendsto (auxU a f g) (𝓝[≠] t₀)
      (𝓝 ((deriv f t₀ - deriv g t₀) / ∏ i ∈ Finset.univ.erase j, (a j - a i))) := by
  set F := dslope f t₀
  set G := dslope g t₀
  set Q : ℂ → ℂ := fun x => ∏ i ∈ Finset.univ.erase j, (x - a i) with hQ
  have hQc : Continuous Q := by simp only [hQ]; fun_prop
  have hQ0 : Q (a j) ≠ 0 := prod_erase_ne_zero ha j
  have hFc : ContinuousAt F t₀ := continuousAt_dslope_same.2 hf.differentiableAt
  have hGc : ContinuousAt G t₀ := continuousAt_dslope_same.2 hg.differentiableAt
  have hF0 : F t₀ = deriv f t₀ := dslope_same f t₀
  have hG0 : G t₀ = deriv g t₀ := dslope_same g t₀
  have hd : ContinuousAt (deriv f) t₀ := hf.deriv.continuousAt
  have hQf : ContinuousAt (fun w => Q (f w)) t₀ := hQc.continuousAt.comp hf.continuousAt
  set Λ : ℂ → ℂ := fun w => (F w - G w) * deriv f w / (F w * Q (f w)) with hΛ
  have hΛc : ContinuousAt Λ t₀ := by
    refine ((hFc.sub hGc).mul hd).div (hFc.mul hQf) ?_
    simp only [hF0, hf0]
    exact mul_ne_zero hf' hQ0
  have hΛ0 : Λ t₀ = (deriv f t₀ - deriv g t₀) / Q (a j) := by
    simp only [hΛ, hF0, hG0, hf0]
    field_simp
  have hev : ∀ᶠ w in 𝓝[≠] t₀, F w ≠ 0 ∧ Q (f w) ≠ 0 := by
    refine nhdsWithin_le_nhds ?_
    filter_upwards [hFc.eventually_ne (by rw [hF0]; exact hf'),
      hQf.eventually_ne (by rw [hf0]; exact hQ0)] with w h1 h2
    exact ⟨h1, h2⟩
  have heq : auxU a f g =ᶠ[𝓝[≠] t₀] Λ := by
    filter_upwards [hev, self_mem_nhdsWithin] with w hw hwt
    have hw' : w - t₀ ≠ 0 := sub_ne_zero.2 hwt
    have e1 : f w - a j = (w - t₀) * F w := by
      rw [← hf0, ← smul_eq_mul, sub_smul_dslope]
    have e2 : g w - a j = (w - t₀) * G w := by
      rw [← hg0, ← smul_eq_mul, sub_smul_dslope]
    have e3 : f w - g w = (w - t₀) * (F w - G w) := by
      linear_combination e1 - e2
    simp only [auxU, hΛ]
    rw [cubicP_eq_mul a j (f w), e1, e3]
    simp only [hQ] at hw ⊢
    field_simp
  exact ((hΛc.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm).trans (by rw [hΛ0])


theorem deriv_eq_prod_auxU_of_simple_analytic {f g u : ℂ → ℂ}
    {z : ℂ} {a : Fin 3 → ℂ} (ha : Function.Injective a) {j : Fin 3}
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z)
    (hf0 : f z = a j) (hg0 : g z = a j) (hf' : deriv f z ≠ 0)
    (hg' : deriv g z = 0) (hu : ContinuousAt u z)
    (hU : auxU a f g =ᶠ[𝓝[≠] z] u) :
    deriv f z = (∏ i ∈ Finset.univ.erase j, (a j - a i)) * u z := by
  have ht := tendsto_auxU_at_simple_analytic ha hf hg hf0 hg0 hf'
  have hu' : Tendsto (auxU a f g) (𝓝[≠] z) (𝓝 (u z)) :=
    (hu.tendsto.mono_left nhdsWithin_le_nhds).congr' hU.symm
  have heq := tendsto_nhds_unique ht hu'
  rw [hg', sub_zero] at heq
  have heq' := (div_eq_iff (prod_erase_ne_zero ha j)).1 heq
  simpa only [mul_comm] using heq'

end ThreeIM
