module

public import RequestProject.ThreeIM.ExponentialSectorFilter
public import RequestProject.ThreeIM.ExponentialSectorRatio

/-! # Filter forms of the sector divergence, small ratio, and holomorphy -/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

theorem ExponentialPair.canonical_g_norm_tendsto_rightSector
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ} (h : ExponentialPair a f g κ)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun t => ‖chartFiniteMap (sphereGermValue g t)‖) (rightSectorAtTop δ) atTop := by
  apply Filter.tendsto_atTop.mpr
  intro B
  obtain ⟨R, _, hR⟩ := h.canonical_g_right_sector_norm_infty hδ B
  exact eventually_rightSectorAtTop_iff.mpr ⟨R, hR⟩

theorem ExponentialPair.canonical_ratio_tendsto_rightSector
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ} (h : ExponentialPair a f g κ)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun t => chartFiniteMap (sphereGermValue f t) /
      chartFiniteMap (sphereGermValue g t)) (rightSectorAtTop δ) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨R, _, hR⟩ := h.canonical_ratio_right_sector_tendsto_zero hδ hε
  exact eventually_rightSectorAtTop_iff.mpr
    ⟨R, fun t ht hs => by simpa only [dist_zero_right] using hR t ht hs⟩

theorem ExponentialPair.canonical_inverse_g_tendsto_rightSector
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ} (h : ExponentialPair a f g κ)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun t => (chartFiniteMap (sphereGermValue g t))⁻¹)
      (rightSectorAtTop δ) (𝓝 0) :=
  tendsto_inv₀_cobounded.comp
    (tendsto_norm_atTop_iff_cobounded.mp (h.canonical_g_norm_tendsto_rightSector hδ))

theorem ExponentialPair.canonical_analytic_eventually_rightSector
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ} (h : ExponentialPair a f g κ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ t in rightSectorAtTop δ,
      AnalyticAt ℂ (fun w => chartFiniteMap (sphereGermValue f w)) t ∧
      AnalyticAt ℂ (fun w => chartFiniteMap (sphereGermValue g w)) t := by
  obtain ⟨R, _, hR⟩ := h.sector_canonical_analytic hδ
  exact eventually_rightSectorAtTop_iff.mpr
    ⟨R, fun t ht hs => hR t ht (hs.trans (le_abs_self t.re))⟩

end ThreeIM
