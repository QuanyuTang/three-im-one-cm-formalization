module

public import RequestProject.ThreeIM.ExponentialSectorDifferential
public import RequestProject.ThreeIM.ExponentialSectorTail

/-!
# Uniform right-sector asymptotics, completing Lemma 8.5

The derivative estimate is integrated along horizontal rays that stay in
the same proper sector. The resulting limit is uniform on the whole
sector, rather than an assertion only along each fixed ray.
-/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

private theorem rightSector_filter_mono {δ δ' : ℝ} (h : δ' ≤ δ) :
    rightSectorAtTop δ ≤ rightSectorAtTop δ' := by
  dsimp only [rightSectorAtTop]
  apply inf_le_inf_left
  exact principal_mono.mpr fun z hz =>
    (mul_le_mul_of_nonneg_right h (norm_nonneg z)).trans hz

theorem tendsto_mul_exp_of_deriv_rightSector {Y : ℂ → ℂ} {κ : ℂ}
    {δ : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hA : ∀ᶠ t in rightSectorAtTop δ, AnalyticAt ℂ Y t)
    (hY : Tendsto Y (rightSectorAtTop δ) (𝓝 0))
    (hD : Tendsto (fun t => deriv Y t * Complex.exp t) (rightSectorAtTop δ) (𝓝 κ)) :
    Tendsto (fun t => Y t * Complex.exp t) (rightSectorAtTop δ) (𝓝 (-κ)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let η : ℝ := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  have herror : ∀ᶠ t in rightSectorAtTop δ, ‖deriv Y t * Complex.exp t - κ‖ < η := by
    simpa only [dist_eq_norm] using Metric.tendsto_nhds.mp hD η hη
  obtain ⟨R₀, hR₀⟩ := eventually_rightSectorAtTop_iff.mp
    (hA.and herror)
  refine eventually_rightSectorAtTop_iff.mpr ⟨max 1 (R₀ / δ), ?_⟩
  intro t ht hs
  have hRe : R₀ ≤ t.re := by
    have hh : R₀ ≤ δ * ‖t‖ := by
      simpa only [mul_comm] using
        (div_le_iff₀ hδ).mp ((le_max_right 1 (R₀ / δ)).trans ht)
    exact hh.trans hs
  have hpath (s : ℝ) (hs0 : 0 ≤ s) :
      AnalyticAt ℂ Y (t + (s : ℂ)) ∧
        ‖deriv Y (t + (s : ℂ)) * Complex.exp (t + (s : ℂ)) - κ‖ < η := by
    apply hR₀
    · have hreal : R₀ ≤ (t + (s : ℂ)).re := by simp only [Complex.add_re, Complex.ofReal_re]; linarith
      exact hreal.trans (Complex.re_le_norm _)
    · exact right_sector_add_nonneg_real hδ.le hδone hs hs0
  have hyD (s : ℝ) (hs0 : 0 ≤ s) :
      HasDerivAt (fun x : ℝ => Y (t + (x : ℂ))) (deriv Y (t + (s : ℂ))) s := by
    have hi : HasDerivAt (fun x : ℂ => t + x) 1 (s : ℂ) := by
      simpa only [id_eq, add_comm] using! (hasDerivAt_id (s : ℂ)).const_add t
    simpa only [Function.comp_def, mul_one] using!
      ((hpath s hs0).1.differentiableAt.hasDerivAt.comp (s : ℂ) hi).comp_ofReal
  have hnorm : Tendsto (fun s : ℝ => ‖t + (s : ℂ)‖) atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro B
    filter_upwards [eventually_ge_atTop (B - t.re)] with s hsb
    have hh := Complex.re_le_norm (t + (s : ℂ))
    simp only [Complex.add_re, Complex.ofReal_re] at hh
    linarith
  have hpathTop : Tendsto (fun s : ℝ => t + (s : ℂ)) atTop (rightSectorAtTop δ) := by
    change Tendsto (fun s : ℝ => t + (s : ℂ)) atTop
      (comap (fun z : ℂ => ‖z‖) atTop ⊓ 𝓟 {z : ℂ | δ * ‖z‖ ≤ z.re})
    apply tendsto_inf.mpr
    refine ⟨tendsto_comap_iff.mpr hnorm, tendsto_principal.mpr ?_⟩
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs0
    exact right_sector_add_nonneg_real hδ.le hδone hs hs0
  have hsmall := norm_mul_exp_add_le_of_deriv_error hyD
    (fun s hs0 => (hpath s hs0).2.le) (hY.comp hpathTop)
  have hfinal : ‖Y t * Complex.exp t + κ‖ < ε := by
    have hh : ‖Y t * Complex.exp t + κ‖ ≤ η := by
      simpa only [Complex.ofReal_zero, add_zero] using hsmall
    exact hh.trans_lt (by dsimp [η]; linarith)
  simpa only [dist_eq_norm, sub_neg_eq_add] using hfinal

theorem ExponentialPair.canonical_inverse_g_mul_exp_tendsto_rightSector
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ} (h : ExponentialPair a f g κ)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun t => (chartFiniteMap (sphereGermValue g t))⁻¹ * Complex.exp t)
      (rightSectorAtTop δ) (𝓝 (-κ)) := by
  let δ₁ : ℝ := min δ 1
  have hδ₁ : 0 < δ₁ := lt_min hδ zero_lt_one
  have hA : ∀ᶠ t in rightSectorAtTop δ₁,
      AnalyticAt ℂ (fun w => (chartFiniteMap (sphereGermValue g w))⁻¹) t := by
    filter_upwards [h.canonical_analytic_eventually_rightSector hδ₁,
      (h.canonical_g_norm_tendsto_rightSector hδ₁).eventually (eventually_gt_atTop 0)]
      with t ht hnorm
    exact ht.2.inv (norm_pos_iff.mp hnorm)
  exact (tendsto_mul_exp_of_deriv_rightSector hδ₁ (min_le_right _ _) hA
    (h.canonical_inverse_g_tendsto_rightSector hδ₁)
    (h.canonical_inverse_g_deriv_mul_exp_tendsto_rightSector hδ₁)).mono_left
      (rightSector_filter_mono (min_le_left _ _))

theorem ExponentialPair.canonical_cubic_logDeriv_tendsto_rightSector
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ} (h : ExponentialPair a f g κ)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun t => deriv (fun w => chartFiniteMap (sphereGermValue f w)) t /
      cubicP a (chartFiniteMap (sphereGermValue f t))) (rightSectorAtTop δ) (𝓝 (κ ^ 2)) := by
  let F : ℂ → ℂ := fun t => chartFiniteMap (sphereGermValue f t)
  let G : ℂ → ℂ := fun t => chartFiniteMap (sphereGermValue g t)
  have hcanon : ExponentialPair a F G κ := h.canonical_representatives
  have hq := h.canonical_ratio_tendsto_rightSector hδ
  have hlim := ((h.canonical_inverse_g_mul_exp_tendsto_rightSector hδ).const_mul κ).div
    (hq.sub_const 1) (by norm_num)
  have hvalue : κ * -κ / (0 - 1) = κ ^ 2 := by ring
  rw [hvalue] at hlim
  have hmarked : ∀ᶠ t in rightSectorAtTop δ, ∀ j, mult F (a j : Sphere) t = 0 := by
    obtain ⟨R, hR⟩ := hcanon.omits_shared_in_sectors hδ
    exact eventually_rightSectorAtTop_iff.mpr
      ⟨R, fun t ht hs j => (hR t ht (hs.trans (le_abs_self t.re)) j).1⟩
  apply hlim.congr'
  filter_upwards [h.canonical_analytic_eventually_rightSector hδ, hmarked,
    (h.canonical_g_norm_tendsto_rightSector hδ).eventually (eventually_gt_atTop 0),
    hq.eventually_ne (show (0 : ℂ) ≠ 1 by norm_num)] with t ht hm hgpos hratio
  obtain ⟨hf, hg⟩ := ht
  have hg0 : G t ≠ 0 := norm_pos_iff.mp hgpos
  have hfa (j : Fin 3) : F t ≠ a j := by
    intro heq
    have hpos := (mult_finite_pos_iff_sphereGermValue_eq
      (hcanon.pair.nonconst_f.meromorphic t)
      (hcanon.pair.nonconst_f.2 t (mem_univ t) (a j))).mpr
      (by
        rw [sphereGermValue_eq_coe_of_analytic hf]
        change (F t : Sphere) = (a j : Sphere)
        rw [heq])
    rw [hm j] at hpos
    omega
  have hfg : F t - G t ≠ 0 := by
    intro heq
    apply hratio
    change F t / G t = (1 : ℂ)
    rw [sub_eq_zero.mp heq, div_self hg0]
  have hU := hcanon.cubic_logDeriv_identity_at hf hg (cubicP_ne_zero_of_ne hfa)
  change κ * ((G t)⁻¹ * Complex.exp t) / (F t / G t - 1) =
    deriv F t / cubicP a (F t)
  generalize deriv F t / cubicP a (F t) = Z at hU ⊢
  change κ * ((G t)⁻¹ * Complex.exp t) / (F t / G t - 1) = Z
  rw [div_sub_one hg0]
  field_simp
  linear_combination -hU

end ThreeIM
