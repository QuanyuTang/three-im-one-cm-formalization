module

public import RequestProject.ThreeIM.ExponentialSectorLimits

/-! # The inverse second derivative has the uniform sector limit κ exp(-t) -/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

private theorem sector_auxV_at_analytic
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ t : ℂ} (h : ExponentialPair a f g κ)
    (hf : AnalyticAt ℂ f t) (hg : AnalyticAt ℂ g t) (hP : cubicP a (g t) ≠ 0) :
    auxV a f g t = κ * Complex.exp (-t) := by
  have hp : ContinuousAt (fun w => cubicP a (g w)) t := by unfold cubicP; fun_prop
  have hc : ContinuousAt (auxV a f g) t :=
    ((hf.continuousAt.sub hg.continuousAt).mul hg.deriv.continuousAt).div hp hP
  have ht := (hc.tendsto.mono_left nhdsWithin_le_nhds).congr'
    (eventually_nhdsNE_of_codiscrete h.eq_V t)
  have he : Tendsto (fun w => κ * Complex.exp (-w)) (𝓝[≠] t)
      (𝓝 (κ * Complex.exp (-t))) := by
    exact (continuous_const.mul (Complex.continuous_exp.comp continuous_neg)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  exact tendsto_nhds_unique ht he

theorem ExponentialPair.canonical_inverse_g_deriv_formula
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ} (h : ExponentialPair a f g κ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ t in rightSectorAtTop δ,
      deriv (fun w => (chartFiniteMap (sphereGermValue g w))⁻¹) t * Complex.exp t =
        κ * ((1 - a 0 / chartFiniteMap (sphereGermValue g t)) *
          (1 - a 1 / chartFiniteMap (sphereGermValue g t)) *
          (1 - a 2 / chartFiniteMap (sphereGermValue g t))) /
          (1 - chartFiniteMap (sphereGermValue f t) / chartFiniteMap (sphereGermValue g t)) := by
  let F : ℂ → ℂ := fun t => chartFiniteMap (sphereGermValue f t)
  let G : ℂ → ℂ := fun t => chartFiniteMap (sphereGermValue g t)
  have hcanon : ExponentialPair a F G κ := h.canonical_representatives
  have hbig : ∀ᶠ t in rightSectorAtTop δ, ∀ j, ‖a j‖ + 1 < ‖G t‖ := by
    rw [eventually_all]
    intro j
    exact (h.canonical_g_norm_tendsto_rightSector hδ).eventually (eventually_gt_atTop _)
  have hratio : ∀ᶠ t in rightSectorAtTop δ, F t / G t ≠ 1 :=
    (h.canonical_ratio_tendsto_rightSector hδ).eventually_ne (by norm_num)
  filter_upwards [h.canonical_analytic_eventually_rightSector hδ, hbig, hratio]
    with t ht hb h1
  obtain ⟨hf, hg⟩ := ht
  have hg0 : G t ≠ 0 := by
    intro heq
    have hh := hb 0
    change ‖a 0‖ + 1 < ‖G t‖ at hh
    rw [heq, norm_zero] at hh
    linarith [norm_nonneg (a 0)]
  have hga (j : Fin 3) : G t ≠ a j := by
    intro heq
    have hh := hb j
    change ‖a j‖ + 1 < ‖G t‖ at hh
    rw [heq] at hh
    linarith
  have hPg := cubicP_ne_zero_of_ne hga
  have hV := sector_auxV_at_analytic hcanon hf hg hPg
  change (F t - G t) * deriv G t / cubicP a (G t) = κ * Complex.exp (-t) at hV
  have hfg : F t - G t ≠ 0 := by
    intro heq
    apply h1
    rw [sub_eq_zero.mp heq, div_self hg0]
  have hgf : G t - F t ≠ 0 := by intro heq; apply hfg; linear_combination -heq
  have hd : deriv G t = κ * Complex.exp (-t) * cubicP a (G t) / (F t - G t) := by
    field_simp
    rw [← hV]
    field_simp
  have hInv : deriv (fun w => (G w)⁻¹) t = -(deriv G t) / (G t) ^ 2 :=
    (hg.differentiableAt.hasDerivAt.inv hg0).deriv
  have he : Complex.exp (-t) * Complex.exp t = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  change deriv (fun w => (G w)⁻¹) t * Complex.exp t =
    κ * ((1 - a 0 / G t) * (1 - a 1 / G t) * (1 - a 2 / G t)) /
      (1 - F t / G t)
  rw [hInv, hd]
  rw [show -(κ * Complex.exp (-t) * cubicP a (G t) / (F t - G t)) /
      (G t) ^ 2 * Complex.exp t =
      -(κ * (Complex.exp (-t) * Complex.exp t) * cubicP a (G t)) /
        ((F t - G t) * (G t) ^ 2) by field_simp,
    he, one_sub_div hg0]
  unfold cubicP
  field_simp <;> ring

theorem ExponentialPair.canonical_inverse_g_deriv_mul_exp_tendsto_rightSector
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ} (h : ExponentialPair a f g κ)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun t => deriv (fun w => (chartFiniteMap (sphereGermValue g w))⁻¹) t *
      Complex.exp t) (rightSectorAtTop δ) (𝓝 κ) := by
  have hY := h.canonical_inverse_g_tendsto_rightSector hδ
  have hq := h.canonical_ratio_tendsto_rightSector hδ
  have hj (j : Fin 3) : Tendsto
      (fun t => 1 - a j / chartFiniteMap (sphereGermValue g t))
      (rightSectorAtTop δ) (𝓝 (1 : ℂ)) := by
    simpa only [div_eq_mul_inv, mul_zero, sub_zero] using (hY.const_mul (a j)).const_sub 1
  have hlim := ((((hj 0).mul (hj 1)).mul (hj 2)).const_mul κ).div (hq.const_sub 1)
    (by norm_num)
  simp only [mul_one, sub_zero, div_one] at hlim
  apply hlim.congr'
  exact (h.canonical_inverse_g_deriv_formula hδ).mono fun _ ht => ht.symm

end ThreeIM
