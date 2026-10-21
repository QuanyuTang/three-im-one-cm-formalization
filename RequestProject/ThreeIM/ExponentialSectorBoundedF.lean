module

public import RequestProject.ThreeIM.ExponentialSectorRightAsymptotics

/-!
# Boundedness of the first component and its approach to the marked roots

The nonzero limiting cubic derivative quotient and the vanishing spherical
derivative exclude large first-component values.  The same derivative
bound then forces the marked cubic to tend to zero.  All functions below
are the canonical finite readings of the meromorphic germs.
-/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

theorem ExponentialPair.sphericalDeriv_f_tendsto_zero_rightSector
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ} (h : ExponentialPair a f g κ)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun t => sphericalDeriv (sphereGermValue f) t)
      (rightSectorAtTop δ) (𝓝 0) := by
  obtain ⟨R, _, M, hM⟩ := h.sector_sphericalDeriv_bound hδ
  rw [Metric.tendsto_nhds]
  intro ε hε
  refine eventually_rightSectorAtTop_iff.mpr ⟨max R ((|M| + 1) / ε), ?_⟩
  intro t ht hs
  have hR : R ≤ ‖t‖ := (le_max_left _ _).trans ht
  have hn : (|M| + 1) / ε ≤ ‖t‖ := (le_max_right _ _).trans ht
  have hmul : |M| + 1 ≤ ε * ‖t‖ := by
    simpa only [mul_comm] using (div_le_iff₀ hε).mp hn
  have hb := hM t hR (hs.trans (le_abs_self t.re))
  have hfnn : 0 ≤ sphericalDeriv (sphereGermValue f) t := norm_nonneg _
  have hgnn : 0 ≤ sphericalDeriv (sphereGermValue g) t := norm_nonneg _
  have hsmall : sphericalDeriv (sphereGermValue f) t < ε := by
    by_contra hbad
    have hlarge := mul_le_mul_of_nonneg_left (le_of_not_gt hbad) (norm_nonneg t)
    have hdrop : ‖t‖ * sphericalDeriv (sphereGermValue f) t ≤
        ‖t‖ * (sphericalDeriv (sphereGermValue f) t + sphericalDeriv (sphereGermValue g) t) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hgnn) (norm_nonneg t)
    nlinarith [le_abs_self M]
  simpa only [dist_zero_right, Real.norm_of_nonneg hfnn] using hsmall

theorem ExponentialPair.canonical_f_eventually_bounded_rightSector
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ} (h : ExponentialPair a f g κ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ t in rightSectorAtTop δ,
      ‖chartFiniteMap (sphereGermValue f t)‖ ≤
        1 + 2 * (‖a 0‖ + ‖a 1‖ + ‖a 2‖) := by
  let F : ℂ → ℂ := fun t => chartFiniteMap (sphereGermValue f t)
  let S : ℝ := 1 + 2 * (‖a 0‖ + ‖a 1‖ + ‖a 2‖)
  let c : ℝ := ‖κ ^ 2‖ / 2
  have hc : 0 < c := by
    dsimp [c]
    exact half_pos (norm_pos_iff.mpr (pow_ne_zero 2 h.κ_ne_zero))
  have hS : 1 ≤ S := by
    dsimp [S]
    linarith [norm_nonneg (a 0), norm_nonneg (a 1), norm_nonneg (a 2)]
  have hSa (j : Fin 3) : 2 * ‖a j‖ ≤ S := by
    fin_cases j <;> dsimp [S] <;>
      linarith [norm_nonneg (a 0), norm_nonneg (a 1), norm_nonneg (a 2)]
  have hDlarge : ∀ᶠ t in rightSectorAtTop δ,
      c < ‖deriv F t / cubicP a (F t)‖ := by
    exact (h.canonical_cubic_logDeriv_tendsto_rightSector hδ).norm.eventually
      (eventually_gt_nhds (by
        dsimp [c]
        exact half_lt_self (norm_pos_iff.mpr (pow_ne_zero 2 h.κ_ne_zero))))
  have hsmall : ∀ᶠ t in rightSectorAtTop δ,
      sphericalDeriv (sphereGermValue f) t < c / 16 :=
    (h.sphericalDeriv_f_tendsto_zero_rightSector hδ).eventually
      (eventually_lt_nhds (by positivity))
  obtain ⟨Rp, _, hp⟩ := h.sector_mult_top_zero hδ
  have hfinite : ∀ᶠ t in rightSectorAtTop δ, sphereGermValue f t ≠ OnePoint.infty := by
    refine eventually_rightSectorAtTop_iff.mpr ⟨Rp, ?_⟩
    intro t ht hs heq
    have hpos := (mult_top_pos_iff_order_neg f t).mpr
      ((sphereGermValue_eq_infty_iff f t).mp heq)
    rw [(hp t ht (hs.trans (le_abs_self t.re))).1] at hpos
    omega
  filter_upwards [hDlarge, hsmall, hfinite] with t hD hs hfin
  change ‖F t‖ ≤ S
  by_contra hbad
  have hlarge : S ≤ ‖F t‖ := (lt_of_not_ge hbad).le
  have hform := sphericalDeriv_eq_chartFiniteMap isOpen_univ
    (sphereHolomorphicOn_sphereGermValue isOpen_univ h.pair.nonconst_f.1) (mem_univ t) hfin
  change sphericalDeriv (sphereGermValue f) t =
    2 * ‖deriv F t‖ / (1 + ‖F t‖ ^ 2) at hform
  have hderiv : 2 * ‖deriv F t‖ ≤
      sphericalDeriv (sphereGermValue f) t * (1 + ‖F t‖ ^ 2) := by
    exact ((eq_div_iff (by positivity : (1 + ‖F t‖ ^ 2) ≠ 0)).mp hform).symm.le
  have hb := norm_cubic_quotient_product_le (hS.trans hlarge)
    (show 0 ≤ sphericalDeriv (sphereGermValue f) t from norm_nonneg _)
    (show (0 : ℝ) ≤ 0 by rfl)
    (fun j => (hSa j).trans hlarge)
    (show ‖(0 : ℂ)‖ ≤ 0 * ‖F t‖ by simp) hderiv
  simp only [sub_zero, mul_div_assoc, norm_mul, add_zero, mul_one] at hb
  have hprod : ‖deriv F t / cubicP a (F t)‖ ≤
      ‖F t‖ * ‖deriv F t / cubicP a (F t)‖ :=
    le_mul_of_one_le_left (norm_nonneg _) (hS.trans hlarge)
  nlinarith

theorem ExponentialPair.canonical_f_deriv_tendsto_zero_rightSector
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ} (h : ExponentialPair a f g κ)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun t => deriv (fun w => chartFiniteMap (sphereGermValue f w)) t)
      (rightSectorAtTop δ) (𝓝 0) := by
  let F : ℂ → ℂ := fun t => chartFiniteMap (sphereGermValue f t)
  let S : ℝ := 1 + 2 * (‖a 0‖ + ‖a 1‖ + ‖a 2‖)
  let C : ℝ := (1 + S ^ 2) / 2
  have hS : 0 ≤ S := by
    dsimp [S]
    positivity
  obtain ⟨Rp, _, hp⟩ := h.sector_mult_top_zero hδ
  have hfinite : ∀ᶠ t in rightSectorAtTop δ, sphereGermValue f t ≠ OnePoint.infty := by
    refine eventually_rightSectorAtTop_iff.mpr ⟨Rp, ?_⟩
    intro t ht hs heq
    have hpos := (mult_top_pos_iff_order_neg f t).mpr
      ((sphereGermValue_eq_infty_iff f t).mp heq)
    rw [(hp t ht (hs.trans (le_abs_self t.re))).1] at hpos
    omega
  have hb : ∀ᶠ t in rightSectorAtTop δ,
      ‖deriv F t‖ ≤ C * sphericalDeriv (sphereGermValue f) t := by
    filter_upwards [h.canonical_f_eventually_bounded_rightSector hδ, hfinite] with t ht hfin
    have ht' : ‖F t‖ ≤ S := ht
    have hsq : ‖F t‖ ^ 2 ≤ S ^ 2 := by nlinarith [norm_nonneg (F t)]
    have hform := sphericalDeriv_eq_chartFiniteMap isOpen_univ
      (sphereHolomorphicOn_sphereGermValue isOpen_univ h.pair.nonconst_f.1) (mem_univ t) hfin
    change sphericalDeriv (sphereGermValue f) t =
      2 * ‖deriv F t‖ / (1 + ‖F t‖ ^ 2) at hform
    have heq := (eq_div_iff (by positivity : (1 + ‖F t‖ ^ 2) ≠ 0)).mp hform
    have hscale := mul_le_mul_of_nonneg_left hsq
      (show 0 ≤ sphericalDeriv (sphereGermValue f) t from norm_nonneg _)
    dsimp [C]
    nlinarith
  have hlim : Tendsto (fun t => C * sphericalDeriv (sphereGermValue f) t)
      (rightSectorAtTop δ) (𝓝 0) := by
    simpa only [mul_zero] using (h.sphericalDeriv_f_tendsto_zero_rightSector hδ).const_mul C
  exact squeeze_zero_norm' hb hlim

theorem ExponentialPair.canonical_cubic_tendsto_zero_rightSector
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ} (h : ExponentialPair a f g κ)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun t => cubicP a (chartFiniteMap (sphereGermValue f t)))
      (rightSectorAtTop δ) (𝓝 0) := by
  let F : ℂ → ℂ := fun t => chartFiniteMap (sphereGermValue f t)
  have hD := h.canonical_cubic_logDeriv_tendsto_rightSector hδ
  have hn := hD.eventually_ne (pow_ne_zero 2 h.κ_ne_zero)
  have hlim := (h.canonical_f_deriv_tendsto_zero_rightSector hδ).div hD
    (pow_ne_zero 2 h.κ_ne_zero)
  simp only [zero_div] at hlim
  apply hlim.congr'
  filter_upwards [hn] with t ht
  change deriv F t / cubicP a (F t) ≠ 0 at ht
  change deriv F t / (deriv F t / cubicP a (F t)) = cubicP a (F t)
  have hd : deriv F t ≠ 0 := by intro heq; exact ht (by simp only [heq, zero_div])
  have hp : cubicP a (F t) ≠ 0 := by intro heq; exact ht (by simp only [heq, div_zero])
  field_simp

end ThreeIM
