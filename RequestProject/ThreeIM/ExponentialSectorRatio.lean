module

public import RequestProject.ThreeIM.ExponentialSectorInfinity
public import RequestProject.ThreeIM.ExponentialSectorRatioBounds

/-!
# The first component is negligible compared with the second

Together with `g → ∞`, the sector spherical-derivative estimate implies
`f/g → 0`. A contrary ratio makes both values large and bounds `g/f`;
the pointwise inverse-coordinate inequality then bounds `U`, contradicting
its exact exponential value. No further normality or derivative-limit
hypothesis is needed.
-/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

theorem ExponentialPair.canonical_ratio_right_sector_tendsto_zero
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ} (h : ExponentialPair a f g κ)
    {δ : ℝ} (hδ : 0 < δ) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ t : ℂ, R ≤ ‖t‖ → δ * ‖t‖ ≤ t.re →
      ‖chartFiniteMap (sphereGermValue f t) / chartFiniteMap (sphereGermValue g t)‖ < ε := by
  let F : ℂ → ℂ := fun t => chartFiniteMap (sphereGermValue f t)
  let G : ℂ → ℂ := fun t => chartFiniteMap (sphereGermValue g t)
  let S : ℝ := 1 + 2 * (‖a 0‖ + ‖a 1‖ + ‖a 2‖)
  have hS : 1 ≤ S := by
    dsimp [S]
    linarith [norm_nonneg (a 0), norm_nonneg (a 1), norm_nonneg (a 2)]
  have hSa (j : Fin 3) : 2 * ‖a j‖ ≤ S := by
    fin_cases j <;> dsimp [S] <;>
      linarith [norm_nonneg (a 0), norm_nonneg (a 1), norm_nonneg (a 2)]
  have hSpos : 0 < S := by linarith
  let B : ℝ := (S + 1) / ε + 1
  have hB : 0 < B := by dsimp [B]; positivity
  obtain ⟨Rg, _, hGlarge⟩ := h.canonical_g_right_sector_norm_infty hδ B
  obtain ⟨Rm, _, M, hMarty⟩ := h.sector_sphericalDeriv_bound hδ
  obtain ⟨Rp, _, hPole⟩ := h.sector_mult_top_zero hδ
  let C : ℝ := |M| + 1
  let K : ℝ := 1 / ε
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hk : 0 < ‖κ‖ := norm_pos_iff.mpr h.κ_ne_zero
  have heTop : Tendsto (fun r : ℝ => ‖κ‖ * Real.exp (δ * r)) atTop atTop :=
    (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hδ)).const_mul_atTop hk
  obtain ⟨Re, hRe⟩ := eventually_atTop.mp
    (heTop.eventually (eventually_gt_atTop (8 * (1 + K) * C)))
  let R : ℝ := max 1 (max Rm (max Rg (max Rp Re)))
  refine ⟨R, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro t ht hs
  have hts : 1 ≤ ‖t‖ ∧ Rm ≤ ‖t‖ ∧ Rg ≤ ‖t‖ ∧ Rp ≤ ‖t‖ ∧ Re ≤ ‖t‖ := by
    simpa only [R, max_le_iff] using ht
  have habs : δ * ‖t‖ ≤ |t.re| := hs.trans (le_abs_self t.re)
  have hzeros := hPole t hts.2.2.2.1 habs
  have hf : AnalyticAt ℂ F t :=
    analyticAt_canonical_of_no_pole h.pair.nonconst_f.1 hzeros.1
  have hg : AnalyticAt ℂ G t :=
    analyticAt_canonical_of_no_pole h.pair.nonconst_g.1 hzeros.2
  have hffinite : sphereGermValue f t ≠ OnePoint.infty := by
    intro hp
    have hn := (sphereGermValue_eq_infty_iff f t).mp hp
    have hpos := (mult_top_pos_iff_order_neg f t).mpr hn
    rw [hzeros.1] at hpos
    omega
  have hGsize : B ≤ ‖G t‖ := hGlarge t hts.2.2.1 hs
  have hGpos : 0 < ‖G t‖ := hB.trans_le hGsize
  by_contra hbad
  have hbad' : ε ≤ ‖F t‖ / ‖G t‖ := by
    simpa only [F, G, norm_div] using le_of_not_gt hbad
  have hFG : ε * ‖G t‖ ≤ ‖F t‖ := (le_div_iff₀ hGpos).mp hbad'
  have hBscale : ε * B = S + 1 + ε := by dsimp [B]; field_simp
  have hscaled := mul_le_mul_of_nonneg_left hGsize hε.le
  rw [hBscale] at hscaled
  have hFsize : S + 1 ≤ ‖F t‖ := by linarith
  have hFone : 1 ≤ ‖F t‖ := by linarith
  have hmarks (j : Fin 3) : 2 * ‖a j‖ ≤ ‖F t‖ := (hSa j).trans (by linarith)
  have hratio : ‖G t‖ ≤ K * ‖F t‖ := by
    dsimp only [K]
    rw [one_div_mul_eq_div, le_div_iff₀ hε]
    nlinarith
  have hM := hMarty t hts.2.1 habs
  have hfnn : 0 ≤ sphericalDeriv (sphereGermValue f) t := norm_nonneg _
  have hgnn : 0 ≤ sphericalDeriv (sphereGermValue g) t := norm_nonneg _
  have hfm : sphericalDeriv (sphereGermValue f) t ≤ C := by
    have h1 : sphericalDeriv (sphereGermValue f) t ≤
        ‖t‖ * sphericalDeriv (sphereGermValue f) t :=
      le_mul_of_one_le_left hfnn hts.1
    have h2 : ‖t‖ * sphericalDeriv (sphereGermValue f) t ≤
        ‖t‖ * (sphericalDeriv (sphereGermValue f) t + sphericalDeriv (sphereGermValue g) t) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hgnn) (norm_nonneg t)
    exact (h1.trans h2).trans (hM.trans (by dsimp [C]; linarith [le_abs_self M]))
  have hform := sphericalDeriv_eq_chartFiniteMap isOpen_univ
    (sphereHolomorphicOn_sphereGermValue isOpen_univ h.pair.nonconst_f.1) (mem_univ t) hffinite
  change sphericalDeriv (sphereGermValue f) t =
    2 * ‖deriv F t‖ / (1 + ‖F t‖ ^ 2) at hform
  rw [hform] at hfm
  have hderiv : 2 * ‖deriv F t‖ ≤ C * (1 + ‖F t‖ ^ 2) :=
    (div_le_iff₀ (by positivity : 0 < 1 + ‖F t‖ ^ 2)).mp hfm
  have hne (j : Fin 3) : F t ≠ a j := by
    intro heq
    have hh := hmarks j
    rw [← heq] at hh
    linarith
  have hcanon : ExponentialPair a F G κ := h.canonical_representatives
  have hid := hcanon.cubic_logDeriv_identity_at hf hg (cubicP_ne_zero_of_ne hne)
  have haux : auxU a F G t = κ * Complex.exp t := by
    simpa only [auxU, mul_div_assoc] using hid
  have hb := norm_cubic_quotient_product_le hFone hC hK hmarks hratio hderiv
  change ‖auxU a F G t‖ ≤ 8 * (1 + K) * C at hb
  rw [haux, norm_mul, Complex.norm_exp] at hb
  have hexp : ‖κ‖ * Real.exp (δ * ‖t‖) ≤ ‖κ‖ * Real.exp t.re :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hs) hk.le
  exact (not_lt_of_ge (hexp.trans hb)) (hRe ‖t‖ hts.2.2.2.2)

end ThreeIM
