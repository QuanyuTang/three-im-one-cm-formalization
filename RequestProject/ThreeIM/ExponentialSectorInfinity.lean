module

public import RequestProject.ThreeIM.ExponentialSectorLimitInfinity

/-!
# Uniform divergence of the second component in proper right sectors

Compactness of the unit directions upgrades convergence along moving
dilates to the full proper-sector assertion. Pole exclusion then gives
the corresponding assertion for the actual canonical complex readings.
-/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

theorem ExponentialPair.sphereGerm_g_right_sector_infty
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ} (h : ExponentialPair a f g κ)
    {δ : ℝ} (hδ : 0 < δ) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ t : ℂ, R ≤ ‖t‖ → δ * ‖t‖ ≤ t.re →
      dist (sphereGermValue g t) OnePoint.infty < ε := by
  classical
  by_contra hbad
  push_neg at hbad
  have hsel (n : ℕ) : ∃ t : ℂ, (n : ℝ) + 1 ≤ ‖t‖ ∧
      δ * ‖t‖ ≤ t.re ∧ ε ≤ dist (sphereGermValue g t) OnePoint.infty :=
    hbad ((n : ℝ) + 1) (by positivity)
  choose t hnorm hsector hlarge using hsel
  have hpos (n : ℕ) : 0 < ‖t n‖ := by linarith [hnorm n, Nat.cast_nonneg (α := ℝ) n]
  have htop : Tendsto (fun n => ‖t n‖) atTop atTop :=
    tendsto_atTop_mono (fun n => (show (n : ℝ) ≤ ‖t n‖ by linarith [hnorm n]))
      tendsto_natCast_atTop_atTop
  let d : ℕ → ℂ := fun n => t n / (‖t n‖ : ℂ)
  have hd (n : ℕ) : ‖d n‖ = 1 := by
    dsimp [d]
    rw [norm_div, Complex.norm_real, norm_norm, div_self (hpos n).ne']
  obtain ⟨d₀, _, ψ, hψ, hdir⟩ := tendsto_subseq_of_bounded
    (x := d) (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 1))
    (fun n => mem_closedBall.mpr (by rw [dist_zero_right, hd n]))
  have hdre (n : ℕ) : δ ≤ (d n).re := by
    dsimp [d]
    rw [Complex.div_ofReal_re]
    exact (le_div_iff₀ (hpos n)).mpr (hsector n)
  have hδd : δ ≤ d₀.re := ge_of_tendsto
    (Complex.continuous_re.continuousAt.tendsto.comp hdir)
    (Eventually.of_forall fun n => hdre (ψ n))
  have hback (n : ℕ) : (‖t n‖ : ℂ) * d n = t n := by
    dsimp [d]
    exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr (hpos n).ne')
  have hconv := h.sphereGerm_g_dilate_moving_tendsto_infty
    (htop.comp hψ.tendsto_atTop) (hδ.trans_le hδd) hdir
  obtain ⟨n, hn⟩ := (Metric.tendsto_nhds.mp hconv ε hε).exists
  change dist (sphereGermValue g ((‖t (ψ n)‖ : ℂ) * d (ψ n))) OnePoint.infty < ε at hn
  rw [hback] at hn
  exact (not_lt_of_ge (hlarge (ψ n))) hn

theorem exists_sphere_distance_for_finite_chart_norm (B : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ v : ℂ,
      dist (v : OnePoint ℂ) OnePoint.infty < ε → B ≤ ‖v‖ := by
  let M : ℝ := |B| + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hs : 0 < Real.sqrt (1 + M ^ 2) := Real.sqrt_pos.mpr (by positivity)
  refine ⟨2 / Real.sqrt (1 + M ^ 2), by positivity, ?_⟩
  intro v hv
  by_contra hB
  have hvB : ‖v‖ < B := lt_of_not_ge hB
  have hvM : ‖v‖ ≤ M := by dsimp [M]; linarith [le_abs_self B]
  have hsq : ‖v‖ ^ 2 ≤ M ^ 2 := by nlinarith [norm_nonneg v]
  have hsv : 0 < Real.sqrt (1 + ‖v‖ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hsle : Real.sqrt (1 + ‖v‖ ^ 2) ≤ Real.sqrt (1 + M ^ 2) :=
    Real.sqrt_le_sqrt (by linarith)
  have hfrac : 2 / Real.sqrt (1 + M ^ 2) ≤ 2 / Real.sqrt (1 + ‖v‖ ^ 2) :=
    div_le_div_of_nonneg_left (by positivity) hsv hsle
  have heq : dist (v : OnePoint ℂ) OnePoint.infty = 2 / Real.sqrt (1 + ‖v‖ ^ 2) := rfl
  rw [heq] at hv
  exact (not_lt_of_ge hfrac) hv

theorem ExponentialPair.canonical_g_right_sector_norm_infty
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ} (h : ExponentialPair a f g κ)
    {δ : ℝ} (hδ : 0 < δ) (B : ℝ) :
    ∃ R : ℝ, 0 < R ∧ ∀ t : ℂ, R ≤ ‖t‖ → δ * ‖t‖ ≤ t.re →
      B ≤ ‖chartFiniteMap (sphereGermValue g t)‖ := by
  obtain ⟨ε, hε, hB⟩ := exists_sphere_distance_for_finite_chart_norm B
  obtain ⟨R₁, hR₁, hdist⟩ := h.sphereGerm_g_right_sector_infty hδ hε
  obtain ⟨R₂, hR₂, hzero⟩ := h.sector_mult_top_zero hδ
  refine ⟨max R₁ R₂, hR₁.trans_le (le_max_left _ _), ?_⟩
  intro t ht hs
  have hd := hdist t ((le_max_left _ _).trans ht) hs
  cases hp : sphereGermValue g t with
  | infty =>
    have hneg := (sphereGermValue_eq_infty_iff g t).mp hp
    have hpos := (mult_top_pos_iff_order_neg g t).mpr hneg
    have h0 := (hzero t ((le_max_right _ _).trans ht) (hs.trans (le_abs_self t.re))).2
    rw [h0] at hpos
    omega
  | coe v =>
    rw [hp] at hd
    simpa only [hp, chartFiniteMap] using hB v hd

end ThreeIM
