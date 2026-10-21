module

public import RequestProject.ThreeIM.LogDerivHolo
public import RequestProject.ThreeIM.LogDerivSum
public import RequestProject.ThreeIM.Cartan

/-!
# Factorization of a meromorphic function on a disk

On a closed disk `|z| ≤ ρ`, a meromorphic function `F` (with no identically vanishing germ) is
`F = ∏ (z - u)^{d u} · g`, with `u` running over the zeros and poles of `F` in the disk, `d u`
their orders and `g` holomorphic and zero-free near the closed disk (Mathlib's
`MeromorphicOn.extract_zeros_poles`).  We derive

* `log |F| = ∑ d u log |z - u| + log |g|` and `F'/F = ∑ d u/(z - u) + g'/g` off discrete sets;
* bounds for the proximity functions of `g` and `1/g` on `|z| = ρ` in terms of those of `F`
  and the total number `∑ |d u|` of zeros and poles in the disk.
-/

@[expose] public section

open Real MeasureTheory Set Filter Metric Topology

namespace ThreeIM

/-- **Factorization on a disk.**  On `|z| ≤ ρ`, a meromorphic function without identically
vanishing germs is `∏ (z - u)^{d u} · g` with `g` holomorphic and zero-free near the closed disk,
`u` running over the (finitely many) zeros and poles in the disk, `d u` their orders.  We record
the consequences for `log |F|` and for the logarithmic derivative `F'/F`. -/
theorem exists_factor_disk {F : ℂ → ℂ} (hF : ∀ z, MeromorphicAt F z)
    (hnz : ∀ z, meromorphicOrderAt F z ≠ ⊤) (ρ : ℝ) :
    ∃ (S : Finset ℂ) (d : ℂ → ℤ) (g : ℂ → ℂ),
      (∀ u ∈ S, ‖u‖ ≤ ρ ∧ d u = (meromorphicOrderAt F u).untop₀) ∧
      AnalyticOnNhd ℂ g (closedBall 0 ρ) ∧ (∀ u ∈ closedBall (0 : ℂ) ρ, g u ≠ 0) ∧
      (∀ᶠ z in codiscreteWithin (closedBall (0 : ℂ) ρ),
        log ‖F z‖ = ∑ u ∈ S, (d u : ℝ) * log ‖z - u‖ + log ‖g z‖) ∧
      (∀ᶠ z in codiscreteWithin (ball (0 : ℂ) ρ),
        logDeriv F z = ∑ u ∈ S, (d u : ℂ) / (z - u) + logDeriv g z) := by
  set U := closedBall (0 : ℂ) ρ with hU
  have hFU : MeromorphicOn F U := fun z _ => hF z
  have hfin := (MeromorphicOn.divisor F U).finiteSupport (isCompact_closedBall 0 ρ)
  obtain ⟨g, hg, hg0, hfac⟩ := hFU.extract_zeros_poles (fun u => hnz u) hfin
  set D := MeromorphicOn.divisor F U with hD
  set S := hfin.toFinset with hS
  have hSU : ∀ u ∈ S, u ∈ U := fun u hu =>
    D.supportWithinDomain (by simpa [S] using hu)
  have hlog := MeromorphicOn.extract_zeros_poles_log hg0 hfac
  have hsum : (∑ᶠ u, fun z : ℂ => (D u : ℝ) * log ‖z - u‖) =
      fun z => ∑ u ∈ S, (D u : ℝ) * log ‖z - u‖ := by
    rw [finsum_eq_sum_of_support_subset (s := S)]
    · ext z; simp [Finset.sum_apply]
    · intro u hu
      simp only [Function.mem_support, ne_eq] at hu
      simp only [hS, Finite.coe_toFinset, Function.mem_support, ne_eq]
      intro h0; apply hu; ext z; simp [h0]
  have hprod : (∏ᶠ u, (fun z : ℂ => z - u) ^ D u) = fun z => ∏ u ∈ S, (z - u) ^ D u := by
    rw [finprod_eq_prod_of_mulSupport_subset (s := S)]
    · ext z; simp [Finset.prod_apply]
    · intro u hu
      simp only [Function.mem_mulSupport, ne_eq] at hu
      simp only [hS, Finite.coe_toFinset, Function.mem_support, ne_eq]
      intro h0; apply hu; ext z; simp [h0]
  refine ⟨S, fun u => D u, g, ?_, hg, fun u hu => hg0 ⟨u, hu⟩, ?_, ?_⟩
  · intro u hu
    refine ⟨by simpa [U] using hSU u hu, ?_⟩
    exact MeromorphicOn.divisor_apply hFU (hSU u hu)
  · rw [hsum] at hlog
    filter_upwards [hlog] with z hz
    simpa using hz
  · rw [hprod] at hfac
    set P : ℂ → ℂ := fun z => ∏ u ∈ S, (z - u) ^ D u with hP
    rw [Filter.Eventually, mem_codiscreteWithin_iff_forall_mem_nhdsNE]
    intro x hx
    have hxU : x ∈ U := ball_subset_closedBall hx
    have hE0 := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 hfac) x hxU
    have hUn : U ∈ 𝓝[≠] x := nhdsWithin_le_nhds
      (mem_of_superset (isOpen_ball.mem_nhds hx) ball_subset_closedBall)
    have hE : ∀ᶠ z in 𝓝[≠] x, F z = P z * g z := by
      filter_upwards [hE0, hUn] with z hz hzU
      rcases hz with hz | hz
      · simpa using hz
      · exact absurd hzU hz
    have hE' : ∀ᶠ y in 𝓝[≠] x, F =ᶠ[𝓝 y] fun z => P z * g z := by
      have := eventually_eventually_nhdsWithin.2 hE
      filter_upwards [this, self_mem_nhdsWithin] with y hy hyx
      rwa [isOpen_compl_singleton.nhdsWithin_eq hyx] at hy
    have hball : ∀ᶠ y in 𝓝[≠] x, y ∈ ball (0 : ℂ) ρ :=
      nhdsWithin_le_nhds (isOpen_ball.mem_nhds hx)
    have hne : ∀ᶠ y in 𝓝[≠] x, ∀ u ∈ S, y ≠ u := by
      rw [Finset.eventually_all]
      intro u _
      by_cases hux : u = x
      · subst hux; exact self_mem_nhdsWithin
      · exact nhdsWithin_le_nhds (isOpen_ne.mem_nhds (Ne.symm hux))
    apply mem_of_superset (hE'.and (hball.and hne))
    rintro y ⟨hy1, hy2, hy3⟩
    left
    simp only [mem_setOf_eq]
    have hgy : g y ≠ 0 := hg0 ⟨y, ball_subset_closedBall hy2⟩
    have hgd : DifferentiableAt ℂ g y := (hg y (ball_subset_closedBall hy2)).differentiableAt
    have hfac_i : ∀ u ∈ S, (fun z : ℂ => (z - u) ^ D u) y ≠ 0 := fun u hu =>
      zpow_ne_zero _ (sub_ne_zero.2 (hy3 u hu))
    have hd_i : ∀ u ∈ S, DifferentiableAt ℂ (fun z : ℂ => (z - u) ^ D u) y := fun u hu =>
      ((differentiableAt_id.sub_const u).zpow (Or.inl (sub_ne_zero.2 (hy3 u hu))))
    have hPy : P y ≠ 0 := Finset.prod_ne_zero_iff.2 hfac_i
    have hPd : DifferentiableAt ℂ P y := DifferentiableAt.fun_finset_prod hd_i
    rw [logDeriv_apply, hy1.deriv_eq, hy1.eq_of_nhds, ← logDeriv_apply,
      logDeriv_fun_mul y hPy hgy hPd hgd]
    congr 1
    have hlp := logDeriv_fun_prod (f := fun u z => (z - u) ^ D u) (x := y) hfac_i hd_i
    rw [hP, hlp]
    refine Finset.sum_congr rfl fun u hu => ?_
    have h1 := logDeriv_fun_zpow (f := fun z : ℂ => z - u) (x := y)
      (differentiableAt_id.sub_const u) (D u)
    rw [h1]
    simp [logDeriv_apply, div_eq_mul_inv]


/-- `(1/2π) ∫ |log |ρ e^{iθ} - u|| dθ ≤ log ρ + 2` for `‖u‖ ≤ ρ`, `ρ ≥ 1`. -/
lemma circleAverage_abs_log_norm_sub_le {u : ℂ} {ρ : ℝ} (hρ : 1 ≤ ρ) (hu : ‖u‖ ≤ ρ) :
    CircleIntegrable (fun z => |log ‖z - u‖|) 0 ρ ∧
    circleAverage (fun z => |log ‖z - u‖|) 0 ρ ≤ log ρ + 2 := by
  have hρ0 : 0 < ρ := by linarith
  have hI1 : CircleIntegrable (fun z => log ‖z - u‖) 0 ρ := circleIntegrable_log_norm_sub_const ρ
  have hI2 : CircleIntegrable (fun z => log⁺ ‖z - u‖) 0 ρ :=
    circleIntegrable_posLog_norm_meromorphicOn fun z _ =>
      (analyticAt_id.sub analyticAt_const).meromorphicAt
  have hfun : (fun z => |log ‖z - u‖|) = fun z => 2 * log⁺ ‖z - u‖ - log ‖z - u‖ := by
    ext z; exact abs_log_eq_two_posLog_sub_log _
  have hI3 : CircleIntegrable (fun z => 2 * log⁺ ‖z - u‖) 0 ρ := by
    have := hI2.const_fun_smul (a := (2 : ℝ)); simpa only [smul_eq_mul] using this
  refine ⟨hfun ▸ hI3.sub hI1, ?_⟩
  rw [hfun, circleAverage_fun_sub hI3 hI1]
  have havg : circleAverage (fun z => log ‖z - u‖) 0 ρ = log ρ := by
    rw [circleAverage_log_norm_sub_const_eq_log_radius_add_posLog hρ0.ne', zero_sub, norm_neg]
    rw [(posLog_eq_zero_iff _).2]; · ring
    rw [abs_of_nonneg (by positivity)]
    exact inv_mul_le_one_of_le₀ hu hρ0.le
  have hpos : circleAverage (fun z => log⁺ ‖z - u‖) 0 ρ ≤ log 2 + log ρ := by
    apply circleAverage_mono_on_of_le_circle hI2
    intro z hz
    rw [mem_sphere, dist_zero_right, abs_of_pos hρ0] at hz
    have h1 : ‖z - u‖ ≤ 2 * ρ := by
      calc ‖z - u‖ ≤ ‖z‖ + ‖u‖ := norm_sub_le _ _
        _ ≤ 2 * ρ := by linarith
    calc log⁺ ‖z - u‖ ≤ log⁺ (2 * ρ) := posLog_le_posLog (le_trans (by norm_num) (norm_nonneg _)) h1
      _ = log (2 * ρ) := posLog_eq_log (by rw [abs_of_pos (by positivity)]; linarith)
      _ = log 2 + log ρ := Real.log_mul two_ne_zero hρ0.ne'
  have hs := circleAverage_fun_smul (a := (2 : ℝ)) (f := fun z => log⁺ ‖z - u‖) (c := 0) (R := ρ)
  simp only [smul_eq_mul] at hs
  rw [hs, havg]
  have := Real.log_two_lt_d9
  nlinarith

/-- Circle averages are monotone with respect to inequalities off discrete subsets of the
circle. -/
lemma circleAverage_mono_codiscrete {f₁ f₂ : ℂ → ℝ} {R : ℝ} (hR : R ≠ 0)
    (hf₁ : CircleIntegrable f₁ 0 R) (hf₂ : CircleIntegrable f₂ 0 R)
    (h : ∀ᶠ z in codiscreteWithin (sphere (0 : ℂ) |R|), f₁ z ≤ f₂ z) :
    circleAverage f₁ 0 R ≤ circleAverage f₂ 0 R := by
  set g : ℂ → ℝ := fun z => min (f₁ z) (f₂ z)
  have hg : f₁ =ᶠ[codiscreteWithin (sphere (0 : ℂ) |R|)] g := by
    filter_upwards [h] with z hz
    simp [g, min_eq_left hz]
  rw [circleAverage_congr_codiscreteWithin hg hR]
  exact circleAverage_mono (hf₁.congr_codiscreteWithin hg) hf₂ fun z _ => min_le_right _ _


/-- Pointwise inequality used in `proximity_factor_le`. -/
lemma max_zero_sub_le (a b : ℝ) : max 0 (a - b) ≤ max 0 a + |b| := by
  rcases le_total 0 (a - b) with h | h
  · rw [max_eq_right h]
    linarith [le_max_right 0 a, neg_abs_le b]
  · rw [max_eq_left h]; positivity

/-- **Proximity of the zero-free factor.**  In the factorization `F = ∏ (z - u)^{d u} · g` on
`|z| ≤ ρ`, `m(ρ, g) + m(ρ, 1/g) ≤ m(ρ, F) + m(ρ, 1/F) + 2 n (log ρ + 2)`, `n = ∑ |d u|`. -/
theorem proximity_factor_le {F g : ℂ → ℂ} (hF : ∀ z, MeromorphicAt F z) {ρ : ℝ} (hρ : 1 ≤ ρ)
    {S : Finset ℂ} {d : ℂ → ℤ} (hS : ∀ u ∈ S, ‖u‖ ≤ ρ)
    (hg : AnalyticOnNhd ℂ g (closedBall 0 ρ))
    (hlog : ∀ᶠ z in codiscreteWithin (closedBall (0 : ℂ) ρ),
      log ‖F z‖ = ∑ u ∈ S, (d u : ℝ) * log ‖z - u‖ + log ‖g z‖) :
    circleAverage (fun z => log⁺ ‖g z‖) 0 ρ + circleAverage (fun z => log⁺ ‖(g z)⁻¹‖) 0 ρ ≤
      circleAverage (fun z => log⁺ ‖F z‖) 0 ρ + circleAverage (fun z => log⁺ ‖F z‖⁻¹) 0 ρ +
        2 * (∑ u ∈ S, |(d u : ℝ)|) * (log ρ + 2) := by
  have hρ0 : 0 < ρ := by linarith
  have hsph : sphere (0 : ℂ) |ρ| ⊆ closedBall 0 ρ := by
    rw [abs_of_pos hρ0]; exact sphere_subset_closedBall
  have hlog' := codiscreteWithin.mono hsph hlog
  set A : ℂ → ℝ := fun z => ∑ u ∈ S, |(d u : ℝ)| * |log ‖z - u‖| with hA
  have hAi : CircleIntegrable A 0 ρ := by
    unfold CircleIntegrable
    have := IntervalIntegrable.sum S (fun u hu =>
      ((circleAverage_abs_log_norm_sub_le hρ (hS u hu)).1).const_mul |(d u : ℝ)|)
    convert this using 1; ext θ; simp [hA, Finset.sum_apply]
  have hAavg : circleAverage A 0 ρ ≤ (∑ u ∈ S, |(d u : ℝ)|) * (log ρ + 2) := by
    rw [hA, circleAverage_fun_sum (fun u hu => by
      have := ((circleAverage_abs_log_norm_sub_le hρ (hS u hu)).1).const_fun_smul (a := |(d u : ℝ)|)
      simpa only [smul_eq_mul] using this), Finset.sum_mul]
    refine Finset.sum_le_sum fun u hu => ?_
    have hs := circleAverage_fun_smul (a := |(d u : ℝ)|) (f := fun z => |log ‖z - u‖|)
      (c := 0) (R := ρ)
    simp only [smul_eq_mul] at hs
    rw [hs]
    exact mul_le_mul_of_nonneg_left (circleAverage_abs_log_norm_sub_le hρ (hS u hu)).2
      (abs_nonneg _)
  have hsumabs : ∀ z, |∑ u ∈ S, (d u : ℝ) * log ‖z - u‖| ≤ A z := fun z =>
    (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (by simp [hA, abs_mul]))
  have hmerF : MeromorphicOn F (sphere (0 : ℂ) |ρ|) := fun z _ => hF z
  have hmerg : MeromorphicOn g (sphere (0 : ℂ) |ρ|) := fun z hz => (hg z (hsph hz)).meromorphicAt
  have iF := circleIntegrable_posLog_norm_meromorphicOn hmerF
  have iFi : CircleIntegrable (fun z => log⁺ ‖F z‖⁻¹) 0 ρ := by
    have := circleIntegrable_posLog_norm_meromorphicOn hmerF.inv
    simpa [norm_inv] using this
  have ig := circleIntegrable_posLog_norm_meromorphicOn hmerg
  have igi : CircleIntegrable (fun z => log⁺ ‖(g z)⁻¹‖) 0 ρ := by
    have := circleIntegrable_posLog_norm_meromorphicOn hmerg.inv
    simpa using this
  have h1 : circleAverage (fun z => log⁺ ‖g z‖) 0 ρ ≤
      circleAverage (fun z => log⁺ ‖F z‖) 0 ρ + circleAverage A 0 ρ := by
    rw [← circleAverage_fun_add iF hAi]
    apply circleAverage_mono_codiscrete hρ0.ne' ig (iF.add hAi)
    filter_upwards [hlog'] with z hz
    show log⁺ ‖g z‖ ≤ log⁺ ‖F z‖ + A z
    rw [posLog_apply, posLog_apply]
    rw [show log ‖g z‖ = log ‖F z‖ - ∑ u ∈ S, (d u : ℝ) * log ‖z - u‖ by linarith]
    exact (max_zero_sub_le _ _).trans (by linarith [hsumabs z])
  have h2 : circleAverage (fun z => log⁺ ‖(g z)⁻¹‖) 0 ρ ≤
      circleAverage (fun z => log⁺ ‖F z‖⁻¹) 0 ρ + circleAverage A 0 ρ := by
    rw [← circleAverage_fun_add iFi hAi]
    apply circleAverage_mono_codiscrete hρ0.ne' igi (iFi.add hAi)
    filter_upwards [hlog'] with z hz
    show log⁺ ‖(g z)⁻¹‖ ≤ log⁺ ‖F z‖⁻¹ + A z
    rw [posLog_apply, posLog_apply, norm_inv, Real.log_inv, Real.log_inv]
    rw [show -log ‖g z‖ = -log ‖F z‖ - (-∑ u ∈ S, (d u : ℝ) * log ‖z - u‖) by linarith]
    refine (max_zero_sub_le _ _).trans ?_
    rw [abs_neg]; linarith [hsumabs z]
  linarith

end ThreeIM
