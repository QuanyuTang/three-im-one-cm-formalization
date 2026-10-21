module

public import RequestProject.ThreeIM.PoissonBound

/-!
# Logarithmic derivative of a zero-free holomorphic function on a disk

For `g` holomorphic and zero-free near the closed disk `|z| ≤ R`, we bound `|g'/g|` on smaller
disks in terms of the circle averages of `log⁺ |g|` and `log⁺ |1/g|` on `|z| = R`:

* `log_norm_le_poisson`: the Poisson-type upper bound
  `log |g(w)| ≤ (R + |w|)/(R - |w|) · (1/2π) ∫ log⁺ |g(R e^{iθ})| dθ` (for any `g` holomorphic
  near the closed disk), via Jensen's inequality composed with a disk automorphism;
* `exists_log_of_ne_zero`: a holomorphic logarithm on a disk;
* `norm_logDeriv_le_of_abs_log_le`: if `|log |g|| ≤ K` on `|w| < s`, then
  `|g'/g| ≤ 8 s (2K + 5)/(s - r)²` on `|z| ≤ r < s` (Borel–Carathéodory and Cauchy's estimate
  for the logarithm of `g`).
-/

@[expose] public section

open Real MeasureTheory Set Filter Metric

namespace ThreeIM

/-- The disk automorphism `ζ ↦ (ζ + ρ)/(1 + ρ ζ)` maps the closed unit disk into itself. -/
lemma norm_mobius_le_one {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1) :
    ‖(ζ + ρ) / (1 + ρ * ζ)‖ ≤ 1 := by
  have hden : 1 + ρ * ζ ≠ 0 := by
    intro h0
    have : ‖(ρ : ℂ) * ζ‖ = 1 := by
      rw [show (ρ : ℂ) * ζ = -1 by linear_combination h0]; simp
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ0] at this
    nlinarith [mul_le_mul_of_nonneg_left hζ hρ0]
  rw [norm_div, div_le_one (norm_pos_iff.2 hden)]
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  have h2 : ζ.re * ζ.re + ζ.im * ζ.im ≤ 1 := by
    have := Complex.sq_norm ζ
    rw [Complex.normSq_apply] at this
    nlinarith [norm_nonneg ζ]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im, add_zero,
    Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im, zero_mul, sub_zero, zero_add]
  nlinarith [mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 (mul_self_le_mul_self hρ0 hρ1.le))]

/-- **Poisson-type upper bound.**  For `g` holomorphic near the closed disk `|z| ≤ R` and
`|w| < R`, `log |g(w)| ≤ (R + |w|)/(R - |w|) · (1/2π) ∫ log⁺ |g(R e^{iθ})| dθ`. -/
theorem log_norm_le_poisson {g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R)) {w : ℂ} (hw : ‖w‖ < R) :
    log ‖g w‖ ≤ (R + ‖w‖) / (R - ‖w‖) * circleAverage (fun z => log⁺ ‖g z‖) 0 R := by
  set r := ‖w‖ with hr
  have hK : 0 < (R + r) / (R - r) := div_pos (by positivity) (by linarith)
  have hA0 : 0 ≤ circleAverage (fun z => log⁺ ‖g z‖) 0 R :=
    circleAverage_nonneg_of_nonneg fun _ _ => posLog_nonneg
  rcases le_or_gt ‖g w‖ 1 with hle | hgt
  · have : log ‖g w‖ ≤ 0 := Real.log_nonpos (norm_nonneg _) hle
    nlinarith
  set ρ := r / R with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := (div_lt_one hR).2 hw
  set α := w.arg
  set u := Complex.exp (α * Complex.I)
  have hu : ‖u‖ = 1 := by simp [u]
  set G : ℝ → ℝ := fun t => log⁺ ‖g (circleMap 0 R t)‖ with hG
  have hgc : ContinuousOn g (closedBall 0 R) := fun z hz => (hg z hz).continuousAt.continuousWithinAt
  have hGc : Continuous G := by
    apply continuous_posLog'.comp
    apply Continuous.norm
    rw [← continuousOn_univ]
    refine hgc.comp (continuous_circleMap 0 R).continuousOn (fun t _ => ?_)
    simp [abs_of_pos hR]
  have hG0 : ∀ t, 0 ≤ G t := fun t => posLog_nonneg
  set h : ℂ → ℂ := fun ζ => g (R * u * ((ζ + ρ) / (1 + ρ * ζ))) with hh
  have hden : ∀ ζ ∈ closedBall (0 : ℂ) 1, 1 + ρ * ζ ≠ 0 := by
    intro ζ hζ h0
    have : ‖(ρ : ℂ) * ζ‖ = 1 := by
      rw [show (ρ : ℂ) * ζ = -1 by linear_combination h0]; simp
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ0] at this
    have := mul_le_mul_of_nonneg_left (show ‖ζ‖ ≤ 1 by simpa using hζ) hρ0
    nlinarith
  have hhan : AnalyticOnNhd ℂ h (closedBall 0 1) := by
    intro ζ hζ
    have hmem : (R : ℂ) * u * ((ζ + ρ) / (1 + ρ * ζ)) ∈ closedBall (0 : ℂ) R := by
      rw [mem_closedBall, dist_zero_right, norm_mul, norm_mul, hu, Complex.norm_real,
        Real.norm_of_nonneg hR.le, mul_one]
      have := norm_mobius_le_one hρ0 hρ1 (show ‖ζ‖ ≤ 1 by simpa using hζ)
      nlinarith
    refine AnalyticAt.comp (g := g) (f := fun ζ : ℂ => (R : ℂ) * u * ((ζ + ρ) / (1 + ρ * ζ)))
      (hg _ hmem) ?_
    apply analyticAt_const.mul
    exact (analyticAt_id.add analyticAt_const).div
      (analyticAt_const.add (analyticAt_const.mul analyticAt_id)) (hden ζ hζ)
  have hh0 : h 0 = g w := by
    simp only [hh, zero_add, mul_zero, add_zero, div_one]
    congr 1
    have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR.ne'
    conv_rhs => rw [← Complex.norm_mul_exp_arg_mul_I w]
    simp only [hρ, u, α, hr]
    push_cast; field_simp
  have hhbd : ∀ θ, h (circleMap 0 1 θ) = g (circleMap 0 R (α + mobLift ρ θ)) := by
    intro θ
    simp only [hh, circleMap, zero_add, Complex.ofReal_one, one_mul]
    rw [mobLift_spec hρ0 hρ1 θ]
    congr 1
    simp only [u, Complex.ofReal_add, add_mul, Complex.exp_add]; ring
  have hjen := log_norm_le_circleAverage hhan (by
    rw [hh0]; intro h0; rw [h0, norm_zero] at hgt; linarith)
  rw [hh0] at hjen
  have hint1 : IntervalIntegrable (fun θ => log ‖h (circleMap 0 1 θ)‖) volume 0 (2 * π) :=
    circleIntegrable_log_norm_meromorphicOn (fun ζ hζ => (hhan ζ (by
      simp only [abs_one, mem_sphere] at hζ
      simp [hζ])).meromorphicAt)
  have hψc : Continuous (mobLift ρ) :=
    continuous_iff_continuousAt.2 fun θ => (hasDerivAt_mobLift hρ0 hρ1 θ).continuousAt
  have h1 : ∫ θ in (0)..(2 * π), log ‖h (circleMap 0 1 θ)‖ ≤
      ∫ θ in (0)..(2 * π), G (α + mobLift ρ θ) := by
    apply intervalIntegral.integral_mono_on two_pi_pos.le hint1
    · exact (hGc.comp (continuous_const.add hψc)).intervalIntegrable _ _
    · intro θ _
      rw [hhbd]
      show _ ≤ max 0 _
      exact le_max_right _ _
  have h2 := integral_comp_mobLift_le hρ0 hρ1 (F := fun t => G (α + t))
    (hGc.comp (continuous_const.add continuous_id)) (fun t => hG0 _)
  have hper : Function.Periodic G (2 * π) := fun t => by
    simp only [hG, periodic_circleMap 0 R t]
  have h3 : ∫ t in (0)..(2 * π), G (α + t) = ∫ t in (0)..(2 * π), G t := by
    rw [intervalIntegral.integral_comp_add_left, add_zero, hper.intervalIntegral_add_eq α 0,
      zero_add]
  have hKρ : (1 + ρ) / (1 - ρ) = (R + r) / (R - r) := by
    rw [hρ]; field_simp
  rw [circleAverage_def, smul_eq_mul] at hjen
  rw [circleAverage_def, smul_eq_mul]
  rw [hKρ, h3] at h2
  have hpi : 0 < (2 * π)⁻¹ := by positivity
  calc log ‖g w‖ ≤ (2 * π)⁻¹ * ∫ θ in (0)..(2 * π), log ‖h (circleMap 0 1 θ)‖ := hjen
    _ ≤ (2 * π)⁻¹ * ((R + r) / (R - r) * ∫ t in (0)..(2 * π), G t) := by
      gcongr; exact h1.trans h2
    _ = (R + r) / (R - r) * ((2 * π)⁻¹ * ∫ t in (0)..(2 * π), G t) := by ring


/-- Two-sided version of `log_norm_le_poisson` for zero-free `g`. -/
theorem abs_log_norm_le_poisson {g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R)) (hg0 : ∀ z ∈ closedBall (0 : ℂ) R, g z ≠ 0)
    {w : ℂ} (hw : ‖w‖ < R) :
    |log ‖g w‖| ≤ (R + ‖w‖) / (R - ‖w‖) *
      (circleAverage (fun z => log⁺ ‖g z‖) 0 R + circleAverage (fun z => log⁺ ‖(g z)⁻¹‖) 0 R) := by
  have hginv : AnalyticOnNhd ℂ (fun z => (g z)⁻¹) (closedBall 0 R) :=
    fun z hz => (hg z hz).inv (hg0 z hz)
  have h1 := log_norm_le_poisson hR hg hw
  have h2 := log_norm_le_poisson hR hginv hw
  rw [norm_inv, Real.log_inv] at h2
  have hK : 0 ≤ (R + ‖w‖) / (R - ‖w‖) := div_nonneg (by positivity) (by linarith)
  have hA : 0 ≤ circleAverage (fun z => log⁺ ‖g z‖) 0 R :=
    circleAverage_nonneg_of_nonneg fun _ _ => posLog_nonneg
  have hB : 0 ≤ circleAverage (fun z => log⁺ ‖(g z)⁻¹‖) 0 R :=
    circleAverage_nonneg_of_nonneg fun _ _ => posLog_nonneg
  rw [abs_le]; constructor <;> nlinarith

/-- A zero-free holomorphic function on a disk has a holomorphic logarithm, which can be chosen
with value `Complex.log (g c)` at the center. -/
theorem exists_log_of_ne_zero {g : ℂ → ℂ} {c : ℂ} {R : ℝ} (hg : DifferentiableOn ℂ g (ball c R))
    (hg0 : ∀ z ∈ ball c R, g z ≠ 0) (hR : 0 < R) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (ball c R) ∧ (∀ z ∈ ball c R, Complex.exp (h z) = g z) ∧
      h c = Complex.log (g c) := by
  have hdg : DifferentiableOn ℂ (deriv g) (ball c R) := hg.deriv isOpen_ball
  have hφ : DifferentiableOn ℂ (fun z => deriv g z / g z) (ball c R) := hdg.div hg hg0
  obtain ⟨H, hH⟩ := hφ.isExactOn_ball
  have hHd : DifferentiableOn ℂ H (ball c R) :=
    fun z hz => (hH z hz).differentiableAt.differentiableWithinAt
  set Q : ℂ → ℂ := fun z => g z * Complex.exp (-H z) with hQ
  have hQd : DifferentiableOn ℂ Q (ball c R) := hg.mul (hHd.neg.cexp)
  have hQ' : (ball c R).EqOn (deriv Q) 0 := by
    intro z hz
    have hgz : HasDerivAt g (deriv g z) z :=
      (hg.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
    have h2 : HasDerivAt Q (deriv g z * Complex.exp (-H z) +
        g z * (Complex.exp (-H z) * -(deriv g z / g z))) z := hgz.mul ((hH z hz).neg.cexp)
    rw [h2.deriv]
    simp only [Pi.zero_apply]
    field_simp [hg0 z hz]
    ring
  have hc : c ∈ ball c R := mem_ball_self hR
  have hQc : ∀ z ∈ ball c R, Q z = Q c := fun z hz =>
    isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c R).isPreconnected hQd hQ' hz hc
  refine ⟨fun z => H z - H c + Complex.log (g c), ?_, ?_, ?_⟩
  · exact (hHd.sub_const _).add_const _
  · intro z hz
    have e1 := hQc z hz
    simp only [hQ] at e1
    rw [Complex.exp_add, Complex.exp_sub, Complex.exp_log (hg0 c hc)]
    have hz0 : Complex.exp (-H z) ≠ 0 := Complex.exp_ne_zero _
    have hc0 : Complex.exp (H c) ≠ 0 := Complex.exp_ne_zero _
    rw [Complex.exp_neg] at e1
    field_simp at e1 ⊢
    rw [Complex.exp_neg] at e1
    field_simp at e1
    linear_combination (-1 : ℂ) * e1
  · simp

/-- **Logarithmic derivative of a zero-free function.**  If `g` is holomorphic and zero-free on
`|w| < s` with `|log |g|| ≤ K` there, then `|g'/g| ≤ 8 s (2K + 5)/(s - r)²` on `|z| ≤ r < s`. -/
theorem norm_logDeriv_le_of_abs_log_le {g : ℂ → ℂ} {s r K : ℝ}
    (hg : DifferentiableOn ℂ g (ball 0 s)) (hg0 : ∀ z ∈ ball (0 : ℂ) s, g z ≠ 0)
    (hK : ∀ w ∈ ball (0 : ℂ) s, |log ‖g w‖| ≤ K) (hr : 0 ≤ r) (hrs : r < s) {z : ℂ}
    (hz : ‖z‖ ≤ r) :
    ‖deriv g z / g z‖ ≤ 8 * s * (2 * K + 5) / (s - r) ^ 2 := by
  have hs : 0 < s := by linarith
  have h0s : (0 : ℂ) ∈ ball (0 : ℂ) s := mem_ball_self hs
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0 h0s)
  obtain ⟨h, hhd, hexp, hh0⟩ := exists_log_of_ne_zero hg hg0 hs
  have hzs : z ∈ ball (0 : ℂ) s := by rw [mem_ball, dist_zero_right]; linarith
  -- `g'/g = h'` at `z`
  have hderiv : deriv g z / g z = deriv h z := by
    have hev : g =ᶠ[nhds z] fun w => Complex.exp (h w) := by
      filter_upwards [isOpen_ball.mem_nhds hzs] with w hw using (hexp w hw).symm
    have hhz : HasDerivAt h (deriv h z) z :=
      (hhd.differentiableAt (isOpen_ball.mem_nhds hzs)).hasDerivAt
    rw [hev.deriv_eq, hhz.cexp.deriv, ← hexp z hzs]
    field_simp [Complex.exp_ne_zero]
  rw [hderiv]
  -- real part of `h`
  have hre : ∀ w ∈ ball (0 : ℂ) s, (h w).re = log ‖g w‖ := by
    intro w hw
    rw [← hexp w hw, Complex.norm_exp, Real.log_exp]
  -- the value at the center
  have hh0n : ‖h 0‖ ≤ K + 4 := by
    rw [hh0]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.log_re, Complex.log_im]
    have := hK 0 h0s
    linarith [Complex.abs_arg_le_pi (g 0), pi_lt_four]
  -- Borel–Carathéodory
  set M := K + 1
  have hM : 0 < M := by positivity
  have hmaps : MapsTo h (ball 0 s) {w | w.re < M} := by
    intro w hw
    simp only [mem_setOf_eq]
    rw [hre w hw]
    have := hK w hw
    linarith [le_abs_self (log ‖g w‖)]
  set δ := (s - r) / 2 with hδ
  have hδ0 : 0 < δ := by linarith
  have hsub : closedBall z δ ⊆ ball (0 : ℂ) s := by
    intro w hw
    rw [mem_closedBall] at hw
    rw [mem_ball, dist_zero_right]
    have := norm_le_norm_add_norm_sub' w z
    rw [dist_eq_norm] at hw
    linarith
  have hbound : ∀ w ∈ sphere z δ, ‖h w‖ ≤ 2 * s * (2 * K + 5) / δ := by
    intro w hw
    have hwb := hsub (sphere_subset_closedBall hw)
    have hBC := Complex.borelCaratheodory hM hhd (by
      intro v hv
      have hv' : (h v).re < M := by simpa only [Set.mem_ofPred_eq] using hmaps hv
      simpa only [Set.mem_ofPred_eq] using hv'.le) hs hwb
    rw [mem_sphere, dist_eq_norm] at hw
    have hwn : ‖w‖ ≤ r + δ := by
      have := norm_le_norm_add_norm_sub' w z
      linarith
    have hsw : δ ≤ s - ‖w‖ := by linarith
    have hw0 : 0 ≤ ‖w‖ := norm_nonneg w
    have hsw0 : 0 < s - ‖w‖ := by linarith
    refine hBC.trans ?_
    rw [← add_div, div_le_div_iff₀ hsw0 hδ0]
    have e1 : 2 * M * ‖w‖ + ‖h 0‖ * (s + ‖w‖) ≤ 2 * s * (2 * K + 5) := by
      have : ‖w‖ ≤ s := by linarith
      have h1 : 2 * M * ‖w‖ ≤ 2 * M * s := by gcongr
      have h2 : ‖h 0‖ * (s + ‖w‖) ≤ (K + 4) * (2 * s) := by
        gcongr
        linarith
      simp only [M] at h1
      nlinarith
    have hnn : 0 ≤ 2 * M * ‖w‖ + ‖h 0‖ * (s + ‖w‖) := by positivity
    nlinarith
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ0
    ((hhd.mono hsub).diffContOnCl_ball subset_rfl) hbound
  refine hcauchy.trans (le_of_eq ?_)
  rw [hδ]; field_simp; ring
end ThreeIM
