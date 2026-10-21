module

public import RequestProject.ThreeIM.Basic

/-!
# Monotonicity of the Nevanlinna characteristic (part of External theorem 2.3)

We prove that the characteristic `T(r, f) = m(r, ∞; f) + N(r, ∞; f)` of a meromorphic function
on `ℂ` is nondecreasing on `(0, ∞)`.  The proof is the classical one behind H. Cartan's
identity:

* by Jensen's formula applied to `f - w`, for every `w ∈ ℂ` and `ρ > 0`,
  `(1/2π) ∫ log |f(ρe^{iθ}) - w| dθ = N(ρ, w; f) - N(ρ, ∞; f) + log |c_w|`, where `c_w` is
  the trailing coefficient of `f - w` at `0`;
* averaging over `w = e^{iφ}` on the unit circle and exchanging the two averages (Fubini), the
  left-hand side becomes `m(ρ, ∞; f)`, since `(1/2π) ∫ log |a - e^{iφ}| dφ = log⁺ |a|`;
* since `N(ρ, w; f)` is nondecreasing in `ρ`, this gives
  `m(R) - m(r) ≥ -(N(R, ∞) - N(r, ∞))` for `0 < r ≤ R`, i.e. `T(r) ≤ T(R)`.
-/

@[expose] public section

open Real MeasureTheory Set Filter

namespace ThreeIM

lemma abs_log_eq_two_posLog_sub_log (t : ℝ) : |log t| = 2 * log⁺ t - log t := by
  rw [posLog_apply]
  rcases le_total 0 (log t) with h | h
  · rw [abs_of_nonneg h, max_eq_right h]; ring
  · rw [abs_of_nonpos h, max_eq_left h]; ring

/-- `∫₀^{2π} log |e^{iφ} - a| dφ = 2π log⁺ |a|`. -/
lemma integral_log_norm_circle_sub (a : ℂ) :
    ∫ φ in Ioc 0 (2*π), log ‖circleMap 0 1 φ - a‖ = 2 * π * log⁺ ‖a‖ := by
  have := circleAverage_log_norm_sub_const_eq_posLog (a := a)
  rw [circleAverage_def, intervalIntegral.integral_of_le two_pi_pos.le, smul_eq_mul] at this
  rw [← this]; field_simp

/-- `∫₀^{2π} |log |e^{iφ} - a|| dφ ≤ 2π (log⁺ |a| + 2 log 2)`. -/
lemma integral_abs_log_norm_circle_sub_le (a : ℂ) :
    ∫ φ in Ioc 0 (2*π), |log ‖circleMap 0 1 φ - a‖| ≤ 2 * π * (log⁺ ‖a‖ + 2 * log 2) := by
  have hI1 : IntegrableOn (fun φ => log ‖circleMap 0 1 φ - a‖) (Ioc 0 (2*π)) := by
    have := circleIntegrable_log_norm_sub_const (a := a) (c := 0) 1
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le).1 this
  have hI2 : IntegrableOn (fun φ => log⁺ ‖circleMap 0 1 φ - a‖) (Ioc 0 (2*π)) := by
    have : CircleIntegrable (fun x => log⁺ ‖x - a‖) 0 1 := by
      apply circleIntegrable_posLog_norm_meromorphicOn
      intro x _
      exact (analyticAt_id.sub analyticAt_const).meromorphicAt
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le).1 this
  have hb : ∫ φ in Ioc 0 (2*π), log⁺ ‖circleMap 0 1 φ - a‖ ≤ 2*π*(log 2 + log⁺ ‖a‖) := by
    have : ∫ φ in Ioc 0 (2*π), log⁺ ‖circleMap 0 1 φ - a‖ ≤
        ∫ φ in Ioc 0 (2*π), (log 2 + log⁺ ‖a‖) := by
      apply setIntegral_mono_on hI2 (integrableOn_const (by simp [ENNReal.mul_eq_top]))
        measurableSet_Ioc
      intro φ _
      have h1 : ‖circleMap 0 1 φ - a‖ ≤ 1 + ‖a‖ := by
        calc _ ≤ ‖circleMap 0 1 φ‖ + ‖a‖ := norm_sub_le _ _
          _ = 1 + ‖a‖ := by simp
      calc log⁺ ‖circleMap 0 1 φ - a‖ ≤ log⁺ (1 + ‖a‖) := posLog_le_posLog (le_trans (by norm_num) (norm_nonneg _)) h1
        _ ≤ log 2 + log⁺ 1 + log⁺ ‖a‖ := posLog_add
        _ = _ := by simp
    rw [setIntegral_const] at this
    have hp : max (π * 2) 0 = π * 2 := max_eq_left (by positivity)
    simpa [two_pi_pos.le, mul_comm, hp] using this
  simp_rw [abs_log_eq_two_posLog_sub_log]
  rw [integral_sub (hI2.const_mul 2) hI1, integral_const_mul, integral_log_norm_circle_sub]
  nlinarith [pi_pos]

/-- Exchange of the two circle averages: averaging `w ↦ (1/2π) ∫ log |f(ρe^{iθ}) - w| dθ` over
the unit circle gives the proximity function `m(ρ, ∞; f)`. -/
lemma circleAverage_swap {f : ℂ → ℂ} (hf : Meromorphic f) (ρ : ℝ) :
    CircleIntegrable (fun w => circleAverage (fun z => log ‖f z - w‖) 0 ρ) 0 1 ∧
    circleAverage (fun w => circleAverage (fun z => log ‖f z - w‖) 0 ρ) 0 1 =
      circleAverage (fun z => log⁺ ‖f z‖) 0 ρ := by
  set μ : Measure ℝ := volume.restrict (Ioc 0 (2*π)) with hμ
  let F : ℝ → ℝ → ℝ := fun θ φ => log ‖f (circleMap 0 ρ θ) - circleMap 0 1 φ‖
  have hmeas : Measurable (Function.uncurry F) := by
    have hf' := hf.measurable
    apply Real.measurable_log.comp; apply Measurable.norm; apply Measurable.sub
    · exact hf'.comp ((continuous_circleMap 0 ρ).measurable.comp measurable_fst)
    · exact (continuous_circleMap 0 1).measurable.comp measurable_snd
  have hpos : Integrable (fun θ => log⁺ ‖f (circleMap 0 ρ θ)‖) μ := by
    have : CircleIntegrable (fun x => log⁺ ‖f x‖) 0 ρ :=
      circleIntegrable_posLog_norm_meromorphicOn (fun x _ => hf x)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le).1 this
  have hint : Integrable (Function.uncurry F) (μ.prod μ) := by
    rw [integrable_prod_iff hmeas.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun θ => ?_, ?_⟩
    · have := circleIntegrable_log_norm_sub_const (a := f (circleMap 0 ρ θ)) (c := 0) 1
      have := (intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le).1 this
      simpa [IntegrableOn, F, μ, Function.uncurry, norm_sub_rev] using this
    · refine Integrable.mono' (g := fun θ => 2*π*(log⁺ ‖f (circleMap 0 ρ θ)‖ + 2*log 2))
        ((hpos.add (integrable_const _)).const_mul _) ?_ ?_
      · exact (hmeas.norm.stronglyMeasurable.integral_prod_right' (ν := μ)).aestronglyMeasurable
      · refine Eventually.of_forall fun θ => ?_
        rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
        have := integral_abs_log_norm_circle_sub_le (f (circleMap 0 ρ θ))
        simpa [IntegrableOn, F, μ, Function.uncurry, norm_sub_rev] using this
  have hswap := integral_integral_swap hint
  have hθ : ∀ θ, ∫ φ, F θ φ ∂μ = 2 * π * log⁺ ‖f (circleMap 0 ρ θ)‖ := by
    intro θ
    rw [← integral_log_norm_circle_sub]
    simp [F, μ, norm_sub_rev]
  have hφ : ∀ φ, ∫ θ, F θ φ ∂μ = 2 * π *
      circleAverage (fun z => log ‖f z - circleMap 0 1 φ‖) 0 ρ := by
    intro φ
    rw [circleAverage_def, intervalIntegral.integral_of_le two_pi_pos.le, smul_eq_mul]
    field_simp
    rfl
  have hint2 := hint.integral_prod_right
  refine ⟨?_, ?_⟩
  · rw [circleIntegrable_def, intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le]
    have : Integrable (fun φ => (2 * π)⁻¹ * ∫ θ, F θ φ ∂μ) μ := hint2.const_mul _
    refine this.congr (Eventually.of_forall fun φ => ?_)
    simp only [hφ]; field_simp
  · rw [circleAverage_def, circleAverage_def, intervalIntegral.integral_of_le two_pi_pos.le,
      intervalIntegral.integral_of_le two_pi_pos.le, smul_eq_mul, smul_eq_mul]
    have e1 : ∫ φ in Ioc 0 (2*π), circleAverage (fun z => log ‖f z - circleMap 0 1 φ‖) 0 ρ =
        (2 * π)⁻¹ * ∫ φ, ∫ θ, F θ φ ∂μ ∂μ := by
      rw [← integral_const_mul]; congr 1; ext φ; rw [hφ]; field_simp
    have e2 : ∫ θ in Ioc 0 (2*π), log⁺ ‖f (circleMap 0 ρ θ)‖ =
        (2 * π)⁻¹ * ∫ θ, ∫ φ, F θ φ ∂μ ∂μ := by
      rw [← integral_const_mul]; congr 1; ext θ; rw [hθ]; field_simp
    rw [e1, e2, hswap]

/-- Jensen's formula for `f - w`:
`(1/2π) ∫ log |f(ρe^{iθ}) - w| dθ = N(ρ, w; f) - N(ρ, ∞; f) + log |c_w|`. -/
lemma circleAverage_log_norm_sub_eq {f : ℂ → ℂ} (hf : Meromorphic f) (w : ℂ) {ρ : ℝ}
    (hρ : ρ ≠ 0) :
    circleAverage (fun z => log ‖f z - w‖) 0 ρ =
      ValueDistribution.logCounting f w ρ - ValueDistribution.logCounting f ⊤ ρ +
        log ‖meromorphicTrailingCoeffAt (f - fun _ => w) 0‖ := by
  have hg : Meromorphic (f - fun _ => w) := hf.sub (fun x => analyticAt_const.meromorphicAt)
  have := ValueDistribution.logCounting_zero_sub_logCounting_top_eq_circleAverage_sub_const hg hρ
  rw [ValueDistribution.logCounting_coe_eq_logCounting_sub_const_zero (f := f) (a₀ := w)]
  have h2 : ValueDistribution.logCounting (f - fun _ => w) ⊤ =
      ValueDistribution.logCounting f ⊤ :=
    ValueDistribution.logCounting_sub_const hf
  rw [← h2]
  simp only [Pi.sub_apply] at this
  linarith

/-- **Monotonicity of the Nevanlinna characteristic.**  For a meromorphic function `f` on `ℂ`,
`T(r, f) ≤ T(R, f)` whenever `0 < r ≤ R`. -/
theorem characteristic_top_mono {f : ℂ → ℂ} (hf : Meromorphic f) {r R : ℝ} (hr : 0 < r)
    (hrR : r ≤ R) :
    ValueDistribution.characteristic f ⊤ r ≤ ValueDistribution.characteristic f ⊤ R := by
  have hR : 0 < R := hr.trans_le hrR
  set D := ValueDistribution.logCounting f ⊤ R - ValueDistribution.logCounting f ⊤ r with hD
  obtain ⟨hiR, heR⟩ := circleAverage_swap hf R
  obtain ⟨hir, her⟩ := circleAverage_swap hf r
  set A : ℂ → ℝ → ℝ := fun w ρ => circleAverage (fun z => log ‖f z - w‖) 0 ρ with hA
  have key : ∀ w : ℂ, A w r - D ≤ A w R := by
    intro w
    simp only [hA]
    rw [circleAverage_log_norm_sub_eq hf w hr.ne', circleAverage_log_norm_sub_eq hf w hR.ne']
    have := ValueDistribution.logCounting_monotoneOn (f := f) (e := (w : WithTop ℂ))
      (show r ∈ Ioi 0 from hr) (show R ∈ Ioi 0 from hR) hrR
    linarith
  have hc : CircleIntegrable (fun _ : ℂ => D) 0 1 := circleIntegrable_const D 0 1
  have hir' : CircleIntegrable (fun w => A w r - D) 0 1 := hir.sub hc
  have hmono := circleAverage_mono hir' hiR (fun w _ => key w)
  have hsub : circleAverage (fun w => A w r - D) 0 1 =
      circleAverage (fun w => A w r) 0 1 - D := by
    rw [show (fun w => A w r - D) = (fun w => A w r) - (fun _ => D) from rfl,
      circleAverage_sub hir hc, circleAverage_const]
  rw [hsub] at hmono
  have e1 : circleAverage (fun w => A w r) 0 1 = circleAverage (fun z => log⁺ ‖f z‖) 0 r := her
  have e2 : circleAverage (fun w => A w R) 0 1 = circleAverage (fun z => log⁺ ‖f z‖) 0 R := heR
  simp only [ValueDistribution.characteristic, Pi.add_apply, ValueDistribution.proximity_top]
  linarith

/-- Monotonicity of `T(r, f)` in the notation of the paper: for `f` meromorphic on `ℂ` and
`0 < r ≤ R`, `T(r, f) ≤ T(R, f)`. -/
theorem charT_mono {f : ℂ → ℂ} (hf : MeromorphicOn f univ) {r R : ℝ} (hr : 0 < r)
    (hrR : r ≤ R) : charT f r ≤ charT f R :=
  characteristic_top_mono (fun x => hf x (mem_univ x)) hr hrR

end ThreeIM
