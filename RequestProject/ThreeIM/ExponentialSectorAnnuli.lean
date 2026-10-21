module

public import RequestProject.ThreeIM.SmallEntire

/-!
# Nonexceptional radii inside expanding annuli

A logarithmic upper estimate outside a finite-measure exceptional set is
incompatible with a positive linear lower estimate on every radius in
annuli of fixed relative width. This isolates the real-variable part of
the angular-sector contradiction in Lemma 8.5.
-/

@[expose] public section

open Filter Set Topology Real

namespace ThreeIM

theorem tendsto_log_affine_div {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun r : ℝ => log (exp 1 + β * r) / r) atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℝ => log x / x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hx : Tendsto (fun r : ℝ => exp 1 + β * r) atTop atTop :=
    tendsto_atTop_mono (fun r : ℝ =>
      (show β * r ≤ exp 1 + β * r by linarith [exp_pos (1 : ℝ)]))
      (tendsto_id.const_mul_atTop hβ)
  have hlin : Tendsto (fun r : ℝ => (exp 1 + β * r) / r) atTop (𝓝 β) := by
    have h := (show Tendsto (fun r : ℝ => exp 1 / r) atTop (𝓝 0) from
      tendsto_const_nhds.div_atTop tendsto_id).add_const β
    simp only [zero_add] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    field_simp [ne_of_gt hr]
  have hprod := (hlog.comp hx).mul hlin
  simp only [zero_mul] at hprod
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  dsimp only [Function.comp_def]
  have hbase : exp 1 + β * r ≠ 0 := by positivity
  field_simp [hbase, ne_of_gt hr]

theorem false_of_log_upper_and_linear_annulus_lower {P : ℝ → ℝ} {C α β c : ℝ}
    (hupper : OutsideFiniteMeasure fun ρ => P ρ ≤ C * log (exp 1 + ρ))
    (hα : 0 < α) (hαβ : α < β) (hc : 0 < c)
    {r : ℕ → ℝ} (hr : Tendsto r atTop atTop)
    (hlower : ∀ᶠ n in atTop, ∀ ρ : ℝ,
      α * r n ≤ ρ → ρ ≤ β * r n → c * r n ≤ P ρ) : False := by
  obtain ⟨E, hEm, hEv, R₀, hP⟩ := hupper
  obtain ⟨R₁, hR₁⟩ := exists_not_mem_of_finite_measure hEm hEv
  have hβ : 0 < β := hα.trans hαβ
  have hsmall : ∀ᶠ s : ℝ in atTop, |C| * log (exp 1 + β * s) < c * s := by
    have hlim := (tendsto_log_affine_div hβ).const_mul |C|
    simp only [mul_zero] at hlim
    filter_upwards [hlim.eventually (eventually_lt_nhds hc),
      eventually_gt_atTop (0 : ℝ)] with s hs hs0
    rw [← mul_div_assoc] at hs
    exact (div_lt_iff₀ hs0).mp hs
  have hbad : ∀ᶠ n : ℕ in atTop, False := by
    filter_upwards [hlower,
      (hr.const_mul_atTop hα).eventually (eventually_ge_atTop (max R₀ R₁)),
      (hr.const_mul_atTop (sub_pos.mpr hαβ)).eventually (eventually_ge_atTop 1),
      hr.eventually (eventually_ge_atTop 1), hr.eventually hsmall]
      with n hn hstart hwidth hrn hsn
    obtain ⟨ρ, hρlo, hρhi, hρE⟩ := hR₁ (α * r n) ((le_max_right _ _).trans hstart)
    have hρβ : ρ ≤ β * r n := by nlinarith
    have hρ0 : 0 ≤ ρ := (mul_nonneg hα.le (by linarith)).trans hρlo
    have hlog0 : 0 ≤ log (exp 1 + ρ) := log_nonneg (by linarith [add_one_le_exp 1])
    have hlogβ : log (exp 1 + ρ) ≤ log (exp 1 + β * r n) :=
      log_le_log (by positivity) (by linarith)
    have hup := hP ρ (((le_max_left _ _).trans hstart).trans hρlo) hρE
    have hbound : P ρ ≤ |C| * log (exp 1 + β * r n) := calc
      _ ≤ C * log (exp 1 + ρ) := hup
      _ ≤ |C| * log (exp 1 + ρ) := mul_le_mul_of_nonneg_right (le_abs_self C) hlog0
      _ ≤ _ := mul_le_mul_of_nonneg_left hlogβ (abs_nonneg C)
    exact (not_lt_of_ge ((hn ρ hρlo hρβ).trans hbound)) hsn
  obtain ⟨n, hn⟩ := hbad.exists
  exact hn

end ThreeIM
