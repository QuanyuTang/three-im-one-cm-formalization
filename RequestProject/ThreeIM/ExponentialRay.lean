module

public import RequestProject.ThreeIM.MathlibImports

/-!
# Integrating `y' = κ e^{-λ s}(1 + o(1))` to infinity (Lemma 8.5, integration step)

If `y → 0` and `y'(s) e^{λ s} → κ` along `s → +∞`, with `Re λ > 0`, then
`y(s) e^{λ s} → -κ/λ`.  This is the step of Lemma 8.5 in which the equation
`(1/g)' = κ e^{-t}(1 + o(1))` is integrated along a ray to get `1/g(t) = -κ e^{-t}(1 + o(1))`.
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

/-- A tail estimate: if `z → 0` and `‖z'(s)‖ ≤ δ e^{-σ s}` for `s ≥ s₀`, then
`‖z(s)‖ ≤ (δ/σ) e^{-σ s}` for `s ≥ s₀`. -/
lemma norm_le_of_deriv_tail {z z' : ℝ → ℂ} {σ δ s₀ : ℝ} (hσ : 0 < σ)
    (hd : ∀ s, s₀ ≤ s → HasDerivAt z (z' s) s)
    (hb : ∀ s, s₀ ≤ s → ‖z' s‖ ≤ δ * Real.exp (-σ * s))
    (hz : Tendsto z atTop (𝓝 0)) :
    ∀ s, s₀ ≤ s → ‖z s‖ ≤ δ / σ * Real.exp (-σ * s) := by
  intro s hs
  have key : ∀ S, s ≤ S → ‖z S - z s‖ ≤ δ / σ * Real.exp (-σ * s) := by
    intro S hS
    set B : ℝ → ℝ := fun x => δ / σ * (Real.exp (-σ * s) - Real.exp (-σ * x)) with hBdef
    have hB : ∀ x, HasDerivAt B (δ * Real.exp (-σ * x)) x := by
      intro x
      have h1 : HasDerivAt (fun x : ℝ => Real.exp (-σ * x)) (Real.exp (-σ * x) * (-σ)) x := by
        have := ((hasDerivAt_id x).const_mul (-σ)).exp
        simpa using this
      have h2 := (h1.const_sub (Real.exp (-σ * s))).const_mul (δ / σ)
      convert h2 using 1
      field_simp
    have hf : ContinuousOn (fun x => z x - z s) (Icc s S) := by
      intro x hx
      exact ((hd x (le_trans hs hx.1)).continuousAt.sub continuousAt_const).continuousWithinAt
    have hf' : ∀ x ∈ Ico s S, HasDerivWithinAt (fun x => z x - z s) (z' x) (Ici x) x := by
      intro x hx
      exact ((hd x (le_trans hs hx.1)).sub_const (z s)).hasDerivWithinAt
    have h := image_norm_le_of_norm_deriv_right_le_deriv_boundary hf hf' (B := B)
      (by simp [hBdef]) hB (fun x hx => hb x (le_trans hs hx.1)) (right_mem_Icc.2 hS)
    refine h.trans ?_
    simp only [hBdef]
    have : 0 ≤ δ :=
      (mul_nonneg_iff_of_pos_right (Real.exp_pos (-σ * s))).1 ((norm_nonneg _).trans (hb s hs))
    have : 0 ≤ δ / σ * Real.exp (-σ * S) := by positivity
    nlinarith
  have hlim : Tendsto (fun S => ‖z S - z s‖) atTop (𝓝 ‖z s‖) := by
    have := (hz.sub_const (z s)).norm
    simpa using this
  exact le_of_tendsto hlim (eventually_atTop.2 ⟨s, key⟩)

/-- **Integration to infinity** (Lemma 8.5, integration step).  If `y(s) → 0` and
`y'(s) e^{λ s} → κ` as `s → +∞`, where `Re λ > 0`, then `y(s) e^{λ s} → -κ/λ`. -/
theorem tendsto_mul_exp_of_deriv {y y' : ℝ → ℂ} {κ c : ℂ} (hc : 0 < c.re)
    (hd : ∀ᶠ s in atTop, HasDerivAt y (y' s) s)
    (hy' : Tendsto (fun s : ℝ => y' s * Complex.exp (c * s)) atTop (𝓝 κ))
    (hy : Tendsto y atTop (𝓝 0)) :
    Tendsto (fun s : ℝ => y s * Complex.exp (c * s)) atTop (𝓝 (-κ / c)) := by
  have hc0 : c ≠ 0 := fun h => by simp [h] at hc
  set σ := c.re with hσ
  set z : ℝ → ℂ := fun s => y s + κ / c * Complex.exp (-c * s) with hz
  have hnexp : ∀ s : ℝ, ‖Complex.exp (-c * s)‖ = Real.exp (-σ * s) := by
    intro s; rw [Complex.norm_exp]; simp [hσ]
  have hpexp : ∀ s : ℝ, ‖Complex.exp (c * s)‖ = Real.exp (σ * s) := by
    intro s; rw [Complex.norm_exp]; simp [hσ]
  have hzd : ∀ᶠ s in atTop, HasDerivAt z (y' s - κ * Complex.exp (-c * s)) s := by
    filter_upwards [hd] with s hs
    have h1 : HasDerivAt (fun s : ℝ => Complex.exp (-c * s)) (Complex.exp (-c * s) * (-c)) s := by
      have := ((hasDerivAt_id (s : ℂ)).const_mul (-c)).cexp.comp_ofReal
      simpa using this
    have := hs.add (h1.const_mul (κ / c))
    convert this using 1
    field_simp
    ring
  have hz0 : Tendsto z atTop (𝓝 0) := by
    have he : Tendsto (fun s : ℝ => Complex.exp (-c * s)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simp only [hnexp]
      apply Real.tendsto_exp_atBot.comp
      exact tendsto_id.const_mul_atTop_of_neg (by linarith)
    have := hy.add (he.const_mul (κ / c))
    rwa [mul_zero, add_zero] at this
  have hmain : Tendsto (fun s : ℝ => z s * Complex.exp (c * s)) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    set δ := ε * σ / 2 with hδdef
    have hδ : 0 < δ := by positivity
    obtain ⟨s₁, hs₁⟩ := eventually_atTop.1
      ((hy'.eventually (Metric.closedBall_mem_nhds κ hδ)).and hzd)
    refine ⟨s₁, fun s hs => ?_⟩
    have hb : ∀ s, s₁ ≤ s → ‖y' s - κ * Complex.exp (-c * s)‖ ≤ δ * Real.exp (-σ * s) := by
      intro s hs
      have : y' s - κ * Complex.exp (-c * s) =
          (y' s * Complex.exp (c * s) - κ) * Complex.exp (-c * s) := by
        rw [sub_mul, mul_assoc, ← Complex.exp_add]
        simp
      rw [this, norm_mul, hnexp]
      gcongr
      rw [← dist_eq_norm]
      exact (hs₁ s hs).1
    have hzs := norm_le_of_deriv_tail hc (fun s hs => (hs₁ s hs).2) hb hz0 s hs
    rw [dist_zero_right, norm_mul, hpexp]
    calc ‖z s‖ * Real.exp (σ * s) ≤ δ / σ * Real.exp (-σ * s) * Real.exp (σ * s) := by gcongr
      _ = δ / σ := by rw [mul_assoc, ← Real.exp_add]; simp
      _ < ε := by
        rw [hδdef, div_lt_iff₀ hc]
        nlinarith
  have heq : (fun s : ℝ => y s * Complex.exp (c * s)) =
      fun s : ℝ => z s * Complex.exp (c * s) + -κ / c := by
    funext s
    simp only [hz]
    rw [add_mul, mul_assoc, ← Complex.exp_add]
    simp only [neg_mul, neg_add_cancel, Complex.exp_zero, mul_one]
    ring
  rw [heq]
  simpa using hmain.add_const (-κ / c)

end ThreeIM
