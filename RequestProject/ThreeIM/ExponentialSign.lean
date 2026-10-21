module

public import RequestProject.ThreeIM.MathlibImports

/-!
# The sign of the stable exponent (Lemma 8.6, last step)

If `u` is holomorphic and zero-free far out along every ray `r e^{iθ}`, `|θ| < π/2`, with
`u'/u → c ≠ 0` and `u → 0` along each such ray, then `c` is a negative real number.

Along the ray in direction `e`, `d/dr |u(re)|² = 2 |u|² Re(e u'/u)`; if `Re(c e) > 0`, then
`|u(re)|²` is eventually nondecreasing and positive, so it cannot tend to `0`.  Hence
`Re(c e^{iθ}) ≤ 0` for `|θ| < π/2`, and letting `θ → ±π/2` gives `Im c = 0`.
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

/-- Along a single ray in direction `e`: if `u'/u → c` and `u → 0`, then `Re(c e) ≤ 0`. -/
theorem re_mul_le_zero_of_ray {u : ℂ → ℂ} {c e : ℂ}
    (hdiff : ∀ᶠ r : ℝ in atTop, DifferentiableAt ℂ u (r * e) ∧ u (r * e) ≠ 0)
    (hlog : Tendsto (fun r : ℝ => deriv u (r * e) / u (r * e)) atTop (𝓝 c))
    (hzero : Tendsto (fun r : ℝ => u (r * e)) atTop (𝓝 0)) :
    (c * e).re ≤ 0 := by
  by_contra hpos
  push_neg at hpos
  have hcont : Continuous fun z : ℂ => (z * e).re := by fun_prop
  have hev : ∀ᶠ r : ℝ in atTop, 0 < (deriv u (r * e) / u (r * e) * e).re :=
    (hcont.tendsto c).comp hlog |>.eventually (lt_mem_nhds hpos)
  obtain ⟨R, hR⟩ := eventually_atTop.1 (hdiff.and hev)
  set φ : ℝ → ℝ := fun r => ‖u (r * e)‖ ^ 2 with hφ
  have hder : ∀ r, R ≤ r → HasDerivAt φ
      (2 * (‖u (r * e)‖ ^ 2 * (deriv u (r * e) / u (r * e) * e).re)) r := by
    intro r hr
    obtain ⟨⟨hd, hne⟩, -⟩ := hR r hr
    have h1 : HasDerivAt (fun z : ℂ => u (z * e)) (deriv u (r * e) * e) (r : ℂ) := by
      have := hd.hasDerivAt.comp (r : ℂ) ((hasDerivAt_id (r : ℂ)).mul_const e)
      simpa only [Function.comp_def, id_eq, one_mul] using! this
    have h2 := h1.comp_ofReal.norm_sq
    convert h2 using 2
    rw [Complex.inner]
    have hnorm : ((‖u (r * e)‖ ^ 2 : ℝ) : ℂ) = (starRingEnd ℂ) (u (r * e)) * u (r * e) := by
      push_cast; rw [Complex.conj_mul']
    have : deriv u (r * e) * e * (starRingEnd ℂ) (u (r * e)) =
        ((‖u (r * e)‖ ^ 2 : ℝ) : ℂ) * (deriv u (r * e) / u (r * e) * e) := by
      rw [hnorm]; field_simp
    rw [this, Complex.re_ofReal_mul]
  have hmono : MonotoneOn φ (Ici R) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici R)
    · intro r hr
      exact (hder r hr).continuousAt.continuousWithinAt
    · intro r hr
      rw [interior_Ici] at hr
      exact (hder r (le_of_lt hr)).differentiableAt.differentiableWithinAt
    · intro r hr
      rw [interior_Ici] at hr
      rw [(hder r (le_of_lt hr)).deriv]
      have := (hR r (le_of_lt hr)).2
      positivity
  have hφR : 0 < φ R := by
    have := (hR R le_rfl).1.2
    simp only [hφ]
    positivity
  have hφ0 : Tendsto φ atTop (𝓝 0) := by
    have := (hzero.norm).pow 2
    simpa using this
  obtain ⟨r, hr⟩ := eventually_atTop.1 (hφ0.eventually (gt_mem_nhds hφR))
  have h1 := hr (max r R) (le_max_left _ _)
  have h2 := hmono self_mem_Ici (show max r R ∈ Ici R from mem_Ici.2 (le_max_right _ _)) (le_max_right _ _)
  linarith

/-- **Lemma 8.6** (last step: the stable exponent is a positive real number).  If `u` is
holomorphic and zero-free far out along every ray `r e^{iθ}` with `|θ| < π/2`, and along each such
ray `u'/u → c` and `u → 0`, where `c ≠ 0`, then `c` is a negative real number. -/
theorem neg_real_of_ray_logDeriv {u : ℂ → ℂ} {c : ℂ} (hc : c ≠ 0)
    (hray : ∀ θ : ℝ, |θ| < Real.pi / 2 →
      (∀ᶠ r : ℝ in atTop, DifferentiableAt ℂ u (r * Complex.exp (θ * Complex.I)) ∧
          u (r * Complex.exp (θ * Complex.I)) ≠ 0) ∧
        Tendsto (fun r : ℝ => deriv u (r * Complex.exp (θ * Complex.I)) /
          u (r * Complex.exp (θ * Complex.I))) atTop (𝓝 c) ∧
        Tendsto (fun r : ℝ => u (r * Complex.exp (θ * Complex.I))) atTop (𝓝 0)) :
    c.im = 0 ∧ c.re < 0 := by
  have hθ : ∀ θ : ℝ, |θ| < Real.pi / 2 → c.re * Real.cos θ - c.im * Real.sin θ ≤ 0 := by
    intro θ hθ
    obtain ⟨h1, h2, h3⟩ := hray θ hθ
    have := re_mul_le_zero_of_ray h1 h2 h3
    simpa [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im] using this
  have hclosed : IsClosed {θ : ℝ | c.re * Real.cos θ - c.im * Real.sin θ ≤ 0} :=
    isClosed_le (by fun_prop) continuous_const
  have hsub : Ioo (-(Real.pi / 2)) (Real.pi / 2) ⊆
      {θ : ℝ | c.re * Real.cos θ - c.im * Real.sin θ ≤ 0} := by
    intro θ hθm
    exact hθ θ (abs_lt.2 hθm)
  have hIcc := hclosed.closure_subset_iff.2 hsub
  rw [closure_Ioo (by linarith [Real.pi_pos])] at hIcc
  have hp := hIcc (right_mem_Icc.2 (by linarith [Real.pi_pos]))
  have hm := hIcc (left_mem_Icc.2 (by linarith [Real.pi_pos]))
  have h0 := hθ 0 (by simp [Real.pi_pos])
  simp only [mem_setOf_eq, Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_neg,
    Real.sin_neg] at hp hm
  simp only [Real.cos_zero, Real.sin_zero] at h0
  have him : c.im = 0 := by linarith
  refine ⟨him, ?_⟩
  rcases h0.lt_or_eq with h | h
  · linarith
  · exfalso
    apply hc
    apply Complex.ext <;> simp [him]; linarith

end ThreeIM
