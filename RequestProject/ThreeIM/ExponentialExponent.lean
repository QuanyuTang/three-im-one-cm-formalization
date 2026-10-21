module

public import RequestProject.ThreeIM.ExponentialSign
public import RequestProject.ThreeIM.ExponentialLocal
public import RequestProject.ThreeIM.ExponentialSector

/-!
# Positivity of the stable exponent `μ = -κ² P'(a)` (Lemma 8.6, last part)

Assuming the right-sector asymptotics of Lemmas 8.5–8.6 along rays — `f` holomorphic far out,
`f → a` and `f'/P(f) → κ²` — the function `u = f - a` is zero-free far out along each ray
(Lemma 8.4, first part: `ExponentialPair.omits_shared_in_sectors`), and
`u'/u = (f'/P(f)) · (P(f)/(f - a)) → κ² P'(a)`.  The sign lemma
`neg_real_of_ray_logDeriv` then shows that `κ² P'(a)` is a negative real number, i.e.
`μ = -κ² P'(a) > 0`.
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

variable {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ}

/-- The derivative of `P(w) = (w - a₀)(w - a₁)(w - a₂)`. -/
lemma hasDerivAt_cubicP (a : Fin 3 → ℂ) (w : ℂ) :
    HasDerivAt (cubicP a)
      ((w - a 1) * (w - a 2) + (w - a 0) * (w - a 2) + (w - a 0) * (w - a 1)) w := by
  have h0 := (hasDerivAt_id w).sub_const (a 0)
  have h1 := (hasDerivAt_id w).sub_const (a 1)
  have h2 := (hasDerivAt_id w).sub_const (a 2)
  have := (h0.mul h1).mul h2
  convert this using 1
  · funext x
    rfl
  · simp only [id_eq, Pi.mul_apply]
    ring

/-- `P'(a j) ≠ 0`: the three roots of `P` are simple. -/
lemma deriv_cubicP_ne_zero (ha : Function.Injective a) (j : Fin 3) :
    deriv (cubicP a) (a j) ≠ 0 := by
  rw [(hasDerivAt_cubicP a (a j)).deriv]
  have h01 : a 0 - a 1 ≠ 0 := sub_ne_zero.2 (ha.ne (by decide))
  have h02 : a 0 - a 2 ≠ 0 := sub_ne_zero.2 (ha.ne (by decide))
  have h12 : a 1 - a 2 ≠ 0 := sub_ne_zero.2 (ha.ne (by decide))
  fin_cases j
  · simp only [Fin.zero_eta, sub_self, zero_mul, add_zero]
    exact mul_ne_zero h01 h02
  · simp only [Fin.mk_one, sub_self, zero_mul, mul_zero, zero_add, add_zero]
    have : a 1 - a 0 ≠ 0 := by rw [← neg_sub]; exact neg_ne_zero.2 h01
    exact mul_ne_zero this h12
  · simp only [Fin.reduceFinMk, sub_self, mul_zero, zero_add, add_zero]
    have h20 : a 2 - a 0 ≠ 0 := by rw [← neg_sub]; exact neg_ne_zero.2 h02
    have h21 : a 2 - a 1 ≠ 0 := by rw [← neg_sub]; exact neg_ne_zero.2 h12
    simpa [zero_mul, add_zero] using mul_ne_zero h20 h21

/-- `P(w)/(w - a j) → P'(a j)` as `w → a j`. -/
lemma tendsto_cubicP_div (a : Fin 3 → ℂ) (j : Fin 3) :
    Tendsto (fun w => cubicP a w / (w - a j)) (𝓝[≠] (a j)) (𝓝 (deriv (cubicP a) (a j))) := by
  have hd : HasDerivAt (cubicP a) (deriv (cubicP a) (a j)) (a j) :=
    (hasDerivAt_cubicP a (a j)).differentiableAt.hasDerivAt
  have := hasDerivAt_iff_tendsto_slope.1 hd
  refine this.congr fun w => ?_
  have hP : cubicP a (a j) = 0 := by
    unfold cubicP; fin_cases j <;> simp
  rw [slope_def_field, hP, sub_zero]

/-- An analytic function with finite order over `c` and zero multiplicity there does not take
the value `c`. -/
lemma ne_of_mult_eq_zero {H : ℂ → ℂ} {z c : ℂ} (hH : AnalyticAt ℂ H z)
    (hne : meromorphicOrderAt (fun w => H w - c) z ≠ ⊤) (h0 : mult H (c : Sphere) z = 0) :
    H z ≠ c := by
  intro heq
  have ha : AnalyticAt ℂ (fun w => H w - c) z := hH.sub analyticAt_const
  have ht : Tendsto (fun w => H w - c) (𝓝[≠] z) (𝓝 0) := by
    have := ha.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := {z}ᶜ))
    simpa [heq] using this
  have hpos := (tendsto_zero_iff_meromorphicOrderAt_pos ha.meromorphicAt).1 ht
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hne
  rw [mult_coe, ← hn, WithTop.untop₀_coe] at h0
  rw [← hn] at hpos
  have : (0 : ℤ) < n := by exact_mod_cast hpos
  omega

/-- **Lemma 8.6** (last part: `μ = -κ² P'(a)` is a positive real number).  Let `f, g` be an
exponential pair and `a j` a root of `P`.  Suppose that along every ray `r e^{iθ}` with
`|θ| < π/2`, the function `f` is holomorphic far out, `f → a j` and `f'/P(f) → κ²`.
`ExponentialSectorExponent` supplies these ray hypotheses for the canonical representatives
from the proved right-sector asymptotics. Then `μ = -κ² P'(a j)` is a positive real number. -/
theorem ExponentialPair.stable_exponent_pos (h : ExponentialPair a f g κ) (j : Fin 3)
    (hray : ∀ θ : ℝ, |θ| < Real.pi / 2 →
      (∀ᶠ r : ℝ in atTop, DifferentiableAt ℂ f (r * Complex.exp (θ * Complex.I))) ∧
        Tendsto (fun r : ℝ => f (r * Complex.exp (θ * Complex.I))) atTop (𝓝 (a j)) ∧
        Tendsto (fun r : ℝ => deriv f (r * Complex.exp (θ * Complex.I)) /
          cubicP a (f (r * Complex.exp (θ * Complex.I)))) atTop (𝓝 (κ ^ 2))) :
    (-(κ ^ 2 * deriv (cubicP a) (a j))).im = 0 ∧ 0 < (-(κ ^ 2 * deriv (cubicP a) (a j))).re := by
  have hc : κ ^ 2 * deriv (cubicP a) (a j) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 h.κ_ne_zero) (deriv_cubicP_ne_zero h.pair.injective j)
  suffices H : (κ ^ 2 * deriv (cubicP a) (a j)).im = 0 ∧ (κ ^ 2 * deriv (cubicP a) (a j)).re < 0 by
    simp only [Complex.neg_im, Complex.neg_re, neg_eq_zero, neg_pos]
    exact H
  apply neg_real_of_ray_logDeriv (u := fun t => f t - a j) hc
  intro θ hθ
  obtain ⟨hdiff, hlim, hratio⟩ := hray θ hθ
  set e : ℂ := Complex.exp (θ * Complex.I) with he
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo (abs_lt.1 hθ)
  obtain ⟨R, hR⟩ := h.omits_shared_in_sectors hcos
  have hnorm_e : ‖e‖ = 1 := by rw [he, Complex.norm_exp_ofReal_mul_I]
  have hre_e : e.re = Real.cos θ := by rw [he, Complex.exp_ofReal_mul_I_re]
  -- far out on the ray, `f` is holomorphic and avoids `a j`
  have hgood : ∀ᶠ r : ℝ in atTop, DifferentiableAt ℂ f (r * e) ∧ ∀ i, f (r * e) ≠ a i := by
    filter_upwards [hdiff, eventually_ge_atTop (max R 0)] with r hd hr
    refine ⟨hd, ?_⟩
    have hr0 : 0 ≤ r := le_trans (le_max_right _ _) hr
    have hnorm : ‖(r : ℂ) * e‖ = r := by
      rw [norm_mul, hnorm_e, mul_one, Complex.norm_real, Real.norm_of_nonneg hr0]
    intro i
    have hmult := (hR ((r : ℂ) * e) (by rw [hnorm]; exact le_trans (le_max_left _ _) hr)
      (by
        rw [hnorm, Complex.re_ofReal_mul, hre_e, abs_of_nonneg (mul_nonneg hr0 hcos.le)]
        linarith [mul_comm (Real.cos θ) r]) i).1
    have han : AnalyticAt ℂ f (r * e) :=
      (h.pair.nonconst_f.1 _ (mem_univ _)).analyticAt hd.continuousAt
    exact ne_of_mult_eq_zero han (h.pair.nonconst_f.2 _ (mem_univ _) (a i)) hmult
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hgood] with r hr
    exact ⟨hr.1.sub_const _, sub_ne_zero.2 (hr.2 j)⟩
  · -- `u'/u = (f'/P(f)) · (P(f)/(f - a j))`
    have hin : Tendsto (fun r : ℝ => f (r * e)) atTop (𝓝[≠] (a j)) :=
      tendsto_nhdsWithin_iff.2 ⟨hlim, hgood.mono fun r hr => hr.2 j⟩
    have hq := (tendsto_cubicP_div a j).comp hin
    have hprod := hratio.mul hq
    refine hprod.congr' ?_
    filter_upwards [hgood] with r hr
    have hP : cubicP a (f (r * e)) ≠ 0 := cubicP_ne_zero_of_ne hr.2
    have hne : f (r * e) - a j ≠ 0 := sub_ne_zero.2 (hr.2 j)
    simp only [Function.comp_apply, deriv_sub_const]
    field_simp
  · simpa using hlim.sub_const (a j)

end ThreeIM
