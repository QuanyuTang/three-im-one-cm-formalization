module

public import RequestProject.ThreeIM.ExponentialData
public import RequestProject.ThreeIM.ThetaLocal
public import RequestProject.ThreeIM.Scalar

/-!
# Local structure of exponential pairs (Lemma 8.2, remaining parts)

* every pole of an exponential pair is simple (since `Ψ = κ²` is a nonzero constant,
  Lemma 3.7 forces the pole order `k` to satisfy `2k - 2 ≤ 0`);
* the derivative of either member does not vanish at a finite point whose value is not one of
  the three finite shared values (otherwise `U` or `V` would vanish there, while `U = κ e^t`,
  `V = κ e^{-t}` are zero-free).
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

variable {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ}

lemma ExponentialPair.auxPsi_eventually_eq (h : ExponentialPair a f g κ) (t : ℂ) :
    auxPsi a f g =ᶠ[𝓝[≠] t] fun _ => κ ^ 2 := by
  filter_upwards [eventually_nhdsNE_of_codiscrete h.eq_U t,
    eventually_nhdsNE_of_codiscrete h.eq_V t] with w hu hv
  simp only [auxPsi, hu, hv]
  rw [mul_mul_mul_comm, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  ring

/-- **Lemma 8.2** (poles).  Every pole of the first member of an exponential pair is simple. -/
theorem ExponentialPair.pole_order_eq_one (h : ExponentialPair a f g κ) {t : ℂ} {k : ℕ}
    (hk : 1 ≤ k) (hf : meromorphicOrderAt f t = -(k : ℤ)) : k = 1 := by
  have hle := order_auxPsi_at_pole h.pair hk hf
  rw [meromorphicOrderAt_congr (h.auxPsi_eventually_eq t),
    order_const_eq _ (pow_ne_zero 2 h.κ_ne_zero)] at hle
  have : (2 * k - 2 : ℤ) ≤ 0 := by exact_mod_cast hle
  omega

/-- **Lemma 8.2** (poles), in terms of local degrees: both members of an exponential pair have
only simple poles. -/
theorem ExponentialPair.mult_top_le_one (h : ExponentialPair a f g κ) (t : ℂ) :
    mult f ⊤ t ≤ 1 ∧ mult g ⊤ t ≤ 1 := by
  have key : mult f ⊤ t ≤ 1 := by
    by_contra hlt
    push_neg at hlt
    set k := mult f ⊤ t with hkdef
    have hord : meromorphicOrderAt f t = -(k : ℤ) := order_eq_neg_mult_top (by omega)
    have := h.pole_order_eq_one (by omega) hord
    omega
  exact ⟨key, (h.pair.cm_top t (mem_univ t)) ▸ key⟩

/-- A quotient `D · F' / P(F)` with `D` convergent tends to zero at a finite critical point of
`F` lying off the zero set of `P`. -/
lemma tendsto_aux_zero_of_deriv_eq_zero {F D : ℂ → ℂ} {t c : ℂ} (hF : AnalyticAt ℂ F t)
    (hP : cubicP a (F t) ≠ 0) (hF' : deriv F t = 0) (hD : Tendsto D (𝓝[≠] t) (𝓝 c)) :
    Tendsto (fun w => D w * deriv F w / cubicP a (F w)) (𝓝[≠] t) (𝓝 0) := by
  have hFc : Tendsto F (𝓝[≠] t) (𝓝 (F t)) := hF.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hdc : Tendsto (deriv F) (𝓝[≠] t) (𝓝 (deriv F t)) :=
    hF.deriv.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hPc : Tendsto (fun w => cubicP a (F w)) (𝓝[≠] t) (𝓝 (cubicP a (F t))) := by
    unfold cubicP
    exact ((hFc.sub_const _).mul (hFc.sub_const _)).mul (hFc.sub_const _)
  have := (hD.mul hdc).div hPc hP
  rwa [hF', mul_zero, zero_div] at this

/-- A meromorphic function with nonnegative order at `t` (in particular, with `mult · ⊤ t = 0`)
converges on the punctured neighbourhood of `t`. -/
lemma exists_tendsto_of_mult_top_eq_zero {g : ℂ → ℂ} {t : ℂ} (hg : MeromorphicAt g t)
    (h0 : mult g ⊤ t = 0) : ∃ c, Tendsto g (𝓝[≠] t) (𝓝 c) := by
  apply tendsto_nhds_of_meromorphicOrderAt_nonneg hg
  rw [mult_top] at h0
  cases ho : meromorphicOrderAt g t with
  | top => exact le_top
  | coe n =>
    rw [ho] at h0
    rw [← WithTop.LinearOrderedAddCommGroup.coe_neg, WithTop.untop₀_coe] at h0
    exact_mod_cast (show (0 : ℤ) ≤ n by omega)

lemma cubicP_ne_zero_of_ne {a : Fin 3 → ℂ} {w : ℂ} (hw : ∀ j, w ≠ a j) : cubicP a w ≠ 0 := by
  unfold cubicP
  exact mul_ne_zero (mul_ne_zero (sub_ne_zero.2 (hw 0)) (sub_ne_zero.2 (hw 1)))
    (sub_ne_zero.2 (hw 2))

/-- **Lemma 8.2** (critical values of `f`).  At a finite point where `f` is holomorphic and takes
a value outside `{a 0, a 1, a 2}`, the derivative of `f` does not vanish.  Hence every critical
value of `f` in `ℂ` is one of the three finite shared values. -/
theorem ExponentialPair.deriv_ne_zero_left (h : ExponentialPair a f g κ) {t : ℂ}
    (hf : AnalyticAt ℂ f t) (hval : ∀ j, f t ≠ a j) : deriv f t ≠ 0 := by
  intro hd
  have hg0 : mult g ⊤ t = 0 :=
    (h.pair.cm_top t (mem_univ t)) ▸ mult_top_eq_zero_of_analyticAt hf
  obtain ⟨c, hc⟩ := exists_tendsto_of_mult_top_eq_zero
    (h.pair.nonconst_g.1 t (mem_univ t)) hg0
  have hFc : Tendsto f (𝓝[≠] t) (𝓝 (f t)) := hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h1 := tendsto_aux_zero_of_deriv_eq_zero hf (cubicP_ne_zero_of_ne hval) hd (hFc.sub hc)
  have h2 : Tendsto (fun w => κ * Complex.exp w) (𝓝[≠] t) (𝓝 (κ * Complex.exp t)) :=
    ((continuous_const.mul Complex.continuous_exp).tendsto t).mono_left nhdsWithin_le_nhds
  have h3 : Tendsto (auxU a f g) (𝓝[≠] t) (𝓝 (κ * Complex.exp t)) :=
    h2.congr' ((eventually_nhdsNE_of_codiscrete h.eq_U t).mono fun w hw => hw.symm)
  have := tendsto_nhds_unique h3 h1
  exact mul_ne_zero h.κ_ne_zero (Complex.exp_ne_zero t) this

/-- **Lemma 8.2** (critical values of `g`).  At a finite point where `g` is holomorphic and takes
a value outside `{a 0, a 1, a 2}`, the derivative of `g` does not vanish. -/
theorem ExponentialPair.deriv_ne_zero_right (h : ExponentialPair a f g κ) {t : ℂ}
    (hg : AnalyticAt ℂ g t) (hval : ∀ j, g t ≠ a j) : deriv g t ≠ 0 := by
  intro hd
  have hf0 : mult f ⊤ t = 0 :=
    (h.pair.cm_top t (mem_univ t)).symm ▸ mult_top_eq_zero_of_analyticAt hg
  obtain ⟨c, hc⟩ := exists_tendsto_of_mult_top_eq_zero
    (h.pair.nonconst_f.1 t (mem_univ t)) hf0
  have hGc : Tendsto g (𝓝[≠] t) (𝓝 (g t)) := hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h1 := tendsto_aux_zero_of_deriv_eq_zero hg (cubicP_ne_zero_of_ne hval) hd (hc.sub hGc)
  have h2 : Tendsto (fun w => κ * Complex.exp (-w)) (𝓝[≠] t) (𝓝 (κ * Complex.exp (-t))) :=
    ((continuous_const.mul (Complex.continuous_exp.comp continuous_neg)).tendsto t).mono_left
      nhdsWithin_le_nhds
  have h3 : Tendsto (auxV a f g) (𝓝[≠] t) (𝓝 (κ * Complex.exp (-t))) :=
    h2.congr' ((eventually_nhdsNE_of_codiscrete h.eq_V t).mono fun w hw => hw.symm)
  have := tendsto_nhds_unique h3 h1
  exact mul_ne_zero h.κ_ne_zero (Complex.exp_ne_zero _) this

end ThreeIM
