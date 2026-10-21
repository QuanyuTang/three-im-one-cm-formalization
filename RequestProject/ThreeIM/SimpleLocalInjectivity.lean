module

public import RequestProject.ThreeIM.AuxiliaryLimits
public import RequestProject.ThreeIM.QuantitativeInverse

/-!
# Local injectivity near a simple point of a holomorphic limit

Locally uniform holomorphic convergence preserves injectivity on a sufficiently
small fixed disk around a point where the limiting derivative is nonzero.
The final lemmas recognize the common simple marked fibers from Psi and Phi.
-/

@[expose] public section

open Filter Set Topology Metric

namespace ThreeIM

theorem eventual_injOn_ball_of_locallyUniformlyOn {Ω : Set ℂ} {F : ℕ → ℂ → ℂ}
    {f : ℂ → ℂ} (hΩ : IsOpen Ω) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω)
    (hF : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) Ω)
    (hconv : TendstoLocallyUniformlyOn F f atTop Ω) (hderiv : deriv f z₀ ≠ 0) :
    ∃ r > 0, ball z₀ r ⊆ Ω ∧ ∀ᶠ n in atTop, InjOn (F n) (ball z₀ r) := by
  have hnorm : 0 < ‖deriv f z₀‖ := norm_pos_iff.mpr hderiv
  have hfa := (hconv.differentiableOn hF hΩ).analyticOnNhd hΩ
  have hdc : ContinuousAt (deriv f) z₀ :=
    hfa.deriv.continuousOn.continuousAt (hΩ.mem_nhds hz₀)
  have hnormlim : Tendsto (fun w => ‖deriv f w - deriv f z₀‖) (𝓝 z₀) (𝓝 0) := by
    simpa only [sub_self, norm_zero] using (hdc.tendsto.sub_const (deriv f z₀)).norm
  have hnear : {w | w ∈ Ω ∧ ‖deriv f w - deriv f z₀‖ < ‖deriv f z₀‖ / 8} ∈ 𝓝 z₀ :=
    inter_mem (hΩ.mem_nhds hz₀) (hnormlim.eventually (gt_mem_nhds (by positivity)))
  obtain ⟨δ, hδ, hδprop⟩ := Metric.mem_nhds_iff.mp hnear
  have hCB : closedBall z₀ (δ / 2) ⊆ ball z₀ δ :=
    closedBall_subset_ball (half_lt_self hδ)
  have hKΩ : closedBall z₀ (δ / 2) ⊆ Ω := fun w hw => (hδprop (hCB hw)).1
  have hBΩ : ball z₀ (δ / 2) ⊆ Ω := ball_subset_closedBall.trans hKΩ
  have hdcv := hconv.deriv hF hΩ
  have hduc : TendstoUniformlyOn (deriv ∘ F) (deriv f) atTop (closedBall z₀ (δ / 2)) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ).mp hdcv
      (closedBall z₀ (δ / 2)) hKΩ (isCompact_closedBall z₀ (δ / 2))
  have herror : ∀ᶠ n in atTop, ∀ w ∈ closedBall z₀ (δ / 2),
      ‖deriv f w - deriv (F n) w‖ < ‖deriv f z₀‖ / 8 := by
    simpa only [dist_eq_norm, Function.comp_apply] using
      (Metric.tendstoUniformlyOn_iff.mp hduc) (‖deriv f z₀‖ / 8) (by positivity)
  refine ⟨δ / 2, half_pos hδ, hBΩ, ?_⟩
  filter_upwards [hF, herror] with n hn hne
  apply (quantitative_inverse_disk (half_pos hδ) hderiv (hn.mono hBΩ) ?_).1
  intro w hw
  have he : ‖deriv (F n) w - deriv f w‖ < ‖deriv f z₀‖ / 8 := by
    rw [norm_sub_rev]
    exact hne w (ball_subset_closedBall hw)
  have hfnear := (hδprop (hCB (ball_subset_closedBall hw))).2
  calc
    ‖deriv (F n) w - deriv f z₀‖ =
        ‖(deriv (F n) w - deriv f w) + (deriv f w - deriv f z₀)‖ := by congr 1; ring
    _ ≤ ‖deriv (F n) w - deriv f w‖ + ‖deriv f w - deriv f z₀‖ := norm_add_le _ _
    _ ≤ ‖deriv f z₀‖ / 8 + ‖deriv f z₀‖ / 8 := add_le_add he.le hfnear.le
    _ = ‖deriv f z₀‖ / 4 := by ring

theorem nat_pair_eq_one_of_min_eq_one_of_ratio_near_one {m n : ℕ}
    (hmin : min m n = 1) (hclose : ‖(m : ℂ) / n - 1‖ < (1 : ℝ) / 2) :
    m = 1 ∧ n = 1 := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have heq : (((m : ℝ) / n - 1 : ℝ) : ℂ) = (m : ℂ) / n - 1 := by push_cast; rfl
  have hreal : |(m : ℝ) / n - 1| < (1 : ℝ) / 2 := by
    rw [← heq, Complex.norm_real, Real.norm_eq_abs] at hclose
    exact hclose
  have hlower : (1 : ℝ) / 2 < (m : ℝ) / n := by linarith [(abs_lt.mp hreal).1]
  have hupper : (m : ℝ) / n < (3 : ℝ) / 2 := by linarith [(abs_lt.mp hreal).2]
  have hcases : m = 1 ∨ n = 1 := by omega
  rcases hcases with hm | hn
  · refine ⟨hm, ?_⟩
    have h := (lt_div_iff₀ hnpos).mp hlower
    rw [hm, Nat.cast_one] at h
    have hnlt : (n : ℝ) < 2 := by linarith
    have : n < 2 := by exact_mod_cast hnlt
    omega
  · refine ⟨?_, hn⟩
    rw [hn, Nat.cast_one, div_one] at hupper
    have hmlt : (m : ℝ) < 2 := by linarith
    have : m < 2 := by exact_mod_cast hmlt
    omega

/-- A nonvanishing Psi germ makes at least one marked multiplicity one.
If the continuous representative of Phi is close to one, both are one,
and the representative takes the value one at the marked point. -/
theorem shared_simple_of_auxPhi_near_one {Ω : Set ℂ} {f g φ : ℂ → ℂ}
    {a : Fin 3 → ℂ} (hp : NormalizedPair Ω f g a) {z : ℂ} (hz : z ∈ Ω) {j : Fin 3}
    (hj : 0 < mult f (a j : Sphere) z)
    (hpsi : meromorphicOrderAt (auxPsi a f g) z = 0) (hφ : ContinuousAt φ z)
    (hΦ : auxPhi a f g =ᶠ[𝓝[≠] z] φ) (hclose : ‖φ z - 1‖ < (1 : ℝ) / 2) :
    mult f (a j : Sphere) z = 1 ∧ mult g (a j : Sphere) z = 1 ∧ φ z = 1 := by
  have hjg := (hp.im j z hz).mp hj
  have hlim := tendsto_auxPhi_at_shared (hp.nonconst_f.1 z hz) (hp.nonconst_g.1 z hz)
    hp.injective hj hjg (order_sub_eq_mult hj) (order_sub_eq_mult hjg) (hp.distinct z hz)
  have hvalue : φ z = (mult f (a j : Sphere) z : ℂ) / mult g (a j : Sphere) z :=
    tendsto_nhds_unique (hφ.tendsto.mono_left nhdsWithin_le_nhds)
      (hlim.congr' hΦ)
  have hpair := nat_pair_eq_one_of_min_eq_one_of_ratio_near_one
    (hp.min_mult_eq_one_of_psi hz hj hpsi) (hvalue ▸ hclose)
  exact ⟨hpair.1, hpair.2, by simpa only [hpair.1, hpair.2, Nat.cast_one, div_one] using hvalue⟩

/-- Cancel the common difference before taking a limit in Phi. This formula
remains valid at zeros of the other raw denominator factors: only the common
difference is canceled off its discrete zero set. -/
theorem auxPhi_cancel_difference {Ω : Set ℂ} {F G : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair Ω F G a) :
    auxPhi a F G =ᶠ[codiscreteWithin Ω]
      (fun z => deriv F z * cubicP a (G z) / (deriv G z * cubicP a (F z))) := by
  have hD : ∀ᶠ z in codiscreteWithin Ω, F z - G z ≠ 0 := by
    apply mem_codiscreteWithin_iff_forall_mem_nhdsNE.mpr
    intro z hz
    have hne := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
      ((hp.nonconst_f.1 z hz).sub (hp.nonconst_g.1 z hz))).mp (hp.distinct z hz)
    filter_upwards [hne] with w hw
    exact Or.inl hw
  have hcancel (D A B P Q : ℂ) (hD : D ≠ 0) :
      (D * A / P) / (D * B / Q) = A * Q / (B * P) := by
    calc
      (D * A / P) / (D * B / Q) = (D * D⁻¹) * (A * Q / (B * P)) := by
        simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
        ring
      _ = A * Q / (B * P) := by rw [mul_inv_cancel₀ hD, one_mul]
  filter_upwards [hD] with z hz
  exact hcancel (F z - G z) (deriv F z) (deriv G z)
    (cubicP a (F z)) (cubicP a (G z)) hz

end ThreeIM
