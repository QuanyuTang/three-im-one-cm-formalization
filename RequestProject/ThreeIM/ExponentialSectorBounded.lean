module

public import RequestProject.ThreeIM.ExponentialSectorCanonical
public import RequestProject.ThreeIM.ExponentialSectorLogDerivative
public import RequestProject.ThreeIM.ExponentialSectorLowerBound

/-!
# Two bounded canonical dilates are impossible

This applies the angular lower bound directly to an exponential pair.
Holomorphy and the pointwise auxiliary identity on the chosen disk are
deduced from the already proved sector omission and pole exclusion.
All values used in the boundedness hypothesis are the canonical finite
chart values, so arbitrary raw values at removable points are harmless.
-/

@[expose] public section

open Filter Set Metric Topology Complex NoWanderingDomains ValueDistribution

namespace ThreeIM

private theorem analytic_ne_of_mult_zero_sector {F : ℂ → ℂ} {z b : ℂ}
    (hF : AnalyticAt ℂ F z)
    (hne : meromorphicOrderAt (fun w => F w - b) z ≠ ⊤)
    (hzero : mult F (b : Sphere) z = 0) : F z ≠ b := by
  intro heq
  have ha : AnalyticAt ℂ (fun w => F w - b) z := hF.sub analyticAt_const
  have ht : Tendsto (fun w => F w - b) (𝓝[≠] z) (𝓝 0) := by
    have hh := ha.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := {z}ᶜ))
    simpa [heq] using hh
  have hpos := (tendsto_zero_iff_meromorphicOrderAt_pos ha.meromorphicAt).mp ht
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hne
  rw [mult_coe, ← hm, WithTop.untop₀_coe] at hzero
  rw [← hm] at hpos
  have : (0 : ℤ) < m := by exact_mod_cast hpos
  omega

theorem ExponentialPair.cubic_logDeriv_identity_at
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ} (h : ExponentialPair a f g κ)
    {t : ℂ} (hf : AnalyticAt ℂ f t) (hg : AnalyticAt ℂ g t)
    (hP : cubicP a (f t) ≠ 0) :
    (f t - g t) * (deriv f t / cubicP a (f t)) = κ * Complex.exp t := by
  have haux : ContinuousAt (auxU a f g) t := by
    have hp : ContinuousAt (fun w => cubicP a (f w)) t := by
      unfold cubicP
      fun_prop
    exact ((hf.continuousAt.sub hg.continuousAt).mul hf.deriv.continuousAt).div hp hP
  have hleft := (haux.tendsto.mono_left nhdsWithin_le_nhds).congr'
    (eventually_nhdsNE_of_codiscrete h.eq_U t)
  have hright : Tendsto (fun w => κ * Complex.exp w) (𝓝[≠] t)
      (𝓝 (κ * Complex.exp t)) := by
    exact (continuous_const.mul Complex.continuous_exp).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have heq := tendsto_nhds_unique hleft hright
  simpa only [auxU, mul_div_assoc] using heq

theorem ExponentialPair.not_bounded_canonical_dilates
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ} (h : ExponentialPair a f g κ)
    {z : ℂ} (hz : 0 < z.re) {ε : ℝ} (hε : 0 < ε)
    {r : ℕ → ℝ} (hr : Tendsto r atTop atTop)
    (hbound : ∃ M : ℝ, ∀ᶠ n in atTop, ∀ ζ ∈ ball z ε,
      ‖chartFiniteMap (sphereGermValue f ((r n : ℂ) * ζ))‖ ≤ M ∧
      ‖chartFiniteMap (sphereGermValue g ((r n : ℂ) * ζ))‖ ≤ M) : False := by
  let F : ℂ → ℂ := fun t => chartFiniteMap (sphereGermValue f t)
  let G : ℂ → ℂ := fun t => chartFiniteMap (sphereGermValue g t)
  have hcanon : ExponentialPair a F G κ := h.canonical_representatives
  obtain ⟨M, hMb⟩ := hbound
  have hsector : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, ∀ t : ℂ,
      R ≤ ‖t‖ → δ * ‖t‖ ≤ |t.re| →
        AnalyticAt ℂ F t ∧ AnalyticAt ℂ G t ∧ ∀ j, F t ≠ a j := by
    intro δ hδ
    obtain ⟨R₁, _, hR₁⟩ := h.sector_canonical_analytic hδ
    obtain ⟨R₂, hR₂⟩ := hcanon.omits_shared_in_sectors hδ
    refine ⟨max R₁ R₂, ?_⟩
    intro t ht hs
    obtain ⟨hf, hg⟩ := hR₁ t ((le_max_left _ _).trans ht) hs
    refine ⟨hf, hg, fun j => ?_⟩
    exact analytic_ne_of_mult_zero_sector hf (hcanon.pair.nonconst_f.2 t (mem_univ t) (a j))
      (hR₂ t ((le_max_right _ _).trans ht) hs j).1
  obtain ⟨ε₁, hε₁, hlocal⟩ := eventually_dilate_of_sector_property hsector hr hz
  let ε₂ : ℝ := min ε ε₁
  have hε₂ : 0 < ε₂ := lt_min hε hε₁
  have hsmall {ζ : ℂ} (hζ : ζ ∈ ball z ε₂) : ζ ∈ ball z ε :=
    ball_subset_ball (min_le_left _ _) hζ
  have hclosed {ζ : ℂ} (hζ : ζ ∈ ball z ε₂) : ζ ∈ closedBall z ε₁ :=
    ball_subset_closedBall (ball_subset_ball (min_le_right _ _) hζ)
  let D : ℂ → ℂ := fun t => deriv F t / cubicP a (F t)
  have hD : Meromorphic D := by
    intro t
    have hm := hcanon.pair.nonconst_f.meromorphic t
    exact hm.deriv.div (((hm.sub (MeromorphicAt.const _ _)).mul
      (hm.sub (MeromorphicAt.const _ _))).mul (hm.sub (MeromorphicAt.const _ _)))
  obtain ⟨K, hK⟩ := hcanon.linear_growth
  obtain ⟨C, hC⟩ := cubic_logDeriv_proximity_le_log_of_linear_growth hcanon.pair hK
  apply false_of_exp_identity_bounded_on_dilates (A := fun t => F t - G t) hD h.κ_ne_zero
    (M := 2 * (|M| + 1)) (by positivity) hC hz hε₂ hr
  · filter_upwards [hMb] with n hn ζ hζ
    have hb := hn ζ (hsmall hζ)
    show ‖F ((r n : ℂ) * ζ) - G ((r n : ℂ) * ζ)‖ ≤ 2 * (|M| + 1)
    have hh := norm_sub_le (F ((r n : ℂ) * ζ)) (G ((r n : ℂ) * ζ))
    change ‖F ((r n : ℂ) * ζ)‖ ≤ M ∧ ‖G ((r n : ℂ) * ζ)‖ ≤ M at hb
    linarith [le_abs_self M]
  · filter_upwards [hlocal] with n hn ζ hζ
    obtain ⟨hf, hg, hvalues⟩ := hn ζ (hclosed hζ)
    exact hcanon.cubic_logDeriv_identity_at hf hg (cubicP_ne_zero_of_ne hvalues)

end ThreeIM
