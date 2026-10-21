module

public import RequestProject.ThreeIM.QuantitativeInverse
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Holomorphic inverse branches on quantitative disks

The quantitative inverse disk supplies both injectivity and a disk in the
image. Here the set-theoretic inverse is proved holomorphic on that whole
disk, with its derivative formula. This is the inverse-map construction in
the last step of the manuscript's finite-disk branch lemma.
-/

@[expose] public section

open Filter Set Metric Topology Function

namespace ThreeIM

/-- A near-linear holomorphic map has a holomorphic, univalent inverse on
the full quantitative target disk. The inverse is centered at zero. -/
theorem quantitative_inverse_branch {F : ℂ → ℂ} {z A : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hA : A ≠ 0) (hF : DifferentiableOn ℂ F (ball z ρ))
    (hclose : ∀ w ∈ ball z ρ, ‖deriv F w - A‖ ≤ ‖A‖ / 4) :
    ∃ γ : ℂ → ℂ, γ 0 = z ∧
      MapsTo γ (ball 0 (3 * ‖A‖ * ρ / 4)) (ball z ρ) ∧
      DifferentiableOn ℂ γ (ball 0 (3 * ‖A‖ * ρ / 4)) ∧
      InjOn γ (ball 0 (3 * ‖A‖ * ρ / 4)) ∧
      ∀ s ∈ ball 0 (3 * ‖A‖ * ρ / 4),
        F (γ s) = F z + s ∧ HasDerivAt γ (deriv F (γ s))⁻¹ s ∧
          deriv γ s ≠ 0 := by
  classical
  obtain ⟨hinj, hcover⟩ := quantitative_inverse_disk hρ hA hF hclose
  let g := invFunOn F (ball z ρ)
  let γ : ℂ → ℂ := fun s => g (F z + s)
  have hz : z ∈ ball z ρ := mem_ball_self hρ
  have hleft : ∀ w ∈ ball z ρ, g (F w) = w := hinj.leftInvOn_invFunOn
  have htarget : ∀ s ∈ ball 0 (3 * ‖A‖ * ρ / 4),
      F z + s ∈ F '' ball z ρ := by
    intro s hs
    apply hcover
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero] using hs
  have hmaps : MapsTo γ (ball 0 (3 * ‖A‖ * ρ / 4)) (ball z ρ) := by
    intro s hs
    exact invFunOn_mem (htarget s hs)
  have hright : ∀ s ∈ ball 0 (3 * ‖A‖ * ρ / 4), F (γ s) = F z + s := by
    intro s hs
    exact invFunOn_eq (htarget s hs)
  have hderiv_ne : ∀ w ∈ ball z ρ, deriv F w ≠ 0 := by
    intro w hw hd
    have hbd := hclose w hw
    rw [hd, zero_sub, norm_neg] at hbd
    have := norm_pos_iff.2 hA
    linarith
  have hderiv : ∀ s ∈ ball 0 (3 * ‖A‖ * ρ / 4),
      HasDerivAt γ (deriv F (γ s))⁻¹ s := by
    intro s hs
    have hγs := hmaps hs
    have hFa : AnalyticAt ℂ F (γ s) := (hF.analyticOnNhd isOpen_ball) _ hγs
    have hFs : HasStrictDerivAt F (deriv F (γ s)) (γ s) :=
      (hFa.contDiffAt (n := 1)).hasStrictDerivAt (by norm_num)
    have hlocal : ∀ᶠ w in 𝓝 (γ s), g (F w) = w :=
      eventually_of_mem (isOpen_ball.mem_nhds hγs) hleft
    have hginv := hFs.to_local_left_inverse (hderiv_ne _ hγs) hlocal
    rw [hright s hs] at hginv
    simpa only [γ, Function.comp_def, mul_one] using hginv.hasDerivAt.comp s
      ((hasDerivAt_id s).const_add (F z))
  refine ⟨γ, ?_, hmaps, ?_, ?_, fun s hs =>
    ⟨hright s hs, hderiv s hs, ?_⟩⟩
  · simpa only [γ, add_zero] using hleft z hz
  · intro s hs
    exact (hderiv s hs).differentiableAt.differentiableWithinAt
  · intro s hs t ht hst
    have heq := congrArg F hst
    rw [hright s hs, hright t ht] at heq
    exact add_left_cancel heq
  · rw [(hderiv s hs).deriv]
    exact inv_ne_zero (hderiv_ne _ (hmaps hs))

/-- A normalized logarithm of the derivative with norm at most `1/8`
provides the quarter-relative-error hypothesis for the inverse theorem. -/
theorem deriv_close_of_exp_log {F L : ℂ → ℂ} {A w : ℂ}
    (hL : ‖L w‖ ≤ 1 / 8) (hderiv : deriv F w = A * Complex.exp (L w)) :
    ‖deriv F w - A‖ ≤ ‖A‖ / 4 := by
  have hL1 : ‖L w‖ ≤ 1 := by linarith
  have he := Complex.norm_exp_sub_one_le hL1
  calc
    ‖deriv F w - A‖ = ‖A‖ * ‖Complex.exp (L w) - 1‖ := by
      rw [hderiv, ← norm_mul]
      congr 1
      ring
    _ ≤ ‖A‖ * (2 * ‖L w‖) := mul_le_mul_of_nonneg_left he (norm_nonneg _)
    _ ≤ ‖A‖ / 4 := by nlinarith [norm_nonneg A]

/-- Inverting a logarithm gives the required exponential sheet `Φ(γ(s)) = q exp s`,
including a holomorphic inverse and its nonzero derivative on the whole disk. -/
theorem exponential_inverse_branch {F Φ : ℂ → ℂ} {z A q : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hA : A ≠ 0) (hF : DifferentiableOn ℂ F (ball z ρ))
    (hclose : ∀ w ∈ ball z ρ, ‖deriv F w - A‖ ≤ ‖A‖ / 4)
    (hΦ : ∀ w ∈ ball z ρ, Φ w = q * Complex.exp (F w - F z)) :
    ∃ γ : ℂ → ℂ, γ 0 = z ∧
      MapsTo γ (ball 0 (3 * ‖A‖ * ρ / 4)) (ball z ρ) ∧
      AnalyticOnNhd ℂ γ (ball 0 (3 * ‖A‖ * ρ / 4)) ∧
      InjOn γ (ball 0 (3 * ‖A‖ * ρ / 4)) ∧
      ∀ s ∈ ball 0 (3 * ‖A‖ * ρ / 4),
        Φ (γ s) = q * Complex.exp s ∧
          deriv γ s = (deriv F (γ s))⁻¹ ∧ deriv γ s ≠ 0 := by
  obtain ⟨γ, hγ0, hγmap, hγd, hγinj, hγ⟩ := quantitative_inverse_branch hρ hA hF hclose
  refine ⟨γ, hγ0, hγmap, hγd.analyticOnNhd isOpen_ball, hγinj, fun s hs => ?_⟩
  obtain ⟨heq, hd, hne⟩ := hγ s hs
  refine ⟨?_, hd.deriv, hne⟩
  rw [hΦ _ (hγmap hs), heq, add_sub_cancel_left]

end ThreeIM
