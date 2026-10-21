module

public import RequestProject.ThreeIM.ClusterLogExistence
public import Mathlib.Analysis.Meromorphic.FactorizedRational

/-!
# Coupled divisor, zero-free factor, and logarithm witnesses

Step 1 uses the same zero-free factor g both on the extraction circle and
inside its disk, where g=exp(H). This structure retains the actual function
identity and log-norm identity from a single extraction. Its existence is
proved from the original meromorphic and finite-order hypotheses.
-/

@[expose] public section

set_option autoImplicit false

open Set Filter Metric Topology Real
open scoped BigOperators

namespace ThreeIM

/-- Coupled data from one actual zero/pole extraction. The boundary g and
interior H belong to the same witness, rather than unrelated choices. -/
structure DivisorFactorData (F : ℂ → ℂ) (R : ℝ) where
  support : Finset ℂ
  exponent : ℂ → ℤ
  g : ℂ → ℂ
  H : ℂ → ℂ
  support_iff : ∀ α, α ∈ support ↔ exponent α ≠ 0
  roots : ∀ α ∈ support, ‖α‖ ≤ R
  exponent_eq_order : ∀ z ∈ closedBall (0 : ℂ) R,
    exponent z = (meromorphicOrderAt F z).untop₀
  g_analytic : AnalyticOnNhd ℂ g (closedBall 0 R)
  g_ne_zero : ∀ z ∈ closedBall (0 : ℂ) R, g z ≠ 0
  H_analytic : AnalyticOnNhd ℂ H (ball 0 R)
  exp_H : ∀ z ∈ ball (0 : ℂ) R, Complex.exp (H z) = g z
  factor : F =ᶠ[codiscreteWithin (closedBall (0 : ℂ) R)]
    (fun z => (∏ α ∈ support, (z - α) ^ exponent α) * g z)
  log_norm : (fun z => Real.log ‖F z‖) =ᶠ[codiscreteWithin (closedBall (0 : ℂ) R)]
    (fun z => (∑ α ∈ support, (exponent α : ℝ) * Real.log ‖z - α‖) + Real.log ‖g z‖)

/-- The complete coupled factor data exist; factor existence is proved
here, not added to the original selection assumptions. -/
theorem exists_divisorFactorData {F : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hF : MeromorphicOn F (closedBall 0 R))
    (hnz : ∀ z ∈ closedBall (0 : ℂ) R, meromorphicOrderAt F z ≠ ⊤) :
    Nonempty (DivisorFactorData F R) := by
  classical
  let U : Set ℂ := closedBall 0 R
  let D := MeromorphicOn.divisor F U
  have hfin := D.finiteSupport (isCompact_closedBall (0 : ℂ) R)
  let S : Finset ℂ := hfin.toFinset
  obtain ⟨g, hg, hg0, hfac⟩ := hF.extract_zeros_poles (fun z => hnz z z.property) hfin
  have hlog := MeromorphicOn.extract_zeros_poles_log hg0 hfac
  have hsum : (∑ᶠ α, fun z : ℂ => (D α : ℝ) * Real.log ‖z - α‖) =
      fun z => ∑ α ∈ S, (D α : ℝ) * Real.log ‖z - α‖ := by
    rw [finsum_eq_sum_of_support_subset (s := S)]
    · ext z
      simp only [Finset.sum_apply]
    · intro α hα
      simp only [Function.mem_support, ne_eq] at hα
      simp only [S, Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support, ne_eq]
      intro hzero
      apply hα
      ext z
      simp only [hzero, Int.cast_zero, zero_mul, Pi.zero_apply]
  have hprod : (∏ᶠ α, (fun z : ℂ => z - α) ^ D α) =
      fun z => ∏ α ∈ S, (z - α) ^ D α := by
    rw [finprod_eq_prod_of_mulSupport_subset (s := S)]
    · ext z
      simp only [Finset.prod_apply, Pi.pow_apply]
    · intro α hα
      simp only [Function.mem_mulSupport, ne_eq] at hα
      simp only [S, Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support, ne_eq]
      intro hzero
      apply hα
      ext z
      simp only [Pi.pow_apply, hzero, zpow_zero, Pi.one_apply]
  have hgball : DifferentiableOn ℂ g (ball 0 R) := by
    intro z hz
    exact (hg z (ball_subset_closedBall hz)).differentiableAt.differentiableWithinAt
  obtain ⟨H, hH, hexp, -⟩ := exists_analytic_log_on_ball hgball
    (fun z hz => hg0 ⟨z, ball_subset_closedBall hz⟩) hR
  refine ⟨{
    support := S
    exponent := D
    g := g
    H := H
    support_iff := ?_
    roots := ?_
    exponent_eq_order := ?_
    g_analytic := hg
    g_ne_zero := fun z hz => hg0 ⟨z, hz⟩
    H_analytic := hH.analyticOnNhd isOpen_ball
    exp_H := hexp
    factor := ?_
    log_norm := ?_
  }⟩
  · intro α
    simp only [S, Set.Finite.mem_toFinset, Function.mem_support]
  · intro α hα
    have hαU : α ∈ U := D.supportWithinDomain (by
      simpa only [S, Set.Finite.mem_toFinset] using hα)
    simpa only [U, mem_closedBall, dist_zero_right] using hαU
  · intro z hz
    exact MeromorphicOn.divisor_apply hF hz
  · rw [hprod] at hfac
    filter_upwards [hfac] with z hz
    simpa only [Pi.smul_apply', smul_eq_mul] using hz
  · rw [hsum] at hlog
    filter_upwards [hlog] with z hz
    simpa only [Pi.add_apply] using hz

end ThreeIM
