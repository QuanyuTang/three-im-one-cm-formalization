module

public import RequestProject.ThreeIM.ClusterFactorCount
public import RequestProject.ThreeIM.ClusterLogExistence
public import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Tactic.FieldSimp

/-!
# A genuine cleared exponential divisor factorization

Unlike a log-norm identity, the codiscrete function identity retained here
can be used to include actual finite meromorphic fibers in an analytic
cleared numerator. The natural numerator and denominator multiplicities
are the positive and negative parts of the actual integer divisor.
No values of a totalized meromorphic representative at isolated points are
used to extend the identity to the center.
-/

@[expose] public section

open Set Filter Metric Topology
open scoped BigOperators

namespace ThreeIM

/-- A nonzero meromorphic germ on a closed disk has an analytic exponential
times finite divisor product on the open disk, with the poles cleared in a
genuine codiscrete function identity. The returned integer multiplicities
are the actual meromorphic orders. Characteristic bounds are separate. -/
theorem exists_cleared_exp_divisor_factorization {F : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hF : MeromorphicOn F (closedBall 0 R))
    (hnz : ∀ z ∈ closedBall (0 : ℂ) R, meromorphicOrderAt F z ≠ ⊤) :
    ∃ (S : Finset ℂ) (d : ℂ → ℤ) (H : ℂ → ℂ),
      (∀ α ∈ S, ‖α‖ ≤ R ∧ d α = (meromorphicOrderAt F α).untop₀ ∧ d α ≠ 0) ∧
      (∀ α ∉ S, d α = 0) ∧
      AnalyticOnNhd ℂ H (ball 0 R) ∧
      (clearedDivisorNumerator S (fun α => (d α).toNat) H =ᶠ[codiscreteWithin (ball 0 R)]
        (fun z => F z * divisorPowerProduct S (fun α => (-d α).toNat) z)) := by
  classical
  let U : Set ℂ := closedBall 0 R
  let D := MeromorphicOn.divisor F U
  have hfin : D.support.Finite := (MeromorphicOn.divisor F U).finiteSupport (isCompact_closedBall 0 R)
  let S : Finset ℂ := hfin.toFinset
  obtain ⟨g, hg, hg0, hfac⟩ := hF.extract_zeros_poles (fun z => hnz z z.property) hfin
  have hSU : ∀ α ∈ S, α ∈ U := by
    intro α hα
    exact D.supportWithinDomain (by simpa only [S, Set.Finite.mem_toFinset] using hα)
  have hgball : DifferentiableOn ℂ g (ball 0 R) := by
    intro z hz
    exact (hg z (ball_subset_closedBall hz)).differentiableAt.differentiableWithinAt
  obtain ⟨H, hH, hexp, -⟩ := exists_analytic_log_on_ball hgball
    (fun z hz => hg0 ⟨z, ball_subset_closedBall hz⟩) hR
  have hprod : (∏ᶠ α, (fun z : ℂ => z - α) ^ D α) = fun z => ∏ α ∈ S, (z - α) ^ D α := by
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
  rw [hprod] at hfac
  have hfacball := hfac.filter_mono (Filter.codiscreteWithin.mono ball_subset_closedBall)
  have havoid : ∀ᶠ z in codiscreteWithin (ball (0 : ℂ) R), z ∉ (S : Set ℂ) := by
    have hcom : ∀ᶠ z in codiscrete ℂ, z ∉ (S : Set ℂ) := S.finite_toSet.compl_mem_codiscrete
    exact hcom.filter_mono (Filter.codiscreteWithin.mono (subset_univ _))
  refine ⟨S, D, H, ?_, ?_, hH.analyticOnNhd isOpen_ball, ?_⟩
  · intro α hα
    refine ⟨by simpa only [U, mem_closedBall, dist_zero_right] using hSU α hα, ?_⟩
    refine ⟨MeromorphicOn.divisor_apply hF (hSU α hα), ?_⟩
    simpa only [S, Set.Finite.mem_toFinset, Function.mem_support] using hα
  · intro α hα
    by_contra hnonzero
    apply hα
    simpa only [S, Set.Finite.mem_toFinset, Function.mem_support] using hnonzero
  · filter_upwards [hfacball, havoid, self_mem_codiscreteWithin (ball (0 : ℂ) R)] with z hfacz hzS hz
    have hregular : ∀ α ∈ S, z - α ≠ 0 := by
      intro α hα hzero
      have heq := sub_eq_zero.mp hzero
      exact hzS (heq.symm ▸ hα)
    have hQ0 : divisorPowerProduct S (fun α => (-D α).toNat) z ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun α hα => pow_ne_zero _ (hregular α hα))
    have hsplit : (∏ α ∈ S, (z - α) ^ D α) =
        divisorPowerProduct S (fun α => (D α).toNat) z /
          divisorPowerProduct S (fun α => (-D α).toNat) z := by
      change _ = (∏ α ∈ S, (z - α) ^ (D α).toNat) / ∏ α ∈ S, (z - α) ^ (-D α).toNat
      rw [← Finset.prod_div_distrib]
      apply Finset.prod_congr rfl
      intro α hα
      rw [← zpow_natCast_sub_natCast₀ (hregular α hα), Int.toNat_sub_toNat_neg]
    have hFz : F z =
        (divisorPowerProduct S (fun α => (D α).toNat) z /
          divisorPowerProduct S (fun α => (-D α).toNat) z) * g z := by
      simpa only [Pi.smul_apply', smul_eq_mul, hsplit] using hfacz
    change Complex.exp (H z) * divisorPowerProduct S (fun α => (D α).toNat) z = _
    rw [hexp z hz, hFz]
    field_simp [hQ0]

end ThreeIM
