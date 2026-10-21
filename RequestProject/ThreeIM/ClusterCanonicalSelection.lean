module

public import RequestProject.ThreeIM.ClusterRegularControl
public import RequestProject.ThreeIM.ClusterGerms

/-!
# Canonical marked fibers, the actual bad-point count, and good sheets

The fiber hypothesis is a genuine positive meromorphic order of raw Phi-q.
It is transported to the honest model by a punctured limit, never by raw
center substitution. The bad-point estimates and inverse sheets are then
instantiated with the same actual Step 1 factors.
-/

@[expose] public section

set_option autoImplicit false

open Set Filter Metric Topology Real
open scoped BigOperators

namespace ThreeIM

theorem DivisorFactorData.exponentialModel_eq_of_fiber_order_pos {Φ : ℂ → ℂ} {ρ : ℝ}
    (D : DivisorFactorData Φ ρ) {z q : ℂ} (hz : z ∈ ball (0 : ℂ) ρ)
    (hne : ∀ α ∈ D.support, z ≠ α)
    (horder : 0 < meromorphicOrderAt (fun w => Φ w - q) z) : D.exponentialModel z = q := by
  have hraw := D.exponentialModel_eq_codiscrete (show ball (0 : ℂ) ρ ⊆ ball 0 ρ from subset_rfl)
  have hclear : D.exponentialModel =ᶠ[codiscreteWithin (ball (0 : ℂ) ρ)]
      (fun w => Φ w * (1 : ℂ)) := by simpa only [mul_one] using hraw.symm
  have hlim := (tendsto_zero_of_meromorphicOrderAt_pos horder).add_const q
  have hlimΦ : Tendsto Φ (𝓝[≠] z) (𝓝 q) := by
    simpa only [sub_add_cancel, zero_add] using hlim
  have heq := cleared_numerator_eq_of_codiscrete_limit isOpen_ball hz
    (D.exponentialModel_analyticAt hz hne).continuousAt continuousAt_const hlimΦ hclear
  simpa only [mul_one] using heq

/-- The original bad-point count now has only genuine function, radius,
and fiber data as inputs; all analytic regular-disk hypotheses are derived. -/
theorem canonical_bad_qpoints_card_le (s : Finset ℂ) {Φ A Ψ : ℂ → ℂ} {q : ℂ} {r R Δ : ℝ}
    (D : DivisorFactorData Φ (r + 7 * Δ / 8))
    (E : DivisorFactorData A (r + 7 * Δ / 8))
    (P : DivisorFactorData Ψ (r + 7 * Δ / 8))
    (hΦ : MeromorphicOn Φ univ) (hA : MeromorphicOn A univ) (hΨ : MeromorphicOn Ψ univ)
    (hlog : A = logDeriv Φ) (hr : 1 ≤ r) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hR : R = r + Δ)
    (hdisk : ∀ z ∈ s, ‖z‖ ≤ r)
    (haway : ∀ z ∈ s, Real.exp (-4 * finiteDiskBudget R Δ (finiteDiskCoefficientMass Φ A Ψ R)) ≤
      truncatedDivisorDistance (jointDivisorSupport D E P) z)
    (hbad : ∀ z ∈ s, ‖E.exponentialModel z‖ ≤
      (finiteDiskBudget R Δ (finiteDiskCoefficientMass Φ A Ψ R)) ^ 10 /
        truncatedDivisorDistance (jointDivisorSupport D E P) z)
    (hfiber : ∀ z ∈ s, 0 < meromorphicOrderAt (fun w => Φ w - q) z) :
    (s.card : ℝ) ≤ 2500000 * (finiteDiskBudget R Δ (finiteDiskCoefficientMass Φ A Ψ R)) ^ 26 := by
  let M := finiteDiskCoefficientMass Φ A Ψ R
  let B := finiteDiskBudget R Δ M
  let S := jointDivisorSupport D E P
  have hR1 : 1 ≤ R := by linarith
  have hM : 1 ≤ M := finiteDiskCoefficientMass_ge_one Φ A Ψ hR1
  obtain ⟨hB, hRB, _, hmassB⟩ := finiteDiskBudget_basic_controls hR1 hΔ hΔ1 hM
  have hρ : 1 ≤ r + 7 * Δ / 8 := by linarith
  have hwindow : r + 7 * Δ / 8 ≤ R - Δ / 8 := by linarith
  have hmass := jointDivisorMass_le_window D E P hΦ hA hΨ hρ hΔ hwindow
  have hSB : (S.card : ℝ) ≤ B := by
    have houter : ValueDistribution.characteristic A ⊤ R + ValueDistribution.characteristic A⁻¹ ⊤ R +
        ValueDistribution.characteristic Ψ ⊤ R + ValueDistribution.characteristic Ψ⁻¹ ⊤ R +
        ValueDistribution.logCounting Φ ⊤ R + ValueDistribution.logCounting Φ⁻¹ ⊤ R ≤ M := by
      dsimp [M, finiteDiskCoefficientMass]
      linarith
    exact (jointDivisorSupport_card_le_mass D E P).trans
      ((hmass.trans ((mul_le_mul_of_nonneg_left houter (show 0 ≤ 8 * R / Δ by positivity)).trans_eq (by ring))).trans hmassB)
  have hdata (z : ℂ) (hz : z ∈ s) :=
    canonical_regular_branch_data D E P hΦ hA hΨ hlog hr hΔ hΔ1 hR (hdisk z hz) (haway z hz)
  apply bad_qpoints_away_divisors_card_le (Φ := D.exponentialModel) (A := E.exponentialModel)
    (q := q) (c := 0) s S hB (by linarith : 0 ≤ r)
    (show r ≤ B from (by linarith : r ≤ R).trans hRB) hSB
    (fun z hz => (hdata z hz).toRegularBadPoint (hbad z hz)) haway
  · intro z hz
    have hzρ : z ∈ ball (0 : ℂ) (r + 7 * Δ / 8) := by
      rw [mem_ball, dist_zero_right]
      linarith [hdisk z hz]
    have hne : ∀ α ∈ D.support, z ≠ α := by
      intro α hα heq
      have hdist := truncatedDivisorDistance_le_norm_sub
        (show α ∈ S from Finset.mem_union_left _ (Finset.mem_union_left _ hα)) (z := z)
      have hzero : ‖z - α‖ = 0 := by simp only [heq, sub_self, norm_zero]
      rw [hzero] at hdist
      linarith only [hdist, (hdata z hz).distance_pos]
    exact D.exponentialModel_eq_of_fiber_order_pos hzρ hne (hfiber z hz)
  · intro z hz
    simpa only [dist_zero_right] using hdisk z hz

/-- A good point of a genuine raw q-fiber gives the full quantitative
sheet with the canonical identity Phi_model(gamma(s))=q exp(s). -/
theorem canonical_good_qpoint_branch {Φ A Ψ : ℂ → ℂ} {q z v : ℂ} {r R Δ : ℝ}
    (D : DivisorFactorData Φ (r + 7 * Δ / 8))
    (E : DivisorFactorData A (r + 7 * Δ / 8))
    (P : DivisorFactorData Ψ (r + 7 * Δ / 8))
    (hΦ : MeromorphicOn Φ univ) (hA : MeromorphicOn A univ) (hΨ : MeromorphicOn Ψ univ)
    (hlog : A = logDeriv Φ) (hr : 1 ≤ r) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hR : R = r + Δ)
    (hz : ‖z‖ ≤ r)
    (haway : Real.exp (-4 * finiteDiskBudget R Δ (finiteDiskCoefficientMass Φ A Ψ R)) ≤
      truncatedDivisorDistance (jointDivisorSupport D E P) z)
    (hgood : (finiteDiskBudget R Δ (finiteDiskCoefficientMass Φ A Ψ R)) ^ 10 /
      truncatedDivisorDistance (jointDivisorSupport D E P) z < ‖E.exponentialModel z‖)
    (hfiber : 0 < meromorphicOrderAt (fun w => Φ w - q) z) (hv : v ^ 2 = P.exponentialModel z) :
    ∃ b : GoodPointBranch D.exponentialModel E.exponentialModel P.exponentialModel z v
      (finiteDiskBudget R Δ (finiteDiskCoefficientMass Φ A Ψ R))
      (truncatedDivisorDistance (jointDivisorSupport D E P) z),
      ∀ s ∈ ball 0 ((finiteDiskBudget R Δ (finiteDiskCoefficientMass Φ A Ψ R)) ^ 6 / 2),
        D.exponentialModel (b.gamma s) = q * Complex.exp s := by
  have hdata := canonical_regular_branch_data D E P hΦ hA hΨ hlog hr hΔ hΔ1 hR hz haway
  obtain ⟨b⟩ := hdata.good_branch hgood hv
  have hzρ : z ∈ ball (0 : ℂ) (r + 7 * Δ / 8) := by
    rw [mem_ball, dist_zero_right]
    linarith
  have hne : ∀ α ∈ D.support, z ≠ α := by
    intro α hα heq
    have hdist := truncatedDivisorDistance_le_norm_sub
      (show α ∈ jointDivisorSupport D E P from Finset.mem_union_left _ (Finset.mem_union_left _ hα)) (z := z)
    have hzero : ‖z - α‖ = 0 := by simp only [heq, sub_self, norm_zero]
    rw [hzero] at hdist
    linarith only [hdist, hdata.distance_pos]
  have hvalue := D.exponentialModel_eq_of_fiber_order_pos hzρ hne hfiber
  refine ⟨b, fun s hs => ?_⟩
  rw [b.gamma_exp s hs, hvalue]

end ThreeIM
