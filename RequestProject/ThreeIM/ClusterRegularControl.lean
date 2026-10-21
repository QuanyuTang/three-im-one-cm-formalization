module

public import RequestProject.ThreeIM.ClusterStepOne
public import RequestProject.ThreeIM.ClusterRegularModels
public import RequestProject.ThreeIM.GoodPointBranch

/-!
# The actual regular-disk data used by counting and inverse branches

All three functions here are the honest exponential models from the same
divisor extractions. Raw auxiliary values are never read at removable junk
points. The source's regular-disk and center estimates follow from Step 1.
-/

@[expose] public section

set_option autoImplicit false

open Set Metric Real
open scoped BigOperators

namespace ThreeIM

/-- Local data common to the bad-point packing and good-point sheet. -/
structure RegularBranchData (Φ A Ψ : ℂ → ℂ) (z : ℂ) (B d : ℝ) : Prop where
  budget_large : 4 ≤ B
  distance_pos : 0 < d
  phi_holo : DifferentiableOn ℂ Φ (ball z (d / B ^ 4))
  phi_ne_zero : ∀ w ∈ ball z (d / B ^ 4), Φ w ≠ 0
  a_holo : DifferentiableOn ℂ A (ball z (d / B ^ 4))
  a_ne_zero : ∀ w ∈ ball z (d / B ^ 4), A w ≠ 0
  psi_holo : DifferentiableOn ℂ Ψ (ball z (d / B ^ 4))
  psi_ne_zero : ∀ w ∈ ball z (d / B ^ 4), Ψ w ≠ 0
  log_deriv_phi : ∀ w ∈ ball z (d / B ^ 4), deriv Φ w / Φ w = A w
  log_deriv_bound : ∀ w ∈ ball z (d / B ^ 4),
    ‖deriv A w / A w‖ + ‖deriv Ψ w / Ψ w‖ ≤ 8 * B / d
  center_log_a : |Real.log ‖A z‖| ≤ 6 * B ^ 2
  center_log_psi : |Real.log ‖Ψ z‖| ≤ 6 * B ^ 2

theorem RegularBranchData.toRegularBadPoint {Φ A Ψ : ℂ → ℂ} {z : ℂ} {B d : ℝ}
    (h : RegularBranchData Φ A Ψ z B d) (hbad : ‖A z‖ ≤ B ^ 10 / d) :
    RegularBadPoint Φ A z B d := {
  distance_pos := h.distance_pos
  phi_holo := h.phi_holo
  phi_ne_zero := h.phi_ne_zero
  a_holo := h.a_holo
  a_ne_zero := h.a_ne_zero
  log_deriv_phi := h.log_deriv_phi
  log_deriv_bound := fun w hw => (le_add_of_nonneg_right (norm_nonneg _)).trans (h.log_deriv_bound w hw)
  bad := hbad
}

theorem RegularBranchData.good_branch {Φ A Ψ : ℂ → ℂ} {z v : ℂ} {B d : ℝ}
    (h : RegularBranchData Φ A Ψ z B d) (hgood : B ^ 10 / d < ‖A z‖) (hv : v ^ 2 = Ψ z) :
    Nonempty (GoodPointBranch Φ A Ψ z v B d) :=
  exists_good_point_branch h.budget_large h.distance_pos h.phi_holo h.phi_ne_zero
    h.a_holo h.a_ne_zero h.psi_holo h.psi_ne_zero h.log_deriv_phi h.log_deriv_bound
    hgood h.center_log_a h.center_log_psi hv

/-- Every point outside the actual eta-divisor clusters has all the
regular disk and center estimates required by the already proved packing
and good-point branch lemmas. The estimates use the original exact M/B. -/
theorem canonical_regular_branch_data {Φ A Ψ : ℂ → ℂ} {r R Δ : ℝ}
    (D : DivisorFactorData Φ (r + 7 * Δ / 8))
    (E : DivisorFactorData A (r + 7 * Δ / 8))
    (P : DivisorFactorData Ψ (r + 7 * Δ / 8))
    (hΦ : MeromorphicOn Φ univ) (hA : MeromorphicOn A univ) (hΨ : MeromorphicOn Ψ univ)
    (hlog : A = logDeriv Φ) (hr : 1 ≤ r) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hR : R = r + Δ)
    {z : ℂ} (hz : ‖z‖ ≤ r)
    (haway : Real.exp (-4 * finiteDiskBudget R Δ (finiteDiskCoefficientMass Φ A Ψ R)) ≤
      truncatedDivisorDistance (jointDivisorSupport D E P) z) :
    RegularBranchData D.exponentialModel E.exponentialModel P.exponentialModel z
      (finiteDiskBudget R Δ (finiteDiskCoefficientMass Φ A Ψ R))
      (truncatedDivisorDistance (jointDivisorSupport D E P) z) := by
  let ρ := r + 7 * Δ / 8
  let M := finiteDiskCoefficientMass Φ A Ψ R
  let B := finiteDiskBudget R Δ M
  let S := jointDivisorSupport D E P
  let d := truncatedDivisorDistance S z
  let N := jointDivisorMass D E P
  have hR1 : 1 ≤ R := by linarith
  have hρ : 1 ≤ ρ := by dsimp [ρ]; linarith
  have hwindow : ρ ≤ R - Δ / 8 := by dsimp [ρ]; linarith
  have hM : 1 ≤ M := finiteDiskCoefficientMass_ge_one Φ A Ψ hR1
  obtain ⟨hB, hRB, hInvB, hmassB⟩ := finiteDiskBudget_basic_controls hR1 hΔ hΔ1 hM
  have hBpos : 0 < B := by linarith
  have hd : 0 < d := (Real.exp_pos (-4 * B)).trans_le haway
  have hd1 : d ≤ 1 := truncatedDivisorDistance_le_one S z
  have hΔB : B⁻¹ ≤ Δ := by
    have hi := inv_anti₀ (inv_pos.mpr hΔ) hInvB
    simpa only [inv_inv] using hi
  have hgeo := regular_disk_geometry S hB hΔB hz hd
  have hDS : D.support ⊆ S := fun _ hα => Finset.mem_union_left _ (Finset.mem_union_left _ hα)
  have hES : E.support ⊆ S := fun _ hα => Finset.mem_union_left _ (Finset.mem_union_right _ hα)
  have hPS : P.support ⊆ S := Finset.subset_union_right
  have hreg : ∀ w ∈ ball z (d / B ^ 4), ∀ α ∈ S, w ≠ α := by
    intro w hw α hα heq
    have hsep := hgeo.2 w hw α hα
    rw [heq, sub_self, norm_zero] at hsep
    linarith
  have hinner : ∀ w ∈ ball z (d / B ^ 4), w ∈ ball (0 : ℂ) ρ := by
    intro w hw
    exact ball_subset_ball (by dsimp [ρ]; linarith : r + Δ / 2 ≤ ρ) (hgeo.1 hw)
  have hStep := finite_disk_factor_control D E P hΦ hA hΨ hlog hr hΔ hΔ1 hR
  change (∀ w ∈ closedBall (0 : ℂ) (r + Δ / 4), ‖deriv D.H w‖ ≤ Real.exp B) ∧
    (∀ w ∈ closedBall (0 : ℂ) (r + Δ / 2),
      |(E.H w).re| + |(P.H w).re| ≤ B / 1000 ∧ ‖deriv E.H w‖ + ‖deriv P.H w‖ ≤ B / 2) at hStep
  have hmass := jointDivisorMass_le_window D E P hΦ hA hΨ hρ hΔ hwindow
  have hNB : N ≤ B := by
    have houter : ValueDistribution.characteristic A ⊤ R + ValueDistribution.characteristic A⁻¹ ⊤ R +
        ValueDistribution.characteristic Ψ ⊤ R + ValueDistribution.characteristic Ψ⁻¹ ⊤ R +
        ValueDistribution.logCounting Φ ⊤ R + ValueDistribution.logCounting Φ⁻¹ ⊤ R ≤ M := by
      dsimp [M, finiteDiskCoefficientMass]
      linarith
    exact (hmass.trans ((mul_le_mul_of_nonneg_left houter (show 0 ≤ 8 * R / Δ by positivity)).trans_eq (by ring))).trans hmassB
  have hdegrees : (∑ α ∈ E.support, |(E.exponent α : ℝ)|) +
      (∑ α ∈ P.support, |(P.exponent α : ℝ)|) ≤ B := by
    have hn : 0 ≤ ∑ α ∈ D.support, |(D.exponent α : ℝ)| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    have heq := jointDivisorMass_eq_sum_degrees D E P
    change N = _ at heq
    linarith
  have hEdegree : (∑ α ∈ E.support, |(E.exponent α : ℝ)|) ≤ B := by
    have hn : 0 ≤ ∑ α ∈ P.support, |(P.exponent α : ℝ)| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    linarith
  have hPdegree : (∑ α ∈ P.support, |(P.exponent α : ℝ)|) ≤ B := by
    have hn : 0 ≤ ∑ α ∈ E.support, |(E.exponent α : ℝ)| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    linarith
  have hzinner : z ∈ closedBall (0 : ℂ) (r + Δ / 2) := by
    rw [mem_closedBall, dist_zero_right]
    linarith
  have hcenter {F : ℂ → ℂ} (Q : DivisorFactorData F ρ)
      (hQS : Q.support ⊆ S) (hQre : |(Q.H z).re| ≤ B / 1000)
      (hQdegree : (∑ α ∈ Q.support, |(Q.exponent α : ℝ)|) ≤ B) :
      |Real.log ‖Q.exponentialModel z‖| ≤ 6 * B ^ 2 := by
    have hband : ∀ α ∈ Q.support,
        Real.exp (-(4 * B)) ≤ ‖z - α‖ ∧ ‖z - α‖ ≤ Real.exp (4 * B) := by
      intro α hα
      have hη : Real.exp (-(4 * B)) ≤ d := by simpa only [neg_mul] using haway
      refine ⟨hη.trans (truncatedDivisorDistance_le_norm_sub (hQS hα)), ?_⟩
      have hroot := Q.roots α hα
      have hρR : ρ ≤ R := by dsimp [ρ]; linarith
      calc
        ‖z - α‖ ≤ ‖z‖ + ‖α‖ := norm_sub_le _ _
        _ ≤ 2 * B := by linarith
        _ ≤ Real.exp (4 * B) :=
          (by linarith : 2 * B ≤ 4 * B + 1).trans (Real.add_one_le_exp _)
    have hb := Q.abs_log_norm_exponentialModel_le (by positivity : 0 ≤ 4 * B) hQre hband hQdegree
    have hB2 : B ≤ B ^ 2 := by
      simpa only [pow_one] using pow_le_pow_right₀ (show 1 ≤ B by linarith) (by decide : 1 ≤ 2)
    exact hb.trans (by nlinarith)
  refine {
    budget_large := hB
    distance_pos := hd
    phi_holo := fun w hw => (D.exponentialModel_analyticAt (hinner w hw)
      (fun α hα => hreg w hw α (hDS hα))).differentiableAt.differentiableWithinAt
    phi_ne_zero := fun w hw => D.exponentialModel_ne_zero (fun α hα => hreg w hw α (hDS hα))
    a_holo := fun w hw => (E.exponentialModel_analyticAt (hinner w hw)
      (fun α hα => hreg w hw α (hES hα))).differentiableAt.differentiableWithinAt
    a_ne_zero := fun w hw => E.exponentialModel_ne_zero (fun α hα => hreg w hw α (hES hα))
    psi_holo := fun w hw => (P.exponentialModel_analyticAt (hinner w hw)
      (fun α hα => hreg w hw α (hPS hα))).differentiableAt.differentiableWithinAt
    psi_ne_zero := fun w hw => P.exponentialModel_ne_zero (fun α hα => hreg w hw α (hPS hα))
    log_deriv_phi := ?_
    log_deriv_bound := ?_
    center_log_a := hcenter E hES (by linarith [(hStep.2 z hzinner).1, abs_nonneg (P.H z).re]) hEdegree
    center_log_psi := hcenter P hPS (by linarith [(hStep.2 z hzinner).1, abs_nonneg (E.H z).re]) hPdegree
  }
  · intro w hw
    rw [D.logDeriv_exponentialModel (hinner w hw) (fun α hα => hreg w hw α (hDS hα))]
    exact eq_sub_iff_add_eq.mp (D.deriv_H_eq_logDeriv_model_sub_sum E hlog (hinner w hw)
      (fun α hα => hreg w hw α (hDS hα)) (fun α hα => hreg w hw α (hES hα)))
  · intro w hw
    rw [E.logDeriv_exponentialModel (hinner w hw) (fun α hα => hreg w hw α (hES hα)),
      P.logDeriv_exponentialModel (hinner w hw) (fun α hα => hreg w hw α (hPS hα))]
    have he := norm_sum_divisor_fractions_le E.support (show 0 < d / 2 by positivity)
      (fun α hα => hgeo.2 w hw α (hES hα)) (show (∑ α ∈ E.support, |(E.exponent α : ℝ)|) ≤
        ∑ α ∈ E.support, |(E.exponent α : ℝ)| from le_rfl)
    have hp := norm_sum_divisor_fractions_le P.support (show 0 < d / 2 by positivity)
      (fun α hα => hgeo.2 w hw α (hPS hα)) (show (∑ α ∈ P.support, |(P.exponent α : ℝ)|) ≤
        ∑ α ∈ P.support, |(P.exponent α : ℝ)| from le_rfl)
    have hfrac : (∑ α ∈ E.support, |(E.exponent α : ℝ)|) / (d / 2) +
        (∑ α ∈ P.support, |(P.exponent α : ℝ)|) / (d / 2) ≤ 2 * B / d := by
      rw [← add_div]
      exact (div_le_div_of_nonneg_right hdegrees (by positivity)).trans_eq (by rw [div_div_eq_mul_div]; ring)
    have hderiv := (hStep.2 w (ball_subset_closedBall (hgeo.1 hw))).2
    have hBdiv : B ≤ B / d := (le_div_iff₀ hd).mpr (mul_le_of_le_one_right hBpos.le hd1)
    have hBdiv0 : 0 ≤ B / d := by positivity
    have hsum := add_le_add
      (norm_add_le (deriv E.H w) (∑ α ∈ E.support, (E.exponent α : ℂ) / (w - α)))
      (norm_add_le (deriv P.H w) (∑ α ∈ P.support, (P.exponent α : ℂ) / (w - α)))
    change ‖deriv E.H w + ∑ α ∈ E.support, (E.exponent α : ℂ) / (w - α)‖ +
      ‖deriv P.H w + ∑ α ∈ P.support, (P.exponent α : ℂ) / (w - α)‖ ≤ 8 * B / d
    have hfrac' : (∑ α ∈ E.support, |(E.exponent α : ℝ)|) / (d / 2) +
        (∑ α ∈ P.support, |(P.exponent α : ℝ)|) / (d / 2) ≤ 2 * (B / d) :=
      hfrac.trans_eq (mul_div_assoc 2 B d)
    have hfinal : ‖deriv E.H w + ∑ α ∈ E.support, (E.exponent α : ℂ) / (w - α)‖ +
        ‖deriv P.H w + ∑ α ∈ P.support, (P.exponent α : ℂ) / (w - α)‖ ≤ 8 * (B / d) := by
      linarith only [he, hp, hfrac', hderiv, hBdiv, hBdiv0, hsum]
    exact hfinal.trans_eq (mul_div_assoc 8 B d).symm

end ThreeIM
