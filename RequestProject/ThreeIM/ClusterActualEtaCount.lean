module

public import RequestProject.ThreeIM.ClusterPaddedFactors
public import RequestProject.ThreeIM.ClusterStepOne
public import RequestProject.ThreeIM.ClusterRegularModels
public import RequestProject.ThreeIM.ClusterUnionCount

/-! # The genuine eta-cluster count from actual characteristic data -/

@[expose] public section

set_option autoImplicit false

open Set Metric Filter Topology Real
open scoped BigOperators

namespace ThreeIM

/-- Actual Step 1 extractions imply the complete q-independent eta-union
count. Factor bounds, Wronskian probes, and log-derivative identities are
all derived; finite fibers are meromorphic-germ assertions. -/
theorem actual_eta_union_meromorphic_card_le (s : Finset ℂ) {Φ A Ψ : ℂ → ℂ}
    {q : ℂ} {r R Δ : ℝ}
    (D : DivisorFactorData Φ (r + 7 * Δ / 8))
    (E : DivisorFactorData A (r + 7 * Δ / 8))
    (P : DivisorFactorData Ψ (r + 7 * Δ / 8))
    (hΦ : MeromorphicOn Φ univ) (hA : MeromorphicOn A univ) (hΨ : MeromorphicOn Ψ univ)
    (hlog : A = logDeriv Φ) (hr : 1 ≤ r) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hR : R = r + Δ)
    (hs : ∀ z ∈ s, ‖z‖ ≤ r ∧ 0 < meromorphicOrderAt (fun w => Φ w - q) z)
    (hcover : ∀ z ∈ s, ∃ c ∈ jointDivisorSupport D E P,
      dist z c ≤ Real.exp (-4 * finiteDiskBudget R Δ (finiteDiskCoefficientMass Φ A Ψ R))) :
    (s.card : ℝ) ≤ 250 * (finiteDiskBudget R Δ (finiteDiskCoefficientMass Φ A Ψ R)) ^ 3 := by
  let ρ := r + 7 * Δ / 8
  let M := finiteDiskCoefficientMass Φ A Ψ R
  let B := finiteDiskBudget R Δ M
  let S := jointDivisorSupport D E P
  let N := jointDivisorMass D E P
  have hR1 : 1 ≤ R := by linarith
  have hρ : 1 ≤ ρ := by dsimp [ρ]; linarith
  have hwindow : ρ ≤ R - Δ / 8 := by dsimp [ρ]; linarith
  have hM : 1 ≤ M := finiteDiskCoefficientMass_ge_one Φ A Ψ hR1
  obtain ⟨hB, hRB, hInvB, hmassB⟩ := finiteDiskBudget_basic_controls hR1 hΔ hΔ1 hM
  have hBpos : 0 < B := by linarith
  have hΔB : B⁻¹ ≤ Δ := by
    have hi := inv_anti₀ (inv_pos.mpr hΔ) hInvB
    simpa only [inv_inv] using hi
  have ht : 1 ≤ Δ⁻¹ := (one_le_inv₀ hΔ).mpr hΔ1
  have hRX : R ≤ R ^ 3 * M * (Δ⁻¹) ^ 2 := by
    calc
      R ≤ R ^ 3 := by simpa only [pow_one] using pow_le_pow_right₀ hR1 (by decide : 1 ≤ 3)
      _ ≤ R ^ 3 * M := le_mul_of_one_le_right (by positivity) hM
      _ ≤ R ^ 3 * M * (Δ⁻¹) ^ 2 := le_mul_of_one_le_right (by positivity) (one_le_pow₀ ht)
  have hmargin := finiteDiskBudget_re_margin hR1 hΔ hΔ1 hM
  have htwice : 2 * R ≤ B := by
    have hX0 : 0 ≤ R ^ 3 * M * (Δ⁻¹) ^ 2 := by positivity
    nlinarith
  have hrB : r + 1 ≤ B := by linarith
  have hmass := jointDivisorMass_le_window D E P hΦ hA hΨ hρ hΔ hwindow
  have hNB : N ≤ B := by
    have houter : ValueDistribution.characteristic A ⊤ R + ValueDistribution.characteristic A⁻¹ ⊤ R +
        ValueDistribution.characteristic Ψ ⊤ R + ValueDistribution.characteristic Ψ⁻¹ ⊤ R +
        ValueDistribution.logCounting Φ ⊤ R + ValueDistribution.logCounting Φ⁻¹ ⊤ R ≤ M := by
      dsimp [M, finiteDiskCoefficientMass]
      linarith
    exact (hmass.trans ((mul_le_mul_of_nonneg_left houter (show 0 ≤ 8 * R / Δ by positivity)).trans_eq (by ring))).trans hmassB
  have hcard : (S.card : ℝ) ≤ B := (jointDivisorSupport_card_le_mass D E P).trans hNB
  have hρR : ρ ≤ R := by dsimp [ρ]; linarith
  have hroots : ∀ α ∈ S, ‖α‖ ≤ B := fun α hα =>
    (jointDivisorSupport_roots D E P α hα).trans (hρR.trans hRB)
  have hDS : D.support ⊆ S := fun _ hα => Finset.mem_union_left _ (Finset.mem_union_left _ hα)
  have hES : E.support ⊆ S := fun _ hα => Finset.mem_union_left _ (Finset.mem_union_right _ hα)
  have hDdegree : (∑ α ∈ S, |(D.exponent α : ℝ)|) ≤ B := by
    apply le_trans _ hNB
    change (∑ α ∈ S, |(D.exponent α : ℝ)|) ≤
      ∑ α ∈ S, (|(D.exponent α : ℝ)| + |(E.exponent α : ℝ)| + |(P.exponent α : ℝ)|)
    apply Finset.sum_le_sum
    intro α _
    linarith [abs_nonneg (E.exponent α : ℝ), abs_nonneg (P.exponent α : ℝ)]
  have hEdegree : (∑ α ∈ S, |(E.exponent α : ℝ)|) ≤ B := by
    apply le_trans _ hNB
    change (∑ α ∈ S, |(E.exponent α : ℝ)|) ≤
      ∑ α ∈ S, (|(D.exponent α : ℝ)| + |(E.exponent α : ℝ)| + |(P.exponent α : ℝ)|)
    apply Finset.sum_le_sum
    intro α _
    linarith [abs_nonneg (D.exponent α : ℝ), abs_nonneg (P.exponent α : ℝ)]
  have hm : (∑ α ∈ S, ((D.exponent α).toNat : ℝ)) ≤ B :=
    (Finset.sum_le_sum (fun α _ => int_toNat_real_le_abs (D.exponent α))).trans hDdegree
  have hn : (∑ α ∈ S, ((-D.exponent α).toNat : ℝ)) ≤ B := by
    have hh := Finset.sum_le_sum (s := S) (fun α _ => int_toNat_real_le_abs (-D.exponent α))
    have hh' : (∑ α ∈ S, ((-D.exponent α).toNat : ℝ)) ≤
        ∑ α ∈ S, |(D.exponent α : ℝ)| := by
      simpa only [Int.cast_neg, abs_neg] using hh
    exact hh'.trans hDdegree
  have hdomain : ball (0 : ℂ) (r + Δ / 4) ⊆ ball (0 : ℂ) ρ :=
    ball_subset_ball (by dsimp [ρ]; linarith)
  have hStep := finite_disk_factor_control D E P hΦ hA hΨ hlog hr hΔ hΔ1 hR
  apply factorized_eta_union_meromorphic_card_le (Φ := Φ) (H := D.H) (h := E.H)
    (m := fun α => (D.exponent α).toNat) (n := fun α => (-D.exponent α).toNat)
    (d := E.exponent) (ζ := q) s S hB hcard hrB hΔB hroots hm hn hEdegree
    (D.H_analytic.mono hdomain)
  · intro w hw
    exact hStep.1 w (ball_subset_closedBall hw)
  · intro w hw
    have hbig : w ∈ closedBall (0 : ℂ) (r + Δ / 2) :=
      closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hw)
    have hp := (hStep.2 w hbig).1
    change |(E.H w).re| + |(P.H w).re| ≤ B / 1000 at hp
    linarith [neg_abs_le (E.H w).re, abs_nonneg (P.H w).re]
  · exact D.quotient_logDeriv_on_superset E hlog S hDS hES isOpen_ball hdomain
  · exact D.cleared_factor_on_superset S hDS hdomain
  · exact hs
  · exact hcover

end ThreeIM
