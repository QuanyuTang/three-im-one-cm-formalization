module

public import RequestProject.ThreeIM.ClusterPairControl
public import RequestProject.ThreeIM.ClusterCircleParameters
public import RequestProject.ThreeIM.ClusterControlCircle
public import RequestProject.ThreeIM.ClusterRadius

/-!
# The actual analytic control in finite-disk Step 1

A control circle is constructed from the genuine joint divisor support.
All its estimates are derived from the original coefficient budget M.
The resulting H'_Phi bound holds throughout the inner disk, including
original divisor points. No synthetic control-circle input is assumed.
-/

@[expose] public section

set_option autoImplicit false

open Set Metric Real
open scoped BigOperators

namespace ThreeIM

/-- Analytic Step 1 for the actual coupled divisor extractions at the
fixed radius r+7Delta/8. Existence of these extractions is separately
proved by `exists_divisorFactorData`. -/
theorem finite_disk_factor_control {Φ A Ψ : ℂ → ℂ} {r R Δ : ℝ}
    (D : DivisorFactorData Φ (r + 7 * Δ / 8))
    (E : DivisorFactorData A (r + 7 * Δ / 8))
    (P : DivisorFactorData Ψ (r + 7 * Δ / 8))
    (hΦ : MeromorphicOn Φ univ) (hA : MeromorphicOn A univ) (hΨ : MeromorphicOn Ψ univ)
    (hlog : A = logDeriv Φ) (hr : 1 ≤ r) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hR : R = r + Δ) :
    let B := finiteDiskBudget R Δ (finiteDiskCoefficientMass Φ A Ψ R)
    (∀ z ∈ closedBall (0 : ℂ) (r + Δ / 4), ‖deriv D.H z‖ ≤ Real.exp B) ∧
      (∀ z ∈ closedBall (0 : ℂ) (r + Δ / 2),
        |(E.H z).re| + |(P.H z).re| ≤ B / 1000 ∧
          ‖deriv E.H z‖ + ‖deriv P.H z‖ ≤ B / 2) := by
  let ρ := r + 7 * Δ / 8
  let M := finiteDiskCoefficientMass Φ A Ψ R
  let B := finiteDiskBudget R Δ M
  let N := jointDivisorMass D E P
  let S := jointDivisorSupport D E P
  let δ := Δ / (100 * (N + 1))
  let C := Real.log (3 * R / δ)
  have hR1 : 1 ≤ R := by linarith
  have hρ : 1 ≤ ρ := by dsimp [ρ]; linarith
  have hwindow : ρ ≤ R - Δ / 8 := by dsimp [ρ]; linarith
  have hM : 1 ≤ M := finiteDiskCoefficientMass_ge_one Φ A Ψ hR1
  have hcard : (S.card : ℝ) ≤ N := jointDivisorSupport_card_le_mass D E P
  have hN : 0 ≤ N := (show 0 ≤ (S.card : ℝ) by positivity).trans hcard
  have hmass := jointDivisorMass_le_window D E P hΦ hA hΨ hρ hΔ hwindow
  have hNbound : N ≤ 8 * R * M * Δ⁻¹ := by
    have houter : ValueDistribution.characteristic A ⊤ R + ValueDistribution.characteristic A⁻¹ ⊤ R +
        ValueDistribution.characteristic Ψ ⊤ R + ValueDistribution.characteristic Ψ⁻¹ ⊤ R +
        ValueDistribution.logCounting Φ ⊤ R + ValueDistribution.logCounting Φ⁻¹ ⊤ R ≤ M := by
      dsimp [M, finiteDiskCoefficientMass]
      linarith
    exact hmass.trans ((mul_le_mul_of_nonneg_left houter (show 0 ≤ 8 * R / Δ by positivity)).trans_eq (by ring))
  obtain ⟨hδ, hδ1, hC, hbandlo, hbandhi, _, _, hfinal⟩ :=
    controlCircle_parameters hR1 hΔ hΔ1 hM hN hNbound
  have hδcard : δ ≤ Δ / (100 * ((S.card : ℝ) + 1)) := by
    exact div_le_div_of_nonneg_left hΔ.le (by positivity) (by linarith)
  obtain ⟨σ, hσrange, hσ, hsep⟩ := exists_divisor_separated_circle S (by linarith : 0 ≤ r) hΔ
  have hσρ : σ < ρ := by dsimp [ρ]; linarith [hσrange.2]
  have hσR : σ ≤ R := by linarith [hσrange.2]
  have hρR : ρ ≤ R := by linarith
  have hDdegree : (∑ α ∈ D.support, |(D.exponent α : ℝ)|) ≤ N := by
    dsimp [N]
    rw [jointDivisorMass_eq_sum_degrees]
    have hE0 : 0 ≤ ∑ α ∈ E.support, |(E.exponent α : ℝ)| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    have hP0 : 0 ≤ ∑ α ∈ P.support, |(P.exponent α : ℝ)| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    linarith
  have hEdegree : (∑ α ∈ E.support, |(E.exponent α : ℝ)|) ≤ N := by
    dsimp [N]
    rw [jointDivisorMass_eq_sum_degrees]
    have hD0 : 0 ≤ ∑ α ∈ D.support, |(D.exponent α : ℝ)| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    have hP0 : 0 ≤ ∑ α ∈ P.support, |(P.exponent α : ℝ)| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    linarith
  have hDS : D.support ⊆ S := fun _ hα => Finset.mem_union_left _ (Finset.mem_union_left _ hα)
  have hES : E.support ⊆ S := fun _ hα => Finset.mem_union_left _ (Finset.mem_union_right _ hα)
  have hsepD : ∀ w ∈ sphere (0 : ℂ) σ, ∀ α ∈ D.support, δ ≤ ‖w - α‖ :=
    fun w hw α hα => hδcard.trans (hsep w hw α (hDS hα))
  have hbandE : ∀ w ∈ sphere (0 : ℂ) σ, ∀ α ∈ E.support,
      Real.exp (-C) ≤ ‖w - α‖ ∧ ‖w - α‖ ≤ Real.exp C := by
    intro w hw α hα
    refine ⟨hbandlo.trans (hδcard.trans (hsep w hw α (hES hα))), ?_⟩
    have hnw : ‖w‖ = σ := by simpa only [mem_sphere, dist_zero_right] using hw
    calc
      ‖w - α‖ ≤ ‖w‖ + ‖α‖ := norm_sub_le _ _
      _ ≤ 2 * R := by have ha := E.roots α hα; change ‖α‖ ≤ ρ at ha; linarith
      _ ≤ Real.exp C := hbandhi
  have hre : ∀ w ∈ sphere (0 : ℂ) σ, (E.H w).re ≤ B / 1000 := by
    intro w hw
    have hnw : ‖w‖ = σ := by simpa only [mem_sphere, dist_zero_right] using hw
    have hinner : ‖w‖ ≤ ρ - Δ / 8 := by dsimp [ρ]; linarith [hσrange.2]
    have hp := factor_pair_abs_re_le_budget D E P hΦ hA hΨ hR1 hρ hΔ hΔ1 hwindow hinner
    change |(E.H w).re| + |(P.H w).re| ≤ B / 1000 at hp
    linarith [le_abs_self (E.H w).re, abs_nonneg (P.H w).re]
  have hmaximum := norm_deriv_H_le_of_control_circle D E hlog hσ hσρ hδ hC
    hDdegree hEdegree hsepD hbandE hre
  refine ⟨?_, ?_⟩
  · intro z hz
    exact (hmaximum z (closedBall_subset_closedBall hσrange.1 hz)).trans hfinal
  · intro z hz
    have hnorm : ‖z‖ ≤ r + Δ / 2 := by simpa only [mem_closedBall, dist_zero_right] using hz
    exact ⟨factor_pair_abs_re_le_budget D E P hΦ hA hΨ hR1 hρ hΔ hΔ1 hwindow
        (by linarith),
      factor_pair_norm_deriv_le_budget D E P hΦ hA hΨ hR1 hρ hΔ hΔ1 hwindow
        (by linarith)⟩

/-- The coupled extractions and all Step 1 analytic estimates are
constructed from the actual meromorphic functions and their nonzero
germs. No factorization or control-circle data are assumed as input. -/
theorem exists_finite_disk_factor_control {Φ A Ψ : ℂ → ℂ} {r R Δ : ℝ}
    (hΦ : MeromorphicOn Φ univ) (hA : MeromorphicOn A univ) (hΨ : MeromorphicOn Ψ univ)
    (hΦfinite : ∀ z, meromorphicOrderAt Φ z ≠ ⊤)
    (hAfinite : ∀ z, meromorphicOrderAt A z ≠ ⊤)
    (hΨfinite : ∀ z, meromorphicOrderAt Ψ z ≠ ⊤)
    (hlog : A = logDeriv Φ) (hr : 1 ≤ r) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hR : R = r + Δ) :
    let B := finiteDiskBudget R Δ (finiteDiskCoefficientMass Φ A Ψ R)
    ∃ (D : DivisorFactorData Φ (r + 7 * Δ / 8))
      (E : DivisorFactorData A (r + 7 * Δ / 8)) (P : DivisorFactorData Ψ (r + 7 * Δ / 8)),
      (∀ z ∈ closedBall (0 : ℂ) (r + Δ / 4), ‖deriv D.H z‖ ≤ Real.exp B) ∧
        (∀ z ∈ closedBall (0 : ℂ) (r + Δ / 2),
          |(E.H z).re| + |(P.H z).re| ≤ B / 1000 ∧
            ‖deriv E.H z‖ + ‖deriv P.H z‖ ≤ B / 2) := by
  have hρ : 0 < r + 7 * Δ / 8 := by linarith
  obtain ⟨D⟩ := exists_divisorFactorData hρ
    (fun z _ => hΦ z (mem_univ z)) (fun z _ => hΦfinite z)
  obtain ⟨E⟩ := exists_divisorFactorData hρ
    (fun z _ => hA z (mem_univ z)) (fun z _ => hAfinite z)
  obtain ⟨P⟩ := exists_divisorFactorData hρ
    (fun z _ => hΨ z (mem_univ z)) (fun z _ => hΨfinite z)
  exact ⟨D, E, P, finite_disk_factor_control D E P hΦ hA hΨ hlog hr hΔ hΔ1 hR⟩

end ThreeIM
