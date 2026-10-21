module

public import RequestProject.ThreeIM.BranchLocalLog
public import RequestProject.ThreeIM.InverseBranch
public import RequestProject.ThreeIM.InverseBranchControl
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The inverse sheet at a good point

This is step 4 of the manuscript's finite-disk branch lemma. The hypotheses
are estimates on actual zero-free holomorphic representatives on the regular
physical disk. The logarithms, inverse map, square-root branch, and coefficient
control are constructed from them. Counting the exceptional points needed to
find such disks remains a separate step.
-/

@[expose] public section

open Filter Set Metric Topology

namespace ThreeIM

/-- The local data constructed at a good point of the finite-disk lemma.
The square-root value at the center is prescribed to permit the later marked
fiber to fix its sign. -/
structure GoodPointBranch (Φ A Ψ : ℂ → ℂ) (z v : ℂ) (B d : ℝ) where
  gamma : ℂ → ℂ
  sigma : ℂ → ℂ
  k : ℂ → ℂ
  normalizedLog : ℂ → ℂ
  gamma_zero : gamma 0 = z
  gamma_maps : MapsTo gamma (ball 0 (B ^ 6 / 2)) (ball z (d / B ^ 4))
  gamma_analytic : AnalyticOnNhd ℂ gamma (ball 0 (B ^ 6 / 2))
  gamma_inj : InjOn gamma (ball 0 (B ^ 6 / 2))
  gamma_exp : ∀ s ∈ ball 0 (B ^ 6 / 2), Φ (gamma s) = Φ z * Complex.exp s
  gamma_deriv : ∀ s ∈ ball 0 (B ^ 6 / 2), deriv gamma s = (A (gamma s))⁻¹
  gamma_deriv_ne_zero : ∀ s ∈ ball 0 (B ^ 6 / 2), deriv gamma s ≠ 0
  sigma_holo : DifferentiableOn ℂ sigma (ball z (d / B ^ 4))
  sigma_center : sigma z = v
  sigma_ne_zero : ∀ w ∈ ball z (d / B ^ 4), sigma w ≠ 0
  sigma_sq : ∀ w ∈ ball z (d / B ^ 4), sigma w ^ 2 = Ψ w
  k_holo : DifferentiableOn ℂ k (ball 0 (B ^ 6 / 2))
  k_ne_zero : ∀ s ∈ ball 0 (B ^ 6 / 2), k s ≠ 0
  k_eq : ∀ s ∈ ball 0 (B ^ 6 / 2), k s = A (gamma s) / sigma (gamma s)
  control_center : |Real.log ‖k 0‖| ≤ 9 * B ^ 2
  log_holo : DifferentiableOn ℂ normalizedLog (ball 0 (B ^ 6 / 2))
  log_zero : normalizedLog 0 = 0
  log_exp : ∀ s ∈ ball 0 (B ^ 6 / 2), Complex.exp (normalizedLog s) = k s / k 0
  log_bound : ∀ s ∈ ball 0 (B ^ 6 / 2), ‖normalizedLog s‖ ≤ 12 * B⁻¹ ^ 3

/-- The source's good-point and regular-disk estimates produce the full
quantitative inverse sheet and coefficient control. -/
theorem exists_good_point_branch {Φ A Ψ : ℂ → ℂ} {z v : ℂ} {B d : ℝ}
    (hB : 4 ≤ B) (hd : 0 < d)
    (hΦ : DifferentiableOn ℂ Φ (ball z (d / B ^ 4)))
    (hΦ0 : ∀ w ∈ ball z (d / B ^ 4), Φ w ≠ 0)
    (hA : DifferentiableOn ℂ A (ball z (d / B ^ 4)))
    (hA0 : ∀ w ∈ ball z (d / B ^ 4), A w ≠ 0)
    (hΨ : DifferentiableOn ℂ Ψ (ball z (d / B ^ 4)))
    (hΨ0 : ∀ w ∈ ball z (d / B ^ 4), Ψ w ≠ 0)
    (hΦderiv : ∀ w ∈ ball z (d / B ^ 4), deriv Φ w / Φ w = A w)
    (hlogderiv : ∀ w ∈ ball z (d / B ^ 4),
      ‖deriv A w / A w‖ + ‖deriv Ψ w / Ψ w‖ ≤ 8 * B / d)
    (hgood : B ^ 10 / d < ‖A z‖)
    (hcenterA : |Real.log ‖A z‖| ≤ 6 * B ^ 2)
    (hcenterΨ : |Real.log ‖Ψ z‖| ≤ 6 * B ^ 2)
    (hv : v ^ 2 = Ψ z) : Nonempty (GoodPointBranch Φ A Ψ z v B d) := by
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hρ : 0 < d / B ^ 4 := div_pos hd (pow_pos hBpos _)
  have hz : z ∈ ball z (d / B ^ 4) := mem_ball_self hρ
  have hAz : A z ≠ 0 := hA0 z hz
  have hv0 : v ≠ 0 := by
    intro hzero
    have h := hv
    rw [hzero, zero_pow (by norm_num)] at h
    exact hΨ0 z hz h.symm
  have hlogA : ∀ w ∈ ball z (d / B ^ 4), ‖deriv A w / A w‖ ≤ 8 * B / d := by
    intro w hw
    exact (le_add_of_nonneg_right (norm_nonneg _)).trans (hlogderiv w hw)
  have hlogΨ : ∀ w ∈ ball z (d / B ^ 4), ‖deriv Ψ w / Ψ w‖ ≤ 8 * B / d := by
    intro w hw
    exact (le_add_of_nonneg_left (norm_nonneg _)).trans (hlogderiv w hw)
  obtain ⟨LA, hLA, hLAz, hLAdata⟩ := normalized_log_on_good_disk hBpos hd hA hA0 hlogA
  obtain ⟨LP, hLP, hLPz, hLPdata⟩ := normalized_log_on_good_disk hBpos hd hΨ hΨ0 hlogΨ
  have heA : ∀ w ∈ ball z (d / B ^ 4), A w = A z * Complex.exp (LA w) := by
    intro w hw
    simpa only [mul_comm] using ((eq_div_iff hAz).mp (hLAdata w hw).1).symm
  have heP : ∀ w ∈ ball z (d / B ^ 4), Ψ w = Ψ z * Complex.exp (LP w) := by
    intro w hw
    simpa only [mul_comm] using ((eq_div_iff (hΨ0 z hz)).mp (hLPdata w hw).1).symm
  obtain ⟨W, hW, hWz, hWdata⟩ := exists_normalized_log_on_ball_with_deriv hρ hΦ hΦ0
  have hWd : ∀ w ∈ ball z (d / B ^ 4), deriv W w = A w := by
    intro w hw
    exact (hWdata w hw).2.trans (hΦderiv w hw)
  have hclose : ∀ w ∈ ball z (d / B ^ 4), ‖deriv W w - A z‖ ≤ ‖A z‖ / 4 := by
    intro w hw
    apply deriv_close_of_exp_log ((hLAdata w hw).2.2.trans (eight_inv_cube_le_one_eighth hB))
    rw [hWd w hw, heA w hw]
  have heΦ : ∀ w ∈ ball z (d / B ^ 4), Φ w = Φ z * Complex.exp (W w - W z) := by
    intro w hw
    rw [hWz, sub_zero]
    simpa only [mul_comm] using ((eq_div_iff (hΦ0 z hz)).mp (hWdata w hw).1).symm
  obtain ⟨γ, hγ0, hγmap, hγan, hγinj, hγ⟩ :=
    exponential_inverse_branch hρ hAz hW hclose heΦ
  have hpower : (B ^ 10 / d) * (d / B ^ 4) = B ^ 6 := by
    field_simp [ne_of_gt hBpos, ne_of_gt hd]
  have hscale : B ^ 6 < ‖A z‖ * (d / B ^ 4) := by
    rw [← hpower]
    exact mul_lt_mul_of_pos_right hgood hρ
  have htarget : B ^ 6 / 2 ≤ 3 * ‖A z‖ * (d / B ^ 4) / 4 := by
    have hB6 : 0 < B ^ 6 := pow_pos hBpos _
    nlinarith
  have hsub : ball (0 : ℂ) (B ^ 6 / 2) ⊆
      ball 0 (3 * ‖A z‖ * (d / B ^ 4) / 4) := ball_subset_ball htarget
  have hγmaps : MapsTo γ (ball 0 (B ^ 6 / 2)) (ball z (d / B ^ 4)) :=
    hγmap.mono_left hsub
  have hγans : AnalyticOnNhd ℂ γ (ball 0 (B ^ 6 / 2)) := hγan.mono hsub
  obtain ⟨σ, K, L, hσ, hK, hL, hσz, hKz, hLz, hdata⟩ :=
    quotient_sqrt_log_control hA hLA hLP hAz hv0 hv hLAz hLPz heA heP
      (fun w hw => (hLAdata w hw).2.2) (fun w hw => (hLPdata w hw).2.2)
  let k : ℂ → ℂ := fun s => K (γ s)
  let ℓ : ℂ → ℂ := fun s => L (γ s)
  have hk0 : k 0 = K z := by
    change K (γ 0) = K z
    rw [hγ0]
  refine ⟨{
    gamma := γ
    sigma := σ
    k := k
    normalizedLog := ℓ
    gamma_zero := hγ0
    gamma_maps := hγmaps
    gamma_analytic := hγans
    gamma_inj := hγinj.mono hsub
    gamma_exp := fun s hs => (hγ s (hsub hs)).1
    gamma_deriv := ?_
    gamma_deriv_ne_zero := fun s hs => (hγ s (hsub hs)).2.2
    sigma_holo := hσ
    sigma_center := hσz
    sigma_ne_zero := fun w hw => (hdata w hw).1
    sigma_sq := fun w hw => (hdata w hw).2.2.1
    k_holo := hK.comp hγans.differentiableOn hγmaps
    k_ne_zero := fun s hs => (hdata (γ s) (hγmaps hs)).2.1
    k_eq := fun s hs => (hdata (γ s) (hγmaps hs)).2.2.2.1
    control_center := ?_
    log_holo := hL.comp hγans.differentiableOn hγmaps
    log_zero := ?_
    log_exp := ?_
    log_bound := ?_
  }⟩
  · intro s hs
    rw [(hγ s (hsub hs)).2.1, hWd (γ s) (hγmaps hs)]
  · rw [hk0, hKz]
    exact log_norm_quotient_sqrt_bound hAz hv0 hv hcenterA hcenterΨ
  · change L (γ 0) = 0
    rw [hγ0, hLz]
  · intro s hs
    change Complex.exp (L (γ s)) = K (γ s) / k 0
    rw [hk0]
    exact (hdata (γ s) (hγmaps hs)).2.2.2.2.1
  · intro s hs
    change ‖L (γ s)‖ ≤ 12 * B⁻¹ ^ 3
    calc
      ‖L (γ s)‖ ≤ 8 * B⁻¹ ^ 3 + 8 * B⁻¹ ^ 3 / 2 :=
        (hdata (γ s) (hγmaps hs)).2.2.2.2.2
      _ = 12 * B⁻¹ ^ 3 := by ring

end ThreeIM
