module

public import RequestProject.ThreeIM.JensenZeroCount
public import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A q-independent cluster count from a Wronskian lower bound

For an analytic numerator N and pole denominator Q, the cleared fiber is
N-qQ. Its Wronskian with Q is independent of q. Cauchy's estimate turns a
positive Wronskian bound at a regular probe into a lower bound for the maximum
of N-qQ, uniformly in q. Jensen then counts its zeros on the cluster disk.
The divisor factors and the probe construction still have to supply the
quantitative inputs in the manuscript. No global absence of poles is assumed.
-/

@[expose] public section

open Filter Set Metric
open scoped Topology

namespace ThreeIM

/-- Clearing a finite fiber at an actual regular germ. A merely punctured
equality would not justify the center value when the raw function has junk. -/
theorem cleared_fiber_eq_zero_iff {Φ N Q : ℂ → ℂ} {z q : ℂ}
    (hQ : Q z ≠ 0) (hrep : Φ =ᶠ[𝓝 z] (fun w => N w / Q w)) :
    N z - q * Q z = 0 ↔ Φ z = q := by
  rw [hrep.self_of_nhds, div_eq_iff hQ, sub_eq_zero]

/-- The exact derivative identity behind the cleared-fiber Wronskian.
Its representative equality is an ordinary germ equality at a regular point. -/
theorem cleared_fiber_wronskian_of_germ {Φ N Q : ℂ → ℂ} {z : ℂ}
    (hN : DifferentiableAt ℂ N z) (hQ : DifferentiableAt ℂ Q z) (hQ0 : Q z ≠ 0)
    (hrep : Φ =ᶠ[𝓝 z] (fun w => N w / Q w)) :
    deriv N z * Q z - N z * deriv Q z = deriv Φ z * Q z ^ 2 := by
  have hd : deriv Φ z = (deriv N z * Q z - N z * deriv Q z) / Q z ^ 2 :=
    hrep.deriv_eq.trans (hN.hasDerivAt.div hQ.hasDerivAt hQ0).deriv
  rw [hd, div_mul_cancel₀ _ (pow_ne_zero 2 hQ0)]

/-- Cauchy's estimate on the half-radius probe disk bounds a Wronskian by
the suprema of its two functions on the cluster disk. -/
theorem norm_wronskian_le_of_closed_disk_bounds {F Q : ℂ → ℂ} {c v : ℂ}
    {ρ S D : ℝ} (hρ : 0 < ρ) (hv : v ∈ closedBall c (ρ / 2))
    (hF : AnalyticOnNhd ℂ F (closedBall c ρ))
    (hQ : AnalyticOnNhd ℂ Q (closedBall c ρ))
    (hFS : ∀ w ∈ closedBall c ρ, ‖F w‖ ≤ S)
    (hQD : ∀ w ∈ closedBall c ρ, ‖Q w‖ ≤ D) :
    ‖deriv F v * Q v - F v * deriv Q v‖ ≤ 4 * S * D / ρ := by
  have hhalf : 0 < ρ / 2 := half_pos hρ
  have hvρ : v ∈ closedBall c ρ :=
    closedBall_subset_closedBall (by linarith) hv
  have hsub : closedBall v (ρ / 2) ⊆ closedBall c ρ :=
    closedBall_subset_closedBall' (by have := mem_closedBall.mp hv; linarith)
  have hdF := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hhalf
    (hF.differentiableOn.diffContOnCl_ball hsub)
    (fun w hw => hFS w (hsub (sphere_subset_closedBall hw)))
  have hdQ := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hhalf
    (hQ.differentiableOn.diffContOnCl_ball hsub)
    (fun w hw => hQD w (hsub (sphere_subset_closedBall hw)))
  have hS0 : 0 ≤ S := (norm_nonneg (F v)).trans (hFS v hvρ)
  have hD0 : 0 ≤ D := (norm_nonneg (Q v)).trans (hQD v hvρ)
  calc
    ‖deriv F v * Q v - F v * deriv Q v‖ ≤
        ‖deriv F v * Q v‖ + ‖F v * deriv Q v‖ := norm_sub_le _ _
    _ = ‖deriv F v‖ * ‖Q v‖ + ‖F v‖ * ‖deriv Q v‖ := by rw [norm_mul, norm_mul]
    _ ≤ (S / (ρ / 2)) * D + S * (D / (ρ / 2)) := by
      exact add_le_add
        (mul_le_mul hdF (hQD v hvρ) (norm_nonneg _) (div_nonneg hS0 hhalf.le))
        (mul_le_mul (hFS v hvρ) hdQ (norm_nonneg _) hS0)
    _ = 4 * S * D / ρ := by
      field_simp [ne_of_gt hρ]
      ring

/-- A quantitative cluster count uniform over every complex fiber q.

The numerator N and denominator Q are analytic on the five-times enlarged
cluster disk. The positive Wronskian and denominator lower bounds are required
only at one regular probe in its inner half disk. They are the later outputs
of the divisor-factor estimates; the theorem derives the zero count itself. -/
theorem cleared_fiber_card_mul_log_two_le (s : Finset ℂ) {N Q : ℂ → ℂ}
    {q c v : ℂ} {ρ E P D K a : ℝ}
    (hρ : 0 < ρ) (hE : 0 < E) (hK : 0 < K) (ha : 0 < a)
    (hP : 0 ≤ P) (hD : 0 ≤ D)
    (hv : v ∈ closedBall c (ρ / 2))
    (hN : AnalyticOnNhd ℂ N (closedBall c (5 * ρ)))
    (hQ : AnalyticOnNhd ℂ Q (closedBall c (5 * ρ)))
    (hNP : ∀ w ∈ closedBall c (5 * ρ), ‖N w‖ ≤ E * P)
    (hQD : ∀ w ∈ closedBall c (5 * ρ), ‖Q w‖ ≤ D)
    (hQa : a ≤ ‖Q v‖)
    (hW : E * K ≤ ‖deriv N v * Q v - N v * deriv Q v‖)
    (hzeros : ∀ z ∈ s, z ∈ closedBall c ρ ∧ N z = q * Q z) :
    (s.card : ℝ) * Real.log 2 ≤
      Real.log (max 1 ((4 * D / (ρ * K)) * P +
        (1 + (4 * D / (ρ * K)) * P) * D / a)) := by
  let F : ℂ → ℂ := fun w => N w - q * Q w
  let C₀ : ℝ := 4 * D / (ρ * K)
  let C : ℝ := C₀ * P + (1 + C₀ * P) * D / a
  have hsmall : closedBall c ρ ⊆ closedBall c (5 * ρ) :=
    closedBall_subset_closedBall (by linarith)
  have hF : AnalyticOnNhd ℂ F (closedBall c (5 * ρ)) := by
    intro w hw
    exact (hN w hw).sub (analyticAt_const.mul (hQ w hw))
  obtain ⟨u, hu, hmax⟩ := (isCompact_closedBall c ρ).exists_isMaxOn
    (nonempty_closedBall.mpr hρ.le) (hF.mono hsmall).continuousOn.norm
  let S : ℝ := ‖F u‖
  have hFS : ∀ w ∈ closedBall c ρ, ‖F w‖ ≤ S := isMaxOn_iff.mp hmax
  have hvsmall : v ∈ closedBall c ρ :=
    closedBall_subset_closedBall (by linarith) hv
  have hvbig := hsmall hvsmall
  have hderF : deriv F v = deriv N v - q * deriv Q v :=
    ((hN v hvbig).differentiableAt.hasDerivAt.sub
      ((hQ v hvbig).differentiableAt.hasDerivAt.const_mul q)).deriv
  have hcancel : deriv F v * Q v - F v * deriv Q v =
      deriv N v * Q v - N v * deriv Q v := by
    rw [hderF]
    dsimp [F]
    ring
  have hWbound : E * K ≤ 4 * S * D / ρ := by
    apply hW.trans
    rw [← hcancel]
    exact norm_wronskian_le_of_closed_disk_bounds hρ hv (hF.mono hsmall) (hQ.mono hsmall)
      hFS (fun w hw => hQD w (hsmall hw))
  have hS : 0 < S := by
    by_contra hnot
    have hz : S = 0 := le_antisymm (le_of_not_gt hnot) (norm_nonneg (F u))
    rw [hz] at hWbound
    simp only [mul_zero, zero_mul, zero_div] at hWbound
    exact (not_le_of_gt (mul_pos hE hK)) hWbound
  have hEbound : E ≤ S * C₀ := by
    have heq : S * C₀ = 4 * S * D / (ρ * K) := by dsimp [C₀]; ring
    rw [heq]
    apply (le_div_iff₀ (mul_pos hρ hK)).2
    have hm := (le_div_iff₀ hρ).mp hWbound
    nlinarith
  have hqraw : ‖q‖ * a ≤ E * P + S := by
    calc
      ‖q‖ * a ≤ ‖q‖ * ‖Q v‖ := mul_le_mul_of_nonneg_left hQa (norm_nonneg q)
      _ = ‖q * Q v‖ := (norm_mul q (Q v)).symm
      _ = ‖N v - F v‖ := by congr 1; dsimp [F]; ring
      _ ≤ ‖N v‖ + ‖F v‖ := norm_sub_le _ _
      _ ≤ E * P + S := add_le_add (hNP v hvbig) (hFS v hvsmall)
  have hq : ‖q‖ ≤ S * (1 + C₀ * P) / a := by
    apply (le_div_iff₀ ha).2
    calc
      ‖q‖ * a ≤ E * P + S := hqraw
      _ ≤ (S * C₀) * P + S := add_le_add (mul_le_mul_of_nonneg_right hEbound hP) le_rfl
      _ = S * (1 + C₀ * P) := by ring
  have hFbig : ∀ w ∈ closedBall c (5 * ρ), ‖F w‖ ≤ S * C := by
    intro w hw
    calc
      ‖F w‖ ≤ ‖N w‖ + ‖q * Q w‖ := norm_sub_le _ _
      _ = ‖N w‖ + ‖q‖ * ‖Q w‖ := by rw [norm_mul]
      _ ≤ E * P + ‖q‖ * D :=
        add_le_add (hNP w hw) (mul_le_mul_of_nonneg_left (hQD w hw) (norm_nonneg q))
      _ ≤ (S * C₀) * P + (S * (1 + C₀ * P) / a) * D :=
        add_le_add (mul_le_mul_of_nonneg_right hEbound hP) (mul_le_mul_of_nonneg_right hq hD)
      _ = S * C := by dsimp [C]; ring
  have hFu : F u ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hS)
  have husub : closedBall u (4 * ρ) ⊆ closedBall c (5 * ρ) :=
    closedBall_subset_closedBall' (by have := mem_closedBall.mp hu; linarith)
  let g : ℂ → ℂ := fun w => F w / F u
  have hg : AnalyticOnNhd ℂ g (closedBall u (4 * ρ)) := by
    intro w hw
    exact (hF w (husub hw)).div analyticAt_const hFu
  have hgu : g u = 1 := div_self hFu
  have hmaxpos : 0 < max (1 : ℝ) C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hgnorm : ∀ w ∈ sphere u (4 * ρ), ‖g w‖ ≤ Real.exp (Real.log (max 1 C)) := by
    intro w hw
    calc
      ‖g w‖ = ‖F w‖ / S := norm_div _ _
      _ ≤ (S * C) / S := div_le_div_of_nonneg_right
        (hFbig w (husub (sphere_subset_closedBall hw))) hS.le
      _ = C := mul_div_cancel_left₀ C (ne_of_gt hS)
      _ ≤ max 1 C := le_max_right _ _
      _ = Real.exp (Real.log (max 1 C)) := (Real.exp_log hmaxpos).symm
  have hgzeros : ∀ z ∈ s, z ∈ closedBall u (2 * ρ) ∧ g z = 0 := by
    intro z hz
    constructor
    · apply mem_closedBall.mpr
      have hzu := dist_triangle z c u
      have hzc := mem_closedBall.mp (hzeros z hz).1
      have huc := mem_closedBall.mp hu
      rw [dist_comm c u] at hzu
      linarith
    · change (N z - q * Q z) / F u = 0
      rw [(hzeros z hz).2, sub_self, zero_div]
  have hj := finite_zero_card_mul_log_le s (by positivity : 0 < 2 * ρ)
    (by linarith : 2 * ρ < 4 * ρ) (Real.log_nonneg (le_max_left 1 C))
    hg hgu hgnorm hgzeros
  have hratio : (4 * ρ) / (2 * ρ) = (2 : ℝ) :=
    (div_eq_iff (mul_ne_zero (by norm_num) (ne_of_gt hρ))).2 (by ring)
  simpa only [hratio] using hj

end ThreeIM
