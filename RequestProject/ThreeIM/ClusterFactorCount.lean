module

public import RequestProject.ThreeIM.ClusterFactorBounds
public import RequestProject.ThreeIM.ClusterGerms
public import RequestProject.ThreeIM.ClusterBudget
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The eta-disk count from actual divisor factors

The probe, all exponential estimates, and the q-independent Jensen count are
constructed from factor data of the kind furnished by step 1 of the finite-disk
lemma. The logarithmic derivative is that of the actual analytic quotient.
The input fiber is the analytic cleared equation; `ClusterGerms` recovers this
equation from genuine finite meromorphic germs without reading junk values.
Deriving the factor data from the characteristic budget remains separate.
-/

@[expose] public section

open Set Metric
open scoped BigOperators

namespace ThreeIM

/-- The polynomial part of a finite divisor with natural multiplicities. -/
noncomputable def divisorPowerProduct (σ : Finset ℂ) (m : ℂ → ℕ) (z : ℂ) : ℂ :=
  ∏ α ∈ σ, (z - α) ^ m α

/-- The analytic numerator after clearing the poles of exp(H) P/Q. -/
noncomputable def clearedDivisorNumerator (σ : Finset ℂ) (m : ℂ → ℕ)
    (H : ℂ → ℂ) (z : ℂ) : ℂ :=
  Complex.exp (H z) * divisorPowerProduct σ m z

/-- The factor data on an enlarged original eta-disk yield the full
`250 B^2` count, without supplying a probe, exponential factor estimates,
Wronskian bound, or a zero-count hypothesis. -/
theorem factorized_eta_disk_card_le (s σ : Finset ℂ) {m n : ℂ → ℕ} {d : ℂ → ℤ}
    {H h : ℂ → ℂ} {ζ c : ℂ} {B : ℝ}
    (hB : 4 ≤ B) (hcard : (σ.card : ℝ) ≤ B)
    (hc : ‖c‖ + 5 * Real.exp (-4 * B) ≤ B)
    (hroots : ∀ α ∈ σ, ‖α‖ ≤ B)
    (hm : (∑ α ∈ σ, (m α : ℝ)) ≤ B)
    (hn : (∑ α ∈ σ, (n α : ℝ)) ≤ B)
    (hd : (∑ α ∈ σ, |(d α : ℝ)|) ≤ B)
    (hH : AnalyticOnNhd ℂ H (closedBall c (5 * Real.exp (-4 * B))))
    (hHderiv : ∀ w ∈ closedBall c (5 * Real.exp (-4 * B)), ‖deriv H w‖ ≤ Real.exp B)
    (hhre : ∀ w ∈ closedBall c (5 * Real.exp (-4 * B)), -B / 1000 ≤ (h w).re)
    (hlog : ∀ w ∈ closedBall c (5 * Real.exp (-4 * B)),
      (∀ α ∈ σ, w ≠ α) →
      deriv (fun u => clearedDivisorNumerator σ m H u / divisorPowerProduct σ n u) w /
        (clearedDivisorNumerator σ m H w / divisorPowerProduct σ n w) =
          Complex.exp (h w) * ∏ α ∈ σ, (w - α) ^ d α)
    (hfiber : ∀ z ∈ s, z ∈ closedBall c (Real.exp (-4 * B)) ∧
      clearedDivisorNumerator σ m H z = ζ * divisorPowerProduct σ n z) :
    (s.card : ℝ) ≤ 250 * B ^ 2 := by
  let P : ℂ → ℂ := divisorPowerProduct σ m
  let Q : ℂ → ℂ := divisorPowerProduct σ n
  let N : ℂ → ℂ := clearedDivisorNumerator σ m H
  let E : ℝ := Real.exp (H c).re
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hB2 : 16 ≤ B ^ 2 := by nlinarith [sq_nonneg (B - 4)]
  have hPanalytic : ∀ w, AnalyticAt ℂ P w := by
    intro w
    apply σ.analyticAt_fun_prod
    intro α hα
    exact (analyticAt_id.sub analyticAt_const).pow (m α)
  have hQanalytic : ∀ w, AnalyticAt ℂ Q w := by
    intro w
    apply σ.analyticAt_fun_prod
    intro α hα
    exact (analyticAt_id.sub analyticAt_const).pow (n α)
  have hNanalytic : AnalyticOnNhd ℂ N (closedBall c (5 * Real.exp (-4 * B))) := by
    intro w hw
    exact (hH w hw).cexp'.mul (hPanalytic w)
  have hupper := norm_sub_le_exp_on_eta_disk σ hB hc hroots
  have hnatupper (k : ℂ → ℕ) (hk : (∑ α ∈ σ, (k α : ℝ)) ≤ B)
      (w : ℂ) (hw : w ∈ closedBall c (5 * Real.exp (-4 * B))) :
      ‖divisorPowerProduct σ k w‖ ≤ Real.exp (3 * B ^ 2) := by
    have hb := norm_prod_pow_le_exp σ (f := fun α => w - α) (m := k)
      (C := 3 * B) (M := B) (by positivity) (hupper w hw) hk
    have he : (3 * B) * B = 3 * B ^ 2 := by ring
    simpa only [he, divisorPowerProduct] using hb
  have hHvar := norm_sub_le_one_on_eta_disk hB hH hHderiv
  have hRe : ∀ w ∈ closedBall c (5 * Real.exp (-4 * B)),
      (H c).re - 1 ≤ (H w).re ∧ (H w).re ≤ (H c).re + 1 := by
    intro w hw
    have ha := (Complex.abs_re_le_norm (H w - H c)).trans (hHvar w hw)
    rw [Complex.sub_re] at ha
    have hab := abs_le.mp ha
    constructor <;> linarith
  have hNP : ∀ w ∈ closedBall c (5 * Real.exp (-4 * B)), ‖N w‖ ≤ E * Real.exp (4 * B ^ 2) := by
    intro w hw
    change ‖Complex.exp (H w) * P w‖ ≤ _
    rw [norm_mul, Complex.norm_exp]
    calc
      Real.exp (H w).re * ‖P w‖ ≤ Real.exp ((H c).re + 1) * Real.exp (3 * B ^ 2) :=
        mul_le_mul (Real.exp_le_exp.mpr (hRe w hw).2) (hnatupper m hm w hw)
          (norm_nonneg _) (Real.exp_pos _).le
      _ = E * Real.exp (1 + 3 * B ^ 2) := by
        dsimp [E]
        rw [Real.exp_add, Real.exp_add]
        ring
      _ ≤ E * Real.exp (4 * B ^ 2) := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le
  obtain ⟨v, hv, hprobe⟩ := exists_eta_probe_with_factor_bounds σ hB hcard hc hroots
  have hvbig : v ∈ closedBall c (5 * Real.exp (-4 * B)) :=
    closedBall_subset_closedBall (by have := Real.exp_pos (-4 * B); linarith) hv
  have hnatlower (k : ℂ → ℕ) (hk : (∑ α ∈ σ, (k α : ℝ)) ≤ B) :
      Real.exp (-24 * B ^ 2) ≤ ‖divisorPowerProduct σ k v‖ := by
    have hb := norm_prod_pow_ge_exp σ (f := fun α => v - α) (m := k)
      (C := 24 * B) (M := B) (by positivity)
      (fun α hα => by simpa only [neg_mul] using (hprobe α hα).1) hk
    have he : -(24 * B) * B = -24 * B ^ 2 := by ring
    simpa only [he, divisorPowerProduct] using hb
  have hRAlower : Real.exp (-24 * B ^ 2) ≤ ‖∏ α ∈ σ, (v - α) ^ d α‖ := by
    have hband : ∀ α ∈ σ, Real.exp (-(24 * B)) ≤ ‖v - α‖ ∧ ‖v - α‖ ≤ Real.exp (24 * B) := by
      intro α hα
      exact ⟨by simpa only [neg_mul] using (hprobe α hα).1,
        (hprobe α hα).2.trans (Real.exp_le_exp.mpr (by linarith))⟩
    have hb := norm_prod_zpow_ge_exp σ (f := fun α => v - α) (d := d)
      (C := 24 * B) (M := B) (by positivity) hband hd
    have he : -(24 * B) * B = -24 * B ^ 2 := by ring
    simpa only [he] using hb
  have hNlower : E * Real.exp (-1 - 24 * B ^ 2) ≤ ‖N v‖ := by
    have he : Real.exp ((H c).re - 1) * Real.exp (-24 * B ^ 2) =
        E * Real.exp (-1 - 24 * B ^ 2) := by
      dsimp [E]
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [← he]
    change _ ≤ ‖Complex.exp (H v) * P v‖
    rw [norm_mul, Complex.norm_exp]
    exact mul_le_mul (Real.exp_le_exp.mpr (hRe v hvbig).1) (hnatlower m hm)
      (Real.exp_pos _).le (Real.exp_pos _).le
  let A : ℂ := Complex.exp (h v) * ∏ α ∈ σ, (v - α) ^ d α
  have hAlower : Real.exp (-B / 1000 - 24 * B ^ 2) ≤ ‖A‖ := by
    rw [show -B / 1000 - 24 * B ^ 2 = (-B / 1000) + (-24 * B ^ 2) by ring, Real.exp_add]
    change _ ≤ ‖Complex.exp (h v) * ∏ α ∈ σ, (v - α) ^ d α‖
    rw [norm_mul, Complex.norm_exp]
    exact mul_le_mul (Real.exp_le_exp.mpr (hhre v hvbig)) hRAlower
      (Real.exp_pos _).le (Real.exp_pos _).le
  have hN0 : N v ≠ 0 := norm_ne_zero_iff.mp
    (ne_of_gt ((mul_pos (Real.exp_pos _) (Real.exp_pos _)).trans_le hNlower))
  have hQ0 : Q v ≠ 0 := norm_ne_zero_iff.mp
    (ne_of_gt ((Real.exp_pos _).trans_le (hnatlower n hn)))
  have hregular : ∀ α ∈ σ, v ≠ α := by
    intro α hα heq
    have hp := (Real.exp_pos (-24 * B)).trans_le (hprobe α hα).1
    simp only [heq, sub_self, norm_zero, lt_self_iff_false] at hp
  have hWidentity : deriv N v * Q v - N v * deriv Q v = N v * Q v * A :=
    wronskian_eq_num_den_mul_of_log_deriv (hNanalytic v hvbig).differentiableAt
      (hQanalytic v).differentiableAt hN0 hQ0 (hlog v hvbig hregular)
  have hW : E * Real.exp (-77 * B ^ 2) ≤ ‖deriv N v * Q v - N v * deriv Q v‖ := by
    calc
      E * Real.exp (-77 * B ^ 2) ≤ E * Real.exp (-72 * B ^ 2 - B / 1000 - 1) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (Real.exp_pos _).le
      _ = (E * Real.exp (-1 - 24 * B ^ 2)) * Real.exp (-24 * B ^ 2) *
          Real.exp (-B / 1000 - 24 * B ^ 2) := by
        rw [show -72 * B ^ 2 - B / 1000 - 1 =
          ((-1 - 24 * B ^ 2) + (-24 * B ^ 2)) + (-B / 1000 - 24 * B ^ 2) by ring,
          Real.exp_add, Real.exp_add]
        ring
      _ ≤ ‖N v‖ * ‖Q v‖ * ‖A‖ :=
        mul_le_mul (mul_le_mul hNlower (hnatlower n hn) (Real.exp_pos _).le (norm_nonneg _))
          hAlower (Real.exp_pos _).le (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = ‖deriv N v * Q v - N v * deriv Q v‖ := by
        simp only [hWidentity, norm_mul]
  exact cleared_fiber_eta_disk_card_le s hB (Real.exp_pos _) hv hNanalytic
    (fun w _ => hQanalytic w) hNP (hnatupper n hn) (hnatlower n hn) hW hfiber

end ThreeIM
