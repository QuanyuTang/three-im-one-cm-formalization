module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A regular probe inside an arbitrary divisor cluster

N forbidden divisor centers cannot cover N+1 equally spaced test points on a
diameter by disks of radius one tenth of their spacing. This gives a probe
separated from every divisor, without assuming any separation of the divisors
themselves. It is the finite geometric input for the cluster Wronskian bound.
-/

@[expose] public section

open Set Metric

namespace ThreeIM

/-- A small disk contains a point quantitatively separated from an arbitrary
finite divisor set. The empty divisor set is allowed. -/
theorem exists_regular_cluster_probe (centers : Finset ℂ) (c : ℂ) {ρ : ℝ}
    (hρ : 0 < ρ) :
    ∃ v ∈ closedBall c (ρ / 2), ∀ α ∈ centers,
      ρ / (10 * ((centers.card : ℝ) + 1)) ≤ dist v α := by
  classical
  let δ : ℝ := ρ / ((centers.card : ℝ) + 1)
  have hden : 0 < (centers.card : ℝ) + 1 := by positivity
  have hδ : 0 < δ := div_pos hρ hden
  have hδid : ((centers.card : ℝ) + 1) * δ = ρ := by
    dsimp [δ]
    field_simp
  have hNδ : (centers.card : ℝ) * δ ≤ ρ := by nlinarith
  let p : Fin (centers.card + 1) → ℂ := fun i =>
    c + ((((i.val : ℝ) - (centers.card : ℝ) / 2) * δ : ℝ) : ℂ)
  have hmem : ∀ i, p i ∈ closedBall c (ρ / 2) := by
    intro i
    have hi0 : (0 : ℝ) ≤ (i.val : ℝ) := Nat.cast_nonneg _
    have hiN : (i.val : ℝ) ≤ (centers.card : ℝ) := by
      exact_mod_cast Nat.le_of_lt_succ i.isLt
    have hlow := mul_le_mul_of_nonneg_right
      (by linarith : -(centers.card : ℝ) / 2 ≤ (i.val : ℝ) - (centers.card : ℝ) / 2) hδ.le
    have hupp := mul_le_mul_of_nonneg_right
      (by linarith : (i.val : ℝ) - (centers.card : ℝ) / 2 ≤ (centers.card : ℝ) / 2) hδ.le
    have habs : |((i.val : ℝ) - (centers.card : ℝ) / 2) * δ| ≤ ρ / 2 := by
      apply abs_le.mpr
      constructor <;> nlinarith
    simpa only [p, mem_closedBall, dist_eq_norm, add_sub_cancel_left,
      Complex.norm_real, Real.norm_eq_abs] using habs
  have hspacing : ∀ i j, i ≠ j → δ ≤ dist (p i) (p j) := by
    intro i j hij
    have hvals : i.val ≠ j.val := fun heq => hij (Fin.ext heq)
    have habs : (1 : ℝ) ≤ |(i.val : ℝ) - (j.val : ℝ)| := by
      rcases lt_or_gt_of_ne hvals with hlt | hgt
      · have hstep : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by
          exact_mod_cast Nat.succ_le_iff.mpr hlt
        rw [abs_of_nonpos (by linarith)]
        linarith
      · have hstep : (j.val : ℝ) + 1 ≤ (i.val : ℝ) := by
          exact_mod_cast Nat.succ_le_iff.mpr hgt
        rw [abs_of_nonneg (by linarith)]
        linarith
    have hsub : p i - p j = ((((i.val : ℝ) - (j.val : ℝ)) * δ : ℝ) : ℂ) := by
      dsimp [p]
      push_cast
      ring
    rw [dist_eq_norm, hsub, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hδ]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right habs hδ.le
  by_contra hnone
  have hcover : ∀ i, ∃ α : centers,
      dist (p i) (α : ℂ) < ρ / (10 * ((centers.card : ℝ) + 1)) := by
    intro i
    by_contra hno
    apply hnone
    refine ⟨p i, hmem i, ?_⟩
    intro α hα
    apply le_of_not_gt
    intro hdist
    exact hno ⟨⟨α, hα⟩, hdist⟩
  let assign : Fin (centers.card + 1) → centers := fun i => Classical.choose (hcover i)
  have hassign : ∀ i, dist (p i) (assign i : ℂ) <
      ρ / (10 * ((centers.card : ℝ) + 1)) := fun i => Classical.choose_spec (hcover i)
  have hinj : Function.Injective assign := by
    intro i j heq
    by_contra hij
    have hja : dist (assign i : ℂ) (p j) < ρ / (10 * ((centers.card : ℝ) + 1)) := by
      rw [heq, dist_comm]
      exact hassign j
    have hupper : dist (p i) (p j) < 2 * (ρ / (10 * ((centers.card : ℝ) + 1))) := by
      have ht := dist_triangle (p i) (assign i : ℂ) (p j)
      linarith [hassign i]
    have hrad : 2 * (ρ / (10 * ((centers.card : ℝ) + 1))) = δ / 5 := by
      dsimp [δ]
      field_simp [ne_of_gt hden]
      ring
    rw [hrad] at hupper
    have hsep := hspacing i j hij
    linarith
  have hcard := Fintype.card_le_of_injective assign hinj
  simp only [Fintype.card_fin, Fintype.card_coe] at hcard
  exact Nat.not_succ_le_self _ hcard

end ThreeIM
