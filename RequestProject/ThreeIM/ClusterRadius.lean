module

public import RequestProject.ThreeIM.ClusterProbe
public import Mathlib.Data.Finset.Image
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A separated control circle from finitely many divisor points

Equally spaced test radii replace the forbidden-interval measure argument.
The resulting circle is the genuine geometric input for the maximum-modulus
bound on H' in step 1. Divisor centers may coincide in modulus or be absent.
-/

@[expose] public section

set_option autoImplicit false

open Set Metric

namespace ThreeIM

/-- A real interval contains a point separated from an arbitrary finite
set, with no separation hypothesis on the forbidden values. -/
theorem exists_separated_real_point (centers : Finset ℝ) {a b : ℝ} (hab : a < b) :
    ∃ x ∈ Icc a b, ∀ α ∈ centers,
      (b - a) / (10 * ((centers.card : ℝ) + 1)) ≤ dist x α := by
  classical
  let δ : ℝ := (b - a) / ((centers.card : ℝ) + 1)
  have hden : 0 < (centers.card : ℝ) + 1 := by positivity
  have hδ : 0 < δ := div_pos (sub_pos.mpr hab) hden
  have hδid : ((centers.card : ℝ) + 1) * δ = b - a := by dsimp [δ]; field_simp
  let p : Fin (centers.card + 1) → ℝ := fun i => a + (i.val : ℝ) * δ
  have hmem : ∀ i, p i ∈ Icc a b := by
    intro i
    have hi0 : (0 : ℝ) ≤ (i.val : ℝ) := Nat.cast_nonneg _
    have hiN : (i.val : ℝ) ≤ (centers.card : ℝ) := by
      exact_mod_cast Nat.le_of_lt_succ i.isLt
    have hmul := mul_le_mul_of_nonneg_right hiN hδ.le
    constructor <;> dsimp [p] <;> nlinarith
  have hspacing : ∀ i j, i ≠ j → δ ≤ dist (p i) (p j) := by
    intro i j hij
    have hvals : i.val ≠ j.val := fun heq => hij (Fin.ext heq)
    have habs : (1 : ℝ) ≤ |(i.val : ℝ) - (j.val : ℝ)| := by
      rcases lt_or_gt_of_ne hvals with hlt | hgt
      · have hstep : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by exact_mod_cast Nat.succ_le_iff.mpr hlt
        rw [abs_of_nonpos (by linarith)]
        linarith
      · have hstep : (j.val : ℝ) + 1 ≤ (i.val : ℝ) := by exact_mod_cast Nat.succ_le_iff.mpr hgt
        rw [abs_of_nonneg (by linarith)]
        linarith
    have hsub : p i - p j = ((i.val : ℝ) - (j.val : ℝ)) * δ := by dsimp [p]; ring
    rw [Real.dist_eq, hsub, abs_mul, abs_of_pos hδ]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right habs hδ.le
  by_contra hnone
  have hcover : ∀ i, ∃ α : centers,
      dist (p i) (α : ℝ) < (b - a) / (10 * ((centers.card : ℝ) + 1)) := by
    intro i
    by_contra hno
    apply hnone
    refine ⟨p i, hmem i, fun α hα => le_of_not_gt ?_⟩
    intro hdist
    exact hno ⟨⟨α, hα⟩, hdist⟩
  let assign : Fin (centers.card + 1) → centers := fun i => Classical.choose (hcover i)
  have hassign : ∀ i, dist (p i) (assign i : ℝ) <
      (b - a) / (10 * ((centers.card : ℝ) + 1)) := fun i => Classical.choose_spec (hcover i)
  have hinj : Function.Injective assign := by
    intro i j heq
    by_contra hij
    have hja : dist (assign i : ℝ) (p j) < (b - a) / (10 * ((centers.card : ℝ) + 1)) := by
      rw [heq, dist_comm]
      exact hassign j
    have hupper : dist (p i) (p j) < 2 * ((b - a) / (10 * ((centers.card : ℝ) + 1))) := by
      have ht := dist_triangle (p i) (assign i : ℝ) (p j)
      linarith [hassign i]
    have hrad : 2 * ((b - a) / (10 * ((centers.card : ℝ) + 1))) = δ / 5 := by
      dsimp [δ]
      field_simp [ne_of_gt hden]
      ring
    rw [hrad] at hupper
    have hsep := hspacing i j hij
    linarith
  have hcard := Fintype.card_le_of_injective assign hinj
  simp only [Fintype.card_fin, Fintype.card_coe] at hcard
  exact Nat.not_succ_le_self _ hcard

/-- The actual source control circle exists, including when the divisor
set is empty. Every linear factor on that circle has the required lower
bound Delta/[100(N+1)]. -/
theorem exists_divisor_separated_circle (centers : Finset ℂ) {r Δ : ℝ}
    (hr : 0 ≤ r) (hΔ : 0 < Δ) :
    ∃ σ ∈ Icc (r + Δ / 4) (r + Δ / 2), 0 < σ ∧
      ∀ w ∈ sphere (0 : ℂ) σ, ∀ α ∈ centers,
        Δ / (100 * ((centers.card : ℝ) + 1)) ≤ ‖w - α‖ := by
  classical
  let mods : Finset ℝ := centers.image (fun α => ‖α‖)
  obtain ⟨σ, hσ, hsep⟩ := exists_separated_real_point mods
    (by linarith : r + Δ / 4 < r + Δ / 2)
  have hσpos : 0 < σ := by linarith [hσ.1]
  refine ⟨σ, hσ, hσpos, ?_⟩
  intro w hw α hα
  have hnorm : ‖w‖ = σ := by simpa only [mem_sphere, dist_zero_right] using hw
  have hmod : ‖α‖ ∈ mods := Finset.mem_image.mpr ⟨α, hα, rfl⟩
  have hc : (mods.card : ℝ) ≤ (centers.card : ℝ) := by exact_mod_cast Finset.card_image_le
  have hden : 0 < 10 * ((mods.card : ℝ) + 1) := by positivity
  have hdenC : 0 < (centers.card : ℝ) + 1 := by positivity
  have hnum : (r + Δ / 2) - (r + Δ / 4) = Δ / 4 := by ring
  have hsmall : Δ / (100 * ((centers.card : ℝ) + 1)) ≤
      ((r + Δ / 2) - (r + Δ / 4)) / (10 * ((mods.card : ℝ) + 1)) := by
    rw [hnum]
    apply (div_le_div_iff₀ (by positivity : 0 < 100 * ((centers.card : ℝ) + 1)) hden).mpr
    nlinarith
  have hlower := hsmall.trans (hsep ‖α‖ hmod)
  rw [Real.dist_eq, ← hnorm] at hlower
  exact hlower.trans (abs_norm_sub_norm_le w α)

end ThreeIM
