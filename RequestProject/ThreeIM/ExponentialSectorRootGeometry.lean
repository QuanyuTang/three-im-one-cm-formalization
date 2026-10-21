module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Connected sectors and separated marked-root neighborhoods -/

@[expose] public section

open Set Metric

namespace ThreeIM

theorem truncated_right_sector_convex (R : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    Convex ℝ {t : ℂ | R ≤ t.re ∧ δ * ‖t‖ ≤ t.re} := by
  intro x hx y hy α β hα hβ hsum
  have hre : (α • x + β • y).re = α * x.re + β * y.re := by
    simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
  have hn : ‖α • x + β • y‖ ≤ α * ‖x‖ + β * ‖y‖ := by
    simpa only [norm_smul, Real.norm_of_nonneg hα, Real.norm_of_nonneg hβ] using
      norm_add_le (α • x) (β • y)
  constructor
  · rw [hre]
    calc
      R = (α + β) * R := by rw [hsum, one_mul]
      _ = α * R + β * R := by ring
      _ ≤ α * x.re + β * y.re := add_le_add
        (mul_le_mul_of_nonneg_left hx.1 hα) (mul_le_mul_of_nonneg_left hy.1 hβ)
  · calc
      δ * ‖α • x + β • y‖ ≤ δ * (α * ‖x‖ + β * ‖y‖) :=
        mul_le_mul_of_nonneg_left hn hδ
      _ = α * (δ * ‖x‖) + β * (δ * ‖y‖) := by ring
      _ ≤ α * x.re + β * y.re := add_le_add
        (mul_le_mul_of_nonneg_left hx.2 hα) (mul_le_mul_of_nonneg_left hy.2 hβ)
      _ = (α • x + β • y).re := hre.symm

theorem IsPreconnected.image_in_one_separated_ball
    {ι : Type*} {S : Set ℂ} {F : ℂ → ℂ} {a : ι → ℂ} {ε : ℝ}
    (hS : IsPreconnected S) (hSne : S.Nonempty) (hF : ContinuousOn F S)
    (hcover : ∀ z ∈ S, ∃ j, ‖F z - a j‖ < ε)
    (hsep : ∀ i j, i ≠ j → 2 * ε ≤ dist (a i) (a j)) :
    ∃ j, ∀ z ∈ S, ‖F z - a j‖ < ε := by
  classical
  obtain ⟨z₀, hz₀⟩ := hSne
  obtain ⟨j, hj⟩ := hcover z₀ hz₀
  let U : Set ℂ := ball (a j) ε
  let V : Set ℂ := ⋃ i, ⋃ (_ : i ≠ j), ball (a i) ε
  have hU : IsOpen U := isOpen_ball
  have hV : IsOpen V := isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_ball
  have huv : Disjoint U V := by
    apply Set.disjoint_left.mpr
    intro w hwu hwv
    obtain ⟨i, hwv⟩ := mem_iUnion.mp hwv
    obtain ⟨hij, hwi⟩ := mem_iUnion.mp hwv
    have hdist := dist_triangle (a i) w (a j)
    have hiw : dist (a i) w < ε := by
      rw [dist_comm]
      exact mem_ball.mp hwi
    have hjw : dist w (a j) < ε := mem_ball.mp hwu
    linarith [hsep i j hij]
  have hc : F '' S ⊆ U ∪ V := by
    rintro w ⟨z, hz, rfl⟩
    obtain ⟨i, hi⟩ := hcover z hz
    have hi' : F z ∈ ball (a i) ε := by simpa only [mem_ball, dist_eq_norm] using hi
    by_cases hij : i = j
    · subst i
      exact Or.inl hi'
    · exact Or.inr (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hij, hi'⟩⟩)
  have hne : (F '' S ∩ U).Nonempty := by
    refine ⟨F z₀, ⟨⟨z₀, hz₀, rfl⟩, ?_⟩⟩
    simpa only [U, mem_ball, dist_eq_norm] using hj
  have hsub := (hS.image F hF).subset_left_of_subset_union hU hV huv hc hne
  refine ⟨j, fun z hz => ?_⟩
  have hm := hsub (mem_image_of_mem F hz)
  simpa only [U, mem_ball, dist_eq_norm] using hm

end ThreeIM
