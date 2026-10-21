module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Mathlib.Data.Finset.Max

/-!
# A pointwise proximity estimate for finitely many distinct values

Only the value nearest to `w` can give a large proximity term. Its contribution is
controlled using `p⁻¹ * (p / (w - a j)) = (w - a j)⁻¹`. The other contributions
are bounded by the separation of the target values. All divisions use the usual
totalized field operations, so the estimate also holds when `w` is a target value.
-/

@[expose] public section

open scoped BigOperators

namespace ThreeIM

/-- A constant depending only on the finite target values. Diagonal terms are zero. -/
noncomputable def finiteValueSeparationConstant {q : ℕ} (a : Fin q → ℂ) : ℝ :=
  ∑ i, ∑ j, Real.posLog (2 / ‖a i - a j‖)

lemma finiteValueSeparationConstant_nonneg {q : ℕ} (a : Fin q → ℂ) :
    0 ≤ finiteValueSeparationConstant a := by
  unfold finiteValueSeparationConstant
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Real.posLog_nonneg

/-- The pointwise finite-target estimate, with an explicit separation constant. -/
theorem finite_values_proximity_pointwise_explicit {q : ℕ} (a : Fin q → ℂ)
    (ha : Function.Injective a) (w p : ℂ) (hp : p ≠ 0) :
    (∑ i, Real.posLog ‖(w - a i)⁻¹‖) ≤
      Real.posLog ‖p⁻¹‖ + (∑ i, Real.posLog ‖p / (w - a i)‖) +
        finiteValueSeparationConstant a := by
  classical
  by_cases hq : q = 0
  · subst q
    simpa [finiteValueSeparationConstant] using
      (Real.posLog_nonneg (x := ‖p⁻¹‖))
  have huniv : (Finset.univ : Finset (Fin q)).Nonempty :=
    ⟨⟨0, Nat.pos_of_ne_zero hq⟩, Finset.mem_univ _⟩
  obtain ⟨j, hj, hnearest⟩ :=
    (Finset.univ : Finset (Fin q)).exists_min_image (fun i => ‖w - a i‖) huniv
  have hcentral : Real.posLog ‖(w - a j)⁻¹‖ ≤
      Real.posLog ‖p⁻¹‖ + Real.posLog ‖p / (w - a j)‖ := by
    have hid : p⁻¹ * (p / (w - a j)) = (w - a j)⁻¹ := by
      rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hp, one_mul]
    rw [← hid, norm_mul]
    exact Real.posLog_mul
  have hother : ∀ i ∈ (Finset.univ : Finset (Fin q)).erase j,
      Real.posLog ‖(w - a i)⁻¹‖ ≤ ∑ k, Real.posLog (2 / ‖a i - a k‖) := by
    intro i hi
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    have hsep : 0 < ‖a i - a j‖ :=
      norm_pos_iff.2 (sub_ne_zero.2 fun h => hij (ha h))
    have hnear : ‖w - a j‖ ≤ ‖w - a i‖ := hnearest i (Finset.mem_univ _)
    have hdist : ‖a i - a j‖ ≤ 2 * ‖w - a i‖ := by
      calc
        ‖a i - a j‖ ≤ ‖a i - w‖ + ‖w - a j‖ :=
          norm_sub_le_norm_sub_add_norm_sub (a i) w (a j)
        _ = ‖w - a i‖ + ‖w - a j‖ := by rw [norm_sub_rev (a i) w]
        _ ≤ ‖w - a i‖ + ‖w - a i‖ := add_le_add le_rfl hnear
        _ = 2 * ‖w - a i‖ := (two_mul _).symm
    have hwi : 0 < ‖w - a i‖ := by
      by_contra hnot
      have hz : ‖w - a i‖ = 0 :=
        le_antisymm (le_of_not_gt hnot) (norm_nonneg _)
      rw [hz, mul_zero] at hdist
      exact (not_le_of_gt hsep) hdist
    have hinv : ‖w - a i‖⁻¹ ≤ 2 / ‖a i - a j‖ := by
      rw [← one_div]
      exact (div_le_div_iff₀ hwi hsep).2 (by simpa only [one_mul] using hdist)
    have hlog : Real.posLog ‖(w - a i)⁻¹‖ ≤ Real.posLog (2 / ‖a i - a j‖) := by
      rw [norm_inv]
      exact Real.posLog_le_posLog
        ((by norm_num : (-1 : ℝ) ≤ 0).trans (inv_nonneg.2 (norm_nonneg _))) hinv
    exact hlog.trans (Finset.single_le_sum
      (f := fun k : Fin q => Real.posLog (2 / ‖a i - a k‖))
      (fun _ _ => Real.posLog_nonneg) (Finset.mem_univ j))
  have hrest : (∑ i ∈ (Finset.univ : Finset (Fin q)).erase j,
      Real.posLog ‖(w - a i)⁻¹‖) ≤ finiteValueSeparationConstant a := by
    refine (Finset.sum_le_sum hother).trans ?_
    unfold finiteValueSeparationConstant
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      (fun _ _ _ => Finset.sum_nonneg fun _ _ => Real.posLog_nonneg)
  have hjterm : Real.posLog ‖p / (w - a j)‖ ≤
      ∑ i, Real.posLog ‖p / (w - a i)‖ :=
    Finset.single_le_sum (f := fun i : Fin q => Real.posLog ‖p / (w - a i)‖)
      (fun _ _ => Real.posLog_nonneg) hj
  calc
    (∑ i, Real.posLog ‖(w - a i)⁻¹‖) =
        Real.posLog ‖(w - a j)⁻¹‖ +
          ∑ i ∈ (Finset.univ : Finset (Fin q)).erase j,
            Real.posLog ‖(w - a i)⁻¹‖ :=
      (Finset.add_sum_erase _ _ hj).symm
    _ ≤ (Real.posLog ‖p⁻¹‖ + Real.posLog ‖p / (w - a j)‖) +
        finiteValueSeparationConstant a := add_le_add hcentral hrest
    _ ≤ Real.posLog ‖p⁻¹‖ + (∑ i, Real.posLog ‖p / (w - a i)‖) +
        finiteValueSeparationConstant a :=
      add_le_add (add_le_add le_rfl hjterm) le_rfl

/-- For distinct finite target values the additive constant is independent of `w` and `p`. -/
theorem finite_values_proximity_pointwise {q : ℕ} (a : Fin q → ℂ)
    (ha : Function.Injective a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w p : ℂ, p ≠ 0 →
      (∑ i, Real.posLog ‖(w - a i)⁻¹‖) ≤
        Real.posLog ‖p⁻¹‖ + (∑ i, Real.posLog ‖p / (w - a i)‖) + C := by
  exact ⟨finiteValueSeparationConstant a, finiteValueSeparationConstant_nonneg a,
    fun w p hp => finite_values_proximity_pointwise_explicit a ha w p hp⟩

end ThreeIM
