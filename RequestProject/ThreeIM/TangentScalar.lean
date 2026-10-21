module

public import RequestProject.ThreeIM.Normality

/-!
# The scalar equation of the tangent system (proof of Lemma 7.13, main step)

For `αβ ≠ 0` put `a(z) = α e^{z/2}`, `b(z) = β e^{-z/2}`, `c = a - b`.  The scalar equation of
Lemma 7.7 for the tangent system reads
`c H (H - 1) H'' - c' H (H - 1) H' - (c (3H - 1) + b) (H')² = 0`.
The main step of the proof of Lemma 7.13 is that its only entire solutions are constant.
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

/-- `a(z) = α e^{z/2}`. -/
noncomputable def tanA (α z : ℂ) : ℂ := α * Complex.exp (z / 2)

/-- `b(z) = β e^{-z/2}`. -/
noncomputable def tanB (β z : ℂ) : ℂ := β * Complex.exp (-z / 2)

/-- `c = a - b`. -/
noncomputable def tanC (α β z : ℂ) : ℂ := tanA α z - tanB β z

/-- `c' = a/2 + b/2`. -/
noncomputable def tanC' (α β z : ℂ) : ℂ := tanA α z / 2 + tanB β z / 2

/-- The scalar equation of the tangent system. -/
def TanScalar (α β : ℂ) (H : ℂ → ℂ) : Prop :=
  ∀ z, tanC α β z * H z * (H z - 1) * deriv (deriv H) z
    - tanC' α β z * H z * (H z - 1) * deriv H z
    - (tanC α β z * (3 * H z - 1) + tanB β z) * deriv H z ^ 2 = 0

lemma hasDerivAt_tanA (α z : ℂ) : HasDerivAt (tanA α) (tanA α z / 2) z := by
  have := ((hasDerivAt_id z).div_const 2).cexp.const_mul α
  convert this using 1
  · ext w
    rfl
  · simp only [tanA, id_eq]
    ring

lemma hasDerivAt_tanB (β z : ℂ) : HasDerivAt (tanB β) (-(tanB β z / 2)) z := by
  have := ((hasDerivAt_id z).neg.div_const 2).cexp.const_mul β
  convert this using 1
  · ext w
    rfl
  · simp only [tanB, Pi.neg_apply, id_eq]
    ring

lemma hasDerivAt_tanC (α β z : ℂ) : HasDerivAt (tanC α β) (tanC' α β z) z := by
  have := (hasDerivAt_tanA α z).sub (hasDerivAt_tanB β z)
  convert this using 1
  · ext w
    rfl
  · simp only [tanC']
    ring

lemma differentiable_tanA (α : ℂ) : Differentiable ℂ (tanA α) :=
  fun z => (hasDerivAt_tanA α z).differentiableAt

lemma differentiable_tanB (β : ℂ) : Differentiable ℂ (tanB β) :=
  fun z => (hasDerivAt_tanB β z).differentiableAt

lemma differentiable_tanC (α β : ℂ) : Differentiable ℂ (tanC α β) :=
  fun z => (hasDerivAt_tanC α β z).differentiableAt

lemma tanA_ne_zero {α : ℂ} (hα : α ≠ 0) (z : ℂ) : tanA α z ≠ 0 :=
  mul_ne_zero hα (Complex.exp_ne_zero _)

lemma tanB_ne_zero {β : ℂ} (hβ : β ≠ 0) (z : ℂ) : tanB β z ≠ 0 :=
  mul_ne_zero hβ (Complex.exp_ne_zero _)

/-- The zeros of `c` are simple: `c = 0` forces `c' = a ≠ 0`. -/
lemma tanC'_ne_zero_of_tanC_eq_zero {α β : ℂ} (hα : α ≠ 0) {z : ℂ} (hz : tanC α β z = 0) :
    tanC' α β z ≠ 0 := by
  have hab : tanA α z = tanB β z := sub_eq_zero.1 hz
  simp only [tanC', ← hab]
  intro h
  exact tanA_ne_zero hα z (by linear_combination h)

end ThreeIM
