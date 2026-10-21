module

public import RequestProject.ThreeIM.TangentPoly
public import RequestProject.ThreeIM.TangentTranscendental

/-!
# The scalar equation of the tangent system has only constant entire solutions

This is the main step of the proof of Lemma 7.13: a polynomial solution is constant
(`tanScalar_poly`) and a transcendental solution does not exist
(`tanScalar_transcendental_false`).
-/

@[expose] public section

open Polynomial

namespace ThreeIM

/-- **Main step of Lemma 7.13**: every entire solution of the scalar equation is constant. -/
theorem tanScalar_const {α β : ℂ} (hα : α ≠ 0) (hβ : β ≠ 0) {H : ℂ → ℂ}
    (hH : Differentiable ℂ H) (h : TanScalar α β H) : ∀ z, H z = H 0 := by
  by_cases htr : Transcendental H
  · exact (tanScalar_transcendental_false hα hβ hH htr h).elim
  · simp only [Transcendental, not_forall, not_exists, not_not] at htr
    obtain ⟨p, hp⟩ := htr
    have hHp : H = fun z => p.eval z := funext hp
    rw [hHp] at h ⊢
    have hd := tanScalar_poly hα h
    rw [Polynomial.eq_C_of_natDegree_eq_zero hd]
    simp

end ThreeIM
