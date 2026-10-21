module

public import RequestProject.ThreeIM.Basic

/-!
# Rational functions on the punctured plane (Section 9)

* `ratEval`: a rational function viewed as a function `ℂ → ℂ`.
  (Proposition 9.28 itself is `rational_four_values` in `RationalFinal.lean`.)
* Lemma 9.24 (polynomial core): a polynomial invariant under all rotations `t ↦ ξ t`,
  `ξ^ρ = 1`, is a polynomial in `t^ρ`.
-/

@[expose] public section

open Filter Set Polynomial

namespace ThreeIM

/-- A rational function, viewed as a function `ℂ → ℂ` (junk values at poles). -/
noncomputable def ratEval (R : RatFunc ℂ) : ℂ → ℂ := fun t => R.eval (RingHom.id ℂ) t

/-- **Lemma 9.24** (descent of a rotation-invariant function, polynomial core).  If a
polynomial `p` satisfies `p(ξ t) = p(t)` for every `ρ`-th root of unity `ξ`, then
`p(t) = q(t^ρ)` for some polynomial `q`. -/
theorem polynomial_descent {ρ : ℕ} (hρ : 0 < ρ) {p : ℂ[X]}
    (hp : ∀ ξ : ℂ, ξ ^ ρ = 1 → p.comp (C ξ * X) = p) :
    ∃ q : ℂ[X], p = q.comp (X ^ ρ) := by
  have hζ := Complex.isPrimitiveRoot_exp ρ hρ.ne'
  set ζ := Complex.exp (2 * ↑Real.pi * Complex.I / ↑ρ)
  have hdiv : ∀ n, p.coeff n ≠ 0 → ρ ∣ n := by
    intro n hn
    have h := congrArg (fun q => q.coeff n) (hp ζ hζ.pow_eq_one)
    simp only [comp_C_mul_X_coeff] at h
    exact (hζ.pow_eq_one_iff_dvd n).1 (mul_left_cancel₀ hn (h.trans (mul_one _).symm))
  refine ⟨contract ρ p, ?_⟩
  rw [← expand_eq_comp_X_pow]
  ext n
  rw [coeff_expand hρ]
  split_ifs with h
  · rw [coeff_contract hρ.ne', Nat.div_mul_cancel h]
  · by_contra hne
    exact h (hdiv n fun h0 => hne h0)

end ThreeIM
