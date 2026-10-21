module

public import RequestProject.ThreeIM.TangentScalar

/-!
# The scalar equation of the tangent system: polynomial solutions

A polynomial solution `H` of the scalar equation of the tangent system is constant.  Multiplying
the equation by `2 e^{z/2}` writes it as `α Q₁(z) e^z + β Q₀(z) = 0` with polynomials `Q₀, Q₁`;
this forces `Q₁ = 0`, and the term `-H (H - 1) H'` of `Q₁` has larger degree than the others.
-/

@[expose] public section

open Filter Set Polynomial

namespace ThreeIM

lemma exp_two_pi_int (k : ℤ) : Complex.exp (2 * Real.pi * Complex.I * k) = 1 := by
  rw [show (2 * Real.pi * Complex.I * k : ℂ) = k * (2 * Real.pi * Complex.I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I k

lemma injective_two_pi_int (w : ℂ) :
    Function.Injective (fun k : ℤ => w + 2 * Real.pi * Complex.I * k) := by
  intro a b hab
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have : (2 * Real.pi * Complex.I : ℂ) * a = 2 * Real.pi * Complex.I * b := by
    simpa using hab
  exact_mod_cast mul_left_cancel₀ h2 this

/-- A polynomial vanishing at all points `w + 2πik`, `k ∈ ℤ`, is zero. -/
lemma poly_eq_zero_of_vanish_progression {P : ℂ[X]} (w : ℂ)
    (h : ∀ k : ℤ, P.eval (w + 2 * Real.pi * Complex.I * k) = 0) : P = 0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective (injective_two_pi_int w))
  rintro _ ⟨k, rfl⟩
  exact h k

/-- If `P(z) e^z + Q(z) = 0` for all `z`, then `P = 0`. -/
lemma poly_exp_eq_zero {P Q : ℂ[X]} (h : ∀ z, P.eval z * Complex.exp z + Q.eval z = 0) :
    P = 0 := by
  have h1 : P + Q = 0 := by
    refine poly_eq_zero_of_vanish_progression 0 fun k => ?_
    have := h (0 + 2 * Real.pi * Complex.I * k)
    rw [zero_add, exp_two_pi_int, mul_one] at this
    simpa using this
  have h2 : 2 * P + Q = 0 := by
    refine poly_eq_zero_of_vanish_progression (Real.log 2) fun k => ?_
    have := h (Real.log 2 + 2 * Real.pi * Complex.I * k)
    rw [Complex.exp_add, exp_two_pi_int, mul_one,
      ← Complex.ofReal_exp, Real.exp_log (by norm_num)] at this
    simp only [eval_add, eval_mul, eval_ofNat]
    push_cast at this ⊢
    linear_combination this
  calc P = (2 * P + Q) - (P + Q) := by ring
    _ = 0 := by rw [h1, h2, sub_zero]

/-- **Lemma 7.13, polynomial case.**  A polynomial solution of the scalar equation of the
tangent system is constant. -/
theorem tanScalar_poly {α β : ℂ} (hα : α ≠ 0) {p : ℂ[X]}
    (h : TanScalar α β (fun z => p.eval z)) : p.natDegree = 0 := by
  set p1 := derivative p with hp1
  set p2 := derivative p1 with hp2
  have hd1 : deriv (fun z => p.eval z) = fun z => p1.eval z := funext fun z => Polynomial.deriv p
  have hd2 : deriv (deriv (fun z => p.eval z)) = fun z => p2.eval z := by
    rw [hd1]; exact funext fun z => Polynomial.deriv p1
  set Q1 : ℂ[X] := 2 * p * (p - 1) * p2 - p * (p - 1) * p1 - 2 * (3 * p - 1) * p1 ^ 2 with hQ1
  set Q0 : ℂ[X] := -2 * p * (p - 1) * p2 - p * (p - 1) * p1 + 2 * (3 * p - 1) * p1 ^ 2
    - 2 * p1 ^ 2 with hQ0
  have hpoly : ∀ z, (C α * Q1).eval z * Complex.exp z + (C β * Q0).eval z = 0 := by
    intro z
    have hz := h z
    rw [hd2, hd1] at hz
    simp only [tanC, tanC', tanA, tanB] at hz
    set u := Complex.exp (z / 2)
    set v := Complex.exp (-z / 2)
    have huv : u * v = 1 := by
      rw [← Complex.exp_add]; ring_nf; exact Complex.exp_zero
    have huu : u * u = Complex.exp z := by
      rw [← Complex.exp_add]; ring_nf
    simp only [hQ1, hQ0, eval_mul, eval_sub, eval_add, eval_pow, eval_C, eval_neg, eval_one,
      eval_ofNat]
    linear_combination (2 * u) * hz
      - α * (2 * eval z p * (eval z p - 1) * eval z p2 - eval z p * (eval z p - 1) * eval z p1
        - 2 * (3 * eval z p - 1) * eval z p1 ^ 2) * huu
      - β * (-2 * eval z p * (eval z p - 1) * eval z p2 - eval z p * (eval z p - 1) * eval z p1
        + 2 * (3 * eval z p - 1) * eval z p1 ^ 2 - 2 * eval z p1 ^ 2) * huv
  have hQ1z : Q1 = 0 := by
    have := poly_exp_eq_zero hpoly
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (C_eq_zero.1 h) hα
    · exact h
  by_contra hd
  have hp0 : p ≠ 0 := by rintro rfl; simp at hd
  have hp10 : p - 1 ≠ 0 := by
    intro h0
    have : (p - C 1).natDegree = p.natDegree := natDegree_sub_C
    rw [C_1, h0] at this
    simp at this
    exact hd this.symm
  have hp1ne : p1 ≠ 0 := fun h0 => hd (natDegree_eq_zero_of_derivative_eq_zero h0)
  have hp1lt : p1.natDegree < p.natDegree := natDegree_derivative_lt hd
  -- `2 p'' - p'` is nonzero with the degree of `p'`
  have hS : (2 * p2 - p1).natDegree = p1.natDegree ∧ 2 * p2 - p1 ≠ 0 := by
    by_cases h1 : p1.natDegree = 0
    · have : p2 = 0 := derivative_of_natDegree_zero h1
      rw [this, mul_zero, zero_sub, natDegree_neg]
      exact ⟨rfl, neg_ne_zero.2 hp1ne⟩
    · have hlt : (2 * p2).natDegree < p1.natDegree :=
        calc (2 * p2).natDegree ≤ p2.natDegree := by
              rw [show (2 : ℂ[X]) = C 2 from (map_ofNat C 2).symm]; exact natDegree_C_mul_le _ _
          _ < p1.natDegree := natDegree_derivative_lt h1
      refine ⟨natDegree_sub_eq_right_of_natDegree_lt hlt, fun h0 => ?_⟩
      have : 2 * p2 = p1 := sub_eq_zero.1 h0
      rw [this] at hlt
      exact lt_irrefl _ hlt
  have hkey : p * (p - 1) * (2 * p2 - p1) = 2 * (3 * p - 1) * p1 ^ 2 := by
    have : Q1 = 0 := hQ1z
    rw [hQ1] at this
    linear_combination this
  have hL : (p * (p - 1) * (2 * p2 - p1)).natDegree =
      p.natDegree + p.natDegree + p1.natDegree := by
    rw [natDegree_mul (mul_ne_zero hp0 hp10) hS.2, natDegree_mul hp0 hp10, hS.1]
    congr 2
    have : (p - C 1).natDegree = p.natDegree := natDegree_sub_C
    rwa [C_1] at this
  have hR : (2 * (3 * p - 1) * p1 ^ 2).natDegree ≤ p.natDegree + 2 * p1.natDegree := by
    refine (natDegree_mul_le).trans (add_le_add ?_ ?_)
    · rw [show (2 : ℂ[X]) = C 2 from (map_ofNat C 2).symm]
      refine (natDegree_C_mul_le _ _).trans ?_
      refine (natDegree_sub_le _ _).trans ?_
      rw [show (3 : ℂ[X]) = C 3 from (map_ofNat C 3).symm, natDegree_one]
      exact max_le (natDegree_C_mul_le _ _) (Nat.zero_le _)
    · exact natDegree_pow_le.trans (by rw [mul_comm])
  rw [hkey] at hL
  omega

end ThreeIM
