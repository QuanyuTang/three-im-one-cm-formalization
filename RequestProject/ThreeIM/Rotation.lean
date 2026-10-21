module

public import RequestProject.ThreeIM.OccupancyEight
public import RequestProject.ThreeIM.Rational

/-!
# Rotation invariance of the finite fibers and descent (Lemmas 9.23 and 9.24)

* `indicator_periodic_of_poly_form`: the combinatorial part of Lemma 9.23.  If the two
  occupancy differences `i₁ - i₀` and `i_c - i₀` of three disjoint fiber indicators both have
  the polynomial form `(u + vX)(1 + X² + ⋯ + X^{N-2})`, then every individual indicator is
  invariant under `j ↦ j + 2`, i.e. under the rotation `t ↦ ζ_N² t = e^{2πi/ρ} t`.
* `OccupancyData.indicator_periodic`: Lemma 9.23 for occupancy data whose polynomials are
  built from fiber indicators.
* `polynomial_pair_descent`: Lemma 9.24 for rational functions `H = A / B`, stated for the
  numerator/denominator pair: if `H(ξ t) = H(t)` for every `ρ`-th root of unity `ξ`, then
  `H(t) = p(t^ρ) / q(t^ρ)`.
* `ratFunc_descent`: the same statement for `H : RatFunc ℂ`.
* `ratFunc_eq_monomial`: the last step of Lemma 9.3 — a rational function without zeros or
  poles on `ℂ*` is `α t^u`.
-/

@[expose] public section

open Polynomial

namespace ThreeIM

/-- The coefficients of `(u + vX)(1 + X² + ⋯ + X^{2m-2})` are `u` at even and `v` at odd
indices below `2m`; in particular they are invariant under `j ↦ j + 2` there. -/
theorem coeff_poly_form_add_two (u v : ℤ) (m j : ℕ) (hj : j + 2 < 2 * m) :
    ((C u + C v * X) * ∑ i ∈ Finset.range m, (X : ℤ[X]) ^ (2 * i)).coeff (j + 2) =
      ((C u + C v * X) * ∑ i ∈ Finset.range m, (X : ℤ[X]) ^ (2 * i)).coeff j := by
  have hG : ∀ k, (∑ i ∈ Finset.range m, (X : ℤ[X]) ^ (2 * i)).coeff k =
      if Even k ∧ k < 2 * m then 1 else 0 := by
    intro k
    rw [finset_sum_coeff]
    simp only [coeff_X_pow]
    split_ifs with h
    · obtain ⟨⟨r, hr⟩, hk⟩ := h
      rw [Finset.sum_eq_single r]
      · simp [hr, two_mul]
      · intro b _ hb; rw [if_neg]; omega
      · intro hr'; simp at hr'; omega
    · refine Finset.sum_eq_zero fun i hi => ?_
      rw [if_neg]
      rintro rfl
      simp at hi
      exact h ⟨⟨i, by ring⟩, by omega⟩
  have hK : ∀ k < 2 * m,
      ((C u + C v * X) * ∑ i ∈ Finset.range m, (X : ℤ[X]) ^ (2 * i)).coeff k =
        if Even k then u else v := by
    intro k hk
    rw [add_mul, coeff_add, coeff_C_mul, mul_assoc, coeff_C_mul, hG]
    rcases k with _ | k
    · simp; omega
    · rw [coeff_X_mul, hG]
      by_cases he : Even (k + 1)
      · have : ¬ Even k := by rw [Nat.even_add_one] at he; exact he
        simp [he, this, hk]
      · have : Even k := by rw [Nat.even_add_one] at he; push_neg at he; exact he
        simp [he, this, show k < 2 * m by omega]
  rw [hK _ hj, hK _ (by omega)]
  simp [Nat.even_add]

/-- The occupancy polynomial `∑_{j<N} (i_v(j) - i_0(j)) X^j` of two fiber indicators. -/
noncomputable def occupancyPoly (N : ℕ) (iv i0 : ℕ → ℤ) : ℤ[X] :=
  ∑ j ∈ Finset.range N, C (iv j - i0 j) * X ^ j

theorem coeff_occupancyPoly {N : ℕ} (iv i0 : ℕ → ℤ) {j : ℕ} (hj : j < N) :
    (occupancyPoly N iv i0).coeff j = iv j - i0 j := by
  rw [occupancyPoly, finset_sum_coeff, Finset.sum_eq_single j]
  · rw [coeff_C_mul, coeff_X_pow]; simp
  · intro b _ hb; rw [coeff_C_mul, coeff_X_pow, if_neg (Ne.symm hb), mul_zero]
  · intro h; exact absurd (Finset.mem_range.2 hj) h

theorem natDegree_occupancyPoly_lt {N : ℕ} (hN : 0 < N) (iv i0 : ℕ → ℤ) :
    (occupancyPoly N iv i0).natDegree < N := by
  rw [occupancyPoly]
  refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := N - 1) fun j hj => ?_) (by omega)
  refine (natDegree_C_mul_le _ _).trans ?_
  simp at hj
  rw [natDegree_X_pow]; omega

/-- **Lemma 9.23, combinatorial part.**  Let `i₀, i₁, i_c` be the indicators (with values in
`{0, 1}`) of three pairwise disjoint fibers at the locations `r_T ζ_N^j`, `0 ≤ j < N`, of a fixed
type `T`.  If both occupancy polynomials `F^{(1)}_T, F^{(c)}_T` have the form
`(u + vX)(1 + X² + ⋯ + X^{N-2})`, then each indicator is invariant under `j ↦ j + 2`. -/
theorem indicator_periodic_of_poly_form {N : ℕ} (i0 i1 ic : ℕ → ℤ)
    (h0 : ∀ j, 0 ≤ i0 j) (h1 : ∀ j, 0 ≤ i1 j) (hc : ∀ j, 0 ≤ ic j)
    (hdisj : ∀ j, i0 j + i1 j + ic j ≤ 1)
    (hF1 : ∃ u v : ℤ, occupancyPoly N i1 i0 =
      (C u + C v * X) * ∑ i ∈ Finset.range (N / 2), X ^ (2 * i))
    (hFc : ∃ u v : ℤ, occupancyPoly N ic i0 =
      (C u + C v * X) * ∑ i ∈ Finset.range (N / 2), X ^ (2 * i))
    (hev : Even N) {j : ℕ} (hj : j + 2 < N) :
    i0 (j + 2) = i0 j ∧ i1 (j + 2) = i1 j ∧ ic (j + 2) = ic j := by
  obtain ⟨m, rfl⟩ : ∃ m, N = 2 * m := ⟨N / 2, by obtain ⟨k, hk⟩ := hev; omega⟩
  rw [show 2 * m / 2 = m by omega] at hF1 hFc
  obtain ⟨u1, v1, e1⟩ := hF1
  obtain ⟨uc, vc, ec⟩ := hFc
  have d1 := coeff_poly_form_add_two u1 v1 m j hj
  have dc := coeff_poly_form_add_two uc vc m j hj
  rw [← e1, coeff_occupancyPoly _ _ hj, coeff_occupancyPoly _ _ (by omega)] at d1
  rw [← ec, coeff_occupancyPoly _ _ hj, coeff_occupancyPoly _ _ (by omega)] at dc
  have := h0 j; have := h1 j; have := hc j; have := hdisj j
  have := h0 (j + 2); have := h1 (j + 2); have := hc (j + 2); have := hdisj (j + 2)
  omega

/-- **Lemma 9.23** for occupancy data built from fiber indicators.  Let `D₁, D_c` be occupancy
data (the two comparisons `v = 1` and `v = c` of Lemma 9.11) for the same even `N`, whose
polynomial at a type `x` is `∑_{j<N} (i_v(x, j) - i_0(x, j)) X^j` for disjoint fiber indicators.
Then every indicator is invariant under `j ↦ j + 2`, i.e. each finite common fiber is invariant
under the rotation `t ↦ e^{2πi/ρ} t`, `N = 2ρ`. -/
theorem OccupancyData.indicator_periodic {N : ℕ} (D₁ Dc : OccupancyData N) (hev : Even N)
    (i0 i1 ic : ℚ → ℕ → ℤ)
    (h0 : ∀ x j, 0 ≤ i0 x j) (h1 : ∀ x j, 0 ≤ i1 x j) (hc : ∀ x j, 0 ≤ ic x j)
    (hdisj : ∀ x j, i0 x j + i1 x j + ic x j ≤ 1)
    (hD₁ : ∀ x, D₁.F x = occupancyPoly N (i1 x) (i0 x))
    (hDc : ∀ x, Dc.F x = occupancyPoly N (ic x) (i0 x))
    (x : ℚ) {j : ℕ} (hj : j + 2 < N) :
    i0 x (j + 2) = i0 x j ∧ i1 x (j + 2) = i1 x j ∧ ic x (j + 2) = ic x j := by
  refine indicator_periodic_of_poly_form (i0 x) (i1 x) (ic x) (h0 x) (h1 x) (hc x) (hdisj x)
    ?_ ?_ hev hj
  · rw [← hD₁]
    exact D₁.poly_form hev x (by rw [hD₁]; exact natDegree_occupancyPoly_lt D₁.N_pos _ _)
  · rw [← hDc]
    exact Dc.poly_form hev x (by rw [hDc]; exact natDegree_occupancyPoly_lt Dc.N_pos _ _)

/-- **Lemma 9.24** (descent of a rotation-invariant rational function), for a representation
`H = A / B`.  The hypothesis `A(ξt) B(t) = A(t) B(ξt)` says `H(ξ t) = H(t)`; the conclusion says
`H(t) = p(t^ρ) / q(t^ρ)`. -/
theorem polynomial_pair_descent {ρ : ℕ} (hρ : 0 < ρ) {A B : ℂ[X]} (hB : B ≠ 0)
    (hinv : ∀ ξ : ℂ, ξ ^ ρ = 1 → A.comp (C ξ * X) * B = A * B.comp (C ξ * X)) :
    ∃ p q : ℂ[X], q ≠ 0 ∧ A * q.comp (X ^ ρ) = p.comp (X ^ ρ) * B := by
  set μ := nthRootsFinset ρ (1 : ℂ)
  have hmem : ∀ ξ : ℂ, ξ ∈ μ ↔ ξ ^ ρ = 1 := fun ξ => by
    rw [mem_nthRootsFinset hρ]
  have hcompcomp : ∀ (P : ℂ[X]) (a b : ℂ), (P.comp (C a * X)).comp (C b * X) =
      P.comp (C (a * b) * X) := by
    intro P a b
    rw [comp_assoc, mul_comp, C_comp, X_comp, ← mul_assoc, ← C_mul]
  have hcomp_ne : ∀ ξ : ℂ, ξ ≠ 0 → ∀ P : ℂ[X], P ≠ 0 → P.comp (C ξ * X) ≠ 0 := by
    intro ξ hξ P hP h
    have := congrArg (fun p => p.comp (C ξ⁻¹ * X)) h
    simp only [hcompcomp, mul_inv_cancel₀ hξ, map_one, one_mul, comp_X, zero_comp] at this
    exact hP this
  have hμ0 : ∀ ξ ∈ μ, ξ ≠ 0 := fun ξ hξ h0 => by
    rw [hmem, h0, zero_pow hρ.ne'] at hξ; exact zero_ne_one hξ
  have h1μ : (1 : ℂ) ∈ μ := (hmem 1).2 (one_pow _)
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℂ[X], Q = ∏ ξ ∈ μ, B.comp (C ξ * X) := ⟨_, rfl⟩
  obtain ⟨Q', hQ'def⟩ : ∃ Q' : ℂ[X], Q' = ∏ ξ ∈ μ.erase 1, B.comp (C ξ * X) := ⟨_, rfl⟩
  have hQ : Q = B * Q' := by
    rw [hQdef, hQ'def, ← Finset.mul_prod_erase μ _ h1μ]; simp
  have hQ_ne : Q ≠ 0 := by
    rw [hQdef]; exact Finset.prod_ne_zero_iff.2 fun ξ hξ => hcomp_ne ξ (hμ0 ξ hξ) B hB
  -- invariance of `Q`
  have hQinv : ∀ η : ℂ, η ^ ρ = 1 → Q.comp (C η * X) = Q := by
    intro η hη
    have hη0 : η ≠ 0 := hμ0 η ((hmem η).2 hη)
    rw [hQdef, Polynomial.prod_comp]
    simp only [hcompcomp]
    refine Finset.prod_nbij' (· * η) (· * η⁻¹) ?_ ?_ ?_ ?_ ?_
    · intro ξ hξ; simp only [hmem] at hξ ⊢; rw [mul_pow, hξ, hη, one_mul]
    · intro ξ hξ; simp only [hmem] at hξ ⊢; rw [mul_pow, hξ, inv_pow, hη, inv_one, one_mul]
    · intro ξ _; simp [hη0]
    · intro ξ _; simp [hη0]
    · intro ξ _; rfl
  -- the numerator of `H Q`
  set P := A * Q'
  have hE : A * Q = P * B := by rw [hQ]; ring
  have hPinv : ∀ η : ℂ, η ^ ρ = 1 → P.comp (C η * X) = P := by
    intro η hη
    have hη0 : η ≠ 0 := hμ0 η ((hmem η).2 hη)
    have hσ := congrArg (fun p => p.comp (C η * X)) hE
    simp only [mul_comp, hQinv η hη] at hσ
    have hBσ := hcomp_ne η hη0 B hB
    apply mul_right_cancel₀ (mul_ne_zero hBσ hB)
    have h2 := hinv η hη
    linear_combination (-B) * hσ + Q * h2 + B.comp (C η * X) * hE
  obtain ⟨p, hp⟩ := polynomial_descent hρ hPinv
  obtain ⟨q, hq⟩ := polynomial_descent hρ hQinv
  refine ⟨p, q, ?_, ?_⟩
  · rintro rfl; rw [zero_comp] at hq; exact hQ_ne hq
  · rw [← hp, ← hq, hE]

/-- **Lemma 9.24** for `H : RatFunc ℂ`.  If `H(ξ t) = H(t)` for every `ρ`-th root of unity `ξ`
(expressed through the numerator and denominator of `H`), then `H(t) = p(t^ρ) / q(t^ρ)` for
polynomials `p, q` with `q ≠ 0`, i.e. `H = h(t^ρ)` with `h = p / q`. -/
theorem ratFunc_descent {ρ : ℕ} (hρ : 0 < ρ) (H : RatFunc ℂ)
    (hinv : ∀ ξ : ℂ, ξ ^ ρ = 1 →
      H.num.comp (C ξ * X) * H.denom = H.num * H.denom.comp (C ξ * X)) :
    ∃ p q : ℂ[X], q ≠ 0 ∧
      H = algebraMap ℂ[X] (RatFunc ℂ) (p.comp (X ^ ρ)) /
        algebraMap ℂ[X] (RatFunc ℂ) (q.comp (X ^ ρ)) := by
  obtain ⟨p, q, hq, h⟩ := polynomial_pair_descent hρ H.denom_ne_zero hinv
  have hq' : q.comp (X ^ ρ) ≠ 0 := by
    intro h0
    rw [comp_eq_zero_iff] at h0
    rcases h0 with h0 | ⟨_, h0⟩
    · exact hq h0
    · have := congrArg (fun r => coeff r ρ) h0
      simp only [coeff_X_pow_self, coeff_X_pow, coeff_C, if_neg hρ.ne'] at this
      exact one_ne_zero this
  refine ⟨p, q, hq, ?_⟩
  conv_lhs => rw [← RatFunc.num_div_denom H]
  rw [div_eq_div_iff (by simpa using H.denom_ne_zero) (by simpa using hq'), ← map_mul, ← map_mul,
    h]

/-- A complex polynomial without zeros on `ℂ*` is a monomial `c t^k`. -/
theorem polynomial_eq_monomial_of_ne_zero {A : ℂ[X]} (hA : A ≠ 0)
    (h : ∀ t : ℂ, t ≠ 0 → A.eval t ≠ 0) :
    A = C A.leadingCoeff * X ^ A.natDegree := by
  have hroots : A.roots = Multiset.replicate A.roots.card 0 := by
    rw [Multiset.eq_replicate]
    refine ⟨rfl, fun r hr => ?_⟩
    by_contra hr0
    exact h r hr0 ((mem_roots hA).1 hr)
  have hc := C_leadingCoeff_mul_prod_multiset_X_sub_C
    (IsAlgClosed.card_roots_eq_natDegree (k := ℂ) (p := A))
  rw [hroots] at hc
  simp only [Multiset.map_replicate, map_zero, sub_zero, Multiset.prod_replicate] at hc
  rw [IsAlgClosed.card_roots_eq_natDegree] at hc
  exact hc.symm

/-- **Lemma 9.3, final step.**  A nonzero rational function whose numerator and denominator have
no zeros on `ℂ*` (i.e. without zeros or poles on `ℂ*`) is `α t^u` with `α ≠ 0` and `u ∈ ℤ`. -/
theorem ratFunc_eq_monomial {H : RatFunc ℂ} (hH : H ≠ 0)
    (hnum : ∀ t : ℂ, t ≠ 0 → H.num.eval t ≠ 0) (hden : ∀ t : ℂ, t ≠ 0 → H.denom.eval t ≠ 0) :
    ∃ α : ℂ, α ≠ 0 ∧ ∃ u : ℤ, H = RatFunc.C α * RatFunc.X ^ u := by
  have hn0 : H.num ≠ 0 := RatFunc.num_ne_zero hH
  have hd0 : H.denom ≠ 0 := H.denom_ne_zero
  have e1 := polynomial_eq_monomial_of_ne_zero hn0 hnum
  have e2 := polynomial_eq_monomial_of_ne_zero hd0 hden
  refine ⟨H.num.leadingCoeff / H.denom.leadingCoeff,
    div_ne_zero (leadingCoeff_ne_zero.2 hn0) (leadingCoeff_ne_zero.2 hd0),
    (H.num.natDegree : ℤ) - H.denom.natDegree, ?_⟩
  have hX : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
  have hb : (RatFunc.C H.denom.leadingCoeff : RatFunc ℂ) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (RatFunc.C (K := ℂ)).injective]
    exact leadingCoeff_ne_zero.2 hd0
  have key : H = algebraMap ℂ[X] (RatFunc ℂ) H.num / algebraMap ℂ[X] (RatFunc ℂ) H.denom :=
    (RatFunc.num_div_denom H).symm
  conv_lhs => rw [key]
  conv_lhs => rw [e1, e2]
  simp only [map_mul, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X, map_div₀]
  rw [zpow_sub₀ hX, zpow_natCast, zpow_natCast]
  field_simp

end ThreeIM
