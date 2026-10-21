module

public import RequestProject.ThreeIM.RationalDescent

/-!
# Endpoint identities with endpoint pole order one, in numerator/denominator form

In the balanced endpoint configuration with `ρ = 1`, for the values `0, 1, c` and with
`R(0) = S(∞) = 0` and `U = κ t^{-1}`, `V = κ t`, the endpoint identities of Lemma 9.5 say:
`R(0) = 0`; `R(t) ∼ t/κ` at `∞`; `S(∞) = 0`; `S(t) ∼ 1/(κ t)` at `0`.  We express these in terms
of reduced numerators and denominators, as required by `rational_cm_rho_one`.
-/

@[expose] public section

open Filter Set Topology Polynomial

namespace ThreeIM

/-- The trailing coefficient at a simple pole `0` of a quotient of polynomials. -/
lemma tc_quot_simple_pole {P Q E : ℂ[X]} (hQ : Q = X * E) (hE : E.eval 0 ≠ 0)
    (hP : P.eval 0 ≠ 0) {F : ℂ → ℂ} (hF : ∀ s, F s = P.eval s / Q.eval s) :
    meromorphicTrailingCoeffAt F 0 = P.eval 0 / E.eval 0 := by
  have hg : AnalyticAt ℂ (fun s => P.eval s / E.eval s) 0 :=
    (P.differentiable.analyticAt 0).div (E.differentiable.analyticAt 0) hE
  refine hg.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE (n := -1) (div_ne_zero hP hE) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : s ≠ 0 := hs
  rw [hF, hQ, eval_mul, eval_X, sub_zero, smul_eq_mul, zpow_neg_one]
  field_simp

/-- In the balanced endpoint configuration with `ρ = 1` for the values `0, 1, c` and `j = 0`,
the endpoint identities in numerator/denominator form. -/
theorem OppositeData.rho_one_conditions {c κ : ℂ} {R S : RatFunc ℂ}
    (hpair : NormalizedPair {0}ᶜ (ratEval R) (ratEval S) ![0, 1, c])
    (hd : OppositeData ![0, 1, c] R S 0 0 1 κ κ) :
    R.num.eval 0 = 0 ∧ R.num.natDegree = R.denom.natDegree + 1 ∧
      R.num.leadingCoeff / R.denom.leadingCoeff = 1 / κ ∧ S.denom.eval 0 = 0 ∧
      S.num.eval 0 / S.denom.derivative.eval 0 = 1 / κ ∧
      S.num.natDegree < S.denom.natDegree := by
  have hRnc := ne_C_of_nonconst hpair.nonconst_f
  have hSnc := ne_C_of_nonconst hpair.nonconst_g
  have hκ := hd.alpha_ne
  obtain ⟨σ, τ, -, hτ, -, hτo, eS, eR, -⟩ := opposite_endpoint_coefficients hpair one_pos
    hd.denom_zero hd.value_zero hd.order_zero hd.order_infty hd.tendsto_infty hd.aux_U hd.aux_V
  -- `R(0) = 0`
  have hR0 : R.num.eval 0 = 0 := by
    have h := hd.value_zero
    rw [ratEval_eq] at h
    simpa [hd.denom_zero] using h
  -- `S(0) = ∞`
  have hS0 : S.denom.eval 0 = 0 := by
    refine (mult_top_ratEval_pos_iff hSnc 0).1 ?_
    rw [mult_top, hd.order_zero, ← WithTop.LinearOrderedAddCommGroup.coe_neg, WithTop.untop₀_coe]
    norm_num
  have hinvR : (fun s => ratEval R s⁻¹) = fun s => R.num.eval s⁻¹ / R.denom.eval s⁻¹ :=
    funext fun s => ratEval_eq R s⁻¹
  have hinvS : (fun s => ratEval S s⁻¹ - (![0, 1, c] : Fin 3 → ℂ) 0) =
      fun s => S.num.eval s⁻¹ / S.denom.eval s⁻¹ :=
    funext fun s => by simp [ratEval_eq]
  -- degrees
  have hdeg : R.num.natDegree = R.denom.natDegree + 1 := by
    have h := hd.order_infty
    rw [hinvR, order_quot_inv _ _ (num_ne_zero_of_nonconst hRnc) R.denom_ne_zero] at h
    have h' : (R.denom.natDegree : ℤ) - R.num.natDegree = -((1 : ℕ) : ℤ) := by exact_mod_cast h
    omega
  have hSinf : S.num.natDegree < S.denom.natDegree := by
    rw [hinvS, order_quot_inv _ _ (num_ne_zero_of_nonconst hSnc) S.denom_ne_zero] at hτo
    have h' : (S.denom.natDegree : ℤ) - S.num.natDegree = τ := by exact_mod_cast hτo
    omega
  refine ⟨hR0, hdeg, ?_, hS0, ?_, hSinf⟩
  · -- the leading coefficient ratio, from `κ A = 1`
    have hlcD : R.denom.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 R.denom_ne_zero
    have hlcN : R.num.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 (num_ne_zero_of_nonconst hRnc)
    have hg : AnalyticAt ℂ (fun s => (reflect R.num.natDegree R.num).eval s /
        (reflect R.denom.natDegree R.denom).eval s) 0 := by
      refine ((reflect R.num.natDegree R.num).differentiable.analyticAt 0).div
        ((reflect R.denom.natDegree R.denom).differentiable.analyticAt 0) ?_
      rw [eval_reflect_zero]; exact hlcD
    have htc : meromorphicTrailingCoeffAt (fun s => ratEval R s⁻¹) 0 =
        R.num.leadingCoeff / R.denom.leadingCoeff := by
      rw [hg.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE (n := -1) (by
        simp only [eval_reflect_zero]; exact div_ne_zero hlcN hlcD)]
      · simp only [eval_reflect_zero]; rfl
      · filter_upwards [self_mem_nhdsWithin] with s hs
        have hs' : s ≠ 0 := hs
        rw [eval_reflect_of_ne_zero le_rfl hs', eval_reflect_of_ne_zero le_rfl hs', ratEval_eq,
          sub_zero, smul_eq_mul, zpow_neg_one, hdeg, pow_succ]
        by_cases hD : R.denom.eval s⁻¹ = 0
        · simp [hD]
        · field_simp
    rw [htc] at eR
    rw [eq_div_iff hκ]
    push_cast at eR
    linear_combination eR
  · -- the residue at `0`, from `κ B = 1`
    obtain ⟨E, hE, hdvd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd S.denom
      S.denom_ne_zero 0
    obtain ⟨-, hSo⟩ := order_ratEval_of_denom_eq_zero hS0
    rw [hd.order_zero] at hSo
    have hk : S.denom.rootMultiplicity 0 = 1 := by
      have : -((1 : ℕ) : ℤ) = -(S.denom.rootMultiplicity 0 : ℤ) := by exact_mod_cast hSo
      omega
    rw [hk, map_zero, sub_zero, pow_one] at hE
    have hE0 : E.eval 0 ≠ 0 := fun h => hdvd (dvd_iff_isRoot.2 h)
    have hN0 : S.num.eval 0 ≠ 0 := (num_or_denom_ne_zero S 0).resolve_right (not_not.2 hS0)
    have hder : S.denom.derivative.eval 0 = E.eval 0 := by
      rw [hE, derivative_mul, derivative_X]; simp
    have htc := tc_quot_simple_pole hE hE0 hN0 (ratEval_eq S)
    rw [htc] at eS
    rw [hder, eq_div_iff hκ]
    push_cast at eS
    linear_combination eS

end ThreeIM
