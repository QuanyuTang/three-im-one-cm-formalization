module

public import RequestProject.ThreeIM.RationalMoments

/-!
# Fiber moment identities (Lemma 9.9, full statement)

For distinct shared values `v, w` (with `u` the third), the identities `U = α t^{-ρ}` and
`V = β t^ρ` give, off a finite set,
`β t^{2ρ} (R'/(R - v) - R'/(R - w)) - α (S'/(S - v) - S'/(S - w)) = α β (v - w) t^{ρ - 1}`,
the paper's `t^N d log((R-v)/(R-w)) - d log((S-v)/(S-w)) = κ (v - w) t^{ρ-1} dt`.
Expanding both logarithmic derivatives at `∞` (each is a sum of `1/(t - z)` over a fiber) and
comparing coefficients yields `M_{v,ℓ} = M_{w,ℓ}` for `ℓ < 2ρ`, `ℓ ≠ ρ`, together with
`M_{v,ρ} - M_{w,ρ} = (v - w) α`.
-/

@[expose] public section

open Filter Set Topology Polynomial

namespace ThreeIM

/-- Coefficient comparison: if, off a compact set,
`t^{n+1} (Σ_M 1/(t-z) - Σ_{M'} 1/(t-z)) - c' (Σ_K 1/(t-z) - Σ_{K'} 1/(t-z)) = c t^m` with
`m ≤ n`, then the power sums of `M, M'` agree in all degrees `k ≤ n` except `k = n - m`, where
they differ by `c`. -/
theorem moments_of_eventually_eq {M M' K K' : Multiset ℂ} {n m : ℕ} (hm : m ≤ n) {c c' : ℂ}
    (h : ∀ᶠ t in cocompact ℂ, t ^ (n + 1) *
      ((M.map fun z => 1 / (t - z)).sum - (M'.map fun z => 1 / (t - z)).sum) -
      c' * ((K.map fun z => 1 / (t - z)).sum - (K'.map fun z => 1 / (t - z)).sum) = c * t ^ m) :
    (∀ k ≤ n, k ≠ n - m → powerSum M k = powerSum M' k) ∧
      powerSum M (n - m) - powerSum M' (n - m) = c := by
  set d : ℕ → ℂ := fun i => powerSum M i - powerSum M' i with hd
  set Q : ℂ[X] := ∑ i ∈ Finset.range (n + 1), C (d i) * X ^ (n - i) - C c * X ^ m with hQ
  have hK : Tendsto (fun t => (K.map fun z => 1 / (t - z)).sum) (cocompact ℂ) (𝓝 0) := by
    simpa using tendsto_multiset_sum_div_sub K (fun _ => 1)
  have hK' : Tendsto (fun t => (K'.map fun z => 1 / (t - z)).sum) (cocompact ℂ) (𝓝 0) := by
    simpa using tendsto_multiset_sum_div_sub K' (fun _ => 1)
  have hrem := ((((hK.sub hK').const_mul c').sub
    (tendsto_multiset_sum_div_sub M (fun z => z ^ (n + 1)))).add
    (tendsto_multiset_sum_div_sub M' (fun z => z ^ (n + 1))))
  simp only [sub_zero, mul_zero, add_zero] at hrem
  have hQt : Tendsto (fun t => Q.eval t) (cocompact ℂ) (𝓝 0) := by
    refine hrem.congr' ?_
    filter_upwards [h, eventually_notMem_cocompact M, eventually_notMem_cocompact M']
      with t ht h1 h2
    rw [mul_sub, mul_sum_inv_sub_eq M n h1, mul_sum_inv_sub_eq M' n h2] at ht
    rw [hQ, eval_sub, eval_finset_sum]
    simp only [eval_mul, eval_C, eval_pow, eval_X, hd, sub_mul, Finset.sum_sub_distrib]
    linear_combination -ht
  have hQC := polynomial_eq_C_of_tendsto hQt
  rw [map_zero] at hQC
  have hcoeff : ∀ k ≤ n, Q.coeff (n - k) = d k - if n - k = m then c else 0 := by
    intro k hk
    rw [hQ, coeff_sub, finset_sum_coeff, Finset.sum_eq_single k, coeff_C_mul_X_pow,
      coeff_C_mul_X_pow, if_pos rfl]
    · intro i hi hik
      rw [coeff_C_mul_X_pow, if_neg]
      have := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      omega
    · intro hk'
      exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le hk)) hk'
  refine ⟨fun k hk hkm => ?_, ?_⟩
  · have h1 := hcoeff k hk
    rw [hQC, coeff_zero, if_neg (by omega), sub_zero] at h1
    exact sub_eq_zero.1 h1.symm
  · have h1 := hcoeff (n - m) (Nat.sub_le n m)
    rw [hQC, coeff_zero, if_pos (by omega)] at h1
    exact (sub_eq_zero.1 h1.symm)

/-- `P(x) = (x - a i)(x - a i')(x - a l)` for any enumeration of the three indices. -/
lemma cubicP_eq_of_distinct (a : Fin 3 → ℂ) {i i' l : Fin 3} (h1 : i' ≠ i) (h2 : l ≠ i)
    (h3 : l ≠ i') (x : ℂ) : cubicP a x = (x - a i) * (x - a i') * (x - a l) := by
  fin_cases i <;> fin_cases i' <;> fin_cases l <;>
    first | (exfalso; simp_all; done) | (simp only [cubicP, Fin.reduceFinMk, Fin.zero_eta, Fin.mk_one] <;> ring)

/-- The pointwise identity behind Lemma 9.9. -/
lemma logDeriv_identity {f g f' g' t v w u α β : ℂ} {ρ : ℕ} (hρ : 0 < ρ) (ht : t ≠ 0)
    (hfg : f - g ≠ 0) (hfv : f - v ≠ 0) (hfw : f - w ≠ 0) (hfu : f - u ≠ 0)
    (hgv : g - v ≠ 0) (hgw : g - w ≠ 0) (hgu : g - u ≠ 0)
    (hU : t * ((f - g) * f' / ((f - v) * (f - w) * (f - u))) = α * t ^ (-(ρ : ℤ)))
    (hV : t * ((f - g) * g' / ((g - v) * (g - w) * (g - u))) = β * t ^ (ρ : ℤ)) :
    β * t ^ (2 * ρ) * (f' / (f - v) - f' / (f - w)) - α * (g' / (g - v) - g' / (g - w)) =
      α * β * (v - w) * t ^ (ρ - 1) := by
  obtain ⟨r, rfl⟩ : ∃ r, ρ = r + 1 := ⟨ρ - 1, by omega⟩
  rw [zpow_neg, zpow_natCast] at hU
  rw [zpow_natCast] at hV
  have htr : t ^ (r + 1) ≠ 0 := pow_ne_zero _ ht
  have hf' : f' = α * ((f - v) * (f - w) * (f - u)) / (t ^ (r + 1) * t * (f - g)) := by
    field_simp at hU ⊢; linear_combination hU
  have hg' : g' = β * t ^ (r + 1) * ((g - v) * (g - w) * (g - u)) / (t * (f - g)) := by
    field_simp at hV ⊢; linear_combination hV
  subst hf' hg'
  rw [Nat.add_sub_cancel, show 2 * (r + 1) = (r + 1) + (r + 1) by ring, pow_add]
  field_simp
  ring
lemma ratEval_sub_const_eq (R : RatFunc ℂ) (v : ℂ) {t : ℂ} (hD : R.denom.eval t ≠ 0) :
    ratEval R t - v = (R.num - C v * R.denom).eval t / R.denom.eval t := by
  rw [ratEval_eq]; simp only [eval_sub, eval_mul, eval_C]; field_simp

lemma ratEval_sub_ratEval_eq (R S : RatFunc ℂ) {t : ℂ} (hR : R.denom.eval t ≠ 0)
    (hS : S.denom.eval t ≠ 0) :
    ratEval R t - ratEval S t = (coincPoly R S).eval t / (R.denom.eval t * S.denom.eval t) := by
  rw [ratEval_eq, ratEval_eq, coincPoly]; simp only [eval_sub, eval_mul]; field_simp

/-- **Lemma 9.9** (fiber moment identities).  In the endpoint configuration of Lemma 9.5
(`U = α t^{-ρ}`, `V = β t^ρ`), for two distinct shared values `a i, a i'` the fiber moments of
`R` satisfy `M_{a i,ℓ} = M_{a i',ℓ}` for all `ℓ < 2ρ` with `ℓ ≠ ρ`, and
`M_{a i,ρ} - M_{a i',ρ} = (a i - a i') α`. -/
theorem OppositeData.fiberMoments_full {a : Fin 3 → ℂ} {R S : RatFunc ℂ} {j k : Fin 3} {ρ : ℕ}
    {α β : ℂ} (hpair : NormalizedPair {0}ᶜ (ratEval R) (ratEval S) a)
    (hd : OppositeData a R S j k ρ α β) {i i' : Fin 3} (hii : i ≠ i') :
    (∀ ℓ < 2 * ρ, ℓ ≠ ρ → fiberMoment R (a i) ℓ = fiberMoment R (a i') ℓ) ∧
      fiberMoment R (a i) ρ - fiberMoment R (a i') ρ = (a i - a i') * α := by
  obtain ⟨l, hli, hli'⟩ := exists_third i i'
  have hρ := hd.rho_pos
  have hβ := hd.beta_ne
  have hRnc := ne_C_of_nonconst hpair.nonconst_f
  have hSnc := ne_C_of_nonconst hpair.nonconst_g
  set v := a i
  set w := a i'
  set u := a l
  have hRv := num_sub_ne_zero (hRnc v)
  have hRw := num_sub_ne_zero (hRnc w)
  have hRu := num_sub_ne_zero (hRnc u)
  have hSv := num_sub_ne_zero (hSnc v)
  have hSw := num_sub_ne_zero (hSnc w)
  have hSu := num_sub_ne_zero (hSnc u)
  have hP : ∀ x, cubicP a x = (x - v) * (x - w) * (x - u) :=
    cubicP_eq_of_distinct a (Ne.symm hii) hli hli'
  have key : ∀ᶠ t in cocompact ℂ, t ^ (2 * ρ - 1 + 1) *
      (((R.num - C v * R.denom).roots.map fun z => 1 / (t - z)).sum -
        ((R.num - C w * R.denom).roots.map fun z => 1 / (t - z)).sum) -
      α / β * (((S.num - C v * S.denom).roots.map fun z => 1 / (t - z)).sum -
        ((S.num - C w * S.denom).roots.map fun z => 1 / (t - z)).sum) =
      ((v - w) * α) * t ^ (ρ - 1) := by
    filter_upwards [cocompact_le_cofinite hd.aux_U, cocompact_le_cofinite hd.aux_V,
      (isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact,
      eventually_eval_ne_zero_cocompact R.denom_ne_zero,
      eventually_eval_ne_zero_cocompact S.denom_ne_zero,
      eventually_eval_ne_zero_cocompact (coincPoly_ne_zero hpair),
      eventually_eval_ne_zero_cocompact hRv, eventually_eval_ne_zero_cocompact hRw,
      eventually_eval_ne_zero_cocompact hRu, eventually_eval_ne_zero_cocompact hSv,
      eventually_eval_ne_zero_cocompact hSw, eventually_eval_ne_zero_cocompact hSu,
      logDeriv_ratEval_eventually R hRv hRw, logDeriv_ratEval_eventually S hSv hSw]
      with t hU hV ht hDR hDS hco h1 h2 h3 h4 h5 h6 hlR hlS
    have ht0 : t ≠ 0 := ht
    rw [Nat.sub_add_cancel (by omega), ← hlR, ← hlS]
    have hfg : ratEval R t - ratEval S t ≠ 0 := by
      rw [ratEval_sub_ratEval_eq R S hDR hDS]; exact div_ne_zero hco (mul_ne_zero hDR hDS)
    have hne : ∀ (T : RatFunc ℂ) (x : ℂ), T.denom.eval t ≠ 0 →
        (T.num - C x * T.denom).eval t ≠ 0 → ratEval T t - x ≠ 0 := by
      intro T x hD hN
      rw [ratEval_sub_const_eq T x hD]; exact div_ne_zero hN hD
    unfold auxU at hU
    unfold auxV at hV
    rw [hP] at hU hV
    have := logDeriv_identity hρ ht0 hfg (hne R v hDR h1) (hne R w hDR h2) (hne R u hDR h3)
      (hne S v hDS h4) (hne S w hDS h5) (hne S u hDS h6) hU hV
    field_simp
    linear_combination this
  obtain ⟨h1, h2⟩ := moments_of_eventually_eq (by omega : ρ - 1 ≤ 2 * ρ - 1) key
  have hnm : 2 * ρ - 1 - (ρ - 1) = ρ := by omega
  rw [hnm] at h1 h2
  exact ⟨fun ℓ hℓ hℓρ => h1 ℓ (by omega) hℓρ, h2⟩

end ThreeIM
