module

public import RequestProject.ThreeIM.Counting
public import RequestProject.ThreeIM.Cartan
public import RequestProject.ThreeIM.PoissonBound

/-!
# Small entire functions (Lemma 4.11)

An entire function `H` with `T(r, H) = O(log r)` outside a set of finite linear measure is a
polynomial.  The proof uses the monotonicity of the characteristic and the bound
`log⁺ M(r, H) ≤ 3 T(2r, H)` (External theorem 2.3), and Cauchy's estimates.
-/

@[expose] public section

open Filter Set Topology Nat

namespace ThreeIM

/-- An entire function whose Taylor coefficients at `0` vanish beyond `N` is a polynomial. -/
lemma polynomial_of_iteratedDeriv_eq_zero {H : ℂ → ℂ} (hH : Differentiable ℂ H) {N : ℕ}
    (hN : ∀ n, N < n → iteratedDeriv n H 0 = 0) :
    ∃ p : Polynomial ℂ, ∀ z, H z = p.eval z := by
  refine ⟨∑ n ∈ Finset.range (N + 1),
    Polynomial.C ((n ! : ℂ)⁻¹ * iteratedDeriv n H 0) * Polynomial.X ^ n, fun z => ?_⟩
  rw [← Complex.taylorSeries_eq_of_entire' (c := 0) (z := z) hH,
    tsum_eq_sum (s := Finset.range (N + 1))]
  · simp [Polynomial.eval_finset_sum]
  · intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    simp [hN n (by omega)]

/-- Every interval `[r, r + 1]` with `r` large meets the complement of a set of finite measure. -/
lemma exists_not_mem_of_finite_measure {E : Set ℝ} (hE : MeasurableSet E)
    (hvol : MeasureTheory.volume E < ⊤) :
    ∃ r₁ : ℝ, ∀ r ≥ r₁, ∃ R, r ≤ R ∧ R ≤ r + 1 ∧ R ∉ E := by
  set s : ℕ → Set ℝ := fun n => E ∩ Ici (n : ℝ)
  have hlim := MeasureTheory.tendsto_measure_iInter_atTop (μ := MeasureTheory.volume) (s := s)
    (fun n => (hE.inter measurableSet_Ici).nullMeasurableSet)
    (fun m n hmn => inter_subset_inter_right _ (Ici_subset_Ici.2 (by exact_mod_cast hmn)))
    ⟨0, ne_top_of_le_ne_top hvol.ne (MeasureTheory.measure_mono inter_subset_left)⟩
  have hempty : (⋂ n, s n) = ∅ := by
    ext x
    simp only [mem_iInter, mem_empty_iff_false, iff_false, not_forall]
    obtain ⟨n, hn⟩ := exists_nat_gt x
    exact ⟨n, fun h => by simp [s] at h; linarith [h.2]⟩
  rw [hempty, MeasureTheory.measure_empty] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds (show (0 : ENNReal) < 1 by norm_num))).exists
  refine ⟨n, fun r hr => ?_⟩
  by_contra hcon
  push_neg at hcon
  have hsub : Icc r (r + 1) ⊆ s n := fun x hx => ⟨hcon x hx.1 hx.2, le_trans hr hx.1⟩
  have := MeasureTheory.measure_mono (μ := MeasureTheory.volume) hsub
  rw [Real.volume_Icc, show r + 1 - r = 1 by ring, ENNReal.ofReal_one] at this
  exact absurd (lt_of_le_of_lt this hn) (lt_irrefl _)

lemma le_exp_posLog (x : ℝ) : x ≤ Real.exp (Real.posLog x) := by
  rcases le_or_gt x 1 with hx | hx
  · exact hx.trans (Real.one_le_exp (Real.posLog_nonneg))
  · rw [Real.posLog_apply, max_eq_right (Real.log_nonneg hx.le), Real.exp_log (by linarith)]

/-- **Lemma 4.11** (small entire functions).  If an entire function `H` satisfies
`T(r, H) = O(log r)` outside a set of finite linear measure, then it is a polynomial. -/
theorem polynomial_of_small_charT {H : ℂ → ℂ} (hH : Differentiable ℂ H) {C : ℝ}
    (hT : OutsideFiniteMeasure fun r => charT H r ≤ C * Real.log r) :
    ∃ p : Polynomial ℂ, ∀ z, H z = p.eval z := by
  obtain ⟨E, hEm, hEv, r₀, hr₀⟩ := hT
  obtain ⟨r₁, hr₁⟩ := exists_not_mem_of_finite_measure hEm hEv
  set C' := max C 0
  set ρ := max (max r₀ r₁) 1
  have hHm : MeromorphicOn H univ := fun z _ => (hH.analyticAt z).meromorphicAt
  -- `T(r) ≤ C' log (r + 1)` for large `r`
  have hTr : ∀ r ≥ ρ, charT H r ≤ C' * Real.log (r + 1) := by
    intro r hr
    have hr0 : r₀ ≤ r := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hr
    have hr1 : r₁ ≤ r := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hr
    have hr2 : 1 ≤ r := le_trans (le_max_right _ _) hr
    obtain ⟨R, hrR, hRr, hRE⟩ := hr₁ r hr1
    have h1 : charT H r ≤ charT H R := charT_mono hHm (by linarith) hrR
    have h2 : charT H R ≤ C * Real.log R := hr₀ R (hr0.trans hrR) hRE
    have hlogR : 0 ≤ Real.log R := Real.log_nonneg (by linarith)
    have h3 : C * Real.log R ≤ C' * Real.log (r + 1) :=
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hlogR).trans
        (mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) hRr) (le_max_right _ _))
    linarith
  -- polynomial bound on circles
  set K : ℕ := ⌈3 * C'⌉₊
  have hbound : ∀ r ≥ ρ, ∀ z : ℂ, ‖z‖ = r → ‖H z‖ ≤ (3 * r) ^ K := by
    intro r hr z hz
    have hr1 : 1 ≤ r := le_trans (le_max_right _ _) hr
    have h1 := entire_posLog_le hH hr1 (show r < 2 * r by linarith) hz
    have h2 := hTr (2 * r) (by linarith)
    rw [show (2 * r + r) / (2 * r - r) = 3 by field_simp; ring] at h1
    have h3 : Real.posLog ‖H z‖ ≤ 3 * C' * Real.log (2 * r + 1) := by nlinarith
    calc ‖H z‖ ≤ Real.exp (3 * C' * Real.log (2 * r + 1)) :=
          (le_exp_posLog _).trans (Real.exp_le_exp.2 h3)
      _ = (2 * r + 1) ^ (3 * C') := by
          rw [Real.rpow_def_of_pos (by linarith)]; ring_nf
      _ ≤ (3 * r) ^ (3 * C') :=
          Real.rpow_le_rpow (by linarith) (by linarith) (by positivity)
      _ ≤ (3 * r) ^ (K : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (Nat.le_ceil _)
      _ = (3 * r) ^ K := Real.rpow_natCast _ _
  -- Cauchy's estimates kill the Taylor coefficients of order `> K`
  refine polynomial_of_iteratedDeriv_eq_zero hH (N := K) fun n hn => ?_
  have hcauchy : ∀ r ≥ ρ, ‖iteratedDeriv n H 0‖ ≤ n ! * 3 ^ K / r := by
    intro r hr
    have hr1 : 1 ≤ r := le_trans (le_max_right _ _) hr
    have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n (c := 0)
      (by linarith : (0 : ℝ) < r) hH.diffContOnCl
      (fun z hz => hbound r hr z (by simpa using hz))
    refine h.trans ?_
    have hrn : r ^ n = r ^ K * r ^ (n - K) := by rw [← pow_add]; congr 1; omega
    have hge : r ≤ r ^ (n - K) := by
      calc r = r ^ 1 := (pow_one r).symm
        _ ≤ r ^ (n - K) := pow_le_pow_right₀ hr1 (by omega)
    rw [mul_pow, hrn, div_le_div_iff₀ (by positivity) (by positivity)]
    have hpos : 0 ≤ (n ! : ℝ) * 3 ^ K * r ^ K := by positivity
    nlinarith
  apply norm_le_zero_iff.1
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set r := max ρ (n ! * 3 ^ K / ε + 1)
  have hr : ρ ≤ r := le_max_left _ _
  have hrpos : 0 < r := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  have hr2 : n ! * 3 ^ K / ε < r := lt_of_lt_of_le (lt_add_one _) (le_max_right _ _)
  have : (n ! : ℝ) * 3 ^ K / r ≤ ε := by
    rw [div_le_iff₀ hrpos]
    rw [div_lt_iff₀ hε] at hr2
    linarith
  linarith [hcauchy r hr]

end ThreeIM
