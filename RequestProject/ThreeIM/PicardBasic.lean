module

public import RequestProject.ThreeIM.SecondMain
public import RequestProject.ThreeIM.SmallEntire
public import RequestProject.ThreeIM.PicardSupport
public import RequestProject.ThreeIM.Normalization
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The entire-function case of little Picard

The second main theorem makes an entire function omitting two finite values
have logarithmic characteristic. Cauchy's estimates then make it a polynomial,
and the fundamental theorem of algebra finishes the argument. Every step uses
germs for multiplicities and actual holomorphic representatives for evaluation.
-/

@[expose] public section

open Filter Set MeasureTheory Real Topology Polynomial

namespace ThreeIM

theorem OutsideFiniteMeasure.eventually_cofinite {P : ℝ → Prop}
    (h : OutsideFiniteMeasure P) : ∀ᶠ r in volume.cofinite ⊓ atTop, P r := by
  obtain ⟨E, _, hEv, r₀, hP⟩ := h
  have hE : ∀ᶠ r in volume.cofinite, r ∉ E := by
    apply Measure.mem_cofinite.2
    change volume Eᶜᶜ < ⊤
    simpa only [compl_compl] using hEv
  filter_upwards [mem_inf_of_left hE, mem_inf_of_right (eventually_ge_atTop r₀)]
    with r hrE hr
  exact hP r hr hrE

theorem OutsideFiniteMeasure.of_eventually_cofinite {P : ℝ → Prop}
    (h : ∀ᶠ r in volume.cofinite ⊓ atTop, P r) : OutsideFiniteMeasure P := by
  obtain ⟨s, hs, t, ht, hst⟩ := Filter.mem_inf_iff.1 h
  obtain ⟨r₀, hr₀⟩ := Filter.mem_atTop_sets.1 ht
  let E := toMeasurable volume sᶜ
  refine ⟨E, measurableSet_toMeasurable _ _, ?_, r₀, ?_⟩
  · simpa only [E, measure_toMeasurable] using Measure.mem_cofinite.1 hs
  · intro r hr hrE
    have hrs : r ∈ s := by
      by_contra hnot
      exact hrE (subset_toMeasurable volume sᶜ hnot)
    have hmem : r ∈ s ∩ t := ⟨hrs, hr₀ r hr⟩
    rw [← hst] at hmem
    exact hmem

theorem reducedCounting_eq_zero_of_mult_zero {f : ℂ → ℂ} {b : Sphere}
    (h : ∀ z, mult f b z = 0) (r : ℝ) : reducedCounting f b r = 0 := by
  simp [reducedCounting, h]

theorem mult_top_eq_zero_of_entire {H : ℂ → ℂ} (hH : Differentiable ℂ H) (z : ℂ) :
    mult H ⊤ z = 0 := by
  rw [mult_top]
  exact untop₀_toNat_neg_eq_zero_of_nonneg (hH.analyticAt z).meromorphicOrderAt_nonneg

theorem mult_pos_of_entire_eq {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    (hHn : IsNonconstMeroOn H univ) {z a : ℂ} (hz : H z = a) :
    0 < mult H (a : Sphere) z := by
  have ha : AnalyticAt ℂ (fun w => H w - a) z := (hH.analyticAt z).sub analyticAt_const
  have ht : Tendsto (fun w => H w - a) (𝓝[≠] z) (𝓝 0) := by
    simpa only [hz, sub_self] using ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hp := (tendsto_zero_iff_meromorphicOrderAt_pos ha.meromorphicAt).1 ht
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 (hHn.2 z (mem_univ z) a)
  have hnpos : 0 < n := by
    rw [← hn] at hp
    exact_mod_cast hp
  simpa only [mult_coe, ← hn, WithTop.untop₀_coe] using Int.pos_iff_toNat_pos.1 hnpos

theorem charT_le_log_of_entire_omits_two {H : ℂ → ℂ}
    (hH : Differentiable ℂ H) (hHn : IsNonconstMeroOn H univ)
    (a : Fin 2 → ℂ) (ha : Function.Injective a)
    (homit : ∀ i z, mult H (a i : Sphere) z = 0) :
    ∃ K : ℝ, OutsideFiniteMeasure fun r => charT H r ≤ K * Real.log r := by
  obtain ⟨C, hC⟩ := second_main_finite hHn a ha
  have hC' : OutsideFiniteMeasure fun r =>
      charT H r ≤ C * Real.log (Real.exp 1 + r * charT H r) :=
    hC.map fun r hr => by
      simpa only [Nat.cast_ofNat, show (2 : ℝ) - 1 = 1 by norm_num, one_mul,
        reducedCounting_eq_zero_of_mult_zero (homit _),
        reducedCounting_eq_zero_of_mult_zero (mult_top_eq_zero_of_entire hH),
        Finset.sum_const_zero, zero_add] using hr
  have hbound : ∀ᶠ r in volume.cofinite ⊓ atTop,
      charT H r ≤ (3 * |C|) * (Real.posLog (charT H r) + Real.log r) := by
    filter_upwards [hC'.eventually_cofinite,
      mem_inf_of_right (eventually_ge_atTop (Real.exp 1))] with r hr hre
    have hr1 : 1 ≤ r := by linarith [Real.add_one_le_exp 1]
    have hlog0 : 0 ≤ Real.log (Real.exp 1 + r * charT H r) := by
      apply Real.log_nonneg
      have hT : 0 ≤ charT H r := ValueDistribution.characteristic_nonneg hr1
      nlinarith [mul_nonneg (show 0 ≤ r by linarith) hT, Real.add_one_le_exp 1]
    have hlarge := PicardSupport.log_error_le (T := charT H r) hre
    have h₁ := mul_le_mul_of_nonneg_right (le_abs_self C) hlog0
    have h₂ := mul_le_mul_of_nonneg_left hlarge (abs_nonneg C)
    nlinarith
  obtain ⟨K, _, hK⟩ := PicardSupport.eventually_le_log_of_le_posLog hbound
  exact ⟨K, OutsideFiniteMeasure.of_eventually_cofinite hK⟩

/-- Entire nonconstant meromorphic germs cannot omit two distinct finite values. -/
theorem entire_omits_two_impossible {H : ℂ → ℂ}
    (hH : Differentiable ℂ H) (hHn : IsNonconstMeroOn H univ)
    (a : Fin 2 → ℂ) (ha : Function.Injective a)
    (homit : ∀ i z, mult H (a i : Sphere) z = 0) : False := by
  classical
  obtain ⟨K, hK⟩ := charT_le_log_of_entire_omits_two hH hHn a ha homit
  obtain ⟨p, hp⟩ := polynomial_of_small_charT hH hK
  let Q := p - Polynomial.C (a 0)
  by_cases hQ : Q.degree = 0
  · have hQc := Polynomial.eq_C_of_degree_le_zero hQ.le
    let c := Q.coeff 0 + a 0
    have hconstant : ∀ z, H z = c := by
      intro z
      have hz := congrArg (fun q : ℂ[X] => q.eval z) hQc
      simp only [Q, Polynomial.eval_sub, Polynomial.eval_C] at hz
      rw [hp z]
      exact sub_eq_iff_eq_add.1 hz
    apply hHn.2 0 (mem_univ 0) c
    apply meromorphicOrderAt_eq_top_iff.2
    exact Eventually.of_forall fun z => by rw [hconstant z]; simp
  · obtain ⟨z, hz⟩ := IsAlgClosed.exists_root Q hQ
    have hHz : H z = a 0 := by
      rw [hp z]
      exact sub_eq_zero.1 (by simpa only [Q, Polynomial.IsRoot.def,
        Polynomial.eval_sub, Polynomial.eval_C] using hz)
    have hpos := mult_pos_of_entire_eq hH hHn hHz
    rw [homit 0 z] at hpos
    exact lt_irrefl 0 hpos

end ThreeIM
