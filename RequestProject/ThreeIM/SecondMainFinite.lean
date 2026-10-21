module

public import RequestProject.ThreeIM.Ramification
public import RequestProject.ThreeIM.FiniteRamification
public import RequestProject.ThreeIM.SecondMainProximity
public import RequestProject.ThreeIM.FiniteExceptions
public import RequestProject.ThreeIM.LogDerivative

/-!
# The second main inequality for finite targets, with the pole term retained

The finite-target proximity estimate, the first main theorem, and the exact
ramification counts give the inequality before any exceptional sets are used.
The logarithmic-derivative lemma then bounds the finitely many error terms.
-/

@[expose] public section

open Set MeasureTheory

namespace ThreeIM

noncomputable def secondMainFiniteConstant (f : ℂ → ℂ) {q : ℕ}
    (a : Fin q → ℂ) : ℝ :=
  finiteValueSeparationConstant a + inverseFirstMainConstant (deriv f) +
    ∑ i, finiteFirstMainConstant f (a i)

theorem secondMainFiniteConstant_nonneg (f : ℂ → ℂ) {q : ℕ} (a : Fin q → ℂ) :
    0 ≤ secondMainFiniteConstant f a := by
  exact add_nonneg
    (add_nonneg (finiteValueSeparationConstant_nonneg a)
      (inverseFirstMainConstant_nonneg _))
    (Finset.sum_nonneg fun i _ => finiteFirstMainConstant_nonneg f (a i))

theorem second_main_finite_with_errors {f : ℂ → ℂ} (hf : IsNonconstMeroOn f univ)
    {q : ℕ} (a : Fin q → ℂ) (ha : Function.Injective a) {r : ℝ} (hr : 1 ≤ r) :
    ((q : ℝ) - 1) * charT f r ≤
      (∑ i, reducedCounting f (a i) r) + reducedCounting f ⊤ r +
        ValueDistribution.proximity (fun z => deriv f z / (f z - 0)) ⊤ r +
        (∑ i, ValueDistribution.proximity (fun z => deriv f z / (f z - a i)) ⊤ r) +
        secondMainFiniteConstant f a := by
  have hm : Meromorphic f := fun z => hf.1 z (mem_univ z)
  have hmain := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin q)))
    (fun i _ => charT_le_proximity_add_count_finite hm (a i) r)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hmain
  have hprox := proximity_sum_finite_le hf a ha (show r ≠ 0 by linarith)
  have hinv := proximity_inv_add_count_le hm.deriv r
  have hderiv := charT_deriv_le_reduced_poles hf hr
  have hram := sum_logCounting_sub_reducedCounting_le_deriv_zero hf a ha hr
  rw [Finset.sum_sub_distrib] at hram
  unfold secondMainFiniteConstant
  linarith

theorem second_main_finite {f : ℂ → ℂ} (hf : IsNonconstMeroOn f univ)
    {q : ℕ} (a : Fin q → ℂ) (ha : Function.Injective a) :
    ∃ C : ℝ, OutsideFiniteMeasure fun r =>
      ((q : ℝ) - 1) * charT f r ≤
        (∑ i, reducedCounting f (a i) r) + reducedCounting f ⊤ r +
          C * Real.log (Real.exp 1 + r * charT f r) := by
  classical
  obtain ⟨C₀, hC₀⟩ := log_derivative_lemma hf 0
  have hlog : ∀ i : Fin q, ∃ C : ℝ, OutsideFiniteMeasure fun r =>
      ValueDistribution.proximity (fun z => deriv f z / (f z - a i)) ⊤ r ≤
        C * Real.log (Real.exp 1 + r * charT f r) := fun i => log_derivative_lemma hf (a i)
  choose C hC using hlog
  refine ⟨C₀ + (∑ i, C i) + secondMainFiniteConstant f a, ?_⟩
  have hC₀' : OutsideFiniteMeasure fun r =>
      ValueDistribution.proximity (fun z => deriv f z / (f z - 0)) ⊤ r ≤
        C₀ * Real.log (Real.exp 1 + r * charT f r) := hC₀
  refine ((hC₀'.conj (OutsideFiniteMeasure.fintype_all hC)).conj
    (OutsideFiniteMeasure.eventually_ge 1)).map ?_
  intro r h
  obtain ⟨⟨hzero, hall⟩, hr⟩ := h
  have hfinite := second_main_finite_with_errors hf a ha hr
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin q))) => hall i)
  rw [← Finset.sum_mul] at hsum
  have hT : 0 ≤ charT f r := ValueDistribution.characteristic_nonneg hr
  have hlog1 : 1 ≤ Real.log (Real.exp 1 + r * charT f r) := by
    have h := Real.log_le_log (Real.exp_pos 1)
      (show Real.exp 1 ≤ Real.exp 1 + r * charT f r by
        nlinarith [mul_nonneg (show 0 ≤ r by linarith) hT])
    rwa [Real.log_exp] at h
  have hconstant := le_mul_of_one_le_right (secondMainFiniteConstant_nonneg f a) hlog1
  nlinarith

end ThreeIM
