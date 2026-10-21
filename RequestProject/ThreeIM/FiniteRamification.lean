module

public import RequestProject.ThreeIM.Holomorphic
public import RequestProject.ThreeIM.Counting

/-!
# Local ramification over finitely many distinct finite values

At a given source point, at most one of the distinct finite target fibers has
positive multiplicity. If its multiplicity is `m`, the derivative has order
`m - 1`. Thus the sum of the finite-fiber excesses is bounded by the positive
part of the derivative's order. All statements use meromorphic germs, so no
choice of a value at a pole or a removable singularity affects the result.
-/

@[expose] public section

open scoped BigOperators

namespace ThreeIM

/-- At a positive finite fiber, every different finite target has multiplicity zero. -/
lemma mult_finite_eq_zero_of_ne_of_pos {f : ℂ → ℂ} {z c d : ℂ}
    (hf : MeromorphicAt f z) (hcd : c ≠ d) (hpos : 0 < mult f (c : Sphere) z) :
    mult f (d : Sphere) z = 0 := by
  have horder : 0 < meromorphicOrderAt (fun w => f w - c) z := by
    rw [order_sub_eq_mult hpos]
    exact_mod_cast hpos
  have hzero := order_sub_const_eq_zero_of_pos hf hcd horder
  simp [mult_coe, hzero]

/-- The derivative's order at a finite fiber of positive multiplicity `m` is `m - 1`. -/
lemma order_deriv_at_finite_fiber {f : ℂ → ℂ} {z c : ℂ}
    (hf : MeromorphicAt f z) (hpos : 0 < mult f (c : Sphere) z) :
    meromorphicOrderAt (deriv f) z =
      (((mult f (c : Sphere) z : ℤ) - 1 : ℤ) : WithTop ℤ) :=
  order_deriv_of_order_sub hf (Nat.succ_le_of_lt hpos) (order_sub_eq_mult hpos)

/-- Local finite-fiber ramification bound; only meromorphy at the source point is needed. -/
theorem finite_fiber_ramification_le_at {f : ℂ → ℂ} {z : ℂ}
    (hf : MeromorphicAt f z) {q : ℕ} (a : Fin q → ℂ) (ha : Function.Injective a) :
    (∑ i, ((mult f (a i : Sphere) z : ℤ) -
      (if 0 < mult f (a i : Sphere) z then 1 else 0))) ≤
        ((meromorphicOrderAt (deriv f) z).untop₀)⁺ := by
  classical
  by_cases hex : ∃ j : Fin q, 0 < mult f (a j : Sphere) z
  · obtain ⟨j, hj⟩ := hex
    have hother : ∀ i : Fin q, i ≠ j → mult f (a i : Sphere) z = 0 := by
      intro i hij
      exact mult_finite_eq_zero_of_ne_of_pos hf (fun h => hij (ha h).symm) hj
    have hsum :
        (∑ i, ((mult f (a i : Sphere) z : ℤ) -
          (if 0 < mult f (a i : Sphere) z then 1 else 0))) =
            (mult f (a j : Sphere) z : ℤ) - 1 := by
      calc
        (∑ i, ((mult f (a i : Sphere) z : ℤ) -
            (if 0 < mult f (a i : Sphere) z then 1 else 0))) =
            (mult f (a j : Sphere) z : ℤ) -
              (if 0 < mult f (a j : Sphere) z then 1 else 0) := by
          apply Finset.sum_eq_single j
          · intro i _ hij
            simp [hother i hij]
          · simp
        _ = (mult f (a j : Sphere) z : ℤ) - 1 := by rw [if_pos hj]
    rw [hsum, order_deriv_at_finite_fiber hf hj, WithTop.untop₀_coe]
    exact le_posPart _
  · have hzero : ∀ i : Fin q, mult f (a i : Sphere) z = 0 := by
      intro i
      exact Nat.eq_zero_of_not_pos (fun hi => hex ⟨i, hi⟩)
    have hsum :
        (∑ i, ((mult f (a i : Sphere) z : ℤ) -
          (if 0 < mult f (a i : Sphere) z then 1 else 0))) = 0 := by
      simp [hzero]
    rw [hsum]
    exact posPart_nonneg _

/-- The finite-fiber ramification inequality for a nonconstant meromorphic function on `ℂ`. -/
theorem finite_fiber_ramification_le {f : ℂ → ℂ} (hf : IsNonconstMeroOn f Set.univ)
    {q : ℕ} (a : Fin q → ℂ) (ha : Function.Injective a) (z : ℂ) :
    (∑ i, ((mult f (a i : Sphere) z : ℤ) -
      (if 0 < mult f (a i : Sphere) z then 1 else 0))) ≤
        ((meromorphicOrderAt (deriv f) z).untop₀)⁺ :=
  finite_fiber_ramification_le_at (hf.1 z (Set.mem_univ z)) a ha

private lemma finiteRamification_sum_apply {α : Type*} (s : Finset α)
    (D : α → Function.locallyFinsupp ℂ ℤ) (z : ℂ) :
    (∑ i ∈ s, D i) z = ∑ i ∈ s, D i z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Function.locallyFinsuppWithin.coe_add, Pi.add_apply,
      ih, Finset.sum_insert hi]

/-- The sum of finite fiber-excess divisors is bounded by the derivative's zero divisor. -/
theorem finite_fiber_divisor_ramification_le {f : ℂ → ℂ}
    (hf : IsNonconstMeroOn f Set.univ) {q : ℕ} (a : Fin q → ℂ)
    (ha : Function.Injective a) :
    (∑ i, (fiberDivisor f (a i : Sphere) - reducedFiberDivisor f (a i : Sphere))) ≤
      (MeromorphicOn.divisor (deriv f) Set.univ)⁺ := by
  intro z
  have hderiv : MeromorphicOn (deriv f) Set.univ :=
    fun w _ => (hf.1 w (Set.mem_univ w)).deriv
  rw [finiteRamification_sum_apply]
  simp only [Function.locallyFinsuppWithin.coe_sub, Pi.sub_apply,
    fiberDivisor_apply hf.1, reducedFiberDivisor_apply hf.1,
    Function.locallyFinsuppWithin.posPart_apply,
    MeromorphicOn.divisor_apply hderiv (Set.mem_univ z)]
  exact finite_fiber_ramification_le hf a ha z

/-- Integrated finite-fiber ramification bound for `r ≥ 1`. -/
theorem sum_logCounting_sub_reducedCounting_le_deriv_zero {f : ℂ → ℂ}
    (hf : IsNonconstMeroOn f Set.univ) {q : ℕ} (a : Fin q → ℂ)
    (ha : Function.Injective a) {r : ℝ} (hr : 1 ≤ r) :
    (∑ i, (ValueDistribution.logCounting f (a i : Sphere) r -
      reducedCounting f (a i : Sphere) r)) ≤
        ValueDistribution.logCounting (deriv f) 0 r := by
  have h := Function.locallyFinsuppWithin.logCounting_le
    (finite_fiber_divisor_ramification_le hf a ha) hr
  simp only [map_sum, map_sub, Finset.sum_apply, Pi.sub_apply] at h
  have hred : ∀ i : Fin q,
      (reducedFiberDivisor f (a i : Sphere)).logCounting r =
        reducedCounting f (a i : Sphere) r := fun i =>
    (reducedCounting_eq_reducedFiberDivisor hf.1 (a i : Sphere)
      (le_trans zero_le_one hr)).symm
  simpa only [fiberDivisor_logCounting, hred, ← ValueDistribution.logCounting_zero] using h

/-- The same integrated bound with the two sums separated. -/
theorem sum_logCounting_sub_sum_reducedCounting_le_deriv_zero {f : ℂ → ℂ}
    (hf : IsNonconstMeroOn f Set.univ) {q : ℕ} (a : Fin q → ℂ)
    (ha : Function.Injective a) {r : ℝ} (hr : 1 ≤ r) :
    (∑ i, ValueDistribution.logCounting f (a i : Sphere) r) -
      (∑ i, reducedCounting f (a i : Sphere) r) ≤
        ValueDistribution.logCounting (deriv f) 0 r := by
  simpa only [Finset.sum_sub_distrib] using
    sum_logCounting_sub_reducedCounting_le_deriv_zero hf a ha hr

end ThreeIM
