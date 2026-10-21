module

public import RequestProject.ThreeIM.NevanlinnaAux
public import RequestProject.ThreeIM.SecondMain
public import RequestProject.ThreeIM.FiniteRamification

/-!
# Counting shared values and comparing characteristics

The reduced finite shared fibers contribute zeros of f-g. CM sharing at
infinity sharpens the pole estimate for f-g. Combined with the second main
theorem, these give the usual four-value characteristic comparisons without
growth assumptions. No unfinished sharing theorem is imported.
-/

@[expose] public section

open Filter Set Topology ValueDistribution Real MeasureTheory Function

namespace ThreeIM

/-- Integer bookkeeping: `(-x).untop₀.toNat = (x.untop₀)⁻`. -/
lemma toNat_untop₀_neg_eq (x : WithTop ℤ) : ((-x).untop₀.toNat : ℤ) = (x.untop₀)⁻ := by
  induction x using WithTop.recTopCoe with
  | top => simp
  | coe n =>
    rw [← WithTop.LinearOrderedAddCommGroup.coe_neg, WithTop.untop₀_coe, WithTop.untop₀_coe]
    simp only [negPart_def]
    omega

/-- Integer bookkeeping for the negative part of an order bounded below by a minimum. -/
lemma negPart_untop₀_le_of_min_le {x y w : WithTop ℤ} (hx : x ≠ ⊤) (hy : y ≠ ⊤) (hw : w ≠ ⊤)
    (h : min x y ≤ w) : (w.untop₀)⁻ ≤ max (x.untop₀)⁻ (y.untop₀)⁻ := by
  obtain ⟨m, rfl⟩ := WithTop.ne_top_iff_exists.1 hx
  obtain ⟨n, rfl⟩ := WithTop.ne_top_iff_exists.1 hy
  obtain ⟨k, rfl⟩ := WithTop.ne_top_iff_exists.1 hw
  rw [← WithTop.coe_min] at h
  have h' : min m n ≤ k := by exact_mod_cast h
  simp only [WithTop.untop₀_coe, negPart_def]
  omega

section Pair

variable {a : Fin 3 → ℂ} {f g : ℂ → ℂ}

/-- The entire function `Ψ` has no poles. -/
lemma logCounting_auxPsi_top (hp : NormalizedPair univ f g a) :
    logCounting (auxPsi a f g) ⊤ = 0 := by
  set Ψ := auxPsi a f g with hΨ
  have hΨm : Meromorphic Ψ := hp.meromorphic_auxPsi
  have hΨm' : MeromorphicOn Ψ univ := fun y _ => hΨm y
  set H := toMeromorphicNFOn Ψ univ
  have hΨH : Ψ =ᶠ[codiscrete ℂ] H := toMeromorphicNFOn_eqOn_codiscrete hΨm'
  have hHa : ∀ x, AnalyticAt ℂ H x := by
    intro x
    apply (meromorphicNFOn_toMeromorphicNFOn Ψ univ (mem_univ x)).meromorphicOrderAt_nonneg_iff_analyticAt.1
    rw [meromorphicOrderAt_congr (hΨm'.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ x))]
    exact (hp.order_aux (mem_univ x)).2.2.1
  have hlcH : logCounting H ⊤ = 0 := by
    have := logCounting_add_analyticOn (f := (0 : ℂ → ℂ)) (g := H)
      (fun x => analyticAt_const.meromorphicAt) (fun x _ => (hHa x).analyticWithinAt)
    rw [zero_add] at this
    rw [this, logCounting_const_zero]
  rw [logCounting_congr_codiscrete hΨH, hlcH]

/-- `T(r, Ψ) = O(L)` (Lemma 3.10). -/
lemma charT_auxPsi_le (hp : NormalizedPair univ f g a) :
    ∃ C : ℝ, OutsideFiniteMeasure fun r => charT (auxPsi a f g) r ≤ C * pairL f g r := by
  obtain ⟨C, hC⟩ := mues_estimate hp
  refine ⟨C, hC.mono fun r _ h => ?_⟩
  have : charT (auxPsi a f g) r = proximity (auxPsi a f g) ⊤ r := by
    simp [charT, characteristic, logCounting_auxPsi_top hp]
  rw [this]; exact h

/-- `N(r, 1/Ψ) = O(L)` (Lemma 3.10). -/
lemma logCounting_auxPsi_zero_le (hp : NormalizedPair univ f g a) :
    ∃ C : ℝ, OutsideFiniteMeasure fun r => logCounting (auxPsi a f g) 0 r ≤ C * pairL f g r := by
  obtain ⟨K, hK⟩ := logCounting_zero_le_charT hp.meromorphic_auxPsi
  obtain ⟨C, hC⟩ := charT_auxPsi_le hp
  refine ⟨|C| + |K|, hC.mono fun r hr h => ?_⟩
  have hL := one_le_pairL (f := f) (g := g) hr
  have h1 := hK r hr
  have k1 : C * pairL f g r ≤ |C| * pairL f g r :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
  have k2 : K ≤ |K| * pairL f g r :=
    (le_abs_self K).trans (le_mul_of_one_le_right (abs_nonneg K) hL)
  rw [add_mul]; linarith

/-- Pointwise: the poles of `f - g` are among the common poles, with no larger order. -/
lemma negPart_divisor_sub_le (hp : NormalizedPair univ f g a) :
    (MeromorphicOn.divisor (fun z => f z - g z) univ)⁻ ≤ (MeromorphicOn.divisor f univ)⁻ := by
  have hfm := hp.nonconst_f.meromorphic
  have hgm := hp.nonconst_g.meromorphic
  have hsm : MeromorphicOn (fun z => f z - g z) univ := fun x _ => (hfm x).sub (hgm x)
  intro z
  rw [Function.locallyFinsuppWithin.negPart_apply, Function.locallyFinsuppWithin.negPart_apply,
    MeromorphicOn.divisor_apply hsm (mem_univ z),
    MeromorphicOn.divisor_apply (fun x _ => hfm x) (mem_univ z)]
  have hfg : (meromorphicOrderAt g z).untop₀⁻ = (meromorphicOrderAt f z).untop₀⁻ := by
    rw [← toNat_untop₀_neg_eq, ← toNat_untop₀_neg_eq]
    have := hp.cm_top z (mem_univ z)
    simp only [mult_top] at this
    rw [this]
  have hmin : min (meromorphicOrderAt f z) (meromorphicOrderAt g z) ≤
      meromorphicOrderAt (fun w => f w - g w) z := by
    have h := meromorphicOrderAt_add (hfm z) ((hgm z).neg) (x := z)
    have hneg : meromorphicOrderAt (-g) z = meromorphicOrderAt g z := order_neg_eq g z
    rw [hneg] at h
    convert h using 2
  have h := negPart_untop₀_le_of_min_le (order_ne_top_of_nonconst hp.nonconst_f (mem_univ z))
    (order_ne_top_of_nonconst hp.nonconst_g (mem_univ z)) (hp.distinct z (mem_univ z)) hmin
  rw [hfg, max_self] at h
  exact h

/-- `T(f - g) ≤ m(f) + m(g) + N(f) + log 2`. -/
lemma charT_sub_le (hp : NormalizedPair univ f g a) {r : ℝ} (hr : 1 ≤ r) :
    charT (fun z => f z - g z) r ≤
      proximity f ⊤ r + proximity g ⊤ r + logCounting f ⊤ r + log 2 := by
  have hfm := hp.nonconst_f.meromorphic
  have hgm := hp.nonconst_g.meromorphic
  have hng : Meromorphic (fun z => (-1 : ℂ) * g z) := fun x =>
    (MeromorphicAt.const _ x).mul (hgm x)
  have hf : (fun z => f z - g z) = f + fun z => (-1 : ℂ) * g z := by ext z; simp; ring
  have e1 := proximity_add_top_le hfm hng r
  simp only [Pi.add_apply] at e1
  have e2 := proximity_const_mul_le (-1 : ℂ) hgm r
  simp only [norm_neg, norm_one, Real.posLog_one, zero_add] at e2
  have hm : proximity (fun z => f z - g z) ⊤ r ≤ proximity f ⊤ r + proximity g ⊤ r + log 2 := by
    rw [hf]; linarith
  have hN : logCounting (fun z => f z - g z) ⊤ r ≤ logCounting f ⊤ r := by
    rw [logCounting_top, logCounting_top]
    exact Function.locallyFinsuppWithin.logCounting_le (negPart_divisor_sub_le hp) hr
  show proximity (fun z => f z - g z) ⊤ r + logCounting (fun z => f z - g z) ⊤ r ≤ _
  linarith

/-- The common pole count: `N(r, g) = N(r, f)`. -/
lemma logCounting_top_eq (hp : NormalizedPair univ f g a) :
    logCounting g ⊤ = logCounting f ⊤ := by
  have key := toNat_untop₀_neg_eq
  rw [logCounting_top, logCounting_top]
  congr 1
  ext z
  rw [Function.locallyFinsuppWithin.negPart_apply, Function.locallyFinsuppWithin.negPart_apply,
    MeromorphicOn.divisor_apply (fun x _ => hp.nonconst_g.meromorphic x) (mem_univ z),
    MeromorphicOn.divisor_apply (fun x _ => hp.nonconst_f.meromorphic x) (mem_univ z),
    ← key, ← key]
  have := hp.cm_top z (mem_univ z)
  simp only [mult_top] at this
  rw [this]

private lemma sharedValue_sum_apply {α : Type*} (s : Finset α)
    (D : α → Function.locallyFinsupp ℂ ℤ) (z : ℂ) :
    (∑ i ∈ s, D i) z = ∑ i ∈ s, D i z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Function.locallyFinsuppWithin.coe_add, Pi.add_apply,
      ih, Finset.sum_insert hi]

/-- Each finite shared fiber contributes a zero of f-g, and the distinct
target fibers cannot contribute at the same source point. -/
theorem sum_reduced_fiber_divisors_le_sub_zero (hp : NormalizedPair univ f g a) :
    (∑ j, reducedFiberDivisor f (a j : Sphere)) ≤
      (MeromorphicOn.divisor (fun w => f w - g w) univ)⁺ := by
  classical
  intro z
  rw [sharedValue_sum_apply]
  simp only [reducedFiberDivisor_apply hp.nonconst_f.1]
  by_cases hex : ∃ j : Fin 3, 0 < mult f (a j : Sphere) z
  · obtain ⟨j, hj⟩ := hex
    have hother : ∀ i : Fin 3, i ≠ j → mult f (a i : Sphere) z = 0 := by
      intro i hij
      exact mult_finite_eq_zero_of_ne_of_pos (hp.nonconst_f.1 z (mem_univ z))
        (fun h => hij (hp.injective h).symm) hj
    have hsum : (∑ i : Fin 3, (if 0 < mult f (a i : Sphere) z then 1 else 0 : ℤ)) = 1 := by
      calc
        (∑ i : Fin 3, (if 0 < mult f (a i : Sphere) z then 1 else 0 : ℤ)) =
            if 0 < mult f (a j : Sphere) z then 1 else 0 := by
          apply Finset.sum_eq_single j
          · intro i _ hij
            simp [hother i hij]
          · simp
        _ = 1 := if_pos hj
    rw [hsum]
    have hgj := (hp.im j z (mem_univ z)).1 hj
    have hfo : 0 < meromorphicOrderAt (fun w => f w - a j) z := by
      rw [order_sub_eq_mult hj]
      exact_mod_cast hj
    have hgo : 0 < meromorphicOrderAt (fun w => g w - a j) z := by
      rw [order_sub_eq_mult hgj]
      exact_mod_cast hgj
    have hmin := meromorphicOrderAt_add
      ((hp.nonconst_f.1 z (mem_univ z)).sub (MeromorphicAt.const (a j) z))
      (((hp.nonconst_g.1 z (mem_univ z)).sub (MeromorphicAt.const (a j) z)).neg) (x := z)
    change min (meromorphicOrderAt (fun w => f w - a j) z)
      (meromorphicOrderAt (fun w => -(g w - a j)) z) ≤
        meromorphicOrderAt (fun w => (f w - a j) + -(g w - a j)) z at hmin
    rw [order_neg_eq] at hmin
    have he : (fun w => (f w - a j) + -(g w - a j)) = (fun w => f w - g w) := by
      funext w
      ring
    rw [he] at hmin
    have hpos : 0 < meromorphicOrderAt (fun w => f w - g w) z :=
      (lt_min hfo hgo).trans_le hmin
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 (hp.distinct z (mem_univ z))
    rw [← hn] at hpos
    have hnpos : (0 : ℤ) < n := by exact_mod_cast hpos
    have hsm : MeromorphicOn (fun w => f w - g w) univ :=
      hp.nonconst_f.1.sub hp.nonconst_g.1
    rw [Function.locallyFinsuppWithin.posPart_apply,
      MeromorphicOn.divisor_apply hsm (mem_univ z),
      ← hn, WithTop.untop₀_coe, posPart_def]
    omega
  · have hzero : ∀ j : Fin 3, mult f (a j : Sphere) z = 0 := by
      intro j
      exact Nat.eq_zero_of_not_pos (fun hj => hex ⟨j, hj⟩)
    simp only [hzero, lt_self_iff_false, ↓reduceIte, Finset.sum_const_zero]
    exact posPart_nonneg _

/-- The integrated finite shared-fiber count is bounded by the zero count of f-g. -/
theorem sum_reduced_finite_le_sub_zero (hp : NormalizedPair univ f g a)
    {r : ℝ} (hr : 1 ≤ r) :
    (∑ j, reducedCounting f (a j : Sphere) r) ≤
      logCounting (fun w => f w - g w) 0 r := by
  have h := Function.locallyFinsuppWithin.logCounting_le
    (sum_reduced_fiber_divisors_le_sub_zero hp) hr
  simp only [map_sum, Finset.sum_apply] at h
  have hred : ∀ j : Fin 3, (reducedFiberDivisor f (a j : Sphere)).logCounting r =
      reducedCounting f (a j : Sphere) r := fun j =>
    (reducedCounting_eq_reducedFiberDivisor hp.nonconst_f.1 _ (by linarith)).symm
  simpa only [hred, ← ValueDistribution.logCounting_zero] using h

/-- The four reduced shared fibers have total count at most Tf+Tg+O(1).
CM sharing at infinity is used only for the common-pole estimate. -/
theorem sum_reduced_four_le_characteristics (hp : NormalizedPair univ f g a) :
    ∃ K : ℝ, ∀ r : ℝ, 1 ≤ r →
      (∑ j, reducedCounting f (a j : Sphere) r) + reducedCounting f ⊤ r ≤
        charT f r + charT g r + K := by
  obtain ⟨K, hK⟩ := logCounting_zero_le_charT
    (fun z => (hp.nonconst_f.meromorphic z).sub (hp.nonconst_g.meromorphic z))
  refine ⟨K + Real.log 2, fun r hr => ?_⟩
  have h₁ := sum_reduced_finite_le_sub_zero hp hr
  have h₂ := hK r hr
  change logCounting (fun w => f w - g w) 0 r ≤
    charT (fun w => f w - g w) r + K at h₂
  have h₃ := charT_sub_le hp hr
  have h₄ := reducedCounting_le_logCounting hp.nonconst_f.1 ⊤ hr
  have hN := congrFun (logCounting_top_eq hp) r
  change proximity f ⊤ r + logCounting f ⊤ r +
    (proximity g ⊤ r + logCounting g ⊤ r) + (K + Real.log 2) ≥ _
  linarith

/-- IM sharing gives equality of reduced counting functions at every radius. -/
theorem reducedCounting_eq_of_sharesIM {b : Sphere}
    (h : SharesIMOn univ f g b) (r : ℝ) : reducedCounting f b r = reducedCounting g b r := by
  have hs : {z : ℂ | ‖z‖ ≤ r ∧ 0 < mult f b z} =
      {z : ℂ | ‖z‖ ≤ r ∧ 0 < mult g b z} := by
    ext z
    exact and_congr_right fun _ => h z (mem_univ z)
  unfold reducedCounting
  simp only [hs, h 0 (mem_univ 0)]

/-- The second main theorem for the four shared values, with the error
expressed using the maximum characteristic of the pair. -/
theorem second_main_pair_left (hp : NormalizedPair univ f g a) :
    ∃ C : ℝ, 0 ≤ C ∧ OutsideFiniteMeasure fun r =>
      2 * charT f r ≤ (∑ j, reducedCounting f (a j : Sphere) r) +
        reducedCounting f ⊤ r + C * pairL f g r := by
  obtain ⟨C, hC⟩ := second_main_finite hp.nonconst_f a hp.injective
  refine ⟨|C|, abs_nonneg C, hC.mono fun r hr h => ?_⟩
  have hT := charT_nonneg (h := f) hr
  have hlog0 : 0 ≤ Real.log (Real.exp 1 + r * charT f r) :=
    Real.log_nonneg (by nlinarith [Real.add_one_le_exp 1])
  have hlog := log_charT_le_pairL_left (f := f) (g := g) hr
  have h₁ := mul_le_mul_of_nonneg_right (le_abs_self C) hlog0
  have h₂ := mul_le_mul_of_nonneg_left hlog (abs_nonneg C)
  norm_num only [Nat.cast_ofNat, show (3 : ℝ) - 1 = 2 by norm_num] at h
  linarith

/-- The two characteristics agree up to the logarithmic error, first in one direction. -/
theorem charT_left_le_right_add_pairL (hp : NormalizedPair univ f g a) :
    ∃ C : ℝ, 0 ≤ C ∧ OutsideFiniteMeasure fun r =>
      charT f r ≤ charT g r + C * pairL f g r := by
  obtain ⟨C, hC0, hC⟩ := second_main_pair_left hp
  obtain ⟨K, hK⟩ := sum_reduced_four_le_characteristics hp
  refine ⟨C + |K|, by positivity, hC.mono fun r hr h => ?_⟩
  have hsum := hK r hr
  have hL := one_le_pairL (f := f) (g := g) hr
  have hconstant : K ≤ |K| * pairL f g r :=
    (le_abs_self K).trans (le_mul_of_one_le_right (abs_nonneg K) hL)
  rw [add_mul]
  linarith

/-- The characteristic comparison for a normalized four-value sharing pair.
The conclusion has no growth or order hypothesis. -/
theorem abs_charT_sub_le_pairL (hp : NormalizedPair univ f g a) :
    ∃ C : ℝ, 0 ≤ C ∧ OutsideFiniteMeasure fun r =>
      |charT f r - charT g r| ≤ C * pairL f g r := by
  obtain ⟨Cf, hCf, hf⟩ := charT_left_le_right_add_pairL hp
  obtain ⟨Cg, hCg, hg⟩ := charT_left_le_right_add_pairL hp.symm
  have hg' : OutsideFiniteMeasure fun r => charT g r ≤ charT f r + Cg * pairL f g r :=
    hg.map fun r h => by simpa only [pairL, pairT, max_comm] using h
  refine ⟨Cf + Cg, add_nonneg hCf hCg,
    ((hf.conj hg').conj (OutsideFiniteMeasure.eventually_ge 1)).map fun r h => ?_⟩
  obtain ⟨⟨hf, hg⟩, hr⟩ := h
  have hL : 0 ≤ pairL f g r := by linarith [one_le_pairL (f := f) (g := g) hr]
  have h₁ := mul_nonneg hCf hL
  have h₂ := mul_nonneg hCg hL
  rw [abs_le, add_mul]
  constructor <;> linarith

/-- Both second-main inequalities use the same reduced shared-fiber counts. -/
theorem second_main_pair_max (hp : NormalizedPair univ f g a) :
    ∃ C : ℝ, 0 ≤ C ∧ OutsideFiniteMeasure fun r =>
      2 * pairT f g r ≤ (∑ j, reducedCounting f (a j : Sphere) r) +
        reducedCounting f ⊤ r + C * pairL f g r := by
  obtain ⟨Cf, hCf, hf⟩ := second_main_pair_left hp
  obtain ⟨Cg, hCg, hg⟩ := second_main_pair_left hp.symm
  have hfinite : ∀ (j : Fin 3) r, reducedCounting g (a j : Sphere) r =
      reducedCounting f (a j : Sphere) r := fun j r =>
    (reducedCounting_eq_of_sharesIM (hp.im j) r).symm
  have htop : ∀ r, reducedCounting g ⊤ r = reducedCounting f ⊤ r := fun r =>
    (reducedCounting_eq_of_sharesIM hp.cm_top.sharesIMOn r).symm
  have hg' : OutsideFiniteMeasure fun r =>
      2 * charT g r ≤ (∑ j, reducedCounting f (a j : Sphere) r) +
        reducedCounting f ⊤ r + Cg * pairL f g r :=
    hg.map fun r h => by simpa only [hfinite, htop, pairL, pairT, max_comm] using h
  refine ⟨Cf + Cg, add_nonneg hCf hCg,
    ((hf.conj hg').conj (OutsideFiniteMeasure.eventually_ge 1)).map fun r h => ?_⟩
  obtain ⟨⟨hf, hg⟩, hr⟩ := h
  have hL : 0 ≤ pairL f g r := by linarith [one_le_pairL (f := f) (g := g) hr]
  have h₁ := mul_nonneg hCf hL
  have h₂ := mul_nonneg hCg hL
  unfold pairT
  rcases le_total (charT f r) (charT g r) with h | h
  · rw [max_eq_right h, add_mul]
    linarith
  · rw [max_eq_left h, add_mul]
    linarith

/-- The sum of the four reduced shared-fiber counting functions is
`2 max(Tf,Tg) + O(log(e+r max(Tf,Tg)))`, outside finite measure. -/
theorem abs_sum_reduced_sub_two_pairT_le_pairL (hp : NormalizedPair univ f g a) :
    ∃ C : ℝ, 0 ≤ C ∧ OutsideFiniteMeasure fun r =>
      |((∑ j, reducedCounting f (a j : Sphere) r) + reducedCounting f ⊤ r) -
        2 * pairT f g r| ≤ C * pairL f g r := by
  obtain ⟨C, hC0, hC⟩ := second_main_pair_max hp
  obtain ⟨K, hK⟩ := sum_reduced_four_le_characteristics hp
  refine ⟨C + |K|, by positivity, hC.mono fun r hr h => ?_⟩
  have hsum := hK r hr
  have hL1 := one_le_pairL (f := f) (g := g) hr
  have hL0 : 0 ≤ pairL f g r := by linarith
  have hconstant : K ≤ |K| * pairL f g r :=
    (le_abs_self K).trans (le_mul_of_one_le_right (abs_nonneg K) hL1)
  have hCf := le_max_left (charT f r) (charT g r)
  have hCg := le_max_right (charT f r) (charT g r)
  change charT f r ≤ pairT f g r at hCf
  change charT g r ≤ pairT f g r at hCg
  have h₁ := mul_nonneg hC0 hL0
  have h₂ := mul_nonneg (abs_nonneg K) hL0
  rw [abs_le, add_mul]
  constructor <;> linarith

end Pair

end ThreeIM
