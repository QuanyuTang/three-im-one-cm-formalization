module

public import RequestProject.ThreeIM.LambdaProximity

/-!
# Pure local and counting properties of the reciprocal-cubic auxiliary function

These declarations are moved without changing their names or types from
`Density`, so that the two-CM proof can use them without importing External.
-/

@[expose] public section

open Filter Set Topology ValueDistribution Real

namespace ThreeIM

/-- The partial-fraction coefficients of the reciprocal cubic. -/
noncomputable def cubicReciprocalCoeff (a : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ![1 / ((a 0 - a 1) * (a 0 - a 2)),
    1 / ((a 1 - a 0) * (a 1 - a 2)),
    1 / ((a 2 - a 0) * (a 2 - a 1))]

/-- The single-function term entering the common-pole auxiliary function. -/
noncomputable def HFun (a : Fin 3 → ℂ) (h : ℂ → ℂ) : ℂ → ℂ :=
  fun z => deriv h z / cubicP a (h z)

/-- The auxiliary function used to count common poles. -/
noncomputable def HAux (a : Fin 3 → ℂ) (f g : ℂ → ℂ) : ℂ → ℂ :=
  fun z => HFun a f z - HFun a g z

/-- Laurent residue of the reciprocal-cubic logarithmic expression. -/
noncomputable def HResidue (a : Fin 3 → ℂ) (h : ℂ → ℂ) (z₀ : ℂ) : ℂ :=
  ∑ i, cubicReciprocalCoeff a i * (ordZ (fun w => h w - a i) z₀ : ℂ)

theorem cubicReciprocalCoeff_ne_zero {a : Fin 3 → ℂ} (ha : Function.Injective a) (i : Fin 3) :
    cubicReciprocalCoeff a i ≠ 0 := by
  have hne (j k : Fin 3) (hjk : j ≠ k) : a j - a k ≠ 0 := sub_ne_zero.2 (ha.ne hjk)
  fin_cases i <;> simp [cubicReciprocalCoeff, hne 0 1 (by decide), hne 0 2 (by decide),
    hne 1 0 (by decide), hne 1 2 (by decide), hne 2 0 (by decide), hne 2 1 (by decide)]

theorem meromorphicAt_HFun {h : ℂ → ℂ} {a : Fin 3 → ℂ} {z₀ : ℂ}
    (hh : MeromorphicAt h z₀) : MeromorphicAt (HFun a h) z₀ := by
  unfold HFun cubicP
  fun_prop

theorem meromorphicAt_HAux {f g : ℂ → ℂ} {a : Fin 3 → ℂ} {z₀ : ℂ}
    (hf : MeromorphicAt f z₀) (hg : MeromorphicAt g z₀) : MeromorphicAt (HAux a f g) z₀ :=
  (meromorphicAt_HFun hf).sub (meromorphicAt_HFun hg)

/-- Partial fractions, interpreted as an identity off discrete fibers. -/
theorem HFun_partial_fractions {h : ℂ → ℂ} (hh : IsNonconstMeroOn h univ)
    {a : Fin 3 → ℂ} (ha : Function.Injective a) :
    HFun a h =ᶠ[codiscrete ℂ] fun z =>
      cubicReciprocalCoeff a 0 * (deriv h z / (h z - a 0)) +
      cubicReciprocalCoeff a 1 * (deriv h z / (h z - a 1)) +
      cubicReciprocalCoeff a 2 * (deriv h z / (h z - a 2)) := by
  filter_upwards [hh.eventually_ne (a 0), hh.eventually_ne (a 1),
    hh.eventually_ne (a 2)] with z h0 h1 h2
  have hw : ∀ i, h z ≠ a i := fun i => by fin_cases i <;> assumption
  have hp := partial_fractions ha hw (j := 0) (by omega)
  calc HFun a h z = deriv h z * ((h z) ^ 0 / cubicP a (h z)) := by
        simp [HFun, div_eq_mul_inv]
    _ = _ := by
      rw [hp]
      simp only [pow_zero, cubicReciprocalCoeff, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      ring

/-- At every point, `h'/P(h)` has a simple-pole term and an analytic remainder. -/
theorem HFun_local {h : ℂ → ℂ} (hh : IsNonconstMeroOn h univ)
    {a : Fin 3 → ℂ} (ha : Function.Injective a) (z₀ : ℂ) :
    ∃ A : ℂ → ℂ, AnalyticAt ℂ A z₀ ∧ ∀ᶠ w in 𝓝[≠] z₀,
      HFun a h w = HResidue a h z₀ / (w - z₀) + A w := by
  have hm := hh.meromorphic z₀
  obtain ⟨A0, hA0, h0⟩ := logDeriv_local_ordZ (F := fun w => h w - a 0)
    (hm.sub (MeromorphicAt.const _ _)) (hh.2 z₀ (mem_univ z₀) _)
  obtain ⟨A1, hA1, h1⟩ := logDeriv_local_ordZ (F := fun w => h w - a 1)
    (hm.sub (MeromorphicAt.const _ _)) (hh.2 z₀ (mem_univ z₀) _)
  obtain ⟨A2, hA2, h2⟩ := logDeriv_local_ordZ (F := fun w => h w - a 2)
    (hm.sub (MeromorphicAt.const _ _)) (hh.2 z₀ (mem_univ z₀) _)
  have hsub (c : ℂ) : deriv (fun w => h w - c) = deriv h :=
    funext fun _ => deriv_sub_const c
  rw [hsub] at h0 h1 h2
  refine ⟨fun w => cubicReciprocalCoeff a 0 * A0 w + cubicReciprocalCoeff a 1 * A1 w +
    cubicReciprocalCoeff a 2 * A2 w,
    ((analyticAt_const.mul hA0).add (analyticAt_const.mul hA1)).add
      (analyticAt_const.mul hA2), ?_⟩
  have hpf := (codiscrete_iff_nhdsNE.1 (HFun_partial_fractions hh ha)) z₀
  filter_upwards [h0, h1, h2, hpf] with w hw0 hw1 hw2 hwp
  rw [hwp, hw0, hw1, hw2]
  simp only [HResidue, Fin.sum_univ_three]
  ring

theorem HAux_local (hp : NormalizedPair univ f g a) (z₀ : ℂ) :
    ∃ A : ℂ → ℂ, AnalyticAt ℂ A z₀ ∧ ∀ᶠ w in 𝓝[≠] z₀,
      HAux a f g w = (HResidue a f z₀ - HResidue a g z₀) / (w - z₀) + A w := by
  obtain ⟨F, hF, hf⟩ := HFun_local hp.nonconst_f hp.injective z₀
  obtain ⟨G, hG, hg⟩ := HFun_local hp.nonconst_g hp.injective z₀
  refine ⟨fun w => F w - G w, hF.sub hG, ?_⟩
  filter_upwards [hf, hg] with w hwf hwg
  simp only [HAux]
  rw [hwf, hwg]
  ring

theorem HResidue_at_value {h : ℂ → ℂ} {a : Fin 3 → ℂ} {z₀ : ℂ}
    (hh : MeromorphicAt h z₀) (ha : Function.Injective a) (j : Fin 3)
    (hpos : 0 < mult h (a j : Sphere) z₀) :
    HResidue a h z₀ = cubicReciprocalCoeff a j * (mult h (a j : Sphere) z₀ : ℂ) := by
  unfold HResidue
  calc (∑ i, cubicReciprocalCoeff a i * (ordZ (fun w => h w - a i) z₀ : ℂ)) =
      cubicReciprocalCoeff a j * (ordZ (fun w => h w - a j) z₀ : ℂ) := by
        apply Finset.sum_eq_single j
        · intro i _ hij
          rw [ordZ_sub_at_value_other hh (ha.ne (Ne.symm hij)) hpos]
          simp
        · simp
    _ = _ := by simp only [ordZ_sub_at_value_self hpos, Int.cast_natCast]

/-- At a pole, `h'/P(h)` has a zero of order at least one. -/
theorem HFun_order_ge_one_at_pole {h : ℂ → ℂ} {a : Fin 3 → ℂ} {z₀ : ℂ}
    (hh : MeromorphicAt h z₀) (hpole : meromorphicOrderAt h z₀ < 0) :
    (1 : WithTop ℤ) ≤ meromorphicOrderAt (HFun a h) z₀ := by
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 hpole.ne_top
  have hkneg : k < 0 := by rw [← hk] at hpole; exact_mod_cast hpole
  have hshift : meromorphicOrderAt (fun w => h w - 0) z₀ = k := by simpa using hk.symm
  have hd := order_deriv_of_order_eq hh hkneg.ne hshift
  have hP := order_cubicP_comp_of_neg hh a hkneg hk.symm
  have hPm : MeromorphicAt (fun w => cubicP a (h w)) z₀ := by unfold cubicP; fun_prop
  have heq : HFun a h = deriv h * (fun w => cubicP a (h w))⁻¹ := by
    ext w
    simp [HFun, div_eq_mul_inv]
  rw [heq, meromorphicOrderAt_mul hh.deriv hPm.inv, meromorphicOrderAt_inv, hd, hP,
    ← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add]
  exact_mod_cast (show (1 : ℤ) ≤ (k - 1) + -(3 * k) by omega)

/-- Common poles are zeros of `H`, without any equality-of-multiplicity requirement. -/
theorem HAux_order_ge_one_at_shared_pole (hp : NormalizedPair univ f g a) {z₀ : ℂ}
    (hfpole : meromorphicOrderAt f z₀ < 0) (hgpole : meromorphicOrderAt g z₀ < 0) :
    (1 : WithTop ℤ) ≤ meromorphicOrderAt (HAux a f g) z₀ := by
  have hf := HFun_order_ge_one_at_pole (a := a) (hp.nonconst_f.meromorphic z₀) hfpole
  have hg := HFun_order_ge_one_at_pole (a := a) (hp.nonconst_g.meromorphic z₀) hgpole
  have heq : HAux a f g = HFun a f + fun w => -HFun a g w := by
    ext w
    simp [HAux, sub_eq_add_neg]
  rw [heq]
  refine le_trans (le_min hf ?_) (meromorphicOrderAt_add
    (meromorphicAt_HFun (hp.nonconst_f.meromorphic z₀))
    (meromorphicAt_HFun (hp.nonconst_g.meromorphic z₀)).neg)
  rwa [order_neg_eq]

/-- Every finite defect gives a simple pole of `H`. -/
theorem HAux_order_at_defect (hp : NormalizedPair univ f g a) {j : Fin 3} {z₀ : ℂ}
    (hd : IsDefect f g (a j : Sphere) z₀) : meromorphicOrderAt (HAux a f g) z₀ = -1 := by
  obtain ⟨A, hA, heq⟩ := HAux_local hp z₀
  apply (order_of_local_form hA heq).2.2
  rw [HResidue_at_value (hp.nonconst_f.meromorphic z₀) hp.injective j hd.1,
    HResidue_at_value (hp.nonconst_g.meromorphic z₀) hp.injective j hd.2.1, ← mul_sub]
  apply mul_ne_zero (cubicReciprocalCoeff_ne_zero hp.injective j)
  intro he
  exact hd.2.2 (by exact_mod_cast (sub_eq_zero.1 he))

theorem HResidue_eq_zero_at_generic {h : ℂ → ℂ} (hh : IsNonconstMeroOn h univ)
    (a : Fin 3 → ℂ) {z₀ : ℂ} (hnn : 0 ≤ meromorphicOrderAt h z₀)
    (hval : ∀ i, mult h (a i : Sphere) z₀ = 0) : HResidue a h z₀ = 0 := by
  have hz (i : Fin 3) : ordZ (fun w => h w - a i) z₀ = 0 := by
    simp only [ordZ, order_sub_const_eq_zero_generic hh (mem_univ z₀) hnn (hval i),
      WithTop.untop₀_zero]
  simp only [HResidue, hz, Int.cast_zero, mul_zero, Finset.sum_const_zero]

/-- All poles of `H` lie at finite multiplicity defects. Critical points away
from the marked fibers cause no poles of `H`. -/
theorem HAux_pole_support (hp : NormalizedPair univ f g a) (z₀ : ℂ)
    (hneg : meromorphicOrderAt (HAux a f g) z₀ < 0) :
    ∃ j, IsDefect f g (a j : Sphere) z₀ := by
  obtain ⟨A, hA, heq⟩ := HAux_local hp z₀
  have hzero := (order_of_local_form hA heq).2.1
  by_cases hpole : 0 < mult f ⊤ z₀
  · have hpoleg : 0 < mult g ⊤ z₀ := by rw [← hp.cm_top z₀ (mem_univ z₀)]; exact hpole
    have hfpole : meromorphicOrderAt f z₀ < 0 := by
      rw [order_eq_neg_mult_top hpole]
      exact_mod_cast (show -(mult f ⊤ z₀ : ℤ) < 0 by omega)
    have hgpole : meromorphicOrderAt g z₀ < 0 := by
      rw [order_eq_neg_mult_top hpoleg]
      exact_mod_cast (show -(mult g ⊤ z₀ : ℤ) < 0 by omega)
    have hge := HAux_order_ge_one_at_shared_pole hp hfpole hgpole
    exact absurd hneg (not_lt.2 (le_trans (by decide) hge))
  have hf0 : mult f ⊤ z₀ = 0 := by omega
  have hfnn := order_nonneg_of_mult_top_eq_zero hf0
    (order_ne_top_of_nonconst hp.nonconst_f (mem_univ z₀))
  have hgnn := order_nonneg_of_mult_top_eq_zero
    (by rw [← hp.cm_top z₀ (mem_univ z₀)]; exact hf0)
    (order_ne_top_of_nonconst hp.nonconst_g (mem_univ z₀))
  by_cases hval : ∃ j, 0 < mult f (a j : Sphere) z₀
  · obtain ⟨j, hj⟩ := hval
    have hjg := (hp.im j z₀ (mem_univ z₀)).1 hj
    by_cases hcm : mult f (a j : Sphere) z₀ = mult g (a j : Sphere) z₀
    · have hz : HResidue a f z₀ - HResidue a g z₀ = 0 := by
        rw [HResidue_at_value (hp.nonconst_f.meromorphic z₀) hp.injective j hj,
          HResidue_at_value (hp.nonconst_g.meromorphic z₀) hp.injective j hjg,
          hcm, sub_self]
      exact absurd hneg (not_lt.2 (hzero hz))
    · exact ⟨j, hj, hjg, hcm⟩
  have hvf : ∀ i, mult f (a i : Sphere) z₀ = 0 := by
    intro i
    have hn : ¬ 0 < mult f (a i : Sphere) z₀ := fun hi => hval ⟨i, hi⟩
    omega
  have hvg : ∀ i, mult g (a i : Sphere) z₀ = 0 := by
    intro i
    by_contra hi
    have hif := (hp.im i z₀ (mem_univ z₀)).2 (Nat.pos_of_ne_zero hi)
    rw [hvf i] at hif
    exact lt_irrefl _ hif
  have hz : HResidue a f z₀ - HResidue a g z₀ = 0 := by
    rw [HResidue_eq_zero_at_generic hp.nonconst_f a hfnn hvf,
      HResidue_eq_zero_at_generic hp.nonconst_g a hgnn hvg, sub_self]
  exact absurd hneg (not_lt.2 (hzero hz))

theorem HAux_order_ne_top_of_defect (hp : NormalizedPair univ f g a)
    (hdefect : ∃ j z₀, IsDefect f g (a j : Sphere) z₀) (z : ℂ) :
    meromorphicOrderAt (HAux a f g) z ≠ ⊤ := by
  obtain ⟨j, z₀, hd⟩ := hdefect
  have hfinite : meromorphicOrderAt (HAux a f g) z₀ ≠ ⊤ := by
    rw [HAux_order_at_defect hp hd]
    exact WithTop.coe_ne_top
  exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
    (fun w _ => meromorphicAt_HAux (hp.nonconst_f.meromorphic w) (hp.nonconst_g.meromorphic w))
    isPreconnected_univ (mem_univ z₀) (mem_univ z) hfinite

private lemma density_negPart_le_one {o : WithTop ℤ} (ho : (-1 : WithTop ℤ) ≤ o) :
    o.untop₀⁻ ≤ 1 ∧ (0 < o.untop₀⁻ → o < 0) := by
  induction h : o using WithTop.recTopCoe with
  | top => simp
  | coe n =>
    rw [h] at ho
    have hn : (-1 : ℤ) ≤ n := WithTop.coe_le_coe.1 ho
    simp only [WithTop.untop₀_coe, negPart_def]
    refine ⟨by omega, fun hpos => ?_⟩
    exact_mod_cast (show n < 0 by omega)

/-- The pole divisor of `H` is bounded by the total reduced defect divisor. -/
theorem negPart_divisor_HAux_le (hp : NormalizedPair univ f g a) :
    (MeromorphicOn.divisor (HAux a f g) univ)⁻ ≤ totalDefectDivisor a f g := by
  have hHm : MeromorphicOn (HAux a f g) univ := fun z _ =>
    meromorphicAt_HAux (hp.nonconst_f.meromorphic z) (hp.nonconst_g.meromorphic z)
  intro z
  rw [Function.locallyFinsuppWithin.negPart_apply,
    MeromorphicOn.divisor_apply hHm (mem_univ z)]
  change (meromorphicOrderAt (HAux a f g) z).untop₀⁻ ≤ totalDefectDivisor a f g z
  have hD0 : (0 : ℤ) ≤ totalDefectDivisor a f g z := totalDefectDivisor_nonneg a f g z
  obtain ⟨A, hA, heq⟩ := HAux_local hp z
  obtain ⟨h1, hneg⟩ := density_negPart_le_one (order_of_local_form hA heq).1
  have h0 := negPart_nonneg (meromorphicOrderAt (HAux a f g) z).untop₀
  by_cases hpos : 0 < (meromorphicOrderAt (HAux a f g) z).untop₀⁻
  · obtain ⟨j, hd⟩ := HAux_pole_support hp z (hneg hpos)
    have hsingle := Finset.single_le_sum (f := fun i => defectDivisor f g (a i : Sphere) z)
      (fun i _ => defectDivisor_nonneg f g (a i : Sphere) z) (Finset.mem_univ j)
    change defectDivisor f g (a j : Sphere) z ≤ ∑ i, defectDivisor f g (a i : Sphere) z
      at hsingle
    have hj1 : defectDivisor f g (a j : Sphere) z = 1 := by
      rw [defectDivisor_apply hp.nonconst_f.1 hp.nonconst_g.1, if_pos hd.2.2]
    rw [hj1] at hsingle
    rw [totalDefectDivisor_apply]
    omega
  · have hzero : (meromorphicOrderAt (HAux a f g) z).untop₀⁻ = 0 := by omega
    rw [hzero]
    exact hD0

theorem logCounting_HAux_top_le (hp : NormalizedPair univ f g a) {r : ℝ} (hr : 1 ≤ r) :
    logCounting (HAux a f g) ⊤ r ≤ totalDefectCounting a f g r := by
  have h := Function.locallyFinsuppWithin.logCounting_le (negPart_divisor_HAux_le hp) hr
  simpa only [← ValueDistribution.logCounting_top, totalDefectDivisor_logCounting] using h

private lemma density_posPart_ge_one {o : WithTop ℤ} (hfinite : o ≠ ⊤)
    (hge : (1 : WithTop ℤ) ≤ o) : 1 ≤ o.untop₀⁺ := by
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hfinite
  rw [← hn] at hge ⊢
  have hn1 : (1 : ℤ) ≤ n := WithTop.coe_le_coe.1 hge
  simp only [WithTop.untop₀_coe, posPart_def]
  omega

/-- Every common pole contributes at least one zero of the nonzero function `H`. -/
theorem reducedFiberDivisor_top_le_HAux (hp : NormalizedPair univ f g a)
    (hdefect : ∃ j z₀, IsDefect f g (a j : Sphere) z₀) :
    reducedFiberDivisor f ⊤ ≤ (MeromorphicOn.divisor (HAux a f g) univ)⁺ := by
  have hHm : MeromorphicOn (HAux a f g) univ := fun z _ =>
    meromorphicAt_HAux (hp.nonconst_f.meromorphic z) (hp.nonconst_g.meromorphic z)
  intro z
  rw [reducedFiberDivisor_apply hp.nonconst_f.1,
    Function.locallyFinsuppWithin.posPart_apply, MeromorphicOn.divisor_apply hHm (mem_univ z)]
  by_cases hpole : 0 < mult f ⊤ z
  · rw [if_pos hpole]
    have hpoleg : 0 < mult g ⊤ z := by rw [← hp.cm_top z (mem_univ z)]; exact hpole
    have hfpole : meromorphicOrderAt f z < 0 := by
      rw [order_eq_neg_mult_top hpole]
      exact_mod_cast (show -(mult f ⊤ z : ℤ) < 0 by omega)
    have hgpole : meromorphicOrderAt g z < 0 := by
      rw [order_eq_neg_mult_top hpoleg]
      exact_mod_cast (show -(mult g ⊤ z : ℤ) < 0 by omega)
    exact density_posPart_ge_one (HAux_order_ne_top_of_defect hp hdefect z)
      (HAux_order_ge_one_at_shared_pole hp hfpole hgpole)
  · rw [if_neg hpole]
    exact posPart_nonneg _

theorem reducedCounting_top_le_HAux_zero (hp : NormalizedPair univ f g a)
    (hdefect : ∃ j z₀, IsDefect f g (a j : Sphere) z₀) {r : ℝ} (hr : 1 ≤ r) :
    reducedCounting f ⊤ r ≤ logCounting (HAux a f g) 0 r := by
  have h := Function.locallyFinsuppWithin.logCounting_le
    (reducedFiberDivisor_top_le_HAux hp hdefect) hr
  simpa only [← ValueDistribution.logCounting_zero,
    ← reducedCounting_eq_reducedFiberDivisor hp.nonconst_f.1 ⊤ (le_trans zero_le_one hr)] using h

private theorem HFun_proximity_bound {f g h : ℂ → ℂ} (hh : IsNonconstMeroOn h univ)
    {a : Fin 3 → ℂ} (ha : Function.Injective a)
    (hD : ∀ i, PairProximityBound f g (fun z => deriv h z / (h z - a i))) :
    PairProximityBound f g (HFun a h) := by
  set D : Fin 3 → ℂ → ℂ := fun i z => deriv h z / (h z - a i)
  have hDm (i : Fin 3) : Meromorphic (D i) := meromorphic_logDeriv_sub hh.meromorphic (a i)
  have hCm (i : Fin 3) : Meromorphic (fun z => cubicReciprocalCoeff a i * D i z) :=
    fun z => (MeromorphicAt.const _ z).mul (hDm i z)
  have h0 := (hD 0).const_mul (hDm 0) (cubicReciprocalCoeff a 0)
  have h1 := (hD 1).const_mul (hDm 1) (cubicReciprocalCoeff a 1)
  have h2 := (hD 2).const_mul (hDm 2) (cubicReciprocalCoeff a 2)
  have hsum := (h0.add h1 (hCm 0) (hCm 1)).add h2 ((hCm 0).add (hCm 1)) (hCm 2)
  exact hsum.congr (HFun_partial_fractions hh ha).symm

/-- The common-pole auxiliary function has logarithmically small proximity. -/
theorem proximity_HAux_le (hp : NormalizedPair univ f g a) :
    PairProximityBound f g (HAux a f g) := by
  have hF (i : Fin 3) : PairProximityBound f g (fun z => deriv f z / (f z - a i)) := by
    obtain ⟨C, hC⟩ := proximity_logDeriv_le_pairL hp (a i)
    exact ⟨C, hC.mono fun r _ h => h.1⟩
  have hG (i : Fin 3) : PairProximityBound f g (fun z => deriv g z / (g z - a i)) := by
    obtain ⟨C, hC⟩ := proximity_logDeriv_le_pairL hp (a i)
    exact ⟨C, hC.mono fun r _ h => h.2⟩
  exact (HFun_proximity_bound hp.nonconst_f hp.injective hF).sub
    (HFun_proximity_bound hp.nonconst_g hp.injective hG)
    (fun z => meromorphicAt_HFun (hp.nonconst_f.meromorphic z))
    (fun z => meromorphicAt_HFun (hp.nonconst_g.meromorphic z))

theorem charT_HAux_le_defect (hp : NormalizedPair univ f g a) :
    ∃ C : ℝ, OutsideFiniteMeasure fun r =>
      charT (HAux a f g) r ≤ totalDefectCounting a f g r + C * pairL f g r := by
  obtain ⟨C, hC⟩ := proximity_HAux_le hp
  refine ⟨C, hC.mono fun r hr h => ?_⟩
  have hN := logCounting_HAux_top_le hp hr
  change proximity (HAux a f g) ⊤ r + logCounting (HAux a f g) ⊤ r ≤ _
  linarith

/-- The reduced common-pole count costs one total reduced defect count. -/
theorem reducedCounting_top_le_defect (hp : NormalizedPair univ f g a)
    (hdefect : ∃ j z₀, IsDefect f g (a j : Sphere) z₀) :
    ∃ C : ℝ, OutsideFiniteMeasure fun r =>
      reducedCounting f ⊤ r ≤ totalDefectCounting a f g r + C * pairL f g r := by
  have hHm : Meromorphic (HAux a f g) := fun z =>
    meromorphicAt_HAux (hp.nonconst_f.meromorphic z) (hp.nonconst_g.meromorphic z)
  obtain ⟨K, hK⟩ := logCounting_zero_le_charT hHm
  obtain ⟨C, hC⟩ := charT_HAux_le_defect hp
  refine ⟨C + |K|, hC.mono fun r hr h => ?_⟩
  have hL := one_le_pairL (f := f) (g := g) hr
  have hconst : K ≤ |K| * pairL f g r :=
    (le_abs_self K).trans (le_mul_of_one_le_right (abs_nonneg K) hL)
  have hzero := reducedCounting_top_le_HAux_zero hp hdefect hr
  have hfirst := hK r hr
  rw [add_mul]
  linarith

end ThreeIM
