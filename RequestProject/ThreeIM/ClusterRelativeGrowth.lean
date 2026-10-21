module

public import RequestProject.ThreeIM.SharedValueCounting
public import RequestProject.ThreeIM.TwoCMCharacteristic

/-! # A coarse characteristic bound for the actual auxiliary ratio

Only the existing derivative characteristic estimate and algebraic
characteristic inequalities are used. This supplies the input needed to
apply the logarithmic derivative lemma to Phi itself.
-/

@[expose] public section

set_option autoImplicit false

open Set Filter ValueDistribution Real

namespace ThreeIM

/-- A coarse bound relative to the original pair, before taking another
logarithm. It is derived below for actual U,V,Phi, not an extra assumption
on the selected configuration. -/
def PairCoarseCharacteristicBound (f g H : ℂ → ℂ) : Prop :=
  ∃ C : ℝ, OutsideFiniteMeasure fun r => charT H r ≤ C * (pairT f g r + pairL f g r)

theorem one_le_pair_characteristic_scale {f g : ℂ → ℂ} {r : ℝ} (hr : 1 ≤ r) :
    1 ≤ pairT f g r + pairL f g r := by
  have hT : 0 ≤ pairT f g r := (charT_nonneg (h := f) hr).trans (le_max_left _ _)
  linarith [one_le_pairL (f := f) (g := g) hr]

theorem PairCoarseCharacteristicBound.left (f g : ℂ → ℂ) : PairCoarseCharacteristicBound f g f := by
  refine ⟨1, ∅, MeasurableSet.empty, by simp, 1, fun r hr _ => ?_⟩
  change charT f r ≤ 1 * (pairT f g r + pairL f g r)
  rw [one_mul]
  exact (le_max_left _ _).trans (le_add_of_nonneg_right
    (show 0 ≤ pairL f g r by linarith [one_le_pairL (f := f) (g := g) hr]))

theorem PairCoarseCharacteristicBound.right (f g : ℂ → ℂ) : PairCoarseCharacteristicBound f g g := by
  refine ⟨1, ∅, MeasurableSet.empty, by simp, 1, fun r hr _ => ?_⟩
  change charT g r ≤ 1 * (pairT f g r + pairL f g r)
  rw [one_mul]
  exact (le_max_right _ _).trans (le_add_of_nonneg_right
    (show 0 ≤ pairL f g r by linarith [one_le_pairL (f := f) (g := g) hr]))

theorem PairCoarseCharacteristicBound.congr {f g H K : ℂ → ℂ}
    (hH : PairCoarseCharacteristicBound f g H) (hHK : H = K) :
    PairCoarseCharacteristicBound f g K := hHK ▸ hH

theorem finite_order_mul {H K : ℂ → ℂ} {z : ℂ}
    (hH : MeromorphicAt H z) (hK : MeromorphicAt K z)
    (hHf : meromorphicOrderAt H z ≠ ⊤) (hKf : meromorphicOrderAt K z ≠ ⊤) :
    meromorphicOrderAt (H * K) z ≠ ⊤ := by
  rw [meromorphicOrderAt_mul hH hK]
  exact WithTop.add_ne_top.mpr ⟨hHf, hKf⟩

theorem finite_order_inv {H : ℂ → ℂ} {z : ℂ} (hH : meromorphicOrderAt H z ≠ ⊤) :
    meromorphicOrderAt H⁻¹ z ≠ ⊤ := by
  rw [meromorphicOrderAt_inv]
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hH
  rw [← hn, ← WithTop.LinearOrderedAddCommGroup.coe_neg]
  exact WithTop.coe_ne_top

theorem PairCoarseCharacteristicBound.mul {f g H K : ℂ → ℂ}
    (hH : PairCoarseCharacteristicBound f g H) (hK : PairCoarseCharacteristicBound f g K)
    (hHm : Meromorphic H) (hKm : Meromorphic K)
    (hHf : ∀ z, meromorphicOrderAt H z ≠ ⊤) (hKf : ∀ z, meromorphicOrderAt K z ≠ ⊤) :
    PairCoarseCharacteristicBound f g (H * K) := by
  obtain ⟨C, hC⟩ := hH
  obtain ⟨D, hD⟩ := hK
  refine ⟨|C| + |D|, (hC.and hD).mono fun r hr ⟨h1, h2⟩ => ?_⟩
  have hS : 0 ≤ pairT f g r + pairL f g r := (by norm_num : (0 : ℝ) ≤ 1).trans
    (one_le_pair_characteristic_scale hr)
  have hc := mul_le_mul_of_nonneg_right (le_abs_self C) hS
  have hd := mul_le_mul_of_nonneg_right (le_abs_self D) hS
  have hprod := characteristic_mul_top_le hr hHm hHf hKm hKf
  change charT (H * K) r ≤ charT H r + charT K r at hprod
  rw [add_mul]
  linarith only [hprod, h1, h2, hc, hd]

theorem PairCoarseCharacteristicBound.inv {f g H : ℂ → ℂ}
    (hH : PairCoarseCharacteristicBound f g H) (hHm : Meromorphic H) :
    PairCoarseCharacteristicBound f g H⁻¹ := by
  obtain ⟨C, hC⟩ := hH
  let K := max |log ‖H 0‖| |log ‖meromorphicTrailingCoeffAt H 0‖|
  refine ⟨|C| + K, hC.mono fun r hr h => ?_⟩
  have hS := one_le_pair_characteristic_scale (f := f) (g := g) hr
  have hK : 0 ≤ K := (abs_nonneg _).trans (le_max_left _ _)
  have hc := mul_le_mul_of_nonneg_right (le_abs_self C) (show 0 ≤ pairT f g r + pairL f g r by linarith)
  have hk := le_mul_of_one_le_right hK hS
  have hInv := characteristic_sub_characteristic_inv_le hHm (R := r)
  change |charT H r - charT H⁻¹ r| ≤ K at hInv
  have hlow := (abs_le.mp hInv).1
  rw [add_mul]
  linarith only [h, hc, hk, hlow]

theorem PairCoarseCharacteristicBound.shift {f g H : ℂ → ℂ}
    (hH : PairCoarseCharacteristicBound f g H) (hHm : Meromorphic H) (c : ℂ) :
    PairCoarseCharacteristicBound f g (fun z => H z - c) := by
  obtain ⟨C, hC⟩ := hH
  let K := Real.posLog ‖c‖ + log 2
  refine ⟨|C| + K, hC.mono fun r hr h => ?_⟩
  have hS := one_le_pair_characteristic_scale (f := f) (g := g) hr
  have hK : 0 ≤ K := add_nonneg Real.posLog_nonneg (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  have hc := mul_le_mul_of_nonneg_right (le_abs_self C) (show 0 ≤ pairT f g r + pairL f g r by linarith)
  have hk := le_mul_of_one_le_right hK hS
  have hShift := abs_characteristic_sub_characteristic_shift_le (a₀ := c) (r := r) hHm
  change |charT H r - charT (fun z => H z - c) r| ≤ K at hShift
  have hlow := (abs_le.mp hShift).1
  rw [add_mul]
  linarith only [h, hc, hk, hlow]

theorem PairCoarseCharacteristicBound.deriv_left {f g : ℂ → ℂ}
    (hf : IsNonconstMeroOn f univ) : PairCoarseCharacteristicBound f g (deriv f) := by
  obtain ⟨C, hC⟩ := charT_deriv_le_log_error hf
  refine ⟨2 + |C|, hC.mono fun r hr h => ?_⟩
  have hL0 : 0 ≤ pairL f g r := by linarith [one_le_pairL (f := f) (g := g) hr]
  have hT0 : 0 ≤ pairT f g r := (charT_nonneg (h := f) hr).trans (le_max_left _ _)
  have hLf := log_charT_le_pairL_left (f := f) (g := g) hr
  have hlog0 : 0 ≤ Real.log (Real.exp 1 + r * charT f r) :=
    Real.log_nonneg (by nlinarith [charT_nonneg (h := f) hr, Real.add_one_le_exp 1])
  calc
    charT (deriv f) r ≤ 2 * charT f r + C * Real.log (Real.exp 1 + r * charT f r) := h
    _ ≤ 2 * (pairT f g r + pairL f g r) + |C| * (pairT f g r + pairL f g r) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left ((le_max_left _ _).trans (le_add_of_nonneg_right hL0)) (by norm_num)
      · exact (mul_le_mul_of_nonneg_right (le_abs_self C) hlog0).trans
          (mul_le_mul_of_nonneg_left (hLf.trans (le_add_of_nonneg_left hT0)) (abs_nonneg C))
    _ = (2 + |C|) * (pairT f g r + pairL f g r) := by ring

theorem PairCoarseCharacteristicBound.deriv_right {f g : ℂ → ℂ}
    (hg : IsNonconstMeroOn g univ) : PairCoarseCharacteristicBound f g (deriv g) := by
  have h := PairCoarseCharacteristicBound.deriv_left (g := f) hg
  simpa only [PairCoarseCharacteristicBound, pairT, pairL, max_comm] using h

theorem NormalizedPair.coarse_characteristic_difference
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} (hp : NormalizedPair univ f g a) :
    PairCoarseCharacteristicBound f g (fun z => f z - g z) := by
  refine ⟨2 + log 2, ∅, MeasurableSet.empty, by simp, 1, fun r hr _ => ?_⟩
  have hS := one_le_pair_characteristic_scale (f := f) (g := g) hr
  have hf : charT f r ≤ pairT f g r + pairL f g r :=
    (le_max_left _ _).trans (le_add_of_nonneg_right (by linarith [one_le_pairL (f := f) (g := g) hr]))
  have hg : charT g r ≤ pairT f g r + pairL f g r :=
    (le_max_right _ _).trans (le_add_of_nonneg_right (by linarith [one_le_pairL (f := f) (g := g) hr]))
  have hsub := charT_sub_le hp hr
  have hPg : proximity g ⊤ r ≤ charT g r := by
    exact le_add_of_nonneg_right (logCounting_nonneg hr)
  have hlog := le_mul_of_one_le_right (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)) hS
  change proximity f ⊤ r + logCounting f ⊤ r ≤ pairT f g r + pairL f g r at hf
  change charT (fun z => f z - g z) r ≤ (2 + log 2) * (pairT f g r + pairL f g r)
  rw [add_mul]
  linarith only [hsub, hf, hg, hPg, hlog]

/-- Cubic denominators have finite germs because the original function
is nonconstant as a meromorphic germ at every point. -/
theorem PairCoarseCharacteristicBound.cubic {f g H : ℂ → ℂ}
    (hH : PairCoarseCharacteristicBound f g H) (hHm : IsNonconstMeroOn H univ) (a : Fin 3 → ℂ) :
    PairCoarseCharacteristicBound f g (fun z => cubicP a (H z)) := by
  have hm (i : Fin 3) : Meromorphic (fun z => H z - a i) :=
    fun z => (hHm.meromorphic z).sub (MeromorphicAt.const _ _)
  have hn (i : Fin 3) (z : ℂ) : meromorphicOrderAt (fun w => H w - a i) z ≠ ⊤ :=
    hHm.2 z (mem_univ z) (a i)
  have h01 := (hH.shift hHm.meromorphic (a 0)).mul (hH.shift hHm.meromorphic (a 1))
    (hm 0) (hm 1) (hn 0) (hn 1)
  have h012 := h01.mul (hH.shift hHm.meromorphic (a 2))
    (fun z => (hm 0 z).mul (hm 1 z)) (hm 2)
    (fun z => finite_order_mul (hm 0 z) (hm 1 z) (hn 0 z) (hn 1 z)) (hn 2)
  exact h012.congr (by ext z; rfl)

theorem finite_order_cubic {H : ℂ → ℂ} (hH : IsNonconstMeroOn H univ) (a : Fin 3 → ℂ) (z : ℂ) :
    meromorphicOrderAt (fun w => cubicP a (H w)) z ≠ ⊤ := by
  have hm (i : Fin 3) : MeromorphicAt (fun w => H w - a i) z :=
    (hH.meromorphic z).sub (MeromorphicAt.const _ _)
  have hn (i : Fin 3) : meromorphicOrderAt (fun w => H w - a i) z ≠ ⊤ :=
    hH.2 z (mem_univ z) (a i)
  exact finite_order_mul ((hm 0).mul (hm 1)) (hm 2)
    (finite_order_mul (hm 0) (hm 1) (hn 0) (hn 1)) (hn 2)

/-- A common algebraic constructor used with H=f and H=g below. Every
finite-germ premise follows from the original pair and nonconstant H. -/
theorem NormalizedPair.coarse_characteristic_coefficient
    {a : Fin 3 → ℂ} {f g H : ℂ → ℂ} (hp : NormalizedPair univ f g a)
    (hH : IsNonconstMeroOn H univ) (hHC : PairCoarseCharacteristicBound f g H)
    (hDC : PairCoarseCharacteristicBound f g (deriv H)) :
    PairCoarseCharacteristicBound f g (fun z => (f z - g z) * deriv H z / cubicP a (H z)) := by
  let D := fun z => f z - g z
  let P := fun z => cubicP a (H z)
  have hDm : Meromorphic D := fun z => (hp.nonconst_f.meromorphic z).sub (hp.nonconst_g.meromorphic z)
  have hDf : ∀ z, meromorphicOrderAt D z ≠ ⊤ := fun z => hp.distinct z (mem_univ z)
  have hderm : Meromorphic (deriv H) := fun z => (hH.meromorphic z).deriv
  have hderf : ∀ z, meromorphicOrderAt (deriv H) z ≠ ⊤ :=
    fun z => (order_deriv_of_nonconst hH (mem_univ z)).1
  have hPm : Meromorphic P := by
    intro z
    have h := hH.meromorphic z
    unfold P cubicP
    fun_prop
  have hPf : ∀ z, meromorphicOrderAt P z ≠ ⊤ := finite_order_cubic hH a
  have hn := hp.coarse_characteristic_difference.mul hDC hDm hderm hDf hderf
  have hden := (hHC.cubic hH a).inv hPm
  have hfull := hn.mul hden (fun z => (hDm z).mul (hderm z)) (fun z => (hPm z).inv)
    (fun z => finite_order_mul (hDm z) (hderm z) (hDf z) (hderf z))
    (fun z => finite_order_inv (hPf z))
  apply hfull.congr
  ext z
  exact (div_eq_mul_inv ((f z - g z) * deriv H z) (cubicP a (H z))).symm

theorem NormalizedPair.coarse_characteristic_auxU
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} (hp : NormalizedPair univ f g a) :
    PairCoarseCharacteristicBound f g (auxU a f g) :=
  hp.coarse_characteristic_coefficient hp.nonconst_f
    (PairCoarseCharacteristicBound.left f g) (PairCoarseCharacteristicBound.deriv_left hp.nonconst_f)

theorem NormalizedPair.coarse_characteristic_auxV
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} (hp : NormalizedPair univ f g a) :
    PairCoarseCharacteristicBound f g (auxV a f g) :=
  hp.coarse_characteristic_coefficient hp.nonconst_g
    (PairCoarseCharacteristicBound.right f g) (PairCoarseCharacteristicBound.deriv_right hp.nonconst_g)

/-- The actual ratio has a coarse characteristic bound in terms of the
original pair. No growth assumption on Phi is supplied by the caller. -/
theorem NormalizedPair.coarse_characteristic_auxPhi
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} (hp : NormalizedPair univ f g a) :
    PairCoarseCharacteristicBound f g (auxPhi a f g) := by
  have h := hp.coarse_characteristic_auxU.mul
    (hp.coarse_characteristic_auxV.inv hp.meromorphic_auxV)
    hp.meromorphic_auxU (fun z => (hp.meromorphic_auxV z).inv)
    (fun z => (hp.order_aux (mem_univ z)).1.2)
    (fun z => finite_order_inv (hp.order_aux (mem_univ z)).2.1.2)
  exact h.congr (by ext z; simp only [auxPhi, Pi.mul_apply, Pi.inv_apply, div_eq_mul_inv])

end ThreeIM
