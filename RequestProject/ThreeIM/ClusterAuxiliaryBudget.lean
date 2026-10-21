module

public import RequestProject.ThreeIM.ClusterRelativeGrowth
public import RequestProject.ThreeIM.ClusterAuxiliaryDivisor
public import RequestProject.ThreeIM.ClusterPairControl

/-! # The original finite-disk coefficient mass is O(pairL)

The ratio's coarse characteristic bound and its genuine divisor support
are both proved from the normalized pair. Ratio nonconstancy is supplied
in the exact expanded form already present in PeriodicCounterexample.
-/

@[expose] public section

set_option autoImplicit false

open Set Filter ValueDistribution Real

namespace ThreeIM

/-- Taking a logarithm turns the coarse bound into the pair's original
logarithmic error. The eventual lower bound on pairT follows from the
nonconstant first member; it is not an added growth assumption. -/
theorem PairCoarseCharacteristicBound.log_characteristic {f g H : ℂ → ℂ}
    (hH : PairCoarseCharacteristicBound f g H) (hf : IsNonconstMeroOn f univ) :
    ∃ C : ℝ, OutsideFiniteMeasure fun r =>
      Real.log (Real.exp 1 + r * charT H r) ≤ C * pairL f g r := by
  obtain ⟨K, hK⟩ := hH
  obtain ⟨r0, hr0⟩ := one_le_charT_eventually hf
  have hT : OutsideFiniteMeasure fun r => 1 ≤ pairT f g r := by
    refine ⟨∅, MeasurableSet.empty, by simp, r0, fun r hr _ => ?_⟩
    exact (hr0 r hr).trans (le_max_left _ _)
  let C := |K| + 1
  refine ⟨|Real.log (1 + 2 * C)| + 2, (hK.and hT).mono fun r hr ⟨hb, hT1⟩ => ?_⟩
  let S := Real.exp 1 + r * pairT f g r
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp zero_le_one
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  have hr0 : 0 ≤ r := by linarith
  have hP0 : 0 ≤ pairT f g r := by linarith
  have hS0 : 0 < S := add_pos_of_pos_of_nonneg he0 (mul_nonneg hr0 hP0)
  have heS : Real.exp 1 ≤ S := le_add_of_nonneg_right (mul_nonneg hr0 hP0)
  have hS1 : 1 ≤ S := he1.trans heS
  have hL : 1 ≤ pairL f g r := one_le_pairL hr
  have hLS : pairL f g r ≤ S := by
    change Real.log S ≤ S
    linarith [Real.log_le_sub_one_of_pos hS0]
  have hPS : pairT f g r ≤ S :=
    (le_mul_of_one_le_left hP0 hr).trans (le_add_of_nonneg_left he0.le)
  have hscale : 0 ≤ pairT f g r + pairL f g r := by linarith
  have hC : 0 < C := by dsimp [C]; positivity
  have hKC : K ≤ C := by dsimp [C]; linarith [le_abs_self K]
  have hHbound : charT H r ≤ 2 * C * S := by
    calc
      charT H r ≤ K * (pairT f g r + pairL f g r) := hb
      _ ≤ C * (pairT f g r + pairL f g r) := mul_le_mul_of_nonneg_right hKC hscale
      _ ≤ C * (2 * S) := mul_le_mul_of_nonneg_left (by linarith only [hPS, hLS]) hC.le
      _ = 2 * C * S := by ring
  have hrS : r ≤ S :=
    (le_mul_of_one_le_right hr0 hT1).trans (le_add_of_nonneg_left he0.le)
  have hSq : S ≤ S ^ 2 := by
    calc
      S = 1 * S := by ring
      _ ≤ S * S := mul_le_mul_of_nonneg_right hS1 hS0.le
      _ = S ^ 2 := by ring
  have hYbound : Real.exp 1 + r * charT H r ≤ (1 + 2 * C) * S ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hHbound hr0
    have h2 := mul_le_mul_of_nonneg_right hrS (show 0 ≤ 2 * C * S by positivity)
    nlinarith only [h1, h2, heS, hSq]
  have hYpos : 0 < Real.exp 1 + r * charT H r :=
    add_pos_of_pos_of_nonneg he0 (mul_nonneg hr0 (charT_nonneg (h := H) hr))
  have hClog : 0 < 1 + 2 * C := by linarith
  have hlog := Real.log_le_log hYpos hYbound
  rw [Real.log_mul hClog.ne' (pow_pos hS0 2).ne', Real.log_pow] at hlog
  have hconst : Real.log (1 + 2 * C) ≤ |Real.log (1 + 2 * C)| * pairL f g r :=
    (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hL)
  change Real.log (Real.exp 1 + r * charT H r) ≤ _
  change Real.log (Real.exp 1 + r * charT H r) ≤ Real.log (1 + 2 * C) + 2 * pairL f g r at hlog
  rw [add_mul]
  linarith only [hlog, hconst]

/-- Small characteristic is preserved by reciprocation with the genuine
first-main-theorem constant, not a raw center-value identity. -/
theorem pairL_characteristic_inverse {f g H : ℂ → ℂ} (hHm : Meromorphic H)
    (hH : ∃ C : ℝ, OutsideFiniteMeasure fun r => charT H r ≤ C * pairL f g r) :
    ∃ C : ℝ, OutsideFiniteMeasure fun r => charT H⁻¹ r ≤ C * pairL f g r := by
  obtain ⟨C, hC⟩ := hH
  let K := max |log ‖H 0‖| |log ‖meromorphicTrailingCoeffAt H 0‖|
  refine ⟨|C| + K, hC.mono fun r hr h => ?_⟩
  have hL := one_le_pairL (f := f) (g := g) hr
  have hK : 0 ≤ K := (abs_nonneg _).trans (le_max_left _ _)
  have hc := mul_le_mul_of_nonneg_right (le_abs_self C) (show 0 ≤ pairL f g r by linarith)
  have hk := le_mul_of_one_le_right hK hL
  have hInv := characteristic_sub_characteristic_inv_le hHm (R := r)
  change |charT H r - charT H⁻¹ r| ≤ K at hInv
  have hlow := (abs_le.mp hInv).1
  rw [add_mul]
  linarith only [h, hc, hk, hlow]

theorem NormalizedPair.proximity_logDeriv_auxPhi_le_pairL
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} (hp : NormalizedPair univ f g a)
    (hNC : ∀ c z, meromorphicOrderAt (fun w => auxPhi a f g w - c) z ≠ ⊤) :
    ∃ C : ℝ, OutsideFiniteMeasure fun r =>
      proximity (logDeriv (auxPhi a f g)) ⊤ r ≤ C * pairL f g r := by
  have hPhi : IsNonconstMeroOn (auxPhi a f g) univ :=
    ⟨fun z _ => hp.meromorphic_auxPhi z, fun z _ c => hNC c z⟩
  obtain ⟨C, hC⟩ := log_derivative_estimate hPhi 0
  obtain ⟨D, hD⟩ := hp.coarse_characteristic_auxPhi.log_characteristic hp.nonconst_f
  refine ⟨|C| * |D|, (hC.and hD).mono fun r hr ⟨h1, h2⟩ => ?_⟩
  have hL0 : 0 ≤ pairL f g r := by linarith [one_le_pairL (f := f) (g := g) hr]
  have hlog0 : 0 ≤ Real.log (Real.exp 1 + r * charT (auxPhi a f g) r) :=
    Real.log_nonneg (by nlinarith [charT_nonneg (h := auxPhi a f g) hr, Real.add_one_le_exp 1])
  have h1' : proximity (logDeriv (auxPhi a f g)) ⊤ r ≤
      C * Real.log (Real.exp 1 + r * charT (auxPhi a f g) r) := by
    have hfun : logDeriv (auxPhi a f g) =
        (fun z => deriv (auxPhi a f g) z / auxPhi a f g z) := by
      funext z
      exact logDeriv_apply _ _
    simpa only [sub_zero, hfun] using h1
  calc
    _ ≤ C * Real.log (Real.exp 1 + r * charT (auxPhi a f g) r) := h1'
    _ ≤ |C| * Real.log (Real.exp 1 + r * charT (auxPhi a f g) r) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) hlog0
    _ ≤ |C| * (|D| * pairL f g r) := mul_le_mul_of_nonneg_left
      (h2.trans (mul_le_mul_of_nonneg_right (le_abs_self D) hL0)) (abs_nonneg C)
    _ = _ := by ring

theorem NormalizedPair.charT_logDeriv_auxPhi_le_pairL
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} (hp : NormalizedPair univ f g a)
    (hNC : ∀ c z, meromorphicOrderAt (fun w => auxPhi a f g w - c) z ≠ ⊤) :
    ∃ C : ℝ, OutsideFiniteMeasure fun r =>
      charT (logDeriv (auxPhi a f g)) r ≤ C * pairL f g r := by
  obtain ⟨C, hC⟩ := hp.proximity_logDeriv_auxPhi_le_pairL hNC
  obtain ⟨D, hD⟩ := logCounting_auxPsi_zero_le hp
  refine ⟨|C| + |D|, (hC.and hD).mono fun r hr ⟨h1, h2⟩ => ?_⟩
  have hL0 : 0 ≤ pairL f g r := by linarith [one_le_pairL (f := f) (g := g) hr]
  have hc := mul_le_mul_of_nonneg_right (le_abs_self C) hL0
  have hd := mul_le_mul_of_nonneg_right (le_abs_self D) hL0
  have hcount := hp.logCounting_logDeriv_auxPhi_le_auxPsi hr
  change proximity (logDeriv (auxPhi a f g)) ⊤ r +
    logCounting (logDeriv (auxPhi a f g)) ⊤ r ≤ _
  rw [add_mul]
  linarith only [h1, h2, hc, hd, hcount]

/-- Every term in the source's exact M is controlled by the original L.
The only nonconstancy input is the original ratio nonconstancy field. -/
theorem NormalizedPair.finiteDiskCoefficientMass_le_pairL
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} (hp : NormalizedPair univ f g a)
    (hNC : ∀ c z, meromorphicOrderAt (fun w => auxPhi a f g w - c) z ≠ ⊤) :
    ∃ C : ℝ, 0 < C ∧ OutsideFiniteMeasure fun r =>
      finiteDiskCoefficientMass (auxPhi a f g) (logDeriv (auxPhi a f g)) (auxPsi a f g) r ≤ C * pairL f g r := by
  have hA : Meromorphic (logDeriv (auxPhi a f g)) := fun z =>
    (hp.meromorphic_auxPhi z).deriv.div (hp.meromorphic_auxPhi z)
  obtain ⟨CA, hCA⟩ := hp.charT_logDeriv_auxPhi_le_pairL hNC
  obtain ⟨CI, hCI⟩ := pairL_characteristic_inverse hA ⟨CA, hCA⟩
  obtain ⟨CP, hCP⟩ := charT_auxPsi_le hp
  obtain ⟨CJ, hCJ⟩ := pairL_characteristic_inverse hp.meromorphic_auxPsi ⟨CP, hCP⟩
  obtain ⟨CN, hCN⟩ := hp.auxPhi_zero_pole_count_le_pairL
  refine ⟨1 + |CA| + |CI| + |CP| + |CJ| + |CN|, by positivity,
    ((((hCA.and hCI).and hCP).and hCJ).and hCN).mono fun r hr ⟨⟨⟨⟨ha, hi⟩, hp0⟩, hj⟩, hn⟩ => ?_⟩
  have hL := one_le_pairL (f := f) (g := g) hr
  have hL0 : 0 ≤ pairL f g r := by linarith
  have ea := mul_le_mul_of_nonneg_right (le_abs_self CA) hL0
  have ei := mul_le_mul_of_nonneg_right (le_abs_self CI) hL0
  have ep := mul_le_mul_of_nonneg_right (le_abs_self CP) hL0
  have ej := mul_le_mul_of_nonneg_right (le_abs_self CJ) hL0
  have en := mul_le_mul_of_nonneg_right (le_abs_self CN) hL0
  unfold finiteDiskCoefficientMass
  change 1 + charT (logDeriv (auxPhi a f g)) r + charT (logDeriv (auxPhi a f g))⁻¹ r +
    charT (auxPsi a f g) r + charT (auxPsi a f g)⁻¹ r +
    logCounting (auxPhi a f g) ⊤ r + logCounting (auxPhi a f g)⁻¹ ⊤ r ≤ _
  simp only [add_mul, one_mul]
  linarith only [ha, hi, hp0, hj, hn, ea, ei, ep, ej, en, hL]

end ThreeIM
