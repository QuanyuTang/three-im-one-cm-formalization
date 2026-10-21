module

public import RequestProject.ThreeIM.LambdaProximity
public import RequestProject.ThreeIM.TwoCMAuxiliary
public import RequestProject.ThreeIM.SharedValueCounting

/-!
# Counting estimates leading to defect density

The finite-fiber estimates retain explicit witnesses of a defect over each
marked finite value. Those witnesses ensure that the corresponding Lambda
differences are nonzero germs. No two-CM theorem is asserted in this module.
-/

@[expose] public section

open Filter Set Topology ValueDistribution Real

namespace ThreeIM

/-- The characteristic of each Lambda difference is controlled by the total
reduced defect count, with the common logarithmic error. -/
theorem charT_EAux_le_defect (hp : NormalizedPair univ f g a) (j : Fin 3) :
    ∃ C : ℝ, OutsideFiniteMeasure fun r =>
      charT (EAux a j f g) r ≤ totalDefectCounting a f g r + C * pairL f g r := by
  obtain ⟨CE, hCE⟩ := proximity_EAux_single_le hp j
  obtain ⟨CP, hCP⟩ := logCounting_auxPsi_zero_le hp
  refine ⟨CE + CP, (hCE.and hCP).mono fun r hr ⟨hE, hP⟩ => ?_⟩
  have hN := logCounting_EAux_top_le hp j hr
  change proximity (EAux a j f g) ⊤ r + logCounting (EAux a j f g) ⊤ r ≤ _
  rw [add_mul]
  linarith

/-- The zero count of each Lambda difference has the same defect bound. -/
theorem logCounting_EAux_zero_le_defect (hp : NormalizedPair univ f g a) (j : Fin 3) :
    ∃ C : ℝ, OutsideFiniteMeasure fun r =>
      logCounting (EAux a j f g) 0 r ≤ totalDefectCounting a f g r + C * pairL f g r := by
  have hEm : Meromorphic (EAux a j f g) := fun z =>
    meromorphicAt_EAux (hp.nonconst_f.meromorphic z) (hp.nonconst_g.meromorphic z) a j
  obtain ⟨K, hK⟩ := logCounting_zero_le_charT hEm
  obtain ⟨C, hC⟩ := charT_EAux_le_defect hp j
  refine ⟨C + |K|, hC.mono fun r hr h => ?_⟩
  have hL := one_le_pairL (f := f) (g := g) hr
  have hconst : K ≤ |K| * pairL f g r :=
    (le_abs_self K).trans (le_mul_of_one_le_right (abs_nonneg K) hL)
  have hfirst := hK r hr
  rw [add_mul]
  linarith

/-- The three finite reduced fibers cost at most four times the total
reduced defects, provided every selected Lambda difference has a defect witness. -/
theorem finite_reducedCounting_le_four_defects (hp : NormalizedPair univ f g a)
    (hdefects : ∀ j, ∃ z₀, IsDefect f g (a j : Sphere) z₀) :
    ∃ C : ℝ, OutsideFiniteMeasure fun r =>
      (∑ j, reducedCounting f (a j : Sphere) r) ≤
        4 * totalDefectCounting a f g r + C * pairL f g r := by
  obtain ⟨C0, hC0⟩ := logCounting_EAux_zero_le_defect hp 0
  obtain ⟨C1, hC1⟩ := logCounting_EAux_zero_le_defect hp 1
  obtain ⟨C2, hC2⟩ := logCounting_EAux_zero_le_defect hp 2
  obtain ⟨CP, hCP⟩ := logCounting_auxPsi_zero_le hp
  refine ⟨C0 + C1 + C2 + 3 * CP,
    (((hC0.and hC1).and hC2).and hCP).mono fun r hr ⟨⟨⟨h0, h1⟩, h2⟩, hP⟩ => ?_⟩
  have h := sum_reducedCounting_finite_le_defect_EAux hp hdefects hr
  simp only [Fin.sum_univ_three] at h
  simp only [Fin.sum_univ_three]
  rw [add_mul, add_mul, add_mul, mul_assoc]
  linarith

/-- The counting inequality `2 T ≤ 5 D_total + O(L)`. The explicit defect
witnesses ensure nonvanishing of the three Lambda differences and of `H`. -/
theorem two_pairT_le_five_defects (hp : NormalizedPair univ f g a)
    (hdefects : ∀ j, ∃ z₀, IsDefect f g (a j : Sphere) z₀) :
    ∃ C : ℝ, OutsideFiniteMeasure fun r =>
      2 * pairT f g r ≤ 5 * totalDefectCounting a f g r + C * pairL f g r := by
  obtain ⟨CF, hCF⟩ := finite_reducedCounting_le_four_defects hp hdefects
  obtain ⟨z₀, hz₀⟩ := hdefects 0
  obtain ⟨CP, hCP⟩ := reducedCounting_top_le_defect hp ⟨0, z₀, hz₀⟩
  obtain ⟨CSf, hCSf⟩ := second_main_finite hp.nonconst_f a hp.injective
  obtain ⟨CSg, hCSg⟩ := second_main_finite hp.nonconst_g a hp.injective
  have hred (j : Fin 3) (r : ℝ) : reducedCounting g (a j : Sphere) r =
      reducedCounting f (a j : Sphere) r := (reducedCounting_eq_of_sharesIM (hp.im j) r).symm
  have htop (r : ℝ) : reducedCounting g ⊤ r = reducedCounting f ⊤ r :=
    (reducedCounting_eq_of_sharesIM (fun z hz => by rw [hp.cm_top z hz]) r).symm
  refine ⟨CF + CP + |CSf| + |CSg|,
    (((hCF.and hCP).and hCSf).and hCSg).mono fun r hr ⟨⟨⟨hF, hP⟩, hSf⟩, hSg⟩ => ?_⟩
  norm_num only [Nat.cast_ofNat, show (3 : ℝ) - 1 = 2 by norm_num] at hSf hSg
  simp only [hred, htop] at hSg
  have hL := one_le_pairL (f := f) (g := g) hr
  have hLf0 : 0 ≤ log (exp 1 + r * charT f r) := Real.log_nonneg (by
    nlinarith [charT_nonneg (h := f) hr, Real.add_one_le_exp (1 : ℝ)])
  have hLg0 : 0 ≤ log (exp 1 + r * charT g r) := Real.log_nonneg (by
    nlinarith [charT_nonneg (h := g) hr, Real.add_one_le_exp (1 : ℝ)])
  have hSferr := (mul_le_mul_of_nonneg_right (le_abs_self CSf) hLf0).trans
    (mul_le_mul_of_nonneg_left (log_charT_le_pairL_left (f := f) (g := g) hr) (abs_nonneg CSf))
  have hSgerr := (mul_le_mul_of_nonneg_right (le_abs_self CSg) hLg0).trans
    (mul_le_mul_of_nonneg_left (log_charT_le_pairL_right (f := f) (g := g) hr) (abs_nonneg CSg))
  have hSf0 : 0 ≤ |CSf| * pairL f g r := mul_nonneg (abs_nonneg CSf) (by linarith)
  have hSg0 : 0 ≤ |CSg| * pairL f g r := mul_nonneg (abs_nonneg CSg) (by linarith)
  rw [add_mul, add_mul, add_mul]
  rcases le_total (charT f r) (charT g r) with hfg | hgf
  · simp only [pairT, max_eq_right hfg]
    linarith
  · simp only [pairT, max_eq_left hgf]
    linarith

end ThreeIM
