module

public import RequestProject.ThreeIM.TwoCMMixedDouble

/-!
# Excluding the zero-scalar canonical mixed case

The reciprocal difference has no poles and has small characteristic after
the second main theorem is applied to the two double fibers. Its values on
these fibers then make both reduced counts small, giving a contradiction.
-/

@[expose] public section

open Filter Set Topology ValueDistribution Real

namespace ThreeIM

private theorem mixed_zero_sum_three_cyclic (R : Fin 3 → ℝ) (j : Fin 3) :
    ∑ i, R i = R j + R (j + 1) + R (j + 2) := by
  fin_cases j <;> simp [Fin.sum_univ_three] <;> ring

theorem twoCM_charT_reciprocalDifference_small {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair univ f g a) (j : Fin 3)
    (hcm : SharesCMOn univ f g (a j : Sphere)) (k : ℂ)
    (hnn : ∀ z, 0 ≤ meromorphicOrderAt (twoCMReciprocalDifference (a j) k f g) z)
    (hpole : ∃ C : ℝ, OutsideFiniteMeasure fun r => logCounting f ⊤ r ≤ C * pairL f g r)
    (hother : ∃ K : ℝ, ∀ r : ℝ, 1 ≤ r →
      reducedCounting f (a (j + 1) : Sphere) r + reducedCounting f (a (j + 2) : Sphere) r ≤ pairT f g r + K) :
    ∃ C : ℝ, OutsideFiniteMeasure fun r =>
      charT (twoCMReciprocalDifference (a j) k f g) r ≤ C * pairL f g r := by
  obtain ⟨Cp, hCp⟩ := hpole
  obtain ⟨Kb, hKb⟩ := hother
  obtain ⟨KH, hKH⟩ := twoCM_charT_reciprocalDifference_le hp.nonconst_f hp.nonconst_g (a j) k hcm hnn
  obtain ⟨Cs, hCs0, hCs⟩ := second_main_pair_max hp
  refine ⟨2 * |Cp| + 2 * Cs + 2 * |Kb| + |KH|, (hCp.and hCs).mono fun r hr ⟨hpole, hs⟩ => ?_⟩
  rw [mixed_zero_sum_three_cyclic (fun i => reducedCounting f (a i : Sphere) r) j] at hs
  have hL := one_le_pairL (f := f) (g := g) hr
  have hL0 : 0 ≤ pairL f g r := by linarith
  have hredA := reducedCounting_le_logCounting hp.nonconst_f.1 (a j : Sphere) hr
  have hredP := reducedCounting_le_logCounting hp.nonconst_f.1 ⊤ hr
  have hKbL := le_mul_of_one_le_right (abs_nonneg Kb) hL
  have hKHL := le_mul_of_one_le_right (abs_nonneg KH) hL
  have hCpL := mul_le_mul_of_nonneg_right (le_abs_self Cp) hL0
  have hTf : charT f r ≤ pairT f g r := le_max_left _ _
  have hTg : charT g r ≤ pairT f g r := le_max_right _ _
  rw [add_mul, add_mul, add_mul]
  nlinarith [hKH r hr, hKb r hr, le_abs_self Kb, le_abs_self KH]

theorem twoCM_false_of_small_reciprocalDifference {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair univ f g a) (j : Fin 3) (k : ℂ)
    (hH : IsNonconstMeroOn (twoCMReciprocalDifference (a j) k f g) univ)
    (hsmall : ∃ C : ℝ, OutsideFiniteMeasure fun r =>
      charT (twoCMReciprocalDifference (a j) k f g) r ≤ C * pairL f g r)
    (hpole : ∃ C : ℝ, OutsideFiniteMeasure fun r => logCounting f ⊤ r ≤ C * pairL f g r)
    (hgrowth : ∃ c > 0, ∀ᶠ r in atTop, c * r ≤ pairT f g r) : False := by
  obtain ⟨CH, hCH⟩ := hsmall
  obtain ⟨Cp, hCp⟩ := hpole
  obtain ⟨Cs, hCs0, hCs⟩ := second_main_pair_max hp
  let H := twoCMReciprocalDifference (a j) k f g
  let b := a (j + 1)
  let c := a (j + 2)
  let vb := (b - a j)⁻¹ - k * (b - a j)⁻¹
  let vc := (c - a j)⁻¹ - k * (c - a j)⁻¹
  obtain ⟨Kb, hKb⟩ := twoCM_logCounting_finite_le_charT hH.meromorphic vb
  obtain ⟨Kc, hKc⟩ := twoCM_logCounting_finite_le_charT hH.meromorphic vc
  obtain ⟨Ka, hKa⟩ := twoCM_logCounting_finite_le_charT hp.nonconst_f.meromorphic (a j)
  have hbne : b ≠ a j := hp.injective.ne (by fin_cases j <;> decide)
  have hcne : c ≠ a j := hp.injective.ne (by fin_cases j <;> decide)
  have hbound : ∃ C : ℝ, OutsideFiniteMeasure fun r => pairT f g r ≤ C * pairL f g r := by
    refine ⟨2 * |CH| + |Cp| + Cs + |Kb| + |Kc| + |Ka|,
      ((hCH.and hCp).and hCs).mono fun r hr ⟨⟨hHbound, hpole⟩, hs⟩ => ?_⟩
    have hredB := twoCM_reducedCounting_le_reciprocalDifference hp.nonconst_f hp.nonconst_g hH hbne
      (hp.im (j + 1)) hr
    have hredC := twoCM_reducedCounting_le_reciprocalDifference hp.nonconst_f hp.nonconst_g hH hcne
      (hp.im (j + 2)) hr
    have hredA := reducedCounting_le_logCounting hp.nonconst_f.1 (a j : Sphere) hr
    have hredP := reducedCounting_le_logCounting hp.nonconst_f.1 ⊤ hr
    rw [mixed_zero_sum_three_cyclic (fun i => reducedCounting f (a i : Sphere) r) j] at hs
    have hL := one_le_pairL (f := f) (g := g) hr
    have hL0 : 0 ≤ pairL f g r := by linarith
    have hCHL := mul_le_mul_of_nonneg_right (le_abs_self CH) hL0
    have hCpL := mul_le_mul_of_nonneg_right (le_abs_self Cp) hL0
    have hKbL := le_mul_of_one_le_right (abs_nonneg Kb) hL
    have hKcL := le_mul_of_one_le_right (abs_nonneg Kc) hL
    have hKaL := le_mul_of_one_le_right (abs_nonneg Ka) hL
    have hTf : charT f r ≤ pairT f g r := le_max_left _ _
    rw [add_mul, add_mul, add_mul, add_mul, add_mul]
    dsimp only [H, vb, vc, b, c] at hKb hKc
    nlinarith [hKb r hr, hKc r hr, hKa r hr, le_abs_self Kb, le_abs_self Kc, le_abs_self Ka]
  obtain ⟨C, hC⟩ := hbound
  obtain ⟨c, hc, hG⟩ := hgrowth
  apply false_of_linear_growth hc hG
  apply hC.mono
  intro r hr h
  change pairT f g r ≤ |C| * (pairL f g r + log r)
  have hL0 : 0 ≤ pairL f g r := by linarith [one_le_pairL (f := f) (g := g) hr]
  have hlog : 0 ≤ log r := Real.log_nonneg hr
  exact h.trans ((mul_le_mul_of_nonneg_right (le_abs_self C) hL0).trans
    (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg C)))

theorem twoCM_false_of_canonical_mixed_zero {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair univ f g a) (j : Fin 3)
    (hcm : SharesCMOn univ f g (a j : Sphere))
    (hdefect : ∃ d z, IsDefect f g (a d : Sphere) z)
    (hgrowth : ∃ c > 0, ∀ᶠ r in atTop, c * r ≤ pairT f g r)
    (hpole : ∃ C : ℝ, OutsideFiniteMeasure fun r => logCounting f ⊤ r ≤ C * pairL f g r)
    (hc : cAux a j = 0) (hW : ∀ z, meromorphicOrderAt (twoCMWChi a j f g) z = ⊤) : False := by
  have hchi := twoCM_chi_zero_of_cAux_zero j hc hW
  obtain ⟨k, hk, hquad⟩ := twoCM_quarticDerivative_ratio_of_chi_zero hp j hchi
  have hH := twoCM_reciprocalDifference_nonconst_of_defect hp hdefect (a j) hk
  have hHnn := twoCM_reciprocalDifference_order_nonneg hp j hcm hc hquad
  have hrel := twoCM_multiplicity_relation_of_quartic hp j hcm hdefect hc hk hquad
  have hdouble := twoCM_double_other_fibers_of_ratio hp j hcm hdefect k hrel
  have hother := twoCM_reduced_other_sum_le_pairT_of_double hp j hdouble
  have hsmall := twoCM_charT_reciprocalDifference_small hp j hcm k hHnn hpole hother
  exact twoCM_false_of_small_reciprocalDifference hp j k hH hsmall hpole hgrowth

end ThreeIM
