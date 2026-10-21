module

public import RequestProject.ThreeIM.TwoCMMixedEtaZero
public import RequestProject.ThreeIM.TwoCMMixedNonzeroReduction

/-!
# The global counting comparison for the mixed case
-/

@[expose] public section

open Filter Set Topology ValueDistribution Real

namespace ThreeIM

theorem twoCM_complementary_bound_of_aux {f g F : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair univ f g a) (j i : Fin 3) (hF : Meromorphic F)
    (hcount : ∀ r : ℝ, 1 ≤ r →
      logCounting f (a j : Sphere) r ≤ logCounting F 0 r + logCounting (auxPsi a f g) 0 r)
    (hT : ∃ C : ℝ, OutsideFiniteMeasure fun r =>
      charT F r + reducedCounting f (a i : Sphere) r ≤ pairT f g r + C * pairL f g r) :
    ∃ C : ℝ, OutsideFiniteMeasure fun r =>
      logCounting f (a j : Sphere) r + reducedCounting f (a i : Sphere) r ≤
        pairT f g r + C * pairL f g r := by
  obtain ⟨C, hC⟩ := hT
  obtain ⟨Cψ, hCψ⟩ := logCounting_auxPsi_zero_le hp
  obtain ⟨K, hK⟩ := logCounting_zero_le_charT hF
  refine ⟨C + Cψ + |K|, (hC.and hCψ).mono fun r hr ⟨hFbound, hPsi⟩ => ?_⟩
  have hKL : K ≤ |K| * pairL f g r :=
    (le_abs_self K).trans (le_mul_of_one_le_right (abs_nonneg K) (one_le_pairL hr))
  rw [add_mul, add_mul]
  linarith [hcount r hr, hK r hr]

private theorem mixed_eta_sum_three_cyclic (R : Fin 3 → ℝ) (j : Fin 3) :
    ∑ i, R i = R j + R (j + 1) + R (j + 2) := by
  fin_cases j <;> simp [Fin.sum_univ_three] <;> ring

theorem twoCM_false_of_mixed_complementary_bounds {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair univ f g a) (j : Fin 3)
    (hcm : SharesCMOn univ f g (a j : Sphere))
    (hdefect : ∃ d z, IsDefect f g (a d : Sphere) z)
    (hgrowth : ∃ c > 0, ∀ᶠ r in atTop, c * r ≤ pairT f g r)
    (hpole : ∃ C : ℝ, OutsideFiniteMeasure fun r => logCounting f ⊤ r ≤ C * pairL f g r)
    (hb : ∃ C : ℝ, OutsideFiniteMeasure fun r =>
      logCounting f (a j : Sphere) r + reducedCounting f (a (j + 1) : Sphere) r ≤
        pairT f g r + C * pairL f g r)
    (hc : ∃ C : ℝ, OutsideFiniteMeasure fun r =>
      logCounting f (a j : Sphere) r + reducedCounting f (a (j + 2) : Sphere) r ≤
        pairT f g r + C * pairL f g r) : False := by
  obtain ⟨Cb, hCb⟩ := hb
  obtain ⟨Cc, hCc⟩ := hc
  obtain ⟨Cp, hCp⟩ := hpole
  obtain ⟨Cs, hCs0, hCs⟩ := second_main_pair_max hp
  have hfinite : ∃ C : ℝ, OutsideFiniteMeasure fun r =>
      logCounting f (a j : Sphere) r ≤ C * pairL f g r := by
    refine ⟨Cb + Cc + Cp + Cs,
      (((hCb.and hCc).and hCp).and hCs).mono fun r hr ⟨⟨⟨hb, hc⟩, hpole⟩, hs⟩ => ?_⟩
    have hredA := reducedCounting_le_logCounting hp.nonconst_f.1 (a j : Sphere) hr
    have hredP := reducedCounting_le_logCounting hp.nonconst_f.1 ⊤ hr
    rw [mixed_eta_sum_three_cyclic (fun i => reducedCounting f (a i : Sphere) r) j] at hs
    rw [add_mul, add_mul, add_mul]
    linarith
  exact twoCM_false_of_both_counts_small hp j hcm hdefect hgrowth hfinite ⟨Cp, hCp⟩

end ThreeIM
