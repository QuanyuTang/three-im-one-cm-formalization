module

public import RequestProject.ThreeIM.TwoCMTargetSwap

/-!
# Reduction to one mixed case

Target inversion transports small counting functions with their actual
exceptional sets. Reapplying the proved dichotomy then removes the need to
analyse both orientations separately.
-/

@[expose] public section

open Filter Set Topology ValueDistribution Real

namespace ThreeIM

theorem twoCM_pairL_targetSwap_le {f g : ℂ → ℂ}
    (hf : IsNonconstMeroOn f univ) (hg : IsNonconstMeroOn g univ) (c : ℂ) :
    ∃ D : ℝ, 0 ≤ D ∧ OutsideFiniteMeasure fun r =>
      pairL f g r ≤ D * pairL (fun w => (f w - c)⁻¹) (fun w => (g w - c)⁻¹) r := by
  let F : ℂ → ℂ := fun w => (f w - c)⁻¹
  let G : ℂ → ℂ := fun w => (g w - c)⁻¹
  obtain ⟨K, hK0, hK⟩ := twoCM_pairT_targetSwap_abs_le hf hg c
  obtain ⟨r₀, hr₀⟩ := one_le_charT_eventually (twoCM_nonconst_targetSwap hf c)
  have hlogK : 0 ≤ log (K + 1) := Real.log_nonneg (by linarith)
  refine ⟨1 + log (K + 1), by positivity,
    OutsideFiniteMeasure.of_ge (r₀ := max r₀ 1) fun r hr => ?_⟩
  have hr1 : 1 ≤ r := le_trans (le_max_right _ _) hr
  have hnew : 1 ≤ pairT F G r := (hr₀ r (le_trans (le_max_left _ _) hr)).trans (le_max_left _ _)
  have hnew0 : 0 ≤ pairT F G r := by linarith
  have hupper : pairT f g r ≤ pairT F G r + K := by
    have hb := (abs_le.1 (hK r hr1)).1
    change -K ≤ pairT F G r - pairT f g r at hb
    linarith
  have hbase : 0 < exp 1 + r * pairT F G r := by positivity
  have hbase_r : 0 ≤ exp 1 + r * pairT F G r - r := by
    nlinarith [Real.exp_pos 1]
  have harg : exp 1 + r * pairT f g r ≤ (K + 1) * (exp 1 + r * pairT F G r) := by
    nlinarith [mul_nonneg hK0 hbase_r, mul_le_mul_of_nonneg_left hupper (by linarith : 0 ≤ r)]
  have holdpos : 0 < exp 1 + r * pairT f g r := by
    have hT : 0 ≤ pairT f g r := le_max_of_le_left (charT_nonneg (h := f) hr1)
    positivity
  have hl := Real.log_le_log holdpos harg
  rw [Real.log_mul (by linarith : K + 1 ≠ 0) (ne_of_gt hbase)] at hl
  change pairL f g r ≤ (1 + log (K + 1)) * pairL F G r
  change pairL f g r ≤ log (K + 1) + pairL F G r at hl
  nlinarith [one_le_pairL (f := F) (g := G) hr1]

theorem twoCM_small_count_targetSwap {f g : ℂ → ℂ}
    (hf : IsNonconstMeroOn f univ) (hg : IsNonconstMeroOn g univ)
    (c : ℂ) (b : Sphere)
    (hsmall : ∃ C : ℝ, OutsideFiniteMeasure fun r => logCounting f b r ≤ C * pairL f g r) :
    ∃ C : ℝ, OutsideFiniteMeasure fun r =>
      logCounting (fun w => (f w - c)⁻¹) (mobius c b) r ≤
        C * pairL (fun w => (f w - c)⁻¹) (fun w => (g w - c)⁻¹) r := by
  obtain ⟨C, hC⟩ := hsmall
  obtain ⟨D, hD0, hD⟩ := twoCM_pairL_targetSwap_le hf hg c
  refine ⟨|C| * D, (hC.and hD).mono fun r hr ⟨hcount, hL⟩ => ?_⟩
  rw [congrFun (twoCM_logCounting_targetSwap hf.meromorphic c b) r]
  have hold0 : 0 ≤ pairL f g r := by linarith [one_le_pairL (f := f) (g := g) hr]
  calc logCounting f b r ≤ C * pairL f g r := hcount
    _ ≤ |C| * pairL f g r := mul_le_mul_of_nonneg_right (le_abs_self C) hold0
    _ ≤ |C| * (D * pairL (fun w => (f w - c)⁻¹) (fun w => (g w - c)⁻¹) r) :=
      mul_le_mul_of_nonneg_left hL (abs_nonneg C)
    _ = _ := by ring

/-- Any two-CM counterexample gives one in the orientation with small pole
count and the squared chi identity. No scalar nonvanishing is assumed. -/
theorem TwoCMPeriodicCounterexample.exists_canonical_mixed {f g : ℂ → ℂ}
    {a : Fin 3 → ℂ} {j : Fin 3} (hP : TwoCMPeriodicCounterexample a j f g) :
    ∃ (b : Fin 3 → ℂ) (k : Fin 3) (F G : ℂ → ℂ),
      TwoCMPeriodicCounterexample b k F G ∧
      (∃ C : ℝ, OutsideFiniteMeasure fun r => logCounting F ⊤ r ≤ C * pairL F G r) ∧
      (∀ z, meromorphicOrderAt (twoCMWChi b k F G) z = ⊤) := by
  rcases hP.two_cases with hfirst | hsecond
  · exact ⟨a, j, f, g, hP, hfirst⟩
  · have hnew := hP.targetSwap
    have hpole : ∃ C : ℝ, OutsideFiniteMeasure fun r =>
        logCounting (fun w => (f w - a j)⁻¹) ⊤ r ≤
          C * pairL (fun w => (f w - a j)⁻¹) (fun w => (g w - a j)⁻¹) r := by
      simpa using twoCM_small_count_targetSwap hP.pair.nonconst_f hP.pair.nonconst_g
        (a j) (a j : Sphere) hsecond.2
    rcases hnew.two_cases with hfirst | hsecond
    · exact ⟨twoCMSwapTargets a j, j, _, _, hnew, hfirst⟩
    · exact (twoCM_false_of_both_counts_small hnew.pair j hnew.cm_finite hnew.defect
        hnew.linear_growth hsecond.2 hpole).elim

end ThreeIM
