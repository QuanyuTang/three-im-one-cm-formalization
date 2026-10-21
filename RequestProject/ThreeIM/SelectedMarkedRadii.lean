module

public import RequestProject.ThreeIM.SelectedCountingErrors
public import RequestProject.ThreeIM.Growth
public import RequestProject.ThreeIM.FiniteExceptions

/-! # Global radii with enough genuine retained marks

Both the inner density estimate and outer coefficient estimate hold at
the chosen radii, outside their common set of finite linear measure.
The output uses the exact finite-disk branch parameter, with no added
order assumption beyond the original infinite-order counterexample.
-/

@[expose] public section

set_option autoImplicit false

open Filter Set Real Topology MeasureTheory

namespace ThreeIM

/-- Incorporate an actual finite-measure estimate at both chosen radii.
Its starting radius is handled by a genuine strict extraction. -/
theorem selected_good_growth_radii_with_estimates
    {f g : ℂ → ℂ} (hf : MeromorphicOn f univ) (hg : MeromorphicOn g univ)
    (hInf : InfiniteOrder f ∨ InfiniteOrder g) {P : ℝ → Prop}
    (hP : OutsideFiniteMeasure P) (p q : ℕ) :
    ∃ r R : ℕ → ℝ, (∀ n, 2 ≤ r n) ∧ Tendsto r atTop atTop ∧ Tendsto R atTop atTop ∧
      (∀ n, P (r n) ∧ P (R n)) ∧
      (∀ n, 1 / (2 * pairL f g (r n)) ≤ R n - r n ∧
        R n - r n ≤ 1 / pairL f g (r n) ∧ pairL f g (R n) ≤ 2 * pairL f g (r n)) ∧
      Tendsto (fun n => pairT f g (r n) /
        (r n ^ p * pairL f g (r n) ^ q * Real.log (r n))) atTop atTop := by
  obtain ⟨E, hEm, hE, r0, hP⟩ := hP
  obtain ⟨r, R, hr2, hr, hR, houtside, hshort, hratio⟩ :=
    selected_good_growth_radii hf hg hInf hEm hE p q
  have hvalid : ∀ᶠ n in atTop, P (r n) ∧ P (R n) := by
    filter_upwards [hr.eventually_ge_atTop r0, hR.eventually_ge_atTop r0] with n hn hN
    exact ⟨hP (r n) hn (houtside n).1, hP (R n) hN (houtside n).2⟩
  obtain ⟨σ, hσ, hσP⟩ := extraction_of_eventually_atTop hvalid
  exact ⟨fun n => r (σ n), fun n => R (σ n), fun n => hr2 (σ n),
    hr.comp hσ.tendsto_atTop, hR.comp hσ.tendsto_atTop, hσP,
    fun n => hshort (σ n), hratio.comp hσ.tendsto_atTop⟩

/-- Density and the honest distinct-point estimate produce enough points
for every fixed finite family of multiplicity ratios. N is the actual
logarithmic marked count and card its actual finite support cardinality
when this lemma is applied; neither is replaced by a chosen large set. -/
theorem selected_large_marked_radii
    {f g : ℂ → ℂ} (hf : MeromorphicOn f univ) (hg : MeromorphicOn g univ)
    (hInf : InfiniteOrder f ∨ InfiniteOrder g)
    (hlinear : ∃ c : ℝ, 0 < c ∧ ∀ᶠ r in atTop, c * r ≤ pairT f g r)
    {M N card : ℝ → ℝ} {rstar α K : ℝ}
    (hM : ∀ r : ℝ, 1 ≤ r → 0 ≤ M r)
    (hmass : ∃ C : ℝ, 0 < C ∧ OutsideFiniteMeasure fun r => M r ≤ C * pairL f g r)
    (hdensity : ∃ C : ℝ, OutsideFiniteMeasure fun r =>
      α * pairT f g r ≤ N r + C * pairL f g r)
    (hcount : ∀ r : ℝ, 1 ≤ r → N r ≤ 3 * card r * Real.log (r / rstar))
    (hstar : 0 < rstar) (hα : 0 < α) (hK : 0 ≤ K) :
    ∃ r R : ℕ → ℝ, (∀ n, 2 ≤ r n) ∧ Tendsto r atTop atTop ∧ Tendsto R atTop atTop ∧
      (∀ n, r n < R n ∧ R n - r n ≤ 1) ∧
      (∀ n, 0 < selectedBranchParameter (r n) (R n) (M (R n))) ∧
      Tendsto (fun n => selectedBranchParameter (r n) (R n) (M (R n))) atTop atTop ∧
      (∀ᶠ n in atTop,
        K * selectedBranchParameter (r n) (R n) (M (R n)) ^ 26 < card (r n)) := by
  obtain ⟨CM, hCM, hmass⟩ := hmass
  obtain ⟨CD, hdensity⟩ := hdensity
  obtain ⟨r, R, hr2, hr, hR, hest, hshort, hratio⟩ :=
    selected_good_growth_radii_with_estimates hf hg hInf (hmass.conj hdensity) 78 182
  have hr1 (n : ℕ) : 1 ≤ r n := by linarith [hr2 n]
  have hL (n : ℕ) : 1 ≤ pairL f g (r n) :=
    (selected_pairL_monotone_and_ge_one hf hg).2 (r n) (hr1 n)
  have hLp (n : ℕ) : 0 < pairL f g (r n) := by linarith [hL n]
  have hrR (n : ℕ) : r n < R n := by
    have hp : 0 < 1 / (2 * pairL f g (r n)) :=
      one_div_pos.mpr (mul_pos (by norm_num) (hLp n))
    linarith [(hshort n).1]
  have hR1 (n : ℕ) : 1 ≤ R n := (hr1 n).trans (hrR n).le
  have hMn (n : ℕ) : 0 ≤ M (R n) := hM (R n) (hR1 n)
  have hMC (n : ℕ) : M (R n) ≤ (2 * CM) * pairL f g (r n) := by
    have hm := (hest n).2.1
    have hl := mul_le_mul_of_nonneg_left (hshort n).2.2 hCM.le
    linarith only [hm, hl]
  have hBge (n : ℕ) : r n ≤ selectedBranchParameter (r n) (R n) (M (R n)) :=
    selectedBranchParameter_ge_radius (hr1 n) (hrR n) (hMn n)
  have hBpos (n : ℕ) : 0 < selectedBranchParameter (r n) (R n) (M (R n)) :=
    (by linarith [hr2 n] : 0 < r n).trans_le (hBge n)
  have hBlim : Tendsto (fun n => selectedBranchParameter (r n) (R n) (M (R n)))
      atTop atTop := selectedBranchParameter_tendsto_atTop hr hr1 hL hMn
        (fun n => (hshort n).1)
  have hlocal := selectedBranchParameter_counting_error_tendsto_zero hr2
    (by positivity : 0 ≤ 2 * CM) hMn hMC (fun n => (hshort n).1)
    (fun n => (hshort n).2.1) hL hratio
  obtain ⟨c, hc, hlin⟩ := hlinear
  have hTtop : Tendsto (pairT f g) atTop atTop :=
    tendsto_atTop_mono' atTop hlin (tendsto_id.const_mul_atTop hc)
  have hTpos : ∀ᶠ n in atTop, 0 < pairT f g (r n) :=
    (hTtop.comp hr).eventually_gt_atTop 0
  have hglobal : Tendsto (fun n => pairL f g (r n) / pairT f g (r n))
      atTop (𝓝 0) := by
    simpa only [pairL, Function.comp_def] using (log_isLittleO_of_linear_growth hc hlin).comp hr
  have hlarge := selected_counting_budget_eventually_lt hr hstar hα hK
    (fun n => (hBpos n).le) hTpos hlocal hglobal
    (Eventually.of_forall fun n => (hest n).1.2) (fun n => hcount (r n) (hr1 n))
  refine ⟨r, R, hr2, hr, hR, ?_, hBpos, hBlim, hlarge⟩
  intro n
  refine ⟨hrR n, (hshort n).2.1.trans ?_⟩
  exact (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) (hL n))
    |>.trans_eq (by norm_num)

end ThreeIM
