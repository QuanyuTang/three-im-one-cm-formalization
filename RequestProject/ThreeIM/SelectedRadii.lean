module

public import RequestProject.ThreeIM.SelectedGrowthRatio
public import RequestProject.ThreeIM.ShortGrowth
public import RequestProject.ThreeIM.MaximalException

/-! # Good outer radii from the one-sided maximal exceptional set -/

@[expose] public section

open Filter Set MeasureTheory Topology

namespace ThreeIM

set_option autoImplicit false

theorem exists_outside_upper_half_of_not_mem_maximalSet {E : Set ℝ}
    (hE : volume E < ⊤) {r : ℝ} (hr : 1 ≤ r) (hrE : r ∉ maximalSet E)
    {h : ℝ} (hh : 0 < h) :
    ∃ R ∈ Icc (r + h / 2) (r + h), R ∉ E := by
  classical
  have hquarter : (volume (E ∩ Icc r (r + h))).toReal ≤ h / 4 :=
    le_of_not_gt (fun he => hrE ⟨hr, h, hh, he⟩)
  by_contra hno
  have hsub : Icc (r + h / 2) (r + h) ⊆ E ∩ Icc r (r + h) := by
    intro x hx
    have hxE : x ∈ E := by
      by_contra hxE
      exact hno ⟨x, hx, hxE⟩
    exact ⟨hxE, by linarith [hx.1], hx.2⟩
  have hfin : volume (E ∩ Icc r (r + h)) ≠ ⊤ :=
    ne_top_of_le_ne_top hE.ne (measure_mono inter_subset_left)
  have hbound := ENNReal.toReal_mono hfin (measure_mono hsub)
  rw [Real.volume_Icc, show r + h - (r + h / 2) = h / 2 by ring,
    ENNReal.toReal_ofReal (half_pos hh).le] at hbound
  linarith

theorem selected_short_growth_exception {L : ℝ → ℝ}
    (hmono : MonotoneOn L (Ici 1)) (hL : ∀ r ≥ 1, 1 ≤ L r)
    {E : Set ℝ} (hEm : MeasurableSet E) (hE : volume E < ⊤) :
    ∃ Z : Set ℝ, MeasurableSet Z ∧ volume Z < ⊤ ∧ E ⊆ Z ∧
      ∀ r ≥ 1, r ∉ Z → ∃ R : ℝ,
        1 / (2 * L r) ≤ R - r ∧ R - r ≤ 1 / L r ∧ R ∉ E ∧ L R ≤ 2 * L r := by
  obtain ⟨E₀, hE₀m, hE₀, hshort⟩ := short_growth hmono hL
  obtain ⟨hmaxm, hmax⟩ := maximalSet_measurable_and_le E hEm hE
  have hmaxfin : volume (maximalSet E) < ⊤ :=
    hmax.trans_lt (ENNReal.mul_lt_top (by norm_num) hE)
  let Z := E ∪ (E₀ ∪ maximalSet E)
  have hZfin : volume Z < ⊤ := (measure_union_le _ _).trans_lt
    (ENNReal.add_lt_top.2 ⟨hE, (measure_union_le _ _).trans_lt (ENNReal.add_lt_top.2 ⟨hE₀, hmaxfin⟩)⟩)
  refine ⟨Z, hEm.union (hE₀m.union hmaxm), hZfin, subset_union_left, ?_⟩
  intro r hr hrZ
  have hrE₀ : r ∉ E₀ := fun he => hrZ (Or.inr (Or.inl he))
  have hrmax : r ∉ maximalSet E := fun he => hrZ (Or.inr (Or.inr he))
  have hLpos : 0 < L r := lt_of_lt_of_le one_pos (hL r hr)
  obtain ⟨R, hR, hRE⟩ := exists_outside_upper_half_of_not_mem_maximalSet hE hr hrmax
    (one_div_pos.2 hLpos)
  have hstep : 1 / (2 * L r) = (1 / L r) / 2 := by field_simp
  have hrR : r ≤ R := by linarith [hR.1, one_div_pos.2 hLpos]
  refine ⟨R, ?_, by linarith [hR.2], hRE, ?_⟩
  · rw [hstep]
    linarith [hR.1]
  · exact (hmono (hr.trans hrR) (by linarith [one_div_pos.2 hLpos] :
      1 ≤ r + 1 / L r) hR.2).trans (hshort r hr hrE₀)

theorem selected_pairL_monotone_and_ge_one {f g : ℂ → ℂ}
    (hf : MeromorphicOn f univ) (hg : MeromorphicOn g univ) :
    MonotoneOn (pairL f g) (Ici 1) ∧ ∀ r ≥ 1, 1 ≤ pairL f g r := by
  have hnonneg (r : ℝ) (hr : 1 ≤ r) : 0 ≤ pairT f g r :=
    le_max_of_le_left (show 0 ≤ charT f r from ValueDistribution.characteristic_nonneg hr)
  constructor
  · intro r hr R hR hrR
    have hr1 : 1 ≤ r := hr
    have hR1 : 1 ≤ R := hR
    have hT := pairT_monotoneOn_Ici_one hf hg hr hR hrR
    apply Real.log_le_log
    · have := hnonneg r hr1
      have := Real.exp_pos (1 : ℝ)
      have hr0 : 0 ≤ r := by linarith
      positivity
    · have hm := mul_le_mul hrR hT (hnonneg r hr1) (by linarith : 0 ≤ R)
      linarith
  · intro r hr
    have hT := hnonneg r hr
    have hr0 : 0 ≤ r := by linarith
    have hh := Real.log_le_log (Real.exp_pos 1)
      (show Real.exp 1 ≤ Real.exp 1 + r * pairT f g r by linarith [mul_nonneg hr0 hT])
    simpa only [Real.log_exp, pairL] using hh

theorem selected_good_growth_radii {f g : ℂ → ℂ}
    (hf : MeromorphicOn f univ) (hg : MeromorphicOn g univ)
    (hInf : InfiniteOrder f ∨ InfiniteOrder g)
    {E : Set ℝ} (hEm : MeasurableSet E) (hE : volume E < ⊤) (p q : ℕ) :
    ∃ r R : ℕ → ℝ, (∀ n, 2 ≤ r n) ∧ Tendsto r atTop atTop ∧ Tendsto R atTop atTop ∧
      (∀ n, r n ∉ E ∧ R n ∉ E) ∧
      (∀ n, 1 / (2 * pairL f g (r n)) ≤ R n - r n ∧
        R n - r n ≤ 1 / pairL f g (r n) ∧ pairL f g (R n) ≤ 2 * pairL f g (r n)) ∧
      Tendsto (fun n => pairT f g (r n) /
        (r n ^ p * pairL f g (r n) ^ q * Real.log (r n))) atTop atTop := by
  classical
  obtain ⟨hmono, hL⟩ := selected_pairL_monotone_and_ge_one hf hg
  obtain ⟨Z, _, hZ, hEZ, hchoose⟩ := selected_short_growth_exception hmono hL hEm hE
  obtain ⟨r, hr2, hr, hrZ, hratio⟩ := selected_large_growth_radii hf hg hInf hZ p q
  have hex (n : ℕ) := hchoose (r n) (by linarith [hr2 n]) (hrZ n)
  choose R hRlo hRhi hRE hRL using hex
  have hrR (n : ℕ) : r n ≤ R n := by
    have hLp : 0 < pairL f g (r n) := lt_of_lt_of_le one_pos (hL (r n) (by linarith [hr2 n]))
    have hpos : 0 < 1 / (2 * pairL f g (r n)) := by positivity
    linarith [hRlo n]
  exact ⟨r, R, hr2, hr, tendsto_atTop_mono hrR hr,
    fun n => ⟨fun hn => hrZ n (hEZ hn), hRE n⟩,
    fun n => ⟨hRlo n, hRhi n, hRL n⟩, hratio⟩

end ThreeIM
