module

public import RequestProject.ThreeIM.MathlibImports

/-!
# A one-sided exceptional-set estimate (Lemma 6.2)
-/

@[expose] public section

open Filter Set MeasureTheory Metric

namespace ThreeIM

/-- The one-sided maximal set
`E* = {r ≥ 1 : sup_{h>0} |E ∩ [r, r+h]| / h > 1/4}` of Lemma 6.2 (the supremum exceeds `1/4`
exactly when some quotient does). -/
def maximalSet (E : Set ℝ) : Set ℝ :=
  {r | 1 ≤ r ∧ ∃ h > 0, h / 4 < (volume (E ∩ Icc r (r + h))).toReal}

lemma volume_inter_Icc_lipschitz (E : Set ℝ) (h : ℝ) (r r' : ℝ) (hrr : r ≤ r') :
    (volume (E ∩ Icc r (r + h))).toReal ≤ (volume (E ∩ Icc r' (r' + h))).toReal + (r' - r) := by
  have hsub : E ∩ Icc r (r + h) ⊆ (E ∩ Icc r' (r' + h)) ∪ Icc r r' := by
    intro x ⟨hxE, hx1, hx2⟩
    by_cases hx : x ≤ r'
    · exact Or.inr ⟨hx1, hx⟩
    · push_neg at hx
      exact Or.inl ⟨hxE, hx.le, by linarith⟩
  have hfin : volume (E ∩ Icc r' (r' + h)) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp [Real.volume_Icc]) (measure_mono inter_subset_right)
  calc (volume (E ∩ Icc r (r + h))).toReal
      ≤ (volume (E ∩ Icc r' (r' + h)) + volume (Icc r r')).toReal := by
        apply ENNReal.toReal_mono (by simp [hfin, Real.volume_Icc])
        exact (measure_mono hsub).trans (measure_union_le _ _)
    _ = _ := by
        rw [ENNReal.toReal_add hfin (by simp [Real.volume_Icc]), Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith)]

lemma continuous_volume_inter_Icc (E : Set ℝ) (h : ℝ) :
    Continuous fun r => (volume (E ∩ Icc r (r + h))).toReal := by
  refine LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun r r' => ?_)
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul, abs_le]
  rcases le_total r r' with hrr | hrr
  · have h1 := volume_inter_Icc_lipschitz E h r r' hrr
    have h2 : (volume (E ∩ Icc r' (r' + h))).toReal ≤
        (volume (E ∩ Icc r (r + h))).toReal + (r' - r) := by
      have hsub : E ∩ Icc r' (r' + h) ⊆ (E ∩ Icc r (r + h)) ∪ Icc (r + h) (r' + h) := by
        intro x ⟨hxE, hx1, hx2⟩
        by_cases hx : x ≤ r + h
        · exact Or.inl ⟨hxE, by linarith, hx⟩
        · push_neg at hx
          exact Or.inr ⟨hx.le, hx2⟩
      have hfin : volume (E ∩ Icc r (r + h)) ≠ ⊤ :=
        ne_top_of_le_ne_top (by simp [Real.volume_Icc]) (measure_mono inter_subset_right)
      calc (volume (E ∩ Icc r' (r' + h))).toReal
          ≤ (volume (E ∩ Icc r (r + h)) + volume (Icc (r + h) (r' + h))).toReal := by
            apply ENNReal.toReal_mono (by simp [hfin, Real.volume_Icc])
            exact (measure_mono hsub).trans (measure_union_le _ _)
        _ = _ := by
            rw [ENNReal.toReal_add hfin (by simp [Real.volume_Icc]), Real.volume_Icc,
              ENNReal.toReal_ofReal (by linarith)]
            ring
    rw [abs_of_nonpos (by linarith)]
    constructor <;> linarith
  · have h1 := volume_inter_Icc_lipschitz E h r' r hrr
    have h2 : (volume (E ∩ Icc r (r + h))).toReal ≤
        (volume (E ∩ Icc r' (r' + h))).toReal + (r - r') := by
      have hsub : E ∩ Icc r (r + h) ⊆ (E ∩ Icc r' (r' + h)) ∪ Icc (r' + h) (r + h) := by
        intro x ⟨hxE, hx1, hx2⟩
        by_cases hx : x ≤ r' + h
        · exact Or.inl ⟨hxE, by linarith, hx⟩
        · push_neg at hx
          exact Or.inr ⟨hx.le, hx2⟩
      have hfin : volume (E ∩ Icc r' (r' + h)) ≠ ⊤ :=
        ne_top_of_le_ne_top (by simp [Real.volume_Icc]) (measure_mono inter_subset_right)
      calc (volume (E ∩ Icc r (r + h))).toReal
          ≤ (volume (E ∩ Icc r' (r' + h)) + volume (Icc (r' + h) (r + h))).toReal := by
            apply ENNReal.toReal_mono (by simp [hfin, Real.volume_Icc])
            exact (measure_mono hsub).trans (measure_union_le _ _)
        _ = _ := by
            rw [ENNReal.toReal_add hfin (by simp [Real.volume_Icc]), Real.volume_Icc,
              ENNReal.toReal_ofReal (by linarith)]
            ring
    rw [abs_of_nonneg (by linarith)]
    constructor <;> linarith

/-- **Lemma 6.2** (a one-sided exceptional-set estimate).  If `E ⊆ [1, ∞)` is measurable with
`|E| < ∞`, then `E* = {r ≥ 1 : sup_{h>0} |E ∩ [r, r+h]| / h > 1/4}` is measurable and
`|E*| ≤ 20 |E|`. -/
theorem maximalSet_measurable_and_le (E : Set ℝ) (hE : MeasurableSet E)
    (hfin : volume E < ⊤) :
    MeasurableSet (maximalSet E) ∧ volume (maximalSet E) ≤ 20 * volume E := by
  constructor
  · -- `E*` is the intersection of `[1, ∞)` with a union of open sets
    have : maximalSet E = Ici 1 ∩ ⋃ h : {h : ℝ // 0 < h},
        {r | h.1 / 4 < (volume (E ∩ Icc r (r + h.1))).toReal} := by
      ext r
      simp only [maximalSet, mem_setOf_eq, mem_inter_iff, mem_Ici, mem_iUnion, Subtype.exists,
        exists_prop]
    rw [this]
    refine measurableSet_Ici.inter (IsOpen.measurableSet (isOpen_iUnion fun h => ?_))
    exact isOpen_lt continuous_const (continuous_volume_inter_Icc E h.1)
  · classical
    -- choose a witness `h r` for every `r ∈ E*`
    have hw : ∀ r ∈ maximalSet E, ∃ h > 0, h / 4 < (volume (E ∩ Icc r (r + h))).toReal :=
      fun r hr => hr.2
    choose! hh hhpos hhbig using hw
    set M := (volume E).toReal with hM
    have hbound : ∀ r ∈ maximalSet E, hh r / 2 ≤ 2 * M := by
      intro r hr
      have h1 := hhbig r hr
      have h2 : (volume (E ∩ Icc r (r + hh r))).toReal ≤ M :=
        ENNReal.toReal_mono hfin.ne (measure_mono inter_subset_left)
      linarith
    obtain ⟨u, hut, hudisj, hucover⟩ :=
      Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall (maximalSet E)
        (fun r => r + hh r / 2) (fun r => hh r / 2) (2 * M) hbound 5 (by norm_num)
    have hball : ∀ r, closedBall (r + hh r / 2) (hh r / 2) = Icc r (r + hh r) := by
      intro r
      rw [Real.closedBall_eq_Icc]
      congr 1 <;> ring
    -- `u` is countable
    have hucount : u.Countable := by
      refine Set.PairwiseDisjoint.countable_of_isOpen (s := fun r => ball (r + hh r / 2)
        (hh r / 2)) ?_ (fun _ _ => isOpen_ball) (fun r hr => ?_)
      · exact hudisj.mono fun r => ball_subset_closedBall
      · exact ⟨_, mem_ball_self (by linarith [hhpos r (hut hr)])⟩
    -- covering
    have hcov : maximalSet E ⊆ ⋃ b ∈ u, closedBall (b + hh b / 2) (5 * (hh b / 2)) := by
      intro r hr
      obtain ⟨b, hbu, hsub⟩ := hucover r hr
      refine mem_iUnion₂.2 ⟨b, hbu, hsub ?_⟩
      rw [hball]
      exact ⟨le_rfl, by linarith [hhpos r hr]⟩
    calc volume (maximalSet E)
        ≤ volume (⋃ b ∈ u, closedBall (b + hh b / 2) (5 * (hh b / 2))) := measure_mono hcov
      _ ≤ ∑' b : u, volume (closedBall ((b : ℝ) + hh b / 2) (5 * (hh b / 2))) :=
          measure_biUnion_le _ hucount _
      _ ≤ ∑' b : u, 20 * volume (E ∩ Icc (b : ℝ) (b + hh b)) := by
          refine ENNReal.tsum_le_tsum fun b => ?_
          have hb := hut b.2
          have h1 := hhbig b hb
          have hfin' : volume (E ∩ Icc (b : ℝ) (b + hh b)) ≠ ⊤ :=
            ne_top_of_le_ne_top hfin.ne (measure_mono inter_subset_left)
          rw [Real.volume_closedBall]
          calc ENNReal.ofReal (2 * (5 * (hh b / 2)))
              ≤ ENNReal.ofReal (20 * (volume (E ∩ Icc (b : ℝ) (b + hh b))).toReal) :=
                ENNReal.ofReal_le_ofReal (by linarith)
            _ = 20 * volume (E ∩ Icc (b : ℝ) (b + hh b)) := by
                rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hfin']
                norm_num
      _ = 20 * ∑' b : u, volume (E ∩ Icc (b : ℝ) (b + hh b)) := ENNReal.tsum_mul_left
      _ = 20 * volume (⋃ b ∈ u, E ∩ Icc b (b + hh b)) := by
          rw [measure_biUnion hucount]
          · refine hudisj.mono fun b => ?_
            change E ∩ Icc b (b + hh b) ⊆ closedBall (b + hh b / 2) (hh b / 2)
            rw [hball]; exact inter_subset_right
          · exact fun b _ => hE.inter measurableSet_Icc
      _ ≤ 20 * volume E := by
          gcongr
          exact iUnion₂_subset fun b _ => inter_subset_left

end ThreeIM
