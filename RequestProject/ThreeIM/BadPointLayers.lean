module

public import RequestProject.ThreeIM.BadPointPacking
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Summing the bad-point distance layers

This implements the remaining layer sum in step 3 of the finite-disk lemma.
We use geometric layers with ratio `exp 1 < 3` in place of dyadic layers.
The lower distance `exp (-4 B)` leaves at most `floor (4 B) + 1` layers.
Together with outer packing this gives an explicit polynomial exception
bound. The divisor-distance definition treats the empty divisor set as in
the manuscript: its truncated distance is one, not Mathlib's `infDist ∅ = 0`.
These results count bad points outside the divisor clusters. Counting points
inside those clusters and deriving the regular-disk estimates remain separate.
-/

@[expose] public section

open Set Metric
open scoped BigOperators

namespace ThreeIM

/-- Distance truncated at one, with the manuscript's empty-set convention. -/
noncomputable def truncatedDivisorDistance (centers : Finset ℂ) (z : ℂ) : ℝ := by
  classical
  exact if centers = ∅ then 1 else min 1 (infDist z (centers : Set ℂ))

@[simp] theorem truncatedDivisorDistance_empty (z : ℂ) :
    truncatedDivisorDistance ∅ z = 1 := by
  classical
  simp [truncatedDivisorDistance]

theorem truncatedDivisorDistance_of_nonempty {centers : Finset ℂ}
    (hcenters : centers.Nonempty) (z : ℂ) :
    truncatedDivisorDistance centers z = min 1 (infDist z (centers : Set ℂ)) := by
  classical
  simp [truncatedDivisorDistance, hcenters.ne_empty]

theorem truncatedDivisorDistance_le_one (centers : Finset ℂ) (z : ℂ) :
    truncatedDivisorDistance centers z ≤ 1 := by
  classical
  by_cases hc : centers = ∅
  · simp [hc]
  · simp only [truncatedDivisorDistance, hc, ↓reduceIte]
    exact min_le_left _ _

/-- Every admissible distance belongs to one of at most `floor (4B)+1`
geometric layers. No rounding assumption on `B` is needed. -/
theorem exists_exponential_distance_layer {B d : ℝ}
    (hd : 0 < d) (hdone : d ≤ 1) (hη : Real.exp (-4 * B) ≤ d) :
    ∃ n ∈ Finset.range (⌊4 * B⌋₊ + 1),
      Real.exp (-(n + 1 : ℝ)) < d ∧ d ≤ Real.exp (-(n : ℝ)) := by
  have hpow (n : ℕ) : (Real.exp (-1)) ^ n = Real.exp (-(n : ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  obtain ⟨n, hnlo, hnhi⟩ := exists_nat_pow_near_of_lt_one hd hdone
    (Real.exp_pos (-1)) (Real.exp_lt_one_iff.mpr (by norm_num))
  rw [hpow] at hnlo hnhi
  have hnB : (n : ℝ) ≤ 4 * B := by
    have hexp := Real.exp_le_exp.mp (hη.trans hnhi)
    linarith
  refine ⟨n, Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hnB)), ?_, hnhi⟩
  simpa only [Nat.cast_add, Nat.cast_one] using hnlo

/-- One exponential distance layer is covered by divisor-centered disks of
radius at most three times its lower distance. Its count is independent of
the layer radius. The small-distance hypothesis forces a nonempty divisor set. -/
theorem bad_qpoints_exponential_layer_card_le (s centers : Finset ℂ)
    {Φ A : ℂ → ℂ} {q : ℂ} {B : ℝ} (n : ℕ) (hB : 4 ≤ B)
    (hdata : ∀ z ∈ s, RegularBadPoint Φ A z B (truncatedDivisorDistance centers z))
    (hsmall : ∀ z ∈ s, truncatedDivisorDistance centers z < 1 / 2)
    (hlower : ∀ z ∈ s, Real.exp (-(n + 1 : ℝ)) ≤ truncatedDivisorDistance centers z)
    (hupper : ∀ z ∈ s, truncatedDivisorDistance centers z ≤ Real.exp (-(n : ℝ)))
    (hfiber : ∀ z ∈ s, Φ z = q) :
    (s.card : ℝ) ≤ (centers.card : ℝ) * 601 ^ 2 * B ^ 22 := by
  classical
  let δ : ℝ := Real.exp (-(n + 1 : ℝ))
  have hδ : 0 < δ := Real.exp_pos _
  have hratio : Real.exp (-(n : ℝ)) = Real.exp 1 * δ := by
    dsimp [δ]
    rw [← Real.exp_add]
    congr 1
    ring
  have hcover : ∀ z ∈ s, ∃ c ∈ centers, dist z c ≤ 3 * δ := by
    intro z hz
    have hcne : centers.Nonempty := by
      by_contra hc
      have hempty : centers = ∅ := Finset.not_nonempty_iff_eq_empty.mp hc
      have hs := hsmall z hz
      simp only [hempty, truncatedDivisorDistance_empty] at hs
      norm_num at hs
    have hdsmall : infDist z (centers : Set ℂ) < 1 := by
      have hs := hsmall z hz
      rw [truncatedDivisorDistance_of_nonempty hcne] at hs
      rcases min_lt_iff.mp (hs.trans (by norm_num : (1 : ℝ) / 2 < 1)) with h | h
      · exact (lt_irrefl 1 h).elim
      · exact h
    have hdEq : truncatedDivisorDistance centers z = infDist z (centers : Set ℂ) := by
      rw [truncatedDivisorDistance_of_nonempty hcne, min_eq_right hdsmall.le]
    have hcset : (centers : Set ℂ).Nonempty := by simpa using hcne
    obtain ⟨c, hc, hzc⟩ := centers.finite_toSet.isCompact.exists_infDist_eq_dist hcset z
    refine ⟨c, hc, ?_⟩
    rw [← hzc, ← hdEq]
    calc
      truncatedDivisorDistance centers z ≤ Real.exp (-(n : ℝ)) := hupper z hz
      _ = Real.exp 1 * δ := hratio
      _ ≤ 3 * δ := mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le hδ.le
  have hpack := bad_qpoints_card_le_of_cover s centers hB hδ (by positivity)
    hdata hlower hfiber hcover
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hBpow : (1 : ℝ) ≤ B ^ 11 := one_le_pow₀ (by linarith : (1 : ℝ) ≤ B)
  have hcancel : 1 + 200 * (3 * δ) * B ^ 11 / δ = 1 + 600 * B ^ 11 := by
    field_simp [ne_of_gt hδ]
    ring
  rw [hcancel] at hpack
  calc
    (s.card : ℝ) ≤ (centers.card : ℝ) * (1 + 600 * B ^ 11) ^ 2 := hpack
    _ ≤ (centers.card : ℝ) * (601 * B ^ 11) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply pow_le_pow_left₀ (by positivity)
      linarith
    _ = (centers.card : ℝ) * 601 ^ 2 * B ^ 22 := by ring

/-- The complete outer-plus-layer count for points outside the divisor
clusters. This includes the empty-divisor case, where all points are outer. -/
theorem bad_qpoints_away_divisors_card_le_raw (s centers : Finset ℂ)
    {Φ A : ℂ → ℂ} {q c : ℂ} {B R : ℝ} (hB : 4 ≤ B) (hR : 0 ≤ R)
    (hdata : ∀ z ∈ s, RegularBadPoint Φ A z B (truncatedDivisorDistance centers z))
    (hdistance : ∀ z ∈ s, Real.exp (-4 * B) ≤ truncatedDivisorDistance centers z)
    (hfiber : ∀ z ∈ s, Φ z = q)
    (hdisk : ∀ z ∈ s, dist z c ≤ R) :
    (s.card : ℝ) ≤ 401 ^ 2 * (R + 1) ^ 2 * B ^ 22 +
      ((⌊4 * B⌋₊ + 1 : ℕ) : ℝ) * (centers.card : ℝ) * 601 ^ 2 * B ^ 22 := by
  classical
  let d := truncatedDivisorDistance centers
  let outer : Finset ℂ := s.filter (fun z => (1 : ℝ) / 2 ≤ d z)
  let layers : Finset ℕ := Finset.range (⌊4 * B⌋₊ + 1)
  let t : ℕ → Finset ℂ := fun n => s.filter (fun z => d z < 1 / 2 ∧
    Real.exp (-(n + 1 : ℝ)) < d z ∧ d z ≤ Real.exp (-(n : ℝ)))
  have hsub : s ⊆ outer ∪ layers.biUnion t := by
    intro z hz
    by_cases ho : (1 : ℝ) / 2 ≤ d z
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hz, ho⟩)
    · obtain ⟨n, hn, hlo, hhi⟩ := exists_exponential_distance_layer
        (hdata z hz).distance_pos (truncatedDivisorDistance_le_one centers z) (hdistance z hz)
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨n, hn, Finset.mem_filter.mpr ⟨hz, lt_of_not_ge ho, hlo, hhi⟩⟩)
  have hcard : (s.card : ℝ) ≤ (outer.card : ℝ) + ∑ n ∈ layers, ((t n).card : ℝ) := by
    have hn := (Finset.card_le_card hsub).trans
      ((Finset.card_union_le outer (layers.biUnion t)).trans
        (Nat.add_le_add_left Finset.card_biUnion_le outer.card))
    exact_mod_cast hn
  have houter : (outer.card : ℝ) ≤ 401 ^ 2 * (R + 1) ^ 2 * B ^ 22 := by
    apply bad_qpoints_outer_card_le outer hB hR
    · intro z hz
      exact hdata z (Finset.mem_filter.mp hz).1
    · intro z hz
      exact (Finset.mem_filter.mp hz).2
    · intro z hz
      exact hfiber z (Finset.mem_filter.mp hz).1
    · intro z hz
      exact hdisk z (Finset.mem_filter.mp hz).1
  have hlayers : ∀ n ∈ layers, ((t n).card : ℝ) ≤
      (centers.card : ℝ) * 601 ^ 2 * B ^ 22 := by
    intro n hn
    apply bad_qpoints_exponential_layer_card_le (t n) centers n hB
    · intro z hz
      exact hdata z (Finset.mem_filter.mp hz).1
    · intro z hz
      exact (Finset.mem_filter.mp hz).2.1
    · intro z hz
      exact (Finset.mem_filter.mp hz).2.2.1.le
    · intro z hz
      exact (Finset.mem_filter.mp hz).2.2.2
    · intro z hz
      exact hfiber z (Finset.mem_filter.mp hz).1
  calc
    (s.card : ℝ) ≤ (outer.card : ℝ) + ∑ n ∈ layers, ((t n).card : ℝ) := hcard
    _ ≤ 401 ^ 2 * (R + 1) ^ 2 * B ^ 22 +
        ∑ _n ∈ layers, (centers.card : ℝ) * 601 ^ 2 * B ^ 22 :=
      add_le_add houter (Finset.sum_le_sum hlayers)
    _ = 401 ^ 2 * (R + 1) ^ 2 * B ^ 22 +
        ((⌊4 * B⌋₊ + 1 : ℕ) : ℝ) * (centers.card : ℝ) * 601 ^ 2 * B ^ 22 := by
      simp only [Finset.sum_const, nsmul_eq_mul, layers, Finset.card_range]
      ring

/-- An explicit polynomial exception bound for all regular bad points outside
the divisor clusters, including an empty divisor set. The original finite-disk
lemma separately bounds points inside the clusters. -/
theorem bad_qpoints_away_divisors_card_le (s centers : Finset ℂ)
    {Φ A : ℂ → ℂ} {q c : ℂ} {B R : ℝ} (hB : 4 ≤ B) (hR : 0 ≤ R)
    (hRB : R ≤ B) (hNB : (centers.card : ℝ) ≤ B)
    (hdata : ∀ z ∈ s, RegularBadPoint Φ A z B (truncatedDivisorDistance centers z))
    (hdistance : ∀ z ∈ s, Real.exp (-4 * B) ≤ truncatedDivisorDistance centers z)
    (hfiber : ∀ z ∈ s, Φ z = q)
    (hdisk : ∀ z ∈ s, dist z c ≤ R) :
    (s.card : ℝ) ≤ 2500000 * B ^ 26 := by
  have h := bad_qpoints_away_divisors_card_le_raw s centers hB hR hdata hdistance hfiber hdisk
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hBone : 1 ≤ B := by linarith
  have hL : ((⌊4 * B⌋₊ + 1 : ℕ) : ℝ) ≤ 5 * B := by
    simp only [Nat.cast_add, Nat.cast_one]
    have hf := Nat.floor_le (by positivity : 0 ≤ 4 * B)
    linarith
  have hLN : ((⌊4 * B⌋₊ + 1 : ℕ) : ℝ) * (centers.card : ℝ) ≤ 5 * B ^ 2 := by
    calc
      ((⌊4 * B⌋₊ + 1 : ℕ) : ℝ) * (centers.card : ℝ) ≤ (5 * B) * B :=
        mul_le_mul hL hNB (Nat.cast_nonneg _) (by positivity)
      _ = 5 * B ^ 2 := by ring
  have hR2 : (R + 1) ^ 2 ≤ (2 * B) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  have hconst : (2449209 : ℝ) ≤ 2500000 * B ^ 2 := by
    have hB2 : (1 : ℝ) ≤ B ^ 2 := one_le_pow₀ hBone
    linarith
  calc
    (s.card : ℝ) ≤ 401 ^ 2 * (R + 1) ^ 2 * B ^ 22 +
        ((⌊4 * B⌋₊ + 1 : ℕ) : ℝ) * (centers.card : ℝ) * 601 ^ 2 * B ^ 22 := h
    _ ≤ 401 ^ 2 * (2 * B) ^ 2 * B ^ 22 + (5 * B ^ 2) * 601 ^ 2 * B ^ 22 := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hR2 (by norm_num)) (pow_nonneg hBpos.le _)
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hLN (by norm_num)) (pow_nonneg hBpos.le _)
    _ = 2449209 * B ^ 24 := by ring
    _ ≤ (2500000 * B ^ 2) * B ^ 24 :=
      mul_le_mul_of_nonneg_right hconst (pow_nonneg hBpos.le _)
    _ = 2500000 * B ^ 26 := by ring

end ThreeIM
