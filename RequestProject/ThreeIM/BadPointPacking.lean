module

public import RequestProject.ThreeIM.BadPointSeparation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Counting the separated bad points

The analytic regular-disk hypotheses imply separation of distinct points of
one fiber. Area packing then counts bad points in an outer region or in one
distance layer around the divisor set. In a distance layer, the covering-disk
radius is twice the lower distance bound, so it cancels from the count.
The divisor-cluster count and the number of layers remain separate.
-/

@[expose] public section

open Set Metric
open scoped BigOperators

namespace ThreeIM

/-- Distinct points in the same fiber cannot lie in the separation disk of a
regular bad point. The second point need not itself be regular. -/
theorem RegularBadPoint.le_dist_of_same_fiber {Φ A : ℂ → ℂ} {z w : ℂ} {B d : ℝ}
    (h : RegularBadPoint Φ A z B d) (hB : 4 ≤ B)
    (hΦ : Φ z = Φ w) (hne : z ≠ w) :
    d / (100 * B ^ 11) ≤ dist z w := by
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hr : 0 < d / (100 * B ^ 11) := by
    exact div_pos h.distance_pos (mul_pos (by norm_num) (pow_pos hBpos _))
  by_contra hlt
  have hw : w ∈ ball z (d / (100 * B ^ 11)) := by
    rw [mem_ball, dist_comm]
    exact lt_of_not_ge hlt
  exact hne (h.injOn_small_ball hB (mem_ball_self hr) hw hΦ)

/-- Bad points of a single fiber in one disk obey the manuscript's area-packing
estimate, if their divisor-distance parameter is at least `δ`. -/
theorem bad_qpoints_card_le (s : Finset ℂ) {Φ A : ℂ → ℂ} {q c : ℂ}
    {B δ R : ℝ} {d : ℂ → ℝ} (hB : 4 ≤ B) (hδ : 0 < δ) (hR : 0 ≤ R)
    (hdata : ∀ z ∈ s, RegularBadPoint Φ A z B (d z))
    (hlower : ∀ z ∈ s, δ ≤ d z)
    (hfiber : ∀ z ∈ s, Φ z = q)
    (hdisk : ∀ z ∈ s, dist z c ≤ R) :
    (s.card : ℝ) ≤ (1 + 200 * R * B ^ 11 / δ) ^ 2 := by
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hden : 0 < 100 * B ^ 11 := mul_pos (by norm_num) (pow_pos hBpos _)
  have hsep : ∀ z ∈ s, ∀ w ∈ s, z ≠ w → δ / (100 * B ^ 11) ≤ dist z w := by
    intro z hz w hw hne
    exact (div_le_div_of_nonneg_right (hlower z hz) hden.le).trans
      ((hdata z hz).le_dist_of_same_fiber hB ((hfiber z hz).trans (hfiber w hw).symm) hne)
  have hpack := card_le_sq_of_separated_complex s c hR (div_pos hδ hden) hdisk hsep
  convert hpack using 1
  field_simp [ne_of_gt hBpos, ne_of_gt hδ]
  ring

/-- The outer bad points, whose distance parameter is at least `1/2`, have
the explicit `C (R+1)^2 B^22` bound used in the manuscript. -/
theorem bad_qpoints_outer_card_le (s : Finset ℂ) {Φ A : ℂ → ℂ} {q c : ℂ}
    {B R : ℝ} {d : ℂ → ℝ} (hB : 4 ≤ B) (hR : 0 ≤ R)
    (hdata : ∀ z ∈ s, RegularBadPoint Φ A z B (d z))
    (hlower : ∀ z ∈ s, (1 : ℝ) / 2 ≤ d z)
    (hfiber : ∀ z ∈ s, Φ z = q)
    (hdisk : ∀ z ∈ s, dist z c ≤ R) :
    (s.card : ℝ) ≤ 401 ^ 2 * (R + 1) ^ 2 * B ^ 22 := by
  have h := bad_qpoints_card_le s hB (by norm_num : (0 : ℝ) < 1 / 2) hR
    hdata hlower hfiber hdisk
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hpow : (1 : ℝ) ≤ B ^ 11 := one_le_pow₀ (by linarith : (1 : ℝ) ≤ B)
  have hrad : 1 + 200 * R * B ^ 11 / (1 / 2) = 1 + 400 * R * B ^ 11 := by ring
  rw [hrad] at h
  calc
    (s.card : ℝ) ≤ (1 + 400 * R * B ^ 11) ^ 2 := h
    _ ≤ (401 * (R + 1) * B ^ 11) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity)
      calc
        1 + 400 * R * B ^ 11 ≤ B ^ 11 + 400 * R * B ^ 11 :=
          add_le_add hpow le_rfl
        _ = (1 + 400 * R) * B ^ 11 := by ring
        _ ≤ (401 * (R + 1)) * B ^ 11 :=
          mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hBpos.le _)
    _ = 401 ^ 2 * (R + 1) ^ 2 * B ^ 22 := by ring

/-- Summing the preceding disk estimate over a finite cover. The cover may
overlap; no separation between divisor centers is assumed. -/
theorem bad_qpoints_card_le_of_cover (s centers : Finset ℂ) {Φ A : ℂ → ℂ} {q : ℂ}
    {B δ R : ℝ} {d : ℂ → ℝ} (hB : 4 ≤ B) (hδ : 0 < δ) (hR : 0 ≤ R)
    (hdata : ∀ z ∈ s, RegularBadPoint Φ A z B (d z))
    (hlower : ∀ z ∈ s, δ ≤ d z)
    (hfiber : ∀ z ∈ s, Φ z = q)
    (hcover : ∀ z ∈ s, ∃ c ∈ centers, dist z c ≤ R) :
    (s.card : ℝ) ≤ (centers.card : ℝ) * (1 + 200 * R * B ^ 11 / δ) ^ 2 := by
  classical
  let t : ℂ → Finset ℂ := fun c => s.filter (fun z => dist z c ≤ R)
  have hsub : s ⊆ centers.biUnion t := by
    intro z hz
    obtain ⟨c, hc, hzc⟩ := hcover z hz
    exact Finset.mem_biUnion.mpr ⟨c, hc, Finset.mem_filter.mpr ⟨hz, hzc⟩⟩
  have hcard : (s.card : ℝ) ≤ ∑ c ∈ centers, ((t c).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  calc
    (s.card : ℝ) ≤ ∑ c ∈ centers, ((t c).card : ℝ) := hcard
    _ ≤ ∑ _c ∈ centers, (1 + 200 * R * B ^ 11 / δ) ^ 2 := by
      apply Finset.sum_le_sum
      intro c hc
      apply bad_qpoints_card_le (t c) hB hδ hR
      · intro z hz
        exact hdata z (Finset.mem_filter.mp hz).1
      · intro z hz
        exact hlower z (Finset.mem_filter.mp hz).1
      · intro z hz
        exact hfiber z (Finset.mem_filter.mp hz).1
      · intro z hz
        exact (Finset.mem_filter.mp hz).2
    _ = (centers.card : ℝ) * (1 + 200 * R * B ^ 11 / δ) ^ 2 := by
      simp only [Finset.sum_const, nsmul_eq_mul]

/-- In a distance layer `δ ≤ d < 2δ`, the points lie in divisor-centered disks
of radius `2δ`. The layer width cancels, leaving `401² N B²²`. -/
theorem bad_qpoints_layer_card_le (s centers : Finset ℂ) {Φ A : ℂ → ℂ} {q : ℂ}
    {B δ : ℝ} {d : ℂ → ℝ} (hB : 4 ≤ B) (hδ : 0 < δ)
    (hdata : ∀ z ∈ s, RegularBadPoint Φ A z B (d z))
    (hlower : ∀ z ∈ s, δ ≤ d z)
    (hfiber : ∀ z ∈ s, Φ z = q)
    (hcover : ∀ z ∈ s, ∃ c ∈ centers, dist z c ≤ 2 * δ) :
    (s.card : ℝ) ≤ (centers.card : ℝ) * 401 ^ 2 * B ^ 22 := by
  have h := bad_qpoints_card_le_of_cover s centers hB hδ (by positivity)
    hdata hlower hfiber hcover
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hBpow : (1 : ℝ) ≤ B ^ 11 := one_le_pow₀ (by linarith : (1 : ℝ) ≤ B)
  have hcancel : 1 + 200 * (2 * δ) * B ^ 11 / δ = 1 + 400 * B ^ 11 := by
    field_simp [ne_of_gt hδ]
    ring
  rw [hcancel] at h
  calc
    (s.card : ℝ) ≤ (centers.card : ℝ) * (1 + 400 * B ^ 11) ^ 2 := h
    _ ≤ (centers.card : ℝ) * (401 * B ^ 11) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply pow_le_pow_left₀ (by positivity)
      linarith
    _ = (centers.card : ℝ) * 401 ^ 2 * B ^ 22 := by ring

/-- The preceding layer bound for the actual truncated distance to a finite
nonempty divisor set. The covering by divisor-centered disks is derived from
attainment of the distance, rather than supplied as extra geometric data. -/
theorem bad_qpoints_distance_layer_card_le (s centers : Finset ℂ) {Φ A : ℂ → ℂ}
    {q : ℂ} {B δ : ℝ} (hB : 4 ≤ B) (hδ : 0 < δ) (hδone : 2 * δ ≤ 1)
    (hcenters : centers.Nonempty)
    (hdata : ∀ z ∈ s, RegularBadPoint Φ A z B (min 1 (infDist z (centers : Set ℂ))))
    (hlower : ∀ z ∈ s, δ ≤ min 1 (infDist z (centers : Set ℂ)))
    (hupper : ∀ z ∈ s, min 1 (infDist z (centers : Set ℂ)) < 2 * δ)
    (hfiber : ∀ z ∈ s, Φ z = q) :
    (s.card : ℝ) ≤ (centers.card : ℝ) * 401 ^ 2 * B ^ 22 := by
  apply bad_qpoints_layer_card_le s centers hB hδ hdata hlower hfiber
  intro z hz
  have hne : (centers : Set ℂ).Nonempty := by simpa using hcenters
  obtain ⟨c, hc, hzc⟩ := centers.finite_toSet.isCompact.exists_infDist_eq_dist hne z
  refine ⟨c, hc, ?_⟩
  have hinf : infDist z (centers : Set ℂ) < 2 * δ := by
    rcases min_lt_iff.mp (hupper z hz) with hbad | hdist
    · exact (not_lt_of_ge hδone hbad).elim
    · exact hdist
  rw [← hzc]
  exact hinf.le

end ThreeIM
