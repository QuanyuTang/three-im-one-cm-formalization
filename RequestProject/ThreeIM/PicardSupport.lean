/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus

Adapted for Lean 4.28 by Codex from ProjectVD, commit
5606b50ee6348c502410a0526be26e0dac7a1bc2, VD/SMT/Picard.lean.
-/
module

public import RequestProject.ThreeIM.MathlibImports

/-!
# Growth estimates for the Picard application of the second main theorem

These elementary real-variable estimates do not import `External` or any
unproved theorem of the sharing development. They are support lemmas, not a
proof of Picard's theorem.
-/

@[expose] public section

open Asymptotics Filter MeasureTheory Real Set Topology

namespace ThreeIM.PicardSupport

/-- A monotone function bounded by a multiple of `log r` outside a set of
finite linear measure has the same asymptotic bound without an exceptional
set. No sign assumption on the function is needed. -/
theorem monotone_isBigO_log_of_eventually_le {u : ℝ → ℝ} {x₀ C : ℝ}
    (hmono : MonotoneOn u (Set.Ici x₀))
    (hbound : ∀ᶠ r in volume.cofinite ⊓ atTop, u r ≤ C * Real.log r) :
    u =O[atTop] Real.log := by
  obtain ⟨s, hs, t, ht, hst⟩ := Filter.mem_inf_iff.1 hbound
  obtain ⟨R₀, hR₀⟩ := Filter.mem_atTop_sets.1 ht
  set M := (volume sᶜ).toReal with hM
  have hM₀ : 0 ≤ M := ENNReal.toReal_nonneg
  have hgood : ∀ r, R₀ ≤ r →
      ∃ r', r ≤ r' ∧ r' ≤ r + (M + 1) ∧ u r' ≤ C * Real.log r' := by
    intro r hr
    rcases (Set.Icc r (r + (M + 1)) ∩ s).eq_empty_or_nonempty with hempty | hne
    · exfalso
      have hsub : Set.Icc r (r + (M + 1)) ⊆ sᶜ := fun x hx hxs ↦
        Set.eq_empty_iff_forall_notMem.1 hempty x ⟨hx, hxs⟩
      have hmeasure := measure_mono (μ := volume) hsub
      rw [Real.volume_Icc, show r + (M + 1) - r = M + 1 by ring] at hmeasure
      have hfinite : volume sᶜ ≤ ENNReal.ofReal M :=
        le_of_eq (ENNReal.ofReal_toReal (Measure.mem_cofinite.1 hs).ne).symm
      have himpossible := hmeasure.trans hfinite
      rw [ENNReal.ofReal_le_ofReal_iff hM₀] at himpossible
      linarith
    · obtain ⟨r', hr'⟩ := hne
      have hrt : r' ∈ t := hR₀ r' (le_trans hr hr'.1.1)
      have hestimate : u r' ≤ C * Real.log r' := by
        have hmem : r' ∈ s ∩ t := ⟨hr'.2, hrt⟩
        rw [← hst] at hmem
        exact hmem
      exact ⟨r', hr'.1.1, hr'.1.2, hestimate⟩
  rw [isBigO_iff]
  refine ⟨max C 0 * (Real.log (M + 2) + 1) + |u (max x₀ R₀)|, ?_⟩
  filter_upwards [eventually_ge_atTop (max x₀ R₀), eventually_ge_atTop 1,
    eventually_ge_atTop (Real.exp 1)] with r hr₁ hr₂ hre
  have hlogr : 1 ≤ Real.log r := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hre
  obtain ⟨r', hrr', hr'M, hr'good⟩ := hgood r (le_trans (le_max_right x₀ R₀) hr₁)
  have hx₀r : x₀ ≤ r := le_trans (le_max_left x₀ R₀) hr₁
  have hmono' : u r ≤ u r' :=
    hmono (Set.mem_Ici.2 hx₀r) (Set.mem_Ici.2 (le_trans hx₀r hrr')) hrr'
  have hlog : Real.log r' ≤ Real.log (M + 2) + Real.log r := by
    have hscaled : r' ≤ (M + 2) * r := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ M + 1)
        (by linarith : (0 : ℝ) ≤ r - 1)]
    calc Real.log r'
        ≤ Real.log ((M + 2) * r) :=
          Real.log_le_log (lt_of_lt_of_le one_pos (le_trans hr₂ hrr')) hscaled
      _ = Real.log (M + 2) + Real.log r :=
          Real.log_mul (by linarith) (by linarith)
  have hlogM : 0 ≤ Real.log (M + 2) := Real.log_nonneg (by linarith)
  have hupper : u r ≤ max C 0 * (Real.log (M + 2) + 1) * Real.log r := by
    calc u r
        ≤ C * Real.log r' := le_trans hmono' hr'good
      _ ≤ max C 0 * Real.log r' :=
          mul_le_mul_of_nonneg_right (le_max_left C 0)
            (Real.log_nonneg (le_trans hr₂ hrr'))
      _ ≤ max C 0 * (Real.log (M + 2) + Real.log r) :=
          mul_le_mul_of_nonneg_left hlog (le_max_right C 0)
      _ ≤ max C 0 * ((Real.log (M + 2) + 1) * Real.log r) := by
          have hlog' : Real.log (M + 2) + Real.log r ≤
              (Real.log (M + 2) + 1) * Real.log r := by nlinarith
          exact mul_le_mul_of_nonneg_left hlog' (le_max_right C 0)
      _ = max C 0 * (Real.log (M + 2) + 1) * Real.log r := by ring
  have hlower : u (max x₀ R₀) ≤ u r :=
    hmono (Set.mem_Ici.2 (le_max_left x₀ R₀)) (Set.mem_Ici.2 hx₀r) hr₁
  have hconstant : 0 ≤ max C 0 * (Real.log (M + 2) + 1) :=
    mul_nonneg (le_max_right C 0) (by linarith)
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ Real.log r), abs_le]
  constructor
  · nlinarith [neg_abs_le (u (max x₀ R₀)), abs_nonneg (u (max x₀ R₀))]
  · nlinarith [abs_nonneg (u (max x₀ R₀))]

/-- The positive logarithm is sublinear at positive infinity. -/
theorem tendsto_posLog_div_atTop :
    Tendsto (fun x : ℝ ↦ log⁺ x / x) atTop (𝓝 0) := by
  apply Tendsto.congr' _ Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  filter_upwards [eventually_ge_atTop 1] with x hx
  rw [Real.posLog_eq_log (by rwa [abs_of_nonneg (by linarith)]), id_eq]

/-- Compare the manuscript's logarithmic error with the form used in
ProjectVD's second main theorem. -/
theorem log_error_le {r T : ℝ} (hr : Real.exp 1 ≤ r) :
    Real.log (Real.exp 1 + r * T) ≤ 3 * (log⁺ T + Real.log r) := by
  have hr1 : 1 ≤ r := by linarith [Real.add_one_le_exp 1]
  have hlogr : 1 ≤ Real.log r := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hr
  have hrpos : log⁺ r = Real.log r :=
    Real.posLog_eq_log (by rwa [abs_of_nonneg (by linarith)])
  have hexp : log⁺ (Real.exp 1) = 1 := by simp [Real.posLog_def]
  have hsum := Real.posLog_add (x := Real.exp 1) (y := r * T)
  have hprod := Real.posLog_mul (x := r) (y := T)
  have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hlog : Real.log (Real.exp 1 + r * T) ≤ log⁺ (Real.exp 1 + r * T) :=
    le_max_right _ _
  rw [hexp] at hsum
  rw [hrpos] at hprod
  linarith [Real.posLog_nonneg (x := T)]

/-- Absorb the self-referential positive logarithm in the second main
theorem's error. The resulting bound still allows the same exceptional set. -/
theorem eventually_le_log_of_le_posLog {u : ℝ → ℝ} {C : ℝ}
    (hbound : ∀ᶠ r in volume.cofinite ⊓ atTop,
      u r ≤ C * (log⁺ (u r) + Real.log r)) :
    ∃ K > 0, ∀ᶠ r in volume.cofinite ⊓ atTop, u r ≤ K * Real.log r := by
  let A := max C 0
  have hA : 0 ≤ A := le_max_right C 0
  obtain ⟨B, hB⟩ := eventually_atTop.1
    (tendsto_posLog_div_atTop.eventually_le_const
      (show (0 : ℝ) < 1 / (2 * (A + 1)) by positivity))
  refine ⟨2 * A + max B 1, by linarith [le_max_right B 1], ?_⟩
  filter_upwards [hbound, mem_inf_of_right (eventually_ge_atTop (Real.exp 1))]
    with r hr hre
  have hlogr : 1 ≤ Real.log r := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hre
  have hsum : 0 ≤ log⁺ (u r) + Real.log r := by
    linarith [Real.posLog_nonneg (x := u r)]
  have hupper : u r ≤ A * log⁺ (u r) + A * Real.log r := by
    have := mul_le_mul_of_nonneg_right (le_max_left C 0) hsum
    dsimp [A]
    nlinarith
  by_cases hlarge : max B 1 ≤ u r
  · have hsmall := hB (u r) (le_trans (le_max_left B 1) hlarge)
    have hu : 0 < u r := lt_of_lt_of_le one_pos (le_trans (le_max_right B 1) hlarge)
    rw [div_le_iff₀ hu] at hsmall
    have hfactor : A * (1 / (2 * (A + 1))) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) two_pos]
      linarith
    have habsorb : A * log⁺ (u r) ≤ u r / 2 := by
      calc A * log⁺ (u r)
          ≤ A * (1 / (2 * (A + 1)) * u r) :=
            mul_le_mul_of_nonneg_left hsmall hA
        _ = (A * (1 / (2 * (A + 1)))) * u r := by ring
        _ ≤ (1 / 2) * u r := mul_le_mul_of_nonneg_right hfactor hu.le
        _ = u r / 2 := by ring
    have hrest : 0 ≤ max B 1 * Real.log r :=
      mul_nonneg (le_trans zero_le_one (le_max_right B 1)) (by linarith)
    nlinarith
  · have hsmall : u r < max B 1 := lt_of_not_ge hlarge
    have hbase : max B 1 ≤ max B 1 * Real.log r :=
      le_mul_of_one_le_right (le_trans zero_le_one (le_max_right B 1)) hlogr
    have hrest : 0 ≤ 2 * A * Real.log r := by positivity
    nlinarith

end ThreeIM.PicardSupport
