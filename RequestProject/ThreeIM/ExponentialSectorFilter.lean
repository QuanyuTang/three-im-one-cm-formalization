module

public import RequestProject.ThreeIM.Basic

/-! # Limits on proper right sectors, and horizontal rays within a sector -/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

noncomputable def rightSectorAtTop (δ : ℝ) : Filter ℂ :=
  comap (fun z : ℂ => ‖z‖) atTop ⊓ 𝓟 {z : ℂ | δ * ‖z‖ ≤ z.re}

theorem eventually_rightSectorAtTop_iff {δ : ℝ} {P : ℂ → Prop} :
    (∀ᶠ z in rightSectorAtTop δ, P z) ↔
      ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → δ * ‖z‖ ≤ z.re → P z := by
  rw [rightSectorAtTop, eventually_inf_principal, eventually_comap, eventually_atTop]
  constructor
  · rintro ⟨R, hR⟩
    exact ⟨R, fun z hz hs => hR ‖z‖ hz z rfl hs⟩
  · rintro ⟨R, hR⟩
    refine ⟨R, ?_⟩
    intro r hr z hz hs
    apply hR z
    · simpa only [hz] using hr
    · exact hs

theorem tendsto_norm_rightSectorAtTop (δ : ℝ) :
    Tendsto (fun z : ℂ => ‖z‖) (rightSectorAtTop δ) atTop :=
  tendsto_comap.mono_left inf_le_left

theorem eventually_sector_rightSectorAtTop (δ : ℝ) :
    ∀ᶠ z in rightSectorAtTop δ, δ * ‖z‖ ≤ z.re := by
  exact eventually_rightSectorAtTop_iff.mpr ⟨0, fun z _ hs => hs⟩

theorem right_sector_add_nonneg_real {δ : ℝ} (hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    {t : ℂ} (ht : δ * ‖t‖ ≤ t.re) {s : ℝ} (hs : 0 ≤ s) :
    δ * ‖t + (s : ℂ)‖ ≤ (t + (s : ℂ)).re := by
  have hn : ‖t + (s : ℂ)‖ ≤ ‖t‖ + s := by
    simpa only [Complex.norm_real, Real.norm_of_nonneg hs] using norm_add_le t (s : ℂ)
  calc
    δ * ‖t + (s : ℂ)‖ ≤ δ * (‖t‖ + s) := mul_le_mul_of_nonneg_left hn hδ
    _ = δ * ‖t‖ + δ * s := by ring
    _ ≤ t.re + s := add_le_add ht (mul_le_of_le_one_left hs hδone)
    _ = (t + (s : ℂ)).re := by simp

end ThreeIM
