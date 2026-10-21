module

public import RequestProject.ThreeIM.SelectedSheet
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Assemble actual sheets with fixed multiplicity and target

The sheet data may choose different targets and multiplicities at different
radii. A finite extraction makes both choices constant while preserving the
unbounded radii and every analytic, sharing, and logarithmic control field.
-/

@[expose] public section

open Filter Set Metric Topology

namespace ThreeIM

set_option autoImplicit false

theorem selected_configuration_of_sheets {a : Fin 3 → ℂ} {B : ℕ → ℝ}
    (hB : ∀ n, 0 < B n) (hBlim : Tendsto B atTop atTop)
    (hsheets : ∀ n, Nonempty (SelectedSheet a (B n))) :
    Nonempty SelectedConfiguration := by
  classical
  let S : (n : ℕ) → SelectedSheet a (B n) := fun n => Classical.choice (hsheets n)
  let p : (Fin 3 × Fin 31) → ℕ → Prop := fun q n => (S n).j = q.1 ∧ (S n).m = q.2.val
  have hex : ∀ n, ∃ q : Fin 3 × Fin 31, p q n := by
    intro n
    exact ⟨⟨(S n).j, ⟨(S n).m, Nat.lt_succ_iff.mpr (S n).m_le_thirty⟩⟩, rfl, rfl⟩
  have hfreq : ∃ᶠ n in atTop, ∃ q : Fin 3 × Fin 31, p q n :=
    (Filter.Eventually.of_forall hex).frequently
  obtain ⟨q, hq⟩ := Filter.frequently_exists.mp hfreq
  obtain ⟨σ, hσ, hσq⟩ := extraction_of_frequently_atTop hq
  have htwo : 2 ≤ q.2.val := by
    rw [← (hσq 0).2]
    exact (S (σ 0)).two_le_m
  refine ⟨{
    a := a
    j := q.1
    m := q.2.val
    two_le_m := htwo
    m_le_thirty := Nat.lt_succ_iff.mp q.2.isLt
    B := fun n => B (σ n)
    B_pos := fun n => hB (σ n)
    tendsto_B := hBlim.comp hσ.tendsto_atTop
    F := fun n => (S (σ n)).F
    G := fun n => (S (σ n)).G
    k := fun n => (S (σ n)).k
    pair := fun n => (S (σ n)).pair
    marked_F := fun n => by simpa only [(hσq n).1] using (S (σ n)).marked_F
    marked_G := fun n => by simpa only [(hσq n).1, (hσq n).2] using (S (σ n)).marked_G
    k_holo := fun n => (S (σ n)).k_holo
    k_ne_zero := fun n => (S (σ n)).k_ne_zero
    coeff_U := fun n => by simpa only [(hσq n).2] using (S (σ n)).coeff_U
    coeff_V := fun n => by simpa only [(hσq n).2] using (S (σ n)).coeff_V
    control_center := fun n => (S (σ n)).control_center
    control_log := fun n => (S (σ n)).control_log
  }⟩

theorem selected_configuration_of_eventual_sheets {a : Fin 3 → ℂ} {B : ℕ → ℝ}
    (hB : ∀ n, 0 < B n) (hBlim : Tendsto B atTop atTop)
    (hsheets : ∀ᶠ n in atTop, Nonempty (SelectedSheet a (B n))) :
    Nonempty SelectedConfiguration := by
  obtain ⟨σ, hσ, hσs⟩ := extraction_of_eventually_atTop hsheets
  exact selected_configuration_of_sheets (fun n => hB (σ n))
    (hBlim.comp hσ.tendsto_atTop) hσs

end ThreeIM
