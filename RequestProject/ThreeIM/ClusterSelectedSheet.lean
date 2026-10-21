module

public import RequestProject.ThreeIM.ClusterBranchProfiles
public import RequestProject.ThreeIM.ClusterMarkedRatios
public import RequestProject.ThreeIM.SheetOrientation

/-! # An actual good marked point supplies a normalized selected sheet

The analytic phase is fixed using honest auxiliary representatives. The
original marked local degrees determine the positive real square root.
The reverse orientation uses source reflection and swapping only after
the physical branch has been constructed with its original budget.
-/

@[expose] public section

set_option autoImplicit false

open Set Filter Metric Topology Real

namespace ThreeIM

/-- The local physical construction gives precisely the one-radius data
of the original selected configuration. No selected sheet is supplied as
an input, and no raw auxiliary center value is evaluated. -/
theorem exists_actual_marked_selected_sheet
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} (hp : NormalizedPair univ f g a)
    {r R Δ : ℝ}
    (D : DivisorFactorData (auxPhi a f g) (r + 7 * Δ / 8))
    (E : DivisorFactorData (logDeriv (auxPhi a f g)) (r + 7 * Δ / 8))
    (P : DivisorFactorData (auxPsi a f g) (r + 7 * Δ / 8))
    (hr : 1 ≤ r) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hR : R = r + Δ)
    {j : Fin 3} {z : ℂ} (hmark : IsBoundedMarkedDefect a f g j z) (hz : ‖z‖ ≤ r)
    (haway : Real.exp (-4 * finiteDiskBudget R Δ
      (finiteDiskCoefficientMass (auxPhi a f g) (logDeriv (auxPhi a f g)) (auxPsi a f g) R)) ≤
      truncatedDivisorDistance (jointDivisorSupport D E P) z)
    (hgood : (finiteDiskBudget R Δ
      (finiteDiskCoefficientMass (auxPhi a f g) (logDeriv (auxPhi a f g)) (auxPsi a f g) R)) ^ 10 /
      truncatedDivisorDistance (jointDivisorSupport D E P) z < ‖E.exponentialModel z‖) :
    Nonempty (SelectedSheet a (finiteDiskBudget R Δ
      (finiteDiskCoefficientMass (auxPhi a f g) (logDeriv (auxPhi a f g)) (auxPsi a f g) R))) := by
  obtain ⟨m, hm, hm30, hcases⟩ := hp.boundedMarkedDefect_multiplicities hmark
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  rcases hcases with ⟨hf, hg⟩ | ⟨hf, hg⟩
  · let c : ℂ := (Real.sqrt (1 / (m : ℝ)) : ℂ)
    have hq : (0 : ℝ) < 1 / (m : ℝ) := one_div_pos.mpr hmpos
    have hc : c ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hq).ne'
    have hsq : c ^ 2 = (1 : ℂ) / m := by
      dsimp only [c]
      have hmSq : (Real.sqrt (m : ℝ) : ℂ) ^ 2 = (m : ℂ) := by
        exact_mod_cast Real.sq_sqrt hmpos.le
      simp only [one_div, Real.sqrt_inv, Complex.ofReal_inv, inv_pow, hmSq]
    have hfiber : 0 < meromorphicOrderAt (fun w => auxPhi a f g w - c ^ 2) z := by
      rw [hsq]
      simpa only [Nat.cast_one] using
        hp.auxPhi_fiber_order_pos_of_multiplicities (by decide : 1 ≤ (1 : ℕ))
          (by omega : 1 ≤ m) hf hg
    obtain ⟨v, b, hpair, hmult, hU, hV⟩ := exists_actual_fiber_sheet_with_profiles hp D E P
      hr hΔ hΔ1 hR hc hz haway hgood hfiber
    exact ⟨{
      j := j
      m := m
      two_le_m := hm
      m_le_thirty := hm30
      F := f ∘ b.gamma
      G := g ∘ b.gamma
      k := b.k
      pair := hpair
      marked_F := (hmult (a j : Sphere)).1.trans hf
      marked_G := (hmult (a j : Sphere)).2.trans hg
      k_holo := b.k_holo
      k_ne_zero := b.k_ne_zero
      coeff_U := hU
      coeff_V := hV
      control_center := b.control_center
      control_log := ⟨b.normalizedLog, b.log_holo, b.log_zero,
        fun s hs => ⟨b.log_exp s hs, b.log_bound s hs⟩⟩ }⟩
  · let c : ℂ := (Real.sqrt (m : ℝ) : ℂ)
    have hc : c ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hmpos).ne'
    have hsq : c ^ 2 = (m : ℂ) := by
      dsimp only [c]
      exact_mod_cast Real.sq_sqrt hmpos.le
    have hfiber : 0 < meromorphicOrderAt (fun w => auxPhi a f g w - c ^ 2) z := by
      rw [hsq]
      simpa only [Nat.cast_one, div_one] using
        hp.auxPhi_fiber_order_pos_of_multiplicities (by omega : 1 ≤ m)
          (by decide : 1 ≤ (1 : ℕ)) hf hg
    obtain ⟨v, b, hpair, hmult, hU, hV⟩ := exists_actual_fiber_sheet_with_profiles hp D E P
      hr hΔ hΔ1 hR hc hz haway hgood hfiber
    exact selected_sheet_of_reverse hm hm30 hpair
      ((hmult (a j : Sphere)).1.trans hf) ((hmult (a j : Sphere)).2.trans hg)
      b.k_holo b.k_ne_zero hU hV b.control_center
      ⟨b.normalizedLog, b.log_holo, b.log_zero,
        fun s hs => ⟨b.log_exp s hs, b.log_bound s hs⟩⟩

end ThreeIM
