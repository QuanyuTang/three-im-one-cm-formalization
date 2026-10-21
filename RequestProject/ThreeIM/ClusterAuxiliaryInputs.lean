module

public import RequestProject.ThreeIM.ClusterStepOne
public import RequestProject.ThreeIM.NevanlinnaAux

/-! # Actual auxiliary functions supply the finite-disk germ hypotheses -/

@[expose] public section

set_option autoImplicit false

open Set Filter Metric Topology

namespace ThreeIM

/-- Nonconstant Phi has a logarithmic derivative with no identically zero
germ. This uses the existing local derivative-order theorem, not any
classification or analytic exclusion theorem. -/
theorem logDeriv_order_ne_top_of_nonconst {Φ : ℂ → ℂ}
    (hΦ : IsNonconstMeroOn Φ univ) (z : ℂ) : meromorphicOrderAt (logDeriv Φ) z ≠ ⊤ := by
  have hm := hΦ.1 z (mem_univ z)
  have hn := (order_deriv_of_nonconst hΦ (mem_univ z)).1
  have hd := order_ne_top_of_nonconst hΦ (mem_univ z)
  have heq : logDeriv Φ = deriv Φ * Φ⁻¹ := by
    ext w
    simp only [logDeriv_apply, Pi.mul_apply, Pi.inv_apply, div_eq_mul_inv]
  rw [heq, meromorphicOrderAt_mul hm.deriv hm.inv, meromorphicOrderAt_inv,
    ← WithTop.coe_untop₀_of_ne_top hn, ← WithTop.coe_untop₀_of_ne_top hd,
    ← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add]
  exact WithTop.coe_ne_top

/-- A normalized pair and its actual nonconstant ratio supply every
germ/extraction hypothesis of the strong Step 1 construction. This
argument is the existing PeriodicCounterexample.phi_nonconst field in
expanded form, avoiding an import cycle through Reduction. -/
theorem NormalizedPair.exists_finite_disk_auxiliary_control
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} (hp : NormalizedPair univ f g a)
    (hNC : ∀ c z, meromorphicOrderAt (fun w => auxPhi a f g w - c) z ≠ ⊤)
    {r R Δ : ℝ} (hr : 1 ≤ r) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hR : R = r + Δ) :
    let Φ := auxPhi a f g
    let A := logDeriv Φ
    let Ψ := auxPsi a f g
    let B := finiteDiskBudget R Δ (finiteDiskCoefficientMass Φ A Ψ R)
    ∃ (D : DivisorFactorData Φ (r + 7 * Δ / 8))
      (E : DivisorFactorData A (r + 7 * Δ / 8)) (P : DivisorFactorData Ψ (r + 7 * Δ / 8)),
      (∀ z ∈ closedBall (0 : ℂ) (r + Δ / 4), ‖deriv D.H z‖ ≤ Real.exp B) ∧
        (∀ z ∈ closedBall (0 : ℂ) (r + Δ / 2),
          |(E.H z).re| + |(P.H z).re| ≤ B / 1000 ∧
            ‖deriv E.H z‖ + ‖deriv P.H z‖ ≤ B / 2) := by
  let Φ := auxPhi a f g
  have hΦ : IsNonconstMeroOn Φ univ :=
    ⟨fun z _ => hp.meromorphic_auxPhi z, fun z _ c => hNC c z⟩
  have hA : MeromorphicOn (logDeriv Φ) univ := by
    intro z _
    exact (hp.meromorphic_auxPhi z).deriv.div (hp.meromorphic_auxPhi z)
  exact exists_finite_disk_factor_control hΦ.1 hA
    (fun z _ => hp.meromorphic_auxPsi z)
    (fun z => order_ne_top_of_nonconst hΦ (mem_univ z))
    (logDeriv_order_ne_top_of_nonconst hΦ)
    (fun z => (hp.order_aux (mem_univ z)).2.2.2) rfl hr hΔ hΔ1 hR

end ThreeIM
