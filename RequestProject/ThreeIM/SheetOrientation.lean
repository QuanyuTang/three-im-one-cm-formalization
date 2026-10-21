module

public import RequestProject.ThreeIM.SelectedSheet
public import RequestProject.ThreeIM.AffineCovariance

/-!
# Normalize a marked sheet of type (m,1)

Swap the two functions and reflect the sheet variable. The two minus signs
in the auxiliary covariance cancel. All controls use the same B and k(-s),
so no new global budget for the swapped original pair is required.
-/

@[expose] public section

open Filter Set Metric Topology

namespace ThreeIM

set_option autoImplicit false

private theorem sheet_neg_maps (R : ℝ) :
    MapsTo (fun z : ℂ => -z) (ball 0 R) (ball 0 R) := by
  intro z hz
  simpa only [mem_ball_zero_iff, norm_neg] using hz

private theorem sheet_neg_deriv (z : ℂ) : deriv (fun w : ℂ => -w) z = -(1 : ℂ) := by
  have hd : HasDerivAt (fun w : ℂ => -w) (-(1 : ℂ)) z := (hasDerivAt_id z).neg
  exact hd.deriv

private theorem sheet_neg_deriv_ne (z : ℂ) : deriv (fun w : ℂ => -w) z ≠ 0 := by
  rw [sheet_neg_deriv]
  norm_num

theorem normalized_pair_swap_reflect {a : Fin 3 → ℂ} {R : ℝ} {F G : ℂ → ℂ}
    (hp : NormalizedPair (ball 0 R) F G a) :
    NormalizedPair (ball 0 R) (fun z => G (-z)) (fun z => F (-z)) a := by
  exact hp.symm.comp_source (h := fun z : ℂ => -z) (fun _ _ => analyticAt_id.neg)
    (fun z _ => sheet_neg_deriv_ne z) (sheet_neg_maps R)

theorem reflected_auxiliary_profiles {a : Fin 3 → ℂ} {R : ℝ} {F G k : ℂ → ℂ} {c : ℂ}
    (hp : NormalizedPair (ball 0 R) F G a)
    (hU : auxU a F G =ᶠ[codiscreteWithin (ball 0 R)]
      fun z => c * Complex.exp (z / 2) / k z)
    (hV : auxV a F G =ᶠ[codiscreteWithin (ball 0 R)]
      fun z => c⁻¹ * Complex.exp (-z / 2) / k z) :
    (auxU a (fun z => G (-z)) (fun z => F (-z)) =ᶠ[codiscreteWithin (ball 0 R)]
      fun z => c⁻¹ * Complex.exp (z / 2) / k (-z)) ∧
    (auxV a (fun z => G (-z)) (fun z => F (-z)) =ᶠ[codiscreteWithin (ball 0 R)]
      fun z => c * Complex.exp (-z / 2) / k (-z)) := by
  have hmaps : MapsTo (fun z : ℂ => 0 + (-1) * z) (ball 0 R) (ball 0 R) := by
    simpa only [zero_add, neg_one_mul] using sheet_neg_maps R
  have hcov := aux_affine_comp_codiscreteWithin hp.nonconst_g.1 hp.nonconst_f.1
    a (-1) 0 (by norm_num) hmaps
  have hcU := codiscreteWithin_comp_source hU hmaps
    (fun z _ => affine_tendsto_nhdsNE (-1) 0 z (by norm_num))
  have hcV := codiscreteWithin_comp_source hV hmaps
    (fun z _ => affine_tendsto_nhdsNE (-1) 0 z (by norm_num))
  constructor
  · filter_upwards [hcov.1, hcV] with z hz hv
    simp only [zero_add, neg_one_mul] at hz hv
    rw [hz]
    have he : -auxU a G F (-z) = auxV a F G (-z) := by dsimp [auxU, auxV]; ring
    rw [he, hv, neg_neg]
  · filter_upwards [hcov.2.1, hcU] with z hz hu
    simp only [zero_add, neg_one_mul] at hz hu
    rw [hz]
    have he : -auxV a G F (-z) = auxU a F G (-z) := by dsimp [auxU, auxV]; ring
    rw [he, hu]

theorem selected_sheet_of_reverse {a : Fin 3 → ℂ} {B : ℝ} {j : Fin 3} {m : ℕ}
    (hm : 2 ≤ m) (hm30 : m ≤ 30) {F G k : ℂ → ℂ}
    (hp : NormalizedPair (ball 0 (B ^ 6 / 2)) F G a)
    (hF : mult F (a j : Sphere) 0 = m) (hG : mult G (a j : Sphere) 0 = 1)
    (hk : DifferentiableOn ℂ k (ball 0 (B ^ 6 / 2)))
    (hk0 : ∀ z ∈ ball (0 : ℂ) (B ^ 6 / 2), k z ≠ 0)
    (hU : auxU a F G =ᶠ[codiscreteWithin (ball 0 (B ^ 6 / 2))]
      fun z => (Real.sqrt (m : ℝ) : ℂ) * Complex.exp (z / 2) / k z)
    (hV : auxV a F G =ᶠ[codiscreteWithin (ball 0 (B ^ 6 / 2))]
      fun z => (Real.sqrt (m : ℝ) : ℂ)⁻¹ * Complex.exp (-z / 2) / k z)
    (hcenter : |Real.log ‖k 0‖| ≤ 9 * B ^ 2)
    (hlog : ∃ ℓ : ℂ → ℂ, DifferentiableOn ℂ ℓ (ball 0 (B ^ 6 / 2)) ∧ ℓ 0 = 0 ∧
      ∀ z ∈ ball (0 : ℂ) (B ^ 6 / 2),
        Complex.exp (ℓ z) = k z / k 0 ∧ ‖ℓ z‖ ≤ 12 * B⁻¹ ^ 3) :
    Nonempty (SelectedSheet a B) := by
  have hcoeff := reflected_auxiliary_profiles hp hU hV
  have hsqrt : (Real.sqrt (1 / (m : ℝ)) : ℂ) = (Real.sqrt (m : ℝ) : ℂ)⁻¹ := by
    simp only [one_div, Real.sqrt_inv, Complex.ofReal_inv]
  have hneg : ∀ z : ℂ, deriv (fun w : ℂ => -w) z ≠ 0 := by
    intro z
    exact sheet_neg_deriv_ne z
  refine ⟨{
    j := j
    m := m
    two_le_m := hm
    m_le_thirty := hm30
    F := fun z => G (-z)
    G := fun z => F (-z)
    k := fun z => k (-z)
    pair := normalized_pair_swap_reflect hp
    marked_F := ?_
    marked_G := ?_
    k_holo := hk.comp (differentiable_id.neg.differentiableOn) (sheet_neg_maps _)
    k_ne_zero := fun z hz => hk0 _ (sheet_neg_maps _ hz)
    coeff_U := by simpa only [hsqrt, Filter.EventuallyEq] using hcoeff.1
    coeff_V := by simpa only [hsqrt, inv_inv, Filter.EventuallyEq] using hcoeff.2
    control_center := by simpa only [neg_zero] using hcenter
    control_log := ?_
  }⟩
  · change mult (G ∘ fun z : ℂ => -z) (a j : Sphere) 0 = 1
    rw [mult_comp_of_deriv_ne_zero (h := fun z : ℂ => -z) (by fun_prop) (hneg 0), neg_zero]
    exact hG
  · change mult (F ∘ fun z : ℂ => -z) (a j : Sphere) 0 = m
    rw [mult_comp_of_deriv_ne_zero (h := fun z : ℂ => -z) (by fun_prop) (hneg 0), neg_zero]
    exact hF
  · obtain ⟨ℓ, hℓ, hℓ0, hℓeq⟩ := hlog
    refine ⟨fun z => ℓ (-z), hℓ.comp (differentiable_id.neg.differentiableOn)
      (sheet_neg_maps _), by simpa only [neg_zero] using hℓ0, ?_⟩
    intro z hz
    simpa only [neg_zero] using hℓeq (-z) (sheet_neg_maps _ hz)

end ThreeIM
