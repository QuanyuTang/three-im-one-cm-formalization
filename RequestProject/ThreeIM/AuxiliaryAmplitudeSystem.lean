module

public import RequestProject.ThreeIM.AmplitudeSequenceCompactness
public import RequestProject.ThreeIM.AuxiliaryPair
public import RequestProject.ThreeIM.RepresentativePairs
public import RequestProject.ThreeIM.MarkedDerivative

/-!
# The actual amplitude system obtained from auxiliary identities

Changes of representatives are through punctured germs. Once the finite
chart is holomorphic, the cleared identities hold at every point. Translation
by a shared value and division by the original nonzero scale give the
amplitude equations used by the compactness theorem.
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

set_option autoImplicit false

def amplitudeRemainder (a : Fin 3 → ℂ) (j : Fin 3) (w : ℂ) : ℂ :=
  ∏ i ∈ Finset.univ.erase j, (w - a i)

theorem amplitudeRemainder_nonzero {a : Fin 3 → ℂ} (ha : Function.Injective a)
    (j : Fin 3) : amplitudeRemainder a j (a j) ≠ 0 :=
  prod_erase_ne_zero ha j

theorem amplitudeRemainder_differentiable (a : Fin 3 → ℂ) (j : Fin 3) :
    Differentiable ℂ (amplitudeRemainder a j) := by
  unfold amplitudeRemainder
  fun_prop

theorem AuxiliaryPairOn.congr_codiscreteWithin {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {f g F G u v : ℂ → ℂ} {a : Fin 3 → ℂ}
    (h : AuxiliaryPairOn Ω f g u v a)
    (hf : f =ᶠ[codiscreteWithin Ω] F) (hg : g =ᶠ[codiscreteWithin Ω] G) :
    AuxiliaryPairOn Ω F G u v a := by
  have haux := auxiliary_congr_codiscreteWithin hΩ hf hg a
  exact ⟨h.pair.congr_codiscreteWithin hΩ hf hg, h.holo_u, h.holo_v,
    h.nonzero_u, h.nonzero_v, haux.1.symm.trans h.u_eq, haux.2.1.symm.trans h.v_eq⟩

theorem AuxiliaryPairOn.cleared_eqOn {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {F G u v : ℂ → ℂ} {a : Fin 3 → ℂ}
    (h : AuxiliaryPairOn Ω F G u v a)
    (hF : DifferentiableOn ℂ F Ω) (hG : DifferentiableOn ℂ G Ω) :
    (∀ z ∈ Ω, (F z - G z) * deriv F z = u z * cubicP a (F z)) ∧
      (∀ z ∈ Ω, (F z - G z) * deriv G z = v z * cubicP a (G z)) := by
  have hd := hF.continuousOn.sub hG.continuousOn
  exact ⟨auxiliary_cleared_eqOn a hΩ (hF.analyticOnNhd hΩ) h.pair.nonconst_f hd
      h.holo_u.continuousOn h.u_eq,
    auxiliary_cleared_eqOn a hΩ (hG.analyticOnNhd hΩ) h.pair.nonconst_g hd
      h.holo_v.continuousOn h.v_eq⟩

theorem auxiliary_amplitude_system {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {F G u v : ℂ → ℂ} {a : Fin 3 → ℂ} (j : Fin 3)
    (h : AuxiliaryPairOn Ω F G u v a)
    (hF : DifferentiableOn ℂ F Ω) (hG : DifferentiableOn ℂ G Ω)
    {ε : ℂ} (hε : ε ≠ 0)
    (hQ : ∀ z ∈ Ω, amplitudeRemainder a j (F z) ≠ 0) :
    AmplitudeSystemOn Ω
      (fun z => (F z - a j) / ε) (fun z => (G z - a j) / ε)
      (fun z => (u z / ε) * amplitudeRemainder a j (F z))
      (fun z => (v z / ε) * amplitudeRemainder a j (G z)) := by
  have hX := (hF.sub_const (a j)).div_const ε
  have hY := (hG.sub_const (a j)).div_const ε
  have hQF := (amplitudeRemainder_differentiable a j).differentiableOn.comp hF
    (mapsTo_univ F Ω)
  have hQG := (amplitudeRemainder_differentiable a j).differentiableOn.comp hG
    (mapsTo_univ G Ω)
  have hclear := h.cleared_eqOn hΩ hF hG
  have hdiff (w : ℂ) :
      (F w - a j) / ε - (G w - a j) / ε = (F w - G w) / ε := by ring
  refine ⟨hX, hY, ((h.holo_u.div_const ε).mul hQF),
    ((h.holo_v.div_const ε).mul hQG), ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact mul_ne_zero (div_ne_zero (h.nonzero_u z hz) hε) (hQ z hz)
  · intro z hz
    have hmero := ((hX.sub hY).analyticOnNhd hΩ z hz).meromorphicAt
    apply (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hmero).mpr
    have hm := (hF.sub hG).analyticOnNhd hΩ z hz
    filter_upwards [(meromorphicOrderAt_ne_top_iff_eventually_ne_zero
      hm.meromorphicAt).mp (h.pair.distinct z hz)] with w hw
    change (F w - a j) / ε - (G w - a j) / ε ≠ 0
    rw [hdiff]
    exact div_ne_zero hw hε
  · intro z hz
    rw [deriv_div_const, deriv_sub_const, hdiff]
    have hc := hclear.1 z hz
    rw [cubicP_eq_mul a j (F z)] at hc
    change (F z - G z) / ε * (deriv F z / ε) =
      u z / ε * amplitudeRemainder a j (F z) * ((F z - a j) / ε)
    dsimp only [amplitudeRemainder]
    calc
      _ = ((F z - G z) * deriv F z) * ε⁻¹ * ε⁻¹ := by
        simp only [div_eq_mul_inv]
        ring
      _ = (u z * ((F z - a j) * ∏ i ∈ Finset.univ.erase j, (F z - a i))) * ε⁻¹ * ε⁻¹ := by
        rw [hc]
      _ = _ := by simp only [div_eq_mul_inv]; ring
  · intro z hz
    rw [deriv_div_const, deriv_sub_const, hdiff]
    have hc := hclear.2 z hz
    rw [cubicP_eq_mul a j (G z)] at hc
    change (F z - G z) / ε * (deriv G z / ε) =
      v z / ε * amplitudeRemainder a j (G z) * ((G z - a j) / ε)
    dsimp only [amplitudeRemainder]
    calc
      _ = ((F z - G z) * deriv G z) * ε⁻¹ * ε⁻¹ := by
        simp only [div_eq_mul_inv]
        ring
      _ = (v z * ((G z - a j) * ∏ i ∈ Finset.univ.erase j, (G z - a i))) * ε⁻¹ * ε⁻¹ := by
        rw [hc]
      _ = _ := by simp only [div_eq_mul_inv]; ring

end ThreeIM
