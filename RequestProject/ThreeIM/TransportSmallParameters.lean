module

public import RequestProject.ThreeIM.TransportParameters

/-! # Transport parameters with an arbitrary positive upper bound -/

@[expose] public section

namespace ThreeIM

set_option autoImplicit false

def transportParameterBounds (a₂ a₃ A₀ B₀ : ℂ) (r₀ s : ℝ) : Prop :=
  let α := A₀ * (a₂ * a₃)
  let C := transportProfileConstant a₂ a₃ α r₀ s
  let eA := ‖A₀‖ * C * (s + s)
  let eB := ‖B₀‖ * C * s * (s + s)
  let qB := ‖B₀ * (a₂ * a₃)‖ * s
  let H := ‖α‖ + eA + qB + eB
  eA + H * s ≤ r₀ / 4 ∧
    (r₀ / 2 + eA + H * s + qB + eB) / (2 * ‖α‖ - r₀) ≤ 1 / 4

private theorem parameter_size_le {a₂ a₃ A₀ B₀ : ℂ} {r₀ s : ℝ}
    (hr : 0 < r₀) (hs : 0 < s)
    (hp : transportParameterBounds a₂ a₃ A₀ B₀ r₀ s) :
    ‖A₀ * (a₂ * a₃)‖ * s ≤ r₀ / 4 := by
  let α := A₀ * (a₂ * a₃)
  let C := transportProfileConstant a₂ a₃ α r₀ s
  let eA := ‖A₀‖ * C * (s + s)
  let eB := ‖B₀‖ * C * s * (s + s)
  let qB := ‖B₀ * (a₂ * a₃)‖ * s
  let H := ‖α‖ + eA + qB + eB
  have hC : 0 ≤ C := by dsimp only [C, transportProfileConstant]; positivity
  have heA : 0 ≤ eA := by dsimp only [eA]; positivity
  have heB : 0 ≤ eB := by dsimp only [eB]; positivity
  have hqB : 0 ≤ qB := by dsimp only [qB]; positivity
  have hH : ‖α‖ ≤ H := by dsimp only [H]; linarith
  have hfirst : eA + H * s ≤ r₀ / 4 := hp.1
  have hmul := mul_le_mul_of_nonneg_right hH hs.le
  change ‖α‖ * s ≤ r₀ / 4
  linarith

theorem exists_bounded_transport_parameters {a₂ a₃ A₀ B₀ : ℂ}
    (hα : A₀ * (a₂ * a₃) ≠ 0) {smax : ℝ} (hsmax : 0 < smax) :
    ∃ r₀ s : ℝ, 0 < r₀ ∧ r₀ ≤ ‖A₀ * (a₂ * a₃)‖ / 4 ∧
      0 < s ∧ s ≤ 1 ∧ s ≤ smax ∧ transportParameterBounds a₂ a₃ A₀ B₀ r₀ s := by
  let α := A₀ * (a₂ * a₃)
  have ha : 0 < ‖α‖ := norm_pos_iff.mpr hα
  let r₀ : ℝ := min (‖α‖ / 8) (‖α‖ * smax)
  have hr : 0 < r₀ := lt_min (by positivity) (mul_pos ha hsmax)
  have hsmall : r₀ ≤ ‖A₀ * (a₂ * a₃)‖ / 4 := by
    have hm := min_le_left (‖α‖ / 8) (‖α‖ * smax)
    change min (‖α‖ / 8) (‖α‖ * smax) ≤ ‖α‖ / 4
    linarith
  obtain ⟨s, hs, hs1, hp⟩ := exists_transport_parameters hr hsmall
  have hp' : transportParameterBounds a₂ a₃ A₀ B₀ r₀ s := hp
  have hss := parameter_size_le hr hs hp'
  have hcap : r₀ / 4 ≤ ‖α‖ * smax := by
    have hm : r₀ ≤ ‖α‖ * smax := min_le_right _ _
    linarith
  have hsbound : s ≤ smax := (mul_le_mul_iff_right₀ ha).mp (hss.trans hcap)
  exact ⟨r₀, s, hr, hsmall, hs, hs1, hsbound, hp'⟩

end ThreeIM
