module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The actual exponential scale in the transport manuscript

These facts instantiate the scale and profile-denominator hypotheses of
`transport_profile_continuation` with `τ(z) = ε exp(z/2)` and `θ(t) = exp(-t)`.
The endpoint is `L = 2 log(δ/ε)`, exactly as in the original proof.
-/

@[expose] public section

namespace ThreeIM

noncomputable def transportScale (ε : ℝ) (z : ℂ) : ℂ := (ε : ℂ) * Complex.exp (z / 2)

theorem analyticAt_transportScale (ε : ℝ) (z : ℂ) :
    AnalyticAt ℂ (transportScale ε) z := by
  exact analyticAt_const.mul ((analyticAt_id.div_const).cexp)

theorem hasDerivAt_transportScale (ε : ℝ) (z : ℂ) :
    HasDerivAt (transportScale ε) (transportScale ε z / 2) z := by
  have hd : HasDerivAt (transportScale ε)
      ((ε : ℂ) * (Complex.exp (z / 2) * (1 / 2))) z :=
    (((hasDerivAt_id z).div_const (2 : ℂ)).cexp).const_mul (ε : ℂ)
  convert hd using 1
  dsimp only [transportScale]
  ring

theorem hasDerivAt_transportScale_real (ε x : ℝ) :
    HasDerivAt (fun t : ℝ => transportScale ε (t : ℂ))
      (transportScale ε (x : ℂ) / 2) x :=
  (hasDerivAt_transportScale ε (x : ℂ)).comp_ofReal

theorem transportScale_ne_zero {ε : ℝ} (hε : ε ≠ 0) (z : ℂ) :
    transportScale ε z ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.mpr hε) (Complex.exp_ne_zero _)

theorem transportScale_profile_U_denominator (ε x : ℝ) (A₀ : ℂ) :
    transportScale ε (x : ℂ) * A₀ = (ε : ℂ) * A₀ * Complex.exp ((x : ℂ) / 2) := by
  dsimp only [transportScale]
  ring

theorem transportScale_profile_V_denominator (ε x : ℝ) (B₀ : ℂ) :
    transportScale ε (x : ℂ) * (B₀ * (Real.exp (-x) : ℂ)) =
      (ε : ℂ) * B₀ * Complex.exp (-(x : ℂ) / 2) := by
  simp only [transportScale, Complex.ofReal_exp, Complex.ofReal_neg]
  have hexp : Complex.exp ((x : ℂ) / 2) * Complex.exp (-(x : ℂ)) =
      Complex.exp (-(x : ℂ) / 2) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  calc
    ((ε : ℂ) * Complex.exp ((x : ℂ) / 2)) * (B₀ * Complex.exp (-(x : ℂ))) =
        (ε : ℂ) * B₀ * (Complex.exp ((x : ℂ) / 2) * Complex.exp (-(x : ℂ))) := by ring
    _ = (ε : ℂ) * B₀ * Complex.exp (-(x : ℂ) / 2) := by rw [hexp]

theorem norm_transportScale (ε x : ℝ) :
    ‖transportScale ε (x : ℂ)‖ = |ε| * Real.exp (x / 2) := by
  simp [transportScale, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]

theorem norm_transportScale_le_endpoint {ε δ t : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (ht : t ≤ 2 * Real.log (δ / ε)) : ‖transportScale ε (t : ℂ)‖ ≤ δ := by
  rw [norm_transportScale, abs_of_pos hε]
  have hsmall : Real.exp (t / 2) ≤ Real.exp (Real.log (δ / ε)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hscaled := mul_le_mul_of_nonneg_left hsmall hε.le
  rw [Real.exp_log (div_pos hδ hε)] at hscaled
  calc
    ε * Real.exp (t / 2) ≤ ε * (δ / ε) := hscaled
    _ = δ := by field_simp [hε.ne']

theorem transportScale_start_le_endpoint {ε δ a : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hstart : ε * Real.exp (a / 2) ≤ δ) : a ≤ 2 * Real.log (δ / ε) := by
  have hsmall : Real.exp (a / 2) ≤ δ / ε :=
    (le_div_iff₀ hε).mpr (by simpa only [mul_comm] using hstart)
  have hlog := (Real.le_log_iff_exp_le (div_pos hδ hε)).mpr hsmall
  linarith

theorem transport_decay_bound {a t : ℝ} (hat : a ≤ t) :
    0 < Real.exp (-t) ∧ Real.exp (-t) ≤ Real.exp (-a) :=
  ⟨Real.exp_pos _, Real.exp_le_exp.mpr (neg_le_neg hat)⟩

end ThreeIM
