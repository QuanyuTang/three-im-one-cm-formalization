module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Regular coordinates and profile estimates for transport

The marked value has been translated to zero. We write
`Q(w) = (w - a₂) * (w - a₃)`, `D = F - G`, and `h = G / D`.
The auxiliary coefficients used here are values of regular representatives.
The first lemma recovers an amplitude identity at an ordinary point where
the displayed auxiliary denominator is nonzero. The subsequent derivative
lemmas instead take the amplitude identities directly, so they can also be
used after extending those identities between holomorphic representatives.
They never evaluate a raw meromorphic quotient at a junk value.

The quantitative bounds use explicit constants. For `‖w‖ ≤ δ * M`, `δ ≤ 1`,
put `K = M * (M + ‖a₂‖ + ‖a₃‖)`. A relative profile error at most `η` gives
an error at most `‖c‖ * (‖a₂ * a₃‖ + K) * (δ + η)` in the scaled
coefficient `u * Q(w) / τ`. For the second profile one takes
`c = B₀ * exp(-x)`, retaining the factor `exp(-x)`.

These are local coordinate and pointwise estimates. They do not establish
normality, meromorphic continuation, or the full transport contradiction.
-/

@[expose] public section

namespace ThreeIM

/-- The quadratic factor of the cubic after the marked value is translated to zero. -/
def transportQ (a₂ a₃ w : ℂ) : ℂ := (w - a₂) * (w - a₃)

/-- Recover the amplitude identity only at a regular auxiliary denominator. -/
theorem transport_amplitude_of_regular_aux {f g f' u a₂ a₃ : ℂ}
    (hden : f * transportQ a₂ a₃ f ≠ 0)
    (hu : u = (f - g) * f' / (f * transportQ a₂ a₃ f)) :
    (f - g) * f' = (u * transportQ a₂ a₃ f) * f := by
  rw [hu]
  calc
    (f - g) * f' = ((f - g) * f' / (f * transportQ a₂ a₃ f)) *
        (f * transportQ a₂ a₃ f) := (div_mul_cancel₀ _ hden).symm
    _ = _ := by ring

/-- Algebraic reconstruction of the two maps from the transport coordinates. -/
theorem transport_coordinate_values {f g τ : ℂ}
    (hD : f - g ≠ 0) (hτ : τ ≠ 0) :
    f = τ * ((f - g) / τ) * (1 + g / (f - g)) ∧
      g = τ * ((f - g) / τ) * (g / (f - g)) := by
  constructor
  · (field_simp [hD, hτ]; ring)
  · field_simp [hD, hτ]

/-- The exact derivative equations in `D = F - G` and `h = G / D`.
Only the two regular amplitude identities and `D ≠ 0` are needed. -/
theorem transport_coordinate_derivatives {F G : ℝ → ℂ} {x : ℝ}
    {f' g' A B : ℂ}
    (hF : HasDerivAt F f' x) (hG : HasDerivAt G g' x)
    (hD : F x - G x ≠ 0)
    (hFA : (F x - G x) * f' = A * F x)
    (hGB : (F x - G x) * g' = B * G x) :
    HasDerivAt (fun t => F t - G t)
      (A + (A - B) * (G x / (F x - G x))) x ∧
    HasDerivAt (fun t => G t / (F t - G t))
      (-(A - B) * (G x / (F x - G x)) *
        (1 + G x / (F x - G x)) / (F x - G x)) x := by
  have hfp : f' = A * F x / (F x - G x) :=
    (eq_div_iff hD).2 (by simpa only [mul_comm] using hFA)
  have hgp : g' = B * G x / (F x - G x) :=
    (eq_div_iff hD).2 (by simpa only [mul_comm] using hGB)
  constructor
  · convert hF.sub hG using 1
    rw [hfp, hgp]
    (field_simp [hD]; ring)
  · convert hG.div (hF.sub hG) hD using 1
    simp only [Pi.sub_apply]
    rw [hfp, hgp]
    (field_simp [hD]; ring)

/-- At a point where `G ≠ 0` as well as `D ≠ 0`, the logarithmic derivative
of the transport coordinate is the expression used in the manuscript. -/
theorem transport_log_derivative {F G : ℝ → ℂ} {x : ℝ} {f' g' A B : ℂ}
    (hF : HasDerivAt F f' x) (hG : HasDerivAt G g' x)
    (hD : F x - G x ≠ 0) (hG₀ : G x ≠ 0)
    (hFA : (F x - G x) * f' = A * F x)
    (hGB : (F x - G x) * g' = B * G x) :
    deriv (fun t => G t / (F t - G t)) x / (G x / (F x - G x)) =
      -(A - B) * (1 + G x / (F x - G x)) / (F x - G x) := by
  rw [(transport_coordinate_derivatives hF hG hD hFA hGB).2.deriv]
  field_simp [hD, hG₀]

/-- Rescaling by a nonzero scale satisfying `τ' = τ / 2` gives precisely the
stable equation required by `transport_bootstrap`. Here `A` and `B` are the
unscaled coefficients and `h` is the value of the second coordinate. -/
theorem transport_rescaled_derivative {D τ : ℝ → ℂ} {x : ℝ} {A B h α : ℂ}
    (hD : HasDerivAt D (A + (A - B) * h) x)
    (hτ : HasDerivAt τ (τ x / 2) x) (hτ₀ : τ x ≠ 0) :
    HasDerivAt (fun t => D t / τ t)
      ((-(1 / 2 : ℝ)) • (D x / τ x - 2 * α) +
        ((A / τ x - α) + (A / τ x - B / τ x) * h)) x := by
  convert hD.div hτ hτ₀ using 1
  simp only [Complex.real_smul, Complex.ofReal_neg, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_ofNat]
  (field_simp [hτ₀]; ring)

/-- The closed bootstrap region bounds both original maps by the small scale
times a fixed constant. No division or pointwise meromorphic value is used. -/
theorem transport_coordinate_norms {f g τ W h α : ℂ} {δ r₀ b₀ : ℝ}
    (hF : f = τ * W * (1 + h)) (hG : g = τ * W * h)
    (hτ : ‖τ‖ ≤ δ) (hW : ‖W - 2 * α‖ ≤ r₀) (hh : ‖h‖ ≤ b₀) :
    ‖f‖ ≤ δ * ((2 * ‖α‖ + r₀) * (1 + b₀)) ∧
      ‖g‖ ≤ δ * ((2 * ‖α‖ + r₀) * (1 + b₀)) := by
  have hδ : 0 ≤ δ := (norm_nonneg τ).trans hτ
  have hr₀ : 0 ≤ r₀ := (norm_nonneg _).trans hW
  have hWnorm : ‖W‖ ≤ 2 * ‖α‖ + r₀ := by
    have htriangle := norm_add_le (W - 2 * α) (2 * α)
    rw [sub_add_cancel, norm_mul] at htriangle
    norm_num at htriangle
    linarith
  have hM : 0 ≤ 2 * ‖α‖ + r₀ := by positivity
  have hτW : ‖τ * W‖ ≤ δ * (2 * ‖α‖ + r₀) := by
    rw [norm_mul]
    exact mul_le_mul hτ hWnorm (norm_nonneg W) hδ
  have hprod : ∀ q : ℂ, ‖q‖ ≤ 1 + b₀ →
      ‖τ * W * q‖ ≤ δ * ((2 * ‖α‖ + r₀) * (1 + b₀)) := by
    intro q hq
    rw [norm_mul]
    calc
      ‖τ * W‖ * ‖q‖ ≤ (δ * (2 * ‖α‖ + r₀)) * (1 + b₀) :=
        mul_le_mul hτW hq (norm_nonneg q) (mul_nonneg hδ hM)
      _ = δ * ((2 * ‖α‖ + r₀) * (1 + b₀)) := by ring
  constructor
  · rw [hF]
    apply hprod
    simpa only [norm_one] using (norm_add_le (1 : ℂ) h).trans
      (add_le_add le_rfl hh)
  · rw [hG]
    exact hprod h (by linarith)

/-- Exact quadratic remainder at the marked value. -/
theorem transportQ_sub_at_zero (a₂ a₃ w : ℂ) :
    transportQ a₂ a₃ w - a₂ * a₃ = w * (w - a₂ - a₃) := by
  dsimp [transportQ]
  ring

/-- A norm bound for the quadratic remainder, with no smallness assumption. -/
theorem norm_transportQ_sub_le (a₂ a₃ w : ℂ) :
    ‖transportQ a₂ a₃ w - a₂ * a₃‖ ≤
      ‖w‖ * (‖w‖ + ‖a₂‖ + ‖a₃‖) := by
  rw [transportQ_sub_at_zero, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg w)
  exact (norm_sub_le _ _).trans
    (add_le_add (norm_sub_le w a₂) le_rfl)

/-- On a fixed bounded coordinate region the quadratic remainder is linear
in the small scale `δ`. -/
theorem norm_transportQ_sub_le_scale {a₂ a₃ w : ℂ} {δ M : ℝ}
    (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1) (hM : 0 ≤ M) (hw : ‖w‖ ≤ δ * M) :
    ‖transportQ a₂ a₃ w - a₂ * a₃‖ ≤
      δ * (M * (M + ‖a₂‖ + ‖a₃‖)) := by
  have hwM : ‖w‖ ≤ M := hw.trans (by nlinarith)
  calc
    ‖transportQ a₂ a₃ w - a₂ * a₃‖ ≤
        ‖w‖ * (‖w‖ + ‖a₂‖ + ‖a₃‖) := norm_transportQ_sub_le _ _ _
    _ ≤ (δ * M) * (M + ‖a₂‖ + ‖a₃‖) :=
      mul_le_mul hw (by linarith) (by positivity) (mul_nonneg hδ hM)
    _ = δ * (M * (M + ‖a₂‖ + ‖a₃‖)) := by ring

/-- Relative profile error controls the scaled coefficient. The nonzero
denominators are explicit; `q` will be a regular value of `Q(F)` or `Q(G)`. -/
theorem transport_coefficient_error {u τ c q p : ℂ} {η L : ℝ}
    (hτ : τ ≠ 0) (hc : c ≠ 0)
    (hprofile : ‖u / (τ * c) - 1‖ ≤ η) (hq : ‖q - p‖ ≤ L) :
    ‖u * q / τ - c * p‖ ≤ ‖c‖ * (L + η * (‖p‖ + L)) := by
  have hη : 0 ≤ η := (norm_nonneg _).trans hprofile
  have hL : 0 ≤ L := (norm_nonneg _).trans hq
  have hscale_identity : u / τ - c = c * (u / (τ * c) - 1) := by
    field_simp [hτ, hc]
  have hscale : ‖u / τ - c‖ ≤ ‖c‖ * η := by
    rw [hscale_identity, norm_mul]
    exact mul_le_mul_of_nonneg_left hprofile (norm_nonneg c)
  have hqnorm : ‖q‖ ≤ ‖p‖ + L := by
    have htriangle := norm_add_le (q - p) p
    rw [sub_add_cancel] at htriangle
    linarith
  have hidentity : u * q / τ - c * p = (u / τ - c) * q + c * (q - p) := by
    simp only [div_eq_mul_inv]
    ring
  calc
    ‖u * q / τ - c * p‖ = ‖(u / τ - c) * q + c * (q - p)‖ := by rw [hidentity]
    _ ≤ ‖u / τ - c‖ * ‖q‖ + ‖c‖ * ‖q - p‖ := by
      simpa only [norm_mul] using norm_add_le ((u / τ - c) * q) (c * (q - p))
    _ ≤ (‖c‖ * η) * (‖p‖ + L) + ‖c‖ * L :=
      add_le_add
        (mul_le_mul hscale hqnorm (norm_nonneg q) (mul_nonneg (norm_nonneg c) hη))
        (mul_le_mul_of_nonneg_left hq (norm_nonneg c))
    _ = ‖c‖ * (L + η * (‖p‖ + L)) := by ring

/-- The explicit `O(δ + η)` estimate for a scaled auxiliary coefficient. -/
theorem transport_scaled_coefficient_bound {u τ c a₂ a₃ w : ℂ} {δ M η : ℝ}
    (hτ : τ ≠ 0) (hc : c ≠ 0)
    (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1) (hM : 0 ≤ M)
    (hw : ‖w‖ ≤ δ * M) (hprofile : ‖u / (τ * c) - 1‖ ≤ η) :
    ‖u * transportQ a₂ a₃ w / τ - c * (a₂ * a₃)‖ ≤
      (‖c‖ * (‖a₂ * a₃‖ + M * (M + ‖a₂‖ + ‖a₃‖))) * (δ + η) := by
  let K : ℝ := M * (M + ‖a₂‖ + ‖a₃‖)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hδK : δ * K ≤ K := by nlinarith
  have hη : 0 ≤ η := (norm_nonneg _).trans hprofile
  have hq : ‖transportQ a₂ a₃ w - a₂ * a₃‖ ≤ δ * K :=
    norm_transportQ_sub_le_scale hδ hδ₁ hM hw
  calc
    ‖u * transportQ a₂ a₃ w / τ - c * (a₂ * a₃)‖ ≤
        ‖c‖ * (δ * K + η * (‖a₂ * a₃‖ + δ * K)) :=
      transport_coefficient_error hτ hc hprofile hq
    _ ≤ ‖c‖ * (δ * K + η * (‖a₂ * a₃‖ + K)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add le_rfl hδK) hη))
        (norm_nonneg c)
    _ ≤ ‖c‖ * ((‖a₂ * a₃‖ + K) * (δ + η)) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg c)
      nlinarith [mul_nonneg hδ (norm_nonneg (a₂ * a₃))]
    _ = (‖c‖ * (‖a₂ * a₃‖ + M * (M + ‖a₂‖ + ‖a₃‖))) * (δ + η) := by
      dsimp [K]
      ring

/-- Both profile estimates, preserving the decaying real factor `θ` in the
second one. In the manuscript `θ = exp(-x)`, and `M` is provided by
`transport_coordinate_norms`. -/
theorem transport_scaled_coefficients_bounds
    {u v τ A₀ B₀ a₂ a₃ f g : ℂ} {θ δ M η : ℝ}
    (hτ : τ ≠ 0) (hA₀ : A₀ ≠ 0) (hB₀ : B₀ ≠ 0) (hθ : 0 < θ)
    (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1) (hM : 0 ≤ M)
    (hf : ‖f‖ ≤ δ * M) (hg : ‖g‖ ≤ δ * M)
    (hu : ‖u / (τ * A₀) - 1‖ ≤ η)
    (hv : ‖v / (τ * (B₀ * (θ : ℂ))) - 1‖ ≤ η) :
    ‖u * transportQ a₂ a₃ f / τ - A₀ * (a₂ * a₃)‖ ≤
        (‖A₀‖ * (‖a₂ * a₃‖ + M * (M + ‖a₂‖ + ‖a₃‖))) * (δ + η) ∧
    ‖v * transportQ a₂ a₃ g / τ - (B₀ * (a₂ * a₃)) * (θ : ℂ)‖ ≤
        θ * ((‖B₀‖ * (‖a₂ * a₃‖ + M * (M + ‖a₂‖ + ‖a₃‖))) * (δ + η)) := by
  constructor
  · exact transport_scaled_coefficient_bound hτ hA₀ hδ hδ₁ hM hf hu
  · have hBθ : B₀ * (θ : ℂ) ≠ 0 :=
      mul_ne_zero hB₀ (Complex.ofReal_ne_zero.mpr hθ.ne')
    have hbound := transport_scaled_coefficient_bound (a₂ := a₂) (a₃ := a₃)
      hτ hBθ hδ hδ₁ hM hg hv
    have hcenter : (B₀ * (θ : ℂ)) * (a₂ * a₃) =
        (B₀ * (a₂ * a₃)) * (θ : ℂ) := by ring
    rw [hcenter] at hbound
    simpa only [norm_mul, Complex.norm_real, Real.norm_of_nonneg hθ.le,
      mul_assoc, mul_comm, mul_left_comm] using hbound

/-- The exact rescaled ODE error is small when its coefficients are close
to their limiting profiles. The bound keeps the actual factor `‖h‖`. -/
theorem transport_rescaled_error_bound {a b α β h : ℂ} {eA eB θ : ℝ}
    (hA : ‖a - α‖ ≤ eA) (hB : ‖b - β‖ ≤ eB) (hβ : ‖β‖ ≤ θ) :
    ‖(a - α) + (a - b) * h‖ ≤
      eA + (‖α‖ + eA + θ + eB) * ‖h‖ := by
  have ha : ‖a‖ ≤ ‖α‖ + eA := by
    have htriangle := norm_add_le (a - α) α
    rw [sub_add_cancel] at htriangle
    linarith
  have hb : ‖b‖ ≤ θ + eB := by
    have htriangle := norm_add_le (b - β) β
    rw [sub_add_cancel] at htriangle
    linarith
  calc
    ‖(a - α) + (a - b) * h‖ ≤ ‖a - α‖ + ‖a - b‖ * ‖h‖ := by
      simpa only [norm_mul] using norm_add_le (a - α) ((a - b) * h)
    _ ≤ eA + (‖a‖ + ‖b‖) * ‖h‖ :=
      add_le_add hA (mul_le_mul_of_nonneg_right (norm_sub_le a b) (norm_nonneg h))
    _ ≤ eA + (‖α‖ + eA + θ + eB) * ‖h‖ := by
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg h)
      linarith

/-- The corresponding logarithmic-derivative error. Its explicit numerator
has the manuscript's five contributions: coordinate error, the two profile
errors, the decaying second profile, and `‖h‖`. -/
theorem transport_log_derivative_error_bound {a b W h α β : ℂ} {eA eB θ : ℝ}
    (hW : W ≠ 0) (hA : ‖a - α‖ ≤ eA) (hB : ‖b - β‖ ≤ eB)
    (hβ : ‖β‖ ≤ θ) :
    ‖-(a - b) * (1 + h) / W + (1 / 2 : ℂ)‖ ≤
      (‖W - 2 * α‖ / 2 + eA +
        (‖α‖ + eA + θ + eB) * ‖h‖ + θ + eB) / ‖W‖ := by
  have hb : ‖b‖ ≤ θ + eB := by
    have htriangle := norm_add_le (b - β) β
    rw [sub_add_cancel] at htriangle
    linarith
  have herror := transport_rescaled_error_bound (h := h) hA hB hβ
  have hidentity : -(a - b) * (1 + h) / W + (1 / 2 : ℂ) =
      ((W - 2 * α) / 2 - ((a - α) + (a - b) * h) + b) / W := by
    (field_simp [hW]; ring)
  rw [hidentity, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg W)
  calc
    ‖(W - 2 * α) / 2 - ((a - α) + (a - b) * h) + b‖ ≤
        ‖(W - 2 * α) / 2 - ((a - α) + (a - b) * h)‖ + ‖b‖ := norm_add_le _ _
    _ ≤ (‖(W - 2 * α) / 2‖ + ‖(a - α) + (a - b) * h‖) + ‖b‖ :=
      add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ (‖W - 2 * α‖ / 2 +
        (eA + (‖α‖ + eA + θ + eB) * ‖h‖)) + (θ + eB) := by
      norm_num only [norm_div, Complex.norm_ofNat]
      exact add_le_add (add_le_add le_rfl herror) hb
    _ = _ := by ring

/-- A quarter-unit complex error from `-1/2` gives the strict logarithmic
decay condition in the real transport bootstrap. -/
theorem transport_re_log_derivative_le {q : ℂ}
    (hq : ‖q + (1 / 2 : ℂ)‖ ≤ 1 / 4) : q.re ≤ -(1 / 4 : ℝ) := by
  have hreal := Complex.re_le_norm (q + (1 / 2 : ℂ))
  norm_num at hreal
  linarith

end ThreeIM
