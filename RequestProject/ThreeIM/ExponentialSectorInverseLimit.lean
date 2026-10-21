module

public import RequestProject.ThreeIM.Basic
public import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# The inverse-chart exclusion of an infinite sector limit

The algebra uses totalized division, including zero cubic denominators.
The locally uniform version derives convergence of derivatives by Cauchy's
theorem. The functions supplied to these lemmas are the actual analytic
chart representatives; arbitrary removable-singularity values are not
assumed analytic.
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

set_option autoImplicit false

def exponentialInverseCubicP (a : Fin 3 → ℂ) (x : ℂ) : ℂ :=
  (1 - a 0 * x) * (1 - a 1 * x) * (1 - a 2 * x)

private theorem exponential_cubicP_inv (a : Fin 3 → ℂ) {x : ℂ} (hx : x ≠ 0) :
    cubicP a x⁻¹ = exponentialInverseCubicP a x / x ^ 3 := by
  unfold cubicP exponentialInverseCubicP
  field_simp [hx]

theorem exponential_auxU_inverse (a : Fin 3 → ℂ) {X G : ℂ → ℂ} {z : ℂ}
    (hX : DifferentiableAt ℂ X z) (hx : X z ≠ 0) :
    auxU a (fun w => (X w)⁻¹) G z =
      -(1 - G z * X z) * deriv X z / exponentialInverseCubicP a (X z) := by
  unfold auxU
  rw [deriv_fun_inv'' hX hx, exponential_cubicP_inv a hx]
  by_cases hD : exponentialInverseCubicP a (X z) = 0
  · simp only [hD, zero_div, div_zero]
  · field_simp [hx, hD]

theorem exponential_deriv_div_cubicP_inverse (a : Fin 3 → ℂ) {X : ℂ → ℂ} {z : ℂ}
    (hX : DifferentiableAt ℂ X z) (hx : X z ≠ 0) :
    deriv (fun w => (X w)⁻¹) z / cubicP a ((X z)⁻¹) =
      -X z * deriv X z / exponentialInverseCubicP a (X z) := by
  rw [deriv_fun_inv'' hX hx, exponential_cubicP_inv a hx]
  by_cases hD : exponentialInverseCubicP a (X z) = 0
  · simp only [hD, zero_div, div_zero]
  · field_simp [hx, hD]

private theorem exponential_inverseCubicP_limit (a : Fin 3 → ℂ) {x : ℕ → ℂ}
    (hx : Tendsto x atTop (𝓝 0)) :
    Tendsto (fun n => exponentialInverseCubicP a (x n)) atTop (𝓝 1) := by
  have hcont : Continuous (exponentialInverseCubicP a) := by
    unfold exponentialInverseCubicP
    fun_prop
  simpa only [Function.comp_def, exponentialInverseCubicP, mul_zero, sub_zero, one_mul]
    using (hcont.tendsto 0).comp hx

theorem exponential_auxU_inverse_tendsto_zero (a : Fin 3 → ℂ)
    {X G : ℕ → ℂ → ℂ} {z b : ℂ}
    (hXd : ∀ᶠ n in atTop, DifferentiableAt ℂ (X n) z)
    (hX0 : ∀ᶠ n in atTop, X n z ≠ 0)
    (hX : Tendsto (fun n => X n z) atTop (𝓝 0))
    (hX' : Tendsto (fun n => deriv (X n) z) atTop (𝓝 0))
    (hG : Tendsto (fun n => G n z) atTop (𝓝 b)) :
    Tendsto (fun n => auxU a (fun w => (X n w)⁻¹) (G n) z) atTop (𝓝 0) := by
  have hden := exponential_inverseCubicP_limit a hX
  have hright : Tendsto (fun n => -(1 - G n z * X n z) * deriv (X n) z /
      exponentialInverseCubicP a (X n z)) atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1) := tendsto_const_nhds
    have ht := ((hc.sub (hG.mul hX)).neg.mul hX').div hden
      (show (1 : ℂ) ≠ 0 by norm_num)
    convert ht using 1 <;> first | (funext n; rfl) | simp
  apply hright.congr'
  filter_upwards [hXd, hX0] with n hn hn0
  exact (exponential_auxU_inverse a hn hn0).symm

theorem exponential_deriv_div_cubicP_inverse_tendsto_zero (a : Fin 3 → ℂ)
    {X : ℕ → ℂ → ℂ} {z : ℂ}
    (hXd : ∀ᶠ n in atTop, DifferentiableAt ℂ (X n) z)
    (hX0 : ∀ᶠ n in atTop, X n z ≠ 0)
    (hX : Tendsto (fun n => X n z) atTop (𝓝 0))
    (hX' : Tendsto (fun n => deriv (X n) z) atTop (𝓝 0)) :
    Tendsto (fun n => deriv (fun w => (X n w)⁻¹) z / cubicP a ((X n z)⁻¹))
      atTop (𝓝 0) := by
  have hden := exponential_inverseCubicP_limit a hX
  have hright : Tendsto (fun n => -X n z * deriv (X n) z /
      exponentialInverseCubicP a (X n z)) atTop (𝓝 0) := by
    have ht := (hX.neg.mul hX').div hden (show (1 : ℂ) ≠ 0 by norm_num)
    convert ht using 1 <;> first | (funext n; rfl) | simp
  apply hright.congr'
  filter_upwards [hXd, hX0] with n hn hn0
  exact (exponential_deriv_div_cubicP_inverse a hn hn0).symm

theorem exponential_auxU_inverse_tendsto_zero_of_locallyUniformlyOn
    (a : Fin 3 → ℂ) {Ω : Set ℂ} (hΩ : IsOpen Ω) {z : ℂ} (hz : z ∈ Ω)
    {X G : ℕ → ℂ → ℂ} {b : ℂ}
    (hXd : ∀ᶠ n in atTop, DifferentiableOn ℂ (X n) Ω)
    (hX : TendstoLocallyUniformlyOn X (fun _ => 0) atTop Ω)
    (hX0 : ∀ᶠ n in atTop, X n z ≠ 0)
    (hG : Tendsto (fun n => G n z) atTop (𝓝 b)) :
    Tendsto (fun n => auxU a (fun w => (X n w)⁻¹) (G n) z) atTop (𝓝 0) := by
  have hd : Tendsto (fun n => deriv (X n) z) atTop (𝓝 0) := by
    simpa only [Function.comp_def, deriv_const] using (hX.deriv hXd hΩ).tendsto_at hz
  exact exponential_auxU_inverse_tendsto_zero a
    (hXd.mono fun n hn => hn.differentiableAt (hΩ.mem_nhds hz)) hX0
    (hX.tendsto_at hz) hd hG

theorem exponential_auxU_tendsto_zero_of_inverse_locallyUniformlyOn
    (a : Fin 3 → ℂ) {Ω : Set ℂ} (hΩ : IsOpen Ω) {z : ℂ} (hz : z ∈ Ω)
    {F G : ℕ → ℂ → ℂ} {b : ℂ}
    (hFd : ∀ᶠ n in atTop, DifferentiableOn ℂ (fun w => (F n w)⁻¹) Ω)
    (hF : TendstoLocallyUniformlyOn (fun n w => (F n w)⁻¹) (fun _ => 0) atTop Ω)
    (hF0 : ∀ᶠ n in atTop, F n z ≠ 0)
    (hG : Tendsto (fun n => G n z) atTop (𝓝 b)) :
    Tendsto (fun n => auxU a (F n) (G n) z) atTop (𝓝 0) := by
  simpa only [inv_inv] using exponential_auxU_inverse_tendsto_zero_of_locallyUniformlyOn
    a hΩ hz hFd hF (hF0.mono fun n hn => inv_ne_zero hn) hG

end ThreeIM
