module

public import RequestProject.ThreeIM.AmplitudeTangentLimits
public import RequestProject.ThreeIM.WVTangentTranscendental

/-!
# The marked tangent model for the actual amplitude subsequence

The scalar quotient has marked value one. The unconditional entire scalar
classification therefore fixes it identically to one. Integrating the
difference with its marked value zero gives the explicit exponential model.
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

set_option autoImplicit false

theorem amplitude_tangent_model {α β : ℂ} (hα : α ≠ 0) (hβ : β ≠ 0)
    {H d : ℂ → ℂ} (hH : Differentiable ℂ H) (hd : Differentiable ℂ d)
    (hH0 : H 0 = 1) (hd0 : d 0 = 0) (hscalar : TanScalar α β H)
    (hder : ∀ z, deriv d z = tanC α β z * H z + tanB β z) :
    (∀ z, H z = 1) ∧ (∀ z, d z = 2 * α * (Complex.exp (z / 2) - 1)) := by
  have hh (z : ℂ) : H z = 1 := (wv_tanScalar_const hα hβ hH hscalar z).trans hH0
  let K : ℂ → ℂ := fun z => d z - 2 * tanA α z
  have hK (z : ℂ) : HasDerivAt K 0 z := by
    have hdf : deriv d z = tanA α z := by
      rw [hder z, hh z, mul_one]
      simp only [tanC, sub_add_cancel]
    have hd' := (hd z).hasDerivAt
    rw [hdf] at hd'
    have ht := hd'.sub ((hasDerivAt_tanA α z).const_mul 2)
    convert ht using 1 <;> ring
  have hKc (z : ℂ) : K z = K 0 :=
    is_const_of_deriv_eq_zero (fun w => (hK w).differentiableAt)
      (fun w => (hK w).deriv) z 0
  refine ⟨hh, fun z => ?_⟩
  have he := hKc z
  dsimp only [K] at he
  simp only [hd0, tanA, zero_div, Complex.exp_zero, mul_one] at he
  linear_combination he

private theorem model_tlu_reindex {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (h : TendstoLocallyUniformlyOn F f atTop univ) {i : ℕ → ℕ}
    (hi : Tendsto i atTop atTop) :
    TendstoLocallyUniformlyOn (fun n => F (i n)) f atTop univ := by
  intro v hv x hx
  obtain ⟨U, hU, hev⟩ := h v hv x hx
  exact ⟨U, hU, hi.eventually hev⟩

theorem amplitude_tangent_model_subsequence
    {X Y a b : ℕ → ℂ → ℂ} {α β : ℂ} (hα : α ≠ 0) (hβ : β ≠ 0)
    (hseq : ∀ R > 0, ∀ᶠ n in atTop,
      AmplitudeSystemOn (Metric.ball 0 R) (X n) (Y n) (a n) (b n))
    (ha : TendstoLocallyUniformlyOn a (tanA α) atTop univ)
    (hb : TendstoLocallyUniformlyOn b (tanB β) atTop univ)
    (hmarked : ∀ᶠ n in atTop, X n 0 = 0 ∧ Y n 0 = 0 ∧
      deriv (X n) 0 ≠ 0 ∧ deriv (Y n) 0 = 0) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoLocallyUniformlyOn
        (fun n => amplitudeQuotient (X (φ n)) (fun z => X (φ n) z - Y (φ n) z))
        (fun _ => 1) atTop univ ∧
      TendstoLocallyUniformlyOn (fun n z => X (φ n) z - Y (φ n) z)
        (fun z => 2 * α * (Complex.exp (z / 2) - 1)) atTop univ ∧
      TendstoLocallyUniformlyOn (fun n => X (φ n))
        (fun z => 2 * α * (Complex.exp (z / 2) - 1)) atTop univ ∧
      TendstoLocallyUniformlyOn (fun n => Y (φ n)) (fun _ => 0) atTop univ := by
  obtain ⟨φ, hφ, H, d, hH, hd, hH0, hd0, hHC, hDC, hXC, hYC⟩ :=
    amplitude_system_subsequence hseq (differentiable_tanA α) (differentiable_tanB β)
      (tanB_ne_zero hβ) ha hb hmarked
  have hseqφ : ∀ R > 0, ∀ᶠ n in atTop,
      AmplitudeSystemOn (Metric.ball 0 R) (X (φ n)) (Y (φ n)) (a (φ n)) (b (φ n)) :=
    fun R hR => hφ.tendsto_atTop.eventually (hseq R hR)
  have ht := amplitude_canonical_tangent_limit α β hseqφ hDC hHC
    (model_tlu_reindex ha hφ.tendsto_atTop) (model_tlu_reindex hb hφ.tendsto_atTop)
  have hm := amplitude_tangent_model hα hβ hH hd hH0 hd0 ht.1 ht.2
  refine ⟨φ, hφ, hHC.congr_right (fun z _ => hm.1 z),
    hDC.congr_right (fun z _ => hm.2 z), ?_, ?_⟩
  · exact hXC.congr_right (fun z _ => by
      change d z * H z = _
      rw [hm.1 z, mul_one, hm.2 z])
  · exact hYC.congr_right (fun z _ => by
      change d z * (H z - 1) = _
      rw [hm.1 z, sub_self, mul_zero])

end ThreeIM
