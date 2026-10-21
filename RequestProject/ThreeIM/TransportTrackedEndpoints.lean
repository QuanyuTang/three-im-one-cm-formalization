module

public import RequestProject.ThreeIM.TransportFiniteTracking
public import RequestProject.ThreeIM.TransportEndpointBounds
public import RequestProject.ThreeIM.TransportEndpointValues

/-!
# Two bounded honest endpoint values from the original transport hypotheses

The first endpoint stays a positive uniform distance from every shared
finite value. Both endpoint values are readings of analytic normal forms
and hence represent the actual shifted meromorphic germs.
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

set_option autoImplicit false

private theorem endpoint_fixed_gap (a : Fin 3 → ℂ) (j : Fin 3) (x : ℂ) (c : ℝ)
    (hlower : c ≤ ‖x‖)
    (hupper : ‖x‖ ≤ min ‖a (j + 1) - a j‖ ‖a (j + 2) - a j‖ / 2) :
    ∀ i : Fin 3,
      min c (min ‖a (j + 1) - a j‖ ‖a (j + 2) - a j‖ / 2) ≤ ‖x + a j - a i‖ := by
  intro i
  let d : ℝ := min ‖a (j + 1) - a j‖ ‖a (j + 2) - a j‖
  have hi : i = j ∨ i = j + 1 ∨ i = j + 2 := by
    fin_cases j <;> fin_cases i <;> decide
  rcases hi with hi | hi | hi
  · rw [hi, add_sub_cancel_right]
    exact (min_le_left _ _).trans hlower
  · rw [hi]
    have ht := norm_sub_le x (x + a j - a (j + 1))
    have he : x - (x + a j - a (j + 1)) = a (j + 1) - a j := by ring
    rw [he] at ht
    have hmin : d ≤ ‖a (j + 1) - a j‖ := min_le_left _ _
    have hγ : min c (d / 2) ≤ d / 2 := min_le_right _ _
    linarith
  · rw [hi]
    have ht := norm_sub_le x (x + a j - a (j + 2))
    have he : x - (x + a j - a (j + 2)) = a (j + 2) - a j := by ring
    rw [he] at ht
    have hmin : d ≤ ‖a (j + 2) - a j‖ := min_le_right _ _
    have hγ : min c (d / 2) ≤ d / 2 := min_le_right _ _
    linarith

theorem transport_tracked_endpoints
    {Ω : ℕ → Set ℂ} (hΩ : ∀ n, IsOpen (Ω n))
    {F G u v : ℕ → ℂ → ℂ} {a : Fin 3 → ℂ} {j : Fin 3}
    (pair : ∀ n, NormalizedPair (Ω n) (F n) (G n) a)
    {ε : ℕ → ℝ} (hεpos : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    {A B : ℂ} (hA : A ≠ 0) (hB : B ≠ 0)
    (hu : ∀ n, DifferentiableOn ℂ (u n) (Ω n))
    (hv : ∀ n, DifferentiableOn ℂ (v n) (Ω n))
    (hU : ∀ n, auxU a (F n) (G n) =ᶠ[codiscreteWithin (Ω n)] u n)
    (hV : ∀ n, auxV a (F n) (G n) =ᶠ[codiscreteWithin (Ω n)] v n)
    (hrect : ∀ R > 0, ∀ᶠ n in atTop, transportRect (ε n) R ⊆ Ω n)
    (hprofU : ∀ R > 0, ∀ η > 0, ∀ᶠ n in atTop, ∀ z ∈ transportRect (ε n) R,
      ‖u n z / (ε n * A * Complex.exp (z / 2)) - 1‖ ≤ η)
    (hprofV : ∀ R > 0, ∀ η > 0, ∀ᶠ n in atTop, ∀ z ∈ transportRect (ε n) R,
      ‖v n z / (ε n * B * Complex.exp (-z / 2)) - 1‖ ≤ η)
    (hconv : TransportTangentConvergence F G ε (a j)
      (A * amplitudeRemainder a j (a j))) :
    ∃ s : ℝ, 0 < s ∧ ∃ vF vG : ℕ → ℂ, ∃ MF MG γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop,
      sphereGermValue (fun z => F n (((2 * Real.log (s / ε n) : ℝ) : ℂ) + z)) 0 =
        (vF n : OnePoint ℂ) ∧
      sphereGermValue (fun z => G n (((2 * Real.log (s / ε n) : ℝ) : ℂ) + z)) 0 =
        (vG n : OnePoint ℂ) ∧
      ‖vF n‖ ≤ MF ∧ ‖vG n‖ ≤ MG ∧ ∀ i : Fin 3, γ ≤ ‖vF n - a i‖ := by
  let a₂ := a (j + 1) - a j
  let a₃ := a (j + 2) - a j
  let α := A * (a₂ * a₃)
  let d : ℝ := min ‖a₂‖ ‖a₃‖
  have hj1 : j + 1 ≠ j := by fin_cases j <;> decide
  have hj2 : j + 2 ≠ j := by fin_cases j <;> decide
  have hd1 : 0 < ‖a₂‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr ((pair 0).injective.ne hj1))
  have hd2 : 0 < ‖a₃‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr ((pair 0).injective.ne hj2))
  have hd : 0 < d := lt_min hd1 hd2
  have hα : α ≠ 0 := mul_ne_zero hA (mul_ne_zero
    (norm_pos_iff.mp hd1) (norm_pos_iff.mp hd2))
  have hαpos : 0 < ‖α‖ := norm_pos_iff.mpr hα
  have hsmax : 0 < d / (16 * ‖α‖) := by positivity
  obtain ⟨r₀, s, start, hr₀, hrsmall, hs, hs1, hscap, hstart, htrack⟩ :=
    transport_finite_tracking hΩ pair hεpos hε hA hB hu hv hU hV hrect
      hprofU hprofV hconv hsmax
  have hstart0 : 0 ≤ start := by linarith
  have hsu : 6 * s * ‖α‖ ≤ d / 2 := by
    have hc : s * (16 * ‖α‖) ≤ d :=
      (le_div_iff₀ (by positivity : 0 < 16 * ‖α‖)).mp hscap
    nlinarith [mul_pos hs hαpos]
  let L : ℕ → ℂ := fun n => ((2 * Real.log (s / ε n) : ℝ) : ℂ)
  let vF : ℕ → ℂ := fun n => transportNormalF (Ω n) (F n) (a j) (L n) + a j
  let vG : ℕ → ℂ := fun n => transportNormalF (Ω n) (G n) (a j) (L n) + a j
  let γ : ℝ := min (s * ‖α‖ / 2) (d / 2)
  have hγ : 0 < γ := lt_min (by positivity) (by positivity)
  refine ⟨s, hs, vF, vG, 6 * s * ‖α‖ + ‖a j‖,
    3 * s * ‖α‖ + ‖a j‖, γ, hγ, ?_⟩
  filter_upwards [htrack, hrect 1 (by norm_num)] with n hn hrectn
  have ht : 2 * Real.log (s / ε n) ∈ Icc start (2 * Real.log (s / ε n)) :=
    ⟨hn.1, le_rfl⟩
  have hL : L n ∈ Ω n := hrectn
    (transport_real_segment_mem_rect (hεpos n) hs hs1 hstart0 ht)
  have hp := hn.2 _ ht
  have hFvalue := hp.2.2.2.2.1
  have hGvalue := hp.2.2.2.2.2.1
  rw [transportScale_endpoint (hεpos n) hs] at hFvalue hGvalue
  have hc := transport_endpoint_coordinate_bounds hs.le hs1 hrsmall hp.2.2.1 hp.2.2.2.1
  have hFlower : s * ‖α‖ / 2 ≤ ‖transportNormalF (Ω n) (F n) (a j) (L n)‖ := by
    rw [hFvalue]
    exact hc.1
  have hFupper : ‖transportNormalF (Ω n) (F n) (a j) (L n)‖ ≤ 6 * s * ‖α‖ := by
    rw [hFvalue]
    exact hc.2.1
  have hGupper : ‖transportNormalF (Ω n) (G n) (a j) (L n)‖ ≤ 3 * s * ‖α‖ := by
    rw [hGvalue]
    exact hc.2.2
  refine ⟨transport_shifted_normal_form_honest_value (pair n).nonconst_f.1 hL hp.1,
    transport_shifted_normal_form_honest_value (pair n).nonconst_g.1 hL hp.2.1,
    (norm_add_le _ _).trans (add_le_add hFupper le_rfl),
    (norm_add_le _ _).trans (add_le_add hGupper le_rfl), ?_⟩
  exact endpoint_fixed_gap a j _ (s * ‖α‖ / 2) hFlower (hFupper.trans hsu)

end ThreeIM
