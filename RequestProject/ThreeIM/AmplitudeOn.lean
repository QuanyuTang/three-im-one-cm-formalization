module

public import RequestProject.ThreeIM.Tangent
public import RequestProject.ThreeIM.Normality

/-!
# The analytic amplitude quotient on an open domain

This is the local-domain form of `amplitude_quotient_entire`. The finite
order of the difference comes from the distinctness of an actual normalized
pair. Analytic normal form removes its apparent quotient singularities.
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

set_option autoImplicit false

theorem exists_analytic_amplitude_quotient {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {X D a : ℂ → ℂ} (hX : DifferentiableOn ℂ X Ω)
    (hD : DifferentiableOn ℂ D Ω) (ha : DifferentiableOn ℂ a Ω)
    (ha0 : ∀ z ∈ Ω, a z ≠ 0)
    (hDfinite : ∀ z ∈ Ω, meromorphicOrderAt D z ≠ ⊤)
    (heq : ∀ z ∈ Ω, D z * deriv X z = a z * X z) :
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H Ω ∧ ∀ z ∈ Ω, X z = D z * H z := by
  let Q : ℂ → ℂ := fun z => X z / D z
  have hXm := hX.analyticOnNhd hΩ
  have hDm := hD.analyticOnNhd hΩ
  have ham := ha.analyticOnNhd hΩ
  have hQm : MeromorphicOn Q Ω := fun z hz =>
    (hXm z hz).meromorphicAt.div (hDm z hz).meromorphicAt
  have hnonneg (z : ℂ) (hz : z ∈ Ω) : 0 ≤ meromorphicOrderAt Q z := by
    obtain ⟨d, hd⟩ := int_of_order_ne_top (hDfinite z hz)
    have hQe : Q = X * D⁻¹ := by ext w; simp [Q, div_eq_mul_inv]
    rw [hQe, meromorphicOrderAt_mul (hXm z hz).meromorphicAt (hDm z hz).meromorphicAt.inv,
      meromorphicOrderAt_inv, hd]
    by_cases hXt : meromorphicOrderAt X z = ⊤
    · rw [hXt]; simp
    obtain ⟨p, hp⟩ := int_of_order_ne_top hXt
    rw [hp]
    by_cases hDz : D z = 0
    · have hXz : X z = 0 := by
        have hh := heq z hz
        rw [hDz, zero_mul] at hh
        exact (mul_eq_zero.mp hh.symm).resolve_left (ha0 z hz)
      have hp1 := order_pos_of_analyticAt (hXm z hz) hXz hp
      have hX' : meromorphicOrderAt (deriv X) z = ((p - 1 : ℤ) : WithTop ℤ) :=
        order_deriv_of_order_eq (a := 0) (hXm z hz).meromorphicAt
          (by omega) (by simpa using hp)
      have heqNear : (fun w => D w * deriv X w) =ᶠ[𝓝[≠] z] (fun w => a w * X w) :=
        (Filter.eventually_of_mem (hΩ.mem_nhds hz) heq).filter_mono nhdsWithin_le_nhds
      have h1 := meromorphicOrderAt_congr heqNear
      change meromorphicOrderAt (D * deriv X) z = meromorphicOrderAt (a * X) z at h1
      rw [meromorphicOrderAt_mul (hDm z hz).meromorphicAt (hXm z hz).meromorphicAt.deriv,
        meromorphicOrderAt_mul (ham z hz).meromorphicAt (hXm z hz).meromorphicAt,
        hd, hX', order_eq_zero_of_analyticAt (ham z hz) (ha0 z hz), hp] at h1
      have h2 : ((d + (p - 1) : ℤ) : WithTop ℤ) = ((0 + p : ℤ) : WithTop ℤ) := by
        push_cast
        exact h1
      have := WithTop.coe_injective h2
      exact_mod_cast (by omega : (0 : ℤ) ≤ p + -d)
    · have hd0 : d = 0 := by
        have hh := order_eq_zero_of_analyticAt (hDm z hz) hDz
        rw [hd] at hh
        exact_mod_cast hh
      have hp0 : 0 ≤ p := by
        have hh := (hXm z hz).meromorphicOrderAt_nonneg
        rw [hp] at hh
        exact_mod_cast hh
      exact_mod_cast (by omega : (0 : ℤ) ≤ p + -d)
  let H : ℂ → ℂ := toMeromorphicNFOn Q Ω
  have hrep (z : ℂ) (hz : z ∈ Ω) : H =ᶠ[𝓝[≠] z] Q :=
    hQm.toMeromorphicNFOn_eq_self_on_nhdsNE hz
  have hHa : AnalyticOnNhd ℂ H Ω := by
    intro z hz
    apply (meromorphicNFOn_toMeromorphicNFOn Q Ω hz).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [meromorphicOrderAt_congr (hrep z hz)]
    exact hnonneg z hz
  refine ⟨H, hHa.differentiableOn, fun z hz => ?_⟩
  have hDne : ∀ᶠ w in 𝓝[≠] z, D w ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hDm z hz).meromorphicAt).mp
      (hDfinite z hz)
  have hc := (hXm z hz).continuousAt.sub ((hDm z hz).continuousAt.mul (hHa z hz).continuousAt)
  have hz0 := eq_zero_of_nhdsNE hc (by
    filter_upwards [hDne, hrep z hz] with w hw hh
    change X w - D w * H w = 0
    rw [hh]
    dsimp only [Q]
    field_simp
    ring)
  exact sub_eq_zero.mp hz0

theorem amplitude_quotient_eq_one_at_simple_marked {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {X Y H : ℂ → ℂ} (hX : DifferentiableOn ℂ X Ω)
    (hY : DifferentiableOn ℂ Y Ω) (hH : DifferentiableOn ℂ H Ω)
    (heq : ∀ z ∈ Ω, X z = (X z - Y z) * H z)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) (hX0 : X z₀ = 0) (hY0 : Y z₀ = 0)
    (hXd : deriv X z₀ ≠ 0) (hYd : deriv Y z₀ = 0) : H z₀ = 1 := by
  have he : X =ᶠ[𝓝 z₀] (fun z => (X z - Y z) * H z) :=
    Filter.eventually_of_mem (hΩ.mem_nhds hz₀) heq
  have hx := hX.differentiableAt (hΩ.mem_nhds hz₀)
  have hy := hY.differentiableAt (hΩ.mem_nhds hz₀)
  have hh := hH.differentiableAt (hΩ.mem_nhds hz₀)
  have hd := he.deriv_eq
  rw [deriv_fun_mul (c := fun z => X z - Y z) (d := H) (hx.sub hy) hh,
    deriv_fun_sub hx hy, hYd, hX0, hY0] at hd
  simp only [sub_zero, sub_self, zero_mul, add_zero] at hd
  exact mul_left_cancel₀ hXd (by simpa only [mul_one] using hd.symm)

theorem exists_scalar_amplitude_quotient {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {X Y a b : ℂ → ℂ} (hX : DifferentiableOn ℂ X Ω)
    (hY : DifferentiableOn ℂ Y Ω) (ha : DifferentiableOn ℂ a Ω)
    (hb : DifferentiableOn ℂ b Ω) (ha0 : ∀ z ∈ Ω, a z ≠ 0)
    (hDfinite : ∀ z ∈ Ω, meromorphicOrderAt (fun w => X w - Y w) z ≠ ⊤)
    (hXeq : ∀ z ∈ Ω, (X z - Y z) * deriv X z = a z * X z)
    (hYeq : ∀ z ∈ Ω, (X z - Y z) * deriv Y z = b z * Y z) :
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H Ω ∧
      (∀ z ∈ Ω, X z = (X z - Y z) * H z) ∧
      (∀ z ∈ Ω, Y z = (X z - Y z) * (H z - 1)) ∧
      (∀ z ∈ Ω, deriv (fun w => X w - Y w) z = (a z - b z) * H z + b z) ∧
      (∀ z ∈ Ω, (a z - b z) * H z * (H z - 1) * deriv (deriv H) z
        - deriv (fun w => a w - b w) z * H z * (H z - 1) * deriv H z
        - ((a z - b z) * (3 * H z - 1) + b z) * deriv H z ^ 2 = 0) := by
  obtain ⟨H, hH, hHX⟩ := exists_analytic_amplitude_quotient hΩ hX (hX.sub hY) ha ha0 hDfinite hXeq
  change ∀ z ∈ Ω, X z = (X z - Y z) * H z at hHX
  have hHY (z : ℂ) (hz : z ∈ Ω) : Y z = (X z - Y z) * (H z - 1) := by
    linear_combination hHX z hz
  have hzeros (z : ℂ) (hz : z ∈ Ω) : ∃ᶠ w in 𝓝[≠] z, X w - Y w ≠ 0 :=
    ((meromorphicOrderAt_ne_top_iff_eventually_ne_zero
      (((hX.sub hY).analyticOnNhd hΩ z hz).meromorphicAt)).mp (hDfinite z hz)).frequently
  have hXeq' (z : ℂ) (hz : z ∈ Ω) :
      (X z - Y z) * deriv (fun w => (X w - Y w) * H w) z = a z * ((X z - Y z) * H z) := by
    have he : X =ᶠ[𝓝 z] (fun w => (X w - Y w) * H w) :=
      Filter.eventually_of_mem (hΩ.mem_nhds hz) hHX
    rw [← he.deriv_eq, ← hHX z hz]
    exact hXeq z hz
  have hYeq' (z : ℂ) (hz : z ∈ Ω) :
      (X z - Y z) * deriv (fun w => (X w - Y w) * (H w - 1)) z = b z * ((X z - Y z) * (H z - 1)) := by
    have he : Y =ᶠ[𝓝 z] (fun w => (X w - Y w) * (H w - 1)) :=
      Filter.eventually_of_mem (hΩ.mem_nhds hz) hHY
    rw [← he.deriv_eq, ← hHY z hz]
    exact hYeq z hz
  have hscalar := amplitude_elimination hΩ ha hb (hX.sub hY) hH hzeros hXeq' hYeq'
  exact ⟨H, hH, hHX, hHY, hscalar.1, hscalar.2.2⟩

end ThreeIM
