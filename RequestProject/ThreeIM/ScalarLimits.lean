module

public import RequestProject.ThreeIM.Scalar
public import RequestProject.ThreeIM.AuxiliaryLimits

/-!
# Limits of the scalar differential equation

Two applications of holomorphic derivative convergence pass the scalar
equation to an autonomous equation on an ordinary chart. Meromorphic
identity extends it to the plane, where the existing autonomous scalar
classification excludes a nonconstant limit, including the degenerate
case where the limiting coefficient of the second derivative is zero.
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

set_option autoImplicit false

theorem scalar_equation_limit_on_chart {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {H C D B : ℕ → ℂ → ℂ} {h : ℂ → ℂ} {c b : ℂ}
    (hH : ∀ᶠ n in atTop, DifferentiableOn ℂ (H n) Ω)
    (hHconv : TendstoLocallyUniformlyOn H h atTop Ω)
    (hCconv : TendstoLocallyUniformlyOn C (fun _ => c) atTop Ω)
    (hDconv : TendstoLocallyUniformlyOn D (fun _ => 0) atTop Ω)
    (hBconv : TendstoLocallyUniformlyOn B (fun _ => b) atTop Ω)
    (heq : ∀ᶠ n in atTop, ∀ z ∈ Ω,
      C n z * H n z * (H n z - 1) * deriv (deriv (H n)) z
      - D n z * H n z * (H n z - 1) * deriv (H n) z
      - (C n z * (3 * H n z - 1) + B n z) * deriv (H n) z ^ 2 = 0) :
    ∀ z ∈ Ω, c * h z * (h z - 1) * deriv (deriv h) z
      - (c * (3 * h z - 1) + b) * deriv h z ^ 2 = 0 := by
  have hHd : ∀ᶠ n in atTop, DifferentiableOn ℂ (deriv (H n)) Ω :=
    hH.mono fun n hn => (hn.analyticOnNhd hΩ).deriv.differentiableOn
  have hdconv := hHconv.deriv hH hΩ
  have hddconv := hdconv.deriv hHd hΩ
  intro z hz
  have hy := hHconv.tendsto_at hz
  have hy' := hdconv.tendsto_at hz
  have hy'' := hddconv.tendsto_at hz
  have hc := hCconv.tendsto_at hz
  have hd := hDconv.tendsto_at hz
  have hb := hBconv.tendsto_at hz
  have hleft := (((hc.mul hy).mul (hy.sub_const 1)).mul hy'').sub
    (((hd.mul hy).mul (hy.sub_const 1)).mul hy')
  have hright := ((hc.mul (hy.const_mul 3 |>.sub_const 1)).add hb).mul (hy'.pow 2)
  have hlimit := hleft.sub hright
  have hzero := tendsto_nhds_unique_of_eventuallyEq hlimit tendsto_const_nhds
    (heq.mono fun n hn => hn z hz)
  simpa only [zero_mul, sub_zero] using hzero

theorem scalar_equation_global_of_local {h : ℂ → ℂ} (hh : Meromorphic h)
    (b c : ℂ) {Ω : Set ℂ} (hΩ : IsOpen Ω) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω)
    (heq : ∀ z ∈ Ω, c * h z * (h z - 1) * deriv (deriv h) z
      - (c * (3 * h z - 1) + b) * deriv h z ^ 2 = 0) :
    ∀ᶠ z in codiscrete ℂ, c * h z * (h z - 1) * deriv (deriv h) z
      - (c * (3 * h z - 1) + b) * deriv h z ^ 2 = 0 := by
  have hm : Meromorphic (fun z => c * h z * (h z - 1) * deriv (deriv h) z
      - (c * (3 * h z - 1) + b) * deriv h z ^ 2) := fun z => by
    have := hh z
    have := (hh z).deriv
    have := (hh z).deriv.deriv
    fun_prop
  have hnear : (fun z => c * h z * (h z - 1) * deriv (deriv h) z
      - (c * (3 * h z - 1) + b) * deriv h z ^ 2) =ᶠ[𝓝[≠] z₀] (fun _ => 0) := by
    exact (Filter.eventually_of_mem (hΩ.mem_nhds hz₀) heq).filter_mono
      nhdsWithin_le_nhds
  exact auxiliary_globalize_identity hm (fun z => MeromorphicAt.const 0 z) hnear

theorem nonconstant_scalar_limit_impossible {h : ℂ → ℂ}
    (hh : IsNonconstMeroOn h univ) (b c : ℂ) (hb : b ≠ 0)
    (heq : ∀ᶠ z in codiscrete ℂ, c * h z * (h z - 1) * deriv (deriv h) z
      - (c * (3 * h z - 1) + b) * deriv h z ^ 2 = 0) : False := by
  by_cases hc : c = 0
  · have hder : deriv h =ᶠ[codiscrete ℂ] (fun _ => 0) := by
      filter_upwards [heq] with z hz
      have hp : b * deriv h z ^ 2 = 0 := by
        simpa only [hc, zero_mul, zero_add, zero_sub, neg_eq_zero] using hz
      have hs : deriv h z * deriv h z = 0 := by
        simpa only [pow_two] using (mul_eq_zero.mp hp).resolve_left hb
      exact (mul_eq_zero.mp hs).elim id id
    have ht : meromorphicOrderAt (deriv h) 0 = ⊤ :=
      meromorphicOrderAt_eq_top_iff.mpr
        (auxiliary_local_of_codiscreteWithin isOpen_univ hder (mem_univ 0))
    exact (order_deriv_of_nonconst hh (mem_univ 0)).1 ht
  · have hscalar : ∀ᶠ z in codiscrete ℂ,
        h z * (h z - 1) * deriv (deriv h) z
          - (3 * h z - 1 + b / c) * deriv h z ^ 2 = 0 := by
      filter_upwards [heq] with z hz
      have halg : c * (h z * (h z - 1) * deriv (deriv h) z
          - (3 * h z - 1 + b / c) * deriv h z ^ 2) =
          c * h z * (h z - 1) * deriv (deriv h) z
          - (c * (3 * h z - 1) + b) * deriv h z ^ 2 := by
        field_simp [hc]
      exact (mul_eq_zero.mp (halg.trans hz)).resolve_left hc
    obtain ⟨k, hk⟩ := autonomous_scalar_const_of_eq (fun z => hh.1 z (mem_univ z))
      (b / c) hscalar
    have hlocal := auxiliary_local_of_codiscreteWithin isOpen_univ hk (mem_univ (0 : ℂ))
    exact hh.2 0 (mem_univ 0) k (meromorphicOrderAt_eq_top_iff.mpr
      (hlocal.mono fun z hz => sub_eq_zero.mpr hz))

end ThreeIM
