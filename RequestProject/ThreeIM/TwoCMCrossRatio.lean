module

public import RequestProject.ThreeIM.TwoCMOpposite

/-!
# Orders and powers of cross-ratios in the opposite-sign case
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

noncomputable def twoCMCrossRatio (b c : ℂ) (h : ℂ → ℂ) : ℂ → ℂ :=
  fun z => (h z - b) / (h z - c)

theorem twoCM_meromorphic_crossRatio {h : ℂ → ℂ}
    (hh : IsNonconstMeroOn h univ) (b c : ℂ) :
    Meromorphic (twoCMCrossRatio b c h) := fun z =>
  ((hh.meromorphic z).sub (MeromorphicAt.const b z)).div
    ((hh.meromorphic z).sub (MeromorphicAt.const c z))

theorem twoCM_crossRatio_order_ne_top {h : ℂ → ℂ}
    (hh : IsNonconstMeroOn h univ) (b c z : ℂ) :
    meromorphicOrderAt (twoCMCrossRatio b c h) z ≠ ⊤ := by
  apply (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
    (twoCM_meromorphic_crossRatio hh b c z)).2
  filter_upwards [codiscrete_iff_nhdsNE.1 (hh.eventually_ne b) z,
    codiscrete_iff_nhdsNE.1 (hh.eventually_ne c) z] with w hb hc
  exact div_ne_zero (sub_ne_zero.2 hb) (sub_ne_zero.2 hc)

theorem twoCM_logDeriv_crossRatio {h : ℂ → ℂ}
    (hh : IsNonconstMeroOn h univ) (b c : ℂ) :
    (fun z => deriv (twoCMCrossRatio b c h) z / twoCMCrossRatio b c h z)
      =ᶠ[codiscrete ℂ] (fun z => (b - c) * twoCMQuadDerivative b c h z) := by
  filter_upwards [eventually_analyticAt_of_meromorphic hh.meromorphic,
    hh.eventually_ne b, hh.eventually_ne c] with z hz hb hc
  change logDeriv (fun w => (h w - b) / (h w - c)) z = _
  rw [logDeriv_fun_div (f := fun w => h w - b) (g := fun w => h w - c) z (sub_ne_zero.2 hb) (sub_ne_zero.2 hc)
    (hz.differentiableAt.sub_const b) (hz.differentiableAt.sub_const c)]
  simp only [logDeriv_apply, deriv_sub_const, twoCMQuadDerivative]
  field_simp [sub_ne_zero.2 hb, sub_ne_zero.2 hc]
  ring

/-- Equality of weighted logarithmic derivatives equates their Laurent
residues at every point. The weights may vanish. -/
theorem twoCM_order_relation_of_log_deriv_eq {U V : ℂ → ℂ}
    (hU : Meromorphic U) (hV : Meromorphic V)
    (hUf : ∀ z, meromorphicOrderAt U z ≠ ⊤) (hVf : ∀ z, meromorphicOrderAt V z ≠ ⊤)
    (p q : ℂ)
    (hlog : (fun z => p * (deriv U z / U z)) =ᶠ[codiscrete ℂ]
      (fun z => q * (deriv V z / V z))) (z : ℂ) :
    p * (ordZ U z : ℂ) = q * (ordZ V z : ℂ) := by
  obtain ⟨E, hE, he⟩ := logDeriv_local_ordZ (hU z) (hUf z)
  obtain ⟨F, hF, hf⟩ := logDeriv_local_ordZ (hV z) (hVf z)
  have heq : ∀ᶠ w in 𝓝[≠] z, (0 : ℂ) =
      (p * (ordZ U z : ℂ) - q * (ordZ V z : ℂ)) / (w - z) +
        (p * E w - q * F w) := by
    filter_upwards [he, hf, codiscrete_iff_nhdsNE.1 hlog z] with w he hf hl
    rw [he, hf] at hl
    linear_combination -hl
  have hres : p * (ordZ U z : ℂ) - q * (ordZ V z : ℂ) = 0 := by
    by_contra hn
    have ho := (order_of_local_form
      ((analyticAt_const.mul hE).sub (analyticAt_const.mul hF)) heq).2.2 hn
    have ht : (⊤ : WithTop ℤ) = ((-1 : ℤ) : WithTop ℤ) := by
      simpa [meromorphicOrderAt_const] using ho
    exact WithTop.coe_ne_top ht.symm
  exact sub_eq_zero.1 hres

theorem twoCM_crossRatio_order_at_first {h : ℂ → ℂ}
    (hh : IsNonconstMeroOn h univ) {b c z : ℂ} (hbc : b ≠ c)
    (hpos : 0 < mult h (b : Sphere) z) :
    ordZ (twoCMCrossRatio b c h) z = (mult h (b : Sphere) z : ℤ) := by
  have hb := order_sub_eq_mult hpos
  have hc : meromorphicOrderAt (fun w => h w - c) z = 0 :=
    order_sub_const_eq_zero_of_pos (hh.meromorphic z) hbc
      (by rw [hb]; exact_mod_cast hpos)
  have heq : twoCMCrossRatio b c h = (fun w => h w - b) * (fun w => h w - c)⁻¹ := by
    ext w; simp [twoCMCrossRatio, div_eq_mul_inv]
  have hbm : MeromorphicAt (fun w => h w - b) z :=
    (hh.meromorphic z).sub (MeromorphicAt.const b z)
  have hcm : MeromorphicAt (fun w => h w - c) z :=
    (hh.meromorphic z).sub (MeromorphicAt.const c z)
  unfold ordZ
  rw [heq, meromorphicOrderAt_mul (f := fun w => h w - b)
    (g := (fun w => h w - c)⁻¹) hbm hcm.inv,
    meromorphicOrderAt_inv, hb, hc]
  simp

theorem twoCM_crossRatio_order_at_second {h : ℂ → ℂ}
    (hh : IsNonconstMeroOn h univ) {b c z : ℂ} (hbc : b ≠ c)
    (hpos : 0 < mult h (c : Sphere) z) :
    ordZ (twoCMCrossRatio b c h) z = -(mult h (c : Sphere) z : ℤ) := by
  have hc := order_sub_eq_mult hpos
  have hb : meromorphicOrderAt (fun w => h w - b) z = 0 :=
    order_sub_const_eq_zero_of_pos (hh.meromorphic z) hbc.symm
      (by rw [hc]; exact_mod_cast hpos)
  have heq : twoCMCrossRatio b c h = (fun w => h w - b) * (fun w => h w - c)⁻¹ := by
    ext w; simp [twoCMCrossRatio, div_eq_mul_inv]
  have hbm : MeromorphicAt (fun w => h w - b) z :=
    (hh.meromorphic z).sub (MeromorphicAt.const b z)
  have hcm : MeromorphicAt (fun w => h w - c) z :=
    (hh.meromorphic z).sub (MeromorphicAt.const c z)
  unfold ordZ
  rw [heq, meromorphicOrderAt_mul (f := fun w => h w - b)
    (g := (fun w => h w - c)⁻¹) hbm hcm.inv,
    meromorphicOrderAt_inv, hb, hc]
  simp

end ThreeIM
