module

public import RequestProject.ThreeIM.TwoCMMixedLocal

/-!
# Removing poles from the reciprocal difference in the zero-scalar case

This uses only the actual quartic quotient identity. In particular, it does
not assume that a logarithmic auxiliary function vanishes at simple zeros.
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

noncomputable def twoCMReciprocalDifference (a k : ℂ) (f g : ℂ → ℂ) : ℂ → ℂ :=
  fun z => (f z - a)⁻¹ - k * (g z - a)⁻¹

theorem twoCM_meromorphic_reciprocalDifference {f g : ℂ → ℂ}
    (hf : Meromorphic f) (hg : Meromorphic g) (a k : ℂ) :
    Meromorphic (twoCMReciprocalDifference a k f g) := fun z =>
  ((hf z).sub (MeromorphicAt.const a z)).inv.sub
    ((MeromorphicAt.const k z).mul ((hg z).sub (MeromorphicAt.const a z)).inv)

theorem twoCM_quartic_partial_fraction {h : ℂ → ℂ} {a b c z : ℂ}
    (hc : 2 * a - b - c = 0) (ha : h z ≠ a) (hb : h z ≠ b) (hcc : h z ≠ c) :
    deriv h z / (h z - a) ^ 2 = twoCMQuadDerivative b c h z +
      ((a - b) * (a - c)) * twoCMQuarticDerivative a b c h z := by
  have hec : c = 2 * a - b := by linear_combination -hc
  simp only [twoCMQuadDerivative, twoCMQuarticDerivative]
  field_simp [sub_ne_zero.2 ha, sub_ne_zero.2 hb, sub_ne_zero.2 hcc]
  rw [hec]
  ring

theorem twoCM_deriv_reciprocalDifference_of_quartic_ratio {f g : ℂ → ℂ}
    (hf : IsNonconstMeroOn f univ) (hg : IsNonconstMeroOn g univ)
    {a b c k : ℂ} (hc : 2 * a - b - c = 0)
    (hquad : twoCMQuarticDerivative a b c f =ᶠ[codiscrete ℂ]
      (fun z => k * twoCMQuarticDerivative a b c g z)) :
    deriv (twoCMReciprocalDifference a k f g) =ᶠ[codiscrete ℂ]
      (fun z => -twoCMQuadDerivative b c f z + k * twoCMQuadDerivative b c g z) := by
  filter_upwards [eventually_analyticAt_of_meromorphic hf.meromorphic,
    eventually_analyticAt_of_meromorphic hg.meromorphic,
    hf.eventually_ne a, hf.eventually_ne b, hf.eventually_ne c,
    hg.eventually_ne a, hg.eventually_ne b, hg.eventually_ne c, hquad]
    with z hfa hga hfa0 hfb hfc hga0 hgb hgc hq
  have hfd := hfa.differentiableAt.sub_const a
  have hgd := hga.differentiableAt.sub_const a
  have hfInv : DifferentiableAt ℂ (fun w => (f w - a)⁻¹) z := hfd.inv (sub_ne_zero.2 hfa0)
  have hgInv : DifferentiableAt ℂ (fun w => (g w - a)⁻¹) z := hgd.inv (sub_ne_zero.2 hga0)
  change deriv (fun w => (f w - a)⁻¹ - k * (g w - a)⁻¹) z = _
  rw [deriv_fun_sub hfInv (hgInv.const_mul k), deriv_const_mul_field,
    deriv_fun_inv'' hfd (sub_ne_zero.2 hfa0), deriv_fun_inv'' hgd (sub_ne_zero.2 hga0),
    deriv_sub_const, deriv_sub_const]
  have hpf := twoCM_quartic_partial_fraction (h := f) hc hfa0 hfb hfc
  have hpg := twoCM_quartic_partial_fraction (h := g) hc hga0 hgb hgc
  linear_combination -hpf + k * hpg - ((a - b) * (a - c)) * hq

theorem twoCM_order_nonneg_of_deriv_order_nonneg {H : ℂ → ℂ} {z : ℂ}
    (hH : MeromorphicAt H z) (hder : 0 ≤ meromorphicOrderAt (deriv H) z) :
    0 ≤ meromorphicOrderAt H z := by
  by_contra hn
  have hneg : meromorphicOrderAt H z < 0 := lt_of_not_ge hn
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hneg)
  have hnneg : n < 0 := by rw [← hn] at hneg; exact_mod_cast hneg
  have hd : meromorphicOrderAt (deriv H) z = ((n - 1 : ℤ) : WithTop ℤ) :=
    order_deriv_of_order_eq hH (a := 0) (by omega) (by simpa only [sub_zero] using hn.symm)
  rw [hd] at hder
  have : (0 : ℤ) ≤ n - 1 := by exact_mod_cast hder
  omega

theorem twoCM_quadDerivative_order_nonneg_at_other {h : ℂ → ℂ}
    (hh : IsNonconstMeroOn h univ) {a b c z : ℂ} (hab : a ≠ b) (hac : a ≠ c)
    (hpos : 0 < mult h (a : Sphere) z) :
    0 ≤ meromorphicOrderAt (twoCMQuadDerivative b c h) z := by
  have hfm := hh.meromorphic z
  have hbm : MeromorphicAt (fun w => h w - b) z := hfm.sub (MeromorphicAt.const b z)
  have hcm : MeromorphicAt (fun w => h w - c) z := hfm.sub (MeromorphicAt.const c z)
  have hapos : 0 < meromorphicOrderAt (fun w => h w - a) z := by
    rw [order_sub_eq_mult hpos]
    exact_mod_cast hpos
  have hb := order_sub_const_eq_zero_of_pos hfm hab hapos
  have hc := order_sub_const_eq_zero_of_pos hfm hac hapos
  have hd := order_deriv_of_order_eq hfm (a := a) (by omega : (mult h (a : Sphere) z : ℤ) ≠ 0)
    (order_sub_eq_mult hpos)
  have heq : twoCMQuadDerivative b c h = deriv h * ((fun w => h w - b) * (fun w => h w - c))⁻¹ := by
    ext w
    simp [twoCMQuadDerivative, div_eq_mul_inv]
  rw [heq, meromorphicOrderAt_mul hfm.deriv (hbm.mul hcm).inv,
    meromorphicOrderAt_inv, meromorphicOrderAt_mul hbm hcm, hb, hc,
    zero_add, neg_zero, add_zero, hd]
  exact_mod_cast (by omega : (0 : ℤ) ≤ (mult h (a : Sphere) z : ℤ) - 1)

private theorem mixed_order_add_nonneg {F G : ℂ → ℂ} {z : ℂ}
    (hF : MeromorphicAt F z) (hG : MeromorphicAt G z)
    (hf : 0 ≤ meromorphicOrderAt F z) (hg : 0 ≤ meromorphicOrderAt G z) :
    0 ≤ meromorphicOrderAt (F + G) z :=
  (le_min hf hg).trans (meromorphicOrderAt_add hF hG)

private theorem mixed_order_const_mul_nonneg {F : ℂ → ℂ} {z : ℂ}
    (hF : MeromorphicAt F z) (hf : 0 ≤ meromorphicOrderAt F z) (c : ℂ) :
    0 ≤ meromorphicOrderAt (fun w => c * F w) z := by
  change 0 ≤ meromorphicOrderAt ((fun _ => c) * F) z
  rw [meromorphicOrderAt_mul (MeromorphicAt.const c z) hF]
  exact add_nonneg (order_const_nonneg c) hf

theorem twoCM_reciprocalDifference_order_nonneg {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair univ f g a) (j : Fin 3)
    (hcm : SharesCMOn univ f g (a j : Sphere)) (hc : cAux a j = 0) {k : ℂ}
    (hquad : twoCMQuarticDerivative (a j) (a (j + 1)) (a (j + 2)) f =ᶠ[codiscrete ℂ]
      (fun z => k * twoCMQuarticDerivative (a j) (a (j + 1)) (a (j + 2)) g z)) (z : ℂ) :
    0 ≤ meromorphicOrderAt (twoCMReciprocalDifference (a j) k f g) z := by
  have hfm := hp.nonconst_f.meromorphic z
  have hgm := hp.nonconst_g.meromorphic z
  have hH := twoCM_meromorphic_reciprocalDifference hp.nonconst_f.meromorphic hp.nonconst_g.meromorphic (a j) k
  by_cases hpos : 0 < mult f (a j : Sphere) z
  · have hposg : 0 < mult g (a j : Sphere) z := by rwa [← hcm z (mem_univ z)]
    have hab : a j ≠ a (j + 1) := hp.injective.ne (by fin_cases j <;> decide)
    have hac : a j ≠ a (j + 2) := hp.injective.ne (by fin_cases j <;> decide)
    have hqf := twoCM_quadDerivative_order_nonneg_at_other hp.nonconst_f hab hac hpos
    have hqg := twoCM_quadDerivative_order_nonneg_at_other hp.nonconst_g hab hac hposg
    have he := twoCM_deriv_reciprocalDifference_of_quartic_ratio hp.nonconst_f hp.nonconst_g hc hquad
    apply twoCM_order_nonneg_of_deriv_order_nonneg (hH z)
    rw [meromorphicOrderAt_congr (codiscrete_iff_nhdsNE.1 he z)]
    have hleft := mixed_order_const_mul_nonneg
      (twoCM_meromorphic_quadDerivative hp.nonconst_f _ _ z) hqf (-1)
    have hright := mixed_order_const_mul_nonneg
      (twoCM_meromorphic_quadDerivative hp.nonconst_g _ _ z) hqg k
    have heq : (fun w => -twoCMQuadDerivative (a (j + 1)) (a (j + 2)) f w +
        k * twoCMQuadDerivative (a (j + 1)) (a (j + 2)) g w) =
        (fun w => (-1 : ℂ) * twoCMQuadDerivative (a (j + 1)) (a (j + 2)) f w) +
        (fun w => k * twoCMQuadDerivative (a (j + 1)) (a (j + 2)) g w) := by
      ext w
      simp
    rw [heq]
    exact mixed_order_add_nonneg
      ((MeromorphicAt.const (-1) z).mul (twoCM_meromorphic_quadDerivative hp.nonconst_f _ _ z))
      ((MeromorphicAt.const k z).mul (twoCM_meromorphic_quadDerivative hp.nonconst_g _ _ z))
      hleft hright
  · have hzero : mult f (a j : Sphere) z = 0 := by omega
    have hzerog : mult g (a j : Sphere) z = 0 := by rw [← hcm z (mem_univ z)]; exact hzero
    have hfi : 0 ≤ meromorphicOrderAt (fun w => (f w - a j)⁻¹) z := by
      have hle := order_sub_nonpos_of_mult_eq_zero hzero (hp.nonconst_f.2 z (mem_univ z) (a j))
      obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 (hp.nonconst_f.2 z (mem_univ z) (a j))
      have hn0 : n ≤ 0 := by rw [← hn] at hle; exact_mod_cast hle
      rw [order_mobius_comp, ← hn, ← WithTop.LinearOrderedAddCommGroup.coe_neg]
      exact_mod_cast (neg_nonneg.2 hn0)

    have hgi : 0 ≤ meromorphicOrderAt (fun w => (g w - a j)⁻¹) z := by
      have hle := order_sub_nonpos_of_mult_eq_zero hzerog (hp.nonconst_g.2 z (mem_univ z) (a j))
      obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 (hp.nonconst_g.2 z (mem_univ z) (a j))
      have hn0 : n ≤ 0 := by rw [← hn] at hle; exact_mod_cast hle
      rw [order_mobius_comp, ← hn, ← WithTop.LinearOrderedAddCommGroup.coe_neg]
      exact_mod_cast (neg_nonneg.2 hn0)

    have hright := mixed_order_const_mul_nonneg (meromorphicAt_mobius_comp hgm (a j)) hgi (-k)
    have heq : twoCMReciprocalDifference (a j) k f g =
        (fun w => (f w - a j)⁻¹) + (fun w => (-k) * (g w - a j)⁻¹) := by
      ext w
      simp [twoCMReciprocalDifference, sub_eq_add_neg]
    rw [heq]
    exact mixed_order_add_nonneg (meromorphicAt_mobius_comp hfm (a j))
      ((MeromorphicAt.const (-k) z).mul (meromorphicAt_mobius_comp hgm (a j))) hfi hright

end ThreeIM
