module

public import RequestProject.ThreeIM.TwoCMChi
public import RequestProject.ThreeIM.TwoCMMeromorphicConst

/-!
# Integrating the opposite-sign auxiliary identity

The opposite sign gives equality of logarithmic derivatives of the two
quadratic differential quotients. This module records the resulting constant
ratio as an equality off a discrete set.
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

noncomputable def twoCMQuadDerivative (b c : ℂ) (h : ℂ → ℂ) : ℂ → ℂ :=
  fun z => deriv h z / ((h z - b) * (h z - c))

variable {f g : ℂ → ℂ} {a : Fin 3 → ℂ}

theorem twoCM_meromorphic_quadDerivative {h : ℂ → ℂ}
    (hh : IsNonconstMeroOn h univ) (b c : ℂ) :
    Meromorphic (twoCMQuadDerivative b c h) := by
  intro z
  exact (hh.meromorphic z).deriv.div
    (((hh.meromorphic z).sub (MeromorphicAt.const b z)).mul
      ((hh.meromorphic z).sub (MeromorphicAt.const c z)))

theorem twoCM_quadDerivative_order_ne_top {h : ℂ → ℂ}
    (hh : IsNonconstMeroOn h univ) (b c z : ℂ) :
    meromorphicOrderAt (twoCMQuadDerivative b c h) z ≠ ⊤ := by
  apply (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
    (twoCM_meromorphic_quadDerivative hh b c z)).2
  have hdn := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
    (hh.meromorphic z).deriv).1 (order_deriv_of_nonconst hh (mem_univ z)).1
  have hbn := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
    ((hh.meromorphic z).sub (MeromorphicAt.const b z))).1
    (hh.2 z (mem_univ z) b)
  have hcn := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
    ((hh.meromorphic z).sub (MeromorphicAt.const c z))).1
    (hh.2 z (mem_univ z) c)
  filter_upwards [hdn, hbn, hcn] with w hd hb hc
  exact div_ne_zero hd (mul_ne_zero hb hc)

theorem twoCM_logDeriv_quadDerivative {h : ℂ → ℂ}
    (hh : IsNonconstMeroOn h univ) (b c : ℂ) :
    (fun z => deriv (twoCMQuadDerivative b c h) z /
      twoCMQuadDerivative b c h z) =ᶠ[codiscrete ℂ]
    (fun z => deriv (deriv h) z / deriv h z - deriv h z / (h z - b) -
      deriv h z / (h z - c)) := by
  have hdn : ∀ᶠ z in codiscrete ℂ, deriv h z ≠ 0 :=
    codiscrete_iff_nhdsNE.2 fun z =>
      (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
        (hh.meromorphic z).deriv).1 (order_deriv_of_nonconst hh (mem_univ z)).1
  have hbn := hh.eventually_ne b
  have hcn := hh.eventually_ne c
  filter_upwards [eventually_analyticAt_of_meromorphic hh.meromorphic,
    eventually_analyticAt_of_meromorphic (fun z => (hh.meromorphic z).deriv),
    hdn, hbn, hcn] with z hz hdz hdn hbn hcn
  change logDeriv (fun w => deriv h w / ((h w - b) * (h w - c))) z = _
  rw [logDeriv_fun_div (f := deriv h) (g := fun w => (h w - b) * (h w - c)) z hdn (mul_ne_zero (sub_ne_zero.2 hbn) (sub_ne_zero.2 hcn))
    hdz.differentiableAt ((hz.differentiableAt.sub_const b).mul (hz.differentiableAt.sub_const c)),
    logDeriv_fun_mul (f := fun w => h w - b) (g := fun w => h w - c) z (sub_ne_zero.2 hbn) (sub_ne_zero.2 hcn)
      (hz.differentiableAt.sub_const b) (hz.differentiableAt.sub_const c)]
  simp only [logDeriv_apply, deriv_sub_const]
  ring

theorem twoCM_quadDerivative_ratio_of_opposite (hp : NormalizedPair univ f g a)
    (j : Fin 3)
    (hopp : thetaAux a j f g =ᶠ[codiscrete ℂ] (fun z => -twoCMChi a j f g z)) :
    ∃ k : ℂ, k ≠ 0 ∧
      twoCMQuadDerivative (a (j + 1)) (a (j + 2)) f =ᶠ[codiscrete ℂ]
      (fun z => k * twoCMQuadDerivative (a (j + 1)) (a (j + 2)) g z) := by
  apply twoCM_const_ratio_of_log_deriv_eq
    (twoCM_meromorphic_quadDerivative hp.nonconst_f _ _)
    (twoCM_meromorphic_quadDerivative hp.nonconst_g _ _)
    (twoCM_quadDerivative_order_ne_top hp.nonconst_f _ _)
    (twoCM_quadDerivative_order_ne_top hp.nonconst_g _ _)
  filter_upwards [twoCM_logDeriv_quadDerivative hp.nonconst_f (a (j + 1)) (a (j + 2)),
    twoCM_logDeriv_quadDerivative hp.nonconst_g (a (j + 1)) (a (j + 2)),
    hopp] with z hf hg hz
  rw [hf, hg]
  simp only [twoCMChi, twoCMLogDiff, thetaAux, ThetaFun] at hz
  linear_combination (1 / 2 : ℂ) * hz

end ThreeIM
