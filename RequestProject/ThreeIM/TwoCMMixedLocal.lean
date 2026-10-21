module

public import RequestProject.ThreeIM.TwoCMOpposite

/-!
# The zero-scalar case of the mixed auxiliary identity

No division by the scalar cAux is used. When it vanishes, the squared chi
identity forces chi itself to vanish, giving a constant ratio of quartic
differential quotients.
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

noncomputable def twoCMQuarticDerivative (a b c : ℂ) (h : ℂ → ℂ) : ℂ → ℂ :=
  fun z => deriv h z / (((h z - a) ^ 2 * (h z - b)) * (h z - c))

theorem twoCM_meromorphic_quarticDerivative {h : ℂ → ℂ}
    (hh : IsNonconstMeroOn h univ) (a b c : ℂ) :
    Meromorphic (twoCMQuarticDerivative a b c h) := by
  intro z
  have hm := hh.meromorphic z
  exact hm.deriv.div ((((hm.sub (MeromorphicAt.const a z)).pow 2).mul
    (hm.sub (MeromorphicAt.const b z))).mul (hm.sub (MeromorphicAt.const c z)))

theorem twoCM_quarticDerivative_order_ne_top {h : ℂ → ℂ}
    (hh : IsNonconstMeroOn h univ) (a b c z : ℂ) :
    meromorphicOrderAt (twoCMQuarticDerivative a b c h) z ≠ ⊤ := by
  apply (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
    (twoCM_meromorphic_quarticDerivative hh a b c z)).2
  have hdn := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
    (hh.meromorphic z).deriv).1 (order_deriv_of_nonconst hh (mem_univ z)).1
  filter_upwards [hdn, codiscrete_iff_nhdsNE.1 (hh.eventually_ne a) z,
    codiscrete_iff_nhdsNE.1 (hh.eventually_ne b) z,
    codiscrete_iff_nhdsNE.1 (hh.eventually_ne c) z] with w hd ha hb hc
  exact div_ne_zero hd (mul_ne_zero
    (mul_ne_zero (pow_ne_zero 2 (sub_ne_zero.2 ha)) (sub_ne_zero.2 hb)) (sub_ne_zero.2 hc))

theorem twoCM_logDeriv_quarticDerivative {h : ℂ → ℂ}
    (hh : IsNonconstMeroOn h univ) (a b c : ℂ) :
    (fun z => deriv (twoCMQuarticDerivative a b c h) z /
      twoCMQuarticDerivative a b c h z) =ᶠ[codiscrete ℂ]
    (fun z => deriv (deriv h) z / deriv h z - 2 * (deriv h z / (h z - a)) -
      deriv h z / (h z - b) - deriv h z / (h z - c)) := by
  have hdn : ∀ᶠ z in codiscrete ℂ, deriv h z ≠ 0 :=
    codiscrete_iff_nhdsNE.2 fun z =>
      (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
        (hh.meromorphic z).deriv).1 (order_deriv_of_nonconst hh (mem_univ z)).1
  filter_upwards [eventually_analyticAt_of_meromorphic hh.meromorphic,
    eventually_analyticAt_of_meromorphic (fun z => (hh.meromorphic z).deriv),
    hdn, hh.eventually_ne a, hh.eventually_ne b, hh.eventually_ne c]
    with z hz hdz hd ha hb hc
  have hDa := hz.differentiableAt.sub_const a
  have hDb := hz.differentiableAt.sub_const b
  have hDc := hz.differentiableAt.sub_const c
  have hna := sub_ne_zero.2 ha
  have hnb := sub_ne_zero.2 hb
  have hnc := sub_ne_zero.2 hc
  change logDeriv (fun w => deriv h w / (((h w - a) ^ 2 * (h w - b)) * (h w - c))) z = _
  rw [logDeriv_fun_div (f := deriv h)
    (g := fun w => ((h w - a) ^ 2 * (h w - b)) * (h w - c)) z hd
    (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hna) hnb) hnc) hdz.differentiableAt
      (((hDa.pow 2).mul hDb).mul hDc),
    logDeriv_fun_mul (f := fun w => (h w - a) ^ 2 * (h w - b))
      (g := fun w => h w - c) z (mul_ne_zero (pow_ne_zero 2 hna) hnb) hnc
      ((hDa.pow 2).mul hDb) hDc,
    logDeriv_fun_mul (f := fun w => (h w - a) ^ 2) (g := fun w => h w - b) z
      (pow_ne_zero 2 hna) hnb (hDa.pow 2) hDb,
    logDeriv_fun_pow hDa 2]
  simp only [logDeriv_apply, deriv_sub_const, Nat.cast_ofNat]
  ring

theorem twoCM_quarticDerivative_ratio_of_chi_zero {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair univ f g a) (j : Fin 3)
    (hchi : twoCMChi a j f g =ᶠ[codiscrete ℂ] (fun _ => 0)) :
    ∃ k : ℂ, k ≠ 0 ∧
      twoCMQuarticDerivative (a j) (a (j + 1)) (a (j + 2)) f =ᶠ[codiscrete ℂ]
      (fun z => k * twoCMQuarticDerivative (a j) (a (j + 1)) (a (j + 2)) g z) := by
  apply twoCM_const_ratio_of_log_deriv_eq
    (twoCM_meromorphic_quarticDerivative hp.nonconst_f _ _ _)
    (twoCM_meromorphic_quarticDerivative hp.nonconst_g _ _ _)
    (twoCM_quarticDerivative_order_ne_top hp.nonconst_f _ _ _)
    (twoCM_quarticDerivative_order_ne_top hp.nonconst_g _ _ _)
  filter_upwards [twoCM_logDeriv_quarticDerivative hp.nonconst_f (a j) (a (j + 1)) (a (j + 2)),
    twoCM_logDeriv_quarticDerivative hp.nonconst_g (a j) (a (j + 1)) (a (j + 2)),
    hchi] with z hf hg hz
  rw [hf, hg]
  simp only [twoCMChi, twoCMLogDiff, thetaAux, ThetaFun] at hz
  linear_combination hz

theorem twoCM_chi_zero_of_cAux_zero {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (j : Fin 3) (hc : cAux a j = 0)
    (hW : ∀ z, meromorphicOrderAt (twoCMWChi a j f g) z = ⊤) :
    twoCMChi a j f g =ᶠ[codiscrete ℂ] (fun _ => 0) := by
  have hz : twoCMWChi a j f g =ᶠ[codiscrete ℂ] (fun _ => 0) :=
    codiscrete_iff_nhdsNE.2 fun z => meromorphicOrderAt_eq_top_iff.1 (hW z)
  filter_upwards [hz] with z hz
  simp only [twoCMWChi, hc, zero_pow (by decide : 2 ≠ 0), zero_mul, sub_zero] at hz
  exact (sq_eq_zero_iff).1 hz

end ThreeIM
