module

/-
Copyright (c) 2026 Yixin He, Quanyu Tang, Jun Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original source authors: Yixin He, Quanyu Tang, Jun Wang
Project authors: Pengcheng Fang, Tao Hu, Yanyang Li, Quanyu Tang
-/
public import RequestProject.ThreeIM.PicardBasic
public import NoWanderingDomains.Sphere.SphereHolomorphic

/-!
# Sphere-valued little Picard

A sphere-holomorphic map on the complex plane omitting three distinct sphere
points is constant. Triple transitivity sends the omitted values to 0, 1 and
infinity. The finite chart is then an entire function omitting 0 and 1, so
the independently proved entire-function little Picard theorem applies.
-/

@[expose] public section

open Filter Set Topology OnePoint

namespace ThreeIM

private lemma spherePicard_entire_nonconst {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    (hnc : ∃ z, H z ≠ H 0) : IsNonconstMeroOn H univ := by
  refine ⟨fun z _ => (hH.analyticAt z).meromorphicAt, fun z _ c => ?_⟩
  have hfinite : analyticOrderAt (fun w => H w - c) z ≠ ⊤ := by
    intro htop
    obtain ⟨z', hz'⟩ := hnc
    have hev : H =ᶠ[𝓝 z] fun _ => c := by
      filter_upwards [analyticOrderAt_eq_top.1 htop] with w hw
      exact sub_eq_zero.1 hw
    have hall := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (f := H)
      (fun w _ => hH.analyticAt w) analyticOnNhd_const isPreconnected_univ
      (mem_univ z) hev
    exact hz' ((hall (mem_univ z')).trans (hall (mem_univ 0)).symm)
  have horder : meromorphicOrderAt (fun w => H w - c) z =
      (analyticOrderAt (fun w => H w - c) z).map (↑) :=
    ((hH.analyticAt z).sub analyticAt_const).meromorphicOrderAt_eq
  rw [horder]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hfinite
  rw [← hn]
  simp

/-- Sphere-valued little Picard: an entire sphere-holomorphic map omitting
three pairwise distinct sphere points is constant. -/
theorem sphere_picard_constant {F : ℂ → OnePoint ℂ}
    (hF : NoWanderingDomains.SphereHolomorphicOn F univ)
    (a b c : OnePoint ℂ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : ∀ z, F z ≠ a) (hb : ∀ z, F z ≠ b) (hc : ∀ z, F z ≠ c) :
    ∃ w : OnePoint ℂ, ∀ z, F z = w := by
  classical
  obtain ⟨A, hAa, hAb, hAc⟩ :=
    NoWanderingDomains.exists_gl_smul_eq_zero_one_infty hab hac hbc
  have hInf : ∀ z, A • F z ≠ (∞ : OnePoint ℂ) := by
    intro z hz
    exact hc z (MulAction.injective A (hz.trans hAc.symm))
  let H : ℂ → ℂ := fun z => NoWanderingDomains.chartFiniteMap (A • F z)
  have hH : Differentiable ℂ H := by
    exact differentiableOn_univ.1
      ((hF.gl_smul A).differentiableOn_chartFiniteMap (fun z _ => hInf z))
  have hcoe : ∀ z, (H z : OnePoint ℂ) = A • F z := by
    intro z
    obtain ⟨w, hw⟩ := OnePoint.ne_infty_iff_exists.mp (hInf z)
    dsimp only [H]
    rw [← hw]
    rfl
  have hZero : ∀ z, H z ≠ 0 := by
    intro z hz
    apply ha z
    apply MulAction.injective A
    change A • F z = A • a
    rw [← hcoe z, hz, hAa]
  have hOne : ∀ z, H z ≠ 1 := by
    intro z hz
    apply hb z
    apply MulAction.injective A
    change A • F z = A • b
    rw [← hcoe z, hz, hAb]
  by_cases hnc : ∃ z, H z ≠ H 0
  · exfalso
    apply entire_omits_two_impossible hH (spherePicard_entire_nonconst hH hnc)
      ![0, 1] (by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all)
    intro i z
    have hne : H z ≠ (![0, 1] : Fin 2 → ℂ) i := by
      fin_cases i
      · exact hZero z
      · exact hOne z
    have hAz : AnalyticAt ℂ (fun w => H w - (![0, 1] : Fin 2 → ℂ) i) z :=
      (hH.analyticAt z).sub analyticAt_const
    have horder : meromorphicOrderAt (fun w => H w - (![0, 1] : Fin 2 → ℂ) i) z =
        (analyticOrderAt (fun w => H w - (![0, 1] : Fin 2 → ℂ) i) z).map (↑) :=
      hAz.meromorphicOrderAt_eq
    simp [mult_coe, horder, hAz.analyticOrderAt_eq_zero.2 (sub_ne_zero.mpr hne)]
  · push_neg at hnc
    refine ⟨F 0, fun z => ?_⟩
    apply MulAction.injective A
    change A • F z = A • F 0
    rw [← hcoe z, ← hcoe 0, hnc z]

end ThreeIM
