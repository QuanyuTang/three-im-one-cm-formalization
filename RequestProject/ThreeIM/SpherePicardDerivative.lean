module

/-
Copyright (c) 2026 Yixin He, Quanyu Tang, Jun Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original source authors: Yixin He, Quanyu Tang, Jun Wang
Project authors: Pengcheng Fang, Tao Hu, Yanyang Li, Quanyu Tang
-/
public import RequestProject.ThreeIM.SpherePicard
public import NoWanderingDomains.NormalFamilies.Zalcman

/-!
# Spherical derivative consequences of little Picard

The derivative of a constant sphere-valued map vanishes. Consequently, a
sphere-holomorphic map on the complex plane omitting three distinct values
cannot have the normalization supplied by Zalcman's rescaling theorem.
-/

@[expose] public section

namespace ThreeIM

theorem sphericalDeriv_const (c : OnePoint ℂ) (z : ℂ) :
    NoWanderingDomains.sphericalDeriv (fun _ => c) z = 0 := by
  simp [NoWanderingDomains.sphericalDeriv]

theorem exists_ne_of_sphericalDeriv_ne_zero {F : ℂ → OnePoint ℂ} {z : ℂ}
    (h : NoWanderingDomains.sphericalDeriv F z ≠ 0) : ∃ w, F w ≠ F 0 := by
  classical
  by_contra hconstant
  push_neg at hconstant
  have hF : F = fun _ => F 0 := funext hconstant
  apply h
  rw [hF]
  exact sphericalDeriv_const _ _

theorem sphere_picard_sphericalDeriv_eq_zero {F : ℂ → OnePoint ℂ}
    (hF : NoWanderingDomains.SphereHolomorphicOn F Set.univ)
    (a b c : OnePoint ℂ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : ∀ z, F z ≠ a) (hb : ∀ z, F z ≠ b) (hc : ∀ z, F z ≠ c) (z : ℂ) :
    NoWanderingDomains.sphericalDeriv F z = 0 := by
  obtain ⟨w, hw⟩ := sphere_picard_constant hF a b c hab hac hbc ha hb hc
  have hconstant : F = fun _ => w := funext hw
  rw [hconstant]
  exact sphericalDeriv_const _ _

theorem sphere_picard_normalized_impossible {F : ℂ → OnePoint ℂ}
    (hF : NoWanderingDomains.SphereHolomorphicOn F Set.univ)
    (a b c : OnePoint ℂ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : ∀ z, F z ≠ a) (hb : ∀ z, F z ≠ b) (hc : ∀ z, F z ≠ c)
    (hnormalized : NoWanderingDomains.sphericalDeriv F 0 = 1) : False := by
  have hzero := sphere_picard_sphericalDeriv_eq_zero hF a b c hab hac hbc ha hb hc 0
  exact zero_ne_one (hzero.symm.trans hnormalized)

end ThreeIM
