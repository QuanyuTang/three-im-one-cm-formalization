module

public import RequestProject.ThreeIM.TransportNormalFormCoordinates
public import RequestProject.ThreeIM.RepresentativePairs
public import RequestProject.ThreeIM.AuxiliaryAmplitudeSystem

/-!
# The original sharing and auxiliary hypotheses for the continuation forms

Translation to the marked value zero and conversion to normal forms
preserve finite germ orders. The original auxiliary identities become the
two regular transport identities, and the original shared marked fiber is
exactly the shared zero fiber needed for continuation.
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

set_option autoImplicit false

theorem transport_sub_const_nonconst {Ω : Set ℂ} {F : ℂ → ℂ}
    (hF : IsNonconstMeroOn F Ω) (c : ℂ) :
    IsNonconstMeroOn (fun z => F z - c) Ω := by
  refine ⟨fun z hz => (hF.1 z hz).sub (MeromorphicAt.const c z), fun z hz b => ?_⟩
  have he : (fun w => (F w - c) - b) = fun w => F w - (c + b) := by
    funext w
    ring
  rw [he]
  exact hF.2 z hz (c + b)

theorem transport_normal_form_nonconst {Ω : Set ℂ} (hΩ : IsOpen Ω) {F : ℂ → ℂ}
    (hF : IsNonconstMeroOn F Ω) (c : ℂ) :
    IsNonconstMeroOn (transportNormalF Ω F c) Ω := by
  have hs := transport_sub_const_nonconst hF c
  exact hs.congr_codiscreteWithin hΩ (toMeromorphicNFOn_eqOn_codiscrete hs.1)

theorem transport_normal_form_shared_zero {Ω : Set ℂ} {F G : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair Ω F G a) (j : Fin 3) {z : ℂ} (hz : z ∈ Ω) :
    0 < (meromorphicOrderAt (transportNormalF Ω F (a j)) z).untop₀.toNat ↔
      0 < (meromorphicOrderAt (transportNormalF Ω G (a j)) z).untop₀.toNat := by
  have hsF := transport_sub_const_nonconst hp.nonconst_f (a j)
  have hsG := transport_sub_const_nonconst hp.nonconst_g (a j)
  have heF := meromorphicOrderAt_congr (hsF.1.toMeromorphicNFOn_eq_self_on_nhdsNE hz)
  have heG := meromorphicOrderAt_congr (hsG.1.toMeromorphicNFOn_eq_self_on_nhdsNE hz)
  change meromorphicOrderAt (transportNormalF Ω F (a j)) z =
    meromorphicOrderAt (fun w => F w - a j) z at heF
  change meromorphicOrderAt (transportNormalF Ω G (a j)) z =
    meromorphicOrderAt (fun w => G w - a j) z at heG
  rw [heF, heG]
  exact hp.im j z hz

theorem transport_cubic_shift_factor (a : Fin 3 → ℂ) (j : Fin 3) (w : ℂ) :
    cubicP a (w + a j) = w * transportQ (a (j + 1) - a j) (a (j + 2) - a j) w := by
  fin_cases j <;> simp [cubicP, transportQ] <;> ring

theorem amplitudeRemainder_eq_transport_product (a : Fin 3 → ℂ) (j : Fin 3) :
    amplitudeRemainder a j (a j) = (a (j + 1) - a j) * (a (j + 2) - a j) := by
  classical
  have he : (Finset.univ : Finset (Fin 3)).erase j = {j + 1, j + 2} := by
    fin_cases j <;> decide
  have hj : j + 1 ≠ j + 2 := by fin_cases j <;> decide
  rw [amplitudeRemainder, he, Finset.prod_pair hj]
  ring

theorem transport_normal_form_auxiliary_identities
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {F G u v : ℂ → ℂ} {a : Fin 3 → ℂ} (j : Fin 3)
    (hF : MeromorphicOn F Ω) (hG : MeromorphicOn G Ω)
    (hU : auxU a F G =ᶠ[codiscreteWithin Ω] u)
    (hV : auxV a F G =ᶠ[codiscreteWithin Ω] v) :
    ((fun z => (transportNormalF Ω F (a j) z - transportNormalF Ω G (a j) z) *
      deriv (transportNormalF Ω F (a j)) z /
      (transportNormalF Ω F (a j) z * transportQ (a (j + 1) - a j) (a (j + 2) - a j)
        (transportNormalF Ω F (a j) z))) =ᶠ[codiscreteWithin Ω] u) ∧
    ((fun z => (transportNormalF Ω F (a j) z - transportNormalF Ω G (a j) z) *
      deriv (transportNormalF Ω G (a j)) z /
      (transportNormalF Ω G (a j) z * transportQ (a (j + 1) - a j) (a (j + 2) - a j)
        (transportNormalF Ω G (a j) z))) =ᶠ[codiscreteWithin Ω] v) := by
  have hFs : MeromorphicOn (fun w => F w - a j) Ω :=
    fun w hw => (hF w hw).sub (MeromorphicAt.const (a j) w)
  have hGs : MeromorphicOn (fun w => G w - a j) Ω :=
    fun w hw => (hG w hw).sub (MeromorphicAt.const (a j) w)
  have heF : (fun w => transportNormalF Ω F (a j) w + a j) =ᶠ[codiscreteWithin Ω] F := by
    filter_upwards [toMeromorphicNFOn_eqOn_codiscrete hFs] with w hw
    change F w - a j = transportNormalF Ω F (a j) w at hw
    linear_combination -hw
  have heG : (fun w => transportNormalF Ω G (a j) w + a j) =ᶠ[codiscreteWithin Ω] G := by
    filter_upwards [toMeromorphicNFOn_eqOn_codiscrete hGs] with w hw
    change G w - a j = transportNormalF Ω G (a j) w at hw
    linear_combination -hw
  have hc := auxiliary_congr_codiscreteWithin hΩ heF heG a
  constructor
  · filter_upwards [hc.1.trans hU] with w hw
    rw [← hw]
    dsimp only [auxU]
    rw [deriv_add_const, transport_cubic_shift_factor]
    congr 1 <;> ring
  · filter_upwards [hc.2.1.trans hV] with w hw
    rw [← hw]
    dsimp only [auxV]
    rw [deriv_add_const, transport_cubic_shift_factor]
    congr 1 <;> ring

end ThreeIM
