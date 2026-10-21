module

public import RequestProject.ThreeIM.SpherePicard

/-!
# Two source points over three spherical targets

An entire nonconstant sphere map cannot take three prescribed distinct
targets only at one source point. Precomposition with z₀ + exp avoids that
point; little Picard makes the composition constant and continuity restores
the missing source value. No rational/transcendental classification is used.
-/

@[expose] public section

open Filter Set Topology NoWanderingDomains

namespace ThreeIM

theorem sphereHolomorphicOn_comp {F : ℂ → OnePoint ℂ} {U : Set ℂ}
    (hF : SphereHolomorphicOn F U) (h : ℂ → ℂ) (hh : Differentiable ℂ h) :
    SphereHolomorphicOn (fun w => F (h w)) (h ⁻¹' U) := by
  intro z hz
  obtain ⟨V, hVo, hzV, hVU, hcase⟩ := hF (h z) hz
  refine ⟨h ⁻¹' V, hVo.preimage hh.continuous, hzV, preimage_mono hVU, ?_⟩
  rcases hcase with ⟨hne, hd⟩ | ⟨hne, hd⟩
  · exact Or.inl ⟨fun w hw => hne (h w) hw,
      hd.comp hh.differentiableOn (fun _ hw => hw)⟩
  · exact Or.inr ⟨fun w hw => hne (h w) hw,
      hd.comp hh.differentiableOn (fun _ hw => hw)⟩

theorem exists_sphere_triple_fiber_away {H : ℂ → OnePoint ℂ}
    (hH : SphereHolomorphicOn H univ)
    (hnc : ¬ ∃ p : OnePoint ℂ, ∀ z, H z = p)
    (a b c : OnePoint ℂ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (z₀ : ℂ) :
    ∃ w : ℂ, w ≠ z₀ ∧ (H w = a ∨ H w = b ∨ H w = c) := by
  classical
  by_contra hnone
  have homits : ∀ w, w ≠ z₀ → H w ≠ a ∧ H w ≠ b ∧ H w ≠ c := by
    intro w hw
    exact ⟨fun ha => hnone ⟨w, hw, Or.inl ha⟩,
      fun hb => hnone ⟨w, hw, Or.inr (Or.inl hb)⟩,
      fun hc => hnone ⟨w, hw, Or.inr (Or.inr hc)⟩⟩
  have hexp : ∀ w : ℂ, z₀ + Complex.exp w ≠ z₀ := by
    intro w hw
    apply Complex.exp_ne_zero w
    exact add_left_cancel (hw.trans (add_zero z₀).symm)
  have hcomp : SphereHolomorphicOn (fun w => H (z₀ + Complex.exp w)) univ := by
    simpa only [preimage_univ] using
      sphereHolomorphicOn_comp hH (fun w => z₀ + Complex.exp w) (by fun_prop)
  obtain ⟨p, hp⟩ := sphere_picard_constant hcomp a b c hab hac hbc
    (fun w => (homits _ (hexp w)).1) (fun w => (homits _ (hexp w)).2.1)
    (fun w => (homits _ (hexp w)).2.2)
  have hpunct : ∀ w : ℂ, w ≠ z₀ → H w = p := by
    intro w hw
    have hpoint : z₀ + Complex.exp (Complex.log (w - z₀)) = w := by
      rw [Complex.exp_log (sub_ne_zero.2 hw)]
      ring
    simpa only [hpoint] using hp (Complex.log (w - z₀))
  have heq : H =ᶠ[𝓝[≠] z₀] (fun _ => p) := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact hpunct w hw
  have hc : ContinuousAt H z₀ :=
    hH.continuousOn.continuousAt (isOpen_univ.mem_nhds (mem_univ z₀))
  have hcenter : H z₀ = p := tendsto_nhds_unique
    (hc.tendsto.mono_left nhdsWithin_le_nhds) (tendsto_const_nhds.congr' heq.symm)
  apply hnc
  refine ⟨p, fun w => ?_⟩
  by_cases hw : w = z₀
  · simpa only [hw] using hcenter
  · exact hpunct w hw

theorem exists_two_sphere_triple_fibers {H : ℂ → OnePoint ℂ}
    (hH : SphereHolomorphicOn H univ)
    (hnc : ¬ ∃ p : OnePoint ℂ, ∀ z, H z = p)
    (a b c : OnePoint ℂ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ w v : ℂ, w ≠ v ∧ (H w = a ∨ H w = b ∨ H w = c) ∧
      (H v = a ∨ H v = b ∨ H v = c) := by
  obtain ⟨w, _, hw⟩ := exists_sphere_triple_fiber_away hH hnc a b c hab hac hbc 0
  obtain ⟨v, hv, hvt⟩ := exists_sphere_triple_fiber_away hH hnc a b c hab hac hbc w
  exact ⟨w, v, hv.symm, hw, hvt⟩

end ThreeIM
