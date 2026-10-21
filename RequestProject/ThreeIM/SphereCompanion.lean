module

public import RequestProject.ThreeIM.SphereCollapse
public import RequestProject.ThreeIM.SphereSharingLimits
public import RequestProject.ThreeIM.SpherePicardDerivative

/-!
# Companion normality for four shared spherical fibers

A Zalcman bubble of a nonnormal companion has a nonconstant entire limit.
The normal member has a subsequence collapsing to a constant on that scale.
At least three of the four targets differ from the constant, contradicting
the constant-companion consequence of Hurwitz and little Picard.
-/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

theorem three_targets_away_of_four {a : Fin 4 → OnePoint ℂ} (ha : Function.Injective a)
    (p : OnePoint ℂ) : ∃ b : Fin 3 → OnePoint ℂ, Function.Injective b ∧
      (∀ j, p ≠ b j) ∧ ∀ j, ∃ i : Fin 4, b j = a i := by
  classical
  by_cases hp : ∃ i, p = a i
  · obtain ⟨i, hpi⟩ := hp
    refine ⟨fun j => a (i.succAbove j), ha.comp Fin.succAbove_right_injective, ?_,
      fun j => ⟨i.succAbove j, rfl⟩⟩
    intro j hj
    exact Fin.ne_succAbove i j (ha (hpi.symm.trans hj))
  · exact ⟨fun j => a j.castSucc, ha.comp (Fin.castSucc_injective 3),
      fun j hj => hp ⟨j.castSucc, hj⟩, fun j => ⟨j.castSucc, rfl⟩⟩

theorem sphere_companion_isNormalAt {ι : Type*} (F G : ι → ℂ → OnePoint ℂ)
    {U : Set ℂ} (hU : IsOpen U) (hF : ∀ i, SphereHolomorphicOn (F i) U)
    (hG : ∀ i, SphereHolomorphicOn (G i) U) (a : Fin 4 → OnePoint ℂ)
    (ha : Function.Injective a)
    (hshare : ∀ i w, w ∈ U → ∀ j, (F i w = a j ↔ G i w = a j))
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hnormal : IsNormalAt (range F) z₀) :
    IsNormalAt (range G) z₀ := by
  classical
  by_contra hnot
  obtain ⟨Q, z, ρ, g, hQ, hz, _, hρ, hg, hg0, _, hconv⟩ :=
    exists_zalcman_rescale hU (fun H hH => by
      obtain ⟨i, rfl⟩ := hH
      exact hG i) hz₀ hnot
  choose i hi using hQ
  obtain ⟨V, hVz, hNV⟩ := hnormal
  obtain ⟨ψ, hψ, f, hfc⟩ := hNV (fun n => ⟨F (i n), mem_range_self _⟩)
  change TendstoLocallyUniformlyOn (fun n => F (i (ψ n))) f atTop V at hfc
  obtain ⟨W, hWsub, hWo, hzW⟩ :=
    _root_.mem_nhds_iff.mp (inter_mem (hU.mem_nhds hz₀) hVz)
  have hfcW : TendstoLocallyUniformlyOn (fun n => F (i (ψ n))) f atTop W :=
    hfc.mono (fun _ hw => (hWsub hw).2)
  have hcf : ContinuousAt f z₀ :=
    (hfcW.continuousOn (Frequently.of_forall fun n =>
      (hF (i (ψ n))).continuousOn.mono (fun _ hw => (hWsub hw).1))).continuousAt
        (hWo.mem_nhds hzW)
  have hzψ : Tendsto (fun n => z (ψ n)) atTop (𝓝 z₀) := hz.comp hψ.tendsto_atTop
  have hρψ : Tendsto (fun n => ρ (ψ n)) atTop (𝓝 0) := hρ.comp hψ.tendsto_atTop
  have hcollapse : TendstoLocallyUniformlyOn
      (fun n w => F (i (ψ n)) (z (ψ n) + (ρ (ψ n) : ℂ) * w))
      (fun _ => f z₀) atTop univ :=
    rescale_tendstoLocallyUniformlyOn_const hWo hzW hcf hfcW hzψ hρψ
  have hQc : TendstoLocallyUniformlyOn
      (fun n w => G (i n) (z n + (ρ n : ℂ) * w)) g atTop univ := by
    apply hconv.congr
    intro n w _
    exact congrFun (hi n).symm _
  have hgc : TendstoLocallyUniformlyOn
      (fun n w => G (i (ψ n)) (z (ψ n) + (ρ (ψ n) : ℂ) * w)) g atTop univ := by
    intro u hu x hx
    obtain ⟨t, ht, hev⟩ := hQc u hu x hx
    exact ⟨t, ht, hψ.tendsto_atTop.eventually hev⟩
  have hgnc : ¬ ∃ p : OnePoint ℂ, ∀ w, g w = p := by
    rintro ⟨p, hp⟩
    have hconstant : g = fun _ => p := funext hp
    have hzero := sphericalDeriv_const p 0
    rw [← hconstant, hg0] at hzero
    exact one_ne_zero hzero
  obtain ⟨b, hb, hpb, hba⟩ := three_targets_away_of_four ha (f z₀)
  apply sphere_constant_companion_impossible hg hgnc hgc hcollapse
    (b 0) (b 1) (b 2) (hb.ne (by decide)) (hb.ne (by decide)) (hb.ne (by decide))
      (hpb 0) (hpb 1) (hpb 2)
  intro w
  let R : ℝ := ‖w‖ + 1
  refine ⟨ball 0 R, isOpen_ball, ?_, ?_⟩
  · rw [mem_ball_zero_iff]
    dsimp only [R]
    linarith
  · filter_upwards [eventually_sphereHolomorphic_rescale hU (fun n => hG (i (ψ n)))
      hz₀ hzψ hρψ R, eventually_rescale_closedBall_subset hU hz₀ hzψ hρψ R]
        with n hn hmap
    refine ⟨hn, fun x hx => ?_⟩
    have hxU := hmap x (ball_subset_closedBall hx)
    have hsb : ∀ j : Fin 3,
        (G (i (ψ n)) (z (ψ n) + (ρ (ψ n) : ℂ) * x) = b j ↔
         F (i (ψ n)) (z (ψ n) + (ρ (ψ n) : ℂ) * x) = b j) := by
      intro j
      obtain ⟨k, hk⟩ := hba j
      rw [hk]
      exact (hshare _ _ hxU k).symm
    exact ⟨hsb 0, hsb 1, hsb 2⟩

theorem sphere_companion_isNormalAt_iff {ι : Type*} (F G : ι → ℂ → OnePoint ℂ)
    {U : Set ℂ} (hU : IsOpen U) (hF : ∀ i, SphereHolomorphicOn (F i) U)
    (hG : ∀ i, SphereHolomorphicOn (G i) U) (a : Fin 4 → OnePoint ℂ)
    (ha : Function.Injective a)
    (hshare : ∀ i w, w ∈ U → ∀ j, (F i w = a j ↔ G i w = a j))
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    IsNormalAt (range F) z₀ ↔ IsNormalAt (range G) z₀ :=
  ⟨sphere_companion_isNormalAt F G hU hF hG a ha hshare hz₀,
   sphere_companion_isNormalAt G F hU hG hF a ha
    (fun i w hw j => (hshare i w hw j).symm) hz₀⟩

end ThreeIM
