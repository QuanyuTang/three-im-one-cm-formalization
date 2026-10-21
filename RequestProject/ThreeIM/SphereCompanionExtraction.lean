module

public import RequestProject.ThreeIM.SphereCompanion
public import RequestProject.ThreeIM.SphereGlobalNormality
public import RequestProject.ThreeIM.SphereTailNormality
public import RequestProject.ThreeIM.SphereSequenceNormality

/-!
# Extracting a nonconstant companion on the plane

The first member already converges locally uniformly to a nonconstant
entire sphere map. Eventual local holomorphy and four shared fibers force
normality of the companion, a global diagonal subsequence, and a nonconstant
companion limit. Finite prefixes need not be holomorphic on fixed disks.
-/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

theorem exists_nonconstant_spherical_companion {F G : ℕ → ℂ → OnePoint ℂ}
    {f : ℂ → OnePoint ℂ} (hf : SphereHolomorphicOn f univ)
    (hfnc : ¬ ∃ p : OnePoint ℂ, ∀ z, f z = p)
    (hF : TendstoLocallyUniformlyOn F f atTop univ)
    (a : Fin 4 → OnePoint ℂ) (ha : Function.Injective a)
    (hloc : ∀ z : ℂ, ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
      ∀ᶠ n in atTop, SphereHolomorphicOn (F n) U ∧ SphereHolomorphicOn (G n) U ∧
        ∀ w ∈ U, ∀ j, (F n w = a j ↔ G n w = a j)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ g : ℂ → OnePoint ℂ,
      SphereHolomorphicOn g univ ∧ (¬ ∃ p : OnePoint ℂ, ∀ z, g z = p) ∧
      TendstoLocallyUniformlyOn (fun n => G (ψ n)) g atTop univ := by
  classical
  have hnormal : ∀ z : ℂ, IsNormalAt (range G) z := by
    intro z
    obtain ⟨U, hU, hzU, hev⟩ := hloc z
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    have hFN : TendstoLocallyUniformlyOn (fun n => F (n + N)) f atTop U := by
      intro v hv x hx
      obtain ⟨t, ht, hc⟩ := hF.mono (subset_univ U) v hv x hx
      exact ⟨t, ht, (tendsto_add_atTop_nat N).eventually hc⟩
    have hnF := isNormalAt_range_of_tendstoLocallyUniformlyOn hU hFN hzU
    have hnG := sphere_companion_isNormalAt (fun n => F (n + N)) (fun n => G (n + N))
      hU (fun n => (hN (n + N) (Nat.le_add_left N n)).1)
      (fun n => (hN (n + N) (Nat.le_add_left N n)).2.1) a ha
      (fun n w hw j => (hN (n + N) (Nat.le_add_left N n)).2.2 w hw j) hzU hnF
    exact isNormalAt_range_of_normal_tail G N hnG
  obtain ⟨ψ, hψ, g, hgc⟩ := (sphere_isNormal_of_forall_isNormalAt hnormal)
    (fun n => ⟨G n, mem_range_self n⟩)
  have hgh : SphereHolomorphicOn g univ :=
    sphereHolomorphicOn_univ_of_locally_eventually hgc (fun z => by
      obtain ⟨U, hU, hzU, hev⟩ := hloc z
      exact ⟨U, hU, hzU, (hψ.tendsto_atTop.eventually hev).mono fun n hn => hn.2.1⟩)
  refine ⟨ψ, hψ, g, hgh, ?_, hgc⟩
  rintro ⟨p, hp⟩
  have hfc : TendstoLocallyUniformlyOn (fun n => F (ψ n)) f atTop univ := by
    intro v hv x hx
    obtain ⟨t, ht, hc⟩ := hF v hv x hx
    exact ⟨t, ht, hψ.tendsto_atTop.eventually hc⟩
  have hgp : g = fun _ => p := funext hp
  rw [hgp] at hgc
  obtain ⟨b, hb, hpb, hba⟩ := three_targets_away_of_four ha p
  apply sphere_constant_companion_impossible hf hfnc hfc hgc
    (b 0) (b 1) (b 2) (hb.ne (by decide)) (hb.ne (by decide)) (hb.ne (by decide))
    (hpb 0) (hpb 1) (hpb 2)
  intro z
  obtain ⟨U, hU, hzU, hev⟩ := hloc z
  refine ⟨U, hU, hzU, (hψ.tendsto_atTop.eventually hev).mono fun n hn => ⟨hn.1, ?_⟩⟩
  intro w hw
  have hsb : ∀ j : Fin 3, (F (ψ n) w = b j ↔ G (ψ n) w = b j) := by
    intro j
    obtain ⟨k, hk⟩ := hba j
    rw [hk]
    exact hn.2.2 w hw k
  exact ⟨hsb 0, hsb 1, hsb 2⟩

end ThreeIM
