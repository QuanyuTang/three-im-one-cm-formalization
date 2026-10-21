module

public import RequestProject.ThreeIM.SphereDiagonal

/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Will (Ziang) Li

Adapted by Codex from the finite-subcover proof in
NoWanderingDomains.NormalFamilies.Basic, upstream commit
0a6497b0cc9ed39a6a705bf013449635894b56d0. The compact domain is each
closed disk, followed by the checked exhaustion diagonal.
-/

/-! # Global spherical extraction from local normality -/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

theorem sphere_isNormal_of_forall_isNormalAt {𝓕 : Set (ℂ → OnePoint ℂ)}
    (h : ∀ z : ℂ, IsNormalAt 𝓕 z) : IsNormal 𝓕 univ := by
  classical
  choose Uz hUz hNz using h
  have hVmem : ∀ z : ℂ, z ∈ interior (Uz z) := fun z =>
    mem_interior_iff_mem_nhds.mpr (hUz z)
  have hVnorm : ∀ z : ℂ, IsNormal 𝓕 (interior (Uz z)) := fun z =>
    (hNz z).mono interior_subset
  have key : ∀ s : Finset ℂ, IsNormal 𝓕 (⋃ z ∈ s, interior (Uz z)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro seq
      refine ⟨id, strictMono_id, (seq 0 : ℂ → OnePoint ℂ), ?_⟩
      intro u hu x hx
      obtain ⟨i, hi, -⟩ := Set.mem_iUnion₂.mp hx
      exact absurd hi (Finset.notMem_empty i)
    | insert a s ha ih =>
      rw [Finset.set_biUnion_insert]
      exact IsNormal.union isOpen_interior
        (isOpen_biUnion fun z _ => isOpen_interior) (hVnorm a) ih
  apply sphere_isNormal_of_normal_balls
  intro m
  obtain ⟨t, ht⟩ := (isCompact_closedBall (0 : ℂ) ((m : ℝ) + 1)).elim_finite_subcover
    (fun z => interior (Uz z)) (fun z => isOpen_interior)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hVmem x⟩)
  exact (key t).mono (ball_subset_closedBall.trans ht)

theorem sphere_pair_subsequence_of_normal {F G : ℕ → ℂ → OnePoint ℂ}
    (hF : IsNormal (range F) univ) (hG : IsNormal (range G) univ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ f g : ℂ → OnePoint ℂ,
      TendstoLocallyUniformlyOn (fun n => F (ψ n)) f atTop univ ∧
      TendstoLocallyUniformlyOn (fun n => G (ψ n)) g atTop univ := by
  obtain ⟨φ, hφ, f, hfc⟩ := hF (fun n => ⟨F n, mem_range_self n⟩)
  obtain ⟨χ, hχ, g, hgc⟩ := hG (fun n => ⟨G (φ n), mem_range_self (φ n)⟩)
  refine ⟨φ ∘ χ, hφ.comp hχ, f, g, ?_, hgc⟩
  intro v hv x hx
  obtain ⟨t, ht, hev⟩ := hfc v hv x hx
  exact ⟨t, ht, hχ.tendsto_atTop.eventually hev⟩

theorem sphereHolomorphicOn_univ_of_locally_eventually {F : ℕ → ℂ → OnePoint ℂ}
    {G : ℂ → OnePoint ℂ}
    (hconv : TendstoLocallyUniformlyOn F G atTop univ)
    (hloc : ∀ z : ℂ, ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
      ∀ᶠ n in atTop, SphereHolomorphicOn (F n) U) : SphereHolomorphicOn G univ := by
  intro z _
  obtain ⟨U, hU, hzU, hev⟩ := hloc z
  have hG := sphereHolomorphicOn_of_eventually hU hev (hconv.mono (subset_univ U))
  obtain ⟨V, hV, hzV, _, hcase⟩ := hG z hzU
  exact ⟨V, hV, hzV, subset_univ V, hcase⟩

end ThreeIM
