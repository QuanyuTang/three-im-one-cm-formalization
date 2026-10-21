module

public import RequestProject.ThreeIM.ClusterMarkedDivisor

/-! # The finite set of genuine marked multiplicity ratios -/

@[expose] public section

set_option autoImplicit false

open Set Classical

namespace ThreeIM

/-- The two possible orientations of a marked pair of multiplicities,
with the larger multiplicity bounded by thirty. -/
theorem NormalizedPair.boundedMarkedDefect_multiplicities
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} (hp : NormalizedPair univ f g a)
    {j : Fin 3} {z : ℂ} (hz : IsBoundedMarkedDefect a f g j z) :
    ∃ m : ℕ, 2 ≤ m ∧ m ≤ 30 ∧
      ((mult f (a j : Sphere) z = 1 ∧ mult g (a j : Sphere) z = m) ∨
        (mult f (a j : Sphere) z = m ∧ mult g (a j : Sphere) z = 1)) := by
  have hmin := hp.min_mult_eq_one_of_psi (mem_univ z) hz.1.1 hz.2.1
  have hne := hz.1.2.2
  have hf30 : mult f (a j : Sphere) z ≤ 30 := (le_max_left _ _).trans hz.2.2
  have hg30 : mult g (a j : Sphere) z ≤ 30 := (le_max_right _ _).trans hz.2.2
  by_cases hf : mult f (a j : Sphere) z = 1
  · refine ⟨mult g (a j : Sphere) z, ?_, hg30, Or.inl ⟨hf, rfl⟩⟩
    omega
  · have hg : mult g (a j : Sphere) z = 1 := by omega
    refine ⟨mult f (a j : Sphere) z, ?_, hf30, Or.inr ⟨rfl, hg⟩⟩
    omega

/-- All possible ratios, before fixing the multiplicity and orientation
on an infinite subsequence. -/
noncomputable def boundedMarkedRatios : Finset ℂ :=
  (Finset.Icc (2 : ℕ) 30).image (fun m : ℕ => (m : ℂ)) ∪
    (Finset.Icc (2 : ℕ) 30).image (fun m : ℕ => (1 : ℂ) / m)

theorem boundedMarkedRatios_card_le : boundedMarkedRatios.card ≤ 58 := by
  have hleft : ((Finset.Icc (2 : ℕ) 30).image (fun m : ℕ => (m : ℂ))).card ≤ 29 := by
    exact (Finset.card_image_le).trans (by decide : (Finset.Icc (2 : ℕ) 30).card ≤ 29)
  have hright : ((Finset.Icc (2 : ℕ) 30).image (fun m : ℕ => (1 : ℂ) / m)).card ≤ 29 := by
    exact (Finset.card_image_le).trans (by decide : (Finset.Icc (2 : ℕ) 30).card ≤ 29)
  unfold boundedMarkedRatios
  exact (Finset.card_union_le _ _).trans (by omega)

/-- The actual quotient of the two positive marked local degrees lies
in this fixed finite set. -/
theorem NormalizedPair.boundedMarkedDefect_ratio_mem
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} (hp : NormalizedPair univ f g a)
    {j : Fin 3} {z : ℂ} (hz : IsBoundedMarkedDefect a f g j z) :
    (mult f (a j : Sphere) z : ℂ) / mult g (a j : Sphere) z ∈ boundedMarkedRatios := by
  obtain ⟨m, hm2, hm30, hcases⟩ := hp.boundedMarkedDefect_multiplicities hz
  have hm : m ∈ Finset.Icc (2 : ℕ) 30 := Finset.mem_Icc.mpr ⟨hm2, hm30⟩
  rcases hcases with ⟨hf, hg⟩ | ⟨hf, hg⟩
  · rw [hf, hg, Nat.cast_one]
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨m, hm, rfl⟩)
  · rw [hf, hg, Nat.cast_one, div_one]
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨m, hm, rfl⟩)

end ThreeIM
