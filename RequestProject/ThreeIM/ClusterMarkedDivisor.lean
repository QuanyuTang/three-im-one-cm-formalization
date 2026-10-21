module

public import RequestProject.ThreeIM.DefectCounting

/-!
# The genuine bounded-multiplicity marked divisor

The selection argument retains defects away from the zero divisor of Psi,
with both marked multiplicities at most thirty. This is a sub-divisor of
the actual germ-based defect divisor, with no choice of point values for
the meromorphic auxiliary functions.
-/

@[expose] public section

set_option autoImplicit false

open Set ValueDistribution Classical
open scoped BigOperators

namespace ThreeIM

/-- A marked defect eligible for the finite family of multiplicity ratios. -/
def IsBoundedMarkedDefect (a : Fin 3 → ℂ) (f g : ℂ → ℂ) (j : Fin 3) (z : ℂ) : Prop :=
  IsDefect f g (a j : Sphere) z ∧ meromorphicOrderAt (auxPsi a f g) z = 0 ∧
    max (mult f (a j : Sphere) z) (mult g (a j : Sphere) z) ≤ 30

/-- Restrict the actual defect divisor by the marked-defect predicate,
keeping a global locally finite divisor so that logarithmic counting
retains the original compensation at the origin. -/
noncomputable def markedDefectDivisor (a : Fin 3 → ℂ) (f g : ℂ → ℂ) (j : Fin 3) :
    Function.locallyFinsupp ℂ ℤ where
  toFun z := if IsBoundedMarkedDefect a f g j z then defectDivisor f g (a j : Sphere) z else 0
  supportWithinDomain' := subset_univ _
  supportLocallyFiniteWithinDomain' := by
    intro z hz
    obtain ⟨t, ht, hfin⟩ := (defectDivisor f g (a j : Sphere)).supportLocallyFiniteWithinDomain z hz
    refine ⟨t, ht, hfin.subset ?_⟩
    intro w hw
    refine ⟨hw.1, ?_⟩
    intro hzero
    exact hw.2 (by simp only [hzero, ite_self])

@[simp] theorem markedDefectDivisor_apply (a : Fin 3 → ℂ) (f g : ℂ → ℂ)
    (j : Fin 3) (z : ℂ) :
    markedDefectDivisor a f g j z =
      if IsBoundedMarkedDefect a f g j z then defectDivisor f g (a j : Sphere) z else 0 := rfl

theorem markedDefectDivisor_nonneg (a : Fin 3 → ℂ) (f g : ℂ → ℂ) (j : Fin 3) :
    0 ≤ markedDefectDivisor a f g j := by
  intro z
  rw [markedDefectDivisor_apply]
  split_ifs
  · exact defectDivisor_nonneg f g (a j : Sphere) z
  · exact le_refl 0

theorem markedDefectDivisor_le (a : Fin 3 → ℂ) (f g : ℂ → ℂ) (j : Fin 3) :
    markedDefectDivisor a f g j ≤ defectDivisor f g (a j : Sphere) := by
  intro z
  rw [markedDefectDivisor_apply]
  split_ifs
  · exact le_refl _
  · exact defectDivisor_nonneg f g (a j : Sphere) z

/-- For a normalized pair the retained coefficient is exactly its honest
marked-defect indicator. -/
theorem NormalizedPair.markedDefectDivisor_apply {a : Fin 3 → ℂ} {f g : ℂ → ℂ}
    (hp : NormalizedPair univ f g a) (j : Fin 3) (z : ℂ) :
    markedDefectDivisor a f g j z = if IsBoundedMarkedDefect a f g j z then 1 else 0 := by
  classical
  rw [ThreeIM.markedDefectDivisor_apply,
    defectDivisor_apply_of_im hp.nonconst_f.1 hp.nonconst_g.1 (hp.im j)]
  by_cases h : IsBoundedMarkedDefect a f g j z
  · simp only [h, h.1, ↓reduceIte]
  · simp only [h, ↓reduceIte]

theorem NormalizedPair.markedDefectDivisor_le_one {a : Fin 3 → ℂ} {f g : ℂ → ℂ}
    (hp : NormalizedPair univ f g a) (j : Fin 3) (z : ℂ) :
    markedDefectDivisor a f g j z ≤ 1 := by
  rw [hp.markedDefectDivisor_apply]
  split_ifs <;> norm_num

/-- The total retained divisor over all three marked targets. -/
noncomputable def totalMarkedDefectDivisor (a : Fin 3 → ℂ) (f g : ℂ → ℂ) :
    Function.locallyFinsupp ℂ ℤ := ∑ j, markedDefectDivisor a f g j

@[simp] theorem totalMarkedDefectDivisor_apply (a : Fin 3 → ℂ) (f g : ℂ → ℂ) (z : ℂ) :
    totalMarkedDefectDivisor a f g z = ∑ j, markedDefectDivisor a f g j z := by
  simp only [totalMarkedDefectDivisor, Fin.sum_univ_three,
    Function.locallyFinsuppWithin.coe_add, Pi.add_apply]

theorem totalMarkedDefectDivisor_nonneg (a : Fin 3 → ℂ) (f g : ℂ → ℂ) :
    0 ≤ totalMarkedDefectDivisor a f g := by
  intro z
  rw [totalMarkedDefectDivisor_apply]
  exact Finset.sum_nonneg fun j _ => markedDefectDivisor_nonneg a f g j z

/-- The total coefficient is at most three; no disjointness shortcut for
the three germ-based finite fibers is needed in the counting estimate. -/
theorem NormalizedPair.totalMarkedDefectDivisor_le_three {a : Fin 3 → ℂ} {f g : ℂ → ℂ}
    (hp : NormalizedPair univ f g a) (z : ℂ) : totalMarkedDefectDivisor a f g z ≤ 3 := by
  rw [totalMarkedDefectDivisor_apply]
  calc
    _ ≤ ∑ _j : Fin 3, (1 : ℤ) := Finset.sum_le_sum fun j _ => hp.markedDefectDivisor_le_one j z
    _ = 3 := by simp

/-- Every point in the retained support has a genuine bounded marked
defect over one of the original three values. -/
theorem NormalizedPair.exists_markedDefect_of_total_ne_zero {a : Fin 3 → ℂ} {f g : ℂ → ℂ}
    (hp : NormalizedPair univ f g a) {z : ℂ}
    (hz : totalMarkedDefectDivisor a f g z ≠ 0) : ∃ j, IsBoundedMarkedDefect a f g j z := by
  classical
  by_contra h
  push_neg at h
  apply hz
  rw [totalMarkedDefectDivisor_apply]
  apply Finset.sum_eq_zero
  intro j _
  rw [hp.markedDefectDivisor_apply, if_neg (h j)]

/-- A nonzero order of the entire auxiliary Psi consumes at least one
unit of its genuine positive divisor. Finite order is used explicitly. -/
theorem NormalizedPair.one_le_auxPsi_posDivisor {a : Fin 3 → ℂ} {f g : ℂ → ℂ}
    (hp : NormalizedPair univ f g a) {z : ℂ}
    (hpsi : meromorphicOrderAt (auxPsi a f g) z ≠ 0) :
    1 ≤ (MeromorphicOn.divisor (auxPsi a f g) univ)⁺ z := by
  have hPm : MeromorphicOn (auxPsi a f g) univ := by
    intro w _
    have hfm := hp.nonconst_f.1 w (mem_univ w)
    have hgm := hp.nonconst_g.1 w (mem_univ w)
    unfold auxPsi auxU auxV cubicP
    fun_prop
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 (hp.order_aux (mem_univ z)).2.2.2
  have hn0 : (0 : ℤ) ≤ n := by
    have h := (hp.order_aux (mem_univ z)).2.2.1
    rw [← hn] at h
    exact_mod_cast h
  have hnne : n ≠ 0 := by
    intro h
    apply hpsi
    rw [← hn, h]
    rfl
  rw [Function.locallyFinsuppWithin.posPart_apply,
    MeromorphicOn.divisor_apply hPm (mem_univ z),
    ← hn, WithTop.untop₀_coe, posPart_def]
  omega

/-- Every discarded defect is charged either to its large full fiber
multiplicity or to a zero of Psi. This is the pointwise source of the
32-denominator in the marked-density estimate. -/
theorem NormalizedPair.defect_le_marked_fibers_auxPsi {a : Fin 3 → ℂ} {f g : ℂ → ℂ}
    (hp : NormalizedPair univ f g a) (j : Fin 3) :
    32 • defectDivisor f g (a j : Sphere) ≤
      32 • markedDefectDivisor a f g j + fiberDivisor f (a j : Sphere) +
        fiberDivisor g (a j : Sphere) + 32 • (MeromorphicOn.divisor (auxPsi a f g) univ)⁺ := by
  classical
  intro z
  simp only [Function.locallyFinsuppWithin.coe_add, Function.locallyFinsuppWithin.coe_nsmul,
    Pi.add_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
  rw [defectDivisor_apply_of_im hp.nonconst_f.1 hp.nonconst_g.1 (hp.im j),
    hp.markedDefectDivisor_apply, fiberDivisor_apply hp.nonconst_f.1,
    fiberDivisor_apply hp.nonconst_g.1]
  have hP : 0 ≤ (MeromorphicOn.divisor (auxPsi a f g) univ)⁺ z := by
    rw [Function.locallyFinsuppWithin.posPart_apply]
    exact posPart_nonneg _
  by_cases hd : IsDefect f g (a j : Sphere) z
  · rw [if_pos hd]
    by_cases hm : IsBoundedMarkedDefect a f g j z
    · rw [if_pos hm]
      omega
    · rw [if_neg hm]
      by_cases hpsi : meromorphicOrderAt (auxPsi a f g) z = 0
      · have hlarge : 30 < max (mult f (a j : Sphere) z) (mult g (a j : Sphere) z) := by
          apply lt_of_not_ge
          exact fun h => hm ⟨hd, hpsi, h⟩
        have hf := hd.1
        have hg := hd.2.1
        omega
      · have hP1 := hp.one_le_auxPsi_posDivisor hpsi
        omega
  · rw [if_neg hd]
    split_ifs <;> omega

end ThreeIM
