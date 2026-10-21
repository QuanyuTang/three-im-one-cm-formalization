module

public import RequestProject.ThreeIM.CharacterCertificates.Data
public import Mathlib.Tactic.FinCases

/-!
# Character table of order 3: certificate batch 2

Each rational pair is checked separately by the Lean kernel. No native evaluation
or additional axioms are used. This batch contains at most four complete rows.
-/

@[expose] public section

set_option Elab.async false
set_option maxHeartbeats 0

namespace ThreeIM.CharacterCertificates

set_option maxRecDepth 100000 in
theorem table3_row_nat_5 : tableRow3 5 := by
  unfold tableRow3
  intro y hy
  simp only [typeSet, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hy
  rcases hy with rfl | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
  · (simp only [isRatPowB3_iff, classes3, Finset.exists_mem_insert]; simp only [Finset.mem_singleton, exists_eq_left]; simp only [Finset.mem_insert, Finset.mem_singleton]; decide +kernel)
  · fin_cases hk <;>
      (simp only [isRatPowB3_iff, classes3, Finset.exists_mem_insert]; simp only [Finset.mem_singleton, exists_eq_left]; simp only [Finset.mem_insert, Finset.mem_singleton]; decide +kernel)
  · fin_cases hk <;>
      (simp only [isRatPowB3_iff, classes3, Finset.exists_mem_insert]; simp only [Finset.mem_singleton, exists_eq_left]; simp only [Finset.mem_insert, Finset.mem_singleton]; decide +kernel)

set_option maxRecDepth 100000 in
theorem table3_row_nat_6 : tableRow3 6 := by
  unfold tableRow3
  intro y hy
  simp only [typeSet, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hy
  rcases hy with rfl | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
  · (simp only [isRatPowB3_iff, classes3, Finset.exists_mem_insert]; simp only [Finset.mem_singleton, exists_eq_left]; simp only [Finset.mem_insert, Finset.mem_singleton]; decide +kernel)
  · fin_cases hk <;>
      (simp only [isRatPowB3_iff, classes3, Finset.exists_mem_insert]; simp only [Finset.mem_singleton, exists_eq_left]; simp only [Finset.mem_insert, Finset.mem_singleton]; decide +kernel)
  · fin_cases hk <;>
      (simp only [isRatPowB3_iff, classes3, Finset.exists_mem_insert]; simp only [Finset.mem_singleton, exists_eq_left]; simp only [Finset.mem_insert, Finset.mem_singleton]; decide +kernel)

set_option maxRecDepth 100000 in
theorem table3_row_nat_7 : tableRow3 7 := by
  unfold tableRow3
  intro y hy
  simp only [typeSet, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hy
  rcases hy with rfl | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
  · (simp only [isRatPowB3_iff, classes3, Finset.exists_mem_insert]; simp only [Finset.mem_singleton, exists_eq_left]; simp only [Finset.mem_insert, Finset.mem_singleton]; decide +kernel)
  · fin_cases hk <;>
      (simp only [isRatPowB3_iff, classes3, Finset.exists_mem_insert]; simp only [Finset.mem_singleton, exists_eq_left]; simp only [Finset.mem_insert, Finset.mem_singleton]; decide +kernel)
  · fin_cases hk <;>
      (simp only [isRatPowB3_iff, classes3, Finset.exists_mem_insert]; simp only [Finset.mem_singleton, exists_eq_left]; simp only [Finset.mem_insert, Finset.mem_singleton]; decide +kernel)

set_option maxRecDepth 100000 in
theorem table3_row_nat_8 : tableRow3 8 := by
  unfold tableRow3
  intro y hy
  simp only [typeSet, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hy
  rcases hy with rfl | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
  · (simp only [isRatPowB3_iff, classes3, Finset.exists_mem_insert]; simp only [Finset.mem_singleton, exists_eq_left]; simp only [Finset.mem_insert, Finset.mem_singleton]; decide +kernel)
  · fin_cases hk <;>
      (simp only [isRatPowB3_iff, classes3, Finset.exists_mem_insert]; simp only [Finset.mem_singleton, exists_eq_left]; simp only [Finset.mem_insert, Finset.mem_singleton]; decide +kernel)
  · fin_cases hk <;>
      (simp only [isRatPowB3_iff, classes3, Finset.exists_mem_insert]; simp only [Finset.mem_singleton, exists_eq_left]; simp only [Finset.mem_insert, Finset.mem_singleton]; decide +kernel)

end ThreeIM.CharacterCertificates
