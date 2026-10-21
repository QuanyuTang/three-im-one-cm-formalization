module

public import RequestProject.ThreeIM.CharacterCertificates.Data
public import Mathlib.Tactic.FinCases

/-!
# Character table of order 8: certificate batch 1

Each rational pair is checked separately by the Lean kernel. No native evaluation
or additional axioms are used. This batch contains at most four complete rows.
-/

@[expose] public section

set_option Elab.async false
set_option maxHeartbeats 0

namespace ThreeIM.CharacterCertificates

set_option maxRecDepth 100000 in
theorem table8_row_one : tableRow8 1 := by
  unfold tableRow8
  intro y hy
  simp only [typeSet, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hy
  rcases hy with rfl | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
  · (simp only [isRatPowB8_iff, classes8, Finset.exists_mem_insert]; simp only [Finset.mem_singleton, exists_eq_left]; simp only [Finset.mem_insert, Finset.mem_singleton]; decide +kernel)
  · fin_cases hk <;>
      (simp only [isRatPowB8_iff, classes8, Finset.exists_mem_insert]; simp only [Finset.mem_singleton, exists_eq_left]; simp only [Finset.mem_insert, Finset.mem_singleton]; decide +kernel)
  · fin_cases hk <;>
      (simp only [isRatPowB8_iff, classes8, Finset.exists_mem_insert]; simp only [Finset.mem_singleton, exists_eq_left]; simp only [Finset.mem_insert, Finset.mem_singleton]; decide +kernel)

set_option maxRecDepth 100000 in
theorem table8_row_nat_2 : tableRow8 2 := by
  unfold tableRow8
  intro y hy
  simp only [typeSet, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hy
  rcases hy with rfl | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
  · (simp only [isRatPowB8_iff, classes8, Finset.exists_mem_insert]; simp only [Finset.mem_singleton, exists_eq_left]; simp only [Finset.mem_insert, Finset.mem_singleton]; decide +kernel)
  · fin_cases hk <;>
      (simp only [isRatPowB8_iff, classes8, Finset.exists_mem_insert]; simp only [Finset.mem_singleton, exists_eq_left]; simp only [Finset.mem_insert, Finset.mem_singleton]; decide +kernel)
  · fin_cases hk <;>
      (simp only [isRatPowB8_iff, classes8, Finset.exists_mem_insert]; simp only [Finset.mem_singleton, exists_eq_left]; simp only [Finset.mem_insert, Finset.mem_singleton]; decide +kernel)

set_option maxRecDepth 100000 in
theorem table8_row_nat_3 : tableRow8 3 := by
  unfold tableRow8
  intro y hy
  simp only [typeSet, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hy
  rcases hy with rfl | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
  · (simp only [isRatPowB8_iff, classes8, Finset.exists_mem_insert]; simp only [Finset.mem_singleton, exists_eq_left]; simp only [Finset.mem_insert, Finset.mem_singleton]; decide +kernel)
  · fin_cases hk <;>
      (simp only [isRatPowB8_iff, classes8, Finset.exists_mem_insert]; simp only [Finset.mem_singleton, exists_eq_left]; simp only [Finset.mem_insert, Finset.mem_singleton]; decide +kernel)
  · fin_cases hk <;>
      (simp only [isRatPowB8_iff, classes8, Finset.exists_mem_insert]; simp only [Finset.mem_singleton, exists_eq_left]; simp only [Finset.mem_insert, Finset.mem_singleton]; decide +kernel)

set_option maxRecDepth 100000 in
theorem table8_row_nat_4 : tableRow8 4 := by
  unfold tableRow8
  intro y hy
  simp only [typeSet, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hy
  rcases hy with rfl | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
  · (simp only [isRatPowB8_iff, classes8, Finset.exists_mem_insert]; simp only [Finset.mem_singleton, exists_eq_left]; simp only [Finset.mem_insert, Finset.mem_singleton]; decide +kernel)
  · fin_cases hk <;>
      (simp only [isRatPowB8_iff, classes8, Finset.exists_mem_insert]; simp only [Finset.mem_singleton, exists_eq_left]; simp only [Finset.mem_insert, Finset.mem_singleton]; decide +kernel)
  · fin_cases hk <;>
      (simp only [isRatPowB8_iff, classes8, Finset.exists_mem_insert]; simp only [Finset.mem_singleton, exists_eq_left]; simp only [Finset.mem_insert, Finset.mem_singleton]; decide +kernel)

end ThreeIM.CharacterCertificates
