module

public import RequestProject.ThreeIM.CharacterCertificates.Order3Batch1
public import RequestProject.ThreeIM.CharacterCertificates.Order3Batch2
public import RequestProject.ThreeIM.CharacterCertificates.Order3Batch3
public import RequestProject.ThreeIM.CharacterCertificates.Order3Batch4
public import RequestProject.ThreeIM.CharacterCertificates.Order3Batch5
public import RequestProject.ThreeIM.CharacterCertificates.Order3Batch6
public import RequestProject.ThreeIM.CharacterCertificates.Order3Batch7
public import RequestProject.ThreeIM.CharacterCertificates.Order4Batch1
public import RequestProject.ThreeIM.CharacterCertificates.Order4Batch2
public import RequestProject.ThreeIM.CharacterCertificates.Order4Batch3
public import RequestProject.ThreeIM.CharacterCertificates.Order4Batch4
public import RequestProject.ThreeIM.CharacterCertificates.Order4Batch5
public import RequestProject.ThreeIM.CharacterCertificates.Order4Batch6
public import RequestProject.ThreeIM.CharacterCertificates.Order4Batch7
public import RequestProject.ThreeIM.CharacterCertificates.Order4Batch8
public import RequestProject.ThreeIM.CharacterCertificates.Order4Batch9
public import RequestProject.ThreeIM.CharacterCertificates.Order4Batch10
public import RequestProject.ThreeIM.CharacterCertificates.Order8Batch1
public import RequestProject.ThreeIM.CharacterCertificates.Order8Batch2
public import RequestProject.ThreeIM.CharacterCertificates.Order8Batch3
public import RequestProject.ThreeIM.CharacterCertificates.Order8Batch4
public import RequestProject.ThreeIM.CharacterCertificates.Order8Batch5
public import RequestProject.ThreeIM.CharacterCertificates.Order8Batch6
public import RequestProject.ThreeIM.CharacterCertificates.Order8Batch7
public import RequestProject.ThreeIM.CharacterCertificates.Order8Batch8
public import RequestProject.ThreeIM.CharacterCertificates.Order8Batch9
public import RequestProject.ThreeIM.CharacterCertificates.Order8Batch10
public import RequestProject.ThreeIM.CharacterCertificates.Order8Batch11
public import RequestProject.ThreeIM.CharacterCertificates.Order8Batch12
public import RequestProject.ThreeIM.CharacterCertificates.Order8Batch13
public import RequestProject.ThreeIM.CharacterCertificates.Order8Batch14
public import RequestProject.ThreeIM.CharacterCertificates.Order8Batch15
public import RequestProject.ThreeIM.CharacterCertificates.Order8Batch16
public import RequestProject.ThreeIM.CharacterCertificates.Order8Batch17
public import RequestProject.ThreeIM.CharacterCertificates.Order8Batch18
public import RequestProject.ThreeIM.CharacterCertificates.Order8Batch19
public import RequestProject.ThreeIM.CharacterCertificates.Order8Batch20

/-!
# Kernel checked finite character tables

The batches prove every permitted rational pair. The public table statements are
exactly those of the original formalization; only their certificates are reorganized.
-/

@[expose] public section

namespace ThreeIM

open CharacterCertificates

private theorem table3_from_rows : ∀ x ∈ typeSet 3, tableRow3 x := by
  intro x hx
  simp only [typeSet, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hx
  rcases hx with rfl | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
  · exact table3_row_one
  · fin_cases hk
    · exact table3_row_nat_2
    · exact table3_row_nat_3
    · exact table3_row_nat_4
    · exact table3_row_nat_5
    · exact table3_row_nat_6
    · exact table3_row_nat_7
    · exact table3_row_nat_8
    · exact table3_row_nat_9
    · exact table3_row_nat_10
    · exact table3_row_nat_11
    · exact table3_row_nat_12
    · exact table3_row_nat_13
    · exact table3_row_nat_14
  · fin_cases hk
    · exact table3_row_inv_2
    · exact table3_row_inv_3
    · exact table3_row_inv_4
    · exact table3_row_inv_5
    · exact table3_row_inv_6
    · exact table3_row_inv_7
    · exact table3_row_inv_8
    · exact table3_row_inv_9
    · exact table3_row_inv_10
    · exact table3_row_inv_11
    · exact table3_row_inv_12
    · exact table3_row_inv_13
    · exact table3_row_inv_14

set_option maxRecDepth 100000 in
theorem table3_check : ∀ x ∈ typeSet 3, ∀ y ∈ typeSet 3,
    (0 < x / y ∧ (x / y).num.natAbs < 6 ^ 3 ∧ (x / y).den < 6 ^ 3) ∧
    (IsRatPowB 3 6 (x / y) ↔ x = y ∨ ∃ C ∈ classes3, x ∈ C ∧ y ∈ C) := by
  exact table3_from_rows

private theorem table4_from_rows : ∀ x ∈ typeSet 4, tableRow4 x := by
  intro x hx
  simp only [typeSet, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hx
  rcases hx with rfl | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
  · exact table4_row_one
  · fin_cases hk
    · exact table4_row_nat_2
    · exact table4_row_nat_3
    · exact table4_row_nat_4
    · exact table4_row_nat_5
    · exact table4_row_nat_6
    · exact table4_row_nat_7
    · exact table4_row_nat_8
    · exact table4_row_nat_9
    · exact table4_row_nat_10
    · exact table4_row_nat_11
    · exact table4_row_nat_12
    · exact table4_row_nat_13
    · exact table4_row_nat_14
    · exact table4_row_nat_15
    · exact table4_row_nat_16
    · exact table4_row_nat_17
    · exact table4_row_nat_18
    · exact table4_row_nat_19
  · fin_cases hk
    · exact table4_row_inv_2
    · exact table4_row_inv_3
    · exact table4_row_inv_4
    · exact table4_row_inv_5
    · exact table4_row_inv_6
    · exact table4_row_inv_7
    · exact table4_row_inv_8
    · exact table4_row_inv_9
    · exact table4_row_inv_10
    · exact table4_row_inv_11
    · exact table4_row_inv_12
    · exact table4_row_inv_13
    · exact table4_row_inv_14
    · exact table4_row_inv_15
    · exact table4_row_inv_16
    · exact table4_row_inv_17
    · exact table4_row_inv_18
    · exact table4_row_inv_19

set_option maxRecDepth 100000 in
theorem table4_check : ∀ x ∈ typeSet 4, ∀ y ∈ typeSet 4,
    (0 < x / y ∧ (x / y).num.natAbs < 5 ^ 4 ∧ (x / y).den < 5 ^ 4) ∧
    (IsRatPowB 4 5 (x / y) ↔ x = y ∨ ∃ C ∈ classes4, x ∈ C ∧ y ∈ C) := by
  exact table4_from_rows

private theorem table8_from_rows : ∀ x ∈ typeSet 8, tableRow8 x := by
  intro x hx
  simp only [typeSet, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hx
  rcases hx with rfl | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
  · exact table8_row_one
  · fin_cases hk
    · exact table8_row_nat_2
    · exact table8_row_nat_3
    · exact table8_row_nat_4
    · exact table8_row_nat_5
    · exact table8_row_nat_6
    · exact table8_row_nat_7
    · exact table8_row_nat_8
    · exact table8_row_nat_9
    · exact table8_row_nat_10
    · exact table8_row_nat_11
    · exact table8_row_nat_12
    · exact table8_row_nat_13
    · exact table8_row_nat_14
    · exact table8_row_nat_15
    · exact table8_row_nat_16
    · exact table8_row_nat_17
    · exact table8_row_nat_18
    · exact table8_row_nat_19
    · exact table8_row_nat_20
    · exact table8_row_nat_21
    · exact table8_row_nat_22
    · exact table8_row_nat_23
    · exact table8_row_nat_24
    · exact table8_row_nat_25
    · exact table8_row_nat_26
    · exact table8_row_nat_27
    · exact table8_row_nat_28
    · exact table8_row_nat_29
    · exact table8_row_nat_30
    · exact table8_row_nat_31
    · exact table8_row_nat_32
    · exact table8_row_nat_33
    · exact table8_row_nat_34
    · exact table8_row_nat_35
    · exact table8_row_nat_36
    · exact table8_row_nat_37
    · exact table8_row_nat_38
    · exact table8_row_nat_39
  · fin_cases hk
    · exact table8_row_inv_2
    · exact table8_row_inv_3
    · exact table8_row_inv_4
    · exact table8_row_inv_5
    · exact table8_row_inv_6
    · exact table8_row_inv_7
    · exact table8_row_inv_8
    · exact table8_row_inv_9
    · exact table8_row_inv_10
    · exact table8_row_inv_11
    · exact table8_row_inv_12
    · exact table8_row_inv_13
    · exact table8_row_inv_14
    · exact table8_row_inv_15
    · exact table8_row_inv_16
    · exact table8_row_inv_17
    · exact table8_row_inv_18
    · exact table8_row_inv_19
    · exact table8_row_inv_20
    · exact table8_row_inv_21
    · exact table8_row_inv_22
    · exact table8_row_inv_23
    · exact table8_row_inv_24
    · exact table8_row_inv_25
    · exact table8_row_inv_26
    · exact table8_row_inv_27
    · exact table8_row_inv_28
    · exact table8_row_inv_29
    · exact table8_row_inv_30
    · exact table8_row_inv_31
    · exact table8_row_inv_32
    · exact table8_row_inv_33
    · exact table8_row_inv_34
    · exact table8_row_inv_35
    · exact table8_row_inv_36
    · exact table8_row_inv_37
    · exact table8_row_inv_38
    · exact table8_row_inv_39

set_option maxRecDepth 100000 in
theorem table8_check : ∀ x ∈ typeSet 8, ∀ y ∈ typeSet 8,
    (0 < x / y ∧ (x / y).num.natAbs < 4 ^ 8 ∧ (x / y).den < 4 ^ 8) ∧
    (0 < x / (16 * y) ∧ (x / (16 * y)).num.natAbs < 4 ^ 8 ∧ (x / (16 * y)).den < 4 ^ 8) ∧
    (IsRatPowB 8 4 (x / y) ∨ IsRatPowB 8 4 (x / (16 * y)) ↔
      x = y ∨ ∃ C ∈ classes8, x ∈ C ∧ y ∈ C) := by
  exact table8_from_rows

end ThreeIM
