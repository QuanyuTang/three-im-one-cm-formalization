module

public import RequestProject.ThreeIM.CyclotomicReal
public import RequestProject.ThreeIM.CharacterCertificates.Tables

/-!
# The exceptional character classes (Lemma 9.21)

Types of finite common points are encoded by positive rationals: the unit type by `1`, the
exterior type `k+` by `k`, and the interior type `k-` by `1/k` (`2 ≤ k < 5h`); the corresponding
radical is `x^{1/h}`.  Two types `x, y` lie in the same character class over `E_h = ℚ(ζ_h)`
exactly when the positive real quotient `(x/y)^{1/h}` of their radicals belongs to `E_h`
(the criterion of Lemma 9.17); this is `SameCharacter h ζ x y`.

For `h ∈ {3, 4, 8}` we determine all classes, confirming the table of Lemma 9.21.
-/

@[expose] public section

open Polynomial IntermediateField

namespace ThreeIM

/-- Two types have the same character over `E_h = ℚ(ζ)`: the positive `h`-th root of `x/y`
lies in `ℚ(ζ)`. -/
def SameCharacter (h : ℕ) (ζ : ℂ) (x y : ℚ) : Prop :=
  ∃ β : ℝ, 0 < β ∧ β ^ h = ((x / y : ℚ) : ℝ) ∧ (β : ℂ) ∈ ℚ⟮ζ⟯

/-- A positive rational is the `m`-th power of a positive rational iff its numerator and
denominator are `m`-th powers (with the search bounded by `B`). -/
theorem exists_rat_pow_iff {m B : ℕ} (hm : 0 < m) {r : ℚ} (hr : 0 < r)
    (hnum : r.num.natAbs < B ^ m) (hden : r.den < B ^ m) :
    (∃ q : ℚ, 0 < q ∧ q ^ m = r) ↔ IsRatPowB m B r := by
  constructor
  · rintro ⟨q, -, rfl⟩
    have hlt : ∀ n : ℕ, n ^ m < B ^ m → n < B := fun n hn =>
      (Nat.pow_lt_pow_iff_left hm.ne').1 hn
    refine ⟨q.num.natAbs, Finset.mem_range.2 (hlt _ ?_), q.den, Finset.mem_range.2 (hlt _ ?_),
      ?_, ?_⟩
    · rwa [Rat.num_pow, Int.natAbs_pow] at hnum
    · rwa [Rat.den_pow] at hden
    · rw [Rat.num_pow, Int.natAbs_pow]
    · rw [Rat.den_pow]
  · rintro ⟨n, -, d, -, hn, hd⟩
    have hd0 : d ≠ 0 := by
      rintro rfl; rw [zero_pow hm.ne'] at hd; exact r.den_nz hd.symm
    have hnum0 : 0 < r.num := Rat.num_pos.2 hr
    have hn0 : n ≠ 0 := by
      rintro rfl; rw [zero_pow hm.ne'] at hn; omega
    refine ⟨n / d, by positivity, ?_⟩
    rw [div_pow]
    have h1 : ((n ^ m : ℕ) : ℚ) = r.num := by
      rw [hn, Nat.cast_natAbs, abs_of_pos hnum0]
    have h2 : ((d ^ m : ℕ) : ℚ) = r.den := by rw [hd]
    push_cast at h1 h2
    rw [h1, h2, Rat.num_div_den]

/-- For `h ∈ {3, 4}`: two types have the same character iff `x/y` is the `h`-th power of a
positive rational (because `E_h ∩ ℝ = ℚ`). -/
theorem sameCharacter_iff_small {h : ℕ} (hh : h = 3 ∨ h = 4) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ h)
    (x y : ℚ) : SameCharacter h ζ x y ↔ ∃ q : ℚ, 0 < q ∧ q ^ h = x / y := by
  constructor
  · rintro ⟨β, hβ, hβh, hmem⟩
    obtain ⟨q, rfl⟩ := real_mem_cyclotomic_small (by tauto) hζ hmem
    exact ⟨q, by exact_mod_cast hβ, by exact_mod_cast hβh⟩
  · rintro ⟨q, hq, hqh⟩
    refine ⟨q, by exact_mod_cast hq, by rw [← hqh]; push_cast; rfl, ?_⟩
    rw [Complex.ofReal_ratCast, ← eq_ratCast (algebraMap ℚ ℂ)]
    exact IntermediateField.algebraMap_mem _ q

/-- For `h = 8`: two types have the same character iff `x/y` or `x/(16y)` is the eighth power
of a positive rational (because `E_8 ∩ ℝ = ℚ(√2)`). -/
theorem sameCharacter_iff_eight {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 8) (x y : ℚ) :
    SameCharacter 8 ζ x y ↔
      (∃ q : ℚ, 0 < q ∧ q ^ 8 = x / y) ∨ ∃ q : ℚ, 0 < q ∧ q ^ 8 = x / (16 * y) := by
  have hratmem : ∀ q : ℚ, ((q : ℝ) : ℂ) ∈ ℚ⟮ζ⟯ := fun q => by
    rw [Complex.ofReal_ratCast, ← eq_ratCast (algebraMap ℚ ℂ)]
    exact IntermediateField.algebraMap_mem _ q
  have hs2 : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs8 : (√2 : ℝ) ^ 8 = 16 := by
    rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, hs2]; norm_num
  constructor
  · rintro ⟨β, hβ, hβh, hmem⟩
    obtain ⟨u, v, huv⟩ := real_mem_cyclotomic_eight hζ hmem
    obtain ⟨-, s, hs⟩ := real_radical_cyclotomic (by norm_num) hζ hβh hmem
    have h0 : u * v = 0 := by
      by_contra hne
      apply irrational_sqrt_two
      refine ⟨(s - u ^ 2 - 2 * v ^ 2) / (2 * u * v), ?_⟩
      have hne' : (2 * u * v : ℝ) ≠ 0 := by
        have : ((u * v : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hne
        push_cast at this; intro h; apply this; linarith
      push_cast
      rw [div_eq_iff hne', ← hs, huv]
      linear_combination ((v : ℝ) ^ 2) * hs2
    rcases mul_eq_zero.1 h0 with hu | hv
    · right
      subst hu
      refine ⟨|v|, ?_, ?_⟩
      · rcases eq_or_ne v 0 with rfl | hv0
        · simp at huv; linarith
        · exact abs_pos.2 hv0
      · have : ((|v| ^ 8 : ℚ) : ℝ) = ((x / (16 * y) : ℚ) : ℝ) := by
          have h16 : ((x / (16 * y) : ℚ) : ℝ) = ((x / y : ℚ) : ℝ) / 16 := by
            push_cast; ring
          rw [h16, ← hβh, huv]
          push_cast
          rw [zero_add, mul_pow, hs8, Even.pow_abs ⟨4, rfl⟩]; ring
        exact_mod_cast this
    · left
      subst hv
      refine ⟨u, ?_, ?_⟩
      · have : (0 : ℝ) < u := by simpa [huv] using hβ
        exact_mod_cast this
      · have : ((u ^ 8 : ℚ) : ℝ) = ((x / y : ℚ) : ℝ) := by rw [← hβh, huv]; push_cast; ring
        exact_mod_cast this
  · rintro (⟨q, hq, hqh⟩ | ⟨q, hq, hqh⟩)
    · exact ⟨q, by exact_mod_cast hq, by rw [← hqh]; push_cast; rfl, hratmem q⟩
    · refine ⟨q * √2, by positivity, ?_, ?_⟩
      · rw [mul_pow, hs8]
        have : ((q ^ 8 : ℚ) : ℝ) = ((x / (16 * y) : ℚ) : ℝ) := by rw [hqh]
        push_cast at this ⊢
        rw [this]; field_simp
      · push_cast
        exact mul_mem (hratmem q) (sqrt_two_mem_cyclotomic_eight hζ)

/-- **Lemma 9.21** (the exceptional character classes), `h = 3`: two permitted types have the
same character over `E_3` iff they are equal or lie in one of the classes
`{1, 8+, 8-}, {2+, 4-}, {2-, 4+}, {3+, 9-}, {3-, 9+}`. -/
theorem character_classes_three {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 3) :
    ∀ x ∈ typeSet 3, ∀ y ∈ typeSet 3,
      (SameCharacter 3 ζ x y ↔ x = y ∨ ∃ C ∈ classes3, x ∈ C ∧ y ∈ C) := by
  intro x hx y hy
  obtain ⟨⟨hpos, hn, hd⟩, htab⟩ := table3_check x hx y hy
  rw [sameCharacter_iff_small (Or.inl rfl) hζ, exists_rat_pow_iff (by norm_num) hpos hn hd, htab]

/-- **Lemma 9.21**, `h = 4`: the classes are
`{1, 16+, 16-}, {2+, 8-}, {2-, 8+}, {4+, 4-}, {9+, 9-}`. -/
theorem character_classes_four {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 4) :
    ∀ x ∈ typeSet 4, ∀ y ∈ typeSet 4,
      (SameCharacter 4 ζ x y ↔ x = y ∨ ∃ C ∈ classes4, x ∈ C ∧ y ∈ C) := by
  intro x hx y hy
  obtain ⟨⟨hpos, hn, hd⟩, htab⟩ := table4_check x hx y hy
  rw [sameCharacter_iff_small (Or.inr rfl) hζ, exists_rat_pow_iff (by norm_num) hpos hn hd, htab]

/-- **Lemma 9.21**, `h = 8`: the classes are
`{1, 16+, 16-}, {2+, 32+, 8-}, {2-, 32-, 8+}, {4+, 4-}`. -/
theorem character_classes_eight {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 8) :
    ∀ x ∈ typeSet 8, ∀ y ∈ typeSet 8,
      (SameCharacter 8 ζ x y ↔ x = y ∨ ∃ C ∈ classes8, x ∈ C ∧ y ∈ C) := by
  intro x hx y hy
  obtain ⟨⟨hpos, hn, hd⟩, ⟨hpos', hn', hd'⟩, htab⟩ := table8_check x hx y hy
  rw [sameCharacter_iff_eight hζ, exists_rat_pow_iff (by norm_num) hpos hn hd,
    exists_rat_pow_iff (by norm_num) hpos' hn' hd', htab]

end ThreeIM
