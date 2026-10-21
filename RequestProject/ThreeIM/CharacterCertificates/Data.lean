module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.Finset.Image

/-!
# Finite data for the exceptional character classes

These definitions and the fixed power sets support the kernel checked certificates
for Lemma 9.21. The original definitions are unchanged. The table computation is
split across modules so the kernel can release its reduction caches between batches.
-/

@[expose] public section

namespace ThreeIM

/-- The permitted types for order `h`: `1`, `k` and `1/k` for `2 ≤ k < 5h`. -/
def typeSet (h : ℕ) : Finset ℚ :=
  insert 1 ((Finset.Ico 2 (5 * h)).image (fun k : ℕ => (k : ℚ)) ∪
    (Finset.Ico 2 (5 * h)).image (fun k : ℕ => 1 / (k : ℚ)))

/-- Bounded decidable test: numerator and denominator of `r` are `m`-th powers of integers
below `B`. -/
def IsRatPowB (m B : ℕ) (r : ℚ) : Prop :=
  ∃ n ∈ Finset.range B, ∃ d ∈ Finset.range B, n ^ m = r.num.natAbs ∧ d ^ m = r.den

instance (m B : ℕ) (r : ℚ) : Decidable (IsRatPowB m B r) := by
  unfold IsRatPowB; infer_instance

/-- The nonsingleton character classes for `h = 3` (Lemma 9.21). -/
def classes3 : Finset (Finset ℚ) := {{1, 8, 1/8}, {2, 1/4}, {4, 1/2}, {3, 1/9}, {9, 1/3}}

/-- The nonsingleton character classes for `h = 4` (Lemma 9.21). -/
def classes4 : Finset (Finset ℚ) := {{1, 16, 1/16}, {2, 1/8}, {8, 1/2}, {4, 1/4}, {9, 1/9}}

/-- The nonsingleton character classes for `h = 8` (Lemma 9.21). -/
def classes8 : Finset (Finset ℚ) := {{1, 16, 1/16}, {2, 32, 1/8}, {8, 1/2, 1/32}, {4, 1/4}}

namespace CharacterCertificates

theorem isRatPowB_image (m B : ℕ) (r : ℚ) :
    IsRatPowB m B r ↔
      r.num.natAbs ∈ (Finset.range B).image (fun n => n ^ m) ∧
      r.den ∈ (Finset.range B).image (fun n => n ^ m) := by
  constructor
  · rintro ⟨n, hn, d, hd, hnum, hden⟩
    exact ⟨Finset.mem_image.2 ⟨n, hn, hnum⟩, Finset.mem_image.2 ⟨d, hd, hden⟩⟩
  · rintro ⟨hnum, hden⟩
    obtain ⟨n, hn, hnum⟩ := Finset.mem_image.1 hnum
    obtain ⟨d, hd, hden⟩ := Finset.mem_image.1 hden
    exact ⟨n, hn, d, hd, hnum, hden⟩

theorem isRatPowB3_iff (r : ℚ) : IsRatPowB 3 6 r ↔
    r.num.natAbs ∈ ({0, 1, 8, 27, 64, 125} : Finset ℕ) ∧
      r.den ∈ ({0, 1, 8, 27, 64, 125} : Finset ℕ) := by
  have powers : (Finset.range 6).image (fun n => n ^ 3) =
      ({0, 1, 8, 27, 64, 125} : Finset ℕ) := by decide +kernel
  rw [isRatPowB_image, powers]

theorem isRatPowB4_iff (r : ℚ) : IsRatPowB 4 5 r ↔
    r.num.natAbs ∈ ({0, 1, 16, 81, 256} : Finset ℕ) ∧
      r.den ∈ ({0, 1, 16, 81, 256} : Finset ℕ) := by
  have powers : (Finset.range 5).image (fun n => n ^ 4) =
      ({0, 1, 16, 81, 256} : Finset ℕ) := by decide +kernel
  rw [isRatPowB_image, powers]

theorem isRatPowB8_iff (r : ℚ) : IsRatPowB 8 4 r ↔
    r.num.natAbs ∈ ({0, 1, 256, 6561} : Finset ℕ) ∧
      r.den ∈ ({0, 1, 256, 6561} : Finset ℕ) := by
  have powers : (Finset.range 4).image (fun n => n ^ 8) =
      ({0, 1, 256, 6561} : Finset ℕ) := by decide +kernel
  rw [isRatPowB_image, powers]

def tableRow3 (x : ℚ) : Prop :=
  ∀ y ∈ typeSet 3,
    (0 < x / y ∧ (x / y).num.natAbs < 6 ^ 3 ∧ (x / y).den < 6 ^ 3) ∧
    (IsRatPowB 3 6 (x / y) ↔ x = y ∨ ∃ C ∈ classes3, x ∈ C ∧ y ∈ C)


def tableRow4 (x : ℚ) : Prop :=
  ∀ y ∈ typeSet 4,
    (0 < x / y ∧ (x / y).num.natAbs < 5 ^ 4 ∧ (x / y).den < 5 ^ 4) ∧
    (IsRatPowB 4 5 (x / y) ↔ x = y ∨ ∃ C ∈ classes4, x ∈ C ∧ y ∈ C)


def tableRow8 (x : ℚ) : Prop :=
  ∀ y ∈ typeSet 8,
    (0 < x / y ∧ (x / y).num.natAbs < 4 ^ 8 ∧ (x / y).den < 4 ^ 8) ∧
    (0 < x / (16 * y) ∧ (x / (16 * y)).num.natAbs < 4 ^ 8 ∧
      (x / (16 * y)).den < 4 ^ 8) ∧
    (IsRatPowB 8 4 (x / y) ∨ IsRatPowB 8 4 (x / (16 * y)) ↔
      x = y ∨ ∃ C ∈ classes8, x ∈ C ∧ y ∈ C)


end CharacterCertificates
end ThreeIM
