module

public import RequestProject.ThreeIM.OccupancyVanishing

/-!
# Lemma 9.22 at the order `h = 8`, and the assembled lemma

At `h = 8` the exceptional classes of Lemma 9.21 are `{1, 16+, 16-}`, `{2+, 32+, 8-}`,
`{8+, 2-, 32-}` and `{4+, 4-}`.  For the three-element classes, the class equations at
`s = 1, 3, 5` are transported to `ζ_8` by the automorphisms `ζ_8 ↦ ζ_8^3, ζ_8^5` (which send
`√2 ↦ -√2`), giving a `3 × 3` linear system with nonzero determinant.

We also record the polynomial consequence used in Lemma 9.23: with `deg F_T < N` and `N` even,
`F_T = (u_T + v_T X)(1 + X^2 + ⋯ + X^{N-2})`.
-/

@[expose] public section

open Polynomial IntermediateField Complex

namespace ThreeIM

theorem zetaC_eight_add : zetaC 8 + zetaC 8 ^ 7 = ((√2 : ℝ) : ℂ) := by
  have h7 : zetaC 8 ^ 7 = (starRingEnd ℂ) (zetaC 8) := by
    have := aeval_pow_pred_eq_conj (h := 8) (by norm_num) X
    simpa using this
  rw [h7, Complex.add_conj]
  have : (zetaC 8).re = √2 / 2 := by
    rw [zetaC, show (2 * (Real.pi : ℂ) * Complex.I / ((8 : ℕ) : ℂ)) = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I by
      push_cast; ring]
    rw [Complex.exp_ofReal_mul_I_re, Real.cos_pi_div_four]
  rw [this]; push_cast; ring

/-- For `s ∈ {3, 5}` there is a ring homomorphism `ℚ(ζ_8) → ℂ` sending `F(ζ_8^s)` to `F(ζ_8)`
for every `F ∈ ℤ[X]` and `√2` to `-√2`. -/
theorem exists_sigma_eight {s : ℕ} (hs : s = 3 ∨ s = 5) :
    ∃ φ : ℚ⟮zetaC 8⟯ →+* ℂ,
      (∀ F : ℤ[X], φ (aeval (⟨zetaC 8, mem_adjoin_simple_self ℚ _⟩ ^ s : ℚ⟮zetaC 8⟯) F) =
        aeval (zetaC 8) F) ∧
      φ (⟨zetaC 8, mem_adjoin_simple_self ℚ _⟩ + ⟨zetaC 8, mem_adjoin_simple_self ℚ _⟩ ^ 7) =
        -((√2 : ℝ) : ℂ) := by
  have hζ := zetaC_isPrimitiveRoot (n := 8) (by norm_num)
  haveI : NeZero 8 := ⟨by norm_num⟩
  set z : ℚ⟮zetaC 8⟯ := ⟨zetaC 8, mem_adjoin_simple_self ℚ _⟩
  have hz : IsPrimitiveRoot z 8 := isPrimitiveRoot_adjoin hζ
  have h8 : z ^ 8 = 1 := hz.pow_eq_one
  have h4 : z ^ 4 + 1 = 0 := by
    have h4' : z ^ 4 ≠ 1 := hz.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
    have : (z ^ 4 - 1) * (z ^ 4 + 1) = 0 := by linear_combination h8
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) h4'
    · exact h
  have hcop : s.Coprime 8 := by rcases hs with rfl | rfl <;> norm_num
  obtain ⟨σ, hσ⟩ := autToPow_surjective_adjoin (by norm_num) hζ (ZMod.unitOfCoprime s hcop)
  have hσz : σ z = z ^ s := by
    rw [← (isPrimitiveRoot_adjoin hζ).autToPow_spec ℚ σ, hσ]
    congr 1
    rcases hs with rfl | rfl <;> rfl
  refine ⟨(algebraMap ℚ⟮zetaC 8⟯ ℂ).comp σ.toRingEquiv.toRingHom, fun F => ?_, ?_⟩
  · have hσs : σ (z ^ s) = z := by
      rw [map_pow, hσz, ← pow_mul]
      rcases hs with rfl | rfl
      · rw [show 3 * 3 = 8 + 1 from rfl, pow_add, h8, one_mul, pow_one]
      · rw [show 5 * 5 = 8 * 3 + 1 from rfl, pow_add, pow_mul, h8, one_pow, one_mul, pow_one]
    simp only [RingHom.coe_comp, Function.comp_apply]
    change ((σ (aeval (z ^ s) F) : ℚ⟮zetaC 8⟯) : ℂ) = _
    have key := Polynomial.aeval_algHom_apply (σ.toAlgHom.restrictScalars ℤ) (z ^ s) F
    simp only [AlgHom.coe_restrictScalars', AlgEquiv.coe_algHom, hσs] at key
    rw [← key]
    have := Polynomial.aeval_algHom_apply (ℚ⟮zetaC 8⟯.val.restrictScalars ℤ) z F
    simpa using this.symm
  · simp only [RingHom.coe_comp, Function.comp_apply]
    change ((σ (z + z ^ 7) : ℚ⟮zetaC 8⟯) : ℂ) = _
    have hw : σ (z + z ^ 7) = -(z + z ^ 7) := by
      rw [map_add, map_pow, hσz]
      rcases hs with rfl | rfl
      · linear_combination (z ^ 13 + z ^ 5) * h8 + (z + z ^ 3) * h4
      · linear_combination (z ^ 27 + z ^ 19 + z ^ 11 + z ^ 3) * h8 + (z + z ^ 3) * h4
    rw [hw, ← zetaC_eight_add]
    rfl
/-- `t = 2^{1/8}` as a complex number. -/
noncomputable def tEight : ℂ := (((2 : ℝ) ^ ((1 : ℝ) / 8) : ℝ) : ℂ)

theorem tEight_ne_zero : tEight ≠ 0 := by
  rw [tEight, Complex.ofReal_ne_zero]; positivity

theorem tEight_pow_four : tEight ^ 4 = ((√2 : ℝ) : ℂ) := by
  rw [tEight, ← Complex.ofReal_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
    Real.sqrt_eq_rpow]
  norm_num

theorem radPow_two_pow (k s : ℕ) :
    radPow ((2 : ℚ) ^ k) s 8 = tEight ^ (k * s) := by
  rw [radPow, tEight, ← Complex.ofReal_pow]
  congr 1
  push_cast
  rw [← Real.rpow_natCast (2 : ℝ) k, ← Real.rpow_mul (by norm_num),
    ← Real.rpow_natCast _ (k * s), ← Real.rpow_mul (by norm_num)]
  congr 1; push_cast; ring

theorem radPow_inv_two_pow (k s : ℕ) :
    radPow (1 / (2 : ℚ) ^ k) s 8 = (tEight ^ (k * s))⁻¹ := by
  rw [← radPow_two_pow, radPow, radPow, ← Complex.ofReal_inv]
  congr 1
  push_cast
  rw [one_div, Real.inv_rpow (by positivity)]

namespace OccupancyData

variable {N : ℕ} (D : OccupancyData N)

theorem term_eight_two_pow (k s : ℕ) :
    D.term 8 s ((2 : ℚ) ^ k) = tEight ^ (k * s) * aeval (zetaC 8 ^ s) (D.F ((2 : ℚ) ^ k)) := by
  have hden : ((2 : ℚ) ^ k).den = 1 := by
    rw [show ((2 : ℚ) ^ k) = ((2 ^ k : ℕ) : ℚ) by push_cast; rfl, Rat.den_natCast]
  simp only [term, hden, Nat.cast_one, one_mul, radPow_two_pow]

theorem term_eight_inv_two_pow (k s : ℕ) :
    D.term 8 s (1 / (2 : ℚ) ^ k) =
      (2 : ℂ) ^ k * (tEight ^ (k * s))⁻¹ * aeval (zetaC 8 ^ s) (D.F (1 / (2 : ℚ) ^ k)) := by
  have hden : (1 / (2 : ℚ) ^ k).den = 2 ^ k := by
    rw [show ((2 : ℚ) ^ k) = ((2 ^ k : ℕ) : ℚ) by push_cast; rfl, one_div,
      Rat.inv_natCast_den_of_pos (by positivity)]
  simp only [term, hden, radPow_inv_two_pow]
  push_cast; ring

end OccupancyData

theorem coe_aeval_adjoin (ζ : ℂ) (F : ℤ[X]) (s : ℕ) :
    ((aeval ((⟨ζ, mem_adjoin_simple_self ℚ ζ⟩ : ℚ⟮ζ⟯) ^ s) F : ℚ⟮ζ⟯) : ℂ) = aeval (ζ ^ s) F := by
  have := Polynomial.aeval_algHom_apply (ℚ⟮ζ⟯.val.restrictScalars ℤ)
    ((⟨ζ, mem_adjoin_simple_self ℚ ζ⟩ : ℚ⟮ζ⟯) ^ s) F
  simpa using this.symm

/-- Transport of a three-term relation at `ζ_8^s` (`s ∈ {3, 5}`) to `ζ_8`, with `√2 ↦ -√2`. -/
theorem sigma_eight_transport {s : ℕ} (hs : s = 3 ∨ s = 5) (F1 F2 F3 : ℤ[X]) (p1 p2 p3 : ℚ)
    (m1 m2 m3 : ℕ)
    (E : (p1 : ℂ) * ((√2 : ℝ) : ℂ) ^ m1 * aeval (zetaC 8 ^ s) F1 +
      (p2 : ℂ) * ((√2 : ℝ) : ℂ) ^ m2 * aeval (zetaC 8 ^ s) F2 +
      (p3 : ℂ) * ((√2 : ℝ) : ℂ) ^ m3 * aeval (zetaC 8 ^ s) F3 = 0) :
    (p1 : ℂ) * (-((√2 : ℝ) : ℂ)) ^ m1 * aeval (zetaC 8) F1 +
      (p2 : ℂ) * (-((√2 : ℝ) : ℂ)) ^ m2 * aeval (zetaC 8) F2 +
      (p3 : ℂ) * (-((√2 : ℝ) : ℂ)) ^ m3 * aeval (zetaC 8) F3 = 0 := by
  obtain ⟨φ, hφF, hφw⟩ := exists_sigma_eight hs
  set z : ℚ⟮zetaC 8⟯ := ⟨zetaC 8, mem_adjoin_simple_self ℚ _⟩
  set W : ℚ⟮zetaC 8⟯ := z + z ^ 7
  have hW : (W : ℂ) = ((√2 : ℝ) : ℂ) := zetaC_eight_add
  set e : ℚ⟮zetaC 8⟯ := (p1 : ℚ⟮zetaC 8⟯) * W ^ m1 * aeval (z ^ s) F1 +
    (p2 : ℚ⟮zetaC 8⟯) * W ^ m2 * aeval (z ^ s) F2 + (p3 : ℚ⟮zetaC 8⟯) * W ^ m3 * aeval (z ^ s) F3
  have he : e = 0 := by
    apply Subtype.ext
    simp only [e, IntermediateField.coe_add, IntermediateField.coe_mul,
      IntermediateField.coe_pow, hW, IntermediateField.coe_zero]
    simp only [z, coe_aeval_adjoin]
    push_cast
    exact E
  have := congrArg φ he
  simp only [e, map_add, map_mul, map_pow, map_ratCast, hφF, hφw, map_zero] at this
  exact this
theorem sqrt_two_sq_complex : ((√2 : ℝ) : ℂ) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; push_cast; rfl

/-- Linear algebra for the classes `{1, 16+, 16-}` and `{2+, 32+, 8-}` at `h = 8`. -/
theorem shapeA_solve {c : ℚ} (hc' : c ≠ 0) {X Y Z : ℂ}
    (E1 : (1 : ℚ) * ((√2 : ℝ) : ℂ) ^ 1 * X + (1 : ℚ) * ((√2 : ℝ) : ℂ) ^ 2 * Y +
      (c : ℂ) * ((√2 : ℝ) : ℂ) ^ 0 * Z = 0)
    (E3 : (1 : ℚ) * (-((√2 : ℝ) : ℂ)) ^ 3 * X + (1 : ℚ) * (-((√2 : ℝ) : ℂ)) ^ 6 * Y +
      (c : ℂ) * (-((√2 : ℝ) : ℂ)) ^ 0 * Z = 0)
    (E5 : (1 : ℚ) * (-((√2 : ℝ) : ℂ)) ^ 5 * X + (1 : ℚ) * (-((√2 : ℝ) : ℂ)) ^ 10 * Y +
      (c : ℂ) * (-((√2 : ℝ) : ℂ)) ^ 0 * Z = 0) :
    X = 0 ∧ Y = 0 ∧ Z = 0 := by
  rw [pow_zero, mul_one] at E1 E3 E5
  have hc : (c : ℂ) ≠ 0 := by exact_mod_cast hc'
  generalize (c : ℂ) = c' at hc E1 E3 E5
  set w : ℂ := ((√2 : ℝ) : ℂ)
  have hw2 : w ^ 2 = 2 := sqrt_two_sq_complex
  have hw0 : w ≠ 0 := by intro h; rw [h] at hw2; norm_num at hw2
  have hw3 : w ^ 3 = 2 * w := by rw [pow_succ, hw2]
  have hw5 : w ^ 5 = 4 * w := by
    have : w ^ 5 = (w ^ 2) ^ 2 * w := by ring
    rw [this, hw2]; norm_num
  have hw6 : w ^ 6 = 8 := by
    have : w ^ 6 = (w ^ 2) ^ 3 := by ring
    rw [this, hw2]; norm_num
  have hw10 : w ^ 10 = 32 := by
    have : w ^ 10 = (w ^ 2) ^ 5 := by ring
    rw [this, hw2]; norm_num
  have e1 : w * X + 2 * Y + c' * Z = 0 := by
    rw [pow_one, hw2] at E1; push_cast at E1; linear_combination E1
  have e3 : -2 * w * X + 8 * Y + c' * Z = 0 := by
    rw [Odd.neg_pow (by decide), Even.neg_pow (by decide), hw3, hw6] at E3
    push_cast at E3; linear_combination E3
  have e5 : -4 * w * X + 32 * Y + c' * Z = 0 := by
    rw [Odd.neg_pow (by decide), Even.neg_pow (by decide), hw5, hw10] at E5
    push_cast at E5; linear_combination E5
  have hZ : c' * Z = 0 := by linear_combination (2 / 3 : ℂ) * (2 * e1 + e3) - (1 / 5 : ℂ) * (4 * e1 + e5)
  have hZ' : Z = 0 := (mul_eq_zero.1 hZ).resolve_left hc
  have hY : Y = 0 := by linear_combination (1 / 12 : ℂ) * (2 * e1 + e3) - (c' / 4) * hZ'
  have hX : w * X = 0 := by linear_combination e1 - 2 * hY - c' * hZ'
  exact ⟨(mul_eq_zero.1 hX).resolve_left hw0, hY, hZ'⟩

/-- Linear algebra for the class `{8+, 2-, 32-}` at `h = 8`. -/
theorem shapeB_solve {X Y Z : ℂ}
    (E1 : (1 : ℚ) * ((√2 : ℝ) : ℂ) ^ 2 * X + (2 : ℚ) * ((√2 : ℝ) : ℂ) ^ 1 * Y +
      (32 : ℚ) * ((√2 : ℝ) : ℂ) ^ 0 * Z = 0)
    (E3 : (1 : ℚ) * (-((√2 : ℝ) : ℂ)) ^ 6 * X + (2 : ℚ) * (-((√2 : ℝ) : ℂ)) ^ 3 * Y +
      (32 : ℚ) * (-((√2 : ℝ) : ℂ)) ^ 0 * Z = 0)
    (E5 : (1 : ℚ) * (-((√2 : ℝ) : ℂ)) ^ 10 * X + (2 : ℚ) * (-((√2 : ℝ) : ℂ)) ^ 5 * Y +
      (32 : ℚ) * (-((√2 : ℝ) : ℂ)) ^ 0 * Z = 0) :
    X = 0 ∧ Y = 0 ∧ Z = 0 := by
  set w : ℂ := ((√2 : ℝ) : ℂ)
  have hw2 : w ^ 2 = 2 := sqrt_two_sq_complex
  have hw0 : w ≠ 0 := by intro h; rw [h] at hw2; norm_num at hw2
  have hw3 : w ^ 3 = 2 * w := by rw [pow_succ, hw2]
  have hw5 : w ^ 5 = 4 * w := by
    have : w ^ 5 = (w ^ 2) ^ 2 * w := by ring
    rw [this, hw2]; norm_num
  have hw6 : w ^ 6 = 8 := by
    have : w ^ 6 = (w ^ 2) ^ 3 := by ring
    rw [this, hw2]; norm_num
  have hw10 : w ^ 10 = 32 := by
    have : w ^ 10 = (w ^ 2) ^ 5 := by ring
    rw [this, hw2]; norm_num
  have e1 : 2 * X + 2 * (w * Y) + 32 * Z = 0 := by
    rw [pow_one, hw2] at E1; push_cast at E1; linear_combination E1
  have e3 : 8 * X - 4 * (w * Y) + 32 * Z = 0 := by
    rw [Even.neg_pow (by decide), Odd.neg_pow (by decide), hw3, hw6] at E3
    push_cast at E3; linear_combination E3
  have e5 : 32 * X - 8 * (w * Y) + 32 * Z = 0 := by
    rw [Even.neg_pow (by decide), Odd.neg_pow (by decide), hw5, hw10] at E5
    push_cast at E5; linear_combination E5
  have hb : w * Y = 0 := by linear_combination (1 / 20 : ℂ) * (e5 - 5 * e3 + 4 * e1)
  have hX : X = 0 := by linear_combination (1 / 6 : ℂ) * (e3 - e1) + hb
  have hZ : Z = 0 := by linear_combination (1 / 32 : ℂ) * (e1 - 2 * hX - 2 * hb)
  exact ⟨hX, (mul_eq_zero.1 hb).resolve_left hw0, hZ⟩

local notation "w2" => ((√2 : ℝ) : ℂ)

theorem triple_A_vanish {F1 F2 F3 : ℤ[X]} {c : ℚ} (hc : c ≠ 0)
    (hE : ∀ s, s = 1 ∨ s = 3 ∨ s = 5 →
      (1 : ℚ) * w2 ^ (1 * s) * aeval (zetaC 8 ^ s) F1 + (1 : ℚ) * w2 ^ (2 * s) * aeval (zetaC 8 ^ s) F2 +
        (c : ℂ) * w2 ^ (0 * s) * aeval (zetaC 8 ^ s) F3 = 0) :
    aeval (zetaC 8) F1 = 0 ∧ aeval (zetaC 8) F2 = 0 ∧ aeval (zetaC 8) F3 = 0 := by
  have E1 := hE 1 (Or.inl rfl)
  rw [pow_one (zetaC 8)] at E1
  have E3 := sigma_eight_transport (Or.inl rfl) F1 F2 F3 1 1 c _ _ _ (hE 3 (Or.inr (Or.inl rfl)))
  have E5 := sigma_eight_transport (Or.inr rfl) F1 F2 F3 1 1 c _ _ _ (hE 5 (Or.inr (Or.inr rfl)))
  exact shapeA_solve hc E1 E3 E5

theorem triple_B_vanish {F1 F2 F3 : ℤ[X]}
    (hE : ∀ s, s = 1 ∨ s = 3 ∨ s = 5 →
      (1 : ℚ) * w2 ^ (2 * s) * aeval (zetaC 8 ^ s) F1 + (2 : ℚ) * w2 ^ (1 * s) * aeval (zetaC 8 ^ s) F2 +
        (32 : ℚ) * w2 ^ (0 * s) * aeval (zetaC 8 ^ s) F3 = 0) :
    aeval (zetaC 8) F1 = 0 ∧ aeval (zetaC 8) F2 = 0 ∧ aeval (zetaC 8) F3 = 0 := by
  have E1 := hE 1 (Or.inl rfl)
  rw [pow_one (zetaC 8)] at E1
  have E3 := sigma_eight_transport (Or.inl rfl) F1 F2 F3 1 2 32 _ _ _ (hE 3 (Or.inr (Or.inl rfl)))
  have E5 := sigma_eight_transport (Or.inr rfl) F1 F2 F3 1 2 32 _ _ _ (hE 5 (Or.inr (Or.inr rfl)))
  exact shapeB_solve E1 E3 E5

namespace OccupancyData

variable {N : ℕ} (D : OccupancyData N)

theorem classA1_rel (s : ℕ)
    (hsum : ∑ y ∈ ({1, 16, 1/16} : Finset ℚ), D.term 8 s y = 0) :
    (1 : ℚ) * w2 ^ (1 * s) * aeval (zetaC 8 ^ s) (D.F 1) +
      (1 : ℚ) * w2 ^ (2 * s) * aeval (zetaC 8 ^ s) (D.F 16) +
      ((16 : ℚ) : ℂ) * w2 ^ (0 * s) * aeval (zetaC 8 ^ s) (D.F (1 / 16)) = 0 := by
  rw [Finset.sum_insert (by norm_num), Finset.sum_pair (by norm_num)] at hsum
  have h16 : D.term 8 s 16 = tEight ^ (4 * s) * aeval (zetaC 8 ^ s) (D.F 16) := by
    rw [show (16 : ℚ) = 2 ^ 4 by norm_num]; exact D.term_eight_two_pow 4 s
  have h116 : D.term 8 s (1 / 16) =
      (2 : ℂ) ^ 4 * (tEight ^ (4 * s))⁻¹ * aeval (zetaC 8 ^ s) (D.F (1 / 16)) := by
    rw [show (16 : ℚ) = 2 ^ 4 by norm_num]; exact D.term_eight_inv_two_pow 4 s
  rw [D.term_one, h16, h116] at hsum
  have ht := tEight_ne_zero
  rw [← tEight_pow_four]
  field_simp at hsum
  push_cast
  linear_combination hsum

theorem classA2_rel (s : ℕ)
    (hsum : ∑ y ∈ ({2, 32, 1/8} : Finset ℚ), D.term 8 s y = 0) :
    (1 : ℚ) * w2 ^ (1 * s) * aeval (zetaC 8 ^ s) (D.F 2) +
      (1 : ℚ) * w2 ^ (2 * s) * aeval (zetaC 8 ^ s) (D.F 32) +
      ((8 : ℚ) : ℂ) * w2 ^ (0 * s) * aeval (zetaC 8 ^ s) (D.F (1 / 8)) = 0 := by
  rw [Finset.sum_insert (by norm_num), Finset.sum_pair (by norm_num)] at hsum
  have h2 : D.term 8 s 2 = tEight ^ (1 * s) * aeval (zetaC 8 ^ s) (D.F 2) := by
    have := D.term_eight_two_pow 1 s; rwa [pow_one] at this
  have h32 : D.term 8 s 32 = tEight ^ (5 * s) * aeval (zetaC 8 ^ s) (D.F 32) := by
    rw [show (32 : ℚ) = 2 ^ 5 by norm_num]; exact D.term_eight_two_pow 5 s
  have h18 : D.term 8 s (1 / 8) =
      (2 : ℂ) ^ 3 * (tEight ^ (3 * s))⁻¹ * aeval (zetaC 8 ^ s) (D.F (1 / 8)) := by
    rw [show (8 : ℚ) = 2 ^ 3 by norm_num]; exact D.term_eight_inv_two_pow 3 s
  rw [h2, h32, h18] at hsum
  have ht := tEight_ne_zero
  rw [← tEight_pow_four]
  field_simp at hsum
  push_cast
  linear_combination hsum

theorem classB_rel (s : ℕ)
    (hsum : ∑ y ∈ ({8, 1/2, 1/32} : Finset ℚ), D.term 8 s y = 0) :
    (1 : ℚ) * w2 ^ (2 * s) * aeval (zetaC 8 ^ s) (D.F 8) +
      (2 : ℚ) * w2 ^ (1 * s) * aeval (zetaC 8 ^ s) (D.F (1 / 2)) +
      (32 : ℚ) * w2 ^ (0 * s) * aeval (zetaC 8 ^ s) (D.F (1 / 32)) = 0 := by
  rw [Finset.sum_insert (by norm_num), Finset.sum_pair (by norm_num)] at hsum
  have h8 : D.term 8 s 8 = tEight ^ (3 * s) * aeval (zetaC 8 ^ s) (D.F 8) := by
    rw [show (8 : ℚ) = 2 ^ 3 by norm_num]; exact D.term_eight_two_pow 3 s
  have h12 : D.term 8 s (1 / 2) =
      (2 : ℂ) ^ 1 * (tEight ^ (1 * s))⁻¹ * aeval (zetaC 8 ^ s) (D.F (1 / 2)) := by
    have := D.term_eight_inv_two_pow 1 s; rwa [pow_one (2 : ℚ)] at this
  have h132 : D.term 8 s (1 / 32) =
      (2 : ℂ) ^ 5 * (tEight ^ (5 * s))⁻¹ * aeval (zetaC 8 ^ s) (D.F (1 / 32)) := by
    rw [show (32 : ℚ) = 2 ^ 5 by norm_num]; exact D.term_eight_inv_two_pow 5 s
  rw [h8, h12, h132] at hsum
  have ht := tEight_ne_zero
  rw [← tEight_pow_four]
  field_simp at hsum
  push_cast
  have hs : tEight ^ (1 * s) ≠ 0 := pow_ne_zero _ ht
  refine (mul_eq_zero.1 (?_ : tEight ^ (1 * s) * _ = 0)).resolve_left hs
  linear_combination hsum

set_option maxRecDepth 10000 in
theorem classes8_sub : ∀ C ∈ classes8, ∀ y ∈ C, y ∈ typeSet 8 := by decide +kernel
set_option maxRecDepth 10000 in
theorem classes8_disj : ∀ C ∈ classes8, ∀ C' ∈ classes8, ∀ z ∈ C, z ∈ C' → C = C' := by
  decide +kernel

theorem vanishing_eight
    (IH : ∀ e ∈ N.divisors, 8 < e → ∀ ξ : ℂ, IsPrimitiveRoot ξ e → ∀ y, aeval ξ (D.F y) = 0)
    (hh : 8 ∣ N) (x : ℚ) : aeval (zetaC 8) (D.F x) = 0 := by
  by_contra hj
  have T := D.table_sums hh (by norm_num) IH classes8
    (character_classes_eight (zetaC_isPrimitiveRoot (by norm_num))) classes8_sub classes8_disj
  by_cases hin : ∃ C ∈ classes8, x ∈ C
  · obtain ⟨C, hC, hxC⟩ := hin
    have hs := T.1 C hC
    have hs' : ∀ s, s = 1 ∨ s = 3 ∨ s = 5 → ∑ y ∈ C, D.term 8 s y = 0 := by
      rintro s (rfl | rfl | rfl) <;> exact hs _ (by norm_num) (by norm_num) (by norm_num)
    simp only [classes8, Finset.mem_insert, Finset.mem_singleton] at hC
    rcases hC with rfl | rfl | rfl | rfl
    · have := triple_A_vanish (by norm_num) fun s hs => D.classA1_rel s (hs' s hs)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxC
      rcases hxC with rfl | rfl | rfl
      · exact hj this.1
      · exact hj this.2.1
      · exact hj this.2.2
    · have := triple_A_vanish (by norm_num) fun s hs => D.classA2_rel s (hs' s hs)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxC
      rcases hxC with rfl | rfl | rfl
      · exact hj this.1
      · exact hj this.2.1
      · exact hj this.2.2
    · have := triple_B_vanish fun s hs => D.classB_rel s (hs' s hs)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxC
      rcases hxC with rfl | rfl | rfl
      · exact hj this.1
      · exact hj this.2.1
      · exact hj this.2.2
    · have := D.two_class_vanish (h := 8) (by norm_num) (a := 4) (b := 4) (by norm_num) (by norm_num)
        (by simpa using hs)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxC
      rcases hxC with rfl | rfl
      · exact hj (by simpa using this.1)
      · exact hj (by simpa using this.2)
  · push_neg at hin
    exact T.2 x hj hin

/-- **Lemma 9.22** (vanishing of the occupancy Fourier coefficients): for every divisor
`h ∣ N` with `h ≥ 3` and every type `x`, `F_x(ζ_h) = 0`. -/
theorem vanishing {h : ℕ} (hh : h ∣ N) (h3 : 3 ≤ h) (x : ℚ) :
    aeval (zetaC h) (D.F x) = 0 := by
  induction hk : N - h using Nat.strong_induction_on generalizing h x with
  | _ k ih =>
    have IH : ∀ e ∈ N.divisors, h < e → ∀ ξ : ℂ, IsPrimitiveRoot ξ e → ∀ y,
        aeval ξ (D.F y) = 0 := by
      intro e he hlt ξ hξ y
      have heN : e ∣ N := Nat.dvd_of_mem_divisors he
      have heN' : e ≤ N := Nat.divisor_le he
      have he0 : 0 < e := by omega
      exact aeval_primitiveRoot_eq_zero he0 (zetaC_isPrimitiveRoot he0) hξ
        (ih (N - e) (by omega) heN (by omega) y rfl)
    by_cases h3' : h = 3
    · subst h3'; exact D.vanishing_three IH hh x
    by_cases h4' : h = 4
    · subst h4'; exact D.vanishing_four IH hh x
    by_cases h8' : h = 8
    · subst h8'; exact D.vanishing_eight IH hh x
    exact D.vanishing_generic hh h3 h3' h4' h8' IH x

end OccupancyData

theorem prod_cyclotomic_ge_three {N : ℕ} (hN : 0 < N) (hev : Even N) :
    (∏ h ∈ N.divisors with 3 ≤ h, cyclotomic h ℤ) * (X ^ 2 - 1) = X ^ N - 1 := by
  rw [← prod_cyclotomic_eq_X_pow_sub_one hN, ← Finset.prod_filter_mul_prod_filter_not N.divisors
    (fun h => 3 ≤ h)]
  congr 1
  have h2 : 2 ∣ N := even_iff_two_dvd.1 hev
  have : (N.divisors.filter fun h => ¬ 3 ≤ h) = {1, 2} := by
    ext h
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hd, -⟩, hlt⟩
      have : h ≠ 0 := by rintro rfl; simp at hd; omega
      omega
    · rintro (rfl | rfl)
      · exact ⟨⟨one_dvd _, hN.ne'⟩, by omega⟩
      · exact ⟨⟨h2, hN.ne'⟩, by omega⟩
  rw [this, Finset.prod_pair (by norm_num), cyclotomic_one, cyclotomic_two]
  ring

theorem even_geom_mul {m : ℕ} :
    (∑ i ∈ Finset.range m, (X : ℤ[X]) ^ (2 * i)) * (X ^ 2 - 1) = X ^ (2 * m) - 1 := by
  simp only [pow_mul]
  exact geom_sum_mul _ _

/-- Polynomial consequence of Lemma 9.22 (first step of Lemma 9.23): an integer polynomial of
degree `< N` (`N` even) vanishing at `ζ_h` for every divisor `h ≥ 3` of `N` has the form
`(u + v X)(1 + X^2 + ⋯ + X^{N-2})`. -/
theorem poly_form_of_vanishing {N : ℕ} (hN : 0 < N) (hev : Even N) (F : ℤ[X])
    (hdeg : F.natDegree < N) (hv : ∀ h ∈ N.divisors, 3 ≤ h → aeval (zetaC h) F = 0) :
    ∃ u v : ℤ, F = (C u + C v * X) * ∑ i ∈ Finset.range (N / 2), X ^ (2 * i) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = 2 * m := ⟨N / 2, by obtain ⟨k, hk⟩ := hev; omega⟩
  rw [show 2 * m / 2 = m by omega]
  set G : ℤ[X] := ∑ i ∈ Finset.range m, X ^ (2 * i)
  set P : ℤ[X] := ∏ h ∈ (2 * m).divisors with 3 ≤ h, cyclotomic h ℤ
  have hX2 : (X ^ 2 - 1 : ℤ[X]) ≠ 0 := by
    intro h
    have := congrArg (fun p => p.coeff 0) h
    simp at this
  have hPG : P = G := by
    apply mul_right_cancel₀ hX2
    rw [prod_cyclotomic_ge_three hN hev, even_geom_mul]
  have hPm : P.Monic := monic_prod_of_monic _ _ fun h _ => cyclotomic.monic h ℤ
  -- each cyclotomic factor divides `F`
  have hdvd : ∀ h ∈ (2 * m).divisors.filter (3 ≤ ·), cyclotomic h ℤ ∣ F := by
    intro h hh
    simp only [Finset.mem_filter] at hh
    have h0 : 0 < h := by omega
    rw [cyclotomic_eq_minpoly (zetaC_isPrimitiveRoot h0) h0]
    exact minpoly.isIntegrallyClosed_dvd ((zetaC_isPrimitiveRoot h0).isIntegral h0) (hv h hh.1 hh.2)
  have hPF : P ∣ F := by
    rw [← map_dvd_map (Int.castRingHom ℚ) (RingHom.injective_int _) hPm]
    simp only [P, Polynomial.map_prod, map_cyclotomic]
    refine Finset.prod_dvd_of_coprime ?_ fun h hh => ?_
    · intro a _ b _ hab
      exact cyclotomic.isCoprime_rat hab
    · rw [← map_cyclotomic h (Int.castRingHom ℚ)]
      exact Polynomial.map_dvd _ (hdvd h hh)
  obtain ⟨Q, hQ⟩ := hPF
  rw [hPG] at hQ
  have hGm : G.Monic := hPG ▸ hPm
  have hGdeg : G.natDegree + 2 = 2 * m := by
    have h1 := congrArg natDegree (even_geom_mul (m := m))
    have hm : 0 < m := by omega
    rw [hGm.natDegree_mul' hX2,
      show (X ^ 2 - 1 : ℤ[X]) = X ^ 2 - C 1 by simp, natDegree_X_pow_sub_C,
      show (X ^ (2 * m) - 1 : ℤ[X]) = X ^ (2 * m) - C 1 by simp, natDegree_X_pow_sub_C] at h1
    exact h1
  by_cases hQ0 : Q = 0
  · exact ⟨0, 0, by rw [hQ, hQ0]; simp⟩
  have hFdeg : F.natDegree = G.natDegree + Q.natDegree := by
    rw [hQ, hGm.natDegree_mul' (by simpa [hGm.leadingCoeff] using hQ0)]
  have hQdeg : Q.natDegree ≤ 1 := by omega
  refine ⟨Q.coeff 0, Q.coeff 1, ?_⟩
  rw [hQ]
  conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hQdeg]
  ring

/-- Lemma 9.22 combined with the degree bound `deg F_T < N` (`N` even): every occupancy
polynomial has the form `(u_T + v_T X)(1 + X^2 + ⋯ + X^{N-2})` (first step of Lemma 9.23). -/
theorem OccupancyData.poly_form {N : ℕ} (D : OccupancyData N) (hev : Even N) (x : ℚ)
    (hdeg : (D.F x).natDegree < N) :
    ∃ u v : ℤ, D.F x = (C u + C v * X) * ∑ i ∈ Finset.range (N / 2), X ^ (2 * i) :=
  poly_form_of_vanishing D.N_pos hev _ hdeg fun _ hh h3 =>
    D.vanishing (Nat.dvd_of_mem_divisors hh) h3 x

end ThreeIM
