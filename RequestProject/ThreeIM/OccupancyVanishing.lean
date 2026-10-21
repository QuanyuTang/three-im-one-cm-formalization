module

public import RequestProject.ThreeIM.CharacterClasses
public import RequestProject.ThreeIM.RadicalCharacters

/-!
# Vanishing of the occupancy Fourier coefficients (Lemma 9.22)

Types of finite common points are encoded by positive rationals `x` of the form `k` (exterior
type `k+`, or the unit type for `k = 1`) or `1/k` (interior type `k-`).  For a type `x`, the
multiplicity `m_T` is `x.den`, the bound index `k_T = max(m_T, n_T)` is `x.num * x.den`, and
`m_T r_T^ℓ = x.den * x^{ℓ/N}`.  The occupancy polynomials are `F x ∈ ℤ[X]`, and
`B_T = ‖F x‖₁`.

Lemma 9.22: under the occupancy bounds and equations of Lemma 9.11, `F_T(ζ_h) = 0` for every
divisor `h ∣ N` with `h ≥ 3` and every type `T`.  This file proves the generic orders and
`h ∈ {3, 4}`; the order `h = 8` and the assembled lemma are in `OccupancyEight.lean`.
-/

@[expose] public section

open Polynomial IntermediateField Complex

namespace ThreeIM

/-- `‖F‖₁`, the sum of the absolute values of the coefficients. -/
noncomputable def l1norm (F : ℤ[X]) : ℝ := ∑ i ∈ F.support, (|F.coeff i| : ℝ)

/-- `ζ_n = e^{2πi/n}`. -/
noncomputable def zetaC (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

/-- `x^{a/b}` as a complex number (real positive power of a positive rational). -/
noncomputable def radPow (x : ℚ) (a b : ℕ) : ℂ := (((x : ℝ) ^ ((a : ℝ) / b) : ℝ) : ℂ)

/-- The hypotheses of Lemma 9.22 (the conclusions of Lemma 9.11): finitely many types, bounds
`B_1 ≤ N`, `k_T B_T < 5N`, and the occupancy moment equations. -/
structure OccupancyData (N : ℕ) where
  S : Finset ℚ
  F : ℚ → ℤ[X]
  N_pos : 0 < N
  type_form : ∀ x ∈ S, 0 < x ∧ (x.num = 1 ∨ x.den = 1)
  support : ∀ x, F x ≠ 0 → x ∈ S
  bound_one : l1norm (F 1) ≤ N
  bound_type : ∀ x ∈ S, ((x.num.natAbs * x.den : ℕ) : ℝ) * l1norm (F x) < 5 * N
  moments : ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ < N → 2 * ℓ ≠ N →
    ∑ x ∈ S, (x.den : ℂ) * radPow x ℓ N * aeval (zetaC N ^ ℓ) (F x) = 0

theorem zetaC_isPrimitiveRoot {n : ℕ} (hn : 0 < n) : IsPrimitiveRoot (zetaC n) n :=
  Complex.isPrimitiveRoot_exp n hn.ne'

theorem zetaC_pow_div {N h : ℕ} (hN : 0 < N) (hh : h ∣ N) : zetaC N ^ (N / h) = zetaC h := by
  obtain ⟨m, rfl⟩ := hh
  have hh0 : 0 < h := Nat.pos_of_mul_pos_right hN
  have hm0 : 0 < m := Nat.pos_of_mul_pos_left hN
  rw [Nat.mul_div_cancel_left _ hh0, zetaC, zetaC, ← Complex.exp_nat_mul]
  have h1 : (m : ℂ) ≠ 0 := by exact_mod_cast hm0.ne'
  have h2 : (h : ℂ) ≠ 0 := by exact_mod_cast hh0.ne'
  congr 1
  push_cast
  field_simp

theorem radPow_mul_div {N h : ℕ} (hN : 0 < N) (hh : h ∣ N) (x : ℚ) (s : ℕ) :
    radPow x (N / h * s) N = radPow x s h := by
  obtain ⟨m, rfl⟩ := hh
  have hh0 : 0 < h := Nat.pos_of_mul_pos_right hN
  have hm0 : 0 < m := Nat.pos_of_mul_pos_left hN
  rw [radPow, radPow, Nat.mul_div_cancel_left _ hh0]
  have h1 : (m : ℝ) ≠ 0 := by exact_mod_cast hm0.ne'
  have h2 : (h : ℝ) ≠ 0 := by exact_mod_cast hh0.ne'
  congr 2
  push_cast
  field_simp

theorem radPow_pos {x : ℚ} (hx : 0 < x) (a b : ℕ) : radPow x a b ≠ 0 := by
  rw [radPow, Complex.ofReal_ne_zero]
  exact (Real.rpow_pos_of_pos (by exact_mod_cast hx) _).ne'

theorem radPow_pow {x : ℚ} (hx : 0 < x) (s : ℕ) {h : ℕ} (hh : 0 < h) :
    radPow x s h ^ h = ((x ^ s : ℚ) : ℂ) := by
  rw [radPow, ← Complex.ofReal_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  rw [div_mul_cancel₀ _ (by positivity), Real.rpow_natCast]
  push_cast; rfl

theorem ratCast_mem_adjoin (ζ : ℂ) (q : ℚ) : (q : ℂ) ∈ ℚ⟮ζ⟯ := by
  rw [← eq_ratCast (algebraMap ℚ ℂ)]
  exact IntermediateField.algebraMap_mem _ q

theorem aeval_mem_adjoin (ζ : ℂ) (F : ℤ[X]) (s : ℕ) : aeval (ζ ^ s) F ∈ ℚ⟮ζ⟯ := by
  have h := Polynomial.aeval_algHom_apply (ℚ⟮ζ⟯.val.restrictScalars ℤ)
    ((⟨ζ, mem_adjoin_simple_self ℚ ζ⟩ : ℚ⟮ζ⟯) ^ s) F
  simp only [AlgHom.coe_restrictScalars', map_pow] at h
  change aeval (ζ ^ s) F ∈ ℚ⟮ζ⟯
  rw [show ζ ^ s = (ℚ⟮ζ⟯.val ⟨ζ, mem_adjoin_simple_self ℚ ζ⟩) ^ s from rfl, h]
  exact Subtype.mem _
theorem mem_typeSet_of_bound {x : ℚ} (hx : 0 < x ∧ (x.num = 1 ∨ x.den = 1)) {h : ℕ}
    (hk : x.num.natAbs * x.den < 5 * h) : x ∈ typeSet h := by
  simp only [typeSet, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_Ico]
  rcases hx with ⟨hpos, hnum | hden⟩
  · have hx' : x = 1 / (x.den : ℚ) := by
      conv_lhs => rw [← Rat.num_div_den x, hnum]
      simp
    rw [hnum] at hk
    simp only [Int.natAbs_one, one_mul] at hk
    by_cases hd : x.den = 1
    · left; rw [hx', hd]; simp
    · right; right
      exact ⟨x.den, ⟨by have := x.den_pos; omega, hk⟩, hx'.symm⟩
  · have hx' : x = (x.num.natAbs : ℚ) := by
      have h1 : (x.num : ℚ) = x := Rat.den_eq_one_iff x |>.1 hden
      have h2 : (0 : ℤ) < x.num := Rat.num_pos.2 hpos
      rw [Nat.cast_natAbs, abs_of_pos h2]; exact h1.symm
    rw [hden, mul_one] at hk
    by_cases hn : x.num.natAbs = 1
    · left; rw [hx', hn]; simp
    · right; left
      have : 0 < x.num.natAbs := Int.natAbs_pos.2 (Rat.num_pos.2 hpos).ne'
      exact ⟨x.num.natAbs, ⟨by omega, hk⟩, hx'.symm⟩

theorem sameCharacter_iff_rpow_mem {h : ℕ} (hh : 0 < h) (ζ : ℂ) {x j : ℚ} (hx : 0 < x)
    (hj : 0 < j) :
    SameCharacter h ζ x j ↔ ((((x / j : ℚ) : ℝ) ^ ((1 : ℝ) / h) : ℝ) : ℂ) ∈ ℚ⟮ζ⟯ := by
  have hr : (0 : ℝ) < ((x / j : ℚ) : ℝ) := by exact_mod_cast div_pos hx hj
  constructor
  · rintro ⟨β, hβ, hβh, hmem⟩
    have : (((x / j : ℚ) : ℝ) ^ ((1 : ℝ) / h)) = β := by
      rw [← hβh, one_div, Real.pow_rpow_inv_natCast hβ.le hh.ne']
    rwa [this]
  · intro hmem
    refine ⟨_, Real.rpow_pos_of_pos hr _, ?_, hmem⟩
    rw [one_div, Real.rpow_inv_natCast_pow hr.le hh.ne']

theorem typeSet_cases {h : ℕ} {x : ℚ} (hx : x ∈ typeSet h) :
    x = 1 ∨ (∃ k : ℕ, 2 ≤ k ∧ k < 5 * h ∧ x = k) ∨ (∃ k : ℕ, 2 ≤ k ∧ k < 5 * h ∧ x = 1 / k) := by
  simp only [typeSet, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_Ico] at hx
  rcases hx with rfl | ⟨k, ⟨hk1, hk2⟩, rfl⟩ | ⟨k, ⟨hk1, hk2⟩, rfl⟩
  · left; rfl
  · right; left; exact ⟨k, hk1, hk2, rfl⟩
  · right; right; exact ⟨k, hk1, hk2, rfl⟩

theorem typeSet_pos {h : ℕ} {x : ℚ} (hx : x ∈ typeSet h) : 0 < x := by
  rcases typeSet_cases hx with rfl | ⟨k, hk, -, rfl⟩ | ⟨k, hk, -, rfl⟩
  · norm_num
  · exact_mod_cast (by omega : 0 < k)
  · have : (0 : ℚ) < k := by exact_mod_cast (by omega : 0 < k)
    positivity

theorem typeSet_ge_one {h : ℕ} (hh : 0 < h) {x : ℚ} (hx : x ∈ typeSet h) (h1 : 1 ≤ x) :
    ∃ a : ℕ, 1 ≤ a ∧ a < 5 * h ∧ x = a := by
  rcases typeSet_cases hx with rfl | ⟨k, hk, hk', rfl⟩ | ⟨k, hk, -, rfl⟩
  · exact ⟨1, le_rfl, by omega, by simp⟩
  · exact ⟨k, by omega, hk', rfl⟩
  · exfalso
    have hk2 : (2 : ℚ) ≤ k := by exact_mod_cast hk
    rw [le_div_iff₀ (by linarith)] at h1
    linarith

theorem typeSet_le_one {h : ℕ} (hh : 0 < h) {x : ℚ} (hx : x ∈ typeSet h) (h1 : x ≤ 1) :
    ∃ b : ℕ, 1 ≤ b ∧ b < 5 * h ∧ x = 1 / b := by
  rcases typeSet_cases hx with rfl | ⟨k, hk, -, rfl⟩ | ⟨k, hk, hk', rfl⟩
  · exact ⟨1, le_rfl, by omega, by simp⟩
  · exfalso
    have hk2 : (2 : ℚ) ≤ k := by exact_mod_cast hk
    linarith
  · exact ⟨k, by omega, hk', rfl⟩

theorem sameCharacter_refl {h : ℕ} (ζ : ℂ) {x : ℚ} (hx : x ≠ 0) : SameCharacter h ζ x x :=
  ⟨1, one_pos, by rw [div_self hx]; simp, by simp⟩

theorem sameCharacter_trans {h : ℕ} {ζ : ℂ} {x y j : ℚ} (hx : SameCharacter h ζ x j)
    (hy : SameCharacter h ζ y j) : SameCharacter h ζ x y := by
  obtain ⟨β1, h1, hβ1, hm1⟩ := hx
  obtain ⟨β2, h2, hβ2, hm2⟩ := hy
  refine ⟨β1 / β2, div_pos h1 h2, ?_, by push_cast; exact div_mem hm1 hm2⟩
  have hj : j ≠ 0 := by
    rintro rfl
    simp only [div_zero, Rat.cast_zero] at hβ1
    exact (pow_pos h1 h).ne' hβ1
  have hyj : ((y / j : ℚ) : ℝ) ≠ 0 := by rw [← hβ2]; positivity
  rw [div_pow, hβ1, hβ2]
  have hy0 : y ≠ 0 := by rintro rfl; simp at hyj
  push_cast
  field_simp

/-- In a generic order, two types of the same character lying weakly on the same side of `1`
coincide (Lemma 9.19). -/
theorem generic_eq {h : ℕ} (h3 : 3 ≤ h) (hne3 : h ≠ 3) (hne4 : h ≠ 4) (hne8 : h ≠ 8) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ h) {x y : ℚ} (hx : x ∈ typeSet h) (hy : y ∈ typeSet h)
    (hS : SameCharacter h ζ x y) (hside : (1 ≤ x ∧ 1 ≤ y) ∨ (x ≤ 1 ∧ y ≤ 1)) : x = y := by
  have hh0 : 0 < h := by omega
  obtain ⟨β, -, hβ, hmem⟩ := hS
  rcases hside with ⟨hx1, hy1⟩ | ⟨hx1, hy1⟩
  · obtain ⟨a, ha, ha', rfl⟩ := typeSet_ge_one hh0 hx hx1
    obtain ⟨b, hb, hb', rfl⟩ := typeSet_ge_one hh0 hy hy1
    have := radical_quotient_eq h3 hne3 hne4 hne8 hζ (by omega) (by omega) ha' hb'
      (β := β) (by rw [hβ]; push_cast; rfl) hmem
    rw [this]
  · obtain ⟨a, ha, ha', rfl⟩ := typeSet_le_one hh0 hx hx1
    obtain ⟨b, hb, hb', rfl⟩ := typeSet_le_one hh0 hy hy1
    have := radical_quotient_eq h3 hne3 hne4 hne8 hζ (by omega) (by omega) hb' ha'
      (β := β) (by
        rw [hβ]
        have : (a : ℝ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
        have : (b : ℝ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
        push_cast; field_simp) hmem
    rw [this]

theorem aeval_pow_pred_eq_conj {h : ℕ} (hh : 0 < h) (F : ℤ[X]) :
    aeval (zetaC h ^ (h - 1)) F = (starRingEnd ℂ) (aeval (zetaC h) F) := by
  have hζ := zetaC_isPrimitiveRoot hh
  have hconjζ : zetaC h ^ (h - 1) = (starRingEnd ℂ) (zetaC h) := by
    have hn : ‖zetaC h‖ = 1 := hζ.norm'_eq_one hh.ne'
    have h0 : zetaC h ≠ 0 := hζ.ne_zero hh.ne'
    have h1 : zetaC h * (starRingEnd ℂ) (zetaC h) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; norm_num
    have h2 : zetaC h * zetaC h ^ (h - 1) = 1 := by
      rw [← pow_succ', Nat.sub_add_cancel hh, hζ.pow_eq_one]
    exact mul_left_cancel₀ h0 (h2.trans h1.symm)
  rw [hconjζ]
  have := Polynomial.aeval_algHom_apply (Complex.conjAe.toAlgHom.restrictScalars ℤ) (zetaC h) F
  simpa using this

theorem norm_aeval_primitive_small {h : ℕ} (hh : h = 3 ∨ h = 4) {ξ : ℂ}
    (hξ : IsPrimitiveRoot ξ h) (F : ℤ[X]) : ‖aeval ξ F‖ = ‖aeval (zetaC h) F‖ := by
  have hh0 : 0 < h := by omega
  haveI : NeZero h := ⟨hh0.ne'⟩
  have hζ := zetaC_isPrimitiveRoot hh0
  obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one hξ.pow_eq_one
  have hcop : i.Coprime h := (hζ.pow_iff_coprime hh0 i).1 hξ
  have hi' : i = 1 ∨ i = h - 1 := by
    rcases hh with rfl | rfl
    · interval_cases i <;> simp_all (config := {decide := true})
    · interval_cases i <;> simp_all (config := {decide := true})
  rcases hi' with rfl | rfl
  · rw [pow_one]
  · rw [aeval_pow_pred_eq_conj hh0, Complex.norm_conj]

namespace OccupancyData

variable {N : ℕ} (D : OccupancyData N)

/-- The term of type `x` in the class equation at exponent `s` for the order `h`. -/
noncomputable def term (h s : ℕ) (x : ℚ) : ℂ :=
  (x.den : ℂ) * radPow x s h * aeval (zetaC h ^ s) (D.F x)

theorem sum_term_eq_zero {h s : ℕ} (hh : h ∣ N) (h3 : 3 ≤ h) (hs : s.Coprime h) (hs1 : 1 ≤ s)
    (hsh : s < h) : ∑ x ∈ D.S, D.term h s x = 0 := by
  have hN := D.N_pos
  have hh0 : 0 < h := by omega
  have hq : 0 < N / h := Nat.div_pos (Nat.le_of_dvd hN hh) hh0
  have hNq : N / h * h = N := Nat.div_mul_cancel hh
  have hlt : N / h * s < N := by
    calc N / h * s < N / h * h := Nat.mul_lt_mul_of_pos_left hsh hq
      _ = N := hNq
  have hne : 2 * (N / h * s) ≠ N := by
    intro h2
    have : 2 * s = h := by
      apply Nat.eq_of_mul_eq_mul_left hq
      calc N / h * (2 * s) = 2 * (N / h * s) := by ring
        _ = N := h2
        _ = N / h * h := hNq.symm
    have := Nat.Coprime.eq_one_of_dvd hs ⟨2, by omega⟩
    omega
  have := D.moments (N / h * s) (Nat.one_le_iff_ne_zero.2 (by positivity)) hlt hne
  have hterm : D.term h s =
      (fun x => (x.den : ℂ) * radPow x s h * aeval (zetaC h ^ s) (D.F x)) := by
    funext x
    rfl
  rw [hterm]
  simpa only [pow_mul, zetaC_pow_div hN hh, radPow_mul_div hN hh] using this

theorem aeval_pow_eq_zero {h s : ℕ} (hh0 : 0 < h) (hs : s.Coprime h) {x : ℚ}
    (hx : aeval (zetaC h) (D.F x) = 0) : aeval (zetaC h ^ s) (D.F x) = 0 :=
  aeval_primitiveRoot_eq_zero hh0 (zetaC_isPrimitiveRoot hh0)
    ((zetaC_isPrimitiveRoot hh0).pow_of_coprime s hs) hx

theorem active_bound {h : ℕ} (hh : h ∣ N) (hh0 : 0 < h)
    (IH : ∀ e ∈ N.divisors, h < e → ∀ ξ : ℂ, IsPrimitiveRoot ξ e → ∀ y, aeval ξ (D.F y) = 0)
    {x : ℚ} (hx : aeval (zetaC h) (D.F x) ≠ 0) :
    x ∈ D.S ∧ x.num.natAbs * x.den < 5 * h := by
  have hxS : x ∈ D.S := D.support x (by rintro h0; rw [h0, map_zero] at hx; exact hx rfl)
  refine ⟨hxS, ?_⟩
  have hnorm := (cyclotomic_divisibility_norm hh0 hh D.N_pos (fun e he hlt ξ hξ => IH e he hlt ξ hξ x)
    (zetaC_isPrimitiveRoot hh0) hx).2
  change ((N / h : ℕ) : ℝ) ≤ l1norm (D.F x) at hnorm
  have hb := D.bound_type x hxS
  have hq : (0 : ℝ) < ((N / h : ℕ) : ℝ) := by
    exact_mod_cast Nat.div_pos (Nat.le_of_dvd D.N_pos hh) hh0
  have hNq : ((N / h : ℕ) : ℝ) * h = N := by exact_mod_cast Nat.div_mul_cancel hh
  have hk0 : (0 : ℝ) ≤ ((x.num.natAbs * x.den : ℕ) : ℝ) := by positivity
  have : ((x.num.natAbs * x.den : ℕ) : ℝ) * ((N / h : ℕ) : ℝ) < (5 * h) * ((N / h : ℕ) : ℝ) := by
    calc _ ≤ ((x.num.natAbs * x.den : ℕ) : ℝ) * l1norm (D.F x) :=
          mul_le_mul_of_nonneg_left hnorm hk0
      _ < 5 * N := hb
      _ = _ := by rw [← hNq]; ring
  have := lt_of_mul_lt_mul_right this hq.le
  exact_mod_cast this

open Classical in
theorem class_sum {h s : ℕ} (hh : h ∣ N) (h3 : 3 ≤ h) (hs : s.Coprime h) (hs1 : 1 ≤ s)
    (hsh : s < h) {j : ℚ} (hj : j ∈ D.S) :
    ∑ x ∈ D.S with SameCharacter h (zetaC h) x j, D.term h s x = 0 := by
  classical
  have hh0 : 0 < h := by omega
  have hζ := zetaC_isPrimitiveRoot hh0
  have hpos : ∀ x ∈ D.S, 0 < x := fun x hx => (D.type_form x hx).1
  have key := radical_classes_separate hh0 hζ D.S (fun x => radPow x s h)
    (fun x => (x.den : ℂ) * aeval (zetaC h ^ s) (D.F x))
    (fun x hx => radPow_pos (hpos x hx) s h)
    (fun x hx => by rw [radPow_pow (hpos x hx) s hh0]; exact ratCast_mem_adjoin _ _)
    (fun x hx => mul_mem (by exact_mod_cast ratCast_mem_adjoin (zetaC h) (x.den : ℚ))
      (aeval_mem_adjoin _ _ _))
    (by rw [← D.sum_term_eq_zero hh h3 hs hs1 hsh]
        exact Finset.sum_congr rfl fun x _ => by simp only [term]; ring) hj
  rw [← key]
  refine (Finset.sum_congr ?_ fun x _ => by simp only [term]; ring)
  ext x
  simp only [Finset.mem_filter, and_congr_right_iff]
  intro hx
  have hx0 := hpos x hx
  have hj0 := hpos j hj
  rw [sameCharacter_iff_rpow_mem hh0 _ hx0 hj0]
  set y : ℂ := ((((x / j : ℚ) : ℝ) ^ ((1 : ℝ) / h) : ℝ) : ℂ)
  have hr : (0 : ℝ) < ((x / j : ℚ) : ℝ) := by exact_mod_cast div_pos hx0 hj0
  have hquot : radPow x s h / radPow j s h = y ^ s := by
    simp only [radPow, y, ← Complex.ofReal_div, ← Complex.ofReal_pow]
    congr 1
    rw [← Real.div_rpow (by exact_mod_cast hx0.le) (by exact_mod_cast hj0.le), ← Real.rpow_natCast,
      ← Real.rpow_mul hr.le]
    push_cast
    congr 1; ring
  rw [hquot]
  refine (radical_class_pow_iff hs ?_ ?_).symm
  · simp only [y, ne_eq, Complex.ofReal_eq_zero]
    exact (Real.rpow_pos_of_pos hr _).ne'
  · simp only [y, ← Complex.ofReal_pow]
    rw [one_div, Real.rpow_inv_natCast_pow hr.le hh0.ne', Complex.ofReal_ratCast]
    exact ratCast_mem_adjoin _ _

open Classical in
/-- Restriction of the class equation to the active types. -/
theorem active_class_sum {h s : ℕ} (hh : h ∣ N) (h3 : 3 ≤ h) (hs : s.Coprime h) (hs1 : 1 ≤ s)
    (hsh : s < h) {j : ℚ} (hj : j ∈ D.S) :
    ∑ x ∈ D.S with (aeval (zetaC h) (D.F x) ≠ 0 ∧ SameCharacter h (zetaC h) x j),
      D.term h s x = 0 := by
  refine Eq.trans ?_ (D.class_sum hh h3 hs hs1 hsh hj)
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : aeval (zetaC h) (D.F x) = 0
  · have h0 : D.term h s x = 0 := by
      simp only [term, D.aeval_pow_eq_zero (by omega) hs hx, mul_zero]
    simp [hx, h0]
  · exact if_congr ⟨fun h' => h'.2, fun h' => ⟨hx, h'⟩⟩ rfl rfl

theorem term_nat (h s a : ℕ) :
    D.term h s (a : ℚ) = (((a : ℝ) ^ ((s : ℝ) / h) : ℝ) : ℂ) *
      aeval (zetaC h ^ s) ((D.F a).map (algebraMap ℤ ℝ)) := by
  simp only [term, radPow, Rat.den_natCast, Nat.cast_one, one_mul, Rat.cast_natCast,
    aeval_map_algebraMap]

theorem term_inv (h s : ℕ) {b : ℕ} (hb : 1 ≤ b) :
    D.term h s (1 / (b : ℚ)) = (b : ℂ) * (((b : ℝ) ^ (-(s : ℝ) / h) : ℝ) : ℂ) *
      aeval (zetaC h ^ s) ((D.F (1 / (b : ℚ))).map (algebraMap ℤ ℝ)) := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  simp only [term, radPow, aeval_map_algebraMap]
  rw [one_div, Rat.inv_natCast_den_of_pos hb]
  congr 3
  push_cast
  rw [Real.inv_rpow hb0.le, neg_div, Real.rpow_neg hb0.le]

theorem coprime_pred_self {h : ℕ} (hh : 0 < h) : (h - 1).Coprime h := by
  obtain ⟨m, rfl⟩ : ∃ m, h = m + 1 := ⟨h - 1, by omega⟩
  simp

/-- Lemma 9.20 applied to a class `{a+, b-}` of the occupancy equations. -/
theorem two_type_vanish {h : ℕ} (h3 : 3 ≤ h) {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hsum : ∀ s, s.Coprime h → 1 ≤ s → s < h → D.term h s a + D.term h s (1 / b) = 0) :
    aeval (zetaC h) (D.F a) = 0 ∧ aeval (zetaC h) (D.F (1 / b)) = 0 := by
  have hh0 : 0 < h := by omega
  have e1 := hsum 1 (Nat.coprime_one_left h) le_rfl (by omega)
  have e2 := hsum (h - 1) (coprime_pred_self hh0) (by omega) (by omega)
  rw [D.term_nat, D.term_inv _ _ (by omega)] at e1 e2
  simp only [Nat.cast_one, pow_one] at e1
  have := two_type_cancellation (by omega) (zetaC_isPrimitiveRoot hh0) ha hb
    ((D.F a).map (algebraMap ℤ ℝ)) ((D.F (1 / (b : ℚ))).map (algebraMap ℤ ℝ)) e1 e2
  simpa only [aeval_map_algebraMap] using this

theorem term_one_ne_zero {h : ℕ} {x : ℚ} (hx : 0 < x) (hF : aeval (zetaC h) (D.F x) ≠ 0) :
    D.term h 1 x ≠ 0 := by
  simp only [term, pow_one]
  exact mul_ne_zero (mul_ne_zero (by exact_mod_cast x.den_nz) (radPow_pos hx 1 h)) hF

open Classical in
theorem class_table_sum {h s : ℕ} (hh : h ∣ N) (h3 : 3 ≤ h) (hs : s.Coprime h) (hs1 : 1 ≤ s)
    (hsh : s < h)
    (IH : ∀ e ∈ N.divisors, h < e → ∀ ξ : ℂ, IsPrimitiveRoot ξ e → ∀ y, aeval ξ (D.F y) = 0)
    (C : Finset ℚ) (hsame : ∀ y ∈ C, ∀ z ∈ C, SameCharacter h (zetaC h) y z)
    (hclosed : ∀ y ∈ typeSet h, ∀ z ∈ C, SameCharacter h (zetaC h) y z → y ∈ C) :
    ∑ y ∈ C, D.term h s y = 0 := by
  have hh0 : 0 < h := by omega
  have hzero : ∀ y, aeval (zetaC h) (D.F y) = 0 → D.term h s y = 0 := fun y hy => by
    simp only [term, D.aeval_pow_eq_zero hh0 hs hy, mul_zero]
  by_cases hex : ∃ j ∈ C, aeval (zetaC h) (D.F j) ≠ 0
  · obtain ⟨j, hjC, hj⟩ := hex
    have hjS := (D.active_bound hh hh0 IH hj).1
    rw [← D.active_class_sum hh h3 hs hs1 hsh hjS]
    rw [← Finset.sum_filter_of_ne (p := fun y => aeval (zetaC h) (D.F y) ≠ 0)
      (fun y _ hy => fun h0 => hy (hzero y h0))]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext y
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hyC, hy⟩
      exact ⟨(D.active_bound hh hh0 IH hy).1, hy, hsame y hyC j hjC⟩
    · rintro ⟨hyS, hy, hyj⟩
      have hb := D.active_bound hh hh0 IH hy
      exact ⟨hclosed y (mem_typeSet_of_bound (D.type_form y hb.1) hb.2) j hjC hyj, hy⟩
  · push_neg at hex
    exact Finset.sum_eq_zero fun y hy => hzero y (hex y hy)

theorem two_pow_rpow (h : ℕ) (hh : 0 < h) (t : ℝ) : ((2 : ℝ) ^ h) ^ (t / h) = (2 : ℝ) ^ t := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  congr 1; field_simp

theorem term_one (h s : ℕ) : D.term h s 1 = aeval (zetaC h ^ s) (D.F 1) := by
  simp [term, radPow]

theorem term_two_pow (h s : ℕ) (hh : 0 < h) :
    D.term h s ((2 : ℚ) ^ h) = ((2 : ℂ) ^ s) * aeval (zetaC h ^ s) (D.F ((2 : ℚ) ^ h)) := by
  have hden : ((2 : ℚ) ^ h).den = 1 := by
    rw [show ((2 : ℚ) ^ h) = ((2 ^ h : ℕ) : ℚ) by push_cast; rfl, Rat.den_natCast]
  simp only [term, radPow, hden, Nat.cast_one, one_mul]
  congr 1
  push_cast
  rw [two_pow_rpow h hh, Real.rpow_natCast]
  push_cast; rfl

theorem term_inv_two_pow (h s : ℕ) (hh : 0 < h) :
    D.term h s (1 / (2 : ℚ) ^ h) = ((2 : ℂ) ^ h / 2 ^ s) *
      aeval (zetaC h ^ s) (D.F (1 / (2 : ℚ) ^ h)) := by
  have hden : (1 / (2 : ℚ) ^ h).den = 2 ^ h := by
    rw [show ((2 : ℚ) ^ h) = ((2 ^ h : ℕ) : ℚ) by push_cast; rfl, one_div,
      Rat.inv_natCast_den_of_pos (by positivity)]
  simp only [term, radPow, hden]
  congr 1
  push_cast
  rw [one_div, Real.inv_rpow (by positivity), two_pow_rpow h hh, Real.rpow_natCast]
  push_cast
  ring

/-- The class `{1, (2^h)+, (2^h)-}` for `h ∈ {3, 4}` (the classes `{1, 8+, 8-}` and
`{1, 16+, 16-}` of Lemma 9.21) vanishes. -/
theorem unit_triple_vanish {h : ℕ} (hh : h = 3 ∨ h = 4) (hhN : h ∣ N)
    (IH : ∀ e ∈ N.divisors, h < e → ∀ ξ : ℂ, IsPrimitiveRoot ξ e → ∀ y, aeval ξ (D.F y) = 0)
    (hsum : ∀ s, s.Coprime h → 1 ≤ s → s < h →
      D.term h s 1 + D.term h s ((2 : ℚ) ^ h) + D.term h s (1 / (2 : ℚ) ^ h) = 0) :
    aeval (zetaC h) (D.F 1) = 0 ∧ aeval (zetaC h) (D.F ((2 : ℚ) ^ h)) = 0 ∧
      aeval (zetaC h) (D.F (1 / (2 : ℚ) ^ h)) = 0 := by
  have hh0 : 0 < h := by omega
  set U := aeval (zetaC h) (D.F 1)
  set V := aeval (zetaC h) (D.F ((2 : ℚ) ^ h))
  set W := aeval (zetaC h) (D.F (1 / (2 : ℚ) ^ h))
  have e1 := hsum 1 (Nat.coprime_one_left h) le_rfl (by omega)
  have e2 := hsum (h - 1) (coprime_pred_self hh0) (by omega) (by omega)
  rw [D.term_one, D.term_two_pow _ _ hh0, D.term_inv_two_pow _ _ hh0] at e1 e2
  simp only [pow_one, aeval_pow_pred_eq_conj hh0] at e1 e2
  have e2' := congrArg (starRingEnd ℂ) e2
  simp only [map_add, map_mul, map_div₀, map_pow, map_ofNat, Complex.conj_conj, map_zero] at e2'
  -- `c' = 2^{h-1}`
  have hc : (2 : ℂ) ^ h = 2 * 2 ^ (h - 1) := by rw [← pow_succ', Nat.sub_add_cancel hh0]
  set c : ℂ := (2 : ℂ) ^ (h - 1)
  have hc2 : (2 : ℂ) ^ (h - 1) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hE1 : U + 2 * V + c * W = 0 := by
    rw [hc] at e1; linear_combination e1
  have hE2 : U + c * V + 2 * W = 0 := by
    rw [hc, mul_div_assoc, div_self hc2, mul_one] at e2'; linear_combination e2'
  have hcne : c ≠ 2 := by
    rcases hh with rfl | rfl <;> norm_num [c]
  have hVW : V = W := by
    have : (2 - c) * (V - W) = 0 := by linear_combination hE1 - hE2
    rcases mul_eq_zero.1 this with h1 | h1
    · exact absurd (sub_eq_zero.1 h1).symm hcne
    · exact sub_eq_zero.1 h1
  have hU : U = -(2 + c) * V := by rw [← hVW] at hE1; linear_combination hE1
  have hV : V = 0 := by
    by_contra hV
    obtain ⟨⟨ξ, hξ, hle⟩, -⟩ := cyclotomic_divisibility_norm hh0 hhN D.N_pos
      (fun e he hlt ξ hξ => IH e he hlt ξ hξ _) (zetaC_isPrimitiveRoot hh0) hV
    rw [norm_aeval_primitive_small hh hξ] at hle
    change _ ≤ ‖V‖ at hle
    have hUle : ‖U‖ ≤ N := (norm_aeval_le_sum_abs_coeff (D.F 1)
      ((zetaC_isPrimitiveRoot hh0).norm'_eq_one hh0.ne')).trans D.bound_one
    have hUn : ‖U‖ = ‖(2 + c)‖ * ‖V‖ := by rw [hU, norm_mul, norm_neg]
    have hq : ((N / h : ℕ) : ℝ) * h = N := by exact_mod_cast Nat.div_mul_cancel hhN
    have hqpos : (0 : ℝ) < ((N / h : ℕ) : ℝ) := by
      exact_mod_cast Nat.div_pos (Nat.le_of_dvd D.N_pos hhN) hh0
    rcases hh with rfl | rfl
    · have hcn : ‖(2 + c)‖ = 6 := by simp only [c]; norm_num
      rw [hcn] at hUn
      push_cast at hq
      nlinarith
    · have hcn : ‖(2 + c)‖ = 10 := by simp only [c]; norm_num
      rw [hcn] at hUn
      push_cast at hq
      nlinarith
  refine ⟨?_, hV, hVW ▸ hV⟩
  rw [hU, hV, mul_zero]

theorem table_sums {h : ℕ} (hh : h ∣ N) (h3 : 3 ≤ h)
    (IH : ∀ e ∈ N.divisors, h < e → ∀ ξ : ℂ, IsPrimitiveRoot ξ e → ∀ y, aeval ξ (D.F y) = 0)
    (cls : Finset (Finset ℚ))
    (hiff : ∀ x ∈ typeSet h, ∀ y ∈ typeSet h,
      (SameCharacter h (zetaC h) x y ↔ x = y ∨ ∃ C ∈ cls, x ∈ C ∧ y ∈ C))
    (hsub : ∀ C ∈ cls, ∀ y ∈ C, y ∈ typeSet h)
    (hdisj : ∀ C ∈ cls, ∀ C' ∈ cls, ∀ z ∈ C, z ∈ C' → C = C') :
    (∀ C ∈ cls, ∀ s, s.Coprime h → 1 ≤ s → s < h → ∑ y ∈ C, D.term h s y = 0) ∧
    (∀ j, aeval (zetaC h) (D.F j) ≠ 0 → (∀ C ∈ cls, j ∉ C) → False) := by
  have hh0 : 0 < h := by omega
  constructor
  · intro C hC s hs hs1 hsh
    refine D.class_table_sum hh h3 hs hs1 hsh IH C
      (fun y hy z hz => (hiff y (hsub C hC y hy) z (hsub C hC z hz)).2 (Or.inr ⟨C, hC, hy, hz⟩))
      (fun y hyT z hz hyz => ?_)
    rcases (hiff y hyT z (hsub C hC z hz)).1 hyz with rfl | ⟨C', hC', hyC', hzC'⟩
    · exact hz
    · rwa [hdisj C' hC' C hC z hzC' hz] at hyC'
  · intro j hj hjn
    have hb := D.active_bound hh hh0 IH hj
    have hjT := mem_typeSet_of_bound (D.type_form j hb.1) hb.2
    have hsum := D.class_table_sum hh h3 (Nat.coprime_one_left h) le_rfl (by omega) IH {j}
      (fun y hy z hz => by
        rw [Finset.mem_singleton] at hy hz; rw [hy, hz]
        exact (hiff j hjT j hjT).2 (Or.inl rfl))
      (fun y hyT z hz hyz => by
        rw [Finset.mem_singleton] at hz ⊢; subst hz
        rcases (hiff y hyT z hjT).1 hyz with h1 | ⟨C, hC, -, hzC⟩
        · exact h1
        · exact absurd hzC (hjn C hC))
    rw [Finset.sum_singleton] at hsum
    exact D.term_one_ne_zero (typeSet_pos hjT) hj hsum

theorem two_class_vanish {h : ℕ} (h3 : 3 ≤ h) {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hs : ∀ s, s.Coprime h → 1 ≤ s → s < h →
      ∑ y ∈ ({(a : ℚ), 1 / (b : ℚ)} : Finset ℚ), D.term h s y = 0) :
    aeval (zetaC h) (D.F a) = 0 ∧ aeval (zetaC h) (D.F (1 / b)) = 0 := by
  have hne : (a : ℚ) ≠ 1 / (b : ℚ) := by
    have h1 : (2 : ℚ) ≤ a := by exact_mod_cast ha
    have h2 : (2 : ℚ) ≤ b := by exact_mod_cast hb
    have : 1 / (b : ℚ) < 1 := by rw [div_lt_one (by linarith)]; linarith
    intro h; linarith
  refine D.two_type_vanish h3 ha hb fun s h1 h2 h3 => ?_
  have := hs s h1 h2 h3
  rwa [Finset.sum_pair hne] at this

set_option maxRecDepth 10000 in
theorem classes3_sub : ∀ C ∈ classes3, ∀ y ∈ C, y ∈ typeSet 3 := by decide +kernel
set_option maxRecDepth 10000 in
theorem classes3_disj : ∀ C ∈ classes3, ∀ C' ∈ classes3, ∀ z ∈ C, z ∈ C' → C = C' := by
  decide +kernel
set_option maxRecDepth 10000 in
theorem classes4_sub : ∀ C ∈ classes4, ∀ y ∈ C, y ∈ typeSet 4 := by decide +kernel
set_option maxRecDepth 10000 in
theorem classes4_disj : ∀ C ∈ classes4, ∀ C' ∈ classes4, ∀ z ∈ C, z ∈ C' → C = C' := by
  decide +kernel

/-- The generic orders `h ∉ {3, 4, 8}`. -/
theorem vanishing_generic {h : ℕ} (hh : h ∣ N) (h3 : 3 ≤ h) (hne3 : h ≠ 3) (hne4 : h ≠ 4)
    (hne8 : h ≠ 8)
    (IH : ∀ e ∈ N.divisors, h < e → ∀ ξ : ℂ, IsPrimitiveRoot ξ e → ∀ y, aeval ξ (D.F y) = 0)
    (x : ℚ) : aeval (zetaC h) (D.F x) = 0 := by
  classical
  by_contra hj
  have hh0 : 0 < h := by omega
  have hζ := zetaC_isPrimitiveRoot hh0
  have hact : ∀ y, aeval (zetaC h) (D.F y) ≠ 0 → y ∈ D.S ∧ y ∈ typeSet h := fun y hy =>
    have hb := D.active_bound hh hh0 IH hy
    ⟨hb.1, mem_typeSet_of_bound (D.type_form y hb.1) hb.2⟩
  obtain ⟨hjS, hjT⟩ := hact x hj
  set P := D.S.filter (fun y => aeval (zetaC h) (D.F y) ≠ 0 ∧ SameCharacter h (zetaC h) y x)
    with hPdef
  have hsumP : ∀ s, s.Coprime h → 1 ≤ s → s < h → ∑ y ∈ P, D.term h s y = 0 :=
    fun s hs hs1 hsh => D.active_class_sum hh h3 hs hs1 hsh hjS
  have hxP : x ∈ P := Finset.mem_filter.2 ⟨hjS, hj, sameCharacter_refl _ (typeSet_pos hjT).ne'⟩
  have hPT : ∀ y ∈ P, y ∈ typeSet h := fun y hy => (hact y (Finset.mem_filter.1 hy).2.1).2
  have hopp : ∀ y ∈ P, ∀ z ∈ P, y ≠ z → (1 < y ∧ z < 1) ∨ (y < 1 ∧ 1 < z) := by
    intro y hy z hz hyz
    have hS : SameCharacter h (zetaC h) y z :=
      sameCharacter_trans (Finset.mem_filter.1 hy).2.2 (Finset.mem_filter.1 hz).2.2
    by_contra hcon
    apply hyz
    apply generic_eq h3 hne3 hne4 hne8 hζ (hPT y hy) (hPT z hz) hS
    rcases le_or_gt 1 y with h1 | h1 <;> rcases le_or_gt 1 z with h2 | h2
    · exact Or.inl ⟨h1, h2⟩
    · rcases h1.lt_or_eq with h1' | h1'
      · exact absurd (Or.inl ⟨h1', h2⟩) hcon
      · exact Or.inr ⟨h1'.ge, h2.le⟩
    · rcases h2.lt_or_eq with h2' | h2'
      · exact absurd (Or.inr ⟨h1, h2'⟩) hcon
      · exact Or.inr ⟨h1.le, h2'.ge⟩
    · exact Or.inr ⟨h1.le, h2.le⟩
  by_cases hall : ∀ y ∈ P, y = x
  · have hP : P = {x} := Finset.eq_singleton_iff_unique_mem.2 ⟨hxP, hall⟩
    have := hsumP 1 (Nat.coprime_one_left h) le_rfl (by omega)
    rw [hP, Finset.sum_singleton] at this
    exact D.term_one_ne_zero (typeSet_pos hjT) hj this
  · push_neg at hall
    obtain ⟨y, hyP, hyx⟩ := hall
    have hP : P = {x, y} := by
      ext z
      constructor
      · intro hz
        by_contra hz'
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz'
        have h1 := hopp z hz x hxP hz'.1
        have h2 := hopp z hz y hyP hz'.2
        have h3 := hopp x hxP y hyP hyx.symm
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;> linarith
      · intro hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact hxP
        · exact hyP
    have hyT := hPT y hyP
    have hsum2 : ∀ s, s.Coprime h → 1 ≤ s → s < h → D.term h s x + D.term h s y = 0 := by
      intro s hs hs1 hsh
      have := hsumP s hs hs1 hsh
      rwa [hP, Finset.sum_pair hyx.symm] at this
    rcases hopp x hxP y hyP hyx.symm with ⟨hx1, hy1⟩ | ⟨hx1, hy1⟩
    · obtain ⟨a, -, -, rfl⟩ := typeSet_ge_one hh0 hjT hx1.le
      obtain ⟨b, hb1, -, rfl⟩ := typeSet_le_one hh0 hyT hy1.le
      have ha : 2 ≤ a := by
        have : (1 : ℚ) < a := hx1
        exact_mod_cast this
      have hb : 2 ≤ b := by
        by_contra hb'
        have : b = 1 := by omega
        subst this; norm_num at hy1
      exact hj (D.two_type_vanish h3 ha hb hsum2).1
    · obtain ⟨a, -, -, rfl⟩ := typeSet_ge_one hh0 hyT hy1.le
      obtain ⟨b, hb1, -, rfl⟩ := typeSet_le_one hh0 hjT hx1.le
      have ha : 2 ≤ a := by
        have : (1 : ℚ) < a := hy1
        exact_mod_cast this
      have hb : 2 ≤ b := by
        by_contra hb'
        have : b = 1 := by omega
        subst this; norm_num at hx1
      exact hj (D.two_type_vanish h3 ha hb fun s hs hs1 hsh => by
        rw [add_comm]; exact hsum2 s hs hs1 hsh).2

theorem vanishing_three
    (IH : ∀ e ∈ N.divisors, 3 < e → ∀ ξ : ℂ, IsPrimitiveRoot ξ e → ∀ y, aeval ξ (D.F y) = 0)
    (hh : 3 ∣ N) (x : ℚ) : aeval (zetaC 3) (D.F x) = 0 := by
  by_contra hj
  have T := D.table_sums hh le_rfl IH classes3
    (character_classes_three (zetaC_isPrimitiveRoot (by norm_num))) classes3_sub classes3_disj
  by_cases hin : ∃ C ∈ classes3, x ∈ C
  · obtain ⟨C, hC, hxC⟩ := hin
    have hs := T.1 C hC
    simp only [classes3, Finset.mem_insert, Finset.mem_singleton] at hC
    rcases hC with rfl | rfl | rfl | rfl | rfl
    · have := D.unit_triple_vanish (Or.inl rfl) hh IH fun s h1 h2 h3 => by
        have := hs s h1 h2 h3
        rw [Finset.sum_insert (by norm_num), Finset.sum_pair (by norm_num)] at this
        norm_num at this ⊢
        linear_combination this
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxC
      norm_num at this
      rcases hxC with rfl | rfl | rfl
      · exact hj this.1
      · exact hj this.2.1
      · exact hj (by simpa using this.2.2)
    · have := D.two_class_vanish le_rfl (a := 2) (b := 4) (by norm_num) (by norm_num)
        (by simpa using hs)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxC
      rcases hxC with rfl | rfl
      · exact hj (by simpa using this.1)
      · exact hj (by simpa using this.2)
    · have := D.two_class_vanish le_rfl (a := 4) (b := 2) (by norm_num) (by norm_num)
        (by simpa using hs)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxC
      rcases hxC with rfl | rfl
      · exact hj (by simpa using this.1)
      · exact hj (by simpa using this.2)
    · have := D.two_class_vanish le_rfl (a := 3) (b := 9) (by norm_num) (by norm_num)
        (by simpa using hs)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxC
      rcases hxC with rfl | rfl
      · exact hj (by simpa using this.1)
      · exact hj (by simpa using this.2)
    · have := D.two_class_vanish le_rfl (a := 9) (b := 3) (by norm_num) (by norm_num)
        (by simpa using hs)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxC
      rcases hxC with rfl | rfl
      · exact hj (by simpa using this.1)
      · exact hj (by simpa using this.2)
  · push_neg at hin
    exact T.2 x hj hin

theorem vanishing_four
    (IH : ∀ e ∈ N.divisors, 4 < e → ∀ ξ : ℂ, IsPrimitiveRoot ξ e → ∀ y, aeval ξ (D.F y) = 0)
    (hh : 4 ∣ N) (x : ℚ) : aeval (zetaC 4) (D.F x) = 0 := by
  by_contra hj
  have T := D.table_sums hh (by norm_num) IH classes4
    (character_classes_four (zetaC_isPrimitiveRoot (by norm_num))) classes4_sub classes4_disj
  by_cases hin : ∃ C ∈ classes4, x ∈ C
  · obtain ⟨C, hC, hxC⟩ := hin
    have hs := T.1 C hC
    simp only [classes4, Finset.mem_insert, Finset.mem_singleton] at hC
    rcases hC with rfl | rfl | rfl | rfl | rfl
    · have := D.unit_triple_vanish (Or.inr rfl) hh IH fun s h1 h2 h3 => by
        have := hs s h1 h2 h3
        rw [Finset.sum_insert (by norm_num), Finset.sum_pair (by norm_num)] at this
        norm_num at this ⊢
        linear_combination this
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxC
      norm_num at this
      rcases hxC with rfl | rfl | rfl
      · exact hj this.1
      · exact hj this.2.1
      · exact hj (by simpa using this.2.2)
    · have := D.two_class_vanish (h := 4) (by norm_num) (a := 2) (b := 8) (by norm_num) (by norm_num)
        (by simpa using hs)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxC
      rcases hxC with rfl | rfl
      · exact hj (by simpa using this.1)
      · exact hj (by simpa using this.2)
    · have := D.two_class_vanish (h := 4) (by norm_num) (a := 8) (b := 2) (by norm_num) (by norm_num)
        (by simpa using hs)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxC
      rcases hxC with rfl | rfl
      · exact hj (by simpa using this.1)
      · exact hj (by simpa using this.2)
    · have := D.two_class_vanish (h := 4) (by norm_num) (a := 4) (b := 4) (by norm_num) (by norm_num)
        (by simpa using hs)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxC
      rcases hxC with rfl | rfl
      · exact hj (by simpa using this.1)
      · exact hj (by simpa using this.2)
    · have := D.two_class_vanish (h := 4) (by norm_num) (a := 9) (b := 9) (by norm_num) (by norm_num)
        (by simpa using hs)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxC
      rcases hxC with rfl | rfl
      · exact hj (by simpa using this.1)
      · exact hj (by simpa using this.2)
  · push_neg at hin
    exact T.2 x hj hin

end OccupancyData

end ThreeIM
