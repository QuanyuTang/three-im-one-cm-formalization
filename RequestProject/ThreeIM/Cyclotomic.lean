module

public import RequestProject.ThreeIM.MathlibImports
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.NumberTheory.Cyclotomic.Gal

/-!
# Cyclotomic lemmas of Section 9 (Lemmas 9.13–9.16 and 9.18)

* Lemma 9.13 (reduction of a cyclotomic polynomial): in characteristic `p`, the roots of
  `Φ_{p^a m}` (`p ∤ m`) are exactly the elements of multiplicative order `m`.
* Lemma 9.14 (a cyclotomic unit): if `e < h` and `e ∤ h`, then `Φ_e(ζ_h)` is a unit of
  `ℤ[ζ_h]`.  We prove the stronger polynomial statement that `Φ_h` and `Φ_e` are coprime in
  `ℤ[X]`.
* Lemma 9.15 (an integral product of conjugates): for `b ∈ ℤ[X]`, the product of `b(ξ)` over
  the primitive `h`-th roots of unity `ξ` is an integer, nonzero if `b(ζ_h) ≠ 0`.
* Lemma 9.16 (divisibility at a primitive root): if `h ∣ N` and `F ∈ ℤ[X]` vanishes at all
  primitive `e`-th roots of unity for the divisors `e > h` of `N`, then `F(ζ_h) ∈ (N/h) ℤ[ζ_h]`;
  if moreover `F(ζ_h) ≠ 0`, some conjugate `F(ξ)` has modulus `≥ N/h`, and `‖F‖₁ ≥ N/h`.
* Lemma 9.18 (real radicals in a cyclotomic field), main part: a real `β ∈ ℚ(ζ_h)` with
  `β^h ∈ ℚ` is rational for odd `h`, and has rational square in general.
-/

@[expose] public section

open Polynomial IntermediateField

namespace ThreeIM

/-- **Lemma 9.13** (reduction of a cyclotomic polynomial).  Over a field of characteristic `p`,
for `p ∤ m`, the roots of `Φ_{p^a m}` are exactly the primitive `m`-th roots of unity. -/
theorem cyclotomic_charP_isRoot_iff {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    {a m : ℕ} (hm : ¬ p ∣ m) {μ : K} :
    (cyclotomic (p ^ a * m) K).IsRoot μ ↔ IsPrimitiveRoot μ m := by
  have : NeZero (m : K) := ⟨fun h => hm ((CharP.cast_eq_zero_iff K p m).1 h)⟩
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simpa using isRoot_cyclotomic_iff
  · rw [cyclotomic_mul_prime_pow_eq K hm ha, ← isRoot_cyclotomic_iff]
    have hpos : p ^ a - p ^ (a - 1) ≠ 0 := by
      have := Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (Nat.sub_lt ha one_pos)
      omega
    simp [IsRoot, eval_pow, pow_eq_zero_iff hpos]

/-- **Lemma 9.14** (a cyclotomic unit), polynomial form: if `0 < e < h` and `e ∤ h`, then the
cyclotomic polynomials `Φ_h` and `Φ_e` are coprime in `ℤ[X]`. -/
theorem cyclotomic_isCoprime_int {e h : ℕ} (he : 0 < e) (heh : e < h) (hdvd : ¬ e ∣ h) :
    IsCoprime (cyclotomic h ℤ) (cyclotomic e ℤ) := by
  rw [← isUnit_resultant_iff_isCoprime (cyclotomic.monic h ℤ), Int.isUnit_iff_natAbs_eq]
  by_contra hne
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  haveI : Fact p.Prime := ⟨hp⟩
  set L := AlgebraicClosure (ZMod p)
  have hzero : (Int.castRingHom L) (resultant (cyclotomic h ℤ) (cyclotomic e ℤ)) = 0 := by
    have : ((resultant (cyclotomic h ℤ) (cyclotomic e ℤ) : ℤ) : ZMod p) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact Int.natCast_dvd.2 hpd
    simp only [eq_intCast]
    rw [← map_intCast (algebraMap (ZMod p) L), this, map_zero]
  rw [← resultant_map_map, map_cyclotomic_int, map_cyclotomic_int, natDegree_cyclotomic,
    natDegree_cyclotomic, ← natDegree_cyclotomic h L, ← natDegree_cyclotomic e L,
    resultant_eq_prod_roots_sub _ _ (cyclotomic.monic _ _) (cyclotomic.monic _ _)
      (IsAlgClosed.splits _) (IsAlgClosed.splits _), Multiset.prod_eq_zero_iff] at hzero
  obtain ⟨⟨α, β⟩, hmem, hαβ⟩ := Multiset.mem_map.1 hzero
  rw [Multiset.mem_product] at hmem
  obtain ⟨hα, hβ⟩ := hmem
  simp only at hαβ hα hβ
  rw [sub_eq_zero] at hαβ
  subst hαβ
  rw [mem_roots (cyclotomic_ne_zero _ _)] at hα hβ
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : h ≠ 0) p hp.ne_one
  obtain ⟨b, m', hm', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : e ≠ 0) p hp.ne_one
  have h1 := (cyclotomic_charP_isRoot_iff (K := L) hm).1 hα
  have h2 := (cyclotomic_charP_isRoot_iff (K := L) hm').1 hβ
  have := h1.unique h2
  subst this
  apply hdvd
  have hab : b < a := by
    by_contra hba
    push_neg at hba
    have := Nat.pow_le_pow_right hp.pos hba
    have : p ^ a * m ≤ p ^ b * m := Nat.mul_le_mul_right _ this
    omega
  exact Nat.mul_dvd_mul_right (Nat.pow_dvd_pow p hab.le) m

/-- A primitive `h`-th root of unity is a root of `Φ_h`. -/
theorem aeval_cyclotomic_self {h : ℕ} (hh : 0 < h) {ξ : ℂ} (hξ : IsPrimitiveRoot ξ h) :
    aeval ξ (cyclotomic h ℤ) = 0 := by
  rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
  exact (isRoot_cyclotomic_iff_charZero hh).2 hξ

/-- **Lemma 9.14** (a cyclotomic unit): if `0 < e < h` and `e ∤ h`, then `Φ_e(ζ_h)` is a unit
of `ℤ[ζ_h]`: there is `G ∈ ℤ[X]` with `Φ_e(ξ) G(ξ) = 1` for every primitive `h`-th root of
unity `ξ`. -/
theorem cyclotomic_eval_isUnit {e h : ℕ} (he : 0 < e) (heh : e < h) (hdvd : ¬ e ∣ h) :
    ∃ G : ℤ[X], ∀ ξ : ℂ, IsPrimitiveRoot ξ h →
      aeval ξ (cyclotomic e ℤ) * aeval ξ G = 1 := by
  obtain ⟨u, v, huv⟩ := cyclotomic_isCoprime_int he heh hdvd
  refine ⟨v, fun ξ hξ => ?_⟩
  have := congrArg (aeval ξ) huv
  simp only [map_add, map_mul, aeval_cyclotomic_self (he.trans heh) hξ, mul_zero, zero_add,
    map_one] at this
  rw [mul_comm]; exact this

/-- **Lemma 9.15** (an integral product of conjugates), integrality: for `b ∈ ℤ[X]`, the
product of `b(ξ)` over the primitive `h`-th roots of unity is an integer. -/
theorem prod_primitiveRoots_aeval_eq_int (h : ℕ) (b : ℤ[X]) :
    ∃ z : ℤ, ∏ ξ ∈ primitiveRoots h ℂ, aeval ξ b = z := by
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · exact ⟨1, by simp⟩
  refine ⟨resultant (cyclotomic h ℤ) b (cyclotomic h ℤ).natDegree b.natDegree, ?_⟩
  have hζ := Complex.isPrimitiveRoot_exp h hh.ne'
  rw [← eq_intCast (Int.castRingHom ℂ), ← resultant_map_map, map_cyclotomic_int]
  rw [show (cyclotomic h ℤ).natDegree = (cyclotomic h ℂ).natDegree by
    simp [natDegree_cyclotomic]]
  rw [resultant_eq_prod_eval _ _ _ natDegree_map_le (IsAlgClosed.splits _),
    (cyclotomic.monic h ℂ).leadingCoeff, one_pow, one_mul,
    cyclotomic_eq_prod_X_sub_primitiveRoots hζ, roots_prod_X_sub_C]
  simp [Finset.prod_map_val, aeval_def, eval₂_eq_eval_map]

/-- If `b ∈ ℤ[X]` vanishes at one primitive `h`-th root of unity, it vanishes at all of them. -/
theorem aeval_primitiveRoot_eq_zero {h : ℕ} (hh : 0 < h) {b : ℤ[X]} {ζ ξ : ℂ}
    (hζ : IsPrimitiveRoot ζ h) (hξ : IsPrimitiveRoot ξ h) (hb : aeval ζ b = 0) :
    aeval ξ b = 0 := by
  have hd : cyclotomic h ℤ ∣ b := by
    rw [cyclotomic_eq_minpoly hζ hh]
    exact minpoly.isIntegrallyClosed_dvd (hζ.isIntegral hh) hb
  obtain ⟨c, rfl⟩ := hd
  rw [map_mul, aeval_cyclotomic_self hh hξ, zero_mul]

/-- **Lemma 9.15** (an integral product of conjugates): if `b ∈ ℤ[X]` and `b(ζ_h) ≠ 0`, then
the product of `b(ξ)` over the primitive `h`-th roots of unity is a nonzero integer. -/
theorem prod_primitiveRoots_aeval_ne_zero {h : ℕ} (hh : 0 < h) {b : ℤ[X]} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ h) (hb : aeval ζ b ≠ 0) :
    ∃ z : ℤ, z ≠ 0 ∧ ∏ ξ ∈ primitiveRoots h ℂ, aeval ξ b = z := by
  obtain ⟨z, hz⟩ := prod_primitiveRoots_aeval_eq_int h b
  refine ⟨z, ?_, hz⟩
  rintro rfl
  rw [Int.cast_zero, Finset.prod_eq_zero_iff] at hz
  obtain ⟨ξ, hξ, h0⟩ := hz
  exact hb (aeval_primitiveRoot_eq_zero hh ((mem_primitiveRoots hh).1 hξ) hζ h0)

/-- **Lemma 9.16** (divisibility at a primitive root), first part: if `h ∣ N` and `F ∈ ℤ[X]`
vanishes at every primitive `e`-th root of unity for every divisor `e > h` of `N`, then
`F(ξ) ∈ (N/h) ℤ[ξ]` for the primitive `h`-th roots of unity `ξ`, with a common witness. -/
theorem cyclotomic_divisibility {N h : ℕ} (hh : 0 < h) (hhN : h ∣ N) (hN : 0 < N) {F : ℤ[X]}
    (hF : ∀ e ∈ N.divisors, h < e → ∀ ξ : ℂ, IsPrimitiveRoot ξ e → aeval ξ F = 0) :
    ∃ b : ℤ[X], ∀ ξ : ℂ, IsPrimitiveRoot ξ h → aeval ξ F = ((N / h : ℕ) : ℂ) * aeval ξ b := by
  classical
  set S1 := N.divisors.filter (fun e => h < e) with hS1
  set S2 := N.divisors.filter (fun e => e < h ∧ ¬ e ∣ h) with hS2
  set Q := ∏ e ∈ S1, cyclotomic e ℤ with hQ
  set W := ∏ e ∈ S2, cyclotomic e ℤ with hW
  -- `Q ∣ F`
  have hQF : Q ∣ F := by
    have hQm : Q.Monic := monic_prod_of_monic _ _ (fun e _ => cyclotomic.monic e ℤ)
    rw [← map_dvd_map (Int.castRingHom ℚ) Int.cast_injective hQm, hQ, Polynomial.map_prod]
    simp_rw [map_cyclotomic_int]
    apply Finset.prod_dvd_of_coprime
    · intro i _ j _ hij
      exact cyclotomic.isCoprime_rat hij
    · intro e he
      obtain ⟨he1, he2⟩ := Finset.mem_filter.1 he
      have hepos : 0 < e := by omega
      have hξ := Complex.isPrimitiveRoot_exp e hepos.ne'
      have hd : cyclotomic e ℤ ∣ F := by
        rw [cyclotomic_eq_minpoly hξ hepos]
        exact minpoly.isIntegrallyClosed_dvd (hξ.isIntegral hepos) (hF e he1 he2 _ hξ)
      simpa using Polynomial.map_dvd (Int.castRingHom ℚ) hd
  -- `Q W (X^h - 1) = X^N - 1`
  have hsplit : Q * W * (X ^ h - 1) = X ^ N - 1 := by
    rw [← prod_cyclotomic_eq_X_pow_sub_one hh, ← prod_cyclotomic_eq_X_pow_sub_one hN,
      ← Finset.prod_filter_mul_prod_filter_not N.divisors (fun e => h < e), mul_assoc]
    congr 1
    rw [← Finset.prod_filter_mul_prod_filter_not (N.divisors.filter fun e => ¬ h < e)
      (fun e => e ∣ h), mul_comm]
    congr 1
    · apply Finset.prod_congr _ (fun _ _ => rfl)
      ext e
      simp only [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨hd, -⟩
        exact ⟨⟨⟨hd.trans hhN, hN.ne'⟩, not_lt.2 (Nat.le_of_dvd hh hd)⟩, hd⟩
      · rintro ⟨-, hd⟩
        exact ⟨hd, hh.ne'⟩
    · apply Finset.prod_congr _ (fun _ _ => rfl)
      ext e
      simp only [Finset.mem_filter, Nat.mem_divisors, hS2]
      constructor
      · rintro ⟨hN', hlt, hne⟩
        exact ⟨⟨hN', not_lt.2 hlt.le⟩, hne⟩
      · rintro ⟨⟨hN', hle⟩, hne⟩
        refine ⟨hN', lt_of_le_of_ne (not_lt.1 hle) ?_, hne⟩
        rintro rfl; exact hne dvd_rfl
  -- `Q W = ∑_{i < N/h} X^{h i}`
  obtain ⟨k, rfl⟩ := hhN
  have hk : h * k / h = k := Nat.mul_div_cancel_left k hh
  have hQW : Q * W = ∑ i ∈ Finset.range k, (X ^ h : ℤ[X]) ^ i := by
    have hne : (X ^ h - 1 : ℤ[X]) ≠ 0 := X_pow_sub_C_ne_zero hh 1
    apply mul_right_cancel₀ hne
    rw [hsplit, geom_sum_mul, pow_mul]
  -- units
  have hunit : ∀ e ∈ S2, ∃ G : ℤ[X], ∀ ξ : ℂ, IsPrimitiveRoot ξ h →
      aeval ξ (cyclotomic e ℤ) * aeval ξ G = 1 := by
    intro e he
    obtain ⟨he1, he2, he3⟩ := Finset.mem_filter.1 he
    exact cyclotomic_eval_isUnit (Nat.pos_of_mem_divisors he1) he2 he3
  choose! G hG using hunit
  obtain ⟨G₀, hG₀⟩ := hQF
  refine ⟨G₀ * ∏ e ∈ S2, G e, fun ξ hξ => ?_⟩
  have hWG : aeval ξ W * aeval ξ (∏ e ∈ S2, G e) = 1 := by
    rw [hW, map_prod, map_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun e he => hG e he ξ hξ
  have hQWe : aeval ξ (Q * W) = (k : ℂ) := by
    rw [hQW, map_sum]
    simp [← pow_mul, pow_mul ξ h, hξ.pow_eq_one]
  rw [hk, hG₀, map_mul, map_mul, ← hQWe, map_mul]
  calc aeval ξ Q * aeval ξ G₀
      = aeval ξ Q * aeval ξ G₀ * (aeval ξ W * aeval ξ (∏ e ∈ S2, G e)) := by rw [hWG, mul_one]
    _ = _ := by ring

/-- The modulus of `F(ξ)` for `|ξ| = 1` is at most the `ℓ¹`-norm of the coefficients. -/
theorem norm_aeval_le_sum_abs_coeff (F : ℤ[X]) {ξ : ℂ} (hξ : ‖ξ‖ = 1) :
    ‖aeval ξ F‖ ≤ ∑ i ∈ F.support, (|F.coeff i| : ℝ) := by
  rw [aeval_def, eval₂_eq_sum, Polynomial.sum_def]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, norm_pow, hξ, one_pow, mul_one]
  simp

/-- **Lemma 9.16** (divisibility at a primitive root), second part: under the hypotheses of
`cyclotomic_divisibility`, if `F(ζ_h) ≠ 0`, then some conjugate `F(ξ)` (`ξ` a primitive `h`-th
root of unity) has modulus at least `N/h`, and hence `‖F‖₁ ≥ N/h`. -/
theorem cyclotomic_divisibility_norm {N h : ℕ} (hh : 0 < h) (hhN : h ∣ N) (hN : 0 < N)
    {F : ℤ[X]}
    (hF : ∀ e ∈ N.divisors, h < e → ∀ ξ : ℂ, IsPrimitiveRoot ξ e → aeval ξ F = 0)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ h) (hne : aeval ζ F ≠ 0) :
    (∃ ξ : ℂ, IsPrimitiveRoot ξ h ∧ ((N / h : ℕ) : ℝ) ≤ ‖aeval ξ F‖) ∧
      ((N / h : ℕ) : ℝ) ≤ ∑ i ∈ F.support, (|F.coeff i| : ℝ) := by
  obtain ⟨b, hb⟩ := cyclotomic_divisibility hh hhN hN hF
  have hk : 0 < N / h := Nat.div_pos (Nat.le_of_dvd hN hhN) hh
  have hbζ : aeval ζ b ≠ 0 := by
    intro h0; apply hne; rw [hb ζ hζ, h0, mul_zero]
  obtain ⟨z, hz0, hz⟩ := prod_primitiveRoots_aeval_ne_zero hh hζ hbζ
  have hex : ∃ ξ : ℂ, IsPrimitiveRoot ξ h ∧ ((N / h : ℕ) : ℝ) ≤ ‖aeval ξ F‖ := by
    by_contra hcon
    push_neg at hcon
    have hlt : ∏ ξ ∈ primitiveRoots h ℂ, ‖aeval ξ F‖ <
        ∏ _ξ ∈ primitiveRoots h ℂ, ((N / h : ℕ) : ℝ) := by
      apply Finset.prod_lt_prod_of_nonempty₀
      · intro ξ hξ
        have hξ' := (mem_primitiveRoots hh).1 hξ
        rw [norm_pos_iff, hb ξ hξ']
        refine mul_ne_zero (by exact_mod_cast hk.ne') ?_
        intro h0
        exact hbζ (aeval_primitiveRoot_eq_zero hh hξ' hζ h0)
      · intro ξ hξ
        exact hcon ξ ((mem_primitiveRoots hh).1 hξ)
      · exact ⟨ζ, (mem_primitiveRoots hh).2 hζ⟩
    have heq : ∏ ξ ∈ primitiveRoots h ℂ, aeval ξ F =
        ((N / h : ℕ) : ℂ) ^ (primitiveRoots h ℂ).card * z := by
      rw [Finset.prod_congr rfl fun ξ hξ => hb ξ ((mem_primitiveRoots hh).1 hξ),
        Finset.prod_mul_distrib, hz, Finset.prod_const]
    have hnorm := congrArg norm heq
    rw [norm_prod, norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_intCast] at hnorm
    rw [hnorm, Finset.prod_const] at hlt
    have hz1 : (1 : ℝ) ≤ |(z : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hz0
    have hpos : (0 : ℝ) ≤ ((N / h : ℕ) : ℝ) ^ (primitiveRoots h ℂ).card := by positivity
    nlinarith
  refine ⟨hex, ?_⟩
  obtain ⟨ξ, hξ, hle⟩ := hex
  exact hle.trans (norm_aeval_le_sum_abs_coeff F (hξ.norm'_eq_one hh.ne'))

/-- **Lemma 9.18** (real radicals in a cyclotomic field), main part.  If a real number `β` with
`β^h ∈ ℚ` lies in `ℚ(ζ_h)`, then `β ∈ ℚ` for odd `h`, and `β² ∈ ℚ` in general.  (The paper
assumes `β > 0`; positivity is not needed.) -/
theorem real_radical_cyclotomic {h : ℕ} (hh : 0 < h) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ h) {β : ℝ}
    {r : ℚ} (hr : β ^ h = r) (hmem : (β : ℂ) ∈ ℚ⟮ζ⟯) :
    (Odd h → ∃ q : ℚ, β = q) ∧ ∃ q : ℚ, β ^ 2 = q := by
  haveI : NeZero h := ⟨hh.ne'⟩
  set K := ℚ⟮ζ⟯
  haveI : IsCyclotomicExtension {h} ℚ K := by
    change IsCyclotomicExtension {h} ℚ (IntermediateField.adjoin ℚ {ζ}).toSubalgebra
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      ((hζ.isIntegral hh).tower_top (A := ℚ)).isAlgebraic]
    exact hζ.adjoin_isCyclotomicExtension ℚ
  haveI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {h} ℚ K
  haveI : FiniteDimensional ℚ K := IsCyclotomicExtension.finiteDimensional {h} ℚ K
  -- a primitive root inside `K`
  have hζK : IsPrimitiveRoot (⟨ζ, mem_adjoin_simple_self ℚ ζ⟩ : K) h := by
    exact IsPrimitiveRoot.of_map_of_injective (f := (algebraMap K ℂ)) hζ (algebraMap K ℂ).injective
  have hcomm : ∀ σ τ : Gal(K/ℚ), σ * τ = τ * σ := by
    intro σ τ
    apply hζK.autToPow_injective ℚ
    rw [map_mul, map_mul, mul_comm]
  let c : Gal(K/ℚ) := (Complex.conjAe.restrictScalars ℚ).restrictNormal K
  have hc : ∀ x : K, ((c x : K) : ℂ) = (starRingEnd ℂ) (x : ℂ) := by
    intro x
    exact AlgEquiv.restrictNormal_commutes _ K x
  set b : K := ⟨β, hmem⟩
  have hbr : b ^ h = algebraMap ℚ K r := by
    apply Subtype.ext
    simp only [b, SubmonoidClass.coe_pow]
    rw [eq_ratCast]
    rw [← Complex.ofReal_pow, hr, Complex.ofReal_ratCast]
    rfl
  have hconj : ∀ σ : Gal(K/ℚ), ((σ b : K) : ℂ) = β ∨ (Even h ∧ ((σ b : K) : ℂ) = -β) := by
    intro σ
    -- `σ b` is real
    have hreal : (starRingEnd ℂ) ((σ b : K) : ℂ) = ((σ b : K) : ℂ) := by
      rw [← hc, ← AlgEquiv.mul_apply, hcomm, AlgEquiv.mul_apply]
      congr 2
      apply Subtype.ext
      rw [hc]; simp [b]
    obtain ⟨y, hy⟩ : ∃ y : ℝ, ((σ b : K) : ℂ) = y :=
      ⟨((σ b : K) : ℂ).re, (Complex.conj_eq_iff_re.1 hreal).symm⟩
    have hyh : y ^ h = β ^ h := by
      have : (σ b) ^ h = b ^ h := by rw [← map_pow, hbr, AlgEquiv.commutes]
      have := congrArg (fun x : K => (x : ℂ)) this
      simp only [SubmonoidClass.coe_pow, hy, b] at this
      exact_mod_cast this
    rcases (pow_eq_pow_iff_of_ne_zero hh.ne').1 hyh with h1 | ⟨h1, h2⟩
    · left; rw [hy, h1]
    · right; exact ⟨h2, by rw [hy, h1]; push_cast; ring⟩
  refine ⟨fun hodd => ?_, ?_⟩
  · have hfix : b ∈ (⊥ : IntermediateField ℚ K) := by
      rw [IsGalois.mem_bot_iff_fixed]
      intro σ
      apply Subtype.ext
      rcases hconj σ with h1 | ⟨h2, -⟩
      · rw [h1]
      · exact absurd h2 (Nat.not_even_iff_odd.2 hodd)
    obtain ⟨q, hq⟩ := IntermediateField.mem_bot.1 hfix
    refine ⟨q, ?_⟩
    have := congrArg (fun x : K => (x : ℂ)) hq
    simp [b] at this
    exact_mod_cast this.symm
  · have hfix : b ^ 2 ∈ (⊥ : IntermediateField ℚ K) := by
      rw [IsGalois.mem_bot_iff_fixed]
      intro σ
      apply Subtype.ext
      rw [map_pow]
      simp only [SubmonoidClass.coe_pow]
      rcases hconj σ with h1 | ⟨-, h1⟩ <;> simp [h1, b]
    obtain ⟨q, hq⟩ := IntermediateField.mem_bot.1 hfix
    refine ⟨q, ?_⟩
    have := congrArg (fun x : K => (x : ℂ)) hq
    simp [b] at this
    exact_mod_cast this.symm

end ThreeIM
