module

public import RequestProject.ThreeIM.Cyclotomic

/-!
# Real subfields of small cyclotomic fields and radical characters (Lemmas 9.18, 9.19, 9.20)

* Lemma 9.18, remaining assertions: `E_3 ∩ ℝ = E_4 ∩ ℝ = E_6 ∩ ℝ = ℚ`
  (`real_mem_cyclotomic_small`), `E_8 ∩ ℝ = ℚ(√2)` (`real_mem_cyclotomic_eight`,
  `sqrt_two_mem_cyclotomic_eight`) and `√2 ∉ E_{10}` (`sqrt_two_not_mem_cyclotomic_ten`).
* Lemma 9.19 (character classes outside `h ∈ {3, 4, 8}`): `radical_quotient_eq`.
* Lemma 9.20 (two-type cancellation): `two_type_cancellation`.

Here `E_h = ℚ(ζ_h) ⊆ ℂ` for a primitive `h`-th root of unity `ζ_h`.
-/

@[expose] public section

open Polynomial IntermediateField

namespace ThreeIM

/-- `ℚ(ζ)` is a cyclotomic extension when `ζ` is a primitive `h`-th root of unity. -/
theorem isCyclotomicExtension_adjoin {h : ℕ} (hh : 0 < h) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ h) :
    IsCyclotomicExtension {h} ℚ ℚ⟮ζ⟯ := by
  haveI : NeZero h := ⟨hh.ne'⟩
  change IsCyclotomicExtension {h} ℚ (IntermediateField.adjoin ℚ {ζ}).toSubalgebra
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
    ((hζ.isIntegral hh).tower_top (A := ℚ)).isAlgebraic]
  exact hζ.adjoin_isCyclotomicExtension ℚ

theorem isPrimitiveRoot_adjoin {h : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ h) :
    IsPrimitiveRoot (⟨ζ, mem_adjoin_simple_self ℚ ζ⟩ : ℚ⟮ζ⟯) h :=
  IsPrimitiveRoot.of_map_of_injective (f := (algebraMap ℚ⟮ζ⟯ ℂ)) hζ
    (algebraMap ℚ⟮ζ⟯ ℂ).injective

/-- Every unit of `ZMod h` is realized by an automorphism of `ℚ(ζ_h)`. -/
theorem autToPow_surjective_adjoin {h : ℕ} (hh : 0 < h) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ h) :
    haveI : NeZero h := ⟨hh.ne'⟩
    Function.Surjective ((isPrimitiveRoot_adjoin hζ).autToPow ℚ) := by
  haveI : NeZero h := ⟨hh.ne'⟩
  haveI := isCyclotomicExtension_adjoin hh hζ
  haveI : IsGalois ℚ ℚ⟮ζ⟯ := IsCyclotomicExtension.isGalois {h} ℚ ℚ⟮ζ⟯
  haveI : FiniteDimensional ℚ ℚ⟮ζ⟯ := IsCyclotomicExtension.finiteDimensional {h} ℚ ℚ⟮ζ⟯
  have hinj := (isPrimitiveRoot_adjoin hζ).autToPow_injective ℚ
  have hcard : Nat.card Gal(ℚ⟮ζ⟯/ℚ) = Nat.card (ZMod h)ˣ := by
    rw [IsGalois.card_aut_eq_finrank, IsCyclotomicExtension.finrank ℚ⟮ζ⟯
      (cyclotomic.irreducible_rat hh), Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  haveI : Fintype Gal(ℚ⟮ζ⟯/ℚ) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hcard
  exact ((Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, hcard⟩).2

/-- In `ℚ(ζ_h)`, an element fixed by an automorphism `σ` whose exponent generates `(ℤ/h)ˣ` is
rational. -/
theorem mem_bot_of_fixed_generator {h : ℕ} (hh : 0 < h) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ h)
    (σ : Gal(ℚ⟮ζ⟯/ℚ))
    (hgen : haveI : NeZero h := ⟨hh.ne'⟩
      ∀ v : (ZMod h)ˣ, ∃ n : ℕ, v = ((isPrimitiveRoot_adjoin hζ).autToPow ℚ σ) ^ n)
    {x : ℚ⟮ζ⟯} (hx : σ x = x) : ∃ q : ℚ, x = algebraMap ℚ ℚ⟮ζ⟯ q := by
  haveI : NeZero h := ⟨hh.ne'⟩
  haveI := isCyclotomicExtension_adjoin hh hζ
  haveI : IsGalois ℚ ℚ⟮ζ⟯ := IsCyclotomicExtension.isGalois {h} ℚ ℚ⟮ζ⟯
  haveI : FiniteDimensional ℚ ℚ⟮ζ⟯ := IsCyclotomicExtension.finiteDimensional {h} ℚ ℚ⟮ζ⟯
  have hfix : x ∈ (⊥ : IntermediateField ℚ ℚ⟮ζ⟯) := by
    rw [IsGalois.mem_bot_iff_fixed]
    intro τ
    obtain ⟨n, hn⟩ := hgen ((isPrimitiveRoot_adjoin hζ).autToPow ℚ τ)
    have hτ : τ = σ ^ n := by
      apply (isPrimitiveRoot_adjoin hζ).autToPow_injective ℚ
      rw [hn, map_pow]
    subst hτ
    clear hn
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ, AlgEquiv.mul_apply, hx, ih]
  obtain ⟨q, hq⟩ := IntermediateField.mem_bot.1 hfix
  exact ⟨q, hq.symm⟩

/-- **Lemma 9.18**, last assertion: `√2 ∉ E_{10} = ℚ(ζ_{10})`. -/
theorem sqrt_two_not_mem_cyclotomic_ten {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 10) :
    ((√2 : ℝ) : ℂ) ∉ ℚ⟮ζ⟯ := by
  intro hmem
  set K := ℚ⟮ζ⟯
  set z : K := ⟨ζ, mem_adjoin_simple_self ℚ ζ⟩
  have hz : IsPrimitiveRoot z 10 := isPrimitiveRoot_adjoin hζ
  set u3 : (ZMod 10)ˣ := ZMod.unitOfCoprime 3 (by norm_num)
  obtain ⟨σ, hσ⟩ := autToPow_surjective_adjoin (by norm_num) hζ u3
  have hσz : σ z = z ^ 3 := by
    rw [← (isPrimitiveRoot_adjoin hζ).autToPow_spec ℚ σ, hσ]
    rfl
  have hgen : ∀ v : (ZMod 10)ˣ, ∃ n : ℕ, v = ((isPrimitiveRoot_adjoin hζ).autToPow ℚ σ) ^ n := by
    rw [hσ]
    have : ∀ v : (ZMod 10)ˣ, ∃ n < 4, v = u3 ^ n := by decide
    intro v
    obtain ⟨n, -, hn⟩ := this v
    exact ⟨n, hn⟩
  have hrat : ∀ x : K, σ x = x → ∃ q : ℚ, x = algebraMap ℚ K q :=
    fun x hx => mem_bot_of_fixed_generator (by norm_num) hζ σ hgen hx
  have h10 : z ^ 10 = 1 := hz.pow_eq_one
  have h2 : z ^ 2 ≠ 1 := hz.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have hgeom : 1 + z ^ 2 + z ^ 4 + z ^ 6 + z ^ 8 = 0 := by
    have : (z ^ 2 - 1) * (1 + z ^ 2 + z ^ 4 + z ^ 6 + z ^ 8) = 0 := by
      linear_combination h10
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) h2
    · exact h
  set s : K := 1 + 2 * (z ^ 2 + z ^ 8)
  have hs2 : s ^ 2 = 5 := by
    simp only [s]
    linear_combination (4 : K) * hgeom + (8 + 4 * z ^ 6) * h10
  have hσs : σ s = -s := by
    simp only [s, map_add, map_mul, map_pow, hσz, map_one, map_ofNat]
    linear_combination (2 : K) * hgeom + 2 * z ^ 4 * (z ^ 10 + 1) * h10
  set r : K := ⟨((√2 : ℝ) : ℂ), hmem⟩
  have hr2 : r ^ 2 = 2 := by
    apply Subtype.ext
    simp only [r, SubmonoidClass.coe_pow]
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_cast
  have hσr : σ r ^ 2 = r ^ 2 := by rw [← map_pow, hr2, map_ofNat]
  have hcoe : ∀ q : ℚ, ((algebraMap ℚ K q : K) : ℂ) = (q : ℂ) := fun q => rfl
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hσr with h | h
  · obtain ⟨q, hq⟩ := hrat r h
    have := congrArg (fun x : K => (x : ℂ)) hq
    simp only [r, hcoe] at this
    exact irrational_sqrt_two ⟨q, by exact_mod_cast this.symm⟩
  · obtain ⟨q, hq⟩ := hrat (r * s) (by rw [map_mul, h, hσs]; ring)
    have hq2 : algebraMap ℚ K (q ^ 2) = 10 := by
      rw [map_pow, ← hq, mul_pow, hr2, hs2]; norm_num
    have hq2' : q ^ 2 = 10 := by
      have := congrArg (fun x : K => (x : ℂ)) hq2
      simp only [hcoe] at this
      exact_mod_cast this
    have hns : ¬ IsSquare (10 : ℕ) := by
      rintro ⟨m, hm⟩
      have : m ≤ 4 := by nlinarith
      interval_cases m <;> omega
    apply (irrational_sqrt_natCast_iff.2 hns)
    refine ⟨|q|, ?_⟩
    rw [Rat.cast_abs, ← Real.sqrt_sq (abs_nonneg (q : ℝ)), sq_abs]
    congr 1
    exact_mod_cast hq2'

/-- Two automorphisms whose exponents generate `(ℤ/h)ˣ`: their common fixed points in `ℚ(ζ_h)`
are rational. -/
theorem mem_bot_of_fixed_generators₂ {h : ℕ} (hh : 0 < h) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ h)
    (σ τ : Gal(ℚ⟮ζ⟯/ℚ))
    (hgen : haveI : NeZero h := ⟨hh.ne'⟩
      ∀ v : (ZMod h)ˣ, ∃ m n : ℕ, v = ((isPrimitiveRoot_adjoin hζ).autToPow ℚ σ) ^ m *
        ((isPrimitiveRoot_adjoin hζ).autToPow ℚ τ) ^ n)
    {x : ℚ⟮ζ⟯} (hσ : σ x = x) (hτ : τ x = x) : ∃ q : ℚ, x = algebraMap ℚ ℚ⟮ζ⟯ q := by
  haveI : NeZero h := ⟨hh.ne'⟩
  haveI := isCyclotomicExtension_adjoin hh hζ
  haveI : IsGalois ℚ ℚ⟮ζ⟯ := IsCyclotomicExtension.isGalois {h} ℚ ℚ⟮ζ⟯
  haveI : FiniteDimensional ℚ ℚ⟮ζ⟯ := IsCyclotomicExtension.finiteDimensional {h} ℚ ℚ⟮ζ⟯
  have hpow : ∀ (ρ : Gal(ℚ⟮ζ⟯/ℚ)), ρ x = x → ∀ n : ℕ, (ρ ^ n) x = x := by
    intro ρ hρ n
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ, AlgEquiv.mul_apply, hρ, ih]
  have hfix : x ∈ (⊥ : IntermediateField ℚ ℚ⟮ζ⟯) := by
    rw [IsGalois.mem_bot_iff_fixed]
    intro ρ
    obtain ⟨m, n, hn⟩ := hgen ((isPrimitiveRoot_adjoin hζ).autToPow ℚ ρ)
    have hρ : ρ = σ ^ m * τ ^ n := by
      apply (isPrimitiveRoot_adjoin hζ).autToPow_injective ℚ
      rw [hn, map_mul, map_pow, map_pow]
    rw [hρ, AlgEquiv.mul_apply, hpow τ hτ, hpow σ hσ]
  obtain ⟨q, hq⟩ := IntermediateField.mem_bot.1 hfix
  exact ⟨q, hq.symm⟩

/-- The exponent of an automorphism of `ℚ(ζ_h)` is read off from its action on `ζ_h`. -/
theorem autToPow_eq_of_apply {h : ℕ} (hh : 0 < h) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ h)
    (σ : Gal(ℚ⟮ζ⟯/ℚ)) {k : ℕ} (hk : k < h)
    (hσ : σ ⟨ζ, mem_adjoin_simple_self ℚ ζ⟩ = ⟨ζ, mem_adjoin_simple_self ℚ ζ⟩ ^ k) :
    haveI : NeZero h := ⟨hh.ne'⟩
    (((isPrimitiveRoot_adjoin hζ).autToPow ℚ σ : (ZMod h)ˣ) : ZMod h) = k := by
  haveI : NeZero h := ⟨hh.ne'⟩
  have hspec := (isPrimitiveRoot_adjoin hζ).autToPow_spec ℚ σ
  rw [hσ] at hspec
  have := (isPrimitiveRoot_adjoin hζ).pow_inj (ZMod.val_lt _) hk hspec
  rw [← ZMod.natCast_zmod_val (((isPrimitiveRoot_adjoin hζ).autToPow ℚ σ : (ZMod h)ˣ) : ZMod h),
    this]

/-- Complex conjugation restricted to `ℚ(ζ_h)`; it acts on `ζ_h` as `ζ_h ↦ ζ_h^{h-1}`. -/
theorem exists_conj_aut {h : ℕ} (hh : 0 < h) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ h) :
    ∃ c : Gal(ℚ⟮ζ⟯/ℚ), (∀ x : ℚ⟮ζ⟯, ((c x : ℚ⟮ζ⟯) : ℂ) = (starRingEnd ℂ) (x : ℂ)) ∧
      c ⟨ζ, mem_adjoin_simple_self ℚ ζ⟩ = ⟨ζ, mem_adjoin_simple_self ℚ ζ⟩ ^ (h - 1) := by
  haveI : NeZero h := ⟨hh.ne'⟩
  haveI := isCyclotomicExtension_adjoin hh hζ
  haveI : IsGalois ℚ ℚ⟮ζ⟯ := IsCyclotomicExtension.isGalois {h} ℚ ℚ⟮ζ⟯
  let c : Gal(ℚ⟮ζ⟯/ℚ) := (Complex.conjAe.restrictScalars ℚ).restrictNormal ℚ⟮ζ⟯
  have hc : ∀ x : ℚ⟮ζ⟯, ((c x : ℚ⟮ζ⟯) : ℂ) = (starRingEnd ℂ) (x : ℂ) := fun x =>
    AlgEquiv.restrictNormal_commutes _ ℚ⟮ζ⟯ x
  refine ⟨c, hc, Subtype.ext ?_⟩
  rw [hc, SubmonoidClass.coe_pow]
  change (starRingEnd ℂ) ζ = ζ ^ (h - 1)
  have hn : ‖ζ‖ = 1 := hζ.norm'_eq_one hh.ne'
  have h0 : ζ ≠ 0 := hζ.ne_zero hh.ne'
  have h1 : ζ * (starRingEnd ℂ) ζ = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; norm_num
  have h2 : ζ * ζ ^ (h - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel hh, hζ.pow_eq_one]
  exact mul_left_cancel₀ h0 (h1.trans h2.symm)

/-- **Lemma 9.18**, first part of the second assertion: `E_3 ∩ ℝ = E_4 ∩ ℝ = E_6 ∩ ℝ = ℚ`. -/
theorem real_mem_cyclotomic_small {h : ℕ} (hh : h = 3 ∨ h = 4 ∨ h = 6) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ h) {β : ℝ} (hmem : (β : ℂ) ∈ ℚ⟮ζ⟯) : ∃ q : ℚ, β = q := by
  have hh0 : 0 < h := by rcases hh with rfl | rfl | rfl <;> norm_num
  haveI : NeZero h := ⟨hh0.ne'⟩
  obtain ⟨c, hc, hcz⟩ := exists_conj_aut hh0 hζ
  have hcpow := autToPow_eq_of_apply hh0 hζ c (Nat.sub_lt hh0 one_pos) hcz
  have hgen : ∀ v : (ZMod h)ˣ, ∃ n : ℕ, v = ((isPrimitiveRoot_adjoin hζ).autToPow ℚ c) ^ n := by
    generalize (isPrimitiveRoot_adjoin hζ).autToPow ℚ c = u at hcpow
    rcases hh with rfl | rfl | rfl
    · have : ∀ u v : (ZMod 3)ˣ, (u : ZMod 3) = 2 → ∃ n < 2, v = u ^ n := by decide
      intro v; obtain ⟨n, -, hn⟩ := this u v hcpow; exact ⟨n, hn⟩
    · have : ∀ u v : (ZMod 4)ˣ, (u : ZMod 4) = 3 → ∃ n < 2, v = u ^ n := by decide
      intro v; obtain ⟨n, -, hn⟩ := this u v hcpow; exact ⟨n, hn⟩
    · have : ∀ u v : (ZMod 6)ˣ, (u : ZMod 6) = 5 → ∃ n < 2, v = u ^ n := by decide
      intro v; obtain ⟨n, -, hn⟩ := this u v hcpow; exact ⟨n, hn⟩
  obtain ⟨q, hq⟩ := mem_bot_of_fixed_generator hh0 hζ c hgen (x := ⟨β, hmem⟩)
    (Subtype.ext (by rw [hc]; simp))
  refine ⟨q, ?_⟩
  have := congrArg (fun x : ℚ⟮ζ⟯ => (x : ℂ)) hq
  simp only [eq_ratCast] at this
  exact Complex.ofReal_injective (this.trans (Complex.ofReal_ratCast q).symm)

/-- For a primitive `8`-th root `ζ`, `(ζ + ζ⁷)² = 2`; hence `ζ + ζ⁷ = ±√2`. -/
theorem cyclotomic_eight_sqrt_two {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 8) :
    ζ + ζ ^ 7 = ((√2 : ℝ) : ℂ) ∨ ζ + ζ ^ 7 = -((√2 : ℝ) : ℂ) := by
  have h8 : ζ ^ 8 = 1 := hζ.pow_eq_one
  have h4 : ζ ^ 4 + 1 = 0 := by
    have h4' : ζ ^ 4 ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
    have : (ζ ^ 4 - 1) * (ζ ^ 4 + 1) = 0 := by linear_combination h8
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) h4'
    · exact h
  apply sq_eq_sq_iff_eq_or_eq_neg.1
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
  push_cast
  linear_combination (2 + ζ ^ 6) * h8 + ζ ^ 2 * h4

/-- `√2 ∈ E_8`. -/
theorem sqrt_two_mem_cyclotomic_eight {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 8) :
    ((√2 : ℝ) : ℂ) ∈ ℚ⟮ζ⟯ := by
  have hw : ζ + ζ ^ 7 ∈ ℚ⟮ζ⟯ :=
    add_mem (mem_adjoin_simple_self ℚ ζ) (pow_mem (mem_adjoin_simple_self ℚ ζ) 7)
  rcases cyclotomic_eight_sqrt_two hζ with h | h
  · rwa [← h]
  · rw [← neg_neg ((√2 : ℝ) : ℂ), ← h]; exact neg_mem hw

/-- **Lemma 9.18**, second part of the second assertion: `E_8 ∩ ℝ = ℚ(√2)`. -/
theorem real_mem_cyclotomic_eight {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 8) {β : ℝ}
    (hmem : (β : ℂ) ∈ ℚ⟮ζ⟯) : ∃ x y : ℚ, β = x + y * √2 := by
  haveI : NeZero 8 := ⟨by norm_num⟩
  haveI := isCyclotomicExtension_adjoin (h := 8) (by norm_num) hζ
  set K := ℚ⟮ζ⟯
  set z : K := ⟨ζ, mem_adjoin_simple_self ℚ ζ⟩
  have hz : IsPrimitiveRoot z 8 := isPrimitiveRoot_adjoin hζ
  have h8 : z ^ 8 = 1 := hz.pow_eq_one
  have h4 : z ^ 4 + 1 = 0 := by
    have h4' : z ^ 4 ≠ 1 := hz.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
    have : (z ^ 4 - 1) * (z ^ 4 + 1) = 0 := by linear_combination h8
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) h4'
    · exact h
  set u3 : (ZMod 8)ˣ := ZMod.unitOfCoprime 3 (by norm_num)
  obtain ⟨σ, hσ⟩ := autToPow_surjective_adjoin (by norm_num) hζ u3
  have hσz : σ z = z ^ 3 := by
    rw [← (isPrimitiveRoot_adjoin hζ).autToPow_spec ℚ σ, hσ]
    rfl
  obtain ⟨c, hc, hcz⟩ := exists_conj_aut (by norm_num) hζ
  rw [show (8 : ℕ) - 1 = 7 from rfl] at hcz
  have hcpow := autToPow_eq_of_apply (by norm_num) hζ c (k := 7) (by norm_num) hcz
  have hσσ : ∀ y : K, σ (σ y) = y := by
    intro y
    have : σ * σ = 1 := by
      apply (isPrimitiveRoot_adjoin hζ).autToPow_injective ℚ
      rw [map_mul, map_one, hσ]
      decide
    rw [← AlgEquiv.mul_apply, this, AlgEquiv.one_apply]
  have hcσ : ∀ y : K, c (σ y) = σ (c y) := by
    intro y
    rw [← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply]
    congr 1
    apply (isPrimitiveRoot_adjoin hζ).autToPow_injective ℚ
    rw [map_mul, map_mul, mul_comm]
  have hgen : ∀ v : (ZMod 8)ˣ, ∃ m n : ℕ, v = ((isPrimitiveRoot_adjoin hζ).autToPow ℚ σ) ^ m *
      ((isPrimitiveRoot_adjoin hζ).autToPow ℚ c) ^ n := by
    rw [hσ]
    generalize (isPrimitiveRoot_adjoin hζ).autToPow ℚ c = u at hcpow
    have : ∀ u v : (ZMod 8)ˣ, (u : ZMod 8) = 7 → ∃ m < 2, ∃ n < 2, v = u3 ^ m * u ^ n := by
      intro u v hu
      have hfinite : ∀ x : ZMod 8, Nat.Coprime x.val 8 →
          ∃ m < 2, ∃ n < 2, x = (3 : ZMod 8) ^ m * (7 : ZMod 8) ^ n := by
        intro x hx
        fin_cases x <;> norm_num [ZMod.val] at hx
        all_goals first
          | (refine ⟨0, by decide, 0, by decide, ?_⟩; norm_num <;> rfl)
          | (refine ⟨1, by decide, 0, by decide, ?_⟩; norm_num <;> rfl)
          | (refine ⟨1, by decide, 1, by decide, ?_⟩; norm_num <;> rfl)
          | (refine ⟨0, by decide, 1, by decide, ?_⟩; norm_num <;> rfl)
      obtain ⟨m, hm, n, hn, h⟩ := hfinite (v : ZMod 8) (ZMod.unitsEquivCoprime v).property
      refine ⟨m, hm, n, hn, ?_⟩
      apply Units.ext
      simpa [u3, hu] using h
    intro v
    obtain ⟨m, -, n, -, hn⟩ := this u v hcpow
    exact ⟨m, n, hn⟩
  have hrat : ∀ y : K, σ y = y → c y = y → ∃ q : ℚ, y = algebraMap ℚ K q :=
    fun y h1 h2 => mem_bot_of_fixed_generators₂ (by norm_num) hζ σ c hgen h1 h2
  set w : K := z + z ^ 7
  have hw2 : w ^ 2 = 2 := by
    simp only [w]; linear_combination (2 + z ^ 6) * h8 + z ^ 2 * h4
  have hσw : σ w = -w := by
    simp only [w, map_add, map_pow, hσz]
    linear_combination (z ^ 13 + z ^ 5) * h8 + (z + z ^ 3) * h4
  have hcw : c w = w := by
    change c (z + z ^ 7) = z + z ^ 7
    rw [map_add, map_pow, hcz]
    linear_combination (z ^ 41 + z ^ 33 + z ^ 25 + z ^ 17 + z ^ 9 + z) * h8
  set x : K := ⟨β, hmem⟩
  have hcx : c x = x := Subtype.ext (by rw [hc]; simp [x])
  obtain ⟨q1, hq1⟩ := hrat (x + σ x) (by rw [map_add, hσσ, add_comm])
    (by rw [map_add, hcσ, hcx])
  obtain ⟨q2, hq2⟩ := hrat ((x - σ x) * w) (by rw [map_mul, map_sub, hσσ, hσw]; ring)
    (by rw [map_mul, map_sub, hcσ, hcx, hcw])
  have hx : x = algebraMap ℚ K (q1 / 2) + algebraMap ℚ K (q2 / 4) * w := by
    rw [map_div₀, map_div₀, ← hq1, ← hq2]
    simp only [map_ofNat]
    linear_combination (-(x - σ x) / 4) * hw2
  have hxC := congrArg (fun y : K => (y : ℂ)) hx
  simp only [x, w, z, IntermediateField.coe_add, IntermediateField.coe_mul, eq_ratCast,
    SubmonoidClass.coe_pow] at hxC
  change (β : ℂ) = ((q1 / 2 : ℚ) : ℂ) + ((q2 / 4 : ℚ) : ℂ) * (ζ + ζ ^ 7) at hxC
  rcases cyclotomic_eight_sqrt_two hζ with h | h
  · refine ⟨q1 / 2, q2 / 4, Complex.ofReal_injective ?_⟩
    rw [hxC, h]; push_cast; ring
  · refine ⟨q1 / 2, -(q2 / 4), Complex.ofReal_injective ?_⟩
    rw [hxC, h]; push_cast; ring

/-- If `q^m = a/b` for positive integers `a, b`, then (with `q = ±n/d` in lowest terms)
`n^m ∣ a`, `d^m ∣ b` and `n^m b = a d^m`. -/
theorem rat_pow_eq_div_bounds {m : ℕ} (q : ℚ) {a b : ℕ} (hb : 0 < b) (hq : q ^ m = a / b) :
    q.num.natAbs ^ m ∣ a ∧ q.den ^ m ∣ b ∧ q.num.natAbs ^ m * b = a * q.den ^ m := by
  have hden : (q.den : ℚ) ≠ 0 := by positivity
  have hZ : q.num ^ m * b = a * q.den ^ m := by
    have h1 : q = q.num / q.den := (Rat.num_div_den q).symm
    rw [h1, div_pow, div_eq_div_iff (pow_ne_zero _ hden) (by positivity)] at hq
    exact_mod_cast hq
  have hN : q.num.natAbs ^ m * b = a * q.den ^ m := by
    have := congrArg Int.natAbs hZ
    simpa [Int.natAbs_mul, Int.natAbs_pow] using this
  have hcop : (q.num.natAbs ^ m).Coprime (q.den ^ m) := q.reduced.pow m m
  refine ⟨?_, ?_, hN⟩
  · exact hcop.dvd_of_dvd_mul_right ⟨b, hN.symm⟩
  · exact hcop.symm.dvd_of_dvd_mul_left ⟨a, by rw [hN, mul_comm]⟩

/-- If `a/b` is the `m`-th power of a rational number and `0 < a, b < 2^m`, then `a = b`. -/
theorem eq_of_rat_pow_eq_div {m : ℕ} (hm : 0 < m) (q : ℚ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hq : q ^ m = a / b) (ha' : a < 2 ^ m) (hb' : b < 2 ^ m) : a = b := by
  obtain ⟨hn, hd, hN⟩ := rat_pow_eq_div_bounds q hb hq
  have hd1 : q.den < 2 :=
    (Nat.pow_lt_pow_iff_left hm.ne').1 ((Nat.le_of_dvd hb hd).trans_lt hb')
  have hn1 : q.num.natAbs < 2 :=
    (Nat.pow_lt_pow_iff_left hm.ne').1 ((Nat.le_of_dvd ha hn).trans_lt ha')
  have hd0 : q.den = 1 := by have := q.den_pos; omega
  rw [hd0, one_pow, mul_one] at hN
  interval_cases hq0 : q.num.natAbs
  · rw [zero_pow hm.ne', zero_mul] at hN; omega
  · rw [one_pow, one_mul] at hN; exact hN.symm

theorem five_mul_lt_two_pow {k : ℕ} (hk : 5 ≤ k) : 5 * k < 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ]; omega

theorem ten_mul_lt_two_pow {k : ℕ} (hk : 6 ≤ k) : 10 * k < 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ]; omega

/-- **Lemma 9.19** (character classes outside three small orders), arithmetic core.  Let
`h ≥ 3`, `h ∉ {3, 4, 8}`, and let `1 ≤ a, b < 5h`.  If a real number `β` with `β^h = a/b` lies in
`E_h = ℚ(ζ_h)` (that is, the radicals `a^{1/h}` and `b^{1/h}` have the same character over
`E_h`), then `a = b`.  Taking `a` or `b` equal to `1` covers the unit radical, and taking
reciprocals covers interior radicals; so the unit radical is alone in its class and every other
class contains at most one exterior and at most one interior radical. -/
theorem radical_quotient_eq {h : ℕ} (h3 : 3 ≤ h) (hne3 : h ≠ 3) (hne4 : h ≠ 4) (hne8 : h ≠ 8)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ h) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (ha' : a < 5 * h)
    (hb' : b < 5 * h) {β : ℝ} (hβ : β ^ h = (a : ℝ) / b) (hmem : (β : ℂ) ∈ ℚ⟮ζ⟯) : a = b := by
  have hr : β ^ h = ((a / b : ℚ) : ℝ) := by push_cast; exact hβ
  obtain ⟨hodd, q2, hq2⟩ := real_radical_cyclotomic (by omega) hζ hr hmem
  rcases Nat.even_or_odd h with ⟨k, hk⟩ | hodd'
  · have hq2k : q2 ^ k = (a : ℚ) / b := by
      have : ((q2 ^ k : ℚ) : ℝ) = ((a / b : ℚ) : ℝ) := by
        rw [Rat.cast_pow, ← hq2, ← pow_mul, ← hr, hk, two_mul]
      exact_mod_cast this
    by_cases hk6 : 6 ≤ k
    · have := ten_mul_lt_two_pow hk6
      exact eq_of_rat_pow_eq_div (by omega) q2 ha hb hq2k (by omega) (by omega)
    · have hk35 : k = 3 ∨ k = 5 := by omega
      rcases hk35 with rfl | rfl
      · -- `h = 6`: the real subfield of `E_6` is `ℚ`
        obtain ⟨q, hq⟩ := real_mem_cyclotomic_small (by omega) hζ hmem
        have hq6 : q ^ 6 = (a : ℚ) / b := by
          have : ((q ^ 6 : ℚ) : ℝ) = ((a / b : ℚ) : ℝ) := by
            rw [Rat.cast_pow, ← hq, ← hr, hk]
          exact_mod_cast this
        exact eq_of_rat_pow_eq_div (by norm_num) q ha hb hq6 (by omega) (by omega)
      · -- `h = 10`: use `√2 ∉ E_{10}`
        subst hk
        have hζ10 : IsPrimitiveRoot ζ 10 := hζ
        obtain ⟨hn, hd, hN⟩ := rat_pow_eq_div_bounds q2 hb hq2k
        have hn2 : q2.num.natAbs ≤ 2 := by
          by_contra hcon
          have := Nat.pow_le_pow_left (show 3 ≤ q2.num.natAbs by omega) 5
          have := Nat.le_of_dvd ha hn
          omega
        have hd2 : q2.den ≤ 2 := by
          by_contra hcon
          have := Nat.pow_le_pow_left (show 3 ≤ q2.den by omega) 5
          have := Nat.le_of_dvd hb hd
          omega
        have hq2nn : 0 ≤ q2 := by
          have : (0 : ℝ) ≤ q2 := by rw [← hq2]; positivity
          exact_mod_cast this
        have hnum : q2.num = q2.num.natAbs := (Int.natAbs_of_nonneg (Rat.num_nonneg.2 hq2nn)).symm
        have hq2eq : q2 = (q2.num.natAbs : ℚ) / q2.den := by
          rw [← Int.cast_natCast, ← hnum, Rat.num_div_den]
        have hcop := q2.reduced
        have hden0 := q2.den_pos
        have hβK : ∀ c : ℚ, ((c * β : ℝ) : ℂ) ∈ ℚ⟮ζ⟯ := fun c => by
          push_cast
          exact mul_mem (by rw [← eq_ratCast (algebraMap ℚ ℂ)]; exact IntermediateField.algebraMap_mem _ c) hmem
        have habs : ∀ c : ℚ, (((|c * β| : ℝ)) : ℂ) ∈ ℚ⟮ζ⟯ := fun c => by
          rcases abs_choice (c * β) with h | h
          · rw [h]; exact hβK c
          · rw [h, Complex.ofReal_neg]; exact neg_mem (hβK c)
        have hsqrt : ∀ c : ℚ, (c * β) ^ 2 = 2 → False := fun c hc => by
          apply sqrt_two_not_mem_cyclotomic_ten hζ10
          rw [← hc, Real.sqrt_sq_eq_abs]
          exact habs c
        interval_cases hn' : q2.num.natAbs <;> interval_cases hd' : q2.den
        · simp at hN; omega
        · simp at hn; omega
        · simp at hN; omega
        · -- `β² = 1/2`
          exfalso
          apply hsqrt 2
          rw [mul_pow, hq2, hq2eq]; push_cast; norm_num
        · -- `β² = 2`
          exfalso
          apply hsqrt 1
          rw [mul_pow, hq2, hq2eq]; push_cast; norm_num
        · norm_num at hcop
  · obtain ⟨q, hq⟩ := hodd hodd'
    have hqh : q ^ h = (a : ℚ) / b := by
      have : ((q ^ h : ℚ) : ℝ) = ((a / b : ℚ) : ℝ) := by rw [Rat.cast_pow, ← hq, ← hr]
      exact_mod_cast this
    have h5 : 5 ≤ h := by obtain ⟨j, rfl⟩ := hodd'; omega
    have := five_mul_lt_two_pow h5
    exact eq_of_rat_pow_eq_div (by omega) q ha hb hqh (by omega) (by omega)

/-- Linear algebra behind Lemma 9.20: the system `α A + γ^{h-1} B = 0`,
`α^{h-1} A + γ B = 0` with `α, γ > 0`, `αγ ≠ 1`, `h > 2` has only the zero solution. -/
theorem two_type_core {h : ℕ} (hh : 2 < h) {α γ : ℝ} (hα : 0 < α) (hγ : 0 < γ)
    (hαγ : α * γ ≠ 1) {A B : ℂ} (e1 : (α : ℂ) * A + (γ : ℂ) ^ (h - 1) * B = 0)
    (e2 : (α : ℂ) ^ (h - 1) * A + (γ : ℂ) * B = 0) : A = 0 ∧ B = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, h = n + 3 := ⟨h - 3, by omega⟩
  simp only [show n + 3 - 1 = n + 2 by omega] at e1 e2
  set D : ℂ := (α : ℂ) * γ - (α : ℂ) ^ (n + 2) * (γ : ℂ) ^ (n + 2)
  have hD : D ≠ 0 := by
    have hD' : D = (((α * γ) * (1 - (α * γ) ^ (n + 1)) : ℝ) : ℂ) := by
      simp only [D]; push_cast; ring
    rw [hD', Complex.ofReal_ne_zero]
    refine mul_ne_zero (by positivity) (sub_ne_zero.2 (Ne.symm ?_))
    rw [Ne, pow_eq_one_iff_of_nonneg (by positivity) (by omega)]
    exact hαγ
  have hA : D * A = 0 := by
    linear_combination (γ : ℂ) * e1 - (γ : ℂ) ^ (n + 2) * e2
  have hB : D * B = 0 := by
    linear_combination (α : ℂ) * e2 - (α : ℂ) ^ (n + 2) * e1
  exact ⟨(mul_eq_zero.1 hA).resolve_left hD, (mul_eq_zero.1 hB).resolve_left hD⟩

theorem rpow_div_eq_pow_rpow {x : ℝ} (hx : 0 < x) (h k : ℕ) :
    x ^ ((k : ℝ) / h) = (x ^ ((1 : ℝ) / h)) ^ k := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
  congr 1; ring

/-- **Lemma 9.20** (two-type cancellation).  Let `h > 2`, let `ζ` be a primitive `h`-th root of
unity, and let `a, b ≥ 2`.  Suppose a character class consists of the exterior type `a+`
(multiplicity `1`, radius power `a^{s/h}`) and the interior type `b-` (multiplicity `b`, radius
power `b^{-s/h}`), with real occupancy polynomials `F = F_{a+}` and `G = F_{b-}`.  If the class
equations at the primitive exponents `s = 1` and `s = h - 1` hold, then `F(ζ) = G(ζ) = 0`. -/
theorem two_type_cancellation {h : ℕ} (hh : 2 < h) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ h) {a b : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (F G : ℝ[X])
    (e1 : (((a : ℝ) ^ ((1 : ℝ) / h) : ℝ) : ℂ) * aeval ζ F +
      (b : ℂ) * (((b : ℝ) ^ (-(1 : ℝ) / h) : ℝ) : ℂ) * aeval ζ G = 0)
    (e2 : (((a : ℝ) ^ (((h - 1 : ℕ) : ℝ) / h) : ℝ) : ℂ) * aeval (ζ ^ (h - 1)) F +
      (b : ℂ) * (((b : ℝ) ^ (-((h - 1 : ℕ) : ℝ) / h) : ℝ) : ℂ) * aeval (ζ ^ (h - 1)) G = 0) :
    aeval ζ F = 0 ∧ aeval ζ G = 0 := by
  have hh0 : 0 < h := by omega
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  set α : ℝ := (a : ℝ) ^ ((1 : ℝ) / h)
  set γ : ℝ := (b : ℝ) ^ ((1 : ℝ) / h)
  have hα : 0 < α := Real.rpow_pos_of_pos ha0 _
  have hγ : 0 < γ := Real.rpow_pos_of_pos hb0 _
  have hγh : γ ^ h = b := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb0.le, one_div_mul_cancel (by positivity),
      Real.rpow_one]
  have hαh : α ^ h = a := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha0.le, one_div_mul_cancel (by positivity),
      Real.rpow_one]
  have hcast : ((h - 1 : ℕ) : ℝ) = h - 1 := by rw [Nat.cast_sub (by omega)]; simp
  -- `b · b^{-1/h} = γ^{h-1}` and `b · b^{-(h-1)/h} = γ`
  have hb1 : (b : ℝ) * (b : ℝ) ^ (-(1 : ℝ) / h) = γ ^ (h - 1) := by
    rw [← rpow_div_eq_pow_rpow hb0 h, hcast]
    conv_lhs => arg 1; rw [← Real.rpow_one (b : ℝ)]
    rw [← Real.rpow_add hb0]
    congr 1; field_simp; ring
  have hb2 : (b : ℝ) * (b : ℝ) ^ (-((h - 1 : ℕ) : ℝ) / h) = γ := by
    rw [hcast]
    conv_lhs => arg 1; rw [← Real.rpow_one (b : ℝ)]
    rw [← Real.rpow_add hb0]
    congr 1; field_simp; ring
  have ha2 : (a : ℝ) ^ (((h - 1 : ℕ) : ℝ) / h) = α ^ (h - 1) := rpow_div_eq_pow_rpow ha0 h _
  -- `ζ^{h-1}` is the complex conjugate of `ζ`
  have hconjζ : ζ ^ (h - 1) = (starRingEnd ℂ) ζ := by
    have hn : ‖ζ‖ = 1 := hζ.norm'_eq_one hh0.ne'
    have h0 : ζ ≠ 0 := hζ.ne_zero hh0.ne'
    have h1 : ζ * (starRingEnd ℂ) ζ = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; norm_num
    have h2 : ζ * ζ ^ (h - 1) = 1 := by
      rw [← pow_succ', Nat.sub_add_cancel hh0, hζ.pow_eq_one]
    exact mul_left_cancel₀ h0 (h2.trans h1.symm)
  have hconj : ∀ P : ℝ[X], aeval (ζ ^ (h - 1)) P = (starRingEnd ℂ) (aeval ζ P) := by
    intro P
    rw [hconjζ]
    simpa using Polynomial.aeval_algHom_apply (Complex.conjAe.toAlgHom) ζ P
  have e1' : (α : ℂ) * aeval ζ F + (γ : ℂ) ^ (h - 1) * aeval ζ G = 0 := by
    rw [← e1, mul_assoc (b : ℂ), ← mul_assoc (b : ℂ)]
    congr 2
    rw [← Complex.ofReal_pow, ← hb1]; push_cast; ring
  have e2' : (α : ℂ) ^ (h - 1) * aeval ζ F + (γ : ℂ) * aeval ζ G = 0 := by
    have := congrArg (starRingEnd ℂ) e2
    rw [map_add, map_mul, map_mul, map_mul, hconj, hconj, Complex.conj_conj, Complex.conj_conj,
      Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_natCast, map_zero, ha2] at this
    rw [← this, ← hb2]; push_cast; ring
  refine two_type_core hh hα hγ ?_ e1' e2'
  intro h1
  have : (α * γ) ^ h = 1 := by rw [h1, one_pow]
  rw [mul_pow, hαh, hγh] at this
  have : (2 : ℝ) * 2 ≤ a * b := by
    apply mul_le_mul <;> first | exact_mod_cast ha | exact_mod_cast hb | positivity
  linarith

end ThreeIM
