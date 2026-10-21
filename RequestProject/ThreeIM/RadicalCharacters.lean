module

public import RequestProject.ThreeIM.MathlibImports
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Separation of radical characters (Lemma 9.17)

For a primitive `h`-th root of unity `ζ` and `E_h = ℚ(ζ)`, radicals `α` with `α^h ∈ E_h` carry
characters `γ ↦ γ(α)/α` of the Galois group of the splitting field over `E_h`; two radicals have
the same character iff their quotient lies in `E_h`.  We prove:

* `radical_classes_separate`: in an `E_h`-linear relation among such radicals, the sum over each
  character class vanishes separately (via Dedekind's independence of characters);
* `radical_class_pow_iff`: replacing the radicals by their `s`-th powers with `gcd(s, h) = 1`
  preserves the partition into classes.
-/

@[expose] public section

open Polynomial IntermediateField

namespace ThreeIM

open Classical in
/-- Separation of Kummer characters.  Let `L/K` be a finite Galois extension in which every
`h`-th root of unity lies in `K`, and let `β_i ∈ L` be nonzero with `β_i^h ∈ K`.  In any
`K`-linear relation `∑ c_i β_i = 0`, the sum over each class of radicals whose quotient lies in
`K` vanishes separately. -/
theorem kummer_separation {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] {h : ℕ}
    (hμ : ∀ u : L, u ^ h = 1 → ∃ k : K, u = algebraMap K L k)
    {ι : Type*} [Fintype ι] (β c : ι → L) (hβ : ∀ i, β i ≠ 0)
    (hβh : ∀ i, ∃ k : K, β i ^ h = algebraMap K L k) (hc : ∀ i, ∃ k : K, c i = algebraMap K L k)
    (hrel : ∑ i, c i * β i = 0) (j : ι) :
    ∑ i with ∃ k : K, β i = algebraMap K L k * β j, c i * β i = 0 := by
  classical
  have hroot : ∀ σ : Gal(L/K), ∀ i, ∃ k : K, σ (β i) = algebraMap K L k * β i := by
    intro σ i
    obtain ⟨k0, hk0⟩ := hβh i
    obtain ⟨k, hk⟩ := hμ (σ (β i) / β i) (by
      rw [div_pow, ← map_pow, hk0, AlgEquiv.commutes, ← hk0, div_self (pow_ne_zero _ (hβ i))])
    refine ⟨k, ?_⟩
    rw [← hk, div_mul_cancel₀ _ (hβ i)]
  let χ : ι → (Gal(L/K) →* L) := fun i =>
    { toFun := fun σ => σ (β i) / β i
      map_one' := by simp [div_self (hβ i)]
      map_mul' := by
        intro σ τ
        obtain ⟨k, hk⟩ := hroot τ i
        simp only [AlgEquiv.mul_apply, hk, map_mul, AlgEquiv.commutes]
        field_simp [hβ i] }
  have hχ : ∀ σ i, χ i σ = σ (β i) / β i := fun _ _ => rfl
  have hχeq : ∀ i, χ i = χ j ↔ ∃ k : K, β i = algebraMap K L k * β j := by
    intro i
    constructor
    · intro he
      have hfix : β i / β j ∈ (⊥ : IntermediateField K L) := by
        rw [IsGalois.mem_bot_iff_fixed]
        intro σ
        have := congrArg (fun f : Gal(L/K) →* L => f σ) he
        simp only [hχ] at this
        rw [map_div₀]
        field_simp [hβ i, hβ j] at this ⊢
        linear_combination this
      obtain ⟨k, hk⟩ := IntermediateField.mem_bot.1 hfix
      exact ⟨k, by rw [hk, div_mul_cancel₀ _ (hβ j)]⟩
    · rintro ⟨k, hk⟩
      ext σ
      have hk0 : algebraMap K L k ≠ 0 := by
        intro h0; apply hβ i; rw [hk, h0, zero_mul]
      simp only [hχ, hk, map_mul, AlgEquiv.commutes]
      field_simp [hβ j, hk0]
  set T := Finset.univ.image χ
  let g : (Gal(L/K) →* L) → L := fun ψ => ∑ i with χ i = ψ, c i * β i
  have hsum : ∑ ψ ∈ T, g ψ • (ψ : Gal(L/K) → L) = 0 := by
    funext σ
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, g, Finset.sum_mul]
    rw [show ∑ x ∈ T, ∑ i with χ i = x, c i * β i * x σ =
        ∑ x ∈ T, ∑ i with χ i = x, c i * β i * χ i σ from
      Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i hi => by
        rw [(Finset.mem_filter.1 hi).2]]
    rw [Finset.sum_fiberwise_of_maps_to (g := χ)
      (fun i _ => Finset.mem_image_of_mem χ (Finset.mem_univ i))
      (f := fun i => c i * β i * χ i σ)]
    have : ∀ i, c i * β i * χ i σ = σ (c i * β i) := by
      intro i
      obtain ⟨k, hk⟩ := hc i
      rw [hχ, map_mul, hk, AlgEquiv.commutes]
      field_simp [hβ i]
    simp only [this, ← map_sum, hrel, map_zero]
  have := linearIndependent_iff'.1 (linearIndependent_monoidHom (Gal(L/K)) L) T g hsum (χ j)
    (Finset.mem_image_of_mem χ (Finset.mem_univ j))
  simp only [g] at this
  rw [← this]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext i
  simp [hχeq]

open Classical in
/-- **Lemma 9.17** (separation of radical characters), separation statement.  Let `ζ` be a
primitive `h`-th root of unity and `E_h = ℚ(ζ)`.  Let `α_i` (`i ∈ s`) be nonzero complex numbers
with `α_i^h ∈ E_h` (for instance positive radicals `k^{±1/h}`), and let `c_i ∈ E_h`.  If
`∑ c_i α_i = 0`, then for every `j ∈ s` the sum over the character class of `α_j` (the indices
`i` with `α_i / α_j ∈ E_h`) is zero. -/
theorem radical_classes_separate {h : ℕ} (hh : 0 < h) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ h)
    {ι : Type*} (s : Finset ι) (α c : ι → ℂ) (hα : ∀ i ∈ s, α i ≠ 0)
    (hαh : ∀ i ∈ s, α i ^ h ∈ ℚ⟮ζ⟯) (hc : ∀ i ∈ s, c i ∈ ℚ⟮ζ⟯)
    (hrel : ∑ i ∈ s, c i * α i = 0) {j : ι} (hj : j ∈ s) :
    ∑ i ∈ s with α i / α j ∈ ℚ⟮ζ⟯, c i * α i = 0 := by
  set K := ℚ⟮ζ⟯
  let a : ι → K := fun i => if hi : i ∈ s then ⟨α i ^ h, hαh i hi⟩ else 1
  let p : K[X] := ∏ i ∈ s, (X ^ h - C (a i))
  have hpm : p.Monic := monic_prod_of_monic _ _ fun i _ => monic_X_pow_sub_C _ hh.ne'
  let L := IntermediateField.adjoin K (p.rootSet ℂ)
  haveI : IsSplittingField K L p := adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  haveI : Normal K L := Normal.of_isSplittingField p
  haveI : FiniteDimensional K L := IsSplittingField.finiteDimensional L p
  haveI : IsGalois K L := IsGalois.mk
  have hαL : ∀ i ∈ s, α i ∈ L := by
    intro i hi
    apply subset_adjoin
    rw [mem_rootSet]
    refine ⟨hpm.ne_zero, ?_⟩
    simp only [p, map_prod]
    apply Finset.prod_eq_zero hi
    simp [a, hi]
  have hKL : ∀ x ∈ K, x ∈ L := fun x hx => by
    simpa using IntermediateField.algebraMap_mem L (⟨x, hx⟩ : K)
  have hcoe : ∀ k : K, ((algebraMap K L k : L) : ℂ) = (k : ℂ) := fun _ => rfl
  let β : s → L := fun i => ⟨α i, hαL i i.2⟩
  let c' : s → L := fun i => ⟨c i, hKL _ (hc i i.2)⟩
  have key := kummer_separation (K := K) (L := L) (h := h) ?_ β c'
    (fun i => by intro h0; apply hα i i.2; simpa [β] using congrArg Subtype.val h0)
    (fun i => ⟨⟨α i ^ h, hαh i i.2⟩, Subtype.ext (by simp [β, hcoe])⟩)
    (fun i => ⟨⟨c i, hc i i.2⟩, Subtype.ext (by simp [c', hcoe])⟩) ?_ ⟨j, hj⟩
  · have key' := congrArg (algebraMap L ℂ) key
    rw [map_sum, map_zero] at key'
    rw [Finset.sum_filter] at key' ⊢
    rw [← Finset.sum_coe_sort s]
    refine Eq.trans ?_ key'
    apply Finset.sum_congr rfl
    intro i _
    apply if_congr _ rfl rfl
    constructor
    · intro hmem
      refine ⟨⟨α i / α j, hmem⟩, Subtype.ext ?_⟩
      simp only [β, IntermediateField.coe_mul, hcoe]
      rw [div_mul_cancel₀ _ (hα j hj)]
    · rintro ⟨k, hk⟩
      have := congrArg Subtype.val hk
      simp only [β, IntermediateField.coe_mul, hcoe] at this
      rw [this, mul_div_cancel_right₀ _ (hα j hj)]
      exact k.2
  · intro u hu
    have hu' : (u : ℂ) ^ h = 1 := by simpa using congrArg Subtype.val hu
    haveI : NeZero h := ⟨hh.ne'⟩
    obtain ⟨m, -, hm⟩ := hζ.eq_pow_of_pow_eq_one hu'
    refine ⟨⟨ζ, mem_adjoin_simple_self ℚ ζ⟩ ^ m, Subtype.ext ?_⟩
    simp [hcoe, hm]
  · apply Subtype.ext
    simp only [IntermediateField.coe_sum, IntermediateField.coe_mul, IntermediateField.coe_zero,
      β, c']
    rw [Finset.sum_coe_sort s (fun i => c i * α i)]
    exact hrel

/-- **Lemma 9.17**, last assertion: for `gcd(s, h) = 1`, a nonzero `x` with `x^h ∈ K` lies in `K`
iff `x^s` does.  Applied to quotients of radicals, raising all radicals to the `s`-th power
preserves the partition into character classes. -/
theorem radical_class_pow_iff {h s : ℕ} (hcop : Nat.Coprime s h) {K : IntermediateField ℚ ℂ}
    {x : ℂ} (hx : x ≠ 0) (hxh : x ^ h ∈ K) : x ^ s ∈ K ↔ x ∈ K := by
  refine ⟨fun hxs => ?_, fun hxK => pow_mem hxK s⟩
  have hb : ((Nat.gcd s h : ℕ) : ℤ) = s * Nat.gcdA s h + h * Nat.gcdB s h := Nat.gcd_eq_gcd_ab s h
  rw [hcop, Nat.cast_one] at hb
  have : x = (x ^ s) ^ Nat.gcdA s h * (x ^ h) ^ Nat.gcdB s h := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hx, ← hb, zpow_one]
  rw [this]
  exact mul_mem (zpow_mem hxs _) (zpow_mem hxh _)

end ThreeIM
