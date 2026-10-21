module

public import RequestProject.ThreeIM.RationalDegreeFiveCount
public import RequestProject.ThreeIM.OccupancyPoints

/-!
# Rotation invariance of the finite fibers (Lemmas 9.10 and 9.23 for rational functions)

In the balanced endpoint configuration of Lemmas 9.5–9.6 (`U = γ t^{-ρ}`, `V = γ t^ρ`, both
finite endpoint values equal to `a j`), and in the presence of a defect, each finite common
fiber in `ℂ*`, together with its multiplicities, is invariant under `t ↦ e^{2πi/ρ} t`.
-/

@[expose] public section

open Filter Set Topology Polynomial

namespace ThreeIM

/-- The `v`-fiber of `R` in `ℂ*`, as a finite set. -/
noncomputable def fib (R : RatFunc ℂ) (v : ℂ) : Finset ℂ :=
  ((R.num - C v * R.denom).roots.toFinset).erase 0

lemma mem_fib {R : RatFunc ℂ} {v : ℂ} (hv : R.num - C v * R.denom ≠ 0) {t : ℂ} :
    t ∈ fib R v ↔ t ≠ 0 ∧ 0 < mult (ratEval R) (v : Sphere) t := by
  rw [fib, Finset.mem_erase, Multiset.mem_toFinset, mem_roots hv,
    mult_ratEval_eq_rootMultiplicity R hv, rootMultiplicity_pos hv]

/-- The total multiplicity of the `v`-points in `ℂ*`, plus the multiplicity at `0`, is at most
the degree of `R.num - v R.denom`. -/
lemma sum_fib_add_le (R : RatFunc ℂ) {v : ℂ} (hv : R.num - C v * R.denom ≠ 0) :
    ∑ t ∈ fib R v, mult (ratEval R) (v : Sphere) t +
      (R.num - C v * R.denom).rootMultiplicity 0 ≤ (R.num - C v * R.denom).natDegree := by
  classical
  unfold fib
  set P := R.num - C v * R.denom
  have htot : ∑ t ∈ P.roots.toFinset, P.rootMultiplicity t ≤ P.natDegree := by
    calc ∑ t ∈ P.roots.toFinset, P.rootMultiplicity t
        = ∑ t ∈ P.roots.toFinset, P.roots.count t := by simp [count_roots]
      _ = P.roots.card := Multiset.toFinset_sum_count_eq _
      _ ≤ P.natDegree := card_roots' P
  have e : ∀ t, mult (ratEval R) (v : Sphere) t = P.rootMultiplicity t :=
    mult_ratEval_eq_rootMultiplicity R hv
  simp only [e]
  by_cases h0 : (0 : ℂ) ∈ P.roots.toFinset
  · have := Finset.add_sum_erase P.roots.toFinset (fun t => P.rootMultiplicity t) h0
    omega
  · have : P.rootMultiplicity 0 = 0 := by
      rw [rootMultiplicity_eq_zero_iff]
      intro hr; exact absurd (Multiset.mem_toFinset.2 ((mem_roots hv).2 hr)) h0
    rw [this, add_zero, Finset.erase_eq_of_notMem h0]; exact htot

/-- If `R(1/s) - v` vanishes at `s = 0`, the degree of `R.num - v R.denom` drops. -/
lemma natDegree_num_sub_lt {R : RatFunc ℂ} {v : ℂ} (hv : R.num - C v * R.denom ≠ 0)
    (h : 0 < meromorphicOrderAt (fun s => ratEval R s⁻¹ - v) 0) :
    (R.num - C v * R.denom).natDegree < ratDeg R := by
  have heq : (fun s => ratEval R s⁻¹ - v) =ᶠ[𝓝[≠] 0]
      fun s => (R.num - C v * R.denom).eval s⁻¹ / R.denom.eval s⁻¹ := by
    filter_upwards [eventually_cofinite_inv (IsRatFun.eventually_ne R.denom_ne_zero)] with s hs
    rw [ratEval_eq, div_sub' hs]; congr 1; simp only [eval_sub, eval_mul, eval_C]; ring
  rw [meromorphicOrderAt_congr heq, order_quot_inv _ _ hv R.denom_ne_zero] at h
  have h' : (0 : ℤ) < (R.denom.natDegree : ℤ) - (R.num - C v * R.denom).natDegree := by
    exact_mod_cast h
  have : R.denom.natDegree ≤ ratDeg R := le_max_right _ _
  omega

lemma rootMultiplicity_zero_pos {R : RatFunc ℂ} {v : ℂ} (hv : R.num - C v * R.denom ≠ 0)
    (hd : R.denom.eval 0 ≠ 0) (hR : ratEval R 0 = v) :
    0 < (R.num - C v * R.denom).rootMultiplicity 0 := by
  rw [rootMultiplicity_pos hv, IsRoot, eval_sub, eval_mul, eval_C, ← hR, ratEval_eq,
    div_mul_cancel₀ _ hd, sub_self]

/-- The fiber moment `M_{v,ℓ}` (`ℓ ≥ 1`) as a sum over the `v`-fiber in `ℂ*`. -/
lemma fiberMoment_eq_sum_fib {R : RatFunc ℂ} {v : ℂ} (hv : R.num - C v * R.denom ≠ 0) {ℓ : ℕ}
    (hℓ : 1 ≤ ℓ) :
    fiberMoment R v ℓ = ∑ t ∈ fib R v, (mult (ratEval R) (v : Sphere) t : ℂ) * t ^ ℓ := by
  rw [fiberMoment_eq_sum_mult R hv, fib, Finset.sum_erase]
  simp [zero_pow (by omega : ℓ ≠ 0)]

/-- The multiplicity of `f` at `t` over its own value `f(t)`. -/
noncomputable def selfMult (f : ℂ → ℂ) (t : ℂ) : ℕ := mult f ((f t : ℂ) : Sphere) t

/-- **Lemmas 9.10 + 9.23** (rotation invariance of the finite fibers).  In the balanced
endpoint configuration (`U = γ t^{-ρ}`, `V = γ t^ρ`, both finite endpoint values `a j`), if a
defect exists in `ℂ*`, each finite fiber of `R` in `ℂ*` is invariant under
`t ↦ e^{2πi/ρ} t`. -/
theorem OppositeData.fib_rotation {a : Fin 3 → ℂ} {R S : RatFunc ℂ} {j : Fin 3} {ρ : ℕ}
    {γ : ℂ} (hpair : NormalizedPair {0}ᶜ (ratEval R) (ratEval S) a)
    (hd : OppositeData a R S j j ρ γ γ)
    (hdef : ∃ k, ∃ z ∈ ({0}ᶜ : Set ℂ), IsDefect (ratEval R) (ratEval S) (a k : Sphere) z) :
    ∀ i, ∀ t ∈ fib R (a i), zetaC ρ * t ∈ fib R (a i) := by
  have hRnc := ne_C_of_nonconst hpair.nonconst_f
  have hSnc := ne_C_of_nonconst hpair.nonconst_g
  have hρ := hd.rho_pos
  have hγ := hd.alpha_ne
  have hN : 0 < 2 * ρ := by omega
  have hev : Even (2 * ρ) := even_two_mul ρ
  have hdeg5 := hd.ratDeg_le_of_defect hpair hdef
  obtain ⟨hdegRS, -⟩ := degree_saturation hpair
  have hRv := fun v => num_sub_ne_zero (hRnc v)
  have hSv := fun v => num_sub_ne_zero (hSnc v)
  set mR := selfMult (ratEval R) with hmR
  set nS := selfMult (ratEval S) with hnS
  have hmem : ∀ i t, t ∈ fib R (a i) → t ≠ 0 ∧ 0 < mult (ratEval R) (a i : Sphere) t ∧
      0 < mult (ratEval S) (a i : Sphere) t ∧ mR t = mult (ratEval R) (a i : Sphere) t ∧
      nS t = mult (ratEval S) (a i : Sphere) t := by
    intro i t ht
    obtain ⟨ht0, hm⟩ := (mem_fib (hRv _)).1 ht
    have hm' := (hpair.im i t ht0).1 hm
    refine ⟨ht0, hm, hm', ?_, ?_⟩
    · simp only [hmR, selfMult, ratEval_eq_of_mult_pos hRnc hm]
    · simp only [hnS, selfMult, ratEval_eq_of_mult_pos hSnc hm']
  have hfibS : ∀ i, fib R (a i) = fib S (a i) := by
    intro i; ext t; rw [mem_fib (hRv _), mem_fib (hSv _)]
    constructor
    · rintro ⟨h0, h⟩; exact ⟨h0, (hpair.im i t h0).1 h⟩
    · rintro ⟨h0, h⟩; exact ⟨h0, (hpair.im i t h0).2 h⟩
  have hok : ∀ i, PointsOK (2 * ρ) mR nS (fib R (a i)) := by
    intro i t ht
    obtain ⟨ht0, hm, -, e1, e2⟩ := hmem i t ht
    rw [e1, e2]
    exact ⟨ht0, ratio_identity hγ hpair hd.aux_U hd.aux_V ht0 hm⟩
  have hdisj : ∀ i i', i ≠ i' → Disjoint (fib R (a i)) (fib R (a i')) := by
    intro i i' hii
    rw [Finset.disjoint_left]
    intro t h1 h2
    have e1 := ratEval_eq_of_mult_pos hRnc (hmem i t h1).2.1
    have e2 := ratEval_eq_of_mult_pos hRnc (hmem i' t h2).2.1
    exact hii (hpair.injective (e1.symm.trans e2))
  have hmom : ∀ i, i ≠ j → ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ < 2 * ρ → 2 * ℓ ≠ 2 * ρ →
      ∑ t ∈ fib R (a i), (mR t : ℂ) * t ^ ℓ = ∑ t ∈ fib R (a j), (mR t : ℂ) * t ^ ℓ := by
    intro i hij ℓ h1 h2 h3
    have hsum : ∀ i', ∑ t ∈ fib R (a i'), (mR t : ℂ) * t ^ ℓ = fiberMoment R (a i') ℓ := by
      intro i'
      rw [fiberMoment_eq_sum_fib (hRv _) h1]
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [(hmem i' t ht).2.2.2.1]
    rw [hsum, hsum]
    exact (hd.fiberMoments_full hpair hij).1 ℓ h2 (by omega)
  -- multiplicity bounds
  have hbR : ∀ i, ∑ t ∈ fib R (a i), mR t ≤ ratDeg R := by
    intro i
    have h1 := sum_fib_add_le R (hRv (a i))
    have h2 : _ ≤ ratDeg R := natDegree_num_sub_le R (a i)
    have e : ∑ t ∈ fib R (a i), mR t = ∑ t ∈ fib R (a i), mult (ratEval R) (a i : Sphere) t :=
      Finset.sum_congr rfl fun t ht => (hmem i t ht).2.2.2.1
    omega
  have hbR0 : ∑ t ∈ fib R (a j), mR t + 1 ≤ ratDeg R := by
    have h1 := sum_fib_add_le R (hRv (a j))
    have h2 : _ ≤ ratDeg R := natDegree_num_sub_le R (a j)
    have h3 := rootMultiplicity_zero_pos (hRv (a j)) hd.denom_zero hd.value_zero
    have e : ∑ t ∈ fib R (a j), mR t = ∑ t ∈ fib R (a j), mult (ratEval R) (a j : Sphere) t :=
      Finset.sum_congr rfl fun t ht => (hmem j t ht).2.2.2.1
    omega
  have hbS : ∀ i, ∑ t ∈ fib R (a i), nS t ≤ ratDeg R := by
    intro i
    have e : ∑ t ∈ fib R (a i), nS t = ∑ t ∈ fib S (a i), mult (ratEval S) (a i : Sphere) t := by
      rw [← hfibS i]; exact Finset.sum_congr rfl fun t ht => (hmem i t ht).2.2.2.2
    have h1 := sum_fib_add_le S (hSv (a i))
    have h2 : _ ≤ ratDeg S := natDegree_num_sub_le S (a i)
    omega
  have hbS0 : ∑ t ∈ fib R (a j), nS t + 1 ≤ ratDeg R := by
    have e : ∑ t ∈ fib R (a j), nS t = ∑ t ∈ fib S (a j), mult (ratEval S) (a j : Sphere) t := by
      rw [← hfibS j]; exact Finset.sum_congr rfl fun t ht => (hmem j t ht).2.2.2.2
    have h1 := sum_fib_add_le S (hSv (a j))
    obtain ⟨σ, τ, -, hτ, -, hτo, -⟩ := opposite_endpoint_coefficients hpair hρ hd.denom_zero
      hd.value_zero hd.order_zero hd.order_infty hd.tendsto_infty hd.aux_U hd.aux_V
    have h2 := natDegree_num_sub_lt (hSv (a j)) (by rw [hτo]; exact_mod_cast hτ)
    omega
  have hj1 : j + 1 ≠ j := by fin_cases j <;> decide
  have hj2 : j + 2 ≠ j := by fin_cases j <;> decide
  have h12 : j + 1 ≠ j + 2 := by fin_cases j <;> decide
  obtain ⟨r0, r1, rc⟩ := rotation_of_points hN hev (hok j) (hok (j + 1)) (hok (j + 2))
    (hdisj _ _ hj1) (hdisj _ _ hj2) (hdisj _ _ h12) (hmom _ hj1) (hmom _ hj2)
    (by have := hbR (j + 1); omega) (by have := hbS (j + 1); omega)
    (by have := hbR (j + 2); omega) (by have := hbS (j + 2); omega)
  have hz : zetaC (2 * ρ) ^ 2 = zetaC ρ := by
    have := zetaC_pow_div hN (dvd_mul_left ρ 2)
    rwa [Nat.mul_div_cancel _ hρ] at this
  intro i
  have hi : i = j ∨ i = j + 1 ∨ i = j + 2 := by fin_cases i <;> fin_cases j <;> decide
  rw [← hz]
  rcases hi with rfl | rfl | rfl
  · exact r0
  · exact r1
  · exact rc

/-- Two pairs `(m, n)`, `(m', n')` with `min = 1` and the same ratio `n/m = n'/m'` are equal. -/
lemma pair_eq_of_ratio {x : ℂ} {m n m' n' : ℕ} (h : x * m = n) (h' : x * m' = n')
    (hmin : min m n = 1) (hmin' : min m' n' = 1) : m = m' ∧ n = n' := by
  have hm : m ≠ 0 := by intro h0; rw [h0] at hmin; simp at hmin
  have hm' : m' ≠ 0 := by intro h0; rw [h0] at hmin'; simp at hmin'
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have hmC' : (m' : ℂ) ≠ 0 := by exact_mod_cast hm'
  have hq : ((n : ℚ) / m) = ((n' : ℚ) / m') := by
    have e : ((((n : ℚ) / m : ℚ)) : ℂ) = (((n' : ℚ) / m' : ℚ) : ℂ) := by
      push_cast
      rw [← h, ← h']; field_simp
    exact_mod_cast e
  have hmm : m = m' := by
    rw [← (type_facts hmin).2.2.1, ← (type_facts hmin').2.2.1, hq]
  subst hmm
  refine ⟨rfl, ?_⟩
  have : (n : ℂ) = n' := by rw [← h, ← h']
  exact_mod_cast this

lemma zetaC_ne_zero (n : ℕ) : zetaC n ≠ 0 := Complex.exp_ne_zero _

/-- An injective self-map of a finite set given by multiplication is onto. -/
lemma mem_of_mul_mem {Z : Finset ℂ} {ξ : ℂ} (hξ : ξ ≠ 0) (h : ∀ t ∈ Z, ξ * t ∈ Z) {t : ℂ}
    (ht : ξ * t ∈ Z) : t ∈ Z := by
  classical
  have hsub : Z.image (ξ * ·) ⊆ Z := by
    intro s hs; obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hs; exact h u hu
  have hinj : Set.InjOn (ξ * ·) (Z : Set ℂ) := fun u _ v _ e => mul_left_cancel₀ hξ e
  have heq : Z.image (ξ * ·) = Z :=
    Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_image_of_injOn hinj])
  rw [← heq] at ht
  obtain ⟨u, hu, e⟩ := Finset.mem_image.1 ht
  rw [mul_left_cancel₀ hξ e] at hu; exact hu

/-- **Lemma 9.23**, with multiplicities: in the balanced endpoint configuration with a defect,
the multiplicities of `R` and `S` over each `a i` are invariant under `t ↦ e^{2πi/ρ} t`. -/
theorem OppositeData.mult_rotation {a : Fin 3 → ℂ} {R S : RatFunc ℂ} {j : Fin 3} {ρ : ℕ}
    {γ : ℂ} (hpair : NormalizedPair {0}ᶜ (ratEval R) (ratEval S) a)
    (hd : OppositeData a R S j j ρ γ γ)
    (hdef : ∃ k, ∃ z ∈ ({0}ᶜ : Set ℂ), IsDefect (ratEval R) (ratEval S) (a k : Sphere) z)
    (i : Fin 3) (t : ℂ) :
    mult (ratEval R) (a i : Sphere) (zetaC ρ * t) = mult (ratEval R) (a i : Sphere) t ∧
      mult (ratEval S) (a i : Sphere) (zetaC ρ * t) = mult (ratEval S) (a i : Sphere) t := by
  have hRnc := ne_C_of_nonconst hpair.nonconst_f
  have hρ := hd.rho_pos
  have hξ := zetaC_ne_zero ρ
  have hRv := num_sub_ne_zero (hRnc (a i))
  have hrot := hd.fib_rotation hpair hdef i
  by_cases ht0 : t = 0
  · subst ht0; simp
  have hξt0 : zetaC ρ * t ≠ 0 := mul_ne_zero hξ ht0
  by_cases ht : t ∈ fib R (a i)
  · have hξt := hrot t ht
    obtain ⟨-, hm⟩ := (mem_fib hRv).1 ht
    obtain ⟨-, hm2⟩ := (mem_fib hRv).1 hξt
    obtain ⟨e1, n1⟩ := ratio_identity hd.alpha_ne hpair hd.aux_U hd.aux_V ht0 hm
    obtain ⟨e2, n2⟩ := ratio_identity hd.alpha_ne hpair hd.aux_U hd.aux_V hξt0 hm2
    have hpow : (zetaC ρ * t) ^ (2 * ρ) = t ^ (2 * ρ) := by
      rw [mul_pow, pow_mul', (zetaC_isPrimitiveRoot hρ).pow_eq_one, one_pow, one_mul]
    rw [hpow] at e2
    obtain ⟨a1, a2⟩ := pair_eq_of_ratio e2 e1 n2 n1
    exact ⟨a1, a2⟩
  · have hξt : zetaC ρ * t ∉ fib R (a i) := fun h => ht (mem_of_mul_mem hξ hrot h)
    have z1 : mult (ratEval R) (a i : Sphere) t = 0 := by
      by_contra h; exact ht ((mem_fib hRv).2 ⟨ht0, Nat.pos_of_ne_zero h⟩)
    have z2 : mult (ratEval R) (a i : Sphere) (zetaC ρ * t) = 0 := by
      by_contra h; exact hξt ((mem_fib hRv).2 ⟨hξt0, Nat.pos_of_ne_zero h⟩)
    have z3 : mult (ratEval S) (a i : Sphere) t = 0 := by
      by_contra h
      exact absurd ((hpair.im i t ht0).2 (Nat.pos_of_ne_zero h)) (by rw [z1]; exact lt_irrefl 0)
    have z4 : mult (ratEval S) (a i : Sphere) (zetaC ρ * t) = 0 := by
      by_contra h
      exact absurd ((hpair.im i _ hξt0).2 (Nat.pos_of_ne_zero h)) (by rw [z2]; exact lt_irrefl 0)
    exact ⟨z2.trans z1.symm, z4.trans z3.symm⟩

/-! ### Descent (Lemma 9.25) -/

/-- A polynomial with `P(0) ≠ 0` whose root multiplicities are invariant under `t ↦ ξ t` is
itself invariant: `P(ξ t) = P(t)`. -/
lemma comp_C_mul_X_eq_self {P : ℂ[X]} {ξ : ℂ} (hξ : ξ ≠ 0) (hP0 : P.eval 0 ≠ 0)
    (hmult : ∀ s, P.rootMultiplicity (ξ * s) = P.rootMultiplicity s) :
    P.comp (C ξ * X) = P := by
  classical
  have hroots : P.roots.map (fun r => ξ⁻¹ * r) = P.roots := by
    ext s
    have hinj : Function.Injective (fun r : ℂ => ξ⁻¹ * r) :=
      fun a b h => mul_left_cancel₀ (inv_ne_zero hξ) h
    have := Multiset.count_map_eq_count' _ P.roots hinj (ξ * s)
    simp only [inv_mul_cancel_left₀ hξ] at this
    rw [this, count_roots, count_roots, hmult]
  have hsplit := C_leadingCoeff_mul_prod_multiset_X_sub_C
    (IsAlgClosed.card_roots_eq_natDegree (p := P))
  have hfac : ∀ r : ℂ, (X - C r).comp (C ξ * X) = C ξ * (X - C (ξ⁻¹ * r)) := by
    intro r
    simp only [sub_comp, X_comp, C_comp]
    rw [mul_sub, ← C_mul, mul_inv_cancel_left₀ hξ]
  have hQ : P.comp (C ξ * X) = C (ξ ^ Multiset.card P.roots) * P := by
    conv_lhs => rw [← hsplit]
    rw [mul_comp, C_comp, multiset_prod_comp, Multiset.map_map]
    simp only [Function.comp_def, hfac]
    rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, ← C_pow]
    have e : (P.roots.map fun r => X - C (ξ⁻¹ * r)) =
        (P.roots.map (fun r => ξ⁻¹ * r)).map (fun a => X - C a) := by
      rw [Multiset.map_map]; rfl
    rw [e, hroots, mul_left_comm, hsplit]
  have hc : ξ ^ Multiset.card P.roots = 1 := by
    have := congrArg (eval 0) hQ
    simp only [eval_comp, eval_mul, eval_C, eval_X, mul_zero] at this
    exact (mul_eq_right₀ hP0).1 this.symm
  rw [hQ, hc, C_1, one_mul]

lemma comp_C_mul_X_sub (P Q : ℂ[X]) (c ξ : ℂ) :
    (P - C c * Q).comp (C ξ * X) = P.comp (C ξ * X) - C c * Q.comp (C ξ * X) := by
  simp [sub_comp, mul_comp]

/-- From the invariance of two fiber polynomials `num - a den`, `num - b den` (`a ≠ b`), the
invariance of `num` and `den`. -/
lemma num_denom_invariant {P Q : ℂ[X]} {a b ξ : ℂ} (hab : a ≠ b)
    (ha : (P - C a * Q).comp (C ξ * X) = P - C a * Q)
    (hb : (P - C b * Q).comp (C ξ * X) = P - C b * Q) :
    P.comp (C ξ * X) = P ∧ Q.comp (C ξ * X) = Q := by
  rw [comp_C_mul_X_sub] at ha hb
  have hQ : C (b - a) * Q.comp (C ξ * X) = C (b - a) * Q := by
    rw [C_sub]; linear_combination ha - hb
  have hc : C (b - a) ≠ 0 := by rw [Ne, C_eq_zero]; exact sub_ne_zero.2 hab.symm
  have hQ' := mul_left_cancel₀ hc hQ
  refine ⟨?_, hQ'⟩
  linear_combination ha + C a * hQ'

/-- **Lemma 9.25**, rotation step: in the balanced endpoint configuration with a defect, the
numerators and denominators of `R` and `S` are invariant under `t ↦ e^{2πi/ρ} t`. -/
theorem OppositeData.num_denom_rotation {a : Fin 3 → ℂ} {R S : RatFunc ℂ} {j : Fin 3} {ρ : ℕ}
    {γ : ℂ} (hpair : NormalizedPair {0}ᶜ (ratEval R) (ratEval S) a)
    (hd : OppositeData a R S j j ρ γ γ)
    (hdef : ∃ k, ∃ z ∈ ({0}ᶜ : Set ℂ), IsDefect (ratEval R) (ratEval S) (a k : Sphere) z) :
    R.num.comp (C (zetaC ρ) * X) = R.num ∧ R.denom.comp (C (zetaC ρ) * X) = R.denom ∧
      S.num.comp (C (zetaC ρ) * X) = S.num ∧ S.denom.comp (C (zetaC ρ) * X) = S.denom := by
  have hRnc := ne_C_of_nonconst hpair.nonconst_f
  have hSnc := ne_C_of_nonconst hpair.nonconst_g
  have hξ := zetaC_ne_zero ρ
  have ha := hpair.injective
  have hj1 : j + 1 ≠ j := by fin_cases j <;> decide
  have hj2 : j + 2 ≠ j := by fin_cases j <;> decide
  have h12 : j + 1 ≠ j + 2 := by fin_cases j <;> decide
  -- `R`
  have hR : ∀ i, i ≠ j → (R.num - C (a i) * R.denom).comp (C (zetaC ρ) * X) =
      R.num - C (a i) * R.denom := by
    intro i hij
    have hv := num_sub_ne_zero (hRnc (a i))
    refine comp_C_mul_X_eq_self hξ ?_ fun s => ?_
    · have h0 := hd.value_zero
      rw [ratEval_eq, div_eq_iff hd.denom_zero] at h0
      rw [eval_sub, eval_mul, eval_C, h0, ← sub_mul]
      exact mul_ne_zero (sub_ne_zero.2 fun h => hij (ha h).symm) hd.denom_zero
    · rw [← mult_ratEval_eq_rootMultiplicity R hv, ← mult_ratEval_eq_rootMultiplicity R hv]
      exact (hd.mult_rotation hpair hdef i s).1
  -- `S`
  have hS0 : S.denom.eval 0 = 0 := by
    refine (mult_top_ratEval_pos_iff hSnc 0).1 ?_
    rw [mult_top, hd.order_zero, ← WithTop.LinearOrderedAddCommGroup.coe_neg, WithTop.untop₀_coe]
    have := hd.rho_pos
    omega
  have hSn0 : S.num.eval 0 ≠ 0 := (num_or_denom_ne_zero S 0).resolve_right (not_not.2 hS0)
  have hS : ∀ i, (S.num - C (a i) * S.denom).comp (C (zetaC ρ) * X) =
      S.num - C (a i) * S.denom := by
    intro i
    have hv := num_sub_ne_zero (hSnc (a i))
    refine comp_C_mul_X_eq_self hξ ?_ fun s => ?_
    · rw [eval_sub, eval_mul, eval_C, hS0, mul_zero, sub_zero]; exact hSn0
    · rw [← mult_ratEval_eq_rootMultiplicity S hv, ← mult_ratEval_eq_rootMultiplicity S hv]
      exact (hd.mult_rotation hpair hdef i s).2
  obtain ⟨r1, r2⟩ := num_denom_invariant (fun h => h12 (ha h)) (hR _ hj1) (hR _ hj2)
  obtain ⟨s1, s2⟩ := num_denom_invariant (fun h => h12 (ha h)) (hS (j + 1)) (hS (j + 2))
  exact ⟨r1, r2, s1, s2⟩

end ThreeIM
