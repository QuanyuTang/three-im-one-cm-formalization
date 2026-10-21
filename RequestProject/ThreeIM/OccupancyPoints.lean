module

public import RequestProject.ThreeIM.Rotation

/-!
# Occupancy data from point configurations (Lemmas 9.10 and 9.23)

Finite common points of type `x = n/m` (with `min(m, n) = 1`) lie at the locations
`r_x ζ_N^j`, `0 ≤ j < N`, where `r_x = x^{1/N} > 0`.  Given three disjoint finite sets of such
points (the finite common fibers in `ℂ*`), with equal weighted moments and the multiplicity
bounds of Lemma 9.10, we build the occupancy data of Lemma 9.10 for both comparisons and deduce
from Lemma 9.23 that each set is invariant under `t ↦ ζ_N² t`.
-/

@[expose] public section

open Polynomial

namespace ThreeIM

/-- `r_x = x^{1/N}`, as a complex number. -/
noncomputable def typeRad (N : ℕ) (x : ℚ) : ℂ := (((x : ℝ) ^ ((1 : ℝ) / N) : ℝ) : ℂ)

/-- The location `r_x ζ_N^j`. -/
noncomputable def typeLoc (N : ℕ) (x : ℚ) (j : ℕ) : ℂ := typeRad N x * zetaC N ^ j

variable {N : ℕ}

lemma typeRad_pow (hN : 0 < N) {x : ℚ} (hx : 0 < x) : typeRad N x ^ N = (x : ℂ) := by
  have hx' : (0 : ℝ) ≤ x := by exact_mod_cast hx.le
  unfold typeRad
  rw [← Complex.ofReal_pow, ← Real.rpow_natCast, ← Real.rpow_mul hx']
  have : (1 : ℝ) / N * N = 1 := by field_simp
  rw [this, Real.rpow_one]; push_cast; rfl

lemma typeRad_ne_zero {x : ℚ} (hx : 0 < x) : typeRad N x ≠ 0 := by
  unfold typeRad
  rw [Complex.ofReal_ne_zero]
  exact (Real.rpow_pos_of_pos (by exact_mod_cast hx) _).ne'

lemma typeLoc_pow (hN : 0 < N) {x : ℚ} (hx : 0 < x) (j : ℕ) : typeLoc N x j ^ N = (x : ℂ) := by
  rw [typeLoc, mul_pow, typeRad_pow hN hx, ← pow_mul, mul_comm j, pow_mul,
    (zetaC_isPrimitiveRoot hN).pow_eq_one, one_pow, mul_one]

lemma typeLoc_ne_zero {x : ℚ} (hx : 0 < x) (j : ℕ) : typeLoc N x j ≠ 0 := by
  have hz : zetaC N ≠ 0 := Complex.exp_ne_zero _
  exact mul_ne_zero (typeRad_ne_zero hx) (pow_ne_zero _ hz)

lemma typeLoc_inj (hN : 0 < N) {x x' : ℚ} (hx : 0 < x) (hx' : 0 < x') {j j' : ℕ} (hj : j < N)
    (hj' : j' < N) (h : typeLoc N x j = typeLoc N x' j') : x = x' ∧ j = j' := by
  have hxx : x = x' := by
    have := congrArg (· ^ N) h
    simp only [typeLoc_pow hN hx, typeLoc_pow hN hx'] at this
    exact_mod_cast this
  subst hxx
  refine ⟨rfl, (zetaC_isPrimitiveRoot hN).pow_inj hj hj' ?_⟩
  exact mul_left_cancel₀ (typeRad_ne_zero hx) h

lemma exists_typeLoc (hN : 0 < N) {t : ℂ} {x : ℚ} (hx : 0 < x) (htx : t ^ N = (x : ℂ)) :
    ∃ j < N, t = typeLoc N x j := by
  haveI : NeZero N := ⟨hN.ne'⟩
  have hr := typeRad_ne_zero (N := N) hx
  have h1 : (t / typeRad N x) ^ N = 1 := by
    rw [div_pow, htx, typeRad_pow hN hx, div_self]
    exact_mod_cast hx.ne'
  obtain ⟨j, hj, e⟩ := (zetaC_isPrimitiveRoot hN).eq_pow_of_pow_eq_one h1
  refine ⟨j, hj, ?_⟩
  rw [typeLoc, e]; field_simp

lemma radPow_eq_typeRad_pow {x : ℚ} (hx : 0 < x) (ℓ : ℕ) :
    radPow x ℓ N = typeRad N x ^ ℓ := by
  have hx' : (0 : ℝ) ≤ x := by exact_mod_cast hx.le
  unfold radPow typeRad
  rw [← Complex.ofReal_pow, ← Real.rpow_mul_natCast hx']
  congr 2; ring

lemma l1norm_occupancyPoly (hN : 0 < N) (iv i0 : ℕ → ℤ) :
    l1norm (occupancyPoly N iv i0) = ∑ j ∈ Finset.range N, (|iv j - i0 j| : ℝ) := by
  unfold l1norm
  have hsub : (occupancyPoly N iv i0).support ⊆ Finset.range N := by
    intro j hj
    rw [Finset.mem_range]
    exact lt_of_le_of_lt (le_natDegree_of_mem_supp j hj) (natDegree_occupancyPoly_lt hN iv i0)
  rw [Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [coeff_occupancyPoly _ _ (Finset.mem_range.1 hj)]; push_cast; rfl
  · intro j _ hj
    rw [notMem_support_iff.1 hj]; simp

/-- Type data: for `min(m, n) = 1`, the type `x = n/m` is a positive rational of the form `k`
or `1/k`, with `den x = m` and `num x · den x = max(m, n)`. -/
lemma type_facts {m n : ℕ} (h : min m n = 1) :
    0 < ((n : ℚ) / m) ∧ (((n : ℚ) / m).num = 1 ∨ ((n : ℚ) / m).den = 1) ∧
      ((n : ℚ) / m).den = m ∧ ((n : ℚ) / m).num.natAbs * ((n : ℚ) / m).den = max m n := by
  rcases Nat.le_total m n with hmn | hmn
  · have hm : m = 1 := by omega
    subst hm
    have hn : 1 ≤ n := hmn
    simp only [Nat.cast_one, div_one, Rat.den_natCast, Rat.num_natCast]
    refine ⟨by exact_mod_cast hn, Or.inr trivial, trivial, ?_⟩
    simp [max_eq_right hn]
  · have hn : n = 1 := by omega
    subst hn
    have hm : 1 ≤ m := hmn
    have hm0 : m ≠ 0 := by omega
    simp only [Nat.cast_one, one_div, Rat.inv_natCast_den, Rat.inv_natCast_num, if_neg hm0]
    refine ⟨by positivity, Or.inl ?_, trivial, ?_⟩
    · simp [Int.sign_natCast_of_ne_zero hm0]
    · simp [Int.sign_natCast_of_ne_zero hm0, max_eq_left hm]

/-! ### Indicators and the type of a point -/

open Classical in
/-- The indicator of the location `r_x ζ_N^j` in a finite set `A` (zero for `x ≤ 0`). -/
noncomputable def pointInd (N : ℕ) (A : Finset ℂ) (x : ℚ) (j : ℕ) : ℤ :=
  if 0 < x ∧ typeLoc N x j ∈ A then 1 else 0

/-- The type `n/m` of a point. -/
noncomputable def typeOf (m n : ℂ → ℕ) (t : ℂ) : ℚ := (n t : ℚ) / m t

/-- The standing hypotheses on a finite set of points: nonzero, with `t^N m = n` and
`min(m, n) = 1`. -/
def PointsOK (N : ℕ) (m n : ℂ → ℕ) (A : Finset ℂ) : Prop :=
  ∀ t ∈ A, t ≠ 0 ∧ t ^ N * (m t : ℂ) = n t ∧ min (m t) (n t) = 1

lemma PointsOK.pow_eq {m n : ℂ → ℕ} {A : Finset ℂ} (h : PointsOK N m n A) {t : ℂ} (ht : t ∈ A) :
    t ^ N = ((typeOf m n t : ℚ) : ℂ) := by
  obtain ⟨-, h1, h2⟩ := h t ht
  have hm : (m t : ℂ) ≠ 0 := by
    have : m t ≠ 0 := by intro h0; rw [h0] at h2; simp at h2
    exact_mod_cast this
  unfold typeOf; push_cast
  rw [eq_div_iff hm, h1]

lemma PointsOK.typeOf_pos {m n : ℂ → ℕ} {A : Finset ℂ} (h : PointsOK N m n A) {t : ℂ}
    (ht : t ∈ A) : 0 < typeOf m n t := (type_facts (h t ht).2.2).1

lemma PointsOK.typeOf_loc (hN : 0 < N) {m n : ℂ → ℕ} {A : Finset ℂ} (h : PointsOK N m n A)
    {x : ℚ} (hx : 0 < x) {j : ℕ} (hj : typeLoc N x j ∈ A) : typeOf m n (typeLoc N x j) = x := by
  have e1 := h.pow_eq hj
  rw [typeLoc_pow hN hx] at e1
  exact_mod_cast e1.symm

lemma PointsOK.union {m n : ℂ → ℕ} {A B : Finset ℂ} (hA : PointsOK N m n A)
    (hB : PointsOK N m n B) : PointsOK N m n (A ∪ B) := by
  classical
  intro t ht
  rcases Finset.mem_union.1 ht with h | h
  · exact hA t h
  · exact hB t h

/-- A sum over the points of `A`, regrouped by types and locations. -/
lemma sum_eq_sum_types (hN : 0 < N) {m n : ℂ → ℕ} {A : Finset ℂ} (hA : PointsOK N m n A)
    {S : Finset ℚ} (hS : ∀ t ∈ A, typeOf m n t ∈ S) (g : ℂ → ℂ) :
    ∑ t ∈ A, g t = ∑ x ∈ S, ∑ j ∈ Finset.range N,
      ((pointInd N A x j : ℤ) : ℂ) * g (typeLoc N x j) := by
  classical
  have e : ∀ x j, ((pointInd N A x j : ℤ) : ℂ) * g (typeLoc N x j) =
      if (0 < x ∧ typeLoc N x j ∈ A) then g (typeLoc N x j) else 0 := by
    intro x j; unfold pointInd; split_ifs <;> simp
  simp only [e]
  rw [← Finset.sum_product' (f := fun x j => if (0 < x ∧ typeLoc N x j ∈ A) then
    g (typeLoc N x j) else 0), ← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun p _ => typeLoc N p.1 p.2) ?_ ?_ ?_ ?_
  · intro p hp
    exact (Finset.mem_filter.1 hp).2.2
  · intro p hp q hq hpq
    obtain ⟨hp1, hp2, -⟩ := Finset.mem_filter.1 hp
    obtain ⟨hq1, hq2, -⟩ := Finset.mem_filter.1 hq
    obtain ⟨e1, e2⟩ := typeLoc_inj hN hp2 hq2 (Finset.mem_range.1 (Finset.mem_product.1 hp1).2)
      (Finset.mem_range.1 (Finset.mem_product.1 hq1).2) hpq
    exact Prod.ext e1 e2
  · intro t ht
    have hx := hA.typeOf_pos ht
    obtain ⟨j, hj, e⟩ := exists_typeLoc hN hx (hA.pow_eq ht)
    refine ⟨(typeOf m n t, j), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hS t ht,
      Finset.mem_range.2 hj⟩, hx, e ▸ ht⟩, e.symm⟩
  · intro p hp; rfl

/-- For a fixed type, the points of that type in `A`, weighted by `g ≥ 0`, are bounded by the
total weight of `A`. -/
lemma sum_locs_le (hN : 0 < N) (A : Finset ℂ) {x : ℚ} (hx : 0 < x) (g : ℂ → ℕ) :
    ∑ j ∈ Finset.range N, (if typeLoc N x j ∈ A then g (typeLoc N x j) else 0) ≤
      ∑ t ∈ A, g t := by
  classical
  rw [← Finset.sum_filter]
  have hinj : Set.InjOn (typeLoc N x) ((Finset.range N).filter fun j => typeLoc N x j ∈ A) := by
    intro j hj j' hj' h
    exact (typeLoc_inj hN hx hx (Finset.mem_range.1 (Finset.mem_filter.1 hj).1)
      (Finset.mem_range.1 (Finset.mem_filter.1 hj').1) h).2
  rw [← Finset.sum_image (f := g) hinj]
  refine Finset.sum_le_sum_of_subset ?_
  intro t ht
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 ht
  exact (Finset.mem_filter.1 hj).2

lemma pointInd_eq (A : Finset ℂ) (x : ℚ) (j : ℕ) :
    pointInd N A x j = 0 ∨ (pointInd N A x j = 1 ∧ 0 < x ∧ typeLoc N x j ∈ A) := by
  unfold pointInd; split_ifs with h
  · exact Or.inr ⟨rfl, h⟩
  · exact Or.inl rfl

lemma PointsOK.max_eq {m n : ℂ → ℕ} {A : Finset ℂ} (h : PointsOK N m n A) {t : ℂ} (ht : t ∈ A) :
    max (m t) (n t) = if 1 ≤ typeOf m n t then n t else m t := by
  have hmin := (h t ht).2.2
  unfold typeOf
  split_ifs with hx
  · rcases Nat.le_total (m t) (n t) with h1 | h1
    · exact max_eq_right h1
    · have hn : n t = 1 := by omega
      have hm : m t ≠ 0 := by omega
      rw [hn] at hx ⊢
      have hm' : (0 : ℚ) < m t := by exact_mod_cast Nat.pos_of_ne_zero hm
      rw [le_div_iff₀ hm', one_mul] at hx
      have : m t ≤ 1 := by exact_mod_cast hx
      omega
  · push_neg at hx
    rcases Nat.le_total (m t) (n t) with h1 | h1
    · have hm : m t = 1 := by omega
      rw [hm] at hx; simp at hx
      omega
    · exact max_eq_left h1

/-- **Lemma 9.10** for a point configuration: two disjoint finite sets of points (the compared
fibers), with equal weighted moments and the multiplicity bounds, give occupancy data whose
polynomials are the differences of the fiber indicators. -/
theorem occupancyData_of_points (hN : 0 < N) {m n : ℂ → ℕ} {A B : Finset ℂ}
    (hA : PointsOK N m n A) (hB : PointsOK N m n B) (hAB : Disjoint A B)
    (hmom : ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ < N → 2 * ℓ ≠ N →
      ∑ t ∈ A, (m t : ℂ) * t ^ ℓ = ∑ t ∈ B, (m t : ℂ) * t ^ ℓ)
    (hbm : ∑ t ∈ A, m t + ∑ t ∈ B, m t < 5 * N)
    (hbn : ∑ t ∈ A, n t + ∑ t ∈ B, n t < 5 * N) :
    ∃ D : OccupancyData N, ∀ x, D.F x = occupancyPoly N (pointInd N A x) (pointInd N B x) := by
  classical
  have hAB' := hA.union hB
  set S := (A ∪ B).image (typeOf m n) with hSdef
  have hSA : ∀ t ∈ A, typeOf m n t ∈ S := fun t ht =>
    Finset.mem_image.2 ⟨t, Finset.mem_union_left _ ht, rfl⟩
  have hSB : ∀ t ∈ B, typeOf m n t ∈ S := fun t ht =>
    Finset.mem_image.2 ⟨t, Finset.mem_union_right _ ht, rfl⟩
  -- the indicators
  have hnotboth : ∀ x j, ¬ (pointInd N A x j = 1 ∧ pointInd N B x j = 1) := by
    intro x j ⟨h1, h2⟩
    rcases pointInd_eq (N := N) A x j with h | ⟨-, -, hA'⟩
    · rw [h] at h1; exact absurd h1 (by decide)
    rcases pointInd_eq (N := N) B x j with h | ⟨-, -, hB'⟩
    · rw [h] at h2; exact absurd h2 (by decide)
    exact Finset.disjoint_left.1 hAB hA' hB'
  have habs : ∀ x j, (|pointInd N A x j - pointInd N B x j| : ℝ) =
      pointInd N A x j + pointInd N B x j := by
    intro x j
    have := hnotboth x j
    rcases pointInd_eq (N := N) A x j with h1 | ⟨h1, -⟩ <;>
      rcases pointInd_eq (N := N) B x j with h2 | ⟨h2, -⟩ <;> simp_all
  refine ⟨OccupancyData.mk S (fun x => occupancyPoly N (pointInd N A x) (pointInd N B x))
    hN ?_ ?_ ?_ ?_ ?_, fun x => rfl⟩
  · intro x hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hx
    have := type_facts (hAB' t ht).2.2
    exact ⟨this.1, this.2.1⟩
  · intro x hx
    by_contra hS
    apply hx
    have hz : ∀ (C : Finset ℂ), C ⊆ A ∪ B → ∀ j, pointInd N C x j = 0 := by
      intro C hC j
      rcases pointInd_eq (N := N) C x j with h | ⟨-, hx0, hm⟩
      · exact h
      · exact absurd (Finset.mem_image.2 ⟨_, hC hm, hAB'.typeOf_loc hN hx0 (hC hm)⟩) hS
    simp only [occupancyPoly, hz A Finset.subset_union_left, hz B Finset.subset_union_right,
      sub_self, map_zero, zero_mul, Finset.sum_const_zero]
  · rw [l1norm_occupancyPoly hN]
    calc ∑ j ∈ Finset.range N, (|pointInd N A 1 j - pointInd N B 1 j| : ℝ)
        ≤ ∑ j ∈ Finset.range N, (1 : ℝ) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [habs]
          have := hnotboth 1 j
          rcases pointInd_eq (N := N) A 1 j with h1 | ⟨h1, -⟩ <;>
            rcases pointInd_eq (N := N) B 1 j with h2 | ⟨h2, -⟩ <;> simp_all
      _ = N := by simp
  · intro x hx
    obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_image.1 hx
    have hx0 := hAB'.typeOf_pos ht₀
    set x := typeOf m n t₀ with hxdef
    set g : ℂ → ℕ := fun t => if 1 ≤ x then n t else m t with hgdef
    have hg : ∀ C ⊆ A ∪ B, ∀ j, typeLoc N x j ∈ C →
        g (typeLoc N x j) = x.num.natAbs * x.den := by
      intro C hC j hj
      have hm := hC hj
      have e := hAB'.typeOf_loc hN hx0 hm
      have e1 := hAB'.max_eq hm
      obtain ⟨-, -, -, hk2⟩ := type_facts (hAB' _ hm).2.2
      have hk2' : (typeOf m n (typeLoc N x j)).num.natAbs * (typeOf m n (typeLoc N x j)).den =
          max (m (typeLoc N x j)) (n (typeLoc N x j)) := hk2
      rw [e] at hk2' e1
      rw [hk2', e1]
    have hcount : ∀ C ⊆ A ∪ B, x.num.natAbs * x.den *
        (∑ j ∈ Finset.range N, if typeLoc N x j ∈ C then 1 else 0) ≤ ∑ t ∈ C, g t := by
      intro C hC
      rw [Finset.mul_sum]
      calc _ = ∑ j ∈ Finset.range N, (if typeLoc N x j ∈ C then g (typeLoc N x j) else 0) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            split_ifs with h
            · rw [hg C hC j h, mul_one]
            · rw [mul_zero]
        _ ≤ _ := sum_locs_le hN C hx0 g
    have hl1 : l1norm (occupancyPoly N (pointInd N A x) (pointInd N B x)) =
        (((∑ j ∈ Finset.range N, if typeLoc N x j ∈ A then 1 else 0) +
          (∑ j ∈ Finset.range N, if typeLoc N x j ∈ B then 1 else 0) : ℕ) : ℝ) := by
      rw [l1norm_occupancyPoly hN]
      push_cast
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [habs]
      unfold pointInd
      simp only [hx0, true_and]
      split_ifs <;> simp
    have hgsum : ∑ t ∈ A, g t + ∑ t ∈ B, g t < 5 * N := by
      simp only [hgdef]
      split_ifs
      · exact hbn
      · exact hbm
    show ((x.num.natAbs * x.den : ℕ) : ℝ) *
      l1norm (occupancyPoly N (pointInd N A x) (pointInd N B x)) < 5 * N
    rw [hl1, ← Nat.cast_mul]
    have := hcount A Finset.subset_union_left
    have := hcount B Finset.subset_union_right
    have hlt : x.num.natAbs * x.den * ((∑ j ∈ Finset.range N, if typeLoc N x j ∈ A then 1 else 0) +
        (∑ j ∈ Finset.range N, if typeLoc N x j ∈ B then 1 else 0)) < 5 * N := by
      rw [mul_add]; omega
    exact_mod_cast hlt
  · intro ℓ h1 h2 h3
    have haeval : ∀ x, aeval (zetaC N ^ ℓ) (occupancyPoly N (pointInd N A x) (pointInd N B x)) =
        ∑ j ∈ Finset.range N,
          ((pointInd N A x j - pointInd N B x j : ℤ) : ℂ) * (zetaC N ^ ℓ) ^ j := by
      intro x; simp [occupancyPoly, map_sum]
    have hterm : ∀ x ∈ S, (x.den : ℂ) * radPow x ℓ N *
        aeval (zetaC N ^ ℓ) (occupancyPoly N (pointInd N A x) (pointInd N B x)) =
        ∑ j ∈ Finset.range N, ((pointInd N A x j : ℤ) : ℂ) *
            ((m (typeLoc N x j) : ℂ) * typeLoc N x j ^ ℓ) -
          ∑ j ∈ Finset.range N, ((pointInd N B x j : ℤ) : ℂ) *
            ((m (typeLoc N x j) : ℂ) * typeLoc N x j ^ ℓ) := by
      intro x hx
      obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_image.1 hx
      have hx0 := hAB'.typeOf_pos ht₀
      set x := typeOf m n t₀
      rw [haeval, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hloc : ∀ C ⊆ A ∪ B, typeLoc N x j ∈ C → (m (typeLoc N x j) : ℂ) = x.den := by
        intro C hC h
        obtain ⟨-, -, hden, -⟩ := type_facts (hAB' _ (hC h)).2.2
        have hden' : (typeOf m n (typeLoc N x j)).den = m (typeLoc N x j) := hden
        rw [hAB'.typeOf_loc hN hx0 (hC h)] at hden'
        exact_mod_cast hden'.symm
      have hpow : typeLoc N x j ^ ℓ = radPow x ℓ N * (zetaC N ^ ℓ) ^ j := by
        rw [typeLoc, mul_pow, radPow_eq_typeRad_pow hx0, ← pow_mul, ← pow_mul, mul_comm j ℓ]
      rcases pointInd_eq (N := N) A x j with hA0 | ⟨hA1, -, hAm⟩ <;>
        rcases pointInd_eq (N := N) B x j with hB0 | ⟨hB1, -, hBm⟩
      · simp [hA0, hB0]
      · rw [hA0, hB1, hloc B Finset.subset_union_right hBm, hpow]; push_cast; ring
      · rw [hA1, hB0, hloc A Finset.subset_union_left hAm, hpow]; push_cast; ring
      · exact absurd ⟨hA1, hB1⟩ (hnotboth x j)
    have eA := sum_eq_sum_types hN hA hSA (fun t => (m t : ℂ) * t ^ ℓ)
    have eB := sum_eq_sum_types hN hB hSB (fun t => (m t : ℂ) * t ^ ℓ)
    show ∑ x ∈ S, (x.den : ℂ) * radPow x ℓ N *
      aeval (zetaC N ^ ℓ) (occupancyPoly N (pointInd N A x) (pointInd N B x)) = 0
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← eA, ← eB, hmom ℓ h1 h2 h3, sub_self]

/-! ### Rotation invariance (Lemma 9.23) -/

lemma periodic_extend {f : ℕ → ℤ} (hf : ∀ j, j + 2 < N → f (j + 2) = f j) :
    ∀ k j, j + 2 * k < N → f (j + 2 * k) = f j := by
  intro k
  induction k with
  | zero => intro j _; rfl
  | succ k ih =>
    intro j hj
    rw [show j + 2 * (k + 1) = (j + 2 * k) + 2 by ring, hf _ (by omega), ih j (by omega)]

lemma pointInd_eq_one {A : Finset ℂ} {x : ℚ} {j : ℕ} :
    pointInd N A x j = 1 ↔ 0 < x ∧ typeLoc N x j ∈ A := by
  unfold pointInd; split_ifs with h <;> simp [h]

lemma zeta_sq_mul_typeLoc (x : ℚ) (j : ℕ) :
    zetaC N ^ 2 * typeLoc N x j = typeLoc N x (j + 2) := by
  unfold typeLoc; rw [pow_add]; ring

lemma rot_mem (hN : 0 < N) (hev : Even N) {Z : Finset ℂ} {x : ℚ} (hx : 0 < x)
    (hper : ∀ j, j + 2 < N → pointInd N Z x (j + 2) = pointInd N Z x j) {j : ℕ} (hj : j < N)
    (hmem : typeLoc N x j ∈ Z) : zetaC N ^ 2 * typeLoc N x j ∈ Z := by
  have h1 : pointInd N Z x j = 1 := pointInd_eq_one.2 ⟨hx, hmem⟩
  rw [zeta_sq_mul_typeLoc]
  by_cases hj2 : j + 2 < N
  · rw [← hper j hj2] at h1
    exact (pointInd_eq_one.1 h1).2
  · obtain ⟨k, hk⟩ := hev
    obtain ⟨d, hd⟩ : ∃ d, j + 2 = d + N := ⟨j + 2 - N, by omega⟩
    have e : typeLoc N x (j + 2) = typeLoc N x d := by
      unfold typeLoc
      rw [hd, pow_add, (zetaC_isPrimitiveRoot hN).pow_eq_one, mul_one]
    have hext := periodic_extend hper (k - 1) d (by omega)
    rw [show d + 2 * (k - 1) = j by omega] at hext
    rw [hext] at h1
    rw [e]; exact (pointInd_eq_one.1 h1).2

/-- **Lemmas 9.10 + 9.23** for a point configuration.  Three pairwise disjoint finite sets of
points `Z0, Z1, Zc` (the finite common fibers in `ℂ*`), with equal weighted moments
`∑ m(t) t^ℓ` (`1 ≤ ℓ < N`, `2ℓ ≠ N`) and the multiplicity bounds of Lemma 9.10, are each
invariant under `t ↦ ζ_N² t`. -/
theorem rotation_of_points (hN : 0 < N) (hev : Even N) {m n : ℂ → ℕ} {Z0 Z1 Zc : Finset ℂ}
    (h0 : PointsOK N m n Z0) (h1 : PointsOK N m n Z1) (hc : PointsOK N m n Zc)
    (d10 : Disjoint Z1 Z0) (dc0 : Disjoint Zc Z0) (d1c : Disjoint Z1 Zc)
    (hmom1 : ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ < N → 2 * ℓ ≠ N →
      ∑ t ∈ Z1, (m t : ℂ) * t ^ ℓ = ∑ t ∈ Z0, (m t : ℂ) * t ^ ℓ)
    (hmomc : ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ < N → 2 * ℓ ≠ N →
      ∑ t ∈ Zc, (m t : ℂ) * t ^ ℓ = ∑ t ∈ Z0, (m t : ℂ) * t ^ ℓ)
    (hbm1 : ∑ t ∈ Z1, m t + ∑ t ∈ Z0, m t < 5 * N)
    (hbn1 : ∑ t ∈ Z1, n t + ∑ t ∈ Z0, n t < 5 * N)
    (hbmc : ∑ t ∈ Zc, m t + ∑ t ∈ Z0, m t < 5 * N)
    (hbnc : ∑ t ∈ Zc, n t + ∑ t ∈ Z0, n t < 5 * N) :
    (∀ t ∈ Z0, zetaC N ^ 2 * t ∈ Z0) ∧ (∀ t ∈ Z1, zetaC N ^ 2 * t ∈ Z1) ∧
      (∀ t ∈ Zc, zetaC N ^ 2 * t ∈ Zc) := by
  obtain ⟨D₁, hD₁⟩ := occupancyData_of_points hN h1 h0 d10 hmom1 hbm1 hbn1
  obtain ⟨Dc, hDc⟩ := occupancyData_of_points hN hc h0 dc0 hmomc hbmc hbnc
  have hnn : ∀ (Z : Finset ℂ) x j, 0 ≤ pointInd N Z x j := by
    intro Z x j; rcases pointInd_eq (N := N) Z x j with h | ⟨h, -⟩ <;> simp [h]
  have hdisj : ∀ x j, pointInd N Z0 x j + pointInd N Z1 x j + pointInd N Zc x j ≤ 1 := by
    intro x j
    rcases pointInd_eq (N := N) Z0 x j with a0 | ⟨a0, -, m0⟩ <;>
      rcases pointInd_eq (N := N) Z1 x j with a1 | ⟨a1, -, m1⟩ <;>
      rcases pointInd_eq (N := N) Zc x j with ac | ⟨ac, -, mc⟩ <;>
      simp only [a0, a1, ac] <;> first
        | decide
        | exact absurd m0 (Finset.disjoint_left.1 d10 m1)
        | exact absurd m0 (Finset.disjoint_left.1 dc0 mc)
        | exact absurd mc (Finset.disjoint_left.1 d1c m1)
  have hper := OccupancyData.indicator_periodic D₁ Dc hev (pointInd N Z0) (pointInd N Z1)
    (pointInd N Zc) (hnn Z0) (hnn Z1) (hnn Zc) hdisj hD₁ hDc
  have key : ∀ (Z : Finset ℂ), PointsOK N m n Z →
      (∀ x j, j + 2 < N → pointInd N Z x (j + 2) = pointInd N Z x j) →
      ∀ t ∈ Z, zetaC N ^ 2 * t ∈ Z := by
    intro Z hZ hZper t ht
    have hx := hZ.typeOf_pos ht
    obtain ⟨j, hj, e⟩ := exists_typeLoc hN hx (hZ.pow_eq ht)
    rw [e] at ht ⊢
    exact rot_mem hN hev hx (hZper _) hj ht
  exact ⟨key Z0 h0 fun x j hj => (hper x hj).1, key Z1 h1 fun x j hj => (hper x hj).2.1,
    key Zc hc fun x j hj => (hper x hj).2.2⟩

end ThreeIM
