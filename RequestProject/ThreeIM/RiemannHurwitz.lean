module

public import RequestProject.ThreeIM.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# A Riemann–Hurwitz count for rational maps (used in Lemma 9.2)

For coprime polynomials `p, q` with `e = max (deg p) (deg q) ≥ 1` (a rational map `H = p/q` of
degree `e`) and four distinct target values `E ⊆ ℂ̂`, the set `Z` of finite points of `H⁻¹(E)`
has at least `2e + 1` elements.  If equality holds, then the value `H(∞)` lies in `E`, and the
Wronskian `p' q - p q'` has no zero outside `Z` (so `H` has no critical point in `ℂ` outside
`H⁻¹(E)`).

The proof is the polynomial form of the Riemann–Hurwitz bound: at a point of multiplicity `m`
over a value of `E`, the Wronskian vanishes to order at least `m - 1`, and its degree is at most
`2e - 1 - k`, where `k` is the deficiency of the fiber polynomial of `H(∞)`.
-/

@[expose] public section

open Polynomial

namespace ThreeIM

/-- The fiber polynomial of `p/q` over `b ∈ ℂ̂`: `p - b q` for finite `b` and `q` for `b = ∞`. -/
noncomputable def fiberPoly (p q : ℂ[X]) (b : Sphere) : ℂ[X] :=
  WithTop.recTopCoe q (fun c : ℂ => p - C c * q) b

@[simp] lemma fiberPoly_top (p q : ℂ[X]) : fiberPoly p q ⊤ = q := rfl

@[simp] lemma fiberPoly_coe (p q : ℂ[X]) (c : ℂ) : fiberPoly p q (c : Sphere) = p - C c * q := rfl

/-- The Wronskian `p' q - p q'`. -/
noncomputable def wron (p q : ℂ[X]) : ℂ[X] := derivative p * q - p * derivative q

/-- The value at `∞` of `p/q`, for `e = max (deg p) (deg q)`. -/
noncomputable def infVal (p q : ℂ[X]) : Sphere :=
  if q.natDegree < max p.natDegree q.natDegree then ⊤
  else ((p.coeff (max p.natDegree q.natDegree) / q.coeff (max p.natDegree q.natDegree) : ℂ) :
    Sphere)

variable {p q : ℂ[X]}

lemma natDegree_fiberPoly_le (p q : ℂ[X]) (b : Sphere) :
    (fiberPoly p q b).natDegree ≤ max p.natDegree q.natDegree := by
  induction b using WithTop.recTopCoe with
  | top => exact le_max_right _ _
  | coe c => exact (natDegree_sub_le _ _).trans (max_le_max le_rfl (natDegree_C_mul_le _ _))

lemma q_ne_zero_of_coprime (hcop : IsCoprime p q) (he : 0 < max p.natDegree q.natDegree) :
    q ≠ 0 := by
  rintro rfl
  have hu : IsUnit p := isCoprime_zero_right.1 hcop
  have : p.natDegree = 0 := natDegree_eq_zero_of_isUnit hu
  simp [this] at he

lemma fiberPoly_ne_zero (hcop : IsCoprime p q) (he : 0 < max p.natDegree q.natDegree)
    (b : Sphere) : fiberPoly p q b ≠ 0 := by
  induction b using WithTop.recTopCoe with
  | top => exact q_ne_zero_of_coprime hcop he
  | coe c =>
    intro h
    rw [fiberPoly_coe, sub_eq_zero] at h
    have hu : IsUnit q := by
      rw [h] at hcop
      exact hcop.isUnit_of_dvd' (dvd_mul_left q (C c)) dvd_rfl
    have h1 : q.natDegree = 0 := natDegree_eq_zero_of_isUnit hu
    have h2 : p.natDegree = 0 := by
      rw [h]; exact Nat.le_zero.1 ((natDegree_C_mul_le _ _).trans h1.le)
    simp [h1, h2] at he

lemma not_eval_eq_zero_and (hcop : IsCoprime p q) (x : ℂ) :
    ¬ (p.eval x = 0 ∧ q.eval x = 0) := by
  rintro ⟨hp, hq⟩
  obtain ⟨u, v, huv⟩ := hcop
  have := congrArg (eval x) huv
  simp [hp, hq] at this

lemma fiber_disjoint (hcop : IsCoprime p q) {b b' : Sphere} (hb : b ≠ b') (x : ℂ) :
    ¬ ((fiberPoly p q b).eval x = 0 ∧ (fiberPoly p q b').eval x = 0) := by
  rintro ⟨h1, h2⟩
  apply not_eval_eq_zero_and hcop x
  induction b using WithTop.recTopCoe with
  | top =>
    induction b' using WithTop.recTopCoe with
    | top => exact absurd rfl hb
    | coe c' =>
      simp only [fiberPoly_top] at h1
      simp only [fiberPoly_coe, eval_sub, eval_mul, eval_C, h1, mul_zero, sub_zero] at h2
      exact ⟨h2, h1⟩
  | coe c =>
    induction b' using WithTop.recTopCoe with
    | top =>
      simp only [fiberPoly_top] at h2
      simp only [fiberPoly_coe, eval_sub, eval_mul, eval_C, h2, mul_zero, sub_zero] at h1
      exact ⟨h1, h2⟩
    | coe c' =>
      simp only [fiberPoly_coe, eval_sub, eval_mul, eval_C] at h1 h2
      have hcc : c - c' ≠ 0 := sub_ne_zero.2 (fun h => hb (by rw [h]))
      have hq : q.eval x = 0 := by
        have : (c - c') * q.eval x = 0 := by linear_combination h2 - h1
        exact (mul_eq_zero.1 this).resolve_left hcc
      refine ⟨?_, hq⟩
      linear_combination h1 + c * hq

lemma natDegree_eq_zero_of_dvd_derivative {F : ℂ[X]} (h : F ∣ derivative F) :
    F.natDegree = 0 := by
  by_contra hne
  have hlt := natDegree_derivative_lt hne
  have hd : derivative F ≠ 0 := fun h0 => hne (natDegree_eq_zero_of_derivative_eq_zero h0)
  have := natDegree_le_of_dvd h hd
  omega

lemma wron_ne_zero (hcop : IsCoprime p q) (he : 0 < max p.natDegree q.natDegree) :
    wron p q ≠ 0 := by
  intro h
  rw [wron, sub_eq_zero] at h
  have hp : p ∣ derivative p := hcop.dvd_of_dvd_mul_right ⟨derivative q, h⟩
  have hq : q ∣ derivative q := hcop.symm.dvd_of_dvd_mul_right ⟨derivative p, by linear_combination -h⟩
  have h1 := natDegree_eq_zero_of_dvd_derivative hp
  have h2 := natDegree_eq_zero_of_dvd_derivative hq
  simp [h1, h2] at he

lemma dvd_wron_aux (F A : ℂ[X]) (x : ℂ) :
    (X - C x) ^ (F.rootMultiplicity x - 1) ∣ derivative F * A - F * derivative A := by
  apply dvd_sub
  · apply Dvd.dvd.mul_right
    exact (pow_dvd_pow _ (rootMultiplicity_sub_one_le_derivative_rootMultiplicity F x)).trans
      (pow_rootMultiplicity_dvd _ _)
  · apply Dvd.dvd.mul_right
    exact (pow_dvd_pow _ (Nat.sub_le _ 1)).trans (pow_rootMultiplicity_dvd _ _)

lemma rootMultiplicity_fiber_le (hcop : IsCoprime p q) (he : 0 < max p.natDegree q.natDegree)
    (b : Sphere) (x : ℂ) :
    (fiberPoly p q b).rootMultiplicity x ≤ (wron p q).rootMultiplicity x + 1 := by
  have hdvd : (X - C x) ^ ((fiberPoly p q b).rootMultiplicity x - 1) ∣ wron p q := by
    induction b using WithTop.recTopCoe with
    | top =>
      have : wron p q = -(derivative q * p - q * derivative p) := by unfold wron; ring
      rw [this, dvd_neg]
      exact dvd_wron_aux q p x
    | coe c =>
      have : wron p q = derivative (p - C c * q) * q - (p - C c * q) * derivative q := by
        unfold wron; simp only [derivative_sub, derivative_mul, derivative_C, zero_mul, zero_add]
        ring
      rw [this]
      exact dvd_wron_aux _ q x
  have := (le_rootMultiplicity_iff (wron_ne_zero hcop he)).2 hdvd
  omega

lemma natDegree_wron_le (A B : ℂ[X]) :
    (derivative A * B - A * derivative B).natDegree ≤ A.natDegree + B.natDegree - 1 := by
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · by_cases hA : A.natDegree = 0
    · rw [derivative_of_natDegree_zero hA]; simp
    · refine (natDegree_mul_le).trans ?_
      have := natDegree_derivative_le A
      omega
  · by_cases hB : B.natDegree = 0
    · rw [derivative_of_natDegree_zero hB]; simp
    · refine (natDegree_mul_le).trans ?_
      have := natDegree_derivative_le B
      omega

lemma defect_add_natDegree_wron_le (he : 0 < max p.natDegree q.natDegree) (b : Sphere) :
    max p.natDegree q.natDegree - (fiberPoly p q b).natDegree + (wron p q).natDegree ≤
      2 * max p.natDegree q.natDegree - 1 := by
  have hF := natDegree_fiberPoly_le p q b
  have hp := le_max_left p.natDegree q.natDegree
  have hq := le_max_right p.natDegree q.natDegree
  induction b using WithTop.recTopCoe with
  | top =>
    have := natDegree_wron_le p q
    simp only [fiberPoly_top] at hF ⊢
    unfold wron
    omega
  | coe c =>
    have : wron p q = derivative (p - C c * q) * q - (p - C c * q) * derivative q := by
      unfold wron; simp only [derivative_sub, derivative_mul, derivative_C, zero_mul, zero_add]
      ring
    have h2 := natDegree_wron_le (p - C c * q) q
    rw [← this] at h2
    simp only [fiberPoly_coe] at hF ⊢
    omega

lemma natDegree_fiberPoly_of_ne_infVal (hq : q ≠ 0) {b : Sphere} (hb : b ≠ infVal p q) :
    (fiberPoly p q b).natDegree = max p.natDegree q.natDegree := by
  by_cases hlt : q.natDegree < max p.natDegree q.natDegree
  · have hpe : p.natDegree = max p.natDegree q.natDegree := by
      rcases le_total p.natDegree q.natDegree with h | h
      · rw [max_eq_right h] at hlt; omega
      · rw [max_eq_left h]
    rw [infVal, if_pos hlt] at hb
    induction b using WithTop.recTopCoe with
    | top => exact absurd rfl hb
    | coe c =>
      rw [fiberPoly_coe, natDegree_sub_eq_left_of_natDegree_lt
        (lt_of_le_of_lt (natDegree_C_mul_le _ _) (by omega))]
      exact hpe
  · have hqe : q.natDegree = max p.natDegree q.natDegree := le_antisymm (le_max_right _ _)
      (not_lt.1 hlt)
    rw [infVal, if_neg hlt] at hb
    induction b using WithTop.recTopCoe with
    | top => exact hqe
    | coe c =>
      rw [fiberPoly_coe]
      apply le_antisymm (natDegree_fiberPoly_le p q c)
      apply le_natDegree_of_ne_zero
      rw [fiberPoly_coe, coeff_sub, coeff_C_mul]
      have hlc : q.coeff (max p.natDegree q.natDegree) ≠ 0 := by
        rw [← hqe]; exact leadingCoeff_ne_zero.2 hq
      intro h0
      apply hb
      rw [WithTop.coe_inj, eq_div_iff hlc]
      linear_combination -h0

lemma natDegree_fiberPoly_infVal_lt (hq : q ≠ 0) (he : 0 < max p.natDegree q.natDegree) :
    (fiberPoly p q (infVal p q)).natDegree < max p.natDegree q.natDegree := by
  by_cases hlt : q.natDegree < max p.natDegree q.natDegree
  · rw [infVal, if_pos hlt]; exact hlt
  · have hqe : q.natDegree = max p.natDegree q.natDegree := le_antisymm (le_max_right _ _)
      (not_lt.1 hlt)
    rw [infVal, if_neg hlt, fiberPoly_coe]
    set e := max p.natDegree q.natDegree
    set F := p - C (p.coeff e / q.coeff e) * q
    have hlc : q.coeff e ≠ 0 := by rw [← hqe]; exact leadingCoeff_ne_zero.2 hq
    have hle : F.natDegree ≤ e :=
      natDegree_fiberPoly_le p q ((p.coeff e / q.coeff e : ℂ) : Sphere)
    rcases hle.lt_or_eq with h | h
    · exact h
    · exfalso
      have hc : F.coeff e = 0 := by
        simp only [F, coeff_sub, coeff_C_mul]; field_simp; ring
      have hF : F = 0 := by
        rw [← leadingCoeff_eq_zero, leadingCoeff, h, hc]
      rw [hF, natDegree_zero] at h
      omega

/-- The finite points of `H⁻¹(E)`. -/
noncomputable def fiberSet (p q : ℂ[X]) (E : Finset Sphere) : Finset ℂ :=
  E.biUnion fun b => (fiberPoly p q b).roots.toFinset

lemma mem_fiberSet (hcop : IsCoprime p q) (he : 0 < max p.natDegree q.natDegree)
    {E : Finset Sphere} {x : ℂ} :
    x ∈ fiberSet p q E ↔ ∃ b ∈ E, (fiberPoly p q b).eval x = 0 := by
  simp [fiberSet, fiberPoly_ne_zero hcop he]

lemma sum_natDegree_fiberPoly_le (hcop : IsCoprime p q) (he : 0 < max p.natDegree q.natDegree)
    (E : Finset Sphere) :
    ∑ b ∈ E, (fiberPoly p q b).natDegree ≤
      (fiberSet p q E).card + ∑ x ∈ fiberSet p q E, (wron p q).rootMultiplicity x := by
  classical
  have hdisj : (E : Set Sphere).PairwiseDisjoint fun b => (fiberPoly p q b).roots.toFinset := by
    intro b _ b' _ hbb'
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Multiset.mem_toFinset, mem_roots (fiberPoly_ne_zero hcop he _), IsRoot.def] at hx hx'
    exact fiber_disjoint hcop hbb' x ⟨hx, hx'⟩
  have hdeg : ∀ b, (fiberPoly p q b).natDegree =
      ∑ x ∈ (fiberPoly p q b).roots.toFinset, (fiberPoly p q b).rootMultiplicity x := by
    intro b
    rw [← IsAlgClosed.card_roots_eq_natDegree, ← Multiset.toFinset_sum_count_eq]
    simp [count_roots]
  calc ∑ b ∈ E, (fiberPoly p q b).natDegree
      = ∑ b ∈ E, ∑ x ∈ (fiberPoly p q b).roots.toFinset,
          (fiberPoly p q b).rootMultiplicity x := Finset.sum_congr rfl fun b _ => hdeg b
    _ ≤ ∑ b ∈ E, ∑ x ∈ (fiberPoly p q b).roots.toFinset, ((wron p q).rootMultiplicity x + 1) :=
        Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun x _ =>
          rootMultiplicity_fiber_le hcop he b x
    _ = ∑ x ∈ fiberSet p q E, ((wron p q).rootMultiplicity x + 1) :=
        (Finset.sum_biUnion hdisj).symm
    _ = (fiberSet p q E).card + ∑ x ∈ fiberSet p q E, (wron p q).rootMultiplicity x := by
        rw [Finset.sum_add_distrib]; simp [add_comm]

lemma sum_rootMultiplicity_le' (N : ℂ[X]) (A : Finset ℂ) :
    ∑ t ∈ A, N.rootMultiplicity t ≤ N.natDegree := by
  classical
  calc ∑ t ∈ A, N.rootMultiplicity t = ∑ t ∈ A, N.roots.count t := by simp [count_roots]
    _ ≤ ∑ t ∈ A ∪ N.roots.toFinset, N.roots.count t :=
      Finset.sum_le_sum_of_subset Finset.subset_union_left
    _ = ∑ t ∈ N.roots.toFinset, N.roots.count t :=
      (Finset.sum_subset Finset.subset_union_right
        (fun x _ hx => Multiset.count_eq_zero.2 (by simpa using hx))).symm
    _ = Multiset.card N.roots := Multiset.toFinset_sum_count_eq _
    _ ≤ N.natDegree := card_roots' N

/-- **Riemann–Hurwitz count.**  For four distinct values, the finite part `Z` of `H⁻¹(E)` has at
least `2e + 1` points; in case of equality `H(∞) ∈ E` and the Wronskian has no zero outside
`Z`. -/
theorem rh_bound (hcop : IsCoprime p q) (he : 0 < max p.natDegree q.natDegree)
    {E : Finset Sphere} (hE : E.card = 4) :
    2 * max p.natDegree q.natDegree + 1 ≤ (fiberSet p q E).card ∧
      ((fiberSet p q E).card ≤ 2 * max p.natDegree q.natDegree + 1 →
        infVal p q ∈ E ∧ ∀ t ∉ fiberSet p q E, (wron p q).eval t ≠ 0) := by
  classical
  have hq : q ≠ 0 := by simpa using fiberPoly_ne_zero hcop he ⊤
  have h1 := sum_natDegree_fiberPoly_le hcop he E
  set e := max p.natDegree q.natDegree with he_def
  set Z := fiberSet p q E
  set W := wron p q
  set D := ∑ b ∈ E, (e - (fiberPoly p q b).natDegree) with hD
  have hsumW : ∑ x ∈ Z, W.rootMultiplicity x ≤ W.natDegree := sum_rootMultiplicity_le' _ _
  have hb0 : (fiberPoly p q (infVal p q)).natDegree < e := natDegree_fiberPoly_infVal_lt hq he
  have hdef0 : e - (fiberPoly p q (infVal p q)).natDegree + W.natDegree ≤ 2 * e - 1 :=
    defect_add_natDegree_wron_le he (infVal p q)
  have hdeg : ∑ b ∈ E, (fiberPoly p q b).natDegree + D = 4 * e := by
    rw [hD, ← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (fun b _ => Nat.add_sub_cancel' (natDegree_fiberPoly_le p q b))]
    simp [hE, he_def]
  have hDW : D + W.natDegree ≤ 2 * e - 1 ∧ (infVal p q ∉ E → D + W.natDegree ≤ 2 * e - 2) := by
    by_cases hin : infVal p q ∈ E
    · have : D = e - (fiberPoly p q (infVal p q)).natDegree := by
        rw [hD, Finset.sum_eq_single (infVal p q)]
        · intro b _ hb; simp [natDegree_fiberPoly_of_ne_infVal hq hb, he_def]
        · intro h; exact absurd hin h
      exact ⟨by rw [this]; exact hdef0, fun h => absurd hin h⟩
    · have : D = 0 := by
        rw [hD]; apply Finset.sum_eq_zero
        intro b hb
        simp [natDegree_fiberPoly_of_ne_infVal hq (fun h => hin (h ▸ hb)), he_def]
      refine ⟨?_, fun _ => ?_⟩ <;> rw [this] <;> omega
  refine ⟨by omega, fun hle => ⟨?_, fun t ht hWt => ?_⟩⟩
  · by_contra hin
    have := hDW.2 hin
    omega
  · have hpos : 0 < W.rootMultiplicity t := (rootMultiplicity_pos (wron_ne_zero hcop he)).2 hWt
    have hZ : t ∉ Z := ht
    have h2 := sum_rootMultiplicity_le' W (insert t Z)
    rw [Finset.sum_insert ht] at h2
    omega

end ThreeIM
