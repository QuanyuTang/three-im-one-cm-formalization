module

public import RequestProject.ThreeIM.RationalEndpointPoles
public import RequestProject.ThreeIM.RiemannHurwitz

/-!
# Saturation of the degree bounds (Lemma 9.2)

Let `R, S ∈ ℂ(t)` be a rational sharing datum: a normalized pair on `ℂ*` (three finite values
`a 0, a 1, a 2` shared IM and `∞` shared CM on `ℂ*`).  Write `E = {a 0, a 1, a 2, ∞}` and let
`C ⊆ ℂ*` be the set of common points over `E`.

* The Riemann–Hurwitz count (`rh_bound`) gives `#C ≥ 2 max (deg R, deg S)`.
* The coincidence polynomial `X = num R · denom S - num S · denom R` vanishes on `C` and has
  degree at most `deg R + deg S`.

Hence equality holds throughout (**Lemma 9.2**): `deg R = deg S = d`, `#C = 2d`, the coincidence
multiplicity is one at every point of `C`, there are no coincidences elsewhere (including at the
endpoints `0` and `∞`), both endpoints lie over `E` for both maps, and neither map has a critical
point in `ℂ*` outside its inverse image of `E`.

As a consequence the hypotheses "conclusions of Lemma 9.2" carried by Lemmas 9.3–9.5 are
discharged, giving unconditional versions of these results.
-/

@[expose] public section

open Filter Set Topology Polynomial

namespace ThreeIM

variable {R S : RatFunc ℂ} {a : Fin 3 → ℂ}

/-- The four shared values `E = {a 0, a 1, a 2, ∞}`. -/
noncomputable def valueSet (a : Fin 3 → ℂ) : Finset Sphere :=
  {(a 0 : Sphere), (a 1 : Sphere), (a 2 : Sphere), ⊤}

lemma card_valueSet (ha : Function.Injective a) : (valueSet a).card = 4 := by
  have h01 : a 0 ≠ a 1 := ha.ne (by decide)
  have h02 : a 0 ≠ a 2 := ha.ne (by decide)
  have h12 : a 1 ≠ a 2 := ha.ne (by decide)
  simp [valueSet, Finset.card_insert_of_notMem, h01, h02, h12]

lemma mem_valueSet {b : Sphere} : b ∈ valueSet a ↔ (∃ j, b = (a j : Sphere)) ∨ b = ⊤ := by
  simp only [valueSet, Finset.mem_insert, Finset.mem_singleton, Fin.exists_fin_succ,
    Fin.exists_fin_zero]
  constructor
  · rintro (h | h | h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr h
  · rintro ((h | h | h | h) | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact h.elim
    · exact Or.inr (Or.inr (Or.inr h))

/-! ### Multiplicities of a rational function and its fiber polynomials -/

lemma mult_top_ratEval_pos_iff (hR : ∀ c : ℂ, R ≠ RatFunc.C c) (t : ℂ) :
    0 < mult (ratEval R) ⊤ t ↔ R.denom.eval t = 0 := by
  have hfun : ratEval R = fun w => R.num.eval w / R.denom.eval w := funext (ratEval_eq R)
  constructor
  · intro h
    by_contra hd
    have hn : R.num ≠ 0 := by simpa using num_sub_ne_zero (hR 0)
    rw [mult_top, hfun, order_polyQuot_of_denom_ne_zero hn hd,
      ← WithTop.LinearOrderedAddCommGroup.coe_neg, WithTop.untop₀_coe] at h
    omega
  · intro hd
    have hn : R.num.eval t ≠ 0 := (num_or_denom_ne_zero R t).resolve_right (not_not.2 hd)
    rw [mult_top, hfun, order_polyQuot R.denom_ne_zero hn,
      ← WithTop.LinearOrderedAddCommGroup.coe_neg, neg_neg, WithTop.untop₀_coe]
    simpa using (rootMultiplicity_pos R.denom_ne_zero).2 hd

lemma mult_ratEval_pos_iff (hR : ∀ c : ℂ, R ≠ RatFunc.C c) (b : Sphere) (t : ℂ) :
    0 < mult (ratEval R) b t ↔ (fiberPoly R.num R.denom b).eval t = 0 := by
  induction b using WithTop.recTopCoe with
  | top => exact mult_top_ratEval_pos_iff hR t
  | coe c =>
    rw [mult_ratEval_eq_rootMultiplicity R (num_sub_ne_zero (hR c)), fiberPoly_coe,
      rootMultiplicity_pos (num_sub_ne_zero (hR c))]
    rfl

/-- The finite points of `R⁻¹(E)`. -/
noncomputable abbrev ratFiberSet (R : RatFunc ℂ) (a : Fin 3 → ℂ) : Finset ℂ :=
  fiberSet R.num R.denom (valueSet a)

lemma mem_ratFiberSet (hR : ∀ c : ℂ, R ≠ RatFunc.C c) {t : ℂ} :
    t ∈ ratFiberSet R a ↔ (∃ j, 0 < mult (ratEval R) (a j : Sphere) t) ∨
      0 < mult (ratEval R) ⊤ t := by
  rw [mem_fiberSet (RatFunc.isCoprime_num_denom R) (max_natDegree_pos hR)]
  constructor
  · rintro ⟨b, hb, h0⟩
    rw [← mult_ratEval_pos_iff hR] at h0
    rcases mem_valueSet.1 hb with ⟨j, rfl⟩ | rfl
    · exact Or.inl ⟨j, h0⟩
    · exact Or.inr h0
  · rintro (⟨j, h⟩ | h)
    · exact ⟨_, mem_valueSet.2 (Or.inl ⟨j, rfl⟩), (mult_ratEval_pos_iff hR _ t).1 h⟩
    · exact ⟨⊤, mem_valueSet.2 (Or.inr rfl), (mult_ratEval_pos_iff hR _ t).1 h⟩

/-- For a normalized pair on `ℂ*`, the two maps have the same points over `E` in `ℂ*`. -/
lemma mem_ratFiberSet_iff (hpair : NormalizedPair {0}ᶜ (ratEval R) (ratEval S) a) {t : ℂ}
    (ht : t ≠ 0) : t ∈ ratFiberSet R a ↔ t ∈ ratFiberSet S a := by
  have ht' : t ∈ ({0}ᶜ : Set ℂ) := ht
  rw [mem_ratFiberSet (ne_C_of_nonconst hpair.nonconst_f),
    mem_ratFiberSet (ne_C_of_nonconst hpair.nonconst_g), hpair.cm_top t ht']
  exact or_congr (exists_congr fun j => hpair.im j t ht') Iff.rfl

/-! ### The coincidence polynomial -/

/-- The coincidence polynomial `num R · denom S - num S · denom R`. -/
noncomputable def coincPoly (R S : RatFunc ℂ) : ℂ[X] := R.num * S.denom - S.num * R.denom

lemma coincPoly_ne_zero (hpair : NormalizedPair {0}ᶜ (ratEval R) (ratEval S) a) :
    coincPoly R S ≠ 0 := by
  intro h
  have hRS : R = S := by
    rw [coincPoly, sub_eq_zero] at h
    rw [← RatFunc.num_div_denom R, ← RatFunc.num_div_denom S,
      div_eq_div_iff (RatFunc.algebraMap_ne_zero R.denom_ne_zero)
        (RatFunc.algebraMap_ne_zero S.denom_ne_zero), ← map_mul, ← map_mul, h]
  apply hpair.distinct 1 (by simp)
  subst hRS
  simp only [sub_self]
  rw [meromorphicOrderAt_const]
  simp

lemma natDegree_coincPoly_le (R S : RatFunc ℂ) :
    (coincPoly R S).natDegree ≤ ratDeg R + ratDeg S := by
  unfold coincPoly ratDeg
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · refine natDegree_mul_le.trans ?_
    omega
  · refine natDegree_mul_le.trans ?_
    omega

lemma coincPoly_eval_eq_zero (hpair : NormalizedPair {0}ᶜ (ratEval R) (ratEval S) a) {t : ℂ}
    (ht : t ≠ 0) (hmem : t ∈ ratFiberSet R a) : (coincPoly R S).eval t = 0 := by
  have ht' : t ∈ ({0}ᶜ : Set ℂ) := ht
  have hRnc := ne_C_of_nonconst hpair.nonconst_f
  have hSnc := ne_C_of_nonconst hpair.nonconst_g
  rcases (mem_ratFiberSet hRnc).1 hmem with ⟨j, hj⟩ | hp
  · have hj' := (hpair.im j t ht').1 hj
    rw [mult_ratEval_pos_iff hRnc, fiberPoly_coe] at hj
    rw [mult_ratEval_pos_iff hSnc, fiberPoly_coe] at hj'
    simp only [eval_sub, eval_mul, eval_C] at hj hj'
    simp only [coincPoly, eval_sub, eval_mul]
    linear_combination S.denom.eval t * hj - R.denom.eval t * hj'
  · have hp' : 0 < mult (ratEval S) ⊤ t := by rw [← hpair.cm_top t ht']; exact hp
    rw [mult_top_ratEval_pos_iff hRnc] at hp
    rw [mult_top_ratEval_pos_iff hSnc] at hp'
    simp [coincPoly, hp, hp']

/-! ### The counting argument -/

lemma eq_one_of_sum_le_card {s : Finset ℂ} {f : ℂ → ℕ} (h1 : ∀ x ∈ s, 1 ≤ f x)
    (hs : ∑ x ∈ s, f x ≤ s.card) : ∀ x ∈ s, f x = 1 := by
  have hsplit : ∑ x ∈ s, f x = s.card + ∑ x ∈ s, (f x - 1) := by
    rw [Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x hx => by have := h1 x hx; omega
  have h0 : ∑ x ∈ s, (f x - 1) = 0 := by omega
  intro x hx
  have := (Finset.sum_eq_zero_iff.1 h0) x hx
  have := h1 x hx
  omega

lemma card_le_sum_of_one_le {s : Finset ℂ} {f : ℂ → ℕ} (h1 : ∀ x ∈ s, 1 ≤ f x) :
    s.card ≤ ∑ x ∈ s, f x := by
  rw [Finset.card_eq_sum_ones]; exact Finset.sum_le_sum h1

/-- **Lemma 9.2**, counting form. -/
theorem degree_saturation (hpair : NormalizedPair {0}ᶜ (ratEval R) (ratEval S) a) :
    ratDeg R = ratDeg S ∧
    (∀ t, t ≠ 0 → t ∈ ratFiberSet R a → (coincPoly R S).rootMultiplicity t = 1) ∧
    (∀ t, (t = 0 ∨ t ∉ ratFiberSet R a) → (coincPoly R S).eval t ≠ 0) ∧
    (coincPoly R S).natDegree = ratDeg R + ratDeg S ∧
    0 ∈ ratFiberSet R a ∧ 0 ∈ ratFiberSet S a ∧
    infVal R.num R.denom ∈ valueSet a ∧ infVal S.num S.denom ∈ valueSet a ∧
    (∀ t ∉ ratFiberSet R a, (wron R.num R.denom).eval t ≠ 0) ∧
    (∀ t ∉ ratFiberSet S a, (wron S.num S.denom).eval t ≠ 0) := by
  classical
  have hRnc := ne_C_of_nonconst hpair.nonconst_f
  have hSnc := ne_C_of_nonconst hpair.nonconst_g
  have heR : 0 < max R.num.natDegree R.denom.natDegree := max_natDegree_pos hRnc
  have heS : 0 < max S.num.natDegree S.denom.natDegree := max_natDegree_pos hSnc
  have hE := card_valueSet hpair.injective
  obtain ⟨rhR1, rhR2⟩ := rh_bound (RatFunc.isCoprime_num_denom R) heR hE
  obtain ⟨rhS1, rhS2⟩ := rh_bound (RatFunc.isCoprime_num_denom S) heS hE
  have hdR : ratDeg R = max R.num.natDegree R.denom.natDegree := rfl
  have hdS : ratDeg S = max S.num.natDegree S.denom.natDegree := rfl
  set C := (ratFiberSet R a).erase 0 with hC
  have hCS : C = (ratFiberSet S a).erase 0 := by
    ext t
    simp only [hC, Finset.mem_erase]
    exact ⟨fun ⟨h0, h⟩ => ⟨h0, (mem_ratFiberSet_iff hpair h0).1 h⟩,
      fun ⟨h0, h⟩ => ⟨h0, (mem_ratFiberSet_iff hpair h0).2 h⟩⟩
  have hcR1 := Finset.pred_card_le_card_erase (s := ratFiberSet R a) (a := 0)
  have hcS1 := Finset.pred_card_le_card_erase (s := ratFiberSet S a) (a := 0)
  rw [← hC] at hcR1
  rw [← hCS] at hcS1
  set X := coincPoly R S
  have hX : X ≠ 0 := coincPoly_ne_zero hpair
  have hroot : ∀ t ∈ C, 1 ≤ X.rootMultiplicity t := by
    intro t ht
    rw [hC, Finset.mem_erase] at ht
    exact (rootMultiplicity_pos hX).2 (coincPoly_eval_eq_zero hpair ht.1 ht.2)
  have hsum : ∑ t ∈ C, X.rootMultiplicity t ≤ X.natDegree := sum_rootMultiplicity_le' _ _
  have hcard := card_le_sum_of_one_le hroot
  have hdeg : X.natDegree ≤ ratDeg R + ratDeg S := natDegree_coincPoly_le R S
  have rR : 2 * ratDeg R + 1 ≤ (ratFiberSet R a).card := rhR1
  have rS : 2 * ratDeg S + 1 ≤ (ratFiberSet S a).card := rhS1
  have hdeq : ratDeg R = ratDeg S := by omega
  have hCcard : C.card = ratDeg R + ratDeg S := by omega
  have hone : ∀ t ∈ C, X.rootMultiplicity t = 1 :=
    eq_one_of_sum_le_card hroot (by omega)
  have hRcard : (ratFiberSet R a).card ≤ 2 * ratDeg R + 1 := by omega
  have hScard : (ratFiberSet S a).card ≤ 2 * ratDeg S + 1 := by omega
  obtain ⟨hinfR, hWR⟩ := rhR2 hRcard
  obtain ⟨hinfS, hWS⟩ := rhS2 hScard
  refine ⟨hdeq, fun t ht0 ht => hone t (by rw [hC, Finset.mem_erase]; exact ⟨ht0, ht⟩),
    fun t ht => ?_, by omega, ?_, ?_, hinfR, hinfS, hWR, hWS⟩
  · intro hXt
    have htC : t ∉ C := by
      rw [hC, Finset.mem_erase]
      rintro ⟨h0, hm⟩
      rcases ht with h | h
      · exact h0 h
      · exact h hm
    have h2 := sum_rootMultiplicity_le' X (insert t C)
    rw [Finset.sum_insert htC] at h2
    have := (rootMultiplicity_pos hX).2 hXt
    omega
  · by_contra h0
    have : C = ratFiberSet R a := Finset.erase_eq_of_notMem h0
    rw [this] at hCcard; omega
  · by_contra h0
    have : C = ratFiberSet S a := hCS.trans (Finset.erase_eq_of_notMem h0)
    rw [this] at hCcard; omega

/-! ### Local forms of `R - S`, `1/R - 1/S` and `R'` -/

lemma sub_ratEval_eventually (R S : RatFunc ℂ) (t : ℂ) :
    (fun w => ratEval R w - ratEval S w) =ᶠ[𝓝[≠] t]
      fun w => (coincPoly R S).eval w / (R.denom * S.denom).eval w := by
  filter_upwards [polynomial_eventually_ne_zero R.denom_ne_zero t,
    polynomial_eventually_ne_zero S.denom_ne_zero t] with w h1 h2
  rw [ratEval_eq, ratEval_eq, coincPoly]
  simp only [eval_sub, eval_mul]
  field_simp

lemma inv_sub_ratEval_eventually {R S : RatFunc ℂ} (hR : R.num ≠ 0) (hS : S.num ≠ 0) (t : ℂ) :
    (fun w => (ratEval R w)⁻¹ - (ratEval S w)⁻¹) =ᶠ[𝓝[≠] t]
      fun w => -((coincPoly R S).eval w / (R.num * S.num).eval w) := by
  filter_upwards [polynomial_eventually_ne_zero hR t,
    polynomial_eventually_ne_zero hS t] with w h1 h2
  rw [ratEval_eq, ratEval_eq, inv_div, inv_div, coincPoly]
  simp only [eval_sub, eval_mul]
  field_simp
  ring

lemma deriv_ratEval_eventually (R : RatFunc ℂ) (t : ℂ) :
    deriv (ratEval R) =ᶠ[𝓝[≠] t]
      fun w => (wron R.num R.denom).eval w / (R.denom * R.denom).eval w := by
  filter_upwards [polynomial_eventually_ne_zero R.denom_ne_zero t] with w hw
  have hfun : ratEval R = fun w => R.num.eval w / R.denom.eval w := funext (ratEval_eq R)
  have hd := (R.num.hasDerivAt w).div (R.denom.hasDerivAt w) hw
  rw [hfun]
  refine hd.deriv.trans ?_
  simp only [wron, eval_sub, eval_mul]
  ring

lemma num_ne_zero_of_nonconst (hR : ∀ c : ℂ, R ≠ RatFunc.C c) : R.num ≠ 0 := by
  simpa using num_sub_ne_zero (hR 0)

lemma denom_eval_ne_zero_of_mult_pos (hR : ∀ c : ℂ, R ≠ RatFunc.C c) {c : ℂ} {t : ℂ}
    (h : 0 < mult (ratEval R) (c : Sphere) t) : R.denom.eval t ≠ 0 := by
  rw [mult_ratEval_pos_iff hR, fiberPoly_coe] at h
  intro hd
  simp only [eval_sub, eval_mul, eval_C, hd, mul_zero, sub_zero] at h
  exact (num_or_denom_ne_zero R t).elim (fun h' => h' h) (fun h' => h' hd)

/-- **Lemma 9.2**, local form: for a rational sharing datum, the conclusions
`CoincidenceSimpleAt` hold at every point of `ℂ*`: coincidence multiplicity one at every common
point over `{a 0, a 1, a 2, ∞}`, and outside these fibers no coincidence and no critical point. -/
theorem rational_coincidenceSimple (hpair : NormalizedPair {0}ᶜ (ratEval R) (ratEval S) a) :
    ∀ t : ℂ, t ≠ 0 → CoincidenceSimpleAt a (ratEval R) (ratEval S) t := by
  intro t ht
  have ht' : t ∈ ({0}ᶜ : Set ℂ) := ht
  have hRnc := ne_C_of_nonconst hpair.nonconst_f
  have hSnc := ne_C_of_nonconst hpair.nonconst_g
  obtain ⟨-, hone, hXne, -, -, -, -, -, hWR, hWS⟩ := degree_saturation hpair
  have hX := coincPoly_ne_zero hpair
  refine ⟨fun j hj => ?_, fun hp => ?_, fun hj hp => ?_⟩
  · have hj' := (hpair.im j t ht').1 hj
    have hdR := denom_eval_ne_zero_of_mult_pos hRnc hj
    have hdS := denom_eval_ne_zero_of_mult_pos hSnc hj'
    have hmem : t ∈ ratFiberSet R a := (mem_ratFiberSet hRnc).2 (Or.inl ⟨j, hj⟩)
    rw [meromorphicOrderAt_congr (sub_ratEval_eventually R S t),
      order_polyQuot_of_denom_ne_zero hX (by simp [hdR, hdS]), hone t ht hmem]
    rfl
  · have hp' : 0 < mult (ratEval S) ⊤ t := by rw [← hpair.cm_top t ht']; exact hp
    have hmem : t ∈ ratFiberSet R a := (mem_ratFiberSet hRnc).2 (Or.inr hp)
    have hdR := (mult_top_ratEval_pos_iff hRnc t).1 hp
    have hdS := (mult_top_ratEval_pos_iff hSnc t).1 hp'
    have hnR : R.num.eval t ≠ 0 := (num_or_denom_ne_zero R t).resolve_right (not_not.2 hdR)
    have hnS : S.num.eval t ≠ 0 := (num_or_denom_ne_zero S t).resolve_right (not_not.2 hdS)
    rw [meromorphicOrderAt_congr (inv_sub_ratEval_eventually (num_ne_zero_of_nonconst hRnc)
      (num_ne_zero_of_nonconst hSnc) t), order_neg_eq,
      order_polyQuot_of_denom_ne_zero hX (by simp [hnR, hnS]), hone t ht hmem]
    rfl
  · have hnot : t ∉ ratFiberSet R a := by
      rw [mem_ratFiberSet hRnc]
      rintro (⟨j, h⟩ | h)
      · rw [hj j] at h; exact lt_irrefl 0 h
      · rw [hp] at h; exact lt_irrefl 0 h
    have hnotS : t ∉ ratFiberSet S a := fun h => hnot ((mem_ratFiberSet_iff hpair ht).2 h)
    have hdR : R.denom.eval t ≠ 0 := fun h => by
      have := (mult_top_ratEval_pos_iff hRnc t).2 h; rw [hp] at this; exact lt_irrefl 0 this
    have hdS : S.denom.eval t ≠ 0 := fun h => by
      have := (mult_top_ratEval_pos_iff hSnc t).2 h
      rw [← hpair.cm_top t ht', hp] at this; exact lt_irrefl 0 this
    refine ⟨?_, ?_, ?_⟩
    · rw [meromorphicOrderAt_congr (sub_ratEval_eventually R S t),
        order_polyQuot_of_denom_ne_zero hX (by simp [hdR, hdS]),
        rootMultiplicity_eq_zero (hXne t (Or.inr hnot))]
      rfl
    · rw [meromorphicOrderAt_congr (deriv_ratEval_eventually R t),
        order_polyQuot_of_denom_ne_zero
          (wron_ne_zero (RatFunc.isCoprime_num_denom R) (max_natDegree_pos hRnc))
          (by simp [hdR]), rootMultiplicity_eq_zero (hWR t hnot)]
      rfl
    · rw [meromorphicOrderAt_congr (deriv_ratEval_eventually S t),
        order_polyQuot_of_denom_ne_zero
          (wron_ne_zero (RatFunc.isCoprime_num_denom S) (max_natDegree_pos hSnc))
          (by simp [hdS]), rootMultiplicity_eq_zero (hWS t hnotS)]
      rfl

/-- **Lemma 9.2**, equal degrees. -/
theorem rational_degree_eq (hpair : NormalizedPair {0}ᶜ (ratEval R) (ratEval S) a) :
    max R.num.natDegree R.denom.natDegree = max S.num.natDegree S.denom.natDegree :=
  (degree_saturation hpair).1

/-! ### The endpoints -/

lemma endpoint_of_mem (hR : ∀ c : ℂ, R ≠ RatFunc.C c) {t : ℂ} (h : t ∈ ratFiberSet R a) :
    R.denom.eval t = 0 ∨ ∃ j, ratEval R t = a j := by
  rcases (mem_ratFiberSet hR).1 h with ⟨j, hj⟩ | hp
  · have hd := denom_eval_ne_zero_of_mult_pos hR hj
    rw [mult_ratEval_pos_iff hR, fiberPoly_coe] at hj
    simp only [eval_sub, eval_mul, eval_C] at hj
    refine Or.inr ⟨j, ?_⟩
    rw [ratEval_eq, div_eq_iff hd]
    linear_combination hj
  · exact Or.inl ((mult_top_ratEval_pos_iff hR t).1 hp)

/-- **Lemma 9.2**, endpoint `0`: both maps lie over `{a 0, a 1, a 2, ∞}` at `0`, and there is no
coincidence at `0` (they are not both infinite there, and if both are finite their values
differ). -/
theorem rational_endpoint_zero (hpair : NormalizedPair {0}ᶜ (ratEval R) (ratEval S) a) :
    (R.denom.eval 0 = 0 ∨ ∃ j, ratEval R 0 = a j) ∧
    (S.denom.eval 0 = 0 ∨ ∃ j, ratEval S 0 = a j) ∧
    ¬ (R.denom.eval 0 = 0 ∧ S.denom.eval 0 = 0) ∧
    (R.denom.eval 0 ≠ 0 → S.denom.eval 0 ≠ 0 → ratEval R 0 ≠ ratEval S 0) := by
  obtain ⟨-, -, hXne, -, h0R, h0S, -⟩ := degree_saturation hpair
  have hX0 := hXne 0 (Or.inl rfl)
  refine ⟨endpoint_of_mem (ne_C_of_nonconst hpair.nonconst_f) h0R,
    endpoint_of_mem (ne_C_of_nonconst hpair.nonconst_g) h0S, ?_, ?_⟩
  · rintro ⟨h1, h2⟩
    apply hX0
    simp [coincPoly, h1, h2]
  · intro h1 h2 heq
    apply hX0
    rw [ratEval_eq, ratEval_eq, div_eq_div_iff h1 h2] at heq
    simp only [coincPoly, eval_sub, eval_mul]
    linear_combination heq

lemma eq_of_infVal_eq {p q p₂ q₂ : ℂ[X]} (hq : q ≠ 0) (hq₂ : q₂ ≠ 0) {e : ℕ}
    (he : max p.natDegree q.natDegree = e) (he₂ : max p₂.natDegree q₂.natDegree = e)
    (h : infVal p q = infVal p₂ q₂) : p.coeff e * q₂.coeff e - p₂.coeff e * q.coeff e = 0 := by
  unfold infVal at h
  rw [he, he₂] at h
  by_cases h1 : q.natDegree < e <;> by_cases h2 : q₂.natDegree < e
  · rw [coeff_eq_zero_of_natDegree_lt h1, coeff_eq_zero_of_natDegree_lt h2]; ring
  · rw [if_pos h1, if_neg h2] at h; exact absurd h WithTop.top_ne_coe
  · rw [if_neg h1, if_pos h2] at h; exact absurd h WithTop.coe_ne_top
  · rw [if_neg h1, if_neg h2, WithTop.coe_inj] at h
    have e1 : q.natDegree = e := le_antisymm (he ▸ le_max_right _ _) (not_lt.1 h1)
    have e2 : q₂.natDegree = e := le_antisymm (he₂ ▸ le_max_right _ _) (not_lt.1 h2)
    have c1 : q.coeff e ≠ 0 := by rw [← e1]; exact leadingCoeff_ne_zero.2 hq
    have c2 : q₂.coeff e ≠ 0 := by rw [← e2]; exact leadingCoeff_ne_zero.2 hq₂
    rw [div_eq_div_iff c1 c2] at h
    linear_combination h

/-- **Lemma 9.2**, endpoint `∞`: the values `R(∞), S(∞)` lie in `{a 0, a 1, a 2, ∞}` and are
distinct (no coincidence at `∞`). -/
theorem rational_endpoint_infty (hpair : NormalizedPair {0}ᶜ (ratEval R) (ratEval S) a) :
    infVal R.num R.denom ∈ valueSet a ∧ infVal S.num S.denom ∈ valueSet a ∧
      infVal R.num R.denom ≠ infVal S.num S.denom := by
  obtain ⟨hdeq, -, -, hXdeg, -, -, hinfR, hinfS, -⟩ := degree_saturation hpair
  refine ⟨hinfR, hinfS, fun h => ?_⟩
  have hX := coincPoly_ne_zero hpair
  set e := ratDeg R
  have hdS : ratDeg S = e := hdeq.symm
  have h0 := eq_of_infVal_eq R.denom_ne_zero S.denom_ne_zero rfl hdS h
  have hcoeff : (coincPoly R S).coeff (e + e) =
      R.num.coeff e * S.denom.coeff e - S.num.coeff e * R.denom.coeff e := by
    have b1 : R.num.natDegree ≤ e := le_max_left _ _
    have b2 : R.denom.natDegree ≤ e := le_max_right _ _
    have b3 : S.num.natDegree ≤ e := by rw [← hdS]; exact le_max_left _ _
    have b4 : S.denom.natDegree ≤ e := by rw [← hdS]; exact le_max_right _ _
    rw [coincPoly, coeff_sub, coeff_mul_add_eq_of_natDegree_le b1 b4,
      coeff_mul_add_eq_of_natDegree_le b3 b2]
  have hlc : (coincPoly R S).coeff (e + e) ≠ 0 := by
    rw [show e + e = (coincPoly R S).natDegree by rw [hXdeg, hdS]]
    exact leadingCoeff_ne_zero.2 hX
  exact hlc (hcoeff.trans h0)

/-- If the value at `∞` of `R` is finite, `R(t)` tends to it as `t → ∞`. -/
lemma tendsto_ratEval_of_infVal {c : ℂ} (h : infVal R.num R.denom = (c : Sphere)) :
    Tendsto (ratEval R) (cocompact ℂ) (𝓝 c) := by
  unfold infVal at h
  by_cases h1 : R.denom.natDegree < max R.num.natDegree R.denom.natDegree
  · rw [if_pos h1] at h; exact absurd h WithTop.top_ne_coe
  rw [if_neg h1, WithTop.coe_inj] at h
  have e1 : R.denom.natDegree = ratDeg R := le_antisymm (le_max_right _ _) (not_lt.1 h1)
  have hQ0 : (reflect (ratDeg R) R.denom).eval 0 ≠ 0 := by
    rw [eval_reflect_zero, ← e1]; exact leadingCoeff_ne_zero.2 R.denom_ne_zero
  have hcont : ContinuousAt (ratInvFun R) 0 :=
    ((reflect (ratDeg R) R.num).differentiable.continuous.continuousAt).div
      ((reflect (ratDeg R) R.denom).differentiable.continuous.continuousAt) hQ0
  have hval : ratInvFun R 0 = c := by
    rw [ratInvFun, eval_reflect_zero, eval_reflect_zero, ← h]; rfl
  have hinv : Tendsto (fun t : ℂ => t⁻¹) (cocompact ℂ) (𝓝 0) :=
    Metric.cobounded_eq_cocompact (α := ℂ) ▸ Filter.tendsto_inv₀_cobounded
  have hne : ∀ᶠ t in cocompact ℂ, t ≠ 0 :=
    (isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact
  refine ((hval ▸ hcont.tendsto).comp hinv).congr' ?_
  filter_upwards [hne] with t ht
  simp [ratInvFun_eq R (inv_ne_zero ht)]

/-! ### Lemmas 9.3–9.5 without the assumption of Lemma 9.2 -/

/-- **Lemma 9.3** (rational auxiliary functions), unconditional: for a rational sharing datum,
`U = α t^u`, `V = β t^v` (off a finite set), and `U/V = m/n` at each finite common point. -/
theorem rational_monomials_of_pair (hpair : NormalizedPair {0}ᶜ (ratEval R) (ratEval S) a) :
    ∃ α β : ℂ, α ≠ 0 ∧ β ≠ 0 ∧ ∃ u v : ℤ,
      (∀ᶠ t in cofinite, t * auxU a (ratEval R) (ratEval S) t = α * t ^ u) ∧
      (∀ᶠ t in cofinite, t * auxV a (ratEval R) (ratEval S) t = β * t ^ v) ∧
      ∀ t₀ : ℂ, t₀ ≠ 0 → ∀ j : Fin 3, 0 < mult (ratEval R) (a j : Sphere) t₀ →
        α * t₀ ^ u * (mult (ratEval S) (a j : Sphere) t₀ : ℂ) =
          β * t₀ ^ v * (mult (ratEval R) (a j : Sphere) t₀ : ℂ) :=
  rational_monomials hpair (rational_coincidenceSimple hpair)

/-- **Lemma 9.4** (finite endpoint case), unconditional: if both maps of a rational sharing
datum are finite at `0`, or both are finite at `∞`, then all four values are shared CM on
`ℂ*`. -/
theorem rational_finite_endpoint_cm (hpair : NormalizedPair {0}ᶜ (ratEval R) (ratEval S) a)
    (hfin : (R.denom.eval 0 ≠ 0 ∧ S.denom.eval 0 ≠ 0) ∨
      (infVal R.num R.denom ≠ ⊤ ∧ infVal S.num S.denom ≠ ⊤)) :
    ∀ i : Fin 4, SharesCMOn {0}ᶜ (ratEval R) (ratEval S)
      (![(a 0 : Sphere), (a 1 : Sphere), (a 2 : Sphere), ⊤] i) := by
  have hco := rational_coincidenceSimple hpair
  have hdeg := rational_degree_eq hpair
  rcases hfin with ⟨hR0, hS0⟩ | ⟨hRi, hSi⟩
  · obtain ⟨hR, hS, -, hne⟩ := rational_endpoint_zero hpair
    obtain ⟨j, hj⟩ := hR.resolve_left hR0
    obtain ⟨k, hk⟩ := hS.resolve_left hS0
    have hjk : j ≠ k := by
      rintro rfl; exact hne hR0 hS0 (hj.trans hk.symm)
    exact rational_finite_endpoint hpair hco hdeg hR0 hS0 hjk hj hk
  · obtain ⟨hR, hS, hne⟩ := rational_endpoint_infty hpair
    obtain ⟨j, hj⟩ := (mem_valueSet.1 hR).resolve_right hRi
    obtain ⟨k, hk⟩ := (mem_valueSet.1 hS).resolve_right hSi
    have hjk : j ≠ k := by
      rintro rfl; exact hne (hj.trans hk.symm)
    exact rational_finite_endpoint_infty hpair hco hdeg hjk (tendsto_ratEval_of_infVal hj)
      (tendsto_ratEval_of_infVal hk)

end ThreeIM
