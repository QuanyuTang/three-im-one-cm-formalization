module

public import RequestProject.ThreeIM.RationalEndpointRhoOne

/-!
# Affine changes of the target for rational sharing data

The affine target change `w ↦ (w - b)/d` (`d ≠ 0`) preserves local degrees, sends a normalized
pair for values `a` to a normalized pair for the transformed values, multiplies the auxiliary
functions `U, V` by `d`, and preserves the endpoint configuration of Lemma 9.5.  It is used in
the proof of Proposition 9.28 to bring the three finite values to `0, 1, c` (Lemma 9.6).
-/

@[expose] public section

open Filter Set Topology Polynomial

namespace ThreeIM

/-! ### Function level -/

lemma mult_congr_nhdsNE {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝[≠] z] g) (b : Sphere) :
    mult f b z = mult g b z := by
  induction b using WithTop.recTopCoe with
  | top => simp only [mult_top]; rw [meromorphicOrderAt_congr h]
  | coe c =>
    simp only [mult_coe]
    rw [meromorphicOrderAt_congr (f₂ := fun w => g w - c) (h.mono fun w hw => by rw [hw])]

lemma order_div_const {F : ℂ → ℂ} {z : ℂ} (hF : MeromorphicAt F z) {d : ℂ} (hd : d ≠ 0) :
    meromorphicOrderAt (fun w => F w / d) z = meromorphicOrderAt F z := by
  have e : (fun w => F w / d) = F * fun _ => d⁻¹ := by ext w; simp [div_eq_mul_inv]
  rw [e, meromorphicOrderAt_mul hF (MeromorphicAt.const _ _), order_const_eq _ (inv_ne_zero hd),
    add_zero]

/-- Local degrees are invariant under an affine change of the target (finite values). -/
lemma mult_affine_coe {f : ℂ → ℂ} {z : ℂ} (hf : MeromorphicAt f z) {d : ℂ} (hd : d ≠ 0)
    (b c : ℂ) : mult (fun w => (f w - b) / d) (((c - b) / d : ℂ) : Sphere) z =
      mult f (c : Sphere) z := by
  simp only [mult_coe]
  have e : (fun w => (f w - b) / d - (c - b) / d) = fun w => (f w - c) / d := by
    ext w; ring
  rw [e, order_div_const (F := fun w => f w - c) (hf.sub (MeromorphicAt.const c z)) hd]

/-- Local degrees are invariant under an affine change of the target (the value `∞`). -/
lemma mult_affine_top {f : ℂ → ℂ} {z : ℂ} (hf : MeromorphicAt f z) {d : ℂ} (hd : d ≠ 0)
    (b : ℂ) : mult (fun w => (f w - b) / d) ⊤ z = mult f ⊤ z := by
  simp only [mult_top]
  rw [order_div_const (F := fun w => f w - b) (hf.sub (MeromorphicAt.const b z)) hd]
  rcases lt_or_ge (meromorphicOrderAt f z) 0 with h | h
  · rw [order_sub_const_of_neg h]
  · rw [untop₀_toNat_neg_eq_zero_of_nonneg h,
      untop₀_toNat_neg_eq_zero_of_nonneg (order_sub_const_nonneg hf h b)]

/-! ### Rational functions -/

/-- The rational function `(R - b)/d`. -/
noncomputable def ratAff (b d : ℂ) (R : RatFunc ℂ) : RatFunc ℂ :=
  algebraMap ℂ[X] (RatFunc ℂ) (C d⁻¹ * (R.num - C b * R.denom)) /
    algebraMap ℂ[X] (RatFunc ℂ) R.denom

lemma isCoprime_ratAff {d : ℂ} (hd : d ≠ 0) (b : ℂ) (R : RatFunc ℂ) :
    IsCoprime (C d⁻¹ * (R.num - C b * R.denom)) R.denom := by
  rw [isCoprime_mul_unit_left_left (isUnit_C.2 (Ne.isUnit (inv_ne_zero hd)))]
  have := (RatFunc.isCoprime_num_denom R).add_mul_left_left (-C b)
  convert this using 1; ring

lemma ratEval_ratAff {d : ℂ} (hd : d ≠ 0) (b : ℂ) (R : RatFunc ℂ) (t : ℂ) :
    ratEval (ratAff b d R) t = d⁻¹ * (R.num.eval t - b * R.denom.eval t) / R.denom.eval t := by
  unfold ratAff
  rw [ratEval_div_of_coprime R.denom_ne_zero (isCoprime_ratAff hd b R)]
  simp

lemma ratEval_ratAff_of_ne {d : ℂ} (hd : d ≠ 0) (b : ℂ) (R : RatFunc ℂ) {t : ℂ}
    (ht : R.denom.eval t ≠ 0) : ratEval (ratAff b d R) t = (ratEval R t - b) / d := by
  rw [ratEval_ratAff hd, ratEval_eq]
  field_simp

lemma denom_ratAff_eval {d : ℂ} (hd : d ≠ 0) (b : ℂ) (R : RatFunc ℂ) {t : ℂ} :
    (ratAff b d R).denom.eval t ≠ 0 ↔ R.denom.eval t ≠ 0 := by
  obtain ⟨u, hu, -, hdd⟩ := num_denom_div_of_coprime R.denom_ne_zero (isCoprime_ratAff hd b R)
  unfold ratAff
  rw [hdd]
  simp [hu]

/-- Off the poles of `R`, and so in a neighbourhood of each such point, `ratAff b d R` is
`(R - b)/d`. -/
lemma ratEval_ratAff_eventuallyEq {d : ℂ} (hd : d ≠ 0) (b : ℂ) (R : RatFunc ℂ) {t : ℂ}
    (ht : R.denom.eval t ≠ 0) :
    ratEval (ratAff b d R) =ᶠ[𝓝 t] fun w => (ratEval R w - b) / d := by
  filter_upwards [R.denom.continuous.continuousAt.eventually_ne ht] with w hw
  exact ratEval_ratAff_of_ne hd b R hw

lemma ratEval_ratAff_cofinite {d : ℂ} (hd : d ≠ 0) (b : ℂ) (R : RatFunc ℂ) :
    ∀ᶠ t in cofinite, ratEval (ratAff b d R) t = (ratEval R t - b) / d := by
  filter_upwards [IsRatFun.eventually_ne R.denom_ne_zero] with t ht
  exact ratEval_ratAff_of_ne hd b R ht

lemma ratEval_ratAff_nhdsNE {d : ℂ} (hd : d ≠ 0) (b : ℂ) (R : RatFunc ℂ) (z : ℂ) :
    ratEval (ratAff b d R) =ᶠ[𝓝[≠] z] fun w => (ratEval R w - b) / d :=
  eventually_nhdsNE_of_cofinite (ratEval_ratAff_cofinite hd b R) z

lemma mult_ratAff_coe {d : ℂ} (hd : d ≠ 0) (b : ℂ) (R : RatFunc ℂ) (c z : ℂ) :
    mult (ratEval (ratAff b d R)) (((c - b) / d : ℂ) : Sphere) z = mult (ratEval R) (c : Sphere) z := by
  rw [mult_congr_nhdsNE (ratEval_ratAff_nhdsNE hd b R z),
    mult_affine_coe (meromorphicAt_ratEval R z) hd]

lemma mult_ratAff_top {d : ℂ} (hd : d ≠ 0) (b : ℂ) (R : RatFunc ℂ) (z : ℂ) :
    mult (ratEval (ratAff b d R)) ⊤ z = mult (ratEval R) ⊤ z := by
  rw [mult_congr_nhdsNE (ratEval_ratAff_nhdsNE hd b R z),
    mult_affine_top (meromorphicAt_ratEval R z) hd]

lemma ratAff_ne_C {d : ℂ} (hd : d ≠ 0) (b : ℂ) {R : RatFunc ℂ}
    (hR : IsNonconstMeroOn (ratEval R) {0}ᶜ) (c : ℂ) : ratAff b d R ≠ RatFunc.C c := by
  intro hc
  apply hR.2 1 one_ne_zero (b + d * c)
  rw [meromorphicOrderAt_eq_top_iff]
  filter_upwards [ratEval_ratAff_nhdsNE hd b R 1] with w hw
  have h1 : ratEval (ratAff b d R) w = c := by rw [hc]; simp [ratEval]
  rw [h1] at hw
  field_simp at hw
  linear_combination -hw

/-- The cubic `P` under the affine change sending `a j, a i, a l` to `0, 1, c`. -/
lemma cubicP_affine {a : Fin 3 → ℂ} {j i l : Fin 3} (hij : i ≠ j) (hlj : l ≠ j) (hli : l ≠ i)
    {d c : ℂ} (hd0 : d ≠ 0) (hd : d = a i - a j) (hc : c * d = a l - a j) (x : ℂ) :
    cubicP ![0, 1, c] ((x - a j) / d) * d ^ 3 = cubicP a x := by
  have e : cubicP ![0, 1, c] ((x - a j) / d) * d ^ 3 = (x - a j) * (x - a i) * (x - a l) := by
    have hi : a i = a j + d := by rw [hd]; ring
    have hl : a l = a j + c * d := by rw [hc]; ring
    rw [hi, hl]
    simp only [cubicP, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    field_simp
    ring
  rw [e]
  fin_cases j <;> fin_cases i <;> fin_cases l <;>
    first
    | exact absurd rfl hij
    | exact absurd rfl hlj
    | exact absurd rfl hli
    | (simp only [cubicP, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue] <;> ring)

/-- The auxiliary function `t·U` under the affine change of the target. -/
lemma mul_auxU_ratAff {a : Fin 3 → ℂ} {R S : RatFunc ℂ} {j i l : Fin 3} (hij : i ≠ j)
    (hlj : l ≠ j) (hli : l ≠ i) {d c : ℂ} (hd0 : d ≠ 0) (hd : d = a i - a j)
    (hc : c * d = a l - a j) {t : ℂ} (hR : R.denom.eval t ≠ 0) (hS : S.denom.eval t ≠ 0) :
    t * auxU ![0, 1, c] (ratEval (ratAff (a j) d R)) (ratEval (ratAff (a j) d S)) t =
      d * (t * auxU a (ratEval R) (ratEval S) t) := by
  have hder : deriv (ratEval (ratAff (a j) d R)) t = deriv (ratEval R) t / d := by
    rw [(ratEval_ratAff_eventuallyEq hd0 (a j) R hR).deriv_eq, deriv_div_const, deriv_sub_const]
  have hP := cubicP_affine hij hlj hli hd0 hd hc (ratEval R t)
  have hP' : cubicP ![0, 1, c] ((ratEval R t - a j) / d) = cubicP a (ratEval R t) / d ^ 3 := by
    rw [← hP]; field_simp
  simp only [auxU]
  rw [hder, ratEval_ratAff_of_ne hd0 _ R hR, ratEval_ratAff_of_ne hd0 _ S hS, hP',
    div_div_eq_mul_div]
  field_simp
  ring

/-- The auxiliary function `t·V` under the affine change of the target. -/
lemma mul_auxV_ratAff {a : Fin 3 → ℂ} {R S : RatFunc ℂ} {j i l : Fin 3} (hij : i ≠ j)
    (hlj : l ≠ j) (hli : l ≠ i) {d c : ℂ} (hd0 : d ≠ 0) (hd : d = a i - a j)
    (hc : c * d = a l - a j) {t : ℂ} (hR : R.denom.eval t ≠ 0) (hS : S.denom.eval t ≠ 0) :
    t * auxV ![0, 1, c] (ratEval (ratAff (a j) d R)) (ratEval (ratAff (a j) d S)) t =
      d * (t * auxV a (ratEval R) (ratEval S) t) := by
  have hder : deriv (ratEval (ratAff (a j) d S)) t = deriv (ratEval S) t / d := by
    rw [(ratEval_ratAff_eventuallyEq hd0 (a j) S hS).deriv_eq, deriv_div_const, deriv_sub_const]
  have hP := cubicP_affine hij hlj hli hd0 hd hc (ratEval S t)
  have hP' : cubicP ![0, 1, c] ((ratEval S t - a j) / d) = cubicP a (ratEval S t) / d ^ 3 := by
    rw [← hP]; field_simp
  simp only [auxV]
  rw [hder, ratEval_ratAff_of_ne hd0 _ R hR, ratEval_ratAff_of_ne hd0 _ S hS, hP',
    div_div_eq_mul_div]
  field_simp
  ring

/-- Defects are preserved by the affine change of the target. -/
lemma IsDefect.ratAff {R S : RatFunc ℂ} {d : ℂ} (hd0 : d ≠ 0) (b v : ℂ) {z : ℂ}
    (h : IsDefect (ratEval R) (ratEval S) (v : Sphere) z) :
    IsDefect (ratEval (ratAff b d R)) (ratEval (ratAff b d S)) (((v - b) / d : ℂ) : Sphere) z := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [IsDefect, mult_ratAff_coe hd0 b R v z, mult_ratAff_coe hd0 b S v z]
  exact ⟨h1, h2, h3⟩

/-- **Affine normalization of the target** (used for Lemma 9.6): the change `w ↦ (w - a j)/d`,
`d = a i - a j`, takes a normalized pair in the balanced endpoint configuration with
`R(0) = S(∞) = a j` to one for the values `0, 1, c` (`c = (a l - a j)/d`), with `R(0) = S(∞) = 0`
and coefficient multiplied by `d`. -/
theorem OppositeData.affine {a : Fin 3 → ℂ} {R S : RatFunc ℂ} {j i l : Fin 3} {ρ : ℕ}
    {κ₀ c : ℂ} (hij : i ≠ j) (hlj : l ≠ j) (hli : l ≠ i) (hc : (a l - a j) / (a i - a j) = c)
    (hpair : NormalizedPair {0}ᶜ (ratEval R) (ratEval S) a)
    (hd : OppositeData a R S j j ρ κ₀ κ₀) :
    NormalizedPair {0}ᶜ (ratEval (ratAff (a j) (a i - a j) R))
        (ratEval (ratAff (a j) (a i - a j) S)) ![0, 1, c] ∧
      OppositeData ![0, 1, c] (ratAff (a j) (a i - a j) R) (ratAff (a j) (a i - a j) S) 0 0 ρ
        ((a i - a j) * κ₀) ((a i - a j) * κ₀) := by
  set d := a i - a j with hd_def
  have ha := hpair.injective
  have hd0 : d ≠ 0 := sub_ne_zero.2 (ha.ne hij)
  have hcd : c * d = a l - a j := by rw [← hc]; field_simp
  have hc0 : c ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hcd; exact ha.ne hlj (sub_eq_zero.1 hcd.symm)
  have hc1 : c ≠ 1 := by
    intro h1; rw [h1, one_mul, hd_def] at hcd; exact ha.ne hli (by linear_combination -hcd)
  have hval : ∀ m : Fin 3, (![0, 1, c] : Fin 3 → ℂ) m = (a (![j, i, l] m) - a j) / d := by
    intro m
    fin_cases m
    · simp
    · exact (div_self hd0).symm
    · simp [← hc, hd_def]
  set R' := ratAff (a j) d R
  set S' := ratAff (a j) d S
  have hpair' : NormalizedPair {0}ᶜ (ratEval R') (ratEval S') ![0, 1, c] := by
    refine ⟨isNonconstMeroOn_ratEval (ratAff_ne_C hd0 _ hpair.nonconst_f) _,
      isNonconstMeroOn_ratEval (ratAff_ne_C hd0 _ hpair.nonconst_g) _, fun z hz => ?_, ?_,
      fun m => ?_, ?_⟩
    · have e : (fun w => ratEval R' w - ratEval S' w) =ᶠ[𝓝[≠] z]
          fun w => (ratEval R w - ratEval S w) / d := by
        filter_upwards [ratEval_ratAff_nhdsNE hd0 (a j) R z,
          ratEval_ratAff_nhdsNE hd0 (a j) S z] with w h1 h2
        rw [h1, h2]; ring
      rw [meromorphicOrderAt_congr e,
        order_div_const (F := fun w => ratEval R w - ratEval S w)
          ((meromorphicAt_ratEval R z).sub (meromorphicAt_ratEval S z)) hd0]
      exact hpair.distinct z hz
    · intro m m' hmm
      fin_cases m <;> fin_cases m' <;> simp_all [eq_comm]
    · intro z hz
      rw [hval m, mult_ratAff_coe hd0, mult_ratAff_coe hd0]
      exact hpair.im _ z hz
    · intro z hz
      rw [mult_ratAff_top hd0, mult_ratAff_top hd0]
      exact hpair.cm_top z hz
  refine ⟨hpair', ?_⟩
  have hden := fun (F : RatFunc ℂ) => IsRatFun.eventually_ne F.denom_ne_zero
  refine ⟨hd.rho_pos, mul_ne_zero hd0 hd.alpha_ne, mul_ne_zero hd0 hd.alpha_ne,
    (denom_ratAff_eval hd0 _ R).2 hd.denom_zero, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ratEval_ratAff_of_ne hd0 _ R hd.denom_zero, hd.value_zero]; simp
  · have hneg : meromorphicOrderAt (ratEval S) 0 < 0 := by
      rw [hd.order_zero]; exact_mod_cast (by have := hd.rho_pos; omega : -(ρ : ℤ) < 0)
    rw [meromorphicOrderAt_congr (ratEval_ratAff_nhdsNE hd0 (a j) S 0),
      order_div_const (F := fun w => ratEval S w - a j)
        ((meromorphicAt_ratEval S 0).sub (MeromorphicAt.const _ _)) hd0,
      order_sub_const_of_neg hneg, hd.order_zero]
  · have hmer : MeromorphicAt (fun s => ratEval R s⁻¹) 0 :=
      (meromorphicAt_ratInvFun R).congr (by
        filter_upwards [self_mem_nhdsWithin] with x hx
        exact ratInvFun_eq R hx)
    have hneg : meromorphicOrderAt (fun s => ratEval R s⁻¹) 0 < 0 := by
      rw [hd.order_infty]; exact_mod_cast (by have := hd.rho_pos; omega : -(ρ : ℤ) < 0)
    have e : (fun s => ratEval R' s⁻¹) =ᶠ[𝓝[≠] 0] fun s => (ratEval R s⁻¹ - a j) / d :=
      eventually_cofinite_inv (ratEval_ratAff_cofinite hd0 (a j) R)
    rw [meromorphicOrderAt_congr e,
      order_div_const (F := fun s => ratEval R s⁻¹ - a j) (hmer.sub (MeromorphicAt.const _ _)) hd0,
      order_sub_const_of_neg hneg, hd.order_infty]
  · have h := (hd.tendsto_infty.sub_const (a j)).div_const d
    rw [sub_self, zero_div] at h
    refine h.congr' ?_
    exact Filter.Eventually.mono (cocompact_le_cofinite (ratEval_ratAff_cofinite hd0 (a j) S))
      fun t ht => ht.symm
  · filter_upwards [hd.aux_U, hden R, hden S] with t ht hR hS
    rw [mul_auxU_ratAff hij hlj hli hd0 rfl hcd hR hS, ht]; ring
  · filter_upwards [hd.aux_V, hden R, hden S] with t ht hR hS
    rw [mul_auxV_ratAff hij hlj hli hd0 rfl hcd hR hS, ht]; ring

end ThreeIM
