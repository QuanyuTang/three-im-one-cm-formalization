module

public import RequestProject.ThreeIM.RationalDegreeFive

/-!
# Lemma 9.8: the count `d ≤ 5ρ`

With `Φ_j = (t θ_j)² - c_j² α β` (see `RationalDegreeFive`), we show:

* `Φ_j = t² W_j` off a finite set (`phiFun_eq_mul_WAux`);
* at `t₀ ∈ ℂ*`, `Φ_j` has at most a double pole, no pole unless `t₀` is a defect over `a_j`,
  and exactly a double pole at such a defect (`order_phiFun_at`);
* `Φ_j` vanishes at each common pole in `ℂ*` (`order_phiFun_pos_at_pole`);
* `Φ_j` is finite at `0` and at `∞` (`order_phiFun_nonneg`, `order_phiFun_infty_nonneg`).

Counting zeros against poles (`card_le_of_ratFun`) gives `d - ρ ≤ 2 D_j`, and summing over `j`
(the defect sets and the common poles are disjoint subsets of the `≤ 2d` common points in `ℂ*`)
gives `d ≤ 5ρ` (`OppositeData.ratDeg_le`, `OppositeData.ratDeg_le_of_defect`).
-/

@[expose] public section

open Filter Set Topology Polynomial

namespace ThreeIM

lemma IsRatFun.meromorphicAt {φ : ℂ → ℂ} (h : IsRatFun φ) (x : ℂ) : MeromorphicAt φ x := by
  obtain ⟨p, q, -, e⟩ := h
  exact (IsRatFun.meromorphicAt_quot p q x).congr
    ((eventually_nhdsNE_of_cofinite e x).mono fun _ h => h.symm)

/-- `Φ_j = t² W_j` off a finite set, in the endpoint configuration `t U = α t^{-ρ}`,
`t V = β t^ρ`. -/
lemma phiFun_eq_mul_WAux {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {ρ : ℕ} {α β : ℂ} (j : Fin 3)
    (hU : ∀ᶠ t in cofinite, t * auxU a f g t = α * t ^ (-(ρ : ℤ)))
    (hV : ∀ᶠ t in cofinite, t * auxV a f g t = β * t ^ (ρ : ℤ)) :
    ∀ᶠ t in cofinite, PhiFun a j (cAux a j ^ 2 * (α * β)) f g t = t ^ 2 * WAux a j f g t := by
  filter_upwards [hU, hV, (Set.finite_singleton (0 : ℂ)).compl_mem_cofinite] with t h1 h2 ht
  have ht : t ≠ 0 := ht
  have key : t ^ 2 * auxPsi a f g t = α * β := by
    simp only [auxPsi]
    calc t ^ 2 * (auxU a f g t * auxV a f g t) = (t * auxU a f g t) * (t * auxV a f g t) := by
          ring
      _ = α * β := by
          rw [h1, h2, mul_mul_mul_comm, ← zpow_add₀ ht]; simp
  simp only [PhiFun, WAux]
  rw [← key]; ring

/-- Order bookkeeping for `θ² - c Ψ` when `Ψ` has order `0`. -/
lemma order_sq_sub_mul {θ Ψ : ℂ → ℂ} {x c : ℂ} (hθ : MeromorphicAt θ x) (hΨ : MeromorphicAt Ψ x)
    (hΨ0 : meromorphicOrderAt Ψ x = 0) :
    ((-1 : WithTop ℤ) ≤ meromorphicOrderAt θ x →
        ((-2 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (fun z => θ z ^ 2 - c * Ψ z) x) ∧
      (0 ≤ meromorphicOrderAt θ x → 0 ≤ meromorphicOrderAt (fun z => θ z ^ 2 - c * Ψ z) x) ∧
      (meromorphicOrderAt θ x = -1 →
        meromorphicOrderAt (fun z => θ z ^ 2 - c * Ψ z) x = ((-2 : ℤ) : WithTop ℤ)) := by
  have hcm : MeromorphicAt (fun z => -(c * Ψ z)) x := ((MeromorphicAt.const c x).mul hΨ).neg
  have hc : 0 ≤ meromorphicOrderAt (fun z => -(c * Ψ z)) x := by
    have e : (fun z => -(c * Ψ z)) = (fun _ => -c) * Ψ := by ext z; simp
    rw [e, meromorphicOrderAt_mul (MeromorphicAt.const _ x) hΨ, hΨ0, add_zero]
    classical
    rw [meromorphicOrderAt_const]
    split_ifs <;> simp
  have hsq : meromorphicOrderAt (fun z => θ z ^ 2) x = 2 * meromorphicOrderAt θ x := by
    have := meromorphicOrderAt_pow hθ (n := 2)
    exact_mod_cast this
  have hsqm : MeromorphicAt (fun z => θ z ^ 2) x := hθ.pow 2
  have eW : (fun z => θ z ^ 2 - c * Ψ z) = (fun z => θ z ^ 2) + (fun z => -(c * Ψ z)) := by
    ext z; simp [sub_eq_add_neg]
  have hmin := meromorphicOrderAt_add hsqm hcm
  rw [← eW, hsq] at hmin
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · refine le_trans (le_min ?_ (le_trans (by decide) hc)) hmin
    generalize meromorphicOrderAt θ x = o at h ⊢
    induction o using WithTop.recTopCoe with
    | top => simp
    | coe n =>
      have : (-1 : ℤ) ≤ n := WithTop.coe_le_coe.1 h
      rw [show (2 : WithTop ℤ) * (n : WithTop ℤ) = ((2 * n : ℤ) : WithTop ℤ) by norm_cast]
      exact WithTop.coe_le_coe.2 (by omega)
  · refine le_trans (le_min ?_ hc) hmin
    generalize meromorphicOrderAt θ x = o at h ⊢
    induction o using WithTop.recTopCoe with
    | top => simp
    | coe n =>
      have : (0 : ℤ) ≤ n := WithTop.coe_le_coe.1 h
      rw [show (2 : WithTop ℤ) * (n : WithTop ℤ) = ((2 * n : ℤ) : WithTop ℤ) by norm_cast]
      exact WithTop.coe_le_coe.2 (by omega)
  · rw [eW, meromorphicOrderAt_add_eq_left_of_lt hcm, hsq, h]
    · rfl
    · rw [hsq, h]; exact lt_of_lt_of_le (by decide) hc


lemma IsRatFun.thetaAux {f g : ℂ → ℂ} (hf : IsRatFun f) (hg : IsRatFun g) (a : Fin 3 → ℂ)
    (j : Fin 3) : IsRatFun (thetaAux a j f g) := by
  unfold ThreeIM.thetaAux; exact (hf.thetaFun a j).sub (hg.thetaFun a j)

/-- Near `t₀ ≠ 0`, `Φ_j` and `W_j` have the same order. -/
lemma order_phiFun_eq_WAux {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {ρ : ℕ} {α β : ℂ}
    (hpair : NormalizedPair {0}ᶜ f g a) (hf : IsRatFun f) (hg : IsRatFun g)
    (hU : ∀ᶠ t in cofinite, t * auxU a f g t = α * t ^ (-(ρ : ℤ)))
    (hV : ∀ᶠ t in cofinite, t * auxV a f g t = β * t ^ (ρ : ℤ)) (j : Fin 3) {t₀ : ℂ}
    (ht₀ : t₀ ≠ 0) :
    MeromorphicAt (WAux a j f g) t₀ ∧
    PhiFun a j (cAux a j ^ 2 * (α * β)) f g =ᶠ[𝓝[≠] t₀] (fun t => t * (t * WAux a j f g t)) ∧
    meromorphicOrderAt (PhiFun a j (cAux a j ^ 2 * (α * β)) f g) t₀ =
      meromorphicOrderAt (WAux a j f g) t₀ := by
  have hθm : MeromorphicAt (thetaAux a j f g) t₀ := (hf.thetaAux hg a j).meromorphicAt t₀
  have hΨm : MeromorphicAt (auxPsi a f g) t₀ :=
    (hpair.meromorphicAt_auxU_of_mem ht₀).mul (hpair.meromorphicAt_auxV_of_mem ht₀)
  have hWm : MeromorphicAt (WAux a j f g) t₀ := by
    unfold WAux; exact (hθm.pow 2).sub ((MeromorphicAt.const _ _).mul hΨm)
  have heq : PhiFun a j (cAux a j ^ 2 * (α * β)) f g =ᶠ[𝓝[≠] t₀]
      (fun t => t * (t * WAux a j f g t)) :=
    (eventually_nhdsNE_of_cofinite (phiFun_eq_mul_WAux j hU hV) t₀).mono fun t h => by
      rw [h]; ring
  refine ⟨hWm, heq, ?_⟩
  have hm2 : MeromorphicAt (fun t => t * WAux a j f g t) t₀ :=
    analyticAt_id.meromorphicAt.mul hWm
  rw [meromorphicOrderAt_congr heq, order_mul_id_eq ht₀ hm2, order_mul_id_eq ht₀ hWm]

/-- **Lemma 9.8**, local part at a point `t₀ ∈ ℂ*`: `Φ_j` has at most a double pole, no pole
unless `t₀` is a defect over `a_j`, and exactly a double pole at a defect over `a_j`. -/
theorem order_phiFun_at {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {ρ : ℕ} {α β : ℂ}
    (hpair : NormalizedPair {0}ᶜ f g a) (hf : IsRatFun f) (hg : IsRatFun g)
    (hα : α ≠ 0) (hβ : β ≠ 0)
    (hU : ∀ᶠ t in cofinite, t * auxU a f g t = α * t ^ (-(ρ : ℤ)))
    (hV : ∀ᶠ t in cofinite, t * auxV a f g t = β * t ^ (ρ : ℤ)) (j : Fin 3) {t₀ : ℂ}
    (ht₀ : t₀ ≠ 0) :
    ((-2 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (PhiFun a j (cAux a j ^ 2 * (α * β)) f g) t₀ ∧
    (¬ IsDefect f g (a j : Sphere) t₀ →
      0 ≤ meromorphicOrderAt (PhiFun a j (cAux a j ^ 2 * (α * β)) f g) t₀) ∧
    (IsDefect f g (a j : Sphere) t₀ →
      meromorphicOrderAt (PhiFun a j (cAux a j ^ 2 * (α * β)) f g) t₀ = ((-2 : ℤ) : WithTop ℤ)) := by
  obtain ⟨-, -, hord⟩ := order_phiFun_eq_WAux hpair hf hg hU hV j ht₀
  have hθm : MeromorphicAt (thetaAux a j f g) t₀ := (hf.thetaAux hg a j).meromorphicAt t₀
  have hΨm : MeromorphicAt (auxPsi a f g) t₀ :=
    (hpair.meromorphicAt_auxU_of_mem ht₀).mul (hpair.meromorphicAt_auxV_of_mem ht₀)
  have hΨ0 := order_auxPsi_eq_zero_of_pow hα hβ hU hV ht₀
  obtain ⟨k1, k2, k3⟩ := order_sq_sub_mul (c := cAux a j ^ 2) hθm hΨm hΨ0
  obtain ⟨t1, t2, t3⟩ := thetaAux_order_on hpair j t₀ ht₀
  rw [hord]
  refine ⟨k1 t1, fun hnd => k2 ?_, fun hd => k3 (t3 hd)⟩
  by_contra hneg
  rcases t2 (lt_of_not_ge hneg) with h | h
  · exact hnd h
  · rw [hΨ0] at h; exact lt_irrefl _ h

/-- **Lemma 9.8**, at a common pole `t₀ ∈ ℂ*`: `Φ_j` vanishes there. -/
theorem order_phiFun_pos_at_pole {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {ρ : ℕ} {α β : ℂ}
    (hpair : NormalizedPair {0}ᶜ f g a) (hf : IsRatFun f) (hg : IsRatFun g)
    (hU : ∀ᶠ t in cofinite, t * auxU a f g t = α * t ^ (-(ρ : ℤ)))
    (hV : ∀ᶠ t in cofinite, t * auxV a f g t = β * t ^ (ρ : ℤ)) (j : Fin 3) {t₀ : ℂ}
    (ht₀ : t₀ ≠ 0) (hco : CoincidenceSimpleAt a f g t₀) (hpole : 0 < mult f ⊤ t₀) :
    0 < meromorphicOrderAt (PhiFun a j (cAux a j ^ 2 * (α * β)) f g) t₀ := by
  obtain ⟨-, heq, -⟩ := order_phiFun_eq_WAux hpair hf hg hU hV j ht₀
  have h1 := (hpair.pole_of_coincidence ht₀ hpole (hco.pole hpole)).1
  have hfo : meromorphicOrderAt f t₀ = -1 := by
    rw [order_eq_neg_mult_top hpole, h1]; rfl
  have hW := tendsto_WAux_simple_pole_on hpair j ht₀ hfo
  have hT : Tendsto (fun t => t * (t * WAux a j f g t)) (𝓝[≠] t₀) (𝓝 0) := by
    have := (tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.tendsto t₀)).mul
      ((tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.tendsto t₀)).mul hW)
    simpa using this
  have hΦm : MeromorphicAt (PhiFun a j (cAux a j ^ 2 * (α * β)) f g) t₀ :=
    ((hf.phiFun hg a j _).meromorphicAt t₀)
  exact (tendsto_zero_iff_meromorphicOrderAt_pos hΦm).1 (hT.congr' heq.symm)


/-! ### Finiteness at `∞` -/

/-- A meromorphic function none of whose translates vanishes identically has a derivative
which does not vanish identically. -/
lemma order_deriv_ne_top {h : ℂ → ℂ} {x : ℂ} (hm : MeromorphicAt h x)
    (hc : ∀ c, meromorphicOrderAt (fun w => h w - c) x ≠ ⊤) :
    meromorphicOrderAt (deriv h) x ≠ ⊤ := by
  have h0 : meromorphicOrderAt h x ≠ ⊤ := by simpa using hc 0
  by_cases hneg : meromorphicOrderAt h x < 0
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 (hc 0)
    have hn0 : n ≠ 0 := by
      rintro rfl
      have : meromorphicOrderAt h x = 0 := by have := hn.symm; simpa using this
      rw [this] at hneg; exact lt_irrefl _ hneg
    rw [order_deriv_of_order_eq hm hn0 hn.symm]; exact WithTop.coe_ne_top
  · obtain ⟨c₀, hc₀⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hm (not_lt.1 hneg)
    have hsub : Tendsto (fun w => h w - c₀) (𝓝[≠] x) (𝓝 0) := by
      simpa using hc₀.sub_const c₀
    have hpos : 0 < meromorphicOrderAt (fun w => h w - c₀) x := (tendsto_zero_iff_meromorphicOrderAt_pos
      (hm.sub (MeromorphicAt.const c₀ x))).1 hsub
    obtain ⟨m, hm'⟩ := WithTop.ne_top_iff_exists.1 (hc c₀)
    have hm0 : m ≠ 0 := by
      rintro rfl; rw [← hm'] at hpos; exact lt_irrefl _ hpos
    rw [order_deriv_of_order_eq hm hm0 hm'.symm]; exact WithTop.coe_ne_top

lemma eventually_cofinite_inv {p : ℂ → Prop} (h : ∀ᶠ w in cofinite, p w) :
    ∀ᶠ s in 𝓝[≠] (0 : ℂ), p s⁻¹ :=
  tendsto_inv_cocompact.eventually (cocompact_le_cofinite h)

lemma order_ratEval_inv_sub_ne_top {R : RatFunc ℂ} {c : ℂ} (hR : R ≠ RatFunc.C c) :
    meromorphicOrderAt (fun s => ratEval R s⁻¹ - c) 0 ≠ ⊤ := by
  have hne : R.num - Polynomial.C c * R.denom ≠ 0 := by
    intro h
    apply hR
    rw [sub_eq_zero] at h
    have hd : (algebraMap (Polynomial ℂ) (RatFunc ℂ) R.denom) ≠ 0 :=
      RatFunc.algebraMap_ne_zero R.denom_ne_zero
    rw [← RatFunc.num_div_denom R, h, map_mul, mul_div_assoc, div_self hd, mul_one]
    simp [RatFunc.algebraMap_C]
  have heq : (fun s => ratEval R s⁻¹ - c) =ᶠ[𝓝[≠] 0]
      fun s => (R.num - Polynomial.C c * R.denom).eval s⁻¹ / R.denom.eval s⁻¹ := by
    filter_upwards [eventually_cofinite_inv (IsRatFun.eventually_ne R.denom_ne_zero)] with s hs
    rw [ratEval_eq, div_sub' hs]; congr 1; simp only [eval_sub, eval_mul, eval_C]; ring
  rw [meromorphicOrderAt_congr heq, order_quot_inv _ _ hne R.denom_ne_zero]
  exact WithTop.coe_ne_top

lemma ratEval_analytic_deriv_ne (R : RatFunc ℂ) (hw : wron R.num R.denom ≠ 0) :
    ∀ᶠ w in cofinite, AnalyticAt ℂ (ratEval R) w ∧ deriv (ratEval R) w ≠ 0 := by
  filter_upwards [IsRatFun.eventually_ne R.denom_ne_zero, IsRatFun.eventually_ne hw] with w h1 h2
  have hfun : ratEval R = fun t => R.num.eval t / R.denom.eval t := funext (ratEval_eq R)
  rw [hfun]
  refine ⟨(R.num.differentiable.analyticAt w).div (R.denom.differentiable.analyticAt w) h1, ?_⟩
  have hd : HasDerivAt (fun t => R.num.eval t / R.denom.eval t) _ w :=
    (R.num.hasDerivAt w).div (R.denom.hasDerivAt w) h1
  rw [hd.deriv]
  simp only [wron, eval_sub, eval_mul] at h2
  exact div_ne_zero h2 (pow_ne_zero 2 h1)

lemma meromorphicAt_ratEval_inv (R : RatFunc ℂ) :
    MeromorphicAt (fun s => ratEval R s⁻¹) 0 :=
  (meromorphicAt_ratInvFun R).congr (by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact ratInvFun_eq R hs)

/-- **Lemma 9.8**, at `∞`: `Φ_j` is finite at `∞`. -/
theorem order_phiFun_infty_nonneg {R S : RatFunc ℂ} (hR : ∀ c : ℂ, R ≠ RatFunc.C c)
    (hS : ∀ c : ℂ, S ≠ RatFunc.C c) (hwR : wron R.num R.denom ≠ 0)
    (hwS : wron S.num S.denom ≠ 0) (a : Fin 3 → ℂ) (j : Fin 3) (K : ℂ) :
    0 ≤ meromorphicOrderAt (fun s => PhiFun a j K (ratEval R) (ratEval S) s⁻¹) 0 := by
  have heq : (fun s => PhiFun a j K (ratEval R) (ratEval S) s⁻¹) =ᶠ[𝓝[≠] 0]
      PhiFun a j K (fun w => ratEval R w⁻¹) (fun w => ratEval S w⁻¹) := by
    filter_upwards [eventually_cofinite_inv (ratEval_analytic_deriv_ne R hwR),
      eventually_cofinite_inv (ratEval_analytic_deriv_ne S hwS), self_mem_nhdsWithin]
      with s h1 h2 hs
    exact phiFun_inv hs h1.1 h2.1 h1.2 h2.2 a j K
  rw [meromorphicOrderAt_congr heq]
  have hRc := fun c => order_ratEval_inv_sub_ne_top (hR c)
  have hSc := fun c => order_ratEval_inv_sub_ne_top (hS c)
  exact order_phiFun_nonneg (meromorphicAt_ratEval_inv R) (meromorphicAt_ratEval_inv S)
    (order_deriv_ne_top (meromorphicAt_ratEval_inv R) hRc)
    (order_deriv_ne_top (meromorphicAt_ratEval_inv S) hSc) hRc hSc a j K


/-! ### The count -/

lemma ratEval_eq_of_mult_pos {R : RatFunc ℂ} (hR : ∀ c : ℂ, R ≠ RatFunc.C c) {c t : ℂ}
    (h : 0 < mult (ratEval R) (c : Sphere) t) : ratEval R t = c := by
  have hd := denom_eval_ne_zero_of_mult_pos hR h
  rw [mult_ratEval_pos_iff hR, fiberPoly_coe] at h
  simp only [eval_sub, eval_mul, eval_C] at h
  rw [ratEval_eq, div_eq_iff hd]
  linear_combination h

/-- The combinatorial core of Lemma 9.8. -/
lemma degree_five_count {C A : Finset ℂ} {P : Fin 3 → Finset ℂ} {d ρ : ℕ} (hA : A ⊆ C)
    (hP : ∀ j, P j ⊆ C) (hPA : ∀ j, Disjoint (P j) A)
    (hPP : ∀ i j, i ≠ j → Disjoint (P i) (P j)) (hcard : ∀ j, A.card ≤ 2 * (P j).card)
    (hC : C.card ≤ 2 * d) (hAd : d ≤ A.card + ρ) : d ≤ 5 * ρ := by
  have h01 := Finset.card_union_of_disjoint (hPP 0 1 (by decide))
  have h012 := Finset.card_union_of_disjoint (s := P 0 ∪ P 1) (t := P 2)
    (Finset.disjoint_union_left.2 ⟨hPP 0 2 (by decide), hPP 1 2 (by decide)⟩)
  have hall := Finset.card_union_of_disjoint (s := P 0 ∪ P 1 ∪ P 2) (t := A)
    (Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_left.2 ⟨hPA 0, hPA 1⟩, hPA 2⟩)
  have hsub : P 0 ∪ P 1 ∪ P 2 ∪ A ⊆ C :=
    Finset.union_subset (Finset.union_subset (Finset.union_subset (hP 0) (hP 1)) (hP 2)) hA
  have hle := Finset.card_le_card hsub
  have c0 := hcard 0; have c1 := hcard 1; have c2 := hcard 2
  omega


/-- **Lemma 9.8** (degree bound in the presence of a defect).  In the endpoint configuration
of Lemma 9.5, if there is a defect over each of `a 0, a 1, a 2` in `ℂ*`, then `d ≤ 5ρ`. -/
theorem OppositeData.ratDeg_le {a : Fin 3 → ℂ} {R S : RatFunc ℂ} {j₀ k₀ : Fin 3} {ρ : ℕ}
    {α β : ℂ} (hpair : NormalizedPair {0}ᶜ (ratEval R) (ratEval S) a)
    (hd : OppositeData a R S j₀ k₀ ρ α β)
    (hdef : ∀ j, ∃ t, t ≠ 0 ∧ IsDefect (ratEval R) (ratEval S) (a j : Sphere) t) :
    ratDeg R ≤ 5 * ρ := by
  classical
  have hRnc := ne_C_of_nonconst hpair.nonconst_f
  have hSnc := ne_C_of_nonconst hpair.nonconst_g
  obtain ⟨hdeg, hone, -, hnat, -, -, -, -, hWR, hWS⟩ := degree_saturation hpair
  have hX := coincPoly_ne_zero hpair
  have hco := rational_coincidenceSimple hpair
  have hwR : wron R.num R.denom ≠ 0 := by
    obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset (ratFiberSet R a)
    intro h; exact hWR t ht (by rw [h, eval_zero])
  have hwS : wron S.num S.denom ≠ 0 := by
    obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset (ratFiberSet S a)
    intro h; exact hWS t ht (by rw [h, eval_zero])
  have hfR := IsRatFun.ratEval R
  have hgS := IsRatFun.ratEval S
  -- degrees
  have hnum : R.num.natDegree = R.denom.natDegree + ρ := by
    have h := hd.order_infty
    have e : (fun t => ratEval R t⁻¹) = fun s => R.num.eval s⁻¹ / R.denom.eval s⁻¹ :=
      funext fun s => ratEval_eq R _
    rw [e, order_quot_inv _ _ (num_ne_zero_of_nonconst hRnc) R.denom_ne_zero] at h
    have := WithTop.coe_inj.1 h
    omega
  have hdR : ratDeg R = R.num.natDegree := by
    unfold ratDeg; omega
  -- the common poles
  set A := R.denom.roots.toFinset with hAdef
  have hAmem : ∀ t ∈ A, t ≠ 0 ∧ 0 < mult (ratEval R) ⊤ t := by
    intro t ht
    rw [hAdef, Multiset.mem_toFinset, mem_roots R.denom_ne_zero] at ht
    refine ⟨fun h0 => hd.denom_zero (by subst h0; exact ht), (mult_top_ratEval_pos_iff hRnc t).2 ht⟩
  have hsimple : ∀ t ∈ A, R.denom.rootMultiplicity t = 1 := by
    intro t ht
    obtain ⟨ht0, hpole⟩ := hAmem t ht
    have h1 := (hpair.pole_of_coincidence ht0 hpole ((hco t ht0).pole hpole)).1
    have e1 := order_eq_neg_mult_top hpole
    have hden : R.denom.eval t = 0 := (mult_top_ratEval_pos_iff hRnc t).1 hpole
    have e2 := (order_ratEval_of_denom_eq_zero hden).2
    rw [e1, h1] at e2
    have := WithTop.coe_inj.1 e2
    omega
  have hAcard : A.card = R.denom.natDegree := by
    rw [← IsAlgClosed.card_roots_eq_natDegree, ← Multiset.toFinset_sum_count_eq, hAdef.symm]
    rw [Finset.card_eq_sum_ones]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [count_roots, hsimple t ht]
  -- the finite common points in `ℂ*`
  set C := (ratFiberSet R a).erase 0 with hCdef
  have hCcard : C.card ≤ 2 * ratDeg R := by
    have hsub : C ⊆ (coincPoly R S).roots.toFinset := by
      intro t ht
      rw [hCdef, Finset.mem_erase] at ht
      rw [Multiset.mem_toFinset, mem_roots hX]
      have := hone t ht.1 ht.2
      exact (rootMultiplicity_pos hX).1 (by omega)
    calc C.card ≤ (coincPoly R S).roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ (coincPoly R S).roots.card := Multiset.toFinset_card_le _
      _ ≤ (coincPoly R S).natDegree := card_roots' _
      _ = 2 * ratDeg R := by rw [hnat, ← hdeg]; ring
  have hAC : A ⊆ C := by
    intro t ht
    obtain ⟨ht0, hpole⟩ := hAmem t ht
    exact Finset.mem_erase.2 ⟨ht0, (mem_ratFiberSet hRnc).2 (Or.inr hpole)⟩
  -- the defects
  set P : Fin 3 → Finset ℂ := fun j =>
    C.filter fun t => IsDefect (ratEval R) (ratEval S) (a j : Sphere) t with hPdef
  have hPC : ∀ j, P j ⊆ C := fun j => Finset.filter_subset _ _
  have hPA : ∀ j, Disjoint (P j) A := by
    intro j
    rw [Finset.disjoint_left]
    intro t htP htA
    have hdt := (Finset.mem_filter.1 htP).2
    exact denom_eval_ne_zero_of_mult_pos hRnc hdt.1
      ((mult_top_ratEval_pos_iff hRnc t).1 (hAmem t htA).2)
  have hPP : ∀ i j, i ≠ j → Disjoint (P i) (P j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro t hi hj
    have h1 := ratEval_eq_of_mult_pos hRnc (Finset.mem_filter.1 hi).2.1
    have h2 := ratEval_eq_of_mult_pos hRnc (Finset.mem_filter.1 hj).2.1
    exact hij (hpair.injective (h1.symm.trans h2))
  have hcard : ∀ j, A.card ≤ 2 * (P j).card := by
    intro j
    refine card_le_of_ratFun (hfR.phiFun hgS a j (cAux a j ^ 2 * (α * β))) ?_ A (P j) ?_ ?_ ?_ ?_
    · obtain ⟨t, ht, hdt⟩ := hdef j
      refine ⟨t, ?_⟩
      rw [(order_phiFun_at hpair hfR hgS hd.alpha_ne hd.beta_ne hd.aux_U hd.aux_V j ht).2.2 hdt]
      exact WithTop.coe_ne_top
    · intro t ht
      obtain ⟨ht0, hpole⟩ := hAmem t ht
      exact order_phiFun_pos_at_pole hpair hfR hgS hd.aux_U hd.aux_V j ht0 (hco t ht0) hpole
    · intro t ht
      by_cases h0 : t = 0
      · subst h0
        have hRc := fun c => order_ratEval_sub_ne_top (hRnc c) (0 : ℂ)
        have hSc := fun c => order_ratEval_sub_ne_top (hSnc c) (0 : ℂ)
        exact order_phiFun_nonneg (meromorphicAt_ratEval R 0) (meromorphicAt_ratEval S 0)
          (order_deriv_ne_top (meromorphicAt_ratEval R 0) hRc)
          (order_deriv_ne_top (meromorphicAt_ratEval S 0) hSc) hRc hSc a j _
      · refine (order_phiFun_at hpair hfR hgS hd.alpha_ne hd.beta_ne hd.aux_U hd.aux_V j
          h0).2.1 fun hdt => ht ?_
        exact Finset.mem_filter.2 ⟨Finset.mem_erase.2 ⟨h0,
          (mem_ratFiberSet hRnc).2 (Or.inl ⟨j, hdt.1⟩)⟩, hdt⟩
    · intro t ht
      have h0 := (Finset.mem_erase.1 (Finset.mem_filter.1 ht).1).1
      exact (order_phiFun_at hpair hfR hgS hd.alpha_ne hd.beta_ne hd.aux_U hd.aux_V j h0).1
    · exact order_phiFun_infty_nonneg hRnc hSnc hwR hwS a j _
  exact degree_five_count hAC hPC hPA hPP hcard hCcard (by omega)


/-- **Lemma 9.8**, as stated in the paper: in the endpoint configuration of Lemma 9.5, if a
defect exists in `ℂ*`, then `d ≤ 5ρ`. -/
theorem OppositeData.ratDeg_le_of_defect {a : Fin 3 → ℂ} {R S : RatFunc ℂ} {j₀ k₀ : Fin 3}
    {ρ : ℕ} {α β : ℂ} (hpair : NormalizedPair {0}ᶜ (ratEval R) (ratEval S) a)
    (hd : OppositeData a R S j₀ k₀ ρ α β)
    (hdef : ∃ k, ∃ z ∈ ({0}ᶜ : Set ℂ), IsDefect (ratEval R) (ratEval S) (a k : Sphere) z) :
    ratDeg R ≤ 5 * ρ := by
  have h := ratEval_defect_at_every_value (ne_C_of_nonconst hpair.nonconst_f)
    (ne_C_of_nonconst hpair.nonconst_g) a hpair.injective hpair.im hpair.cm_top hdef
  exact hd.ratDeg_le hpair fun j => by
    obtain ⟨z, hz, hzd⟩ := h j
    exact ⟨z, hz, hzd⟩

end ThreeIM
