module

public import RequestProject.ThreeIM.RationalRotation
public import RequestProject.ThreeIM.RationalReality

/-!
# Descent to simple endpoint poles (Lemma 9.25)

In the balanced endpoint configuration of Lemmas 9.5–9.6 with a defect, the numerators and
denominators of `R, S` are invariant under `t ↦ e^{2πi/ρ} t` (`OppositeData.num_denom_rotation`).
Hence `R(t) = r(t^ρ)`, `S(t) = s(t^ρ)` for rational `r, s`, and `r, s` form again a normalized
pair on `ℂ*`, in the balanced endpoint configuration with endpoint pole order `1` and
coefficient `γ/ρ`, and with a retained defect.
-/

@[expose] public section

open Filter Set Topology Polynomial

namespace ThreeIM

/-! ### Polynomial and rational descent -/

/-- A polynomial invariant under `t ↦ e^{2πi/ρ} t` is a polynomial in `t^ρ`. -/
lemma exists_comp_X_pow_of_rot {ρ : ℕ} (hρ : 0 < ρ) {P : ℂ[X]}
    (h : P.comp (C (zetaC ρ) * X) = P) : ∃ p : ℂ[X], P = p.comp (X ^ ρ) := by
  have hζ := zetaC_isPrimitiveRoot hρ
  have key : ∀ k : ℕ, P.comp (C (zetaC ρ ^ k) * X) = P := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : (C (zetaC ρ) * X : ℂ[X]).comp (C (zetaC ρ ^ k) * X) =
          C (zetaC ρ ^ (k + 1)) * X := by
        simp only [mul_comp, C_comp, X_comp, pow_succ, C_mul]; ring
      rw [← e, ← comp_assoc, h, ih]
  haveI : NeZero ρ := ⟨hρ.ne'⟩
  refine polynomial_descent hρ fun ξ hξ => ?_
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hξ
  exact key i

/-- Coprimality descends along `t ↦ t^ρ`. -/
lemma isCoprime_of_comp_X_pow {ρ : ℕ} (hρ : 0 < ρ) {p q : ℂ[X]}
    (h : IsCoprime (p.comp (X ^ ρ)) (q.comp (X ^ ρ))) : IsCoprime p q := by
  rw [← isRelPrime_iff_isCoprime] at h ⊢
  intro d hp hq
  have hu := h (map_dvd (compRingHom (X ^ ρ)) hp) (map_dvd (compRingHom (X ^ ρ)) hq)
  simp only [coe_compRingHom_apply] at hu
  have h0 : d.comp (X ^ ρ) ≠ 0 := hu.ne_zero
  have hd0 : d ≠ 0 := by rintro rfl; simp at h0
  have := natDegree_eq_zero_of_isUnit hu
  rw [natDegree_comp, natDegree_X_pow, mul_eq_zero] at this
  rcases this with h1 | h1
  · rw [eq_C_of_natDegree_eq_zero h1] at hd0 ⊢
    exact isUnit_C.2 (Ne.isUnit (by simpa using hd0))
  · omega

/-- **Lemma 9.24** for the reduced representation: if the numerator and denominator of `R` are
invariant under `t ↦ e^{2πi/ρ} t`, then `R(t) = r(t^ρ)` for a rational `r` (with equality of the
evaluations at every point, including poles), and `r` is finite at `0` iff `R` is. -/
lemma ratFunc_descent_eval {ρ : ℕ} (hρ : 0 < ρ) {R : RatFunc ℂ}
    (hn : R.num.comp (C (zetaC ρ) * X) = R.num) (hd : R.denom.comp (C (zetaC ρ) * X) = R.denom) :
    ∃ r : RatFunc ℂ, (∀ t, ratEval R t = ratEval r (t ^ ρ)) ∧
      (r.denom.eval 0 ≠ 0 ↔ R.denom.eval 0 ≠ 0) := by
  obtain ⟨p, hp⟩ := exists_comp_X_pow_of_rot hρ hn
  obtain ⟨q, hq⟩ := exists_comp_X_pow_of_rot hρ hd
  have hq0 : q ≠ 0 := by
    rintro rfl; rw [zero_comp] at hq; exact R.denom_ne_zero hq
  have hcop : IsCoprime p q := by
    have := RatFunc.isCoprime_num_denom R
    rw [hp, hq] at this
    exact isCoprime_of_comp_X_pow hρ this
  refine ⟨algebraMap ℂ[X] (RatFunc ℂ) p / algebraMap ℂ[X] (RatFunc ℂ) q, fun t => ?_, ?_⟩
  · rw [ratEval_div_of_coprime hq0 hcop, ratEval_eq, hp, hq, eval_comp, eval_comp]; simp
  · obtain ⟨u, hu, -, hd'⟩ := num_denom_div_of_coprime hq0 hcop
    rw [hd', hq]; simp [eval_comp, hu, zero_pow hρ.ne']

/-! ### Pullback by `t ↦ t^ρ` -/

lemma tendsto_pow_nhdsNE {ρ : ℕ} (hρ : 0 < ρ) :
    Tendsto (fun t : ℂ => t ^ ρ) (𝓝[≠] 0) (𝓝[≠] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have := ((continuous_pow ρ).tendsto (0 : ℂ))
    simpa [zero_pow hρ.ne'] using this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact pow_ne_zero _ ht

lemma deriv_comp_pow {f : ℂ → ℂ} {ρ : ℕ} {t : ℂ} (hf : DifferentiableAt ℂ f (t ^ ρ)) :
    deriv (fun x => f (x ^ ρ)) t = deriv f (t ^ ρ) * (ρ * t ^ (ρ - 1)) := by
  simpa only [Function.comp_def] using!
    (hf.hasDerivAt.comp t (hasDerivAt_pow ρ t)).deriv

lemma mul_pow_aux {ρ : ℕ} (t A B D : ℂ) :
    t * (A * (B * (ρ * t ^ (ρ - 1))) / D) = ρ * (t ^ ρ * (A * B / D)) := by
  rcases Nat.eq_zero_or_pos ρ with h | h
  · subst h; simp
  · have : t ^ ρ = t * t ^ (ρ - 1) := by rw [← pow_succ']; congr 1; omega
    rw [this]; ring

/-- The meromorphic order at `0` is multiplied by `ρ` under the pullback by `t ↦ t^ρ`. -/
lemma meromorphicOrderAt_comp_pow {F : ℂ → ℂ} (hF : MeromorphicAt F 0) {ρ : ℕ} (hρ : 0 < ρ)
    {n : ℤ} (h : meromorphicOrderAt F 0 = n) :
    meromorphicOrderAt (fun t => F (t ^ ρ)) 0 = ((ρ * n : ℤ) : WithTop ℤ) := by
  have hpow : Tendsto (fun t : ℂ => t ^ ρ) (𝓝[≠] 0) (𝓝[≠] 0) := tendsto_pow_nhdsNE hρ
  have hpa : AnalyticAt ℂ (fun t : ℂ => t ^ ρ) 0 := (differentiable_pow ρ).analyticAt 0
  have h00 : (fun t : ℂ => t ^ ρ) 0 = 0 := by simp [zero_pow hρ.ne']
  obtain ⟨g, hg, hg0, hev⟩ := (meromorphicOrderAt_eq_int_iff hF).1 h
  have hm : MeromorphicAt (fun t => F (t ^ ρ)) 0 :=
    MeromorphicAt.comp_analyticAt (f := F) (g := fun t : ℂ => t ^ ρ) (x := 0)
      (by simpa only [zero_pow hρ.ne'] using hF) hpa
  rw [meromorphicOrderAt_eq_int_iff hm]
  refine ⟨fun t => g (t ^ ρ), ?_, by simpa [zero_pow hρ.ne'] using hg0, ?_⟩
  · have : AnalyticAt ℂ g ((fun t : ℂ => t ^ ρ) 0) := by rw [h00]; exact hg
    exact AnalyticAt.comp (f := fun t : ℂ => t ^ ρ) this hpa
  · filter_upwards [hpow.eventually hev, self_mem_nhdsWithin] with t ht ht0
    simp only [sub_zero, smul_eq_mul] at ht ⊢
    rw [ht, ← zpow_natCast, ← zpow_mul]

lemma meromorphicOrderAt_comp_pow_top {F : ℂ → ℂ} {ρ : ℕ} (hρ : 0 < ρ)
    (h : meromorphicOrderAt F 0 = ⊤) : meromorphicOrderAt (fun t => F (t ^ ρ)) 0 = ⊤ := by
  rw [meromorphicOrderAt_eq_top_iff] at h ⊢
  exact (tendsto_pow_nhdsNE hρ).eventually h

/-- If `F(t^ρ)` has order `-ρ` at `0`, then `F` has order `-1` at `0`. -/
lemma meromorphicOrderAt_eq_neg_one_of_comp_pow {F : ℂ → ℂ} (hF : MeromorphicAt F 0) {ρ : ℕ}
    (hρ : 0 < ρ) (h : meromorphicOrderAt (fun t => F (t ^ ρ)) 0 = ((-(ρ : ℤ) : ℤ) : WithTop ℤ)) :
    meromorphicOrderAt F 0 = ((-1 : ℤ) : WithTop ℤ) := by
  rcases hn : meromorphicOrderAt F 0 with _ | n
  · rw [meromorphicOrderAt_comp_pow_top hρ hn] at h; exact absurd h WithTop.top_ne_coe
  · rw [meromorphicOrderAt_comp_pow hF hρ hn] at h
    have h' : (ρ : ℤ) * n = -(ρ : ℤ) := by exact_mod_cast h
    have : n = -1 := by
      have hρ' : (ρ : ℤ) ≠ 0 := by exact_mod_cast hρ.ne'
      exact mul_left_cancel₀ hρ' (by rw [h']; ring)
    rw [this]; rfl

/-- Limits at `∞` descend along `t ↦ t^ρ`. -/
lemma tendsto_cocompact_of_comp_pow {F : ℂ → ℂ} {ρ : ℕ} (hρ : 0 < ρ) {L : Filter ℂ}
    (h : Tendsto (fun t => F (t ^ ρ)) (cocompact ℂ) L) : Tendsto F (cocompact ℂ) L := by
  intro s hs
  have h1 := h hs
  rw [mem_map, mem_cocompact] at h1 ⊢
  obtain ⟨K, hK, hKs⟩ := h1
  obtain ⟨M, hM⟩ := (isBounded_iff_forall_norm_le.1 hK.isBounded)
  refine ⟨Metric.closedBall 0 (max M 0 ^ ρ), isCompact_closedBall _ _, fun x hx => ?_⟩
  simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hx
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq x hρ
  have htK : t ∉ K := by
    intro htK
    have h2 := hM t htK
    have : ‖x‖ ≤ max M 0 ^ ρ := by
      rw [← ht, norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (h2.trans (le_max_left _ _)) ρ
    linarith
  have := hKs htK
  simp only [Set.mem_preimage] at this
  rwa [ht] at this

/-- The auxiliary functions under the pullback by `t ↦ t^ρ`. -/
lemma mul_auxU_comp_pow {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {ρ : ℕ} {t : ℂ}
    (hf : DifferentiableAt ℂ f (t ^ ρ)) :
    t * auxU a (fun x => f (x ^ ρ)) (fun x => g (x ^ ρ)) t =
      ρ * (t ^ ρ * auxU a f g (t ^ ρ)) := by
  simp only [auxU]
  rw [deriv_comp_pow hf]
  exact mul_pow_aux _ _ _ _

lemma mul_auxV_comp_pow {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {ρ : ℕ} {t : ℂ}
    (hg : DifferentiableAt ℂ g (t ^ ρ)) :
    t * auxV a (fun x => f (x ^ ρ)) (fun x => g (x ^ ρ)) t =
      ρ * (t ^ ρ * auxV a f g (t ^ ρ)) := by
  simp only [auxV]
  rw [deriv_comp_pow hg]
  exact mul_pow_aux _ _ _ _

/-- A cofinite property of `t` transfers to `x = t^ρ`: off a finite set, every `x` has a
`ρ`-th root outside a given finite set. -/
lemma eventually_cofinite_exists_root {ρ : ℕ} (hρ : 0 < ρ) {P : ℂ → Prop}
    (h : ∀ᶠ t in cofinite, P t) : ∀ᶠ x in cofinite, ∃ t, t ^ ρ = x ∧ P t := by
  have hB : {t | ¬ P t}.Finite := h
  refine ((hB.image fun t => t ^ ρ).subset ?_ : {x | ¬ ∃ t, t ^ ρ = x ∧ P t}.Finite)
  intro x hx
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq x hρ
  exact ⟨t, fun hP => hx ⟨t, ht, hP⟩, ht⟩

lemma differentiableAt_ratEval {r : RatFunc ℂ} {x : ℂ} (hx : r.denom.eval x ≠ 0) :
    DifferentiableAt ℂ (ratEval r) x := by
  rw [funext (ratEval_eq r)]
  exact (r.num.differentiableAt).div (r.denom.differentiableAt) hx

/-- **Lemma 9.25** (descent to simple endpoint poles).  In the balanced endpoint configuration
with a defect, `R(t) = r(t^ρ)` and `S(t) = s(t^ρ)` where `r, s` form a normalized pair on `ℂ*`
in the balanced endpoint configuration with endpoint pole order `1` and coefficient `γ/ρ`. -/
theorem OppositeData.descent {a : Fin 3 → ℂ} {R S : RatFunc ℂ} {j : Fin 3} {ρ : ℕ}
    {γ : ℂ} (hpair : NormalizedPair {0}ᶜ (ratEval R) (ratEval S) a)
    (hd : OppositeData a R S j j ρ γ γ)
    (hdef : ∃ k, ∃ z ∈ ({0}ᶜ : Set ℂ), IsDefect (ratEval R) (ratEval S) (a k : Sphere) z) :
    ∃ r s : RatFunc ℂ, (∀ t, ratEval R t = ratEval r (t ^ ρ)) ∧
      (∀ t, ratEval S t = ratEval s (t ^ ρ)) ∧
      NormalizedPair {0}ᶜ (ratEval r) (ratEval s) a ∧
      OppositeData a r s j j 1 (γ / ρ) (γ / ρ) ∧
      ∃ k, ∃ z ∈ ({0}ᶜ : Set ℂ), IsDefect (ratEval r) (ratEval s) (a k : Sphere) z := by
  have hρ := hd.rho_pos
  have hρC : (ρ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hρ.ne'
  obtain ⟨h1, h2, h3, h4⟩ := hd.num_denom_rotation hpair hdef
  obtain ⟨r, hr, hr0⟩ := ratFunc_descent_eval hρ h1 h2
  obtain ⟨s, hs, -⟩ := ratFunc_descent_eval hρ h3 h4
  have hRf : ratEval R = ratEval r ∘ fun t => t ^ ρ := funext hr
  have hSf : ratEval S = ratEval s ∘ fun t => t ^ ρ := funext hs
  have hpa : ∀ z : ℂ, AnalyticAt ℂ (fun t : ℂ => t ^ ρ) z := fun z =>
    (differentiable_pow ρ).analyticAt z
  have hpd : ∀ z : ℂ, z ≠ 0 → deriv (fun t : ℂ => t ^ ρ) z ≠ 0 := by
    intro z hz
    simp only [deriv_pow_field, ne_eq, mul_eq_zero, Nat.cast_eq_zero, pow_eq_zero_iff', not_or]
    exact ⟨hρ.ne', fun h => hz h.1⟩
  have hnc : ∀ (F : RatFunc ℂ) (G : RatFunc ℂ), IsNonconstMeroOn (ratEval G) {0}ᶜ →
      ratEval G = ratEval F ∘ (fun t => t ^ ρ) → ∀ c : ℂ, F ≠ RatFunc.C c := by
    intro F G hG hGF c hc
    apply hG.2 1 (by norm_num) c
    have : (fun w => ratEval G w - c) = fun _ => (0 : ℂ) := by
      funext w
      rw [hGF, hc]
      simp [ratEval]
    rw [this, meromorphicOrderAt_eq_top_iff]
    exact Eventually.of_forall fun _ => rfl
  have hrnc := hnc r R hpair.nonconst_f hRf
  have hsnc := hnc s S hpair.nonconst_g hSf
  have hpair' : NormalizedPair {0}ᶜ (ratEval r) (ratEval s) a := by
    refine ⟨isNonconstMeroOn_ratEval hrnc _, isNonconstMeroOn_ratEval hsnc _, fun z hz => ?_,
      hpair.injective, fun i => ?_, ?_⟩
    · obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq z hρ
      have ht0 : t ≠ 0 := by rintro rfl; exact hz (by rw [← ht, zero_pow hρ.ne']; rfl)
      have := hpair.distinct t ht0
      have e : (fun w => ratEval R w - ratEval S w) =
          (fun x => ratEval r x - ratEval s x) ∘ fun t => t ^ ρ := by
        rw [hRf, hSf]; rfl
      rw [e, meromorphicOrderAt_comp_of_deriv_ne_zero (hpa t) (hpd t ht0), ht] at this
      exact this
    · rw [sharesIMOn_punctured_iff_comp_pow hρ, ← hRf, ← hSf]; exact hpair.im i
    · rw [sharesCMOn_punctured_iff_comp_pow hρ, ← hRf, ← hSf]; exact hpair.cm_top
  refine ⟨r, s, hr, hs, hpair', ?_, ?_⟩
  · have hinvf : ∀ (F : RatFunc ℂ) (G : RatFunc ℂ), ratEval G = ratEval F ∘ (fun t => t ^ ρ) →
        (fun t => (fun x => ratEval F x⁻¹) (t ^ ρ)) = fun t => ratEval G t⁻¹ := by
      intro F G hGF
      funext t
      rw [hGF]; simp [inv_pow]
    have hmer : ∀ F : RatFunc ℂ, MeromorphicAt (fun x => ratEval F x⁻¹) 0 := fun F =>
      (meromorphicAt_ratInvFun F).congr (by
        filter_upwards [self_mem_nhdsWithin] with x hx
        exact ratInvFun_eq F hx)
    have hdenom : ∀ F : RatFunc ℂ, ∀ᶠ x in cofinite, F.denom.eval x ≠ 0 := fun F =>
      IsRatFun.eventually_ne F.denom_ne_zero
    refine ⟨one_pos, div_ne_zero hd.alpha_ne hρC, div_ne_zero hd.alpha_ne hρC,
      hr0.2 hd.denom_zero, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := hr 0
      rw [zero_pow hρ.ne'] at this
      rw [← this]; exact hd.value_zero
    · have := meromorphicOrderAt_eq_neg_one_of_comp_pow (meromorphicAt_ratEval s 0) hρ
        (by have e := hd.order_zero; rw [hSf] at e; exact e)
      rw [this]; rfl
    · have := meromorphicOrderAt_eq_neg_one_of_comp_pow (hmer r) hρ
        (by rw [hinvf r R hRf]; exact hd.order_infty)
      rw [this]; rfl
    · exact tendsto_cocompact_of_comp_pow hρ (by
        have e := hd.tendsto_infty; rw [hSf] at e; exact e)
    · filter_upwards [eventually_cofinite_exists_root hρ hd.aux_U, hdenom r]
        with x ⟨t, htx, ht⟩ hx
      subst htx
      have e := mul_auxU_comp_pow (a := a) (g := ratEval s) (ρ := ρ) (t := t)
        (differentiableAt_ratEval hx)
      have e1 : (fun x => ratEval r (x ^ ρ)) = ratEval R := hRf.symm
      have e2 : (fun x => ratEval s (x ^ ρ)) = ratEval S := hSf.symm
      rw [e1, e2, ht] at e
      have hzp : (t ^ ρ) ^ (-((1 : ℕ) : ℤ)) = t ^ (-(ρ : ℤ)) := by
        rw [← zpow_natCast, ← zpow_mul]; congr 1; push_cast; ring
      rw [hzp]
      field_simp
      linear_combination -e
    · filter_upwards [eventually_cofinite_exists_root hρ hd.aux_V, hdenom s]
        with x ⟨t, htx, ht⟩ hx
      subst htx
      have e := mul_auxV_comp_pow (a := a) (f := ratEval r) (ρ := ρ) (t := t)
        (differentiableAt_ratEval hx)
      have e1 : (fun x => ratEval r (x ^ ρ)) = ratEval R := hRf.symm
      have e2 : (fun x => ratEval s (x ^ ρ)) = ratEval S := hSf.symm
      rw [e1, e2, ht] at e
      have hzp : (t ^ ρ) ^ ((1 : ℕ) : ℤ) = t ^ (ρ : ℤ) := by
        rw [← zpow_natCast, ← zpow_mul]; congr 1; push_cast; ring
      rw [hzp]
      field_simp
      linear_combination -e
  · obtain ⟨k, z, hz, hdz⟩ := hdef
    have hz0 : z ≠ 0 := hz
    refine ⟨k, z ^ ρ, pow_ne_zero _ hz0, ?_⟩
    have e : ∀ (F : RatFunc ℂ) (G : RatFunc ℂ), ratEval G = ratEval F ∘ (fun t => t ^ ρ) →
        ∀ b, mult (ratEval G) b z = mult (ratEval F) b (z ^ ρ) := by
      intro F G hGF b
      rw [hGF, mult_comp_of_deriv_ne_zero (hpa z) (hpd z hz0)]
    obtain ⟨d1, d2, d3⟩ := hdz
    rw [e r R hRf] at d1 d3
    rw [e s S hSf] at d2 d3
    exact ⟨d1, d2, d3⟩

end ThreeIM
