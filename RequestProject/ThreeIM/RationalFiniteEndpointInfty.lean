module

public import RequestProject.ThreeIM.RationalFiniteEndpoint

/-!
# The finite endpoint case at `∞` (Lemma 9.4, second endpoint)

We treat the endpoint `∞` by the change of variable `s = 1/t`.  For `R = p/q` of degree
`e = max (deg p) (deg q)` the function `s ↦ R(1/s)` is the quotient of the reflected
polynomials `reflect e p` and `reflect e q`; it is analytic at `s = 0` when `R` has a finite
limit at `∞`.  The identity `s · U_{F,G}(s) = -(s⁻¹ · U_{R,S}(s⁻¹))` for `F(s) = R(1/s)`,
`G(s) = S(1/s)` and the order computation of Lemma 9.4 at the endpoint `0` then show that the
monomials of Lemma 9.3 are constants, and the counting core finishes the proof.
-/

@[expose] public section

open Filter Set Topology Polynomial

namespace ThreeIM

lemma tendsto_inv_cocompact : Tendsto (fun s : ℂ => s⁻¹) (𝓝[≠] 0) (cocompact ℂ) :=
  Metric.cobounded_eq_cocompact (α := ℂ) ▸ tendsto_inv₀_nhdsNE_zero

lemma eval_reflect_of_ne_zero {p : ℂ[X]} {N : ℕ} (hp : p.natDegree ≤ N) {s : ℂ} (hs : s ≠ 0) :
    (reflect N p).eval s = s ^ N * p.eval s⁻¹ := by
  letI : Invertible s⁻¹ := invertibleOfNonzero (inv_ne_zero hs)
  have h := eval₂_reflect_mul_pow (RingHom.id ℂ) s⁻¹ N p hp
  rw [invOf_eq_inv, inv_inv] at h
  have e : ∀ (x : ℂ) (q : ℂ[X]), eval₂ (RingHom.id ℂ) x q = q.eval x := fun _ _ => rfl
  rw [e, e] at h
  rw [← h, mul_comm (s ^ N), mul_assoc, ← mul_pow, inv_mul_cancel₀ hs, one_pow, mul_one]

lemma eval_reflect_zero (p : ℂ[X]) (N : ℕ) : (reflect N p).eval 0 = p.coeff N := by
  rw [← coeff_zero_eq_eval_zero, coeff_reflect, revAt_le (Nat.zero_le N), Nat.sub_zero]

/-- The common degree `max (deg num) (deg denom)` of a rational function. -/
noncomputable def ratDeg (R : RatFunc ℂ) : ℕ := max R.num.natDegree R.denom.natDegree

/-- The rational function `s ↦ R(1/s)`, as the quotient of the reflected numerator and
denominator. -/
noncomputable def ratInvFun (R : RatFunc ℂ) : ℂ → ℂ :=
  fun s => (reflect (ratDeg R) R.num).eval s / (reflect (ratDeg R) R.denom).eval s

lemma ratInvFun_eq (R : RatFunc ℂ) {s : ℂ} (hs : s ≠ 0) : ratInvFun R s = ratEval R s⁻¹ := by
  rw [ratInvFun, eval_reflect_of_ne_zero (N := ratDeg R) (le_max_left _ _) hs,
    eval_reflect_of_ne_zero (N := ratDeg R) (le_max_right _ _) hs, ratEval_eq,
    mul_div_mul_left _ _ (pow_ne_zero _ hs)]

lemma reflect_denom_ne_zero (R : RatFunc ℂ) : reflect (ratDeg R) R.denom ≠ 0 :=
  fun h => R.denom_ne_zero (reflect_eq_zero_iff.1 h)

/-- If `R` has a finite limit at `∞`, the reflected denominator does not vanish at `0`, and
`s ↦ R(1/s)` is analytic at `0` with value the limit. -/
lemma ratInvFun_of_tendsto {R : RatFunc ℂ} {c : ℂ}
    (hR : Tendsto (ratEval R) (cocompact ℂ) (𝓝 c)) :
    (reflect (ratDeg R) R.denom).eval 0 ≠ 0 ∧ AnalyticAt ℂ (ratInvFun R) 0 ∧
      ratInvFun R 0 = c := by
  set P := reflect (ratDeg R) R.num
  set Q := reflect (ratDeg R) R.denom
  have hlim : Tendsto (ratInvFun R) (𝓝[≠] 0) (𝓝 c) := by
    refine (hR.comp tendsto_inv_cocompact).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (ratInvFun_eq R hs).symm
  have hQ0 : Q.eval 0 ≠ 0 := by
    intro h0
    have hP0 : P.eval 0 ≠ 0 := by
      simp only [P, Q, eval_reflect_zero, ratDeg] at h0 ⊢
      rcases le_or_gt R.num.natDegree R.denom.natDegree with h | h
      · exfalso
        rw [max_eq_right h] at h0
        exact (leadingCoeff_ne_zero.2 R.denom_ne_zero) h0
      · have hn : R.num ≠ 0 := by
          intro hn
          rw [hn, natDegree_zero] at h
          exact Nat.not_lt_zero _ h
        rw [max_eq_left h.le]
        exact leadingCoeff_ne_zero.2 hn
    have h1 : Tendsto (fun s => ratInvFun R s * Q.eval s) (𝓝[≠] 0) (𝓝 (c * Q.eval 0)) :=
      hlim.mul ((Q.continuous.tendsto 0).mono_left nhdsWithin_le_nhds)
    have h2 : Tendsto (fun s => ratInvFun R s * Q.eval s) (𝓝[≠] 0) (𝓝 (P.eval 0)) := by
      refine ((P.continuous.tendsto 0).mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [polynomial_eventually_ne_zero (reflect_denom_ne_zero R) 0] with s hs
      simp only [ratInvFun]
      exact (div_mul_cancel₀ _ hs).symm
    rw [h0, mul_zero] at h1
    exact hP0 (tendsto_nhds_unique h2 h1)
  have han : AnalyticAt ℂ (ratInvFun R) 0 :=
    (P.differentiable.analyticAt 0).div (Q.differentiable.analyticAt 0) hQ0
  refine ⟨hQ0, han, ?_⟩
  exact tendsto_nhds_unique (han.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hlim

/-- If the reflected denominator does not vanish at `0`, then `s ↦ R(1/s) - c` has finite order
at `0` for every `c` (for nonconstant `R`). -/
lemma order_ratInvFun_sub_ne_top {R : RatFunc ℂ} {c : ℂ} (hRc : R ≠ RatFunc.C c)
    (hQ0 : (reflect (ratDeg R) R.denom).eval 0 ≠ 0) :
    meromorphicOrderAt (fun w => ratInvFun R w - c) 0 ≠ ⊤ := by
  set Q := reflect (ratDeg R) R.denom
  set N := reflect (ratDeg R) R.num - Polynomial.C c * Q
  have hN : N ≠ 0 := by
    have : N = reflect (ratDeg R) (R.num - Polynomial.C c * R.denom) := by
      rw [reflect_sub, reflect_C_mul]
    rw [this]
    exact fun h => num_sub_ne_zero hRc (reflect_eq_zero_iff.1 h)
  have heq : (fun w => ratInvFun R w - c) =ᶠ[𝓝[≠] 0] fun w => N.eval w / Q.eval w := by
    filter_upwards [polynomial_eventually_ne_zero (reflect_denom_ne_zero R) 0] with w hw
    simp only [ratInvFun, N, Q, eval_sub, eval_mul, eval_C]
    field_simp
  rw [meromorphicOrderAt_congr heq, order_polyQuot_of_denom_ne_zero hN hQ0]
  exact WithTop.coe_ne_top

/-- Near `s = 0`, `s · U_{F,G}(s) = -(s⁻¹ · U_{R,S}(s⁻¹))` for `F(s) = R(1/s)`, `G(s) = S(1/s)`. -/
lemma mul_auxU_ratInvFun (a : Fin 3 → ℂ) (R S : RatFunc ℂ) :
    ∀ᶠ s in 𝓝[≠] 0, s * auxU a (ratInvFun R) (ratInvFun S) s =
      -(s⁻¹ * auxU a (ratEval R) (ratEval S) s⁻¹) := by
  have hfin : ∀ᶠ x in cocompact ℂ, R.denom.eval x ≠ 0 :=
    (R.denom.finite_setOf_isRoot R.denom_ne_zero).isCompact.compl_mem_cocompact
  filter_upwards [self_mem_nhdsWithin, tendsto_inv_cocompact.eventually hfin] with s hs hd
  have hs' : s ∈ ({0}ᶜ : Set ℂ) := hs
  have hloc : ratInvFun R =ᶠ[𝓝 s] ratEval R ∘ fun x => x⁻¹ := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hs'] with x hx
    exact ratInvFun_eq R hx
  have hdiff : DifferentiableAt ℂ (ratEval R) s⁻¹ := by
    rw [funext (ratEval_eq R)]
    exact (R.num.differentiable _).div (R.denom.differentiable _) hd
  have hderiv : deriv (ratInvFun R) s = deriv (ratEval R) s⁻¹ * (-(s ^ 2)⁻¹) := by
    rw [hloc.deriv_eq, deriv_comp s hdiff (differentiableAt_inv hs), deriv_inv]
  simp only [auxU, hderiv, ratInvFun_eq R hs, ratInvFun_eq S hs]
  rcases eq_or_ne (cubicP a (ratEval R s⁻¹)) 0 with h0 | h0
  · simp [h0]
  · field_simp

/-- If `t · H(t) = α t^u` off a finite set, then `-(s⁻¹ · H(s⁻¹)) = -α s^{-u}` near `s = 0`. -/
lemma inv_monomial_eventually {H : ℂ → ℂ} {α : ℂ} {u : ℤ}
    (hU : ∀ᶠ t in cofinite, t * H t = α * t ^ u) :
    (fun s => -(s⁻¹ * H s⁻¹)) =ᶠ[𝓝[≠] 0] fun s => (-α) * s ^ (-u) := by
  filter_upwards [tendsto_inv_cocompact.eventually (hU.filter_mono cocompact_le_cofinite)]
    with s hs
  rw [hs, inv_zpow', neg_mul]

/-- **Lemma 9.4 at `∞`, exponent step.**  If `R, S` have distinct finite limits `a j`, `c` at
`∞` and `t · U(t) = α t^u` off a finite set (Lemma 9.3), then `u = 0`. -/
lemma exponent_eq_zero_of_tendsto {R S : RatFunc ℂ} {a : Fin 3 → ℂ} (ha : Function.Injective a)
    (hRnc : ∀ c : ℂ, R ≠ RatFunc.C c) {j : Fin 3} {c : ℂ} (hjc : a j ≠ c)
    (hR : Tendsto (ratEval R) (cocompact ℂ) (𝓝 (a j)))
    (hS : Tendsto (ratEval S) (cocompact ℂ) (𝓝 c)) {α : ℂ} (hα : α ≠ 0) {u : ℤ}
    (hU : ∀ᶠ t in cofinite, t * auxU a (ratEval R) (ratEval S) t = α * t ^ u) : u = 0 := by
  obtain ⟨hQ0, hFa, hF0⟩ := ratInvFun_of_tendsto hR
  obtain ⟨-, hGa, hG0⟩ := ratInvFun_of_tendsto hS
  have hne := order_ratInvFun_sub_ne_top (hRnc (a j)) hQ0
  have h1 := order_mul_auxU_endpoint ha hFa hGa hF0 (by rw [hF0, hG0]; exact hjc) hne
  rw [meromorphicOrderAt_congr (mul_auxU_ratInvFun a R S),
    meromorphicOrderAt_congr (inv_monomial_eventually hU), order_monomial_zero (neg_ne_zero.2 hα)]
    at h1
  have : -u = 0 := by exact_mod_cast h1
  omega

/-- **Lemma 9.4** (finite endpoint case), endpoint `∞`, assuming the conclusions of Lemma 9.2.
Let `R, S ∈ ℂ(t)` form a normalized pair on `ℂ*` for the finite values `a 0, a 1, a 2`, with
coincidence multiplicity one on `ℂ*` and no other coincidences or critical points there, of the
same degree, and with distinct finite limits `R(∞) = a j`, `S(∞) = a k` at `∞`.  Then `R, S`
share all four values `a 0, a 1, a 2, ∞` CM on `ℂ*`. -/
theorem rational_finite_endpoint_infty {R S : RatFunc ℂ} {a : Fin 3 → ℂ}
    (hpair : NormalizedPair {0}ᶜ (ratEval R) (ratEval S) a)
    (hco : ∀ t : ℂ, t ≠ 0 → CoincidenceSimpleAt a (ratEval R) (ratEval S) t)
    (hdeg : max R.num.natDegree R.denom.natDegree = max S.num.natDegree S.denom.natDegree)
    {j k : Fin 3} (hjk : j ≠ k)
    (hRj : Tendsto (ratEval R) (cocompact ℂ) (𝓝 (a j)))
    (hSk : Tendsto (ratEval S) (cocompact ℂ) (𝓝 (a k))) :
    ∀ i : Fin 4, SharesCMOn {0}ᶜ (ratEval R) (ratEval S)
      (![(a 0 : Sphere), (a 1 : Sphere), (a 2 : Sphere), ⊤] i) := by
  have hRnc := ne_C_of_nonconst hpair.nonconst_f
  have hSnc := ne_C_of_nonconst hpair.nonconst_g
  obtain ⟨α, β, hα, hβ, u, v, hU, hV, -⟩ := rational_monomials hpair hco
  have hu : u = 0 :=
    exponent_eq_zero_of_tendsto hpair.injective hRnc (hpair.injective.ne hjk) hRj hSk hα hU
  have hV' : ∀ᶠ t in cofinite, t * auxU a (ratEval S) (ratEval R) t = (-β) * t ^ v := by
    filter_upwards [hV] with t ht
    rw [neg_mul, ← ht]
    simp only [auxV, auxU]
    ring
  have hv : v = 0 :=
    exponent_eq_zero_of_tendsto hpair.injective hSnc (hpair.injective.ne hjk.symm) hSk hRj
      (neg_ne_zero.2 hβ) hV'
  subst hu hv
  exact cm_of_same_exponent hpair hdeg hα hβ hU hV

end ThreeIM
