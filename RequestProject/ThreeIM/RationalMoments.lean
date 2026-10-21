module

public import RequestProject.ThreeIM.RationalRescale
public import RequestProject.ThreeIM.RationalCritical

/-!
# Fiber moments at the endpoint `∞` (Lemma 9.9, first half) and Lemma 9.6

In the endpoint configuration of Lemma 9.5 (`R(0) = a j`, `R` has a pole of order `ρ` at `∞`,
`U = α t^{-ρ}`), the logarithmic derivative of `(R - v)/(R - w)` satisfies
`t^{ρ+1} (R'/(R - v) - R'/(R - w)) → (v - w) α` as `t → ∞`.  Writing that logarithmic
derivative as `Σ_{R(z) = v} 1/(t - z) - Σ_{R(z) = w} 1/(t - z)` and expanding at `∞` gives the
moment identities

* `M_{v,ℓ} = M_{w,ℓ}` for `ℓ < ρ` and `M_{v,ρ} - M_{w,ρ} = (v - w) α`,

where `M_{v,ℓ} = Σ_{R(t) = v} m(t) t^ℓ` (`OppositeData.fiberMoments`).  This is the residue
computation of the paper (the total residue of `t^ρ d log((R - v)/(R - w))` on the sphere)
written as a coefficient comparison.

With balanced constants (`α = β = γ`), the ratio identity `t^{2ρ} m = n` at finite common
points (`ratio_of_balanced`) makes every `t^ρ` real, hence every fiber moment `M_{a i, ρ}` real,
and so `(a i - a j) γ` real.  Combined with the endpoint coefficient identities this proves
Lemma 9.6 (`OppositeData.residue_normalization`, `rational_residue_normalization`).
-/

@[expose] public section

open Filter Set Topology Polynomial

namespace ThreeIM

/-- The `k`-th power sum of a multiset of complex numbers. -/
noncomputable def powerSum (M : Multiset ℂ) (k : ℕ) : ℂ := (M.map fun z => z ^ k).sum

/-- A polynomial with a finite limit at `∞` is constant. -/
lemma polynomial_eq_C_of_tendsto {Q : ℂ[X]} {L : ℂ}
    (h : Tendsto (fun t => Q.eval t) (cocompact ℂ) (𝓝 L)) : Q = C L := by
  by_cases hdeg : 0 < Q.degree
  · exfalso
    have h1 := Q.tendsto_norm_atTop hdeg (l := cocompact ℂ) (z := id) tendsto_norm_cocompact_atTop
    have h2 := h.norm
    exact not_tendsto_nhds_of_tendsto_atTop h1 _ h2
  · push_neg at hdeg
    rw [eq_C_of_degree_le_zero hdeg] at h ⊢
    simp only [eval_C] at h
    rw [tendsto_const_nhds_iff.1 h]

lemma pow_succ_div_sub (ρ : ℕ) {t z : ℂ} (h : t ≠ z) :
    t ^ (ρ + 1) / (t - z) =
      ∑ i ∈ Finset.range (ρ + 1), z ^ i * t ^ (ρ - i) + z ^ (ρ + 1) / (t - z) := by
  have hz : t - z ≠ 0 := sub_ne_zero.2 h
  rw [div_eq_iff hz, add_mul, div_mul_cancel₀ _ hz, Finset.sum_mul]
  have : ∀ i ∈ Finset.range (ρ + 1), z ^ i * t ^ (ρ - i) * (t - z) =
      z ^ i * t ^ (ρ + 1 - i) - z ^ (i + 1) * t ^ (ρ + 1 - (i + 1)) := by
    intro i hi
    have hi' : i ≤ ρ := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [show ρ + 1 - i = (ρ - i) + 1 by omega, show ρ + 1 - (i + 1) = ρ - i by omega]
    ring
  rw [Finset.sum_congr rfl this, Finset.sum_range_sub' (fun i => z ^ i * t ^ (ρ + 1 - i))]
  simp

lemma mul_sum_inv_sub_eq (M : Multiset ℂ) (ρ : ℕ) {t : ℂ} (ht : t ∉ M) :
    t ^ (ρ + 1) * (M.map fun z => 1 / (t - z)).sum =
      ∑ i ∈ Finset.range (ρ + 1), powerSum M i * t ^ (ρ - i) +
        (M.map fun z => z ^ (ρ + 1) / (t - z)).sum := by
  rw [← Multiset.sum_map_mul_left]
  have : ∀ z ∈ M, t ^ (ρ + 1) * (1 / (t - z)) =
      ∑ i ∈ Finset.range (ρ + 1), z ^ i * t ^ (ρ - i) + z ^ (ρ + 1) / (t - z) := by
    intro z hz
    rw [mul_one_div]
    exact pow_succ_div_sub ρ (fun h => ht (h ▸ hz))
  rw [Multiset.map_congr rfl this, Multiset.sum_map_add]
  congr 1
  induction M using Multiset.induction_on with
  | empty => simp [powerSum]
  | cons a M ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, powerSum] at ih ⊢
    rw [ih (fun h => ht (Multiset.mem_cons_of_mem h)) (fun z hz => this z
      (Multiset.mem_cons_of_mem hz)), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

lemma tendsto_multiset_sum_div_sub (M : Multiset ℂ) (c : ℂ → ℂ) :
    Tendsto (fun t => (M.map fun z => c z / (t - z)).sum) (cocompact ℂ) (𝓝 0) := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons a M ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    rw [← zero_add (0 : ℂ)]
    refine Tendsto.add ?_ ih
    have h1 : Tendsto (fun t : ℂ => t - a) (cocompact ℂ) (cocompact ℂ) := by
      rw [← Metric.cobounded_eq_cocompact]
      exact tendsto_sub_const_cobounded a
    have h2 : Tendsto (fun t : ℂ => (t - a)⁻¹) (cocompact ℂ) (𝓝 0) := by
      rw [← Metric.cobounded_eq_cocompact] at h1 ⊢
      exact tendsto_inv₀_cobounded.comp h1
    simpa [div_eq_mul_inv] using h2.const_mul (c a)

lemma eventually_notMem_cocompact (M : Multiset ℂ) : ∀ᶠ t in cocompact ℂ, t ∉ M := by
  have := (M.toFinset.finite_toSet).isCompact.compl_mem_cocompact
  filter_upwards [this] with t ht
  simpa using ht

/-- **Moment identities from an asymptotic expansion.**  If, for two multisets `M, M'`,
`t^{ρ+1} (Σ_{z ∈ M} 1/(t-z) - Σ_{z ∈ M'} 1/(t-z)) → L` as `t → ∞`, then the power sums of
`M, M'` agree in degrees `< ρ`, and differ by `L` in degree `ρ`. -/
theorem moments_of_tendsto {M M' : Multiset ℂ} {ρ : ℕ} {L : ℂ}
    (h : Tendsto (fun t => t ^ (ρ + 1) *
      ((M.map fun z => 1 / (t - z)).sum - (M'.map fun z => 1 / (t - z)).sum))
      (cocompact ℂ) (𝓝 L)) :
    (∀ k < ρ, powerSum M k = powerSum M' k) ∧ powerSum M ρ - powerSum M' ρ = L := by
  set d : ℕ → ℂ := fun i => powerSum M i - powerSum M' i with hd
  set Q : ℂ[X] := ∑ i ∈ Finset.range (ρ + 1), C (d i) * X ^ (ρ - i) with hQ
  have hrem := (tendsto_multiset_sum_div_sub M (fun z => z ^ (ρ + 1))).sub
    (tendsto_multiset_sum_div_sub M' (fun z => z ^ (ρ + 1)))
  rw [sub_zero] at hrem
  have hQt : Tendsto (fun t => Q.eval t) (cocompact ℂ) (𝓝 L) := by
    have := h.sub hrem
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_notMem_cocompact M, eventually_notMem_cocompact M'] with t h1 h2
    rw [mul_sub, mul_sum_inv_sub_eq M ρ h1, mul_sum_inv_sub_eq M' ρ h2, hQ, eval_finset_sum]
    simp only [eval_mul, eval_C, eval_pow, eval_X, hd, sub_mul, Finset.sum_sub_distrib]
    ring
  have hQC := polynomial_eq_C_of_tendsto hQt
  have hcoeff : ∀ k ≤ ρ, Q.coeff (ρ - k) = d k := by
    intro k hk
    rw [hQ, finset_sum_coeff, Finset.sum_eq_single k]
    · rw [coeff_C_mul_X_pow, if_pos rfl]
    · intro i hi hik
      rw [coeff_C_mul_X_pow, if_neg]
      have := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      omega
    · intro hk'
      exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le hk)) hk'
  refine ⟨fun k hk => ?_, ?_⟩
  · have h1 := hcoeff k hk.le
    rw [hQC, coeff_C, if_neg (by omega)] at h1
    exact sub_eq_zero.1 h1.symm
  · have h1 := hcoeff ρ le_rfl
    rw [hQC, Nat.sub_self, coeff_C_zero] at h1
    exact h1.symm

/-! ### The logarithmic derivative of `(R - v)/(R - w)` -/

lemma eventually_eval_ne_zero_cocompact {P : ℂ[X]} (hP : P ≠ 0) :
    ∀ᶠ t in cocompact ℂ, P.eval t ≠ 0 := by
  filter_upwards [eventually_notMem_cocompact P.roots] with t ht h0
  exact ht ((mem_roots hP).2 h0)

lemma logDeriv_alg_one {n d n' d' v : ℂ} (hd : d ≠ 0) (h1 : n - v * d ≠ 0) :
    (n' * d - n * d') / d ^ 2 / (n / d - v) = (n' - v * d') / (n - v * d) - d' / d := by
  generalize hA : n - v * d = A at h1
  have hn : n = A + v * d := by rw [← hA]; ring
  subst hn
  have e : (A + v * d) / d - v = A / d := by field_simp; ring
  rw [e]
  field_simp
  ring

lemma logDeriv_alg {n d n' d' v w : ℂ} (hd : d ≠ 0) (h1 : n - v * d ≠ 0)
    (h2 : n - w * d ≠ 0) :
    (n' * d - n * d') / d ^ 2 / (n / d - v) - (n' * d - n * d') / d ^ 2 / (n / d - w) =
      (n' - v * d') / (n - v * d) - (n' - w * d') / (n - w * d) := by
  rw [logDeriv_alg_one hd h1, logDeriv_alg_one hd h2]
  ring

/-- Away from finitely many points, `R'/(R - v) - R'/(R - w)` is the sum of `1/(t - z)` over the
`v`-points `z` of `R` minus the same sum over the `w`-points (with multiplicity). -/
lemma logDeriv_ratEval_eventually (R : RatFunc ℂ) {v w : ℂ}
    (hv : R.num - C v * R.denom ≠ 0) (hw : R.num - C w * R.denom ≠ 0) :
    ∀ᶠ t in cocompact ℂ,
      deriv (ratEval R) t / (ratEval R t - v) - deriv (ratEval R) t / (ratEval R t - w) =
        ((R.num - C v * R.denom).roots.map fun z => 1 / (t - z)).sum -
          ((R.num - C w * R.denom).roots.map fun z => 1 / (t - z)).sum := by
  filter_upwards [eventually_eval_ne_zero_cocompact R.denom_ne_zero,
    eventually_eval_ne_zero_cocompact hv, eventually_eval_ne_zero_cocompact hw] with t hD h1 h2
  rw [← (IsAlgClosed.splits _).eval_derivative_div_eval_of_ne_zero h1,
    ← (IsAlgClosed.splits _).eval_derivative_div_eval_of_ne_zero h2]
  have hfun : ratEval R = fun w => R.num.eval w / R.denom.eval w := funext (ratEval_eq R)
  have hd : deriv (ratEval R) t = (R.num.derivative.eval t * R.denom.eval t -
      R.num.eval t * R.denom.derivative.eval t) / R.denom.eval t ^ 2 := by
    rw [hfun]; exact ((R.num.hasDerivAt t).div (R.denom.hasDerivAt t) hD).deriv
  rw [hd, ratEval_eq]
  simp only [eval_sub, eval_mul, eval_C, derivative_sub, derivative_mul, derivative_C,
    zero_mul, zero_add] at h1 h2 ⊢
  exact logDeriv_alg hD h1 h2

/-! ### The asymptotics at `∞` -/

/-- If `R` has a pole of order `ρ ≥ 1` at `∞`, with leading coefficient `A` (`R(t) ∼ A t^ρ`),
then `t^{ρ+1} (R'/(R - v) - R'/(R - w)) → (v - w) ρ / A` as `t → ∞`. -/
theorem tendsto_logDeriv_infty {R : RatFunc ℂ} {ρ : ℕ} (hρ : 0 < ρ)
    (hRo : meromorphicOrderAt (fun t => ratEval R t⁻¹) 0 = ((-(ρ : ℤ) : ℤ) : WithTop ℤ))
    {v w : ℂ} (hvw : v ≠ w) :
    Tendsto (fun t => t ^ (ρ + 1) *
      (deriv (ratEval R) t / (ratEval R t - v) - deriv (ratEval R) t / (ratEval R t - w)))
      (cocompact ℂ)
      (𝓝 ((v - w) * ρ / meromorphicTrailingCoeffAt (fun t => ratEval R t⁻¹) 0)) := by
  set G : ℂ → ℂ := fun s => ratEval R s⁻¹ with hGdef
  set A := meromorphicTrailingCoeffAt G 0 with hA
  have hGm : MeromorphicAt G 0 := (meromorphicAt_ratInvFun R).congr (by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact ratInvFun_eq R hs)
  have hA0 : A ≠ 0 := hGm.meromorphicTrailingCoeffAt_ne_zero (by rw [hRo]; exact WithTop.coe_ne_top)
  have hneg : meromorphicOrderAt G 0 < 0 := by
    rw [hRo]; exact_mod_cast (by omega : -(ρ : ℤ) < 0)
  have hsub : ∀ c : ℂ, meromorphicOrderAt (fun s => G s - c) 0 = ((-(ρ : ℤ) : ℤ) : WithTop ℤ) := by
    intro c
    have e : (fun s => G s - c) = G + (fun _ => -c) := by ext s; simp [sub_eq_add_neg]
    rw [e, meromorphicOrderAt_add_eq_left_of_lt (MeromorphicAt.const (-c) 0), hRo]
    rw [meromorphicOrderAt_const]
    split_ifs
    · exact lt_of_lt_of_le hneg le_top
    · exact hneg
  have hGc : ∀ c : ℂ, MeromorphicAt (fun s => G s - c) 0 :=
    fun c => hGm.sub (MeromorphicAt.const c 0)
  -- the auxiliary function in the coordinate `s = 1/t`
  set M : ℂ → ℂ := fun s => (-(v - w)) * s ^ ((1 : ℤ) - ρ) with hM
  set K : ℂ → ℂ := M * deriv G * ((fun s => G s - v) * (fun s => G s - w))⁻¹ with hK
  have hMm : MeromorphicAt M 0 := (MeromorphicAt.const _ 0).mul
    ((show MeromorphicAt (fun t : ℂ => t) 0 from analyticAt_id.meromorphicAt).zpow _)
  have hDm : MeromorphicAt (deriv G) 0 := hGm.deriv
  have hPm : MeromorphicAt ((fun s => G s - v) * (fun s => G s - w)) 0 := (hGc v).mul (hGc w)
  have hKm : MeromorphicAt K 0 := (hMm.mul hDm).mul hPm.inv
  have hvw' : -(v - w) ≠ 0 := neg_ne_zero.2 (sub_ne_zero.2 hvw)
  have hGo : meromorphicOrderAt (fun s => G s - 0) 0 = ((-(ρ : ℤ) : ℤ) : WithTop ℤ) := hsub 0
  have hdo := order_deriv_of_order_eq hGm (by omega : (-(ρ : ℤ)) ≠ 0) hGo
  have hdt := tc_deriv_of_order_eq hGm (by omega : (-(ρ : ℤ)) ≠ 0) hGo
  have hG0 : (fun s => G s - 0) = G := by ext s; simp
  rw [hG0] at hdt
  have hKo : meromorphicOrderAt K 0 = 0 := by
    rw [hK, meromorphicOrderAt_mul (hMm.mul hDm) hPm.inv, meromorphicOrderAt_mul hMm hDm,
      meromorphicOrderAt_inv, meromorphicOrderAt_mul (hGc v) (hGc w), hsub v, hsub w, hdo, hM,
      order_monomial_zero hvw']
    rw [← WithTop.coe_add, ← WithTop.coe_add, ← WithTop.LinearOrderedAddCommGroup.coe_neg,
      ← WithTop.coe_add, show (1 - (ρ : ℤ)) + (-(ρ : ℤ) - 1) + -((-(ρ : ℤ)) + (-(ρ : ℤ))) = 0 by ring]
    rfl
  have hKt : meromorphicTrailingCoeffAt K 0 = (v - w) * ρ / A := by
    rw [hK, (hMm.mul hDm).meromorphicTrailingCoeffAt_mul hPm.inv,
      hMm.meromorphicTrailingCoeffAt_mul hDm, meromorphicTrailingCoeffAt_inv,
      (hGc v).meromorphicTrailingCoeffAt_mul (hGc w), tc_sub_of_pole v hneg,
      tc_sub_of_pole w hneg, hdt, hM, tc_monomial, ← hA]
    field_simp
    push_cast
    ring
  have hKlim : Tendsto K (𝓝[≠] 0) (𝓝 ((v - w) * ρ / A)) := by
    have := hKm.tendsto_nhds_meromorphicTrailingCoeffAt
    rw [hKo, hKt] at this
    simpa using this
  -- comparison with the original function
  set φ : ℂ → ℂ := fun t => t ^ (ρ + 1) *
      (deriv (ratEval R) t / (ratEval R t - v) - deriv (ratEval R) t / (ratEval R t - w))
    with hφ
  have hev : ∀ᶠ s in 𝓝[≠] 0, φ s⁻¹ = K s := by
    have hD : ∀ᶠ s in 𝓝[≠] (0 : ℂ), R.denom.eval s⁻¹ ≠ 0 :=
      tendsto_inv_cocompact.eventually (eventually_eval_ne_zero_cocompact R.denom_ne_zero)
    have hv : ∀ᶠ s in 𝓝[≠] (0 : ℂ), G s - v ≠ 0 :=
      (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hGc v)).1
        (by rw [hsub v]; exact WithTop.coe_ne_top)
    have hw : ∀ᶠ s in 𝓝[≠] (0 : ℂ), G s - w ≠ 0 :=
      (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hGc w)).1
        (by rw [hsub w]; exact WithTop.coe_ne_top)
    filter_upwards [hD, hv, hw, self_mem_nhdsWithin] with s hDs hvs hws hs
    have hs' : s ≠ 0 := hs
    have hRd : HasDerivAt (ratEval R) (deriv (ratEval R) s⁻¹) s⁻¹ := by
      have hfun : ratEval R = fun w => R.num.eval w / R.denom.eval w := funext (ratEval_eq R)
      rw [hfun]
      exact ((R.num.differentiableAt).div (R.denom.differentiableAt) hDs).hasDerivAt
    have hGd : deriv G s = deriv (ratEval R) s⁻¹ * (-(s ^ 2)⁻¹) :=
      (hRd.comp s (hasDerivAt_inv hs')).deriv
    simp only [hφ, hK, hM, Pi.mul_apply, Pi.inv_apply, hGd]
    change (s⁻¹) ^ (ρ + 1) * (deriv (ratEval R) s⁻¹ / (G s - v) -
      deriv (ratEval R) s⁻¹ / (G s - w)) = _
    rw [zpow_sub₀ hs', zpow_one, zpow_natCast]
    simp only [inv_pow]
    field_simp
    ring
  have hlim : Tendsto (fun s => φ s⁻¹) (𝓝[≠] 0) (𝓝 ((v - w) * ρ / A)) :=
    hKlim.congr' (hev.mono fun s hs => hs.symm)
  have hinv : Tendsto (fun t : ℂ => t⁻¹) (cocompact ℂ) (𝓝[≠] 0) := by
    rw [← Metric.cobounded_eq_cocompact]; exact tendsto_inv₀_cobounded'
  have := hlim.comp hinv
  simpa [Function.comp_def] using this

/-! ### Fiber moments -/

/-- The fiber moment `M_{v,ℓ} = Σ_{R(t) = v} m(t) t^ℓ` of a rational function (sum over the
`v`-points in `ℂ`, counted with multiplicity). -/
noncomputable def fiberMoment (R : RatFunc ℂ) (v : ℂ) (ℓ : ℕ) : ℂ :=
  powerSum (R.num - C v * R.denom).roots ℓ

/-- The fiber moment as a sum over the `v`-points, weighted by the multiplicities. -/
lemma fiberMoment_eq_sum_mult (R : RatFunc ℂ) {v : ℂ} (hv : R.num - C v * R.denom ≠ 0)
    (ℓ : ℕ) :
    fiberMoment R v ℓ = ∑ t ∈ (R.num - C v * R.denom).roots.toFinset,
      (mult (ratEval R) (v : Sphere) t : ℂ) * t ^ ℓ := by
  classical
  rw [fiberMoment, powerSum, Finset.sum_multiset_map_count]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [count_roots, mult_ratEval_eq_rootMultiplicity R hv, nsmul_eq_mul]

/-- **Lemma 9.9**, first half (fiber moments from the endpoint `∞`).  In the endpoint
configuration of Lemma 9.5 (`U = α t^{-ρ}`, `R` with a pole of order `ρ` at `∞`), for any two
distinct values `v, w`, the fiber moments of `R` satisfy `M_{v,ℓ} = M_{w,ℓ}` for `ℓ < ρ`, and
`M_{v,ρ} - M_{w,ρ} = (v - w) α`. -/
theorem OppositeData.fiberMoments {a : Fin 3 → ℂ} {R S : RatFunc ℂ} {j k : Fin 3} {ρ : ℕ}
    {α β : ℂ} (hpair : NormalizedPair {0}ᶜ (ratEval R) (ratEval S) a)
    (hd : OppositeData a R S j k ρ α β) {v w : ℂ} (hvw : v ≠ w) :
    (∀ ℓ < ρ, fiberMoment R v ℓ = fiberMoment R w ℓ) ∧
      fiberMoment R v ρ - fiberMoment R w ρ = (v - w) * α := by
  have hRnc := ne_C_of_nonconst hpair.nonconst_f
  obtain ⟨_, _, _, _, _, _, _, hA, _⟩ := opposite_endpoint_coefficients hpair
    hd.rho_pos hd.denom_zero hd.value_zero hd.order_zero hd.order_infty hd.tendsto_infty
    hd.aux_U hd.aux_V
  have hlim := tendsto_logDeriv_infty hd.rho_pos hd.order_infty hvw
  have hA0 : meromorphicTrailingCoeffAt (fun s => ratEval R s⁻¹) 0 ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hA; exact (Nat.cast_ne_zero.2 hd.rho_pos.ne') hA.symm
  have hL : (v - w) * ρ / meromorphicTrailingCoeffAt (fun s => ratEval R s⁻¹) 0 =
      (v - w) * α := by
    rw [div_eq_iff hA0, ← hA]; ring
  rw [hL] at hlim
  have hlim' := hlim.congr' (by
    filter_upwards [logDeriv_ratEval_eventually R (num_sub_ne_zero (hRnc v))
      (num_sub_ne_zero (hRnc w))] with t ht
    rw [ht])
  exact moments_of_tendsto hlim'

/-! ### The ratio identity of Lemma 9.5 and reality of `t^ρ` -/

/-- **Lemma 9.5**, ratio identity: with balanced constants (`U = γ t^{-ρ}`, `V = γ t^ρ`), at a
finite common point `t₀ ∈ ℂ*` with multiplicities `(m, n)`, `t₀^{2ρ} m = n`. -/
theorem ratio_of_balanced {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {ρ : ℕ} {γ : ℂ} (hγ : γ ≠ 0)
    (hpair : NormalizedPair {0}ᶜ f g a)
    (hU : ∀ᶠ t in cofinite, t * auxU a f g t = γ * t ^ (-(ρ : ℤ)))
    (hV : ∀ᶠ t in cofinite, t * auxV a f g t = γ * t ^ (ρ : ℤ)) {t₀ : ℂ} (ht₀ : t₀ ≠ 0)
    {i : Fin 3} (hm : 0 < mult f (a i : Sphere) t₀) :
    t₀ ^ (2 * ρ) * (mult f (a i : Sphere) t₀ : ℂ) = mult g (a i : Sphere) t₀ := by
  have h := rational_aux_ratio hpair hγ hU hV ht₀ hm
  have hp : t₀ ^ (ρ : ℤ) ≠ 0 := zpow_ne_zero _ ht₀
  rw [zpow_neg, zpow_natCast] at h
  have hp' : t₀ ^ ρ ≠ 0 := pow_ne_zero _ ht₀
  have := congrArg (· * (t₀ ^ ρ / γ)) h
  field_simp at this
  rw [pow_mul', sq]
  linear_combination -this

/-- With `U = α t^{-ρ}`, `V = β t^ρ`, the Mues function `Ψ = U V = α β t^{-2}` has order zero
at every `t₀ ≠ 0`. -/
lemma order_auxPsi_eq_zero_of_pow {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {ρ : ℕ} {α β : ℂ}
    (hα : α ≠ 0) (hβ : β ≠ 0)
    (hU : ∀ᶠ t in cofinite, t * auxU a f g t = α * t ^ (-(ρ : ℤ)))
    (hV : ∀ᶠ t in cofinite, t * auxV a f g t = β * t ^ (ρ : ℤ)) {t₀ : ℂ} (ht₀ : t₀ ≠ 0) :
    meromorphicOrderAt (auxPsi a f g) t₀ = 0 := by
  have heq : auxPsi a f g =ᶠ[𝓝[≠] t₀] fun t => α * β / t ^ 2 := by
    filter_upwards [eventually_nhdsNE_of_cofinite hU t₀, eventually_nhdsNE_of_cofinite hV t₀,
      nhdsWithin_le_nhds (isOpen_ne.mem_nhds ht₀)] with t h1 h2 ht
    have e1 : auxU a f g t = α * t ^ (-(ρ : ℤ)) / t := by rw [← h1]; field_simp
    have e2 : auxV a f g t = β * t ^ (ρ : ℤ) / t := by rw [← h2]; field_simp
    simp only [auxPsi]
    rw [e1, e2, zpow_neg, zpow_natCast]
    have : t ^ ρ ≠ 0 := pow_ne_zero _ ht
    field_simp
  have hA : AnalyticAt ℂ (fun t : ℂ => α * β / t ^ 2) t₀ :=
    analyticAt_const.div (analyticAt_id.pow 2) (pow_ne_zero 2 ht₀)
  rw [meromorphicOrderAt_congr heq]
  have hne : ¬ (fun t : ℂ => α * β / t ^ 2) t₀ = 0 := by simp [ht₀, hα, hβ]
  rw [analyticAt_eq_zero_iff_order_pos hA, not_lt] at hne
  exact le_antisymm hne hA.meromorphicOrderAt_nonneg

/-- **Lemma 9.5**, ratio identity: with balanced constants, at every finite common point
`t₀ ∈ ℂ*` with multiplicities `(m, n)`: `t₀^{2ρ} m = n` and `min(m, n) = 1`. -/
theorem ratio_identity {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {ρ : ℕ} {γ : ℂ} (hγ : γ ≠ 0)
    (hpair : NormalizedPair {0}ᶜ f g a)
    (hU : ∀ᶠ t in cofinite, t * auxU a f g t = γ * t ^ (-(ρ : ℤ)))
    (hV : ∀ᶠ t in cofinite, t * auxV a f g t = γ * t ^ (ρ : ℤ)) {t₀ : ℂ} (ht₀ : t₀ ≠ 0)
    {i : Fin 3} (hm : 0 < mult f (a i : Sphere) t₀) :
    t₀ ^ (2 * ρ) * (mult f (a i : Sphere) t₀ : ℂ) = mult g (a i : Sphere) t₀ ∧
      min (mult f (a i : Sphere) t₀) (mult g (a i : Sphere) t₀) = 1 :=
  ⟨ratio_of_balanced hγ hpair hU hV ht₀ hm,
    hpair.min_mult_eq_one_of_psi ht₀ hm (order_auxPsi_eq_zero_of_pow hγ hγ hU hV ht₀)⟩

/-- At a finite common point `t₀ ∈ ℂ*`, `t₀^ρ` is real (since `t₀^{2ρ} = n/m > 0`). -/
theorem im_pow_eq_zero_of_balanced {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {ρ : ℕ} {γ : ℂ}
    (hγ : γ ≠ 0) (hpair : NormalizedPair {0}ᶜ f g a)
    (hU : ∀ᶠ t in cofinite, t * auxU a f g t = γ * t ^ (-(ρ : ℤ)))
    (hV : ∀ᶠ t in cofinite, t * auxV a f g t = γ * t ^ (ρ : ℤ)) {t₀ : ℂ} (ht₀ : t₀ ≠ 0)
    {i : Fin 3} (hm : 0 < mult f (a i : Sphere) t₀) : (t₀ ^ ρ).im = 0 := by
  have h := ratio_of_balanced hγ hpair hU hV ht₀ hm
  have hn : 0 < mult g (a i : Sphere) t₀ := (hpair.im i t₀ ht₀).1 hm
  set y := t₀ ^ ρ
  set m : ℕ := mult f (a i : Sphere) t₀
  set n : ℕ := mult g (a i : Sphere) t₀
  rw [pow_mul'] at h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [sq, Complex.mul_re, Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
    mul_zero, sub_zero] at hre him
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  by_contra hy
  have hre0 : y.re = 0 := by
    have : (y.re * y.im + y.im * y.re) * m = 0 := by linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · have : 2 * y.im * y.re = 0 := by linarith
      rcases mul_eq_zero.1 this with h2 | h2
      · exact absurd (by linarith : y.im = 0) hy
      · exact h2
    · linarith
  rw [hre0] at hre
  nlinarith [sq_nonneg y.im]

/-- With balanced constants, the fiber moment `M_{a i, ρ}` is real. -/
theorem fiberMoment_im_eq_zero {a : Fin 3 → ℂ} {R S : RatFunc ℂ} {ρ : ℕ} {γ : ℂ} (hρ : 0 < ρ)
    (hγ : γ ≠ 0) (hpair : NormalizedPair {0}ᶜ (ratEval R) (ratEval S) a)
    (hU : ∀ᶠ t in cofinite, t * auxU a (ratEval R) (ratEval S) t = γ * t ^ (-(ρ : ℤ)))
    (hV : ∀ᶠ t in cofinite, t * auxV a (ratEval R) (ratEval S) t = γ * t ^ (ρ : ℤ))
    (i : Fin 3) : (fiberMoment R (a i) ρ).im = 0 := by
  have hv := num_sub_ne_zero (ne_C_of_nonconst hpair.nonconst_f (a i))
  rw [fiberMoment_eq_sum_mult R hv, Complex.im_sum]
  refine Finset.sum_eq_zero fun t ht => ?_
  simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
  by_cases ht0 : t = 0
  · rw [ht0, zero_pow hρ.ne']; simp
  · have hroot : (R.num - C (a i) * R.denom).IsRoot t :=
      (mem_roots hv).1 (Multiset.mem_toFinset.1 ht)
    have hm : 0 < mult (ratEval R) (a i : Sphere) t := by
      rw [mult_ratEval_eq_rootMultiplicity R hv]
      exact (rootMultiplicity_pos hv).2 hroot
    rw [im_pow_eq_zero_of_balanced hγ hpair hU hV ht0 hm, mul_zero]

/-- `P'(a j) = (a j - a i)(a j - a l)` when `{i, l}` are the two other indices. -/
lemma cubicPDeriv_eq (a : Fin 3 → ℂ) {j i l : Fin 3} (hij : i ≠ j) (hlj : l ≠ j) (hli : l ≠ i) :
    cubicPDeriv a j = (a j - a i) * (a j - a l) := by
  have e0 : Finset.univ.erase (0 : Fin 3) = {1, 2} := by decide
  have e1 : Finset.univ.erase (1 : Fin 3) = {0, 2} := by decide
  have e2 : Finset.univ.erase (2 : Fin 3) = {0, 1} := by decide
  fin_cases j <;> fin_cases i <;> fin_cases l <;> simp_all [cubicPDeriv] <;> ring

lemma exists_third (j k : Fin 3) : ∃ l : Fin 3, l ≠ j ∧ l ≠ k := by
  fin_cases j <;> fin_cases k <;> decide

/-- With balanced constants `U = γ t^{-ρ}`, `V = γ t^ρ`, the numbers `(a i - a j) γ` are real for
`j` the index of `R(0) = a j` and any `i`.  This is the residue argument of Lemma 9.6: the
total residue of `t^ρ d log((R - a j)/(R - a i))` gives `(a j - a i) γ = M_{a j, ρ} - M_{a i, ρ}`,
and the fiber moments are real. -/
theorem OppositeData.im_mul_eq_zero {a : Fin 3 → ℂ} {R S : RatFunc ℂ} {j k : Fin 3} {ρ : ℕ}
    {γ : ℂ} (hpair : NormalizedPair {0}ᶜ (ratEval R) (ratEval S) a)
    (hd : OppositeData a R S j k ρ γ γ) (v i : Fin 3) : ((a i - a v) * γ).im = 0 := by
  by_cases hiv : i = v
  · rw [hiv, sub_self, zero_mul, Complex.zero_im]
  have hne : a i ≠ a v := hpair.injective.ne hiv
  obtain ⟨-, h⟩ := hd.fiberMoments hpair hne
  have h1 := fiberMoment_im_eq_zero hd.rho_pos hd.alpha_ne hpair hd.aux_U hd.aux_V i
  have h2 := fiberMoment_im_eq_zero hd.rho_pos hd.alpha_ne hpair hd.aux_U hd.aux_V v
  rw [← h, Complex.sub_im, h1, h2, sub_zero]

/-- **Lemma 9.6** (residue normalization), in invariant form.  In the balanced endpoint
configuration of Lemma 9.5 (`R(0) = a j`, `S(∞) = a k`, `U = γ t^{-ρ}`, `V = γ t^ρ`):
* `a = b`, i.e. `j = k`;
* `σ = ord₀(R - a j)` equals `τ = ord_∞(S - a k)`, and `γ² P'(a j) = -ρσ`;
* for the two other indices `i, l`, after the affine target change `w ↦ (w - a j)/(a i - a j)`
  (which sends `a j, a i, a l` to `0, 1, c` and the coefficient `γ` to `κ = (a i - a j) γ`), the
  coefficient `κ` is real and the third value `c = (a l - a j)/(a i - a j)` is real and negative.
-/
theorem OppositeData.residue_normalization {a : Fin 3 → ℂ} {R S : RatFunc ℂ} {j k : Fin 3}
    {ρ : ℕ} {γ : ℂ} (hpair : NormalizedPair {0}ᶜ (ratEval R) (ratEval S) a)
    (hd : OppositeData a R S j k ρ γ γ) :
    j = k ∧ ∃ σ : ℕ, 0 < σ ∧
      meromorphicOrderAt (fun t => ratEval R t - a j) 0 = ((σ : ℤ) : WithTop ℤ) ∧
      meromorphicOrderAt (fun s => ratEval S s⁻¹ - a k) 0 = ((σ : ℤ) : WithTop ℤ) ∧
      γ ^ 2 * cubicPDeriv a j = -((ρ : ℂ) * σ) ∧
      ∀ i l : Fin 3, i ≠ j → l ≠ j → l ≠ i →
        ((a i - a j) * γ).im = 0 ∧ ∃ c : ℝ, c < 0 ∧ (a l - a j) / (a i - a j) = c := by
  have ha := hpair.injective
  have hγ := hd.alpha_ne
  have hρ : (0 : ℝ) < ρ := by exact_mod_cast hd.rho_pos
  obtain ⟨σ, τ, hσ, hτ, hσo, hτo, -, -, -, -, e1, e2⟩ := opposite_endpoint_coefficients hpair
    hd.rho_pos hd.denom_zero hd.value_zero hd.order_zero hd.order_infty hd.tendsto_infty
    hd.aux_U hd.aux_V
  have hσ' : (0 : ℝ) < σ := by exact_mod_cast hσ
  have hτ' : (0 : ℝ) < τ := by exact_mod_cast hτ
  -- the real part of a real complex number
  have hreal : ∀ x : ℂ, x.im = 0 → x ^ 2 = ((x.re ^ 2 : ℝ) : ℂ) := by
    intro x hx
    apply Complex.ext <;> simp [sq, hx]
  have hjk : j = k := by
    by_contra hjk
    obtain ⟨l, hlj, hlk⟩ := exists_third j k
    have hk : k ≠ j := Ne.symm hjk
    rw [cubicPDeriv_eq a hk hlj (by exact hlk)] at e1
    rw [cubicPDeriv_eq a hjk hlk (by exact hlj)] at e2
    set x := (a k - a j) * γ
    have hx2 : x ^ 2 = -((ρ : ℂ) * (σ + τ)) := by
      simp only [x]; linear_combination e1 + e2
    rw [hreal x (hd.im_mul_eq_zero hpair j k)] at hx2
    have hre := congrArg Complex.re hx2
    simp only [Complex.ofReal_re, Complex.neg_re, Complex.mul_re, Complex.natCast_re,
      Complex.natCast_im, Complex.add_re, Complex.add_im, zero_mul, sub_zero] at hre
    nlinarith [sq_nonneg x.re]
  subst hjk
  have hστ : σ = τ := by
    have : (ρ : ℂ) * σ = ρ * τ := by rw [← neg_inj, ← e1, ← e2]
    have hρ0 : (ρ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hd.rho_pos.ne'
    exact_mod_cast mul_left_cancel₀ hρ0 this
  subst hστ
  refine ⟨rfl, σ, hσ, hσo, hτo, by linear_combination e1, fun i l hij hlj hli => ?_⟩
  have him := hd.im_mul_eq_zero hpair j i
  refine ⟨him, ?_⟩
  set x := (a i - a j) * γ with hxdef
  have hx0 : x ≠ 0 := mul_ne_zero (sub_ne_zero.2 (ha.ne hij)) hγ
  have hxr : x = (x.re : ℂ) := (Complex.ext rfl (by simpa using him))
  have hre0 : x.re ≠ 0 := by
    intro h0; apply hx0; rw [hxr, h0, Complex.ofReal_zero]
  refine ⟨-((ρ : ℝ) * σ) / x.re ^ 2, div_neg_of_neg_of_pos (by nlinarith) (by positivity), ?_⟩
  rw [cubicPDeriv_eq a hij hlj hli] at e1
  have hd0 : a i - a j ≠ 0 := sub_ne_zero.2 (ha.ne hij)
  have hx2 : x ^ 2 = ((x.re ^ 2 : ℝ) : ℂ) := hreal x him
  push_cast
  rw [← Complex.ofReal_pow, ← hx2, hxdef, div_eq_div_iff hd0 (by rw [← hxdef]; exact pow_ne_zero 2 hx0)]
  linear_combination (a i - a j) * e1

/-- **Lemmas 9.5 + 9.6** for a rational sharing datum.  If the finite endpoint case (Lemma 9.4)
does not apply, then after possibly interchanging `R, S` and rescaling `t ↦ ct`, the pair is a
normalized pair on `ℂ*` in the balanced endpoint configuration with `R(0) = S(∞) = a j`
(`U = γ t^{-ρ}`, `V = γ t^ρ`), and for the two other indices `i, l` the normalized coefficient
`(a i - a j) γ` is real and the normalized third value `(a l - a j)/(a i - a j)` is real and
negative. -/
theorem rational_residue_normalization {a : Fin 3 → ℂ} {R S : RatFunc ℂ}
    (hpair : NormalizedPair {0}ᶜ (ratEval R) (ratEval S) a)
    (hnot : ¬ ((R.denom.eval 0 ≠ 0 ∧ S.denom.eval 0 ≠ 0) ∨
      (infVal R.num R.denom ≠ ⊤ ∧ infVal S.num S.denom ≠ ⊤))) :
    ∃ R₁ S₁ : RatFunc ℂ, ((R₁ = R ∧ S₁ = S) ∨ (R₁ = S ∧ S₁ = R)) ∧ ∃ c : ℂ, c ≠ 0 ∧
      NormalizedPair {0}ᶜ (ratEval (ratScale c R₁)) (ratEval (ratScale c S₁)) a ∧
      ∃ (j : Fin 3) (ρ : ℕ) (γ : ℂ), OppositeData a (ratScale c R₁) (ratScale c S₁) j j ρ γ γ ∧
        ∀ i l : Fin 3, i ≠ j → l ≠ j → l ≠ i →
          ((a i - a j) * γ).im = 0 ∧ ∃ c' : ℝ, c' < 0 ∧ (a l - a j) / (a i - a j) = c' := by
  have key : ∀ R₁ S₁ : RatFunc ℂ, NormalizedPair {0}ᶜ (ratEval R₁) (ratEval S₁) a →
      OppositeEndpoints a R₁ S₁ → ∃ c : ℂ, c ≠ 0 ∧
        NormalizedPair {0}ᶜ (ratEval (ratScale c R₁)) (ratEval (ratScale c S₁)) a ∧
        ∃ (j : Fin 3) (ρ : ℕ) (γ : ℂ),
          OppositeData a (ratScale c R₁) (ratScale c S₁) j j ρ γ γ ∧
          ∀ i l : Fin 3, i ≠ j → l ≠ j → l ≠ i →
            ((a i - a j) * γ).im = 0 ∧ ∃ c' : ℝ, c' < 0 ∧ (a l - a j) / (a i - a j) = c' := by
    intro R₁ S₁ hp hop
    obtain ⟨c, hc, hp', j, k, ρ, γ, hd⟩ := hop.exists_balanced hp
    obtain ⟨hjk, σ, -, -, -, -, hrest⟩ := hd.residue_normalization hp'
    subst hjk
    exact ⟨c, hc, hp', j, ρ, γ, hd, hrest⟩
  rcases rational_opposite_endpoints hpair hnot with h | h
  · exact ⟨R, S, Or.inl ⟨rfl, rfl⟩, key R S hpair h⟩
  · exact ⟨S, R, Or.inr ⟨rfl, rfl⟩, key S R hpair.symm h⟩

end ThreeIM
