module

public import RequestProject.ThreeIM.External
public import RequestProject.ThreeIM.EntireRoot
public import RequestProject.ThreeIM.Holomorphic

/-!
# The autonomous scalar equation (Lemma 7.9)

The only meromorphic solutions on `ℂ` of `h (h - 1) h'' - (3h - 1 + k) (h')² = 0` are constant.

The proof follows the paper: a local analysis of the lowest-order coefficient at poles, zeros
and `1`-points of `h`, Picard's theorem (External theorem 2.1 (v)), and Lemma 7.8.
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

lemma eventually_nhds_of_nhdsNE {z₀ : ℂ} {p : ℂ → Prop} (h : ∀ᶠ z in 𝓝[≠] z₀, p z) :
    ∀ᶠ z in 𝓝[≠] z₀, ∀ᶠ w in 𝓝 z, p w := by
  have := eventually_eventually_nhdsWithin.2 h
  filter_upwards [this, self_mem_nhdsWithin] with z hz hz0
  rwa [nhdsWithin_eq_nhds.2 (isOpen_compl_singleton.mem_nhds hz0)] at hz

lemma eq_zero_of_nhdsNE {E : ℂ → ℂ} {z₀ : ℂ} (hE : ContinuousAt E z₀)
    (h : ∀ᶠ z in 𝓝[≠] z₀, E z = 0) : E z₀ = 0 :=
  tendsto_nhds_unique (hE.tendsto.mono_left nhdsWithin_le_nhds)
    (tendsto_const_nhds.congr' (EventuallyEq.symm h))

/-- Derivatives of `h = c + (z - z₀)^n v` near `z₀`. -/
lemma local_derivs {h v : ℂ → ℂ} {z₀ c : ℂ} {n : ℤ} (hv : AnalyticAt ℂ v z₀)
    (hrep : ∀ᶠ z in 𝓝[≠] z₀, h z = c + (z - z₀) ^ n * v z) :
    ∀ᶠ z in 𝓝[≠] z₀, (z - z₀) * deriv h z = (z - z₀) ^ n * (n * v z + (z - z₀) * deriv v z) ∧
      (z - z₀) ^ 2 * deriv (deriv h) z = (z - z₀) ^ n * (n * (n - 1) * v z +
        2 * n * (z - z₀) * deriv v z + (z - z₀) ^ 2 * deriv (deriv v) z) := by
  have hva : ∀ᶠ z in 𝓝[≠] z₀, ∀ᶠ w in 𝓝 z, AnalyticAt ℂ v w :=
    eventually_nhds_of_nhdsNE (nhdsWithin_le_nhds hv.eventually_analyticAt)
  have hne : ∀ᶠ z in 𝓝[≠] z₀, ∀ᶠ w in 𝓝 z, w ≠ z₀ :=
    eventually_nhds_of_nhdsNE self_mem_nhdsWithin
  filter_upwards [eventually_nhds_of_nhdsNE hrep, hva, hne, self_mem_nhdsWithin]
    with z hz hvz hnez hz0
  have hz0' : z - z₀ ≠ 0 := sub_ne_zero.2 hz0
  have hpow : ∀ w, w ≠ z₀ → ∀ m : ℤ,
      HasDerivAt (fun w => (w - z₀) ^ m) (m * (w - z₀) ^ (m - 1)) w := by
    intro w hw0 m
    have := (hasDerivAt_zpow m (w - z₀) (Or.inl (sub_ne_zero.2 hw0))).comp w
      ((hasDerivAt_id w).sub_const z₀)
    simpa [Function.comp_def] using this
  have hD : ∀ᶠ w in 𝓝 z, HasDerivAt (fun w => c + (w - z₀) ^ n * v w)
      ((n * (w - z₀) ^ (n - 1)) * v w + (w - z₀) ^ n * deriv v w) w := by
    filter_upwards [hvz, hnez] with w hw hw0
    exact ((hpow w hw0 n).mul hw.differentiableAt.hasDerivAt).const_add c
  have hd1 : deriv h =ᶠ[𝓝 z]
      fun w => (n * (w - z₀) ^ (n - 1)) * v w + (w - z₀) ^ n * deriv v w := by
    filter_upwards [hz.eventually_nhds, hD] with w hw hDw
    rw [(show h =ᶠ[𝓝 w] _ from hw).deriv_eq]; exact hDw.deriv
  have hvz' := hvz.self_of_nhds
  have hdv : HasDerivAt (deriv v) (deriv (deriv v) z) z :=
    hvz'.deriv.differentiableAt.hasDerivAt
  have hD2 : HasDerivAt (fun w => (n * (w - z₀) ^ (n - 1)) * v w + (w - z₀) ^ n * deriv v w)
      ((n * ((n - 1 : ℤ) * (z - z₀) ^ (n - 1 - 1))) * v z + (n * (z - z₀) ^ (n - 1)) * deriv v z +
        ((n * (z - z₀) ^ (n - 1)) * deriv v z + (z - z₀) ^ n * deriv (deriv v) z)) z := by
    have := (((hpow z hz0 (n - 1)).const_mul (n : ℂ)).mul hvz'.differentiableAt.hasDerivAt).add
      ((hpow z hz0 n).mul hdv)
    convert this using 1
  have e1 : (z - z₀) ^ (n - 1) = (z - z₀) ^ n / (z - z₀) := by
    rw [zpow_sub_one₀ hz0', div_eq_mul_inv]
  have e2 : (z - z₀) ^ (n - 1 - 1) = (z - z₀) ^ n / (z - z₀) ^ 2 := by
    rw [zpow_sub_one₀ hz0', zpow_sub_one₀ hz0']; field_simp
  constructor
  · rw [(show h =ᶠ[𝓝 z] _ from hz).deriv_eq, (hD.self_of_nhds).deriv, e1]
    field_simp
  · rw [hd1.deriv_eq, hD2.deriv, e1, e2]
    push_cast
    field_simp
    ring

/-- The scalar equation, multiplied by `(z - z₀)²`, in terms of a local representation
`h = c + (z - z₀)^n v`. -/
lemma scalar_local_eq {h v : ℂ → ℂ} {z₀ c k : ℂ} {n : ℤ} (hv : AnalyticAt ℂ v z₀)
    (hrep : ∀ᶠ z in 𝓝[≠] z₀, h z = c + (z - z₀) ^ n * v z)
    (heq : ∀ᶠ z in 𝓝[≠] z₀,
      h z * (h z - 1) * deriv (deriv h) z - (3 * h z - 1 + k) * deriv h z ^ 2 = 0) :
    ∀ᶠ z in 𝓝[≠] z₀, (c + (z - z₀) ^ n * v z) * (c + (z - z₀) ^ n * v z - 1) *
      ((z - z₀) ^ n * (n * (n - 1) * v z + 2 * n * (z - z₀) * deriv v z +
        (z - z₀) ^ 2 * deriv (deriv v) z)) -
      (3 * (c + (z - z₀) ^ n * v z) - 1 + k) *
        ((z - z₀) ^ n * (n * v z + (z - z₀) * deriv v z)) ^ 2 = 0 := by
  filter_upwards [hrep, local_derivs hv hrep, heq] with z h1 h2 h3
  rw [← h2.1, ← h2.2, ← h1]
  linear_combination (z - z₀) ^ 2 * h3

/-- A solution of the scalar equation has no poles. -/
lemma scalar_no_pole {h v : ℂ → ℂ} {z₀ k : ℂ} {p : ℕ} (hp : 1 ≤ p) (hv : AnalyticAt ℂ v z₀)
    (hv0 : v z₀ ≠ 0) (hrep : ∀ᶠ z in 𝓝[≠] z₀, h z = 0 + (z - z₀) ^ (-(p : ℤ)) * v z)
    (heq : ∀ᶠ z in 𝓝[≠] z₀,
      h z * (h z - 1) * deriv (deriv h) z - (3 * h z - 1 + k) * deriv h z ^ 2 = 0) : False := by
  set E : ℂ → ℂ := fun z => v z * (v z - (z - z₀) ^ p) * ((p : ℂ) * (p + 1) * v z -
    2 * p * (z - z₀) * deriv v z + (z - z₀) ^ 2 * deriv (deriv v) z) -
    (3 * v z - (1 - k) * (z - z₀) ^ p) * (-(p : ℂ) * v z + (z - z₀) * deriv v z) ^ 2
  have hE : ∀ᶠ z in 𝓝[≠] z₀, E z = 0 := by
    filter_upwards [scalar_local_eq hv hrep heq, self_mem_nhdsWithin] with z hz hz0
    have ht : (z - z₀) ^ p ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hz0)
    rw [zpow_neg, zpow_natCast] at hz
    push_cast at hz
    field_simp at hz
    simp only [E]
    linear_combination hz
  have hc : ContinuousAt E z₀ := by
    have h1 := hv.continuousAt
    have h2 := hv.deriv.continuousAt
    have h3 := hv.deriv.deriv.continuousAt
    simp only [E]
    fun_prop
  have := eq_zero_of_nhdsNE hc hE
  simp only [E, sub_self, zero_pow (by omega : p ≠ 0), zero_mul, add_zero,
    mul_zero] at this
  have h2p : (2 * (p : ℂ) - 1) ≠ 0 := by
    intro h2
    have : ((2 * p - 1 : ℕ) : ℂ) = 0 := by
      push_cast [show 1 ≤ 2 * p by omega]; linear_combination h2
    exact absurd (by exact_mod_cast this : 2 * p - 1 = 0) (by omega)
  have : v z₀ ^ 3 * (p : ℂ) * (2 * p - 1) = 0 := by linear_combination -this
  simp_all

/-- At a zero of order `p` of a solution, `k p = 1`. -/
lemma scalar_zero_order {h v : ℂ → ℂ} {z₀ k : ℂ} {p : ℕ} (hp : 1 ≤ p) (hv : AnalyticAt ℂ v z₀)
    (hv0 : v z₀ ≠ 0) (hrep : ∀ᶠ z in 𝓝[≠] z₀, h z = 0 + (z - z₀) ^ (p : ℤ) * v z)
    (heq : ∀ᶠ z in 𝓝[≠] z₀,
      h z * (h z - 1) * deriv (deriv h) z - (3 * h z - 1 + k) * deriv h z ^ 2 = 0) :
    k * p = 1 := by
  set E : ℂ → ℂ := fun z => v z * ((z - z₀) ^ p * v z - 1) * ((p : ℂ) * (p - 1) * v z +
    2 * p * (z - z₀) * deriv v z + (z - z₀) ^ 2 * deriv (deriv v) z) -
    (3 * (z - z₀) ^ p * v z - 1 + k) * ((p : ℂ) * v z + (z - z₀) * deriv v z) ^ 2
  have hE : ∀ᶠ z in 𝓝[≠] z₀, E z = 0 := by
    filter_upwards [scalar_local_eq hv hrep heq, self_mem_nhdsWithin] with z hz hz0
    have ht : (z - z₀) ^ p ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hz0)
    rw [zpow_natCast] at hz
    push_cast at hz
    have : ((z - z₀) ^ p) ^ 2 * E z = 0 := by
      simp only [E]; linear_combination hz
    simpa [ht] using this
  have hc : ContinuousAt E z₀ := by
    have h1 := hv.continuousAt
    have h2 := hv.deriv.continuousAt
    have h3 := hv.deriv.deriv.continuousAt
    simp only [E]
    fun_prop
  have := eq_zero_of_nhdsNE hc hE
  simp only [E, sub_self, zero_pow (by omega : p ≠ 0), zero_mul, add_zero,
    mul_zero] at this
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have : v z₀ ^ 2 * (p : ℂ) * (1 - k * p) = 0 := by linear_combination this
  simp only [mul_eq_zero, pow_eq_zero_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    hv0, hp', false_or] at this
  linear_combination -this

/-- At a `1`-point of order `q` of a solution, `(1 + k) q = -1`. -/
lemma scalar_one_order {h v : ℂ → ℂ} {z₀ k : ℂ} {q : ℕ} (hq : 1 ≤ q) (hv : AnalyticAt ℂ v z₀)
    (hv0 : v z₀ ≠ 0) (hrep : ∀ᶠ z in 𝓝[≠] z₀, h z = 1 + (z - z₀) ^ (q : ℤ) * v z)
    (heq : ∀ᶠ z in 𝓝[≠] z₀,
      h z * (h z - 1) * deriv (deriv h) z - (3 * h z - 1 + k) * deriv h z ^ 2 = 0) :
    (1 + k) * q = -1 := by
  set E : ℂ → ℂ := fun z => (1 + (z - z₀) ^ q * v z) * v z * ((q : ℂ) * (q - 1) * v z +
    2 * q * (z - z₀) * deriv v z + (z - z₀) ^ 2 * deriv (deriv v) z) -
    (2 + k + 3 * (z - z₀) ^ q * v z) * ((q : ℂ) * v z + (z - z₀) * deriv v z) ^ 2
  have hE : ∀ᶠ z in 𝓝[≠] z₀, E z = 0 := by
    filter_upwards [scalar_local_eq hv hrep heq, self_mem_nhdsWithin] with z hz hz0
    have ht : (z - z₀) ^ q ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hz0)
    rw [zpow_natCast] at hz
    push_cast at hz
    have : ((z - z₀) ^ q) ^ 2 * E z = 0 := by
      simp only [E]; linear_combination hz
    simpa [ht] using this
  have hc : ContinuousAt E z₀ := by
    have h1 := hv.continuousAt
    have h2 := hv.deriv.continuousAt
    have h3 := hv.deriv.deriv.continuousAt
    simp only [E]
    fun_prop
  have := eq_zero_of_nhdsNE hc hE
  simp only [E, sub_self, zero_pow (by omega : q ≠ 0), zero_mul, add_zero,
    mul_zero] at this
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have : v z₀ ^ 2 * (q : ℂ) * (1 + (1 + k) * q) = 0 := by linear_combination -this
  simp only [mul_eq_zero, pow_eq_zero_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    hv0, hq', false_or] at this
  linear_combination this

/-- The scalar equation at all points near `z₀`. -/
abbrev ScalarEqNear (h : ℂ → ℂ) (k z₀ : ℂ) : Prop :=
  ∀ᶠ z in 𝓝[≠] z₀, h z * (h z - 1) * deriv (deriv h) z - (3 * h z - 1 + k) * deriv h z ^ 2 = 0

/-- A meromorphic solution of the scalar equation has nonnegative order (no poles). -/
lemma scalar_order_nonneg {h : ℂ → ℂ} {z₀ k : ℂ} (hm : MeromorphicAt h z₀)
    (hne : meromorphicOrderAt h z₀ ≠ ⊤) (heq : ScalarEqNear h k z₀) :
    0 ≤ meromorphicOrderAt h z₀ := by
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hne
  rw [← hn]
  by_contra hlt
  have hlt' : n < 0 := by exact_mod_cast not_le.1 hlt
  obtain ⟨g, hga, hg0, hrep⟩ := (meromorphicOrderAt_eq_int_iff hm).1 hn.symm
  refine scalar_no_pole (p := n.natAbs) (by omega) hga hg0 ?_ heq
  filter_upwards [hrep] with z hz
  rw [hz, smul_eq_mul, zero_add]
  congr 2
  omega

/-- Order of a zero of a solution: `k p = 1`. -/
lemma scalar_zero_of_order {h : ℂ → ℂ} {z₀ k : ℂ} {p : ℕ} (hp : 1 ≤ p) (hm : MeromorphicAt h z₀)
    (hn : meromorphicOrderAt h z₀ = ((p : ℤ) : WithTop ℤ)) (heq : ScalarEqNear h k z₀) :
    k * p = 1 := by
  obtain ⟨g, hga, hg0, hrep⟩ := (meromorphicOrderAt_eq_int_iff hm).1 hn
  refine scalar_zero_order hp hga hg0 ?_ heq
  filter_upwards [hrep] with z hz
  rw [hz, smul_eq_mul, zero_add]

/-- Order of a `1`-point of a solution: `(1 + k) q = -1`. -/
lemma scalar_one_of_order {h : ℂ → ℂ} {z₀ k : ℂ} {q : ℕ} (hq : 1 ≤ q) (hm : MeromorphicAt h z₀)
    (hn : meromorphicOrderAt (fun w => h w - 1) z₀ = ((q : ℤ) : WithTop ℤ))
    (heq : ScalarEqNear h k z₀) :
    (1 + k) * q = -1 := by
  obtain ⟨g, hga, hg0, hrep⟩ := (meromorphicOrderAt_eq_int_iff (hm.sub (MeromorphicAt.const 1 z₀))).1 hn
  refine scalar_one_order hq hga hg0 ?_ heq
  filter_upwards [hrep] with z hz
  rw [smul_eq_mul, Pi.sub_apply] at hz; linear_combination hz

/-- If `(H - 1) H'' - 3 (H')² = 0` for an entire function omitting `1`, then `H` is constant:
`H' / (H - 1)³` is constant, and otherwise `(H - 1)^{-2}` would be a nonconstant affine
function without zeros. -/
lemma scalar_affine_const {H : ℂ → ℂ} (hH : Differentiable ℂ H) (h1 : ∀ z, H z ≠ 1)
    (heq : ∀ z, (H z - 1) * deriv (deriv H) z - 3 * deriv H z ^ 2 = 0) :
    ∀ z, H z = H 0 := by
  have hH' : Differentiable ℂ (deriv H) := fun z => ((hH.analyticAt z).deriv).differentiableAt
  have hne : ∀ z, H z - 1 ≠ 0 := fun z => sub_ne_zero.2 (h1 z)
  set K : ℂ → ℂ := fun z => deriv H z / (H z - 1) ^ 3
  have hKd : ∀ z, HasDerivAt K 0 z := by
    intro z
    have h1 := (hH' z).hasDerivAt
    have h2 := ((hH z).hasDerivAt.sub_const 1).pow 3
    convert h1.div h2 (pow_ne_zero _ (hne z)) using 1
    simp only [Pi.pow_apply]
    field_simp [hne z]
    simp only [Nat.cast_ofNat]
    linear_combination (-(H z - 1) ^ 2) * heq z
  have hK : ∀ z, K z = K 0 := fun z =>
    is_const_of_deriv_eq_zero (fun w => (hKd w).differentiableAt) (fun w => (hKd w).deriv) z 0
  set κ := K 0
  have hH'eq : ∀ z, deriv H z = κ * (H z - 1) ^ 3 := by
    intro z
    have := hK z
    simp only [K] at this
    field_simp [hne z] at this
    rw [this, mul_comm]
  by_cases hκ : κ = 0
  · intro z
    exact is_const_of_deriv_eq_zero hH (fun w => by rw [hH'eq w, hκ, zero_mul]) z 0
  · exfalso
    set G : ℂ → ℂ := fun z => ((H z - 1) ^ 2)⁻¹ + 2 * κ * z
    have hGd : ∀ z, HasDerivAt G 0 z := by
      intro z
      have h2 := ((hH z).hasDerivAt.sub_const 1).pow 2
      have h3 := (h2.inv (pow_ne_zero _ (hne z))).add (((hasDerivAt_id z).const_mul (2 * κ)))
      convert h3 using 1
      · ext w
        rfl
      · simp only [Pi.pow_apply]
        rw [hH'eq z]
        field_simp [hne z]
        ring
    have hG : ∀ z, G z = G 0 := fun z =>
      is_const_of_deriv_eq_zero (fun w => (hGd w).differentiableAt) (fun w => (hGd w).deriv) z 0
    have h2κ : 2 * κ ≠ 0 := mul_ne_zero two_ne_zero hκ
    have hz₁ : 2 * κ * (G 0 / (2 * κ)) = G 0 := mul_div_cancel₀ _ h2κ
    have := hG (G 0 / (2 * κ))
    have hval : G (G 0 / (2 * κ)) =
        ((H (G 0 / (2 * κ)) - 1) ^ 2)⁻¹ + 2 * κ * (G 0 / (2 * κ)) := rfl
    rw [hval, hz₁] at this
    have : ((H (G 0 / (2 * κ)) - 1) ^ 2)⁻¹ = 0 := by linear_combination this
    exact inv_ne_zero (pow_ne_zero 2 (hne _)) this

/-- A nonconstant entire function has finite order at every point over every value. -/
lemma entire_analyticOrder_ne_top {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    (hnc : ∃ z, H z ≠ H 0) (z c : ℂ) : analyticOrderAt (fun w => H w - c) z ≠ ⊤ := by
  intro htop
  obtain ⟨z', hz'⟩ := hnc
  have hev : H =ᶠ[𝓝 z] fun _ => c := by
    filter_upwards [analyticOrderAt_eq_top.1 htop] with w hw
    exact sub_eq_zero.1 hw
  have hall := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (f := H)
    (fun w _ => hH.analyticAt w) analyticOnNhd_const isPreconnected_univ (mem_univ z) hev
  exact hz' ((hall (mem_univ z')).trans (hall (mem_univ 0)).symm)

lemma entire_meromorphicOrder_eq {H : ℂ → ℂ} (hH : Differentiable ℂ H) (z c : ℂ) :
    meromorphicOrderAt (fun w => H w - c) z = (analyticOrderAt (fun w => H w - c) z).map (↑) :=
  ((hH.analyticAt z).sub analyticAt_const).meromorphicOrderAt_eq

lemma isNonconstMeroOn_of_entire {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    (hnc : ∃ z, H z ≠ H 0) : IsNonconstMeroOn H univ := by
  refine ⟨fun z _ => (hH.analyticAt z).meromorphicAt, fun z _ c => ?_⟩
  rw [entire_meromorphicOrder_eq hH]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (entire_analyticOrder_ne_top hH hnc z c)
  rw [← hn]; simp

/-- A positive multiplicity of an analytic function over a finite value means it takes that
value. -/
lemma eq_of_mult_pos {H : ℂ → ℂ} {z c : ℂ} (hH : AnalyticAt ℂ H z)
    (hpos : 0 < mult H (c : Sphere) z) : H z = c := by
  by_contra hne
  have h0 : meromorphicOrderAt (fun w => H w - c) z = 0 := by
    have ha : AnalyticAt ℂ (fun w => H w - c) z := hH.sub analyticAt_const
    rw [ha.meromorphicOrderAt_eq, (analyticOrderAt_eq_zero (f := fun w => H w - c)).2
      (Or.inr (sub_ne_zero.2 hne))]
    rfl
  rw [mult_coe, h0] at hpos
  simp at hpos

lemma mult_top_eq_zero_of_analyticAt {H : ℂ → ℂ} {z : ℂ} (hH : AnalyticAt ℂ H z) :
    mult H ⊤ z = 0 := by
  rw [mult_top]
  exact untop₀_toNat_neg_eq_zero_of_nonneg hH.meromorphicOrderAt_nonneg

/-- The order of a nonconstant entire function at a point where it takes the value `c`. -/
lemma entire_order_of_eq {H : ℂ → ℂ} (hH : Differentiable ℂ H) (hnc : ∃ z, H z ≠ H 0)
    {z c : ℂ} (hz : H z = c) : ∃ m : ℕ, 1 ≤ m ∧ analyticOrderAt (fun w => H w - c) z = m ∧
      meromorphicOrderAt (fun w => H w - c) z = ((m : ℤ) : WithTop ℤ) := by
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 (entire_analyticOrder_ne_top hH hnc z c)
  refine ⟨m, ?_, hm.symm, ?_⟩
  · have : analyticOrderAt (fun w => H w - c) z ≠ 0 :=
      analyticOrderAt_ne_zero.2 ⟨(hH.analyticAt z).sub analyticAt_const, by simp [hz]⟩
    rw [← hm] at this
    have : m ≠ 0 := by exact_mod_cast this
    omega
  · rw [entire_meromorphicOrder_eq hH, ← hm]; rfl

/-- Three distinct points of the sphere: two finite values and `∞`. -/
lemma injective_two_finite_top {a b : ℂ} (hab : a ≠ b) :
    Function.Injective ![(a : Sphere), (b : Sphere), ⊤] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

/-- The core case of Lemma 7.9: a nonconstant entire solution cannot take `0` and omit `1`. -/
lemma scalar_entire_zero_case {H : ℂ → ℂ} {k : ℂ} (hH : Differentiable ℂ H)
    (hnc : ∃ z, H z ≠ H 0) (heq : ∀ z₀, ScalarEqNear H k z₀) (h0 : ∃ z₀, H z₀ = 0)
    (h1 : ∀ z, H z ≠ 1) : False := by
  obtain ⟨z₀, hz₀⟩ := h0
  obtain ⟨p, hp, -, hpm⟩ := entire_order_of_eq hH hnc hz₀
  have hkp : k * p = 1 := scalar_zero_of_order hp (hH.analyticAt z₀).meromorphicAt
    (by simpa using hpm) (heq z₀)
  have hk0 : k ≠ 0 := by rintro rfl; simp at hkp
  -- all zeros have the same order `p`
  have hdiv : ∀ z, (p : ℕ∞) ∣ analyticOrderAt H z := by
    intro z
    by_cases hz : H z = 0
    · obtain ⟨m, hm, hma, hmm⟩ := entire_order_of_eq hH hnc hz
      have hkm : k * m = 1 := scalar_zero_of_order hm (hH.analyticAt z).meromorphicAt
        (by simpa using hmm) (heq z)
      have : (m : ℂ) = p := mul_left_cancel₀ hk0 (hkm.trans hkp.symm)
      have : m = p := by exact_mod_cast this
      simp only [sub_zero] at hma
      rw [hma, this]
    · rw [(analyticOrderAt_eq_zero).2 (Or.inr hz)]; exact dvd_zero _
  have hHne : ∃ z, H z ≠ 0 := by
    obtain ⟨z, hz⟩ := hnc
    by_cases h00 : H 0 = 0
    · exact ⟨z, h00 ▸ hz⟩
    · exact ⟨0, h00⟩
  obtain ⟨u, hu, hup⟩ := exists_entire_root_of_dvd hH hHne hp hdiv
  -- Picard's theorem for the root `u` forces `p = 1`
  have hp1 : p = 1 := by
    by_contra hp1
    have hunc : ∃ z, u z ≠ u 0 := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨z, hz⟩ := hnc
      apply hz
      rw [← hup z, ← hup 0, hcon z]
    have hζ := Complex.isPrimitiveRoot_exp p (by omega)
    have hζ1 : Complex.exp (2 * Real.pi * Complex.I / p) ≠ 1 := hζ.ne_one (by omega)
    obtain ⟨i, z, hiz⟩ := ext_picard (isNonconstMeroOn_of_entire hu hunc) _
      (injective_two_finite_top hζ1.symm)
    fin_cases i
    · have := eq_of_mult_pos (hu.analyticAt z) hiz
      exact h1 z (by rw [← hup z, this, one_pow])
    · have := eq_of_mult_pos (hu.analyticAt z) hiz
      exact h1 z (by rw [← hup z, this, hζ.pow_eq_one])
    · have hiz' : 0 < mult u ⊤ z := hiz
      rw [mult_top_eq_zero_of_analyticAt (hu.analyticAt z)] at hiz'
      exact lt_irrefl _ hiz'
  subst hp1
  have hk : k = 1 := by simpa using hkp
  subst hk
  -- the reduced equation `(H - 1) H'' - 3 (H')² = 0`
  have hH' : Differentiable ℂ (deriv H) := fun z => ((hH.analyticAt z).deriv).differentiableAt
  have hH'' : Differentiable ℂ (deriv (deriv H)) := fun z =>
    ((hH.analyticAt z).deriv.deriv).differentiableAt
  have hred : ∀ z, (H z - 1) * deriv (deriv H) z - 3 * deriv H z ^ 2 = 0 := by
    intro z
    have hc : ContinuousAt (fun z => (H z - 1) * deriv (deriv H) z - 3 * deriv H z ^ 2) z := by
      have := (hH z).continuousAt
      have := (hH' z).continuousAt
      have := (hH'' z).continuousAt
      fun_prop
    refine eq_zero_of_nhdsNE (E := fun z => (H z - 1) * deriv (deriv H) z - 3 * deriv H z ^ 2)
      hc ?_
    have hiso : ∀ᶠ w in 𝓝[≠] z, H w ≠ 0 := by
      rcases (hH.analyticAt z).eventually_eq_zero_or_eventually_ne_zero with h | h
      · exfalso
        apply entire_analyticOrder_ne_top hH hnc z 0
        simpa using analyticOrderAt_eq_top.2 h
      · exact h
    filter_upwards [heq z, hiso] with w hw hw0
    have : H w * ((H w - 1) * deriv (deriv H) w - 3 * deriv H w ^ 2) = 0 := by
      linear_combination hw
    exact (mul_eq_zero.1 this).resolve_left hw0
  obtain ⟨z, hz⟩ := hnc
  exact hz (scalar_affine_const hH h1 hred z)

/-- **Lemma 7.9** (autonomous scalar equation): the only meromorphic solutions on `ℂ` of
`h (h - 1) h'' - (3h - 1 + k) (h')² = 0` are constant. -/
theorem autonomous_scalar_const_of_eq {h : ℂ → ℂ} (hh : Meromorphic h) (k : ℂ)
    (heq : ∀ᶠ z in codiscrete ℂ,
      h z * (h z - 1) * deriv (deriv h) z - (3 * h z - 1 + k) * deriv h z ^ 2 = 0) :
    ∃ c : ℂ, ∀ᶠ z in codiscrete ℂ, h z = c := by
  by_contra hcon
  have heqL : ∀ z₀, ScalarEqNear h k z₀ := codiscrete_iff_nhdsNE.1 heq
  have hmo : MeromorphicOn h univ := fun z _ => hh z
  -- `h` is nonconstant
  have hnc : ∀ c z, meromorphicOrderAt (fun w => h w - c) z ≠ ⊤ := by
    intro c z htop
    apply hcon
    refine ⟨c, codiscrete_iff_nhdsNE.2 fun x => ?_⟩
    have hx : meromorphicOrderAt (fun w => h w - c) x = ⊤ := by
      by_contra hx
      exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
        (fun w _ => (hh w).sub (MeromorphicAt.const c w)) isPreconnected_univ
        (mem_univ x) (mem_univ z) hx htop
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 hx] with w hw
    exact sub_eq_zero.1 hw
  -- no poles
  have hnn : ∀ z, 0 ≤ meromorphicOrderAt h z := fun z =>
    scalar_order_nonneg (hh z) (by simpa using hnc 0 z) (heqL z)
  -- an entire representative `H` of `h`
  set H := toMeromorphicNFOn h univ
  have hHh : ∀ x, H =ᶠ[𝓝[≠] x] h := fun x =>
    hmo.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ x)
  have hHa : ∀ x, AnalyticAt ℂ H x := by
    intro x
    apply (meromorphicNFOn_toMeromorphicNFOn h univ (mem_univ x)).meromorphicOrderAt_nonneg_iff_analyticAt.1
    rw [meromorphicOrderAt_congr (hHh x)]
    exact hnn x
  have hH : Differentiable ℂ H := fun x => (hHa x).differentiableAt
  have heqH : ∀ z₀, ScalarEqNear H k z₀ := by
    intro z₀
    filter_upwards [eventually_nhds_of_nhdsNE (hHh z₀), heqL z₀] with z hz hzeq
    have hz' : H =ᶠ[𝓝 z] h := hz
    rw [hz'.self_of_nhds, hz'.deriv_eq, hz'.deriv.deriv_eq]
    exact hzeq
  have hHnc : ∃ z, H z ≠ H 0 := by
    by_contra hc
    push_neg at hc
    apply hnc (H 0) 0
    rw [meromorphicOrderAt_eq_top_iff]
    filter_upwards [hHh 0] with w hw
    rw [← hw, hc w, sub_self]
  -- Picard's theorem: `H` takes `0` or `1`
  obtain ⟨i, z, hiz⟩ := ext_picard (isNonconstMeroOn_of_entire hH hHnc) _
    (injective_two_finite_top (zero_ne_one : (0 : ℂ) ≠ 1))
  have htakes : (∃ z, H z = 0) ∨ (∃ z, H z = 1) := by
    fin_cases i
    · exact Or.inl ⟨z, eq_of_mult_pos (hHa z) hiz⟩
    · exact Or.inr ⟨z, eq_of_mult_pos (hHa z) hiz⟩
    · have hiz' : 0 < mult H ⊤ z := hiz
      rw [mult_top_eq_zero_of_analyticAt (hHa z)] at hiz'
      exact absurd hiz' (lt_irrefl 0)
  by_cases h0 : ∃ z, H z = 0
  · by_cases h1 : ∃ z, H z = 1
    · -- `H` cannot take both `0` and `1`
      obtain ⟨z₁, hz₁⟩ := h0
      obtain ⟨z₂, hz₂⟩ := h1
      obtain ⟨p, hp, -, hpm⟩ := entire_order_of_eq hH hHnc hz₁
      obtain ⟨q, hq, -, hqm⟩ := entire_order_of_eq hH hHnc hz₂
      have hkp := scalar_zero_of_order hp (hHa z₁).meromorphicAt (by simpa using hpm) (heqH z₁)
      have hkq := scalar_one_of_order hq (hHa z₂).meromorphicAt hqm (heqH z₂)
      have : (((p + 1) * q + p : ℕ) : ℂ) = 0 := by
        push_cast
        linear_combination (p : ℂ) * hkq - q * hkp
      have := (Nat.cast_eq_zero).1 this
      omega
    · push_neg at h1
      exact scalar_entire_zero_case hH hHnc heqH h0 h1
  · -- `H` takes `1` and omits `0`: pass to `1 - H`, which solves the equation for `-1 - k`
    push_neg at h0
    have h1 : ∃ z, H z = 1 := htakes.resolve_left (by push_neg; exact h0)
    refine scalar_entire_zero_case (H := fun z => 1 - H z) (k := -1 - k) (hH.const_sub 1) ?_ ?_
      ?_ ?_
    · obtain ⟨z, hz⟩ := hHnc
      exact ⟨z, fun h' => hz (by linear_combination -h')⟩
    · intro z₀
      have hd1 : deriv (fun z => 1 - H z) = fun z => -deriv H z :=
        funext fun z => by simp [deriv_const_sub]
      have hd2 : deriv (fun z => -deriv H z) = fun z => -deriv (deriv H) z :=
        funext fun z => by simp
      filter_upwards [heqH z₀] with z hz
      rw [hd1, hd2]
      linear_combination -hz
    · obtain ⟨z, hz⟩ := h1
      exact ⟨z, by simp [hz]⟩
    · intro z hz
      exact h0 z (by linear_combination -hz)

end ThreeIM
