module

public import RequestProject.ThreeIM.NevanlinnaAux

/-!
# The logarithmic auxiliary functions (Definition 4.3, Lemma 4.4) — local analysis

For `{a, b, c} = {a₁, a₂, a₃}` (here `a = a j`, `b = a (j+1)`, `c = a (j+2)`):

* `Θ_a(h) = h''/h' + 2h'/(h - a) - h'/(h - b) - h'/(h - c)`;
* `θ_a = Θ_a(f) - Θ_a(g)`;
* `W_a = θ_a² - c_a² Ψ`, `c_a = 2a - b - c` (from the proof of Lemma 4.5).

We prove the local facts used in Lemma 4.5:

* all poles of `θ_a` are simple; a pole of `θ_a` is an `a`-defect or a zero of `Ψ`, and every
  `a`-defect is a pole of `θ_a` (Lemma 4.4);
* at a common pole of order `k`, `ord Ψ ≥ 2k - 2` (Lemma 3.7);
* `W_a` vanishes at every common simple pole (equations (3.4) and (4.2)).
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

/-- `Θ_a(h) = h''/h' + 2h'/(h - a) - h'/(h - b) - h'/(h - c)` with `a = a j`. -/
noncomputable def ThetaFun (a : Fin 3 → ℂ) (j : Fin 3) (h : ℂ → ℂ) : ℂ → ℂ := fun z =>
  deriv (deriv h) z / deriv h z + 2 * (deriv h z / (h z - a j)) -
    deriv h z / (h z - a (j + 1)) - deriv h z / (h z - a (j + 2))

/-- `θ_a = Θ_a(f) - Θ_a(g)`. -/
noncomputable def thetaAux (a : Fin 3 → ℂ) (j : Fin 3) (f g : ℂ → ℂ) : ℂ → ℂ := fun z =>
  ThetaFun a j f z - ThetaFun a j g z

/-- `c_a = 2a - b - c`. -/
def cAux (a : Fin 3 → ℂ) (j : Fin 3) : ℂ := 2 * a j - a (j + 1) - a (j + 2)

/-- `W_a = θ_a² - c_a² Ψ`. -/
noncomputable def WAux (a : Fin 3 → ℂ) (j : Fin 3) (f g : ℂ → ℂ) : ℂ → ℂ := fun z =>
  thetaAux a j f g z ^ 2 - cAux a j ^ 2 * auxPsi a f g z

/-! ### Logarithmic derivatives near a point -/

/-- Derivative of a function of the local form `(z - z₀)^n g(z)`. -/
lemma deriv_local_form {F g : ℂ → ℂ} {z₀ : ℂ} (hga : AnalyticAt ℂ g z₀) {n : ℤ}
    (hfg : ∀ᶠ z in 𝓝[≠] z₀, F z = (z - z₀) ^ n * g z) :
    ∀ᶠ z in 𝓝[≠] z₀, deriv F z = (z - z₀) ^ (n - 1) * (n * g z + (z - z₀) * deriv g z) := by
  set G : ℂ → ℂ := fun w => (w - z₀) ^ n * g w with hG
  have hFG : F =ᶠ[𝓝[≠] z₀] G := hfg
  have hderiv : deriv F =ᶠ[𝓝[≠] z₀] deriv G := hFG.nhdsNE_deriv
  filter_upwards [hderiv, nhdsWithin_le_nhds hga.eventually_analyticAt, self_mem_nhdsWithin]
    with w h2 hw hwz
  have hwz' : w - z₀ ≠ 0 := sub_ne_zero.2 hwz
  have hd : DifferentiableAt ℂ (fun w => (w - z₀) ^ n) w :=
    ((differentiableAt_zpow).2 (Or.inl hwz')).comp w (differentiableAt_id.sub_const z₀)
  rw [h2, hG, deriv_fun_mul hd hw.differentiableAt]
  have : deriv (fun w => (w - z₀) ^ n) w = (n : ℂ) * (w - z₀) ^ (n - 1) := by
    rw [deriv_comp_sub_const (f := fun x : ℂ => x ^ n)]
    simp [deriv_zpow]
  rw [this]
  have hpow : (w - z₀) ^ n = (w - z₀) ^ (n - 1) * (w - z₀) := by
    rw [← zpow_add_one₀ hwz', sub_add_cancel]
  rw [hpow]; ring

/-- Logarithmic derivative of a function of the local form `(z - z₀)^n g(z)`, `g(z₀) ≠ 0`. -/
lemma logDeriv_of_local_form {F g : ℂ → ℂ} {z₀ : ℂ} (hga : AnalyticAt ℂ g z₀) (hg0 : g z₀ ≠ 0)
    {n : ℤ} (hfg : ∀ᶠ z in 𝓝[≠] z₀, F z = (z - z₀) ^ n * g z) :
    ∀ᶠ z in 𝓝[≠] z₀, deriv F z / F z = n / (z - z₀) + deriv g z / g z := by
  have hgne : ∀ᶠ w in 𝓝 z₀, g w ≠ 0 := hga.continuousAt.eventually_ne hg0
  filter_upwards [hfg, deriv_local_form hga hfg, nhdsWithin_le_nhds hgne, self_mem_nhdsWithin]
    with w h1 h2 hgw hwz
  have hwz' : w - z₀ ≠ 0 := sub_ne_zero.2 hwz
  rw [h1, h2]
  have hpow : (w - z₀) ^ n = (w - z₀) ^ (n - 1) * (w - z₀) := by
    rw [← zpow_add_one₀ hwz', sub_add_cancel]
  have hp1 : (w - z₀) ^ (n - 1) ≠ 0 := zpow_ne_zero _ hwz'
  rw [hpow]; field_simp

/-- Near `z₀`, `F'/F = n/(z - z₀) + E` with `E` analytic, where `n = ord_{z₀} F`. -/
lemma logDeriv_local {F : ℂ → ℂ} {z₀ : ℂ} (hF : MeromorphicAt F z₀) {n : ℤ}
    (hn : meromorphicOrderAt F z₀ = n) :
    ∃ E : ℂ → ℂ, AnalyticAt ℂ E z₀ ∧
      ∀ᶠ z in 𝓝[≠] z₀, deriv F z / F z = n / (z - z₀) + E z := by
  obtain ⟨g, hga, hg0, hfg⟩ := (meromorphicOrderAt_eq_int_iff hF).1 hn
  set G : ℂ → ℂ := fun w => (w - z₀) ^ n * g w with hG
  have hFG : F =ᶠ[𝓝[≠] z₀] G := hfg.mono fun w hw => by simpa [hG] using hw
  have hderiv : deriv F =ᶠ[𝓝[≠] z₀] deriv G := hFG.nhdsNE_deriv
  refine ⟨fun w => deriv g w / g w, hga.deriv.div hga hg0, ?_⟩
  have hgne : ∀ᶠ w in 𝓝 z₀, g w ≠ 0 := hga.continuousAt.eventually_ne hg0
  filter_upwards [hFG, hderiv, nhdsWithin_le_nhds hga.eventually_analyticAt,
    nhdsWithin_le_nhds hgne, self_mem_nhdsWithin] with w h1 h2 hw hgw hwz
  have hwz' : w - z₀ ≠ 0 := sub_ne_zero.2 hwz
  have hd : DifferentiableAt ℂ (fun w => (w - z₀) ^ n) w :=
    ((differentiableAt_zpow).2 (Or.inl hwz')).comp w (differentiableAt_id.sub_const z₀)
  rw [h1, h2, hG, deriv_fun_mul hd hw.differentiableAt]
  have : deriv (fun w => (w - z₀) ^ n) w = (n : ℂ) * (w - z₀) ^ (n - 1) := by
    rw [deriv_comp_sub_const (f := fun x : ℂ => x ^ n)]
    simp [deriv_zpow]
  rw [this]
  have hpow : (w - z₀) ^ n = (w - z₀) ^ (n - 1) * (w - z₀) := by
    rw [← zpow_add_one₀ hwz', sub_add_cancel]
  have hp1 : (w - z₀) ^ (n - 1) ≠ 0 := zpow_ne_zero _ hwz'
  simp only
  rw [hpow]
  field_simp

/-- Orders of a function of the form `R/(z - z₀) + E` with `E` analytic. -/
lemma order_of_local_form {θ E : ℂ → ℂ} {z₀ R : ℂ} (hE : AnalyticAt ℂ E z₀)
    (hθ : ∀ᶠ z in 𝓝[≠] z₀, θ z = R / (z - z₀) + E z) :
    (-1 : WithTop ℤ) ≤ meromorphicOrderAt θ z₀ ∧
      (R = 0 → 0 ≤ meromorphicOrderAt θ z₀) ∧
      (R ≠ 0 → meromorphicOrderAt θ z₀ = -1) := by
  set G : ℂ → ℂ := fun z => R / (z - z₀) + E z with hG
  have hGm : MeromorphicAt G z₀ := by
    have := hE.meromorphicAt
    simp only [hG]; fun_prop
  have hord : meromorphicOrderAt θ z₀ = meromorphicOrderAt G z₀ := meromorphicOrderAt_congr hθ
  have hR0 : R = 0 → 0 ≤ meromorphicOrderAt θ z₀ := by
    intro hR
    rw [hord]
    have : G =ᶠ[𝓝[≠] z₀] E := Eventually.of_forall fun z => by simp [hG, hR]
    rw [meromorphicOrderAt_congr this]
    exact hE.meromorphicOrderAt_nonneg
  have hR1 : R ≠ 0 → meromorphicOrderAt θ z₀ = -1 := by
    intro hR
    rw [hord]
    have : meromorphicOrderAt G z₀ = ((-1 : ℤ) : WithTop ℤ) := by
      rw [meromorphicOrderAt_eq_int_iff hGm]
      refine ⟨fun z => R + (z - z₀) * E z, by fun_prop, by simpa using hR, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hz' : z - z₀ ≠ 0 := sub_ne_zero.2 hz
      simp only [hG, smul_eq_mul, zpow_neg, zpow_one]
      field_simp
    rw [this]; rfl
  refine ⟨?_, hR0, hR1⟩
  by_cases hR : R = 0
  · exact le_trans (by decide) (hR0 hR)
  · rw [hR1 hR]

/-! ### Local form of `Θ_a` and `θ_a` -/

/-- The integer order of a function with finite order. -/
noncomputable def ordZ (F : ℂ → ℂ) (z : ℂ) : ℤ := (meromorphicOrderAt F z).untop₀

/-- The residue of `Θ_a(h)` at `z₀`, in terms of orders. -/
noncomputable def thetaRes (a : Fin 3 → ℂ) (j : Fin 3) (h : ℂ → ℂ) (z₀ : ℂ) : ℤ :=
  ordZ (deriv h) z₀ + 2 * ordZ (fun w => h w - a j) z₀ - ordZ (fun w => h w - a (j + 1)) z₀ -
    ordZ (fun w => h w - a (j + 2)) z₀

/-- `logDeriv_local` with the order written as `ordZ`. -/
lemma logDeriv_local_ordZ {F : ℂ → ℂ} {z₀ : ℂ} (hF : MeromorphicAt F z₀)
    (htop : meromorphicOrderAt F z₀ ≠ ⊤) :
    ∃ E : ℂ → ℂ, AnalyticAt ℂ E z₀ ∧
      ∀ᶠ z in 𝓝[≠] z₀, deriv F z / F z = (ordZ F z₀ : ℂ) / (z - z₀) + E z := by
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 htop
  have : ordZ F z₀ = n := by simp [ordZ, ← hn]
  rw [this]
  exact logDeriv_local hF hn.symm

lemma ThetaFun_local {h : ℂ → ℂ} {Ω : Set ℂ} (hh : IsNonconstMeroOn h Ω) (a : Fin 3 → ℂ) (j : Fin 3)
    (z₀ : ℂ) (hz : z₀ ∈ Ω) :
    ∃ E : ℂ → ℂ, AnalyticAt ℂ E z₀ ∧
      ∀ᶠ z in 𝓝[≠] z₀, ThetaFun a j h z = (thetaRes a j h z₀ : ℂ) / (z - z₀) + E z := by
  have hm := hh.1 z₀ hz
  have hsub : ∀ c : ℂ, deriv (fun w => h w - c) = deriv h := fun c => funext fun w => deriv_sub_const c
  obtain ⟨E₀, hE₀, h₀⟩ := logDeriv_local_ordZ hm.deriv (order_deriv_of_nonconst hh hz).1
  obtain ⟨E₁, hE₁, h₁⟩ := logDeriv_local_ordZ (F := fun w => h w - a j)
    (hm.sub (MeromorphicAt.const (a j) z₀))
    (hh.2 z₀ hz (a j))
  obtain ⟨E₂, hE₂, h₂⟩ := logDeriv_local_ordZ (F := fun w => h w - a (j + 1))
    (hm.sub (MeromorphicAt.const (a (j + 1)) z₀))
    (hh.2 z₀ hz (a (j + 1)))
  obtain ⟨E₃, hE₃, h₃⟩ := logDeriv_local_ordZ (F := fun w => h w - a (j + 2))
    (hm.sub (MeromorphicAt.const (a (j + 2)) z₀))
    (hh.2 z₀ hz (a (j + 2)))
  refine ⟨fun z => E₀ z + 2 * E₁ z - E₂ z - E₃ z, by fun_prop, ?_⟩
  filter_upwards [h₀, h₁, h₂, h₃] with z e₀ e₁ e₂ e₃
  rw [hsub] at e₁ e₂ e₃
  simp only [ThetaFun, thetaRes]
  rw [e₀, e₁, e₂, e₃]
  push_cast
  ring

lemma ordZ_eq_of_eq {F : ℂ → ℂ} {z₀ : ℂ} {n : ℤ} (h : meromorphicOrderAt F z₀ = n) :
    ordZ F z₀ = n := by
  simp [ordZ, h]

lemma ordZ_deriv_at_value {h : ℂ → ℂ} {Ω : Set ℂ} (hh : IsNonconstMeroOn h Ω) {c z₀ : ℂ} (hz : z₀ ∈ Ω)
    (hpos : 0 < mult h (c : Sphere) z₀) :
    ordZ (deriv h) z₀ = (mult h (c : Sphere) z₀ : ℤ) - 1 :=
  ordZ_eq_of_eq (order_deriv_of_order_eq (hh.1 z₀ hz) (by omega)
    (order_sub_eq_mult hpos))

lemma ordZ_sub_at_value_self {h : ℂ → ℂ} {c z₀ : ℂ} (hpos : 0 < mult h (c : Sphere) z₀) :
    ordZ (fun w => h w - c) z₀ = mult h (c : Sphere) z₀ :=
  ordZ_eq_of_eq (order_sub_eq_mult hpos)

lemma ordZ_sub_at_value_other {h : ℂ → ℂ} {z₀ : ℂ} (hm : MeromorphicAt h z₀) {c d : ℂ}
    (hcd : c ≠ d) (hpos : 0 < mult h (c : Sphere) z₀) :
    ordZ (fun w => h w - d) z₀ = 0 := by
  have hp' : 0 < meromorphicOrderAt (fun w => h w - c) z₀ := by
    rw [order_sub_eq_mult hpos]; exact_mod_cast hpos
  simp [ordZ, order_sub_const_eq_zero_of_pos hm hcd hp']

lemma thetaRes_at_pole {h : ℂ → ℂ} {Ω : Set ℂ} (hh : IsNonconstMeroOn h Ω) (a : Fin 3 → ℂ) (j : Fin 3)
    {z₀ : ℂ} (hz : z₀ ∈ Ω) {k : ℤ} (hk : k < 0) (ho : meromorphicOrderAt h z₀ = k) :
    thetaRes a j h z₀ = k - 1 := by
  have hm := hh.1 z₀ hz
  have hneg : meromorphicOrderAt h z₀ < 0 := by rw [ho]; exact_mod_cast hk
  have h0 : meromorphicOrderAt (fun w => h w - 0) z₀ = k := by simpa using ho
  have e1 := ordZ_eq_of_eq (order_deriv_of_order_eq hm hk.ne h0)
  have e2 : ∀ c, ordZ (fun w => h w - c) z₀ = k := fun c =>
    ordZ_eq_of_eq ((order_sub_const_of_neg hneg c).trans ho)
  simp only [thetaRes, e1, e2]; ring

lemma order_sub_const_eq_zero_generic {h : ℂ → ℂ} {Ω : Set ℂ} (hh : IsNonconstMeroOn h Ω) {z₀ c : ℂ} (hz : z₀ ∈ Ω)
    (hnn : 0 ≤ meromorphicOrderAt h z₀) (hval : mult h (c : Sphere) z₀ = 0) :
    meromorphicOrderAt (fun w => h w - c) z₀ = 0 :=
  le_antisymm (order_sub_nonpos_of_mult_eq_zero hval (hh.2 z₀ hz c))
    (order_sub_const_nonneg (hh.1 z₀ hz) hnn c)

lemma thetaRes_generic {h : ℂ → ℂ} {Ω : Set ℂ} (hh : IsNonconstMeroOn h Ω) (a : Fin 3 → ℂ) (j : Fin 3)
    {z₀ : ℂ} (hz : z₀ ∈ Ω) (hnn : 0 ≤ meromorphicOrderAt h z₀) (hval : ∀ i, mult h (a i : Sphere) z₀ = 0) :
    thetaRes a j h z₀ = ordZ (deriv h) z₀ := by
  have e : ∀ i, ordZ (fun w => h w - a i) z₀ = 0 := fun i => by
    simp [ordZ, order_sub_const_eq_zero_generic hh hz hnn (hval i)]
  simp only [thetaRes, e]; ring

lemma NormalizedPair.meromorphicAt_auxU_of_mem {Ω : Set ℂ} {a : Fin 3 → ℂ} {f g : ℂ → ℂ}
    (hp : NormalizedPair Ω f g a) {z : ℂ} (hz : z ∈ Ω) : MeromorphicAt (auxU a f g) z := by
  have := hp.nonconst_f.1 z hz; have := (hp.nonconst_f.1 z hz).deriv
  have := hp.nonconst_g.1 z hz
  unfold auxU cubicP; fun_prop

lemma NormalizedPair.meromorphicAt_auxV_of_mem {Ω : Set ℂ} {a : Fin 3 → ℂ} {f g : ℂ → ℂ}
    (hp : NormalizedPair Ω f g a) {z : ℂ} (hz : z ∈ Ω) : MeromorphicAt (auxV a f g) z := by
  have := hp.nonconst_f.1 z hz; have := (hp.nonconst_g.1 z hz).deriv
  have := hp.nonconst_g.1 z hz
  unfold auxV cubicP; fun_prop

/-- The residue of `θ_a` vanishes except at `a`-defects and zeros of `Ψ`, and does not vanish
at `a`-defects. -/
lemma thetaRes_sub_spec {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {Ω : Set ℂ} (hp : NormalizedPair Ω f g a)
    (j : Fin 3) (z₀ : ℂ) (hz : z₀ ∈ Ω) :
    (thetaRes a j f z₀ - thetaRes a j g z₀ ≠ 0 →
        IsDefect f g (a j : Sphere) z₀ ∨ 0 < meromorphicOrderAt (auxPsi a f g) z₀) ∧
      (IsDefect f g (a j : Sphere) z₀ → thetaRes a j f z₀ - thetaRes a j g z₀ ≠ 0) := by
  have hfm := hp.nonconst_f.1 z₀ hz
  have hgm := hp.nonconst_g.1 z₀ hz
  have hj1 : j ≠ j + 1 := by fin_cases j <;> decide
  have hj2 : j ≠ j + 2 := by fin_cases j <;> decide
  have hj12 : j + 1 ≠ j + 2 := by fin_cases j <;> decide
  have hmz : ∀ (h : ℂ → ℂ) (c : ℂ), mult h (c : Sphere) z₀ = (ordZ (fun w => h w - c) z₀).toNat :=
    fun _ _ => rfl
  by_cases hpole : 0 < mult f ⊤ z₀
  · have hpole' : 0 < mult g ⊤ z₀ := by rw [← hp.cm_top z₀ hz]; exact hpole
    have hof := order_eq_neg_mult_top hpole
    have hog := order_eq_neg_mult_top hpole'
    rw [← hp.cm_top z₀ hz] at hog
    have hk : (-(mult f ⊤ z₀ : ℕ) : ℤ) < 0 := by omega
    rw [thetaRes_at_pole hp.nonconst_f a j hz hk hof, thetaRes_at_pole hp.nonconst_g a j hz hk hog]
    refine ⟨fun h => absurd (sub_self _) h, fun hd => ?_⟩
    exfalso
    have hneg : meromorphicOrderAt f z₀ < 0 := by rw [hof]; exact_mod_cast hk
    have h1 := hd.1
    rw [hmz, ordZ_eq_of_eq ((order_sub_const_of_neg hneg _).trans hof)] at h1
    omega
  have hf0 : mult f ⊤ z₀ = 0 := by omega
  have hfnn : 0 ≤ meromorphicOrderAt f z₀ :=
    order_nonneg_of_mult_top_eq_zero hf0 (order_ne_top_of_nonconst hp.nonconst_f hz)
  have hgnn : 0 ≤ meromorphicOrderAt g z₀ :=
    order_nonneg_of_mult_top_eq_zero (by rw [← hp.cm_top z₀ hz]; exact hf0)
      (order_ne_top_of_nonconst hp.nonconst_g hz)
  by_cases hval : ∃ i, 0 < mult f (a i : Sphere) z₀
  · obtain ⟨i, hi⟩ := hval
    have hi' := (hp.im i z₀ hz).1 hi
    have df := ordZ_deriv_at_value hp.nonconst_f hz hi
    have dg := ordZ_deriv_at_value hp.nonconst_g hz hi'
    have sf := ordZ_sub_at_value_self hi
    have sg := ordZ_sub_at_value_self hi'
    have of : ∀ x, x ≠ i → ordZ (fun w => f w - a x) z₀ = 0 := fun x hx =>
      ordZ_sub_at_value_other hfm (hp.injective.ne (Ne.symm hx)) hi
    have og : ∀ x, x ≠ i → ordZ (fun w => g w - a x) z₀ = 0 := fun x hx =>
      ordZ_sub_at_value_other hgm (hp.injective.ne (Ne.symm hx)) hi'
    have hcases : i = j ∨ i = j + 1 ∨ i = j + 2 := by fin_cases i <;> fin_cases j <;> decide
    rcases hcases with rfl | rfl | rfl
    · simp only [thetaRes, df, dg, sf, sg, of (i + 1) (Ne.symm hj1), of (i + 2) (Ne.symm hj2),
        og (i + 1) (Ne.symm hj1), og (i + 2) (Ne.symm hj2)]
      refine ⟨fun hne => Or.inl ⟨hi, hi', fun heq => hne ?_⟩, fun hd => ?_⟩
      · rw [heq]; ring
      · have := hd.2.2; omega
    · simp only [thetaRes, df, dg, sf, sg, of j hj1, of (j + 2) (Ne.symm hj12),
        og j hj1, og (j + 2) (Ne.symm hj12)]
      refine ⟨fun hne => absurd (by ring) hne, fun hd => ?_⟩
      have h1 := hd.1
      rw [hmz, of j hj1] at h1
      omega
    · simp only [thetaRes, df, dg, sf, sg, of j hj2, of (j + 1) hj12,
        og j hj2, og (j + 1) hj12]
      refine ⟨fun hne => absurd (by ring) hne, fun hd => ?_⟩
      have h1 := hd.1
      rw [hmz, of j hj2] at h1
      omega
  · push_neg at hval
    have hvf : ∀ i, mult f (a i : Sphere) z₀ = 0 := fun i => by have := hval i; omega
    have hvg : ∀ i, mult g (a i : Sphere) z₀ = 0 := fun i => by
      by_contra h
      have := (hp.im i z₀ hz).2 (Nat.pos_of_ne_zero h)
      have := hvf i
      omega
    rw [thetaRes_generic hp.nonconst_f a j hz hfnn hvf, thetaRes_generic hp.nonconst_g a j hz hgnn hvg]
    refine ⟨fun hne => Or.inr ?_, fun hd => absurd hd.1 (by rw [hvf j]; omega)⟩
    have hzf : ∀ i, meromorphicOrderAt (fun w => f w - a i) z₀ = 0 := fun i =>
      order_sub_const_eq_zero_generic hp.nonconst_f hz hfnn (hvf i)
    have hzg : ∀ i, meromorphicOrderAt (fun w => g w - a i) z₀ = 0 := fun i =>
      order_sub_const_eq_zero_generic hp.nonconst_g hz hgnn (hvg i)
    have hPf := order_cubicP_comp_eq_zero hfm a hzf
    have hPg := order_cubicP_comp_eq_zero hgm a hzg
    have hfg : MeromorphicAt (fun w => f w - g w) z₀ := hfm.sub hgm
    have hPfm : MeromorphicAt (fun w => cubicP a (f w)) z₀ := by unfold cubicP; fun_prop
    have hPgm : MeromorphicAt (fun w => cubicP a (g w)) z₀ := by unfold cubicP; fun_prop
    have hU : auxU a f g = ((fun w => f w - g w) * deriv f) * (fun w => cubicP a (f w))⁻¹ := by
      ext w; simp [auxU, div_eq_mul_inv]
    have hV : auxV a f g = ((fun w => f w - g w) * deriv g) * (fun w => cubicP a (g w))⁻¹ := by
      ext w; simp [auxV, div_eq_mul_inv]
    have hPsi : auxPsi a f g = auxU a f g * auxV a f g := rfl
    obtain ⟨dd, hdd⟩ := WithTop.ne_top_iff_exists.1 (hp.distinct z₀ hz)
    obtain ⟨e, he⟩ := WithTop.ne_top_iff_exists.1
      (order_deriv_of_nonconst hp.nonconst_f hz).1
    obtain ⟨e', he'⟩ := WithTop.ne_top_iff_exists.1
      (order_deriv_of_nonconst hp.nonconst_g hz).1
    have h1 : 0 ≤ meromorphicOrderAt (fun w => f w - g w) z₀ := by
      have : (fun w => f w - g w) = f + fun w => -g w := by ext w; simp [sub_eq_add_neg]
      rw [this]
      refine le_trans ?_ (meromorphicOrderAt_add hfm hgm.neg)
      rw [order_neg_eq]
      exact le_min hfnn hgnn
    have h2 := (order_deriv_of_nonconst hp.nonconst_f hz).2 hfnn
    have h3 := (order_deriv_of_nonconst hp.nonconst_g hz).2 hgnn
    rw [← hdd] at h1
    rw [← he] at h2
    rw [← he'] at h3
    have h1' : (0 : ℤ) ≤ dd := by exact_mod_cast h1
    have h2' : (0 : ℤ) ≤ e := by exact_mod_cast h2
    have h3' : (0 : ℤ) ≤ e' := by exact_mod_cast h3
    have hne' : e - e' ≠ 0 := by
      rwa [ordZ_eq_of_eq he.symm, ordZ_eq_of_eq he'.symm] at hne
    rw [hPsi, meromorphicOrderAt_mul (hp.meromorphicAt_auxU_of_mem hz) (hp.meromorphicAt_auxV_of_mem hz), hU, hV,
      meromorphicOrderAt_mul (hfg.mul hfm.deriv) hPfm.inv, meromorphicOrderAt_mul hfg hfm.deriv,
      meromorphicOrderAt_inv, meromorphicOrderAt_mul (hfg.mul hgm.deriv) hPgm.inv,
      meromorphicOrderAt_mul hfg hgm.deriv, meromorphicOrderAt_inv, hPf, hPg, ← hdd, ← he, ← he']
    simp only [neg_zero, add_zero, ← WithTop.coe_add]
    exact_mod_cast (by omega : (0 : ℤ) < dd + e + (dd + e'))

/-- **Lemma 4.4** (local part).  All poles of `θ_a` are simple; a pole of `θ_a` is an
`a`-defect or a zero of `Ψ`; every `a`-defect is a pole of `θ_a`. -/
theorem thetaAux_order_on {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {Ω : Set ℂ} (hp : NormalizedPair Ω f g a)
    (j : Fin 3) (z₀ : ℂ) (hz : z₀ ∈ Ω) :
    (-1 : WithTop ℤ) ≤ meromorphicOrderAt (thetaAux a j f g) z₀ ∧
      (meromorphicOrderAt (thetaAux a j f g) z₀ < 0 →
        IsDefect f g (a j : Sphere) z₀ ∨ 0 < meromorphicOrderAt (auxPsi a f g) z₀) ∧
      (IsDefect f g (a j : Sphere) z₀ → meromorphicOrderAt (thetaAux a j f g) z₀ = -1) := by
  obtain ⟨Ef, hEf, hf⟩ := ThetaFun_local hp.nonconst_f a j z₀ hz
  obtain ⟨Eg, hEg, hg⟩ := ThetaFun_local hp.nonconst_g a j z₀ hz
  have hloc : ∀ᶠ z in 𝓝[≠] z₀, thetaAux a j f g z =
      ((thetaRes a j f z₀ - thetaRes a j g z₀ : ℤ) : ℂ) / (z - z₀) + (Ef z - Eg z) := by
    filter_upwards [hf, hg] with z e₁ e₂
    simp only [thetaAux, e₁, e₂]
    push_cast
    ring
  obtain ⟨o1, o2, o3⟩ := order_of_local_form (hEf.sub hEg) hloc
  obtain ⟨s1, s2⟩ := thetaRes_sub_spec hp j z₀ hz
  refine ⟨o1, fun hneg => s1 ?_, fun hd => o3 ?_⟩
  · intro h0
    have := o2 (by rw [h0]; simp)
    exact absurd hneg (not_lt.2 this)
  · exact_mod_cast s2 hd

/-! ### Poles -/

/-- At a common pole of order `k`, `g` also has order `-k`. -/
lemma order_g_at_pole {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {Ω : Set ℂ} (hp : NormalizedPair Ω f g a)
    {z₀ : ℂ} (hz : z₀ ∈ Ω) {k : ℕ} (hk : 1 ≤ k) (hf : meromorphicOrderAt f z₀ = -(k : ℤ)) :
    meromorphicOrderAt g z₀ = ((-(k : ℤ) : ℤ) : WithTop ℤ) := by
  have hof : meromorphicOrderAt f z₀ = ((-(k : ℤ) : ℤ) : WithTop ℤ) := by rw [hf]; rfl
  have hmf : mult f ⊤ z₀ = k := by
    rw [mult_top, hof, ← WithTop.LinearOrderedAddCommGroup.coe_neg, neg_neg, WithTop.untop₀_coe]
    simp
  have hpole' : 0 < mult g ⊤ z₀ := by rw [← hp.cm_top z₀ hz, hmf]; omega
  have hog := order_eq_neg_mult_top hpole'
  rw [← hp.cm_top z₀ hz, hmf] at hog
  exact hog

/-- At a common pole of order `k`, `ord U ≥ k - 1`. -/
lemma order_auxU_at_pole {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {Ω : Set ℂ} (hp : NormalizedPair Ω f g a)
    {z₀ : ℂ} (hz : z₀ ∈ Ω) {k : ℕ} (hk : 1 ≤ k) (hf : meromorphicOrderAt f z₀ = -(k : ℤ)) :
    (((k : ℤ) - 1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (auxU a f g) z₀ := by
  have hfm := hp.nonconst_f.1 z₀ hz
  have hgm := hp.nonconst_g.1 z₀ hz
  have hfg : MeromorphicAt (fun w => f w - g w) z₀ := hfm.sub hgm
  have hPf : MeromorphicAt (fun w => cubicP a (f w)) z₀ := by unfold cubicP; fun_prop
  have hU : auxU a f g = ((fun w => f w - g w) * deriv f) * (fun w => cubicP a (f w))⁻¹ := by
    ext w; simp [auxU, div_eq_mul_inv]
  obtain ⟨dd, hdd⟩ := WithTop.ne_top_iff_exists.1 (hp.distinct z₀ hz)
  have hof : meromorphicOrderAt f z₀ = ((-(k : ℤ) : ℤ) : WithTop ℤ) := by rw [hf]; rfl
  have hog := order_g_at_pole hp hz hk hf
  have h1 : ((-k : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (fun w => f w - g w) z₀ := by
    have : (fun w => f w - g w) = f + fun w => -g w := by ext w; simp [sub_eq_add_neg]
    rw [this]
    refine le_trans ?_ (meromorphicOrderAt_add hfm hgm.neg)
    rw [order_neg_eq, hof, hog, min_self]
  have h2 : meromorphicOrderAt (deriv f) z₀ = ((-k - 1 : ℤ) : WithTop ℤ) := by
    have : meromorphicOrderAt (fun w => f w - 0) z₀ = ((-k : ℤ) : WithTop ℤ) := by
      rw [show (fun w => f w - 0) = f by ext; simp]; exact hof
    exact order_deriv_of_order_eq hfm (by omega) this
  have h3 := order_cubicP_comp_of_neg hfm a (by omega : -(k : ℤ) < 0) hof
  rw [hU, meromorphicOrderAt_mul (hfg.mul hfm.deriv) hPf.inv,
    meromorphicOrderAt_mul hfg hfm.deriv, meromorphicOrderAt_inv, h2, h3, ← hdd]
  rw [← hdd] at h1
  have h1' : -(k : ℤ) ≤ dd := by exact_mod_cast h1
  rw [← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add, ← WithTop.coe_add]
  exact_mod_cast (by omega : (k : ℤ) - 1 ≤ dd + (-k - 1) + -(3 * -k))

/-- **Lemma 3.7** (first part): at a common pole of order `k`, `ord Ψ ≥ 2k - 2`. -/
theorem order_auxPsi_at_pole_on {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {Ω : Set ℂ} (hp : NormalizedPair Ω f g a)
    {z₀ : ℂ} (hz : z₀ ∈ Ω) {k : ℕ} (hk : 1 ≤ k) (hf : meromorphicOrderAt f z₀ = -(k : ℤ)) :
    (((2 * k - 2 : ℤ)) : WithTop ℤ) ≤ meromorphicOrderAt (auxPsi a f g) z₀ := by
  have hU := order_auxU_at_pole hp hz hk hf
  have hg := order_g_at_pole hp hz hk hf
  have hV := order_auxU_at_pole hp.symm (a := a) hz hk (by rw [hg]; rfl)
  have hVeq : auxV a f g = fun w => -auxU a g f w := by
    ext w; simp only [auxV, auxU]; ring
  have hPsi : auxPsi a f g = auxU a f g * auxV a f g := rfl
  have hUm := hp.meromorphicAt_auxU_of_mem hz
  have hVm := hp.meromorphicAt_auxV_of_mem hz
  rw [hPsi, meromorphicOrderAt_mul hUm hVm, hVeq, order_neg_eq]
  calc (((2 * k - 2 : ℤ)) : WithTop ℤ) = (((k : ℤ) - 1 : ℤ) : WithTop ℤ) +
      (((k : ℤ) - 1 : ℤ) : WithTop ℤ) := by rw [← WithTop.coe_add]; congr 1; ring
    _ ≤ _ := add_le_add hU hV

/-! ### Common simple poles -/

/-- At a simple pole `h = F/(z - z₀)`: `h' = K/(z - z₀)²` with `K = -F + (z - z₀) F'`. -/
noncomputable def poleK (F : ℂ → ℂ) (z₀ : ℂ) : ℂ → ℂ := fun z =>
  ((-1 : ℤ) : ℂ) * F z + (z - z₀) * deriv F z

/-- At a simple pole `h = F/(z - z₀)`: `h - x = M_x/(z - z₀)` with `M_x = F - x (z - z₀)`. -/
noncomputable def poleM (F : ℂ → ℂ) (z₀ x : ℂ) : ℂ → ℂ := fun z => F z - x * (z - z₀)

/-- The regular part of `Θ_a(h)` at a simple pole `h = F/(z - z₀)`. -/
noncomputable def poleE (a : Fin 3 → ℂ) (j : Fin 3) (F : ℂ → ℂ) (z₀ : ℂ) : ℂ → ℂ := fun z =>
  deriv (poleK F z₀) z / poleK F z₀ z + 2 * (deriv (poleM F z₀ (a j)) z / poleM F z₀ (a j) z) -
    deriv (poleM F z₀ (a (j + 1))) z / poleM F z₀ (a (j + 1)) z -
    deriv (poleM F z₀ (a (j + 2))) z / poleM F z₀ (a (j + 2)) z

section SimplePole

variable {F : ℂ → ℂ} {z₀ : ℂ} (hFa : AnalyticAt ℂ F z₀) (hF0 : F z₀ ≠ 0)
include hFa

lemma analyticAt_poleK : AnalyticAt ℂ (poleK F z₀) z₀ := by
  have := hFa.deriv
  unfold poleK; fun_prop

omit hFa in
lemma poleK_self : poleK F z₀ z₀ = -F z₀ := by simp [poleK]

lemma deriv_poleK_self : deriv (poleK F z₀) z₀ = 0 := by
  have h1 : HasDerivAt (fun z => ((-1 : ℤ) : ℂ) * F z) (((-1 : ℤ) : ℂ) * deriv F z₀) z₀ :=
    hFa.differentiableAt.hasDerivAt.const_mul _
  have h2 : HasDerivAt (fun z => (z - z₀) * deriv F z)
      (1 * deriv F z₀ + (z₀ - z₀) * deriv (deriv F) z₀) z₀ :=
    ((hasDerivAt_id' z₀).sub_const z₀).mul hFa.deriv.differentiableAt.hasDerivAt
  have := (h1.add h2).deriv
  show deriv (fun z => ((-1 : ℤ) : ℂ) * F z + (z - z₀) * deriv F z) z₀ = 0
  refine this.trans ?_; simp

lemma analyticAt_poleM (x : ℂ) : AnalyticAt ℂ (poleM F z₀ x) z₀ := by
  unfold poleM; fun_prop

omit hFa in
lemma poleM_self (x : ℂ) : poleM F z₀ x z₀ = F z₀ := by simp [poleM]

lemma deriv_poleM_self (x : ℂ) : deriv (poleM F z₀ x) z₀ = deriv F z₀ - x := by
  have h := hFa.differentiableAt.hasDerivAt.sub (((hasDerivAt_id' z₀).sub_const z₀).const_mul x)
  have := h.deriv
  show deriv (fun z => F z - x * (z - z₀)) z₀ = _
  refine this.trans ?_; ring

include hF0

lemma analyticAt_poleE (a : Fin 3 → ℂ) (j : Fin 3) : AnalyticAt ℂ (poleE a j F z₀) z₀ := by
  have hK := analyticAt_poleK hFa
  have hM := analyticAt_poleM hFa
  have hK0 : poleK F z₀ z₀ ≠ 0 := by rw [poleK_self]; exact neg_ne_zero.2 hF0
  have hM0 : ∀ x, poleM F z₀ x z₀ ≠ 0 := fun x => by rw [poleM_self]; exact hF0
  unfold poleE
  have e1 := hK.deriv.div hK hK0
  have e2 := fun x => (hM x).deriv.div (hM x) (hM0 x)
  exact ((e1.add (analyticAt_const.mul (e2 (a j)))).sub (e2 _)).sub (e2 _)

lemma poleE_self (a : Fin 3 → ℂ) (j : Fin 3) :
    poleE a j F z₀ z₀ = -cAux a j / F z₀ := by
  simp only [poleE, deriv_poleK_self hFa, deriv_poleM_self hFa, poleM_self, cAux]
  field_simp
  ring

/-- `Θ_a(h) = -2/(z - z₀) + E` at a simple pole `h = F/(z - z₀)`. -/
lemma ThetaFun_simple_pole {h : ℂ → ℂ}
    (hhF : ∀ᶠ z in 𝓝[≠] z₀, h z = (z - z₀) ^ (-1 : ℤ) * F z) (a : Fin 3 → ℂ) (j : Fin 3) :
    ∀ᶠ z in 𝓝[≠] z₀, ThetaFun a j h z = (-2 : ℂ) / (z - z₀) + poleE a j F z₀ z := by
  have hK := analyticAt_poleK hFa
  have hK0 : poleK F z₀ z₀ ≠ 0 := by rw [poleK_self]; exact neg_ne_zero.2 hF0
  have hd1 : ∀ᶠ z in 𝓝[≠] z₀, deriv h z = (z - z₀) ^ ((-1 : ℤ) - 1) * poleK F z₀ z :=
    deriv_local_form hFa hhF
  have l1 := logDeriv_of_local_form hK hK0 hd1
  have hsub : ∀ x : ℂ, deriv (fun w => h w - x) = deriv h := fun x =>
    funext fun w => deriv_sub_const x
  have hx : ∀ x : ℂ, ∀ᶠ z in 𝓝[≠] z₀, h z - x = (z - z₀) ^ (-1 : ℤ) * poleM F z₀ x z := by
    intro x
    filter_upwards [hhF, self_mem_nhdsWithin] with z hz hzz
    have : z - z₀ ≠ 0 := sub_ne_zero.2 hzz
    rw [hz]; simp only [poleM, zpow_neg, zpow_one]
    field_simp
  have lx : ∀ x : ℂ, ∀ᶠ z in 𝓝[≠] z₀, deriv h z / (h z - x) =
      ((-1 : ℤ) : ℂ) / (z - z₀) + deriv (poleM F z₀ x) z / poleM F z₀ x z := by
    intro x
    have := logDeriv_of_local_form (analyticAt_poleM hFa x) (by rw [poleM_self]; exact hF0)
      (hx x)
    rw [hsub] at this
    exact this
  filter_upwards [l1, lx (a j), lx (a (j + 1)), lx (a (j + 2))] with z e1 e2 e3 e4
  simp only [ThetaFun, poleE]
  rw [e1, e2, e3, e4]
  push_cast
  ring

end SimplePole

/-- The local form at a simple pole. -/
lemma exists_simple_pole_form {h : ℂ → ℂ} {z₀ : ℂ} (hm : MeromorphicAt h z₀)
    (ho : meromorphicOrderAt h z₀ = ((-1 : ℤ) : WithTop ℤ)) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F z₀ ∧ F z₀ ≠ 0 ∧
      ∀ᶠ z in 𝓝[≠] z₀, h z = (z - z₀) ^ (-1 : ℤ) * F z := by
  obtain ⟨F, hFa, hF0, hhF⟩ := (meromorphicOrderAt_eq_int_iff hm).1 ho
  exact ⟨F, hFa, hF0, hhF.mono fun z hz => by simpa using hz⟩

/-- The factor `U = (f - g) f'/P(f)` at a common simple pole, in terms of the local data. -/
noncomputable def poleU (a : Fin 3 → ℂ) (F G : ℂ → ℂ) (z₀ : ℂ) : ℂ → ℂ := fun z =>
  (F z - G z) * poleK F z₀ z / (poleM F z₀ (a 0) z * poleM F z₀ (a 1) z * poleM F z₀ (a 2) z)

lemma analyticAt_poleU (a : Fin 3 → ℂ) {F G : ℂ → ℂ} {z₀ : ℂ} (hFa : AnalyticAt ℂ F z₀)
    (hF0 : F z₀ ≠ 0) (hGa : AnalyticAt ℂ G z₀) : AnalyticAt ℂ (poleU a F G z₀) z₀ := by
  have hM := analyticAt_poleM hFa
  have hden : poleM F z₀ (a 0) z₀ * poleM F z₀ (a 1) z₀ * poleM F z₀ (a 2) z₀ ≠ 0 := by
    simp only [poleM_self]; exact mul_ne_zero (mul_ne_zero hF0 hF0) hF0
  exact ((hFa.sub hGa).mul (analyticAt_poleK hFa)).div (((hM _).mul (hM _)).mul (hM _)) hden

lemma poleU_self (a : Fin 3 → ℂ) {F G : ℂ → ℂ} {z₀ : ℂ} (hF0 : F z₀ ≠ 0) :
    poleU a F G z₀ z₀ = -(F z₀ - G z₀) / F z₀ ^ 2 := by
  simp only [poleU, poleM_self, poleK_self]
  field_simp

/-- `U` agrees with `poleU` near a common simple pole. -/
lemma auxU_simple_pole (a : Fin 3 → ℂ) {f g F G : ℂ → ℂ} {z₀ : ℂ} (hFa : AnalyticAt ℂ F z₀)
    (hF0 : F z₀ ≠ 0) (hfF : ∀ᶠ z in 𝓝[≠] z₀, f z = (z - z₀) ^ (-1 : ℤ) * F z)
    (hgG : ∀ᶠ z in 𝓝[≠] z₀, g z = (z - z₀) ^ (-1 : ℤ) * G z) :
    ∀ᶠ z in 𝓝[≠] z₀, auxU a f g z = poleU a F G z₀ z := by
  have hd := deriv_local_form hFa hfF
  have hM : ∀ x, ∀ᶠ z in 𝓝 z₀, poleM F z₀ x z ≠ 0 := fun x =>
    (analyticAt_poleM hFa x).continuousAt.eventually_ne (by rw [poleM_self]; exact hF0)
  filter_upwards [hfF, hgG, hd, nhdsWithin_le_nhds (hM (a 0)), nhdsWithin_le_nhds (hM (a 1)),
    nhdsWithin_le_nhds (hM (a 2)), self_mem_nhdsWithin] with z e1 e2 e3 m0 m1 m2 hz
  have ht : z - z₀ ≠ 0 := sub_ne_zero.2 hz
  have e : ((-1 : ℤ) - 1) = -((2 : ℕ) : ℤ) := by norm_num
  rw [e, zpow_neg, zpow_natCast] at e3
  simp only [poleM] at m0 m1 m2
  simp only [auxU, cubicP, poleU, poleM, poleK, e1, e2, e3, zpow_neg, zpow_one]
  field_simp

/-- Equations (3.4) and (4.2): `W_a = θ_a² - c_a² Ψ` vanishes at every common simple pole. -/
theorem tendsto_WAux_simple_pole_on {a : Fin 3 → ℂ} {f g : ℂ → ℂ}
    {Ω : Set ℂ} (hp : NormalizedPair Ω f g a) (j : Fin 3) {z₀ : ℂ} (hz : z₀ ∈ Ω)
    (hf : meromorphicOrderAt f z₀ = -1) :
    Tendsto (WAux a j f g) (𝓝[≠] z₀) (𝓝 0) := by
  have hfm := hp.nonconst_f.1 z₀ hz
  have hgm := hp.nonconst_g.1 z₀ hz
  have hf' : meromorphicOrderAt f z₀ = ((-1 : ℤ) : WithTop ℤ) := by rw [hf]; rfl
  have hg' : meromorphicOrderAt g z₀ = ((-1 : ℤ) : WithTop ℤ) := by
    rw [order_g_at_pole hp hz (k := 1) le_rfl (by rw [hf]; rfl)]; rfl
  obtain ⟨F, hFa, hF0, hfF⟩ := exists_simple_pole_form hfm hf'
  obtain ⟨G, hGa, hG0, hgG⟩ := exists_simple_pole_form hgm hg'
  have hθ : ∀ᶠ z in 𝓝[≠] z₀, thetaAux a j f g z = poleE a j F z₀ z - poleE a j G z₀ z := by
    filter_upwards [ThetaFun_simple_pole hFa hF0 hfF a j, ThetaFun_simple_pole hGa hG0 hgG a j]
      with z e1 e2
    simp only [thetaAux, e1, e2]; ring
  have hU := auxU_simple_pole a hFa hF0 hfF hgG
  have hU' := auxU_simple_pole a hGa hG0 hgG hfF
  have hΨ : ∀ᶠ z in 𝓝[≠] z₀, auxPsi a f g z = poleU a F G z₀ z * -poleU a G F z₀ z := by
    filter_upwards [hU, hU'] with z e1 e2
    have hV : auxV a f g z = -auxU a g f z := by simp only [auxV, auxU]; ring
    simp only [auxPsi, hV, e1, e2]
  set R : ℂ → ℂ := fun z => (poleE a j F z₀ z - poleE a j G z₀ z) ^ 2 -
    cAux a j ^ 2 * (poleU a F G z₀ z * -poleU a G F z₀ z) with hR
  have hWR : WAux a j f g =ᶠ[𝓝[≠] z₀] R := by
    filter_upwards [hθ, hΨ] with z e1 e2
    simp only [WAux, hR, e1, e2]
  have hRc : ContinuousAt R z₀ := by
    have h1 := analyticAt_poleE hFa hF0 a j
    have h2 := analyticAt_poleE hGa hG0 a j
    have h3 := analyticAt_poleU a hFa hF0 hGa
    have h4 := analyticAt_poleU a hGa hG0 hFa
    exact (((h1.sub h2).pow 2).sub (analyticAt_const.mul (h3.mul h4.neg))).continuousAt
  have hR0 : R z₀ = 0 := by
    simp only [hR, poleE_self hFa hF0, poleE_self hGa hG0, poleU_self a hF0, poleU_self a hG0]
    field_simp
    ring
  rw [← hR0] at *
  exact (hRc.tendsto.mono_left nhdsWithin_le_nhds).congr' hWR.symm


/-! ### The statements on `ℂ` -/

/-- **Lemma 4.4** (local part).  All poles of `θ_a` are simple; a pole of `θ_a` is an
`a`-defect or a zero of `Ψ`; every `a`-defect is a pole of `θ_a`. -/
theorem thetaAux_order {a : Fin 3 → ℂ} {f g : ℂ → ℂ} (hp : NormalizedPair univ f g a)
    (j : Fin 3) (z₀ : ℂ) :
    (-1 : WithTop ℤ) ≤ meromorphicOrderAt (thetaAux a j f g) z₀ ∧
      (meromorphicOrderAt (thetaAux a j f g) z₀ < 0 →
        IsDefect f g (a j : Sphere) z₀ ∨ 0 < meromorphicOrderAt (auxPsi a f g) z₀) ∧
      (IsDefect f g (a j : Sphere) z₀ → meromorphicOrderAt (thetaAux a j f g) z₀ = -1) :=
  thetaAux_order_on hp j z₀ (mem_univ _)

/-- **Lemma 3.7** (first part): at a common pole of order `k`, `ord Ψ ≥ 2k - 2`. -/
theorem order_auxPsi_at_pole {a : Fin 3 → ℂ} {f g : ℂ → ℂ} (hp : NormalizedPair univ f g a)
    {z₀ : ℂ} {k : ℕ} (hk : 1 ≤ k) (hf : meromorphicOrderAt f z₀ = -(k : ℤ)) :
    (((2 * k - 2 : ℤ)) : WithTop ℤ) ≤ meromorphicOrderAt (auxPsi a f g) z₀ :=
  order_auxPsi_at_pole_on hp (mem_univ _) hk hf

/-- Equations (3.4) and (4.2): `W_a = θ_a² - c_a² Ψ` vanishes at every common simple pole. -/
theorem tendsto_WAux_simple_pole {a : Fin 3 → ℂ} {f g : ℂ → ℂ}
    (hp : NormalizedPair univ f g a) (j : Fin 3) {z₀ : ℂ}
    (hf : meromorphicOrderAt f z₀ = -1) :
    Tendsto (WAux a j f g) (𝓝[≠] z₀) (𝓝 0) :=
  tendsto_WAux_simple_pole_on hp j (mem_univ _) hf

end ThreeIM
