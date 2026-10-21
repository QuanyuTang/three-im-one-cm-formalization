module

public import RequestProject.ThreeIM.Normalization

/-!
# Local identities at finite shared points (Lemma 3.6)
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

/-- If `f - a` vanishes to order `m ≥ 1` at `z₀`, then `f'` vanishes to order `m - 1`. -/
theorem order_deriv_of_order_sub {f : ℂ → ℂ} {z₀ a : ℂ} (hf : MeromorphicAt f z₀) {m : ℕ}
    (hm1 : 1 ≤ m) (hm : meromorphicOrderAt (fun w => f w - a) z₀ = (m : ℤ)) :
    meromorphicOrderAt (deriv f) z₀ = ((m : ℤ) - 1 : ℤ) := by
  obtain ⟨g, hga, hg0, hfg⟩ :=
    (meromorphicOrderAt_eq_int_iff (hf.sub (MeromorphicAt.const a z₀))).1 hm
  -- `f - a = (w - z₀)^m g` on a punctured neighbourhood
  set F : ℂ → ℂ := fun w => (w - z₀) ^ m * g w with hF
  have hfF : (fun w => f w - a) =ᶠ[𝓝[≠] z₀] F :=
    hfg.mono fun w hw => by simpa [hF, zpow_natCast] using hw
  have hderiv : deriv (fun w => f w - a) =ᶠ[𝓝[≠] z₀] deriv F := hfF.nhdsNE_deriv
  have hderiv' : deriv f =ᶠ[𝓝[≠] z₀] deriv F := by
    have : deriv (fun w => f w - a) = deriv f := funext fun w => deriv_sub_const a
    rwa [this] at hderiv
  -- `F' = (w - z₀)^(m-1) (m g + (w - z₀) g')` near `z₀`
  set G : ℂ → ℂ := fun w => (m : ℂ) * g w + (w - z₀) * deriv g w with hG
  have hGa : AnalyticAt ℂ G z₀ := by
    have := hga.deriv
    simp only [hG]
    fun_prop
  have hG0 : G z₀ ≠ 0 := by
    simp only [hG, sub_self, zero_mul, add_zero]
    exact mul_ne_zero (by exact_mod_cast (by omega : m ≠ 0)) hg0
  have hFG : ∀ᶠ w in 𝓝 z₀, deriv F w = (w - z₀) ^ (m - 1) * G w := by
    filter_upwards [hga.eventually_analyticAt] with w hw
    have hd : DifferentiableAt ℂ (fun w => (w - z₀) ^ m) w := by fun_prop
    rw [hF, deriv_fun_mul hd hw.differentiableAt]
    have : deriv (fun w => (w - z₀) ^ m) w = (m : ℂ) * (w - z₀) ^ (m - 1) := by
      rw [deriv_comp_sub_const (f := fun w => w ^ m)]
      simp
    rw [this, hG]
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel, pow_succ]
    ring
  rw [meromorphicOrderAt_eq_int_iff hf.deriv]
  refine ⟨G, hGa, hG0, ?_⟩
  filter_upwards [hderiv', nhdsWithin_le_nhds hFG] with w h1 h2
  rw [h1, h2, smul_eq_mul]
  congr 1
  rw [show ((m : ℤ) - 1) = ((m - 1 : ℕ) : ℤ) by omega, zpow_natCast]

/-- The order of `P ∘ f` at a point where `f - a j` vanishes to order `m ≥ 1`. -/
theorem order_cubicP_comp {f : ℂ → ℂ} {z₀ : ℂ} (hf : MeromorphicAt f z₀) {a : Fin 3 → ℂ}
    (ha : Function.Injective a) {j : Fin 3} {m : ℕ} (hm1 : 1 ≤ m)
    (hm : meromorphicOrderAt (fun w => f w - a j) z₀ = (m : ℤ)) :
    meromorphicOrderAt (fun w => cubicP a (f w)) z₀ = (m : ℤ) := by
  have hpos : 0 < meromorphicOrderAt (fun w => f w - a j) z₀ := by
    rw [hm]; exact_mod_cast (by omega : 0 < m)
  have hord : ∀ i, meromorphicOrderAt (fun w => f w - a i) z₀ = if i = j then (m : ℤ) else 0 := by
    intro i
    split_ifs with h
    · rw [h, hm]
    · exact order_sub_const_eq_zero_of_pos hf (fun h' => h (ha h').symm) hpos
  have hmer : ∀ i, MeromorphicAt (fun w => f w - a i) z₀ :=
    fun i => hf.sub (MeromorphicAt.const _ _)
  have hfun : (fun w => cubicP a (f w)) =
      ((fun w => f w - a 0) * (fun w => f w - a 1)) * (fun w => f w - a 2) := by
    ext w; simp [cubicP]
  rw [hfun, meromorphicOrderAt_mul ((hmer 0).mul (hmer 1)) (hmer 2),
    meromorphicOrderAt_mul (hmer 0) (hmer 1), hord 0, hord 1, hord 2]
  fin_cases j <;> simp

/-- **Lemma 3.6** (finite shared points), orders.  At a common `a j`-point `z₀` of `f` and `g`
with multiplicities `m, n ≥ 1`, and with `d = ord_{z₀}(f - g)`, one has
`ord U = ord V = d - 1` and `ord Ψ = 2d - 2`. -/
theorem order_aux_at_shared {f g : ℂ → ℂ} {z₀ : ℂ} (hf : MeromorphicAt f z₀)
    (hg : MeromorphicAt g z₀) {a : Fin 3 → ℂ} (ha : Function.Injective a) {j : Fin 3}
    {m n : ℕ} (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
    (hm : meromorphicOrderAt (fun w => f w - a j) z₀ = (m : ℤ))
    (hn : meromorphicOrderAt (fun w => g w - a j) z₀ = (n : ℤ))
    {d : ℤ} (hd : meromorphicOrderAt (fun w => f w - g w) z₀ = d) :
    meromorphicOrderAt (auxU a f g) z₀ = ((d - 1 : ℤ) : WithTop ℤ) ∧
    meromorphicOrderAt (auxV a f g) z₀ = ((d - 1 : ℤ) : WithTop ℤ) ∧
    meromorphicOrderAt (auxPsi a f g) z₀ = ((2 * d - 2 : ℤ) : WithTop ℤ) := by
  have hfg : MeromorphicAt (fun w => f w - g w) z₀ := hf.sub hg
  have hPf : MeromorphicAt (fun w => cubicP a (f w)) z₀ := by
    unfold cubicP; fun_prop
  have hPg : MeromorphicAt (fun w => cubicP a (g w)) z₀ := by
    unfold cubicP; fun_prop
  have key : ∀ {h : ℂ → ℂ} {k : ℕ}, MeromorphicAt h z₀ → 1 ≤ k →
      meromorphicOrderAt (fun w => h w - a j) z₀ = (k : ℤ) →
      meromorphicOrderAt (fun z => (f z - g z) * deriv h z / cubicP a (h z)) z₀ =
        ((d - 1 : ℤ) : WithTop ℤ) := by
    intro h k hh hk1 hk
    have hP : MeromorphicAt (fun w => cubicP a (h w)) z₀ := by unfold cubicP; fun_prop
    have hfun : (fun z => (f z - g z) * deriv h z / cubicP a (h z)) =
        ((fun w => f w - g w) * deriv h) * (fun w => cubicP a (h w))⁻¹ := by
      ext z; simp [div_eq_mul_inv]
    rw [hfun, meromorphicOrderAt_mul (hfg.mul hh.deriv) hP.inv,
      meromorphicOrderAt_mul hfg hh.deriv, meromorphicOrderAt_inv,
      order_cubicP_comp hh ha hk1 hk, order_deriv_of_order_sub hh hk1 hk, hd]
    rw [← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add, ← WithTop.coe_add]
    congr 1; ring
  have hU := key hf hm1 hm
  have hV := key hg hn1 hn
  refine ⟨hU, hV, ?_⟩
  have hUm : MeromorphicAt (auxU a f g) z₀ := by
    unfold auxU; exact (hfg.mul hf.deriv).div hPf
  have hVm : MeromorphicAt (auxV a f g) z₀ := by
    unfold auxV; exact (hfg.mul hg.deriv).div hPg
  have : auxPsi a f g = auxU a f g * auxV a f g := rfl
  rw [this, meromorphicOrderAt_mul hUm hVm]
  rw [show auxU a f g = fun z => (f z - g z) * deriv f z / cubicP a (f z) from rfl, hU,
    show auxV a f g = fun z => (f z - g z) * deriv g z / cubicP a (g z) from rfl, hV,
    ← WithTop.coe_add]
  congr 1; ring

end ThreeIM

namespace ThreeIM

/-- Local representation at an `a`-point of order `m ≥ 1`:
`f = a + (w - z₀)^m F` and `f' = (w - z₀)^(m-1) (m F + (w - z₀) F')` near `z₀`, with `F`
analytic and `F(z₀) ≠ 0`. -/
theorem local_rep {f : ℂ → ℂ} {z₀ a : ℂ} (hf : MeromorphicAt f z₀) {m : ℕ}
    (hm1 : 1 ≤ m) (hm : meromorphicOrderAt (fun w => f w - a) z₀ = (m : ℤ)) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F z₀ ∧ F z₀ ≠ 0 ∧ ∀ᶠ w in 𝓝[≠] z₀,
      f w = a + (w - z₀) ^ m * F w ∧
      deriv f w = (w - z₀) ^ (m - 1) * ((m : ℂ) * F w + (w - z₀) * deriv F w) := by
  obtain ⟨g, hga, hg0, hfg⟩ :=
    (meromorphicOrderAt_eq_int_iff (hf.sub (MeromorphicAt.const a z₀))).1 hm
  set F : ℂ → ℂ := fun w => (w - z₀) ^ m * g w with hF
  have hfF : (fun w => f w - a) =ᶠ[𝓝[≠] z₀] F :=
    hfg.mono fun w hw => by simpa [hF, zpow_natCast] using hw
  have hderiv : deriv (fun w => f w - a) =ᶠ[𝓝[≠] z₀] deriv F := hfF.nhdsNE_deriv
  have hderiv' : deriv f =ᶠ[𝓝[≠] z₀] deriv F := by
    have : deriv (fun w => f w - a) = deriv f := funext fun w => deriv_sub_const a
    rwa [this] at hderiv
  have hFG : ∀ᶠ w in 𝓝 z₀, deriv F w =
      (w - z₀) ^ (m - 1) * ((m : ℂ) * g w + (w - z₀) * deriv g w) := by
    filter_upwards [hga.eventually_analyticAt] with w hw
    have hd : DifferentiableAt ℂ (fun w => (w - z₀) ^ m) w := by fun_prop
    rw [hF, deriv_fun_mul hd hw.differentiableAt]
    have : deriv (fun w => (w - z₀) ^ m) w = (m : ℂ) * (w - z₀) ^ (m - 1) := by
      rw [deriv_comp_sub_const (f := fun w => w ^ m)]
      simp
    rw [this]
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel, pow_succ]
    ring
  refine ⟨g, hga, hg0, ?_⟩
  filter_upwards [hfF, hderiv', nhdsWithin_le_nhds hFG] with w h1 h2 h3
  refine ⟨?_, by rw [h2, h3]⟩
  have := h1; simp only [hF] at this; linear_combination this

/-- `P(x) = (x - a j) · Q_j(x)`, where `Q_j(x) = ∏_{i ≠ j} (x - a i)`. -/
lemma cubicP_eq_mul (a : Fin 3 → ℂ) (j : Fin 3) (x : ℂ) :
    cubicP a x = (x - a j) * ∏ i ∈ Finset.univ.erase j, (x - a i) := by
  rw [Finset.mul_prod_erase Finset.univ (fun i => x - a i) (Finset.mem_univ j),
    Fin.prod_univ_three, cubicP]

lemma prod_erase_ne_zero {a : Fin 3 → ℂ} (ha : Function.Injective a) (j : Fin 3) :
    ∏ i ∈ Finset.univ.erase j, (a j - a i) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  exact sub_ne_zero.2 fun h => (Finset.mem_erase.1 hi).1 (ha h).symm

/-- **Lemma 3.6** (finite shared points), value of the ratio: `Φ(z₀) = m / n`, i.e.
`Φ(z) → m/n` as `z → z₀`, `z ≠ z₀`. -/
theorem tendsto_auxPhi_at_shared {f g : ℂ → ℂ} {z₀ : ℂ} (hf : MeromorphicAt f z₀)
    (hg : MeromorphicAt g z₀) {a : Fin 3 → ℂ} (ha : Function.Injective a) {j : Fin 3}
    {m n : ℕ} (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
    (hm : meromorphicOrderAt (fun w => f w - a j) z₀ = (m : ℤ))
    (hn : meromorphicOrderAt (fun w => g w - a j) z₀ = (n : ℤ))
    (hd : meromorphicOrderAt (fun w => f w - g w) z₀ ≠ ⊤) :
    Tendsto (auxPhi a f g) (𝓝[≠] z₀) (𝓝 ((m : ℂ) / n)) := by
  obtain ⟨F, hFa, hF0, hFrep⟩ := local_rep hf hm1 hm
  obtain ⟨G, hGa, hG0, hGrep⟩ := local_rep hg hn1 hn
  set Q : ℂ → ℂ := fun x => ∏ i ∈ Finset.univ.erase j, (x - a i) with hQ
  have hQ0 : Q (a j) ≠ 0 := prod_erase_ne_zero ha j
  -- the continuous model of `Φ`
  set Λ : ℂ → ℂ := fun w =>
    (((m : ℂ) * F w + (w - z₀) * deriv F w) * (G w * Q (a j + (w - z₀) ^ n * G w))) /
    (((n : ℂ) * G w + (w - z₀) * deriv G w) * (F w * Q (a j + (w - z₀) ^ m * F w)))
    with hΛ
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hΛz : Λ z₀ = (m : ℂ) / n := by
    simp only [hΛ, sub_self, zero_mul, add_zero, zero_pow (by omega : m ≠ 0),
      zero_pow (by omega : n ≠ 0)]
    field_simp
  have hcont : ContinuousAt Λ z₀ := by
    have hQc : Continuous Q := by simp only [hQ]; fun_prop
    have hF' := hFa.deriv.continuousAt
    have hG' := hGa.deriv.continuousAt
    have hFc := hFa.continuousAt
    have hGc := hGa.continuousAt
    apply ContinuousAt.div
    · exact (continuousAt_const.mul hFc |>.add ((continuousAt_id.sub continuousAt_const).mul
        hF')).mul (hGc.mul (hQc.continuousAt.comp (continuousAt_const.add
        (((continuousAt_id.sub continuousAt_const).pow n).mul hGc))))
    · exact (continuousAt_const.mul hGc |>.add ((continuousAt_id.sub continuousAt_const).mul
        hG')).mul (hFc.mul (hQc.continuousAt.comp (continuousAt_const.add
        (((continuousAt_id.sub continuousAt_const).pow m).mul hFc))))
    · simp only [sub_self, zero_mul, add_zero, zero_pow (by omega : m ≠ 0)]
      exact mul_ne_zero (mul_ne_zero hn0 hG0) (mul_ne_zero hF0 hQ0)
  -- eventual nonvanishing of the relevant factors
  have hQne : ∀ᶠ w in 𝓝[≠] z₀, Q (a j + (w - z₀) ^ m * F w) ≠ 0 ∧
      Q (a j + (w - z₀) ^ n * G w) ≠ 0 ∧ F w ≠ 0 ∧ G w ≠ 0 ∧
      (m : ℂ) * F w + (w - z₀) * deriv F w ≠ 0 ∧
      (n : ℂ) * G w + (w - z₀) * deriv G w ≠ 0 := by
    have hQc : Continuous Q := by simp only [hQ]; fun_prop
    have c1 : ContinuousAt (fun w => Q (a j + (w - z₀) ^ m * F w)) z₀ := by
      have := hFa.continuousAt; fun_prop
    have c2 : ContinuousAt (fun w => Q (a j + (w - z₀) ^ n * G w)) z₀ := by
      have := hGa.continuousAt; fun_prop
    have c3 : ContinuousAt (fun w => (m : ℂ) * F w + (w - z₀) * deriv F w) z₀ := by
      have := hFa.continuousAt; have := hFa.deriv.continuousAt; fun_prop
    have c4 : ContinuousAt (fun w => (n : ℂ) * G w + (w - z₀) * deriv G w) z₀ := by
      have := hGa.continuousAt; have := hGa.deriv.continuousAt; fun_prop
    refine nhdsWithin_le_nhds ?_
    filter_upwards [c1.eventually_ne (by simpa [zero_pow (by omega : m ≠ 0)] using hQ0),
      c2.eventually_ne (by simpa [zero_pow (by omega : n ≠ 0)] using hQ0),
      hFa.continuousAt.eventually_ne hF0, hGa.continuousAt.eventually_ne hG0,
      c3.eventually_ne (by simp only [sub_self, zero_mul, add_zero]; exact mul_ne_zero hm0 hF0),
      c4.eventually_ne (by simp only [sub_self, zero_mul, add_zero]; exact mul_ne_zero hn0 hG0)] with w h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  have hfg : ∀ᶠ w in 𝓝[≠] z₀, f w - g w ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hf.sub hg)).1 hd
  have heq : auxPhi a f g =ᶠ[𝓝[≠] z₀] Λ := by
    filter_upwards [hFrep, hGrep, hQne, hfg, self_mem_nhdsWithin] with w hFw hGw hne hfgw hw
    obtain ⟨hq1, hq2, hF1, hG1, hDF, hDG⟩ := hne
    have hwz : w - z₀ ≠ 0 := sub_ne_zero.2 hw
    obtain ⟨m', rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    obtain ⟨n', rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hFw hGw
    simp only [auxPhi, auxU, auxV, hΛ]
    rw [cubicP_eq_mul a j (f w), cubicP_eq_mul a j (g w), hFw.2, hGw.2, hFw.1, hGw.1]
    simp only [hQ, add_sub_cancel_left] at hq1 hq2 ⊢
    rw [hFw.1, hGw.1] at hfgw
    field_simp
    ring
  exact (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm |>.trans (by rw [hΛz])

end ThreeIM
