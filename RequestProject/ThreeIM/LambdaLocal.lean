module

public import RequestProject.ThreeIM.Holomorphic

/-!
# Local analysis of the Lambda auxiliary function

For distinct target values `a, b, c`, write
`Λ_a(h) = h''/h' - 2h'/(h-a) + h'(h-a)/((h-b)(h-c))`.
At an `a`-point of multiplicity `m`, its Laurent residue is `-(m+1)`.
If `m = 1`, the analytic remainder has value zero at the marked point.
All identities below are identities of germs on punctured neighborhoods.

The only project import is `Holomorphic`; the file does not import the
Nevanlinna estimates or any unfinished external theorem.
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

/-- The Lambda function with its three target values written explicitly. -/
noncomputable def LambdaCore (a b c : ℂ) (h : ℂ → ℂ) : ℂ → ℂ := fun z =>
  deriv (deriv h) z / deriv h z - 2 * (deriv h z / (h z - a)) +
    deriv h z * (h z - a) / ((h z - b) * (h z - c))

/-- `Λ_a(h)` for the three marked finite values, with `a = a j`. -/
noncomputable def LambdaFun (a : Fin 3 → ℂ) (j : Fin 3) (h : ℂ → ℂ) : ℂ → ℂ :=
  LambdaCore (a j) (a (j + 1)) (a (j + 2)) h

/-- The difference `E_a = Λ_a(f) - Λ_a(g)`. -/
noncomputable def EAux (a : Fin 3 → ℂ) (j : Fin 3) (f g : ℂ → ℂ) : ℂ → ℂ :=
  fun z => LambdaFun a j f z - LambdaFun a j g z

/-- The Lambda expression is meromorphic, including at zeros of its totalized denominators. -/
lemma meromorphicAt_LambdaCore {h : ℂ → ℂ} {z₀ a b c : ℂ}
    (hh : MeromorphicAt h z₀) : MeromorphicAt (LambdaCore a b c h) z₀ := by
  have hd := hh.deriv
  have hdd := hd.deriv
  unfold LambdaCore
  fun_prop

/-- The difference auxiliary expression is meromorphic. -/
lemma meromorphicAt_EAux {f g : ℂ → ℂ} {z₀ : ℂ} (hf : MeromorphicAt f z₀)
    (hg : MeromorphicAt g z₀) (a : Fin 3 → ℂ) (j : Fin 3) :
    MeromorphicAt (EAux a j f g) z₀ :=
  (meromorphicAt_LambdaCore hf).sub (meromorphicAt_LambdaCore hg)

private lemma lambda_deriv_local_form {F g : ℂ → ℂ} {z₀ : ℂ}
    (hga : AnalyticAt ℂ g z₀) {n : ℤ}
    (hfg : ∀ᶠ z in 𝓝[≠] z₀, F z = (z - z₀) ^ n * g z) :
    ∀ᶠ z in 𝓝[≠] z₀,
      deriv F z = (z - z₀) ^ (n - 1) * (n * g z + (z - z₀) * deriv g z) := by
  set G : ℂ → ℂ := fun w => (w - z₀) ^ n * g w with hG
  have hFG : F =ᶠ[𝓝[≠] z₀] G := hfg
  have hderiv : deriv F =ᶠ[𝓝[≠] z₀] deriv G := hFG.nhdsNE_deriv
  filter_upwards [hderiv, nhdsWithin_le_nhds hga.eventually_analyticAt,
    self_mem_nhdsWithin] with w h2 hw hwz
  have hwz' : w - z₀ ≠ 0 := sub_ne_zero.2 hwz
  have hd : DifferentiableAt ℂ (fun w => (w - z₀) ^ n) w :=
    ((differentiableAt_zpow).2 (Or.inl hwz')).comp w (differentiableAt_id.sub_const z₀)
  rw [h2, hG, deriv_fun_mul hd hw.differentiableAt]
  have hpowderiv : deriv (fun w => (w - z₀) ^ n) w =
      (n : ℂ) * (w - z₀) ^ (n - 1) := by
    rw [deriv_comp_sub_const (f := fun x : ℂ => x ^ n)]
    simp [deriv_zpow]
  rw [hpowderiv]
  have hpow : (w - z₀) ^ n = (w - z₀) ^ (n - 1) * (w - z₀) := by
    rw [← zpow_add_one₀ hwz', sub_add_cancel]
  rw [hpow]
  ring

private lemma lambda_logDeriv_local_form {F g : ℂ → ℂ} {z₀ : ℂ}
    (hga : AnalyticAt ℂ g z₀) (hg0 : g z₀ ≠ 0) {n : ℤ}
    (hfg : ∀ᶠ z in 𝓝[≠] z₀, F z = (z - z₀) ^ n * g z) :
    ∀ᶠ z in 𝓝[≠] z₀,
      deriv F z / F z = n / (z - z₀) + deriv g z / g z := by
  have hgne : ∀ᶠ w in 𝓝 z₀, g w ≠ 0 := hga.continuousAt.eventually_ne hg0
  filter_upwards [hfg, lambda_deriv_local_form hga hfg,
    nhdsWithin_le_nhds hgne, self_mem_nhdsWithin] with w h1 h2 hgw hwz
  have hwz' : w - z₀ ≠ 0 := sub_ne_zero.2 hwz
  rw [h1, h2]
  have hpow : (w - z₀) ^ n = (w - z₀) ^ (n - 1) * (w - z₀) := by
    rw [← zpow_add_one₀ hwz', sub_add_cancel]
  have hp1 : (w - z₀) ^ (n - 1) ≠ 0 := zpow_ne_zero _ hwz'
  rw [hpow]
  field_simp

/-- At an `a`-point of order `m`, `Λ = -(m+1)/(z-z₀) + A`, with analytic `A`.
For a simple point, `A z₀ = 0`, so the expansion has no constant term. -/
theorem LambdaCore_local_at_value {h : ℂ → ℂ} {z₀ a b c : ℂ}
    (hh : MeromorphicAt h z₀) (hab : a ≠ b) (hac : a ≠ c) {m : ℕ}
    (hm1 : 1 ≤ m) (hm : meromorphicOrderAt (fun w => h w - a) z₀ = (m : ℤ)) :
    ∃ A : ℂ → ℂ, AnalyticAt ℂ A z₀ ∧ (m = 1 → A z₀ = 0) ∧
      ∀ᶠ w in 𝓝[≠] z₀,
        LambdaCore a b c h w = -((m : ℂ) + 1) / (w - z₀) + A w := by
  obtain ⟨F, hFa, hF0, hrep⟩ := local_rep hh hm1 hm
  set G : ℂ → ℂ := fun w => (m : ℂ) * F w + (w - z₀) * deriv F w with hG
  set V : ℂ → ℂ := fun w => a + (w - z₀) ^ m * F w with hV
  set J : ℂ → ℂ := fun w => (w - z₀) ^ (m - 1) * G w with hJ
  have hm0 : m ≠ 0 := by omega
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm0
  have hGa : AnalyticAt ℂ G z₀ := by
    have hFd := hFa.deriv
    simp only [hG]
    fun_prop
  have hGvalue : G z₀ = (m : ℂ) * F z₀ := by simp [hG]
  have hG0 : G z₀ ≠ 0 := by rw [hGvalue]; exact mul_ne_zero hmC hF0
  have hVa : AnalyticAt ℂ V z₀ := by simp only [hV]; fun_prop
  have hJa : AnalyticAt ℂ J z₀ := by simp only [hJ]; fun_prop
  have hVvalue : V z₀ = a := by simp [hV, hm0]
  have hVb : V z₀ - b ≠ 0 := by rw [hVvalue]; exact sub_ne_zero.2 hab
  have hVc : V z₀ - c ≠ 0 := by rw [hVvalue]; exact sub_ne_zero.2 hac
  have hGderiv : deriv G z₀ = (m : ℂ) * deriv F z₀ + deriv F z₀ := by
    have hd := (hFa.differentiableAt.hasDerivAt.const_mul (m : ℂ)).add
      (((hasDerivAt_id z₀).sub_const z₀).mul hFa.deriv.differentiableAt.hasDerivAt)
    have hfun : ((fun y => (m : ℂ) * F y) + (fun x => x - z₀) * deriv F) = G := by
      funext w
      simp [hG]
    simpa [hfun] using hd.deriv
  have hsubrep : ∀ᶠ w in 𝓝[≠] z₀,
      (h w - a) = (w - z₀) ^ (m : ℤ) * F w := hrep.mono fun w hw => by
    rw [hw.1, add_sub_cancel_left, zpow_natCast]
  have hderivrep : ∀ᶠ w in 𝓝[≠] z₀,
      deriv h w = (w - z₀) ^ ((m : ℤ) - 1) * G w := hrep.mono fun w hw => by
    rw [show (m : ℤ) - 1 = ((m - 1 : ℕ) : ℤ) by omega, zpow_natCast]
    exact hw.2
  have hldF := lambda_logDeriv_local_form hFa hF0 hsubrep
  have hldG := lambda_logDeriv_local_form hGa hG0 hderivrep
  have hsubderiv : deriv (fun w => h w - a) = deriv h :=
    funext fun _ => deriv_sub_const a
  rw [hsubderiv] at hldF
  set A : ℂ → ℂ := fun w => deriv G w / G w - 2 * (deriv F w / F w) +
    J w * (V w - a) / ((V w - b) * (V w - c)) with hA
  have hAa : AnalyticAt ℂ A z₀ := by
    exact ((hGa.deriv.div hGa hG0).sub (analyticAt_const.mul (hFa.deriv.div hFa hF0))).add
      ((hJa.mul (hVa.sub analyticAt_const)).div
        ((hVa.sub analyticAt_const).mul (hVa.sub analyticAt_const)) (mul_ne_zero hVb hVc))
  refine ⟨A, hAa, ?_, ?_⟩
  · intro hmone
    change deriv G z₀ / G z₀ - 2 * (deriv F z₀ / F z₀) +
      J z₀ * (V z₀ - a) / ((V z₀ - b) * (V z₀ - c)) = 0
    have hthird : J z₀ * (V z₀ - a) / ((V z₀ - b) * (V z₀ - c)) = 0 := by
      simp [hVvalue]
    rw [hthird, hGderiv, hGvalue, hmone]
    norm_num
    ring
  · filter_upwards [hrep, hldF, hldG] with w hw hFlog hGlog
    have hhw : h w = V w := hw.1
    have hdw : deriv h w = J w := hw.2
    simp only [LambdaCore]
    rw [hGlog, hFlog, hhw, hdw]
    simp only [hA]
    push_cast
    ring

private lemma lambda_order_of_local_form {θ A : ℂ → ℂ} {z₀ R : ℂ}
    (hA : AnalyticAt ℂ A z₀)
    (hθ : ∀ᶠ w in 𝓝[≠] z₀, θ w = R / (w - z₀) + A w) :
    (-1 : WithTop ℤ) ≤ meromorphicOrderAt θ z₀ ∧
      (R = 0 → 0 ≤ meromorphicOrderAt θ z₀) ∧
      (R ≠ 0 → meromorphicOrderAt θ z₀ = -1) := by
  set G : ℂ → ℂ := fun w => R / (w - z₀) + A w with hG
  have hGm : MeromorphicAt G z₀ := by
    have := hA.meromorphicAt
    simp only [hG]
    fun_prop
  have hord : meromorphicOrderAt θ z₀ = meromorphicOrderAt G z₀ :=
    meromorphicOrderAt_congr hθ
  have hzero : R = 0 → 0 ≤ meromorphicOrderAt θ z₀ := by
    intro hR
    rw [hord]
    have heq : G =ᶠ[𝓝[≠] z₀] A := Eventually.of_forall fun w => by simp [hG, hR]
    rw [meromorphicOrderAt_congr heq]
    exact hA.meromorphicOrderAt_nonneg
  have hpole : R ≠ 0 → meromorphicOrderAt θ z₀ = -1 := by
    intro hR
    rw [hord]
    have he : meromorphicOrderAt G z₀ = ((-1 : ℤ) : WithTop ℤ) := by
      rw [meromorphicOrderAt_eq_int_iff hGm]
      refine ⟨fun w => R + (w - z₀) * A w, by fun_prop, by simpa using hR, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with w hw
      have hw' : w - z₀ ≠ 0 := sub_ne_zero.2 hw
      simp only [hG, smul_eq_mul, zpow_neg, zpow_one]
      field_simp
    rw [he]
    rfl
  refine ⟨?_, hzero, hpole⟩
  by_cases hR : R = 0
  · exact le_trans (by decide) (hzero hR)
  · rw [hpole hR]

private lemma lambda_order_ge_one_of_analytic_zero {θ A : ℂ → ℂ} {z₀ : ℂ}
    (hA : AnalyticAt ℂ A z₀) (hAz : A z₀ = 0)
    (hθ : θ =ᶠ[𝓝[≠] z₀] A) : (1 : WithTop ℤ) ≤ meromorphicOrderAt θ z₀ := by
  rw [meromorphicOrderAt_congr hθ]
  have hpos : 0 < meromorphicOrderAt A z₀ :=
    (tendsto_zero_iff_meromorphicOrderAt_pos hA.meromorphicAt).1 (by
      rw [← hAz]
      exact hA.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  induction ho : meromorphicOrderAt A z₀ using WithTop.recTopCoe with
  | top => simp
  | coe k =>
    rw [ho] at hpos
    have hk : (0 : ℤ) < k := by exact_mod_cast hpos
    exact_mod_cast (by omega : (1 : ℤ) ≤ k)

/-- For a finite value point, the Lambda auxiliary function always has a simple pole. -/
theorem LambdaCore_order_at_value {h : ℂ → ℂ} {z₀ a b c : ℂ}
    (hh : MeromorphicAt h z₀) (hab : a ≠ b) (hac : a ≠ c) {m : ℕ}
    (hm1 : 1 ≤ m) (hm : meromorphicOrderAt (fun w => h w - a) z₀ = (m : ℤ)) :
    meromorphicOrderAt (LambdaCore a b c h) z₀ = -1 := by
  obtain ⟨A, hA, -, heq⟩ := LambdaCore_local_at_value hh hab hac hm1 hm
  apply (lambda_order_of_local_form hA heq).2.2
  apply neg_ne_zero.2
  have hmne : (m + 1 : ℕ) ≠ 0 := by omega
  exact_mod_cast hmne

/-- The Laurent form of `Λ_a(h)` for the three finite marked values. -/
theorem LambdaFun_local_at_value {h : ℂ → ℂ} {z₀ : ℂ} {a : Fin 3 → ℂ}
    (hh : MeromorphicAt h z₀) (ha : Function.Injective a) (j : Fin 3) {m : ℕ}
    (hm1 : 1 ≤ m) (hm : meromorphicOrderAt (fun w => h w - a j) z₀ = (m : ℤ)) :
    ∃ A : ℂ → ℂ, AnalyticAt ℂ A z₀ ∧ (m = 1 → A z₀ = 0) ∧
      ∀ᶠ w in 𝓝[≠] z₀,
        LambdaFun a j h w = -((m : ℂ) + 1) / (w - z₀) + A w := by
  have hab : a j ≠ a (j + 1) := fun h => by
    have hj := ha h
    fin_cases j <;> simp at hj
  have hac : a j ≠ a (j + 2) := fun h => by
    have hj := ha h
    fin_cases j <;> simp at hj
  exact LambdaCore_local_at_value hh hab hac hm1 hm

/-- At a shared finite point of type `(m,n)`, `E_a` has residue `n-m`.
At a shared simple point its analytic remainder vanishes. -/
theorem EAux_local_at_shared {f g : ℂ → ℂ} {z₀ : ℂ} {a : Fin 3 → ℂ}
    (hf : MeromorphicAt f z₀) (hg : MeromorphicAt g z₀) (ha : Function.Injective a)
    (j : Fin 3) {m n : ℕ} (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
    (hm : meromorphicOrderAt (fun w => f w - a j) z₀ = (m : ℤ))
    (hn : meromorphicOrderAt (fun w => g w - a j) z₀ = (n : ℤ)) :
    ∃ A : ℂ → ℂ, AnalyticAt ℂ A z₀ ∧ (m = 1 → n = 1 → A z₀ = 0) ∧
      ∀ᶠ w in 𝓝[≠] z₀,
        EAux a j f g w = ((n : ℂ) - (m : ℂ)) / (w - z₀) + A w := by
  obtain ⟨F, hFa, hFzero, hF⟩ := LambdaFun_local_at_value hf ha j hm1 hm
  obtain ⟨G, hGa, hGzero, hG⟩ := LambdaFun_local_at_value hg ha j hn1 hn
  refine ⟨fun w => F w - G w, hFa.sub hGa, ?_, ?_⟩
  · intro hmone hnone
    change F z₀ - G z₀ = 0
    rw [hFzero hmone, hGzero hnone, sub_self]
  · filter_upwards [hF, hG] with w hwF hwG
    simp only [EAux]
    rw [hwF, hwG]
    ring

/-- Every finite shared point is at worst a simple pole of `E_a`;
equal multiplicities remove this pole, and unequal multiplicities give order exactly `-1`. -/
theorem EAux_order_at_shared {f g : ℂ → ℂ} {z₀ : ℂ} {a : Fin 3 → ℂ}
    (hf : MeromorphicAt f z₀) (hg : MeromorphicAt g z₀) (ha : Function.Injective a)
    (j : Fin 3) {m n : ℕ} (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
    (hm : meromorphicOrderAt (fun w => f w - a j) z₀ = (m : ℤ))
    (hn : meromorphicOrderAt (fun w => g w - a j) z₀ = (n : ℤ)) :
    (-1 : WithTop ℤ) ≤ meromorphicOrderAt (EAux a j f g) z₀ ∧
      (m = n → 0 ≤ meromorphicOrderAt (EAux a j f g) z₀) ∧
      (m ≠ n → meromorphicOrderAt (EAux a j f g) z₀ = -1) := by
  obtain ⟨A, hA, -, heq⟩ := EAux_local_at_shared hf hg ha j hm1 hn1 hm hn
  have hlocal := lambda_order_of_local_form hA heq
  refine ⟨hlocal.1, ?_, ?_⟩
  · intro he
    apply hlocal.2.1
    rw [he, sub_self]
  · intro hne
    apply hlocal.2.2
    intro he
    have hnm : n = m := by exact_mod_cast (sub_eq_zero.1 he)
    exact hne hnm.symm

/-- At a common simple `a`-point, `E_a` vanishes to order at least one. -/
theorem EAux_order_ge_one_at_shared_simple {f g : ℂ → ℂ} {z₀ : ℂ} {a : Fin 3 → ℂ}
    (hf : MeromorphicAt f z₀) (hg : MeromorphicAt g z₀) (ha : Function.Injective a)
    (j : Fin 3)
    (hm : meromorphicOrderAt (fun w => f w - a j) z₀ = (1 : ℤ))
    (hn : meromorphicOrderAt (fun w => g w - a j) z₀ = (1 : ℤ)) :
    (1 : WithTop ℤ) ≤ meromorphicOrderAt (EAux a j f g) z₀ := by
  obtain ⟨A, hA, hAzero, heq⟩ :=
    EAux_local_at_shared hf hg ha j (m := 1) (n := 1) (by omega) (by omega) hm hn
  have hEA : EAux a j f g =ᶠ[𝓝[≠] z₀] A := heq.mono fun w hw => by simpa using hw
  exact lambda_order_ge_one_of_analytic_zero hA (hAzero rfl rfl) hEA

/-- The coefficient of the simple-pole term in the Lambda expansion.
The orders are integers because the local germs involved are nonzero. -/
noncomputable def LambdaCoreResidue (a b c : ℂ) (h : ℂ → ℂ) (z₀ : ℂ) : ℂ :=
  ((meromorphicOrderAt (deriv h) z₀).untop₀ : ℂ) -
    2 * ((meromorphicOrderAt (fun w => h w - a) z₀).untop₀ : ℂ) +
    ((b - a) / (b - c)) * ((meromorphicOrderAt (fun w => h w - b) z₀).untop₀ : ℂ) +
    ((a - c) / (b - c)) * ((meromorphicOrderAt (fun w => h w - c) z₀).untop₀ : ℂ)

private lemma lambda_logDeriv_local {h : ℂ → ℂ} {z₀ : ℂ}
    (hh : MeromorphicAt h z₀) (hfinite : meromorphicOrderAt h z₀ ≠ ⊤) :
    ∃ A : ℂ → ℂ, AnalyticAt ℂ A z₀ ∧
      ∀ᶠ w in 𝓝[≠] z₀,
        deriv h w / h w = ((meromorphicOrderAt h z₀).untop₀ : ℂ) / (w - z₀) + A w := by
  obtain ⟨F, hFa, hF0, hrep⟩ := (meromorphicOrderAt_eq_int_iff hh).1
    (WithTop.coe_untop₀_of_ne_top hfinite).symm
  refine ⟨fun w => deriv F w / F w, hFa.deriv.div hFa hF0, ?_⟩
  exact lambda_logDeriv_local_form hFa hF0 (hrep.mono fun w hw => by
    simpa only [smul_eq_mul] using hw)

/-- Partial fractions for the last summand in Lambda. The nonzero denominator
conditions are used only on punctured neighborhoods, never at a marked value itself. -/
theorem LambdaCore_partial_fractions {a b c x p : ℂ} (hbc : b ≠ c)
    (hxb : x - b ≠ 0) (hxc : x - c ≠ 0) :
    p * (x - a) / ((x - b) * (x - c)) =
      ((b - a) / (b - c)) * (p / (x - b)) +
        ((a - c) / (b - c)) * (p / (x - c)) := by
  field_simp [hxb, hxc, sub_ne_zero.2 hbc]
  ring

/-- Every Lambda germ is a simple-pole term plus an analytic remainder. -/
theorem LambdaCore_local {h : ℂ → ℂ} {Ω : Set ℂ} {z₀ a b c : ℂ}
    (hh : IsNonconstMeroOn h Ω) (hz : z₀ ∈ Ω) (hbc : b ≠ c) :
    ∃ A : ℂ → ℂ, AnalyticAt ℂ A z₀ ∧
      ∀ᶠ w in 𝓝[≠] z₀,
        LambdaCore a b c h w = LambdaCoreResidue a b c h z₀ / (w - z₀) + A w := by
  have hhm := hh.1 z₀ hz
  obtain ⟨A, hAa, hA⟩ := lambda_logDeriv_local hhm.deriv
    (order_deriv_of_nonconst hh hz).1
  obtain ⟨B, hBa, hB⟩ := lambda_logDeriv_local (h := fun w => h w - a)
    (hhm.sub (MeromorphicAt.const a z₀))
    (hh.2 z₀ hz a)
  obtain ⟨C, hCa, hC⟩ := lambda_logDeriv_local (h := fun w => h w - b)
    (hhm.sub (MeromorphicAt.const b z₀))
    (hh.2 z₀ hz b)
  obtain ⟨D, hDa, hD⟩ := lambda_logDeriv_local (h := fun w => h w - c)
    (hhm.sub (MeromorphicAt.const c z₀))
    (hh.2 z₀ hz c)
  have hsubderiv (d : ℂ) : deriv (fun w => h w - d) = deriv h :=
    funext fun _ => deriv_sub_const d
  rw [hsubderiv a] at hB
  rw [hsubderiv b] at hC
  rw [hsubderiv c] at hD
  have hbne := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
    (hhm.sub (MeromorphicAt.const b z₀))).1 (hh.2 z₀ hz b)
  have hcne := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
    (hhm.sub (MeromorphicAt.const c z₀))).1 (hh.2 z₀ hz c)
  refine ⟨fun w => A w - 2 * B w + ((b - a) / (b - c)) * C w +
    ((a - c) / (b - c)) * D w, ?_, ?_⟩
  · exact ((hAa.sub (analyticAt_const.mul hBa)).add
      (analyticAt_const.mul hCa)).add (analyticAt_const.mul hDa)
  · filter_upwards [hA, hB, hC, hD, hbne, hcne] with w hwA hwB hwC hwD hwb hwc
    simp only [LambdaCore]
    rw [LambdaCore_partial_fractions hbc hwb hwc, hwA, hwB, hwC, hwD]
    simp only [LambdaCoreResidue]
    ring

/-- The Lambda function has at most a simple pole at every point. -/
theorem LambdaCore_order_ge_neg_one {h : ℂ → ℂ} {Ω : Set ℂ} {z₀ a b c : ℂ}
    (hh : IsNonconstMeroOn h Ω) (hz : z₀ ∈ Ω) (hbc : b ≠ c) :
    (-1 : WithTop ℤ) ≤ meromorphicOrderAt (LambdaCore a b c h) z₀ := by
  obtain ⟨A, hA, heq⟩ := LambdaCore_local hh hz hbc (a := a)
  exact (lambda_order_of_local_form hA heq).1

/-- At a pole of any order, the Lambda residue is always `-1`. -/
theorem LambdaCoreResidue_eq_neg_one_at_pole {h : ℂ → ℂ} {Ω : Set ℂ}
    {z₀ a b c : ℂ} (hh : IsNonconstMeroOn h Ω) (hz : z₀ ∈ Ω) (hbc : b ≠ c)
    (hpole : meromorphicOrderAt h z₀ < 0) :
    LambdaCoreResidue a b c h z₀ = -1 := by
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 (order_ne_top_of_nonconst hh hz)
  have hkneg : k < 0 := by rw [← hk] at hpole; exact_mod_cast hpole
  have hk' : meromorphicOrderAt (fun w => h w - 0) z₀ = k := by
    simpa only [sub_zero] using hk.symm
  have hd := order_deriv_of_order_eq (hh.1 z₀ hz) hkneg.ne hk'
  simp only [LambdaCoreResidue, hd, order_sub_const_of_neg hpole,
    ← hk, WithTop.untop₀_coe]
  push_cast
  field_simp [sub_ne_zero.2 hbc]
  ring

/-- At a pole the Lambda function has a simple pole with residue `-1`. -/
theorem LambdaCore_local_at_pole {h : ℂ → ℂ} {Ω : Set ℂ} {z₀ a b c : ℂ}
    (hh : IsNonconstMeroOn h Ω) (hz : z₀ ∈ Ω) (hbc : b ≠ c)
    (hpole : meromorphicOrderAt h z₀ < 0) :
    ∃ A : ℂ → ℂ, AnalyticAt ℂ A z₀ ∧
      ∀ᶠ w in 𝓝[≠] z₀, LambdaCore a b c h w = -1 / (w - z₀) + A w := by
  obtain ⟨A, hA, heq⟩ := LambdaCore_local hh hz hbc (a := a)
  exact ⟨A, hA, by rwa [LambdaCoreResidue_eq_neg_one_at_pole hh hz hbc hpole] at heq⟩

/-- Every `E_a` germ is a simple-pole term plus an analytic remainder. -/
theorem EAux_local {f g : ℂ → ℂ} {Ω : Set ℂ} {z₀ : ℂ} {a : Fin 3 → ℂ}
    (hf : IsNonconstMeroOn f Ω) (hg : IsNonconstMeroOn g Ω) (hz : z₀ ∈ Ω)
    (ha : Function.Injective a) (j : Fin 3) :
    ∃ A : ℂ → ℂ, AnalyticAt ℂ A z₀ ∧
      ∀ᶠ w in 𝓝[≠] z₀,
        EAux a j f g w =
          (LambdaCoreResidue (a j) (a (j + 1)) (a (j + 2)) f z₀ -
            LambdaCoreResidue (a j) (a (j + 1)) (a (j + 2)) g z₀) / (w - z₀) + A w := by
  have hbc : a (j + 1) ≠ a (j + 2) := fun he => by
    have hj := ha he
    fin_cases j <;> simp at hj
  obtain ⟨F, hFa, hF⟩ := LambdaCore_local hf hz hbc (a := a j)
  obtain ⟨G, hGa, hG⟩ := LambdaCore_local hg hz hbc (a := a j)
  refine ⟨fun w => F w - G w, hFa.sub hGa, ?_⟩
  filter_upwards [hF, hG] with w hwF hwG
  simp only [EAux, LambdaFun]
  rw [hwF, hwG]
  ring

/-- The difference auxiliary function has at most a simple pole at every point. -/
theorem EAux_order_ge_neg_one {f g : ℂ → ℂ} {Ω : Set ℂ} {z₀ : ℂ} {a : Fin 3 → ℂ}
    (hf : IsNonconstMeroOn f Ω) (hg : IsNonconstMeroOn g Ω) (hz : z₀ ∈ Ω)
    (ha : Function.Injective a) (j : Fin 3) :
    (-1 : WithTop ℤ) ≤ meromorphicOrderAt (EAux a j f g) z₀ := by
  obtain ⟨A, hA, heq⟩ := EAux_local hf hg hz ha j
  exact (lambda_order_of_local_form hA heq).1

/-- Equal Lambda residues remove the pole of `E_a`. -/
theorem EAux_order_nonneg_of_residues_eq {f g : ℂ → ℂ} {Ω : Set ℂ}
    {z₀ : ℂ} {a : Fin 3 → ℂ}
    (hf : IsNonconstMeroOn f Ω) (hg : IsNonconstMeroOn g Ω) (hz : z₀ ∈ Ω)
    (ha : Function.Injective a) (j : Fin 3)
    (he : LambdaCoreResidue (a j) (a (j + 1)) (a (j + 2)) f z₀ =
      LambdaCoreResidue (a j) (a (j + 1)) (a (j + 2)) g z₀) :
    0 ≤ meromorphicOrderAt (EAux a j f g) z₀ := by
  obtain ⟨A, hA, heq⟩ := EAux_local hf hg hz ha j
  exact (lambda_order_of_local_form hA heq).2.1 (sub_eq_zero.2 he)

/-- Common poles make no pole of `E_a`, even if their multiplicities differ. -/
theorem EAux_order_nonneg_at_shared_pole {f g : ℂ → ℂ} {Ω : Set ℂ}
    {z₀ : ℂ} {a : Fin 3 → ℂ}
    (hf : IsNonconstMeroOn f Ω) (hg : IsNonconstMeroOn g Ω) (hz : z₀ ∈ Ω)
    (ha : Function.Injective a) (j : Fin 3)
    (hfpole : meromorphicOrderAt f z₀ < 0) (hgpole : meromorphicOrderAt g z₀ < 0) :
    0 ≤ meromorphicOrderAt (EAux a j f g) z₀ := by
  have hbc : a (j + 1) ≠ a (j + 2) := fun he => by
    have hj := ha he
    fin_cases j <;> simp at hj
  apply EAux_order_nonneg_of_residues_eq hf hg hz ha j
  rw [LambdaCoreResidue_eq_neg_one_at_pole hf hz hbc hfpole,
    LambdaCoreResidue_eq_neg_one_at_pole hg hz hbc hgpole]

/-- Equal multiplicities at any of the three shared finite values remove the pole of every
`E_a`, including the two functions based at the other marked values. -/
theorem EAux_order_nonneg_at_shared_cm {f g : ℂ → ℂ} {Ω : Set ℂ}
    {z₀ : ℂ} {a : Fin 3 → ℂ}
    (hf : IsNonconstMeroOn f Ω) (hg : IsNonconstMeroOn g Ω) (hz : z₀ ∈ Ω)
    (ha : Function.Injective a) (j k : Fin 3)
    (hpos : 0 < mult f (a k : Sphere) z₀)
    (hcm : mult f (a k : Sphere) z₀ = mult g (a k : Sphere) z₀) :
    0 ≤ meromorphicOrderAt (EAux a j f g) z₀ := by
  have hposg : 0 < mult g (a k : Sphere) z₀ := by rw [← hcm]; exact hpos
  have hford := order_sub_eq_mult hpos
  have hgord := order_sub_eq_mult hposg
  have hfderiv := order_deriv_of_order_sub (hf.1 z₀ hz) hpos hford
  have hgderiv := order_deriv_of_order_sub (hg.1 z₀ hz) hposg hgord
  have hderiv : meromorphicOrderAt (deriv f) z₀ = meromorphicOrderAt (deriv g) z₀ := by
    rw [hfderiv, hgderiv, hcm]
  have hfordpos : 0 < meromorphicOrderAt (fun w => f w - a k) z₀ := by
    rw [hford]; exact_mod_cast hpos
  have hgordpos : 0 < meromorphicOrderAt (fun w => g w - a k) z₀ := by
    rw [hgord]; exact_mod_cast hposg
  have horders (i : Fin 3) : meromorphicOrderAt (fun w => f w - a i) z₀ =
      meromorphicOrderAt (fun w => g w - a i) z₀ := by
    by_cases hik : i = k
    · subst i
      rw [hford, hgord, hcm]
    · rw [order_sub_const_eq_zero_of_pos (hf.1 z₀ hz) (ha.ne (Ne.symm hik)) hfordpos,
        order_sub_const_eq_zero_of_pos (hg.1 z₀ hz) (ha.ne (Ne.symm hik)) hgordpos]
  apply EAux_order_nonneg_of_residues_eq hf hg hz ha j
  simp only [LambdaCoreResidue, hderiv, horders]

/-- At a point away from the finite fibers and the derivative zero divisors, `E_a` is
holomorphic after removing removable singularities. -/
theorem EAux_order_nonneg_at_regular {f g : ℂ → ℂ} {Ω : Set ℂ}
    {z₀ : ℂ} {a : Fin 3 → ℂ}
    (hf : IsNonconstMeroOn f Ω) (hg : IsNonconstMeroOn g Ω) (hz : z₀ ∈ Ω)
    (ha : Function.Injective a) (j : Fin 3)
    (hfd : meromorphicOrderAt (deriv f) z₀ = 0)
    (hgd : meromorphicOrderAt (deriv g) z₀ = 0)
    (hfv : ∀ i, meromorphicOrderAt (fun w => f w - a i) z₀ = 0)
    (hgv : ∀ i, meromorphicOrderAt (fun w => g w - a i) z₀ = 0) :
    0 ≤ meromorphicOrderAt (EAux a j f g) z₀ := by
  apply EAux_order_nonneg_of_residues_eq hf hg hz ha j
  simp only [LambdaCoreResidue, hfd, hgd, hfv, hgv]

/-- A defect at the value underlying `E_a` prevents `E_a` from vanishing identically on `ℂ`. -/
theorem EAux_order_ne_top_of_defect {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hf : Meromorphic f) (hg : Meromorphic g) (ha : Function.Injective a) (j : Fin 3)
    (hdefect : ∃ z₀, IsDefect f g (a j : Sphere) z₀) (z : ℂ) :
    meromorphicOrderAt (EAux a j f g) z ≠ ⊤ := by
  obtain ⟨z₀, hd⟩ := hdefect
  have hlocal := EAux_order_at_shared (hf z₀) (hg z₀) ha j hd.1 hd.2.1
    (order_sub_eq_mult hd.1) (order_sub_eq_mult hd.2.1)
  have hfinite : meromorphicOrderAt (EAux a j f g) z₀ ≠ ⊤ := by
    rw [hlocal.2.2 hd.2.2]
    exact WithTop.coe_ne_top
  exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
    (fun y _ => meromorphicAt_EAux (hf y) (hg y) a j) isPreconnected_univ
    (mem_univ z₀) (mem_univ z) hfinite

private lemma lambda_deriv_orders_zero_at_generic {f g : ℂ → ℂ} {Ω : Set ℂ}
    {z₀ : ℂ} {a : Fin 3 → ℂ} (hp : NormalizedPair Ω f g a) (hz : z₀ ∈ Ω)
    (hfnn : 0 ≤ meromorphicOrderAt f z₀) (hgnn : 0 ≤ meromorphicOrderAt g z₀)
    (hzf : ∀ i, meromorphicOrderAt (fun w => f w - a i) z₀ = 0)
    (hzg : ∀ i, meromorphicOrderAt (fun w => g w - a i) z₀ = 0)
    (hpsi : meromorphicOrderAt (auxPsi a f g) z₀ = 0) :
    meromorphicOrderAt (deriv f) z₀ = 0 ∧ meromorphicOrderAt (deriv g) z₀ = 0 := by
  have hfm := hp.nonconst_f.1 z₀ hz
  have hgm := hp.nonconst_g.1 z₀ hz
  have hfg : MeromorphicAt (fun w => f w - g w) z₀ := hfm.sub hgm
  have hPfm : MeromorphicAt (fun w => cubicP a (f w)) z₀ := by unfold cubicP; fun_prop
  have hPgm : MeromorphicAt (fun w => cubicP a (g w)) z₀ := by unfold cubicP; fun_prop
  have hUm : MeromorphicAt (auxU a f g) z₀ := by unfold auxU cubicP; fun_prop
  have hVm : MeromorphicAt (auxV a f g) z₀ := by unfold auxV cubicP; fun_prop
  have hPf := order_cubicP_comp_eq_zero hfm a hzf
  have hPg := order_cubicP_comp_eq_zero hgm a hzg
  have hU : auxU a f g = ((fun w => f w - g w) * deriv f) *
      (fun w => cubicP a (f w))⁻¹ := by ext w; simp [auxU, div_eq_mul_inv]
  have hV : auxV a f g = ((fun w => f w - g w) * deriv g) *
      (fun w => cubicP a (g w))⁻¹ := by ext w; simp [auxV, div_eq_mul_inv]
  have hPsi : auxPsi a f g = auxU a f g * auxV a f g := rfl
  obtain ⟨dd, hdd⟩ := WithTop.ne_top_iff_exists.1 (hp.distinct z₀ hz)
  obtain ⟨e, he⟩ := WithTop.ne_top_iff_exists.1
    (order_deriv_of_nonconst hp.nonconst_f hz).1
  obtain ⟨e', he'⟩ := WithTop.ne_top_iff_exists.1
    (order_deriv_of_nonconst hp.nonconst_g hz).1
  have h1 : 0 ≤ meromorphicOrderAt (fun w => f w - g w) z₀ := by
    have hsub : (fun w => f w - g w) = f + fun w => -g w := by
      ext w
      simp [sub_eq_add_neg]
    rw [hsub]
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
  rw [hPsi, meromorphicOrderAt_mul hUm hVm, hU, hV,
    meromorphicOrderAt_mul (hfg.mul hfm.deriv) hPfm.inv,
    meromorphicOrderAt_mul hfg hfm.deriv, meromorphicOrderAt_inv,
    meromorphicOrderAt_mul (hfg.mul hgm.deriv) hPgm.inv,
    meromorphicOrderAt_mul hfg hgm.deriv, meromorphicOrderAt_inv,
    hPf, hPg, ← hdd, ← he, ← he'] at hpsi
  simp only [neg_zero, add_zero, ← WithTop.coe_add] at hpsi
  have hsum : dd + e + (dd + e') = 0 := by exact_mod_cast hpsi
  constructor
  · rw [← he]
    exact_mod_cast (by omega : e = 0)
  · rw [← he']
    exact_mod_cast (by omega : e' = 0)

/-- The only poles of `E_a` lie at a finite multiplicity defect or at a zero of `Ψ`.
The defect may occur over any of the three marked finite values. -/
theorem EAux_pole_support_on {f g : ℂ → ℂ} {Ω : Set ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair Ω f g a) (j : Fin 3) (z₀ : ℂ) (hz : z₀ ∈ Ω)
    (hneg : meromorphicOrderAt (EAux a j f g) z₀ < 0) :
    (∃ k, IsDefect f g (a k : Sphere) z₀) ∨
      0 < meromorphicOrderAt (auxPsi a f g) z₀ := by
  classical
  by_cases hdef : ∃ k, IsDefect f g (a k : Sphere) z₀
  · exact Or.inl hdef
  refine Or.inr ?_
  by_contra hpsi
  have hpsi0 : meromorphicOrderAt (auxPsi a f g) z₀ = 0 :=
    le_antisymm (not_lt.1 hpsi) (hp.order_aux hz).2.2.1
  have hfm := hp.nonconst_f.1 z₀ hz
  have hgm := hp.nonconst_g.1 z₀ hz
  by_cases hpole : 0 < mult f ⊤ z₀
  · have hpoleg : 0 < mult g ⊤ z₀ := by rw [← hp.cm_top z₀ hz]; exact hpole
    have hfpole : meromorphicOrderAt f z₀ < 0 := by
      rw [order_eq_neg_mult_top hpole]
      exact_mod_cast (show -(mult f ⊤ z₀ : ℤ) < 0 by omega)
    have hgpole : meromorphicOrderAt g z₀ < 0 := by
      rw [order_eq_neg_mult_top hpoleg]
      exact_mod_cast (show -(mult g ⊤ z₀ : ℤ) < 0 by omega)
    exact absurd hneg (not_lt.2 (EAux_order_nonneg_at_shared_pole hp.nonconst_f
      hp.nonconst_g hz hp.injective j hfpole hgpole))
  have hf0 : mult f ⊤ z₀ = 0 := by omega
  have hfnn := order_nonneg_of_mult_top_eq_zero hf0
    (order_ne_top_of_nonconst hp.nonconst_f hz)
  have hgnn := order_nonneg_of_mult_top_eq_zero
    (by rw [← hp.cm_top z₀ hz]; exact hf0) (order_ne_top_of_nonconst hp.nonconst_g hz)
  by_cases hval : ∃ k, 0 < mult f (a k : Sphere) z₀
  · obtain ⟨k, hk⟩ := hval
    have hkg := (hp.im k z₀ hz).1 hk
    have hcm : mult f (a k : Sphere) z₀ = mult g (a k : Sphere) z₀ := by
      by_contra hne
      exact hdef ⟨k, hk, hkg, hne⟩
    exact absurd hneg (not_lt.2 (EAux_order_nonneg_at_shared_cm hp.nonconst_f
      hp.nonconst_g hz hp.injective j k hk hcm))
  have hvf : ∀ i, mult f (a i : Sphere) z₀ = 0 := by
    intro i
    have hn : ¬ 0 < mult f (a i : Sphere) z₀ := fun hi => hval ⟨i, hi⟩
    omega
  have hvg : ∀ i, mult g (a i : Sphere) z₀ = 0 := by
    intro i
    by_contra hi
    have hif := (hp.im i z₀ hz).2 (Nat.pos_of_ne_zero hi)
    rw [hvf i] at hif
    exact lt_irrefl _ hif
  have hzf : ∀ i, meromorphicOrderAt (fun w => f w - a i) z₀ = 0 := fun i =>
    le_antisymm (order_sub_nonpos_of_mult_eq_zero (hvf i) (hp.nonconst_f.2 z₀ hz (a i)))
      (order_sub_const_nonneg hfm hfnn (a i))
  have hzg : ∀ i, meromorphicOrderAt (fun w => g w - a i) z₀ = 0 := fun i =>
    le_antisymm (order_sub_nonpos_of_mult_eq_zero (hvg i) (hp.nonconst_g.2 z₀ hz (a i)))
      (order_sub_const_nonneg hgm hgnn (a i))
  obtain ⟨hfd, hgd⟩ := lambda_deriv_orders_zero_at_generic hp hz hfnn hgnn hzf hzg hpsi0
  exact absurd hneg (not_lt.2 (EAux_order_nonneg_at_regular hp.nonconst_f
    hp.nonconst_g hz hp.injective j hfd hgd hzf hzg))

/-- Local Lambda counting facts for a normalized pair: all poles are simple; they lie over
defects or zeros of `Ψ`; and every defect of the selected value is a pole. -/
theorem EAux_order_on {f g : ℂ → ℂ} {Ω : Set ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair Ω f g a) (j : Fin 3) (z₀ : ℂ) (hz : z₀ ∈ Ω) :
    (-1 : WithTop ℤ) ≤ meromorphicOrderAt (EAux a j f g) z₀ ∧
      (meromorphicOrderAt (EAux a j f g) z₀ < 0 →
        (∃ k, IsDefect f g (a k : Sphere) z₀) ∨
          0 < meromorphicOrderAt (auxPsi a f g) z₀) ∧
      (IsDefect f g (a j : Sphere) z₀ → meromorphicOrderAt (EAux a j f g) z₀ = -1) := by
  refine ⟨EAux_order_ge_neg_one hp.nonconst_f hp.nonconst_g hz hp.injective j,
    EAux_pole_support_on hp j z₀ hz, ?_⟩
  intro hd
  exact (EAux_order_at_shared (hp.nonconst_f.1 z₀ hz) (hp.nonconst_g.1 z₀ hz)
    hp.injective j hd.1 hd.2.1 (order_sub_eq_mult hd.1)
      (order_sub_eq_mult hd.2.1)).2.2 hd.2.2

end ThreeIM
