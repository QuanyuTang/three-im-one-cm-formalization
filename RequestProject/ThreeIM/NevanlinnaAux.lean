module

public import RequestProject.ThreeIM.Mues
public import RequestProject.ThreeIM.Covariance
public import RequestProject.ThreeIM.Growth
public import RequestProject.ThreeIM.Local

/-!
# Auxiliary Nevanlinna-theory lemmas for normalized pairs

Generic facts about meromorphic functions on `ℂ`, proximity functions and sets of finite
measure, and basic facts about the auxiliary functions `U, V, Ψ, Φ` of a normalized pair, used
in the proofs of Lemmas 4.5 and 4.10.
-/

@[expose] public section

open Filter Set Topology ValueDistribution Real MeasureTheory

namespace ThreeIM

/-! ### Generic helpers -/

/-- `m(r, F²) = 2 m(r, F)`. -/
lemma proximity_sq (F : ℂ → ℂ) (r : ℝ) :
    proximity (fun z => F z ^ 2) ⊤ r = 2 * proximity F ⊤ r := by
  rw [proximity_top, proximity_top]
  have : (fun z => log⁺ ‖F z ^ 2‖) = (2 : ℝ) • fun z => log⁺ ‖F z‖ := by
    ext z; simp [norm_pow, Real.posLog_pow]
  rw [this, circleAverage_smul, smul_eq_mul]

/-- Integrating a pointwise bound that holds off a discrete set. -/
lemma proximity_le_of_eventually {F G₁ G₂ : ℂ → ℂ} (hF : Meromorphic F) (hG₁ : Meromorphic G₁)
    (hG₂ : Meromorphic G₂) {K k₁ k₂ : ℝ} (hK : 0 ≤ K) (hk₁ : 0 ≤ k₁) (hk₂ : 0 ≤ k₂)
    (h : ∀ᶠ z in codiscrete ℂ, log⁺ ‖F z‖ ≤ K + k₁ * log⁺ ‖G₁ z‖ + k₂ * log⁺ ‖G₂ z‖)
    {r : ℝ} (hr : r ≠ 0) :
    proximity F ⊤ r ≤ K + k₁ * proximity G₁ ⊤ r + k₂ * proximity G₂ ⊤ r := by
  classical
  set B : ℂ → ℝ := fun z => K + k₁ * log⁺ ‖G₁ z‖ + k₂ * log⁺ ‖G₂ z‖ with hB
  set F' : ℂ → ℂ := fun z => if log⁺ ‖F z‖ ≤ B z then F z else 0 with hF'
  have hFF' : F =ᶠ[codiscrete ℂ] F' := h.mono fun z hz => by
    show F z = if log⁺ ‖F z‖ ≤ B z then F z else 0
    rw [if_pos hz]
  have hF'm : Meromorphic F' := fun x =>
    (hF x).congr ((codiscrete_iff_nhdsNE.1 hFF') x)
  have hpt : ∀ z, log⁺ ‖F' z‖ ≤ B z := by
    intro z
    by_cases hz : log⁺ ‖F z‖ ≤ B z
    · show log⁺ ‖(if log⁺ ‖F z‖ ≤ B z then F z else 0)‖ ≤ B z
      rw [if_pos hz]; exact hz
    · show log⁺ ‖(if log⁺ ‖F z‖ ≤ B z then F z else 0)‖ ≤ B z
      rw [if_neg hz, norm_zero, Real.posLog_zero]
      exact add_nonneg (add_nonneg hK (mul_nonneg hk₁ Real.posLog_nonneg))
        (mul_nonneg hk₂ Real.posLog_nonneg)
  rw [proximity_congr_codiscrete hFF' hr, proximity_top, proximity_top, proximity_top]
  have hi1 := circleIntegrable_posLog_norm_meromorphicOn (c := 0) (R := r) (fun x _ => hG₁ x)
  have hi2 := circleIntegrable_posLog_norm_meromorphicOn (c := 0) (R := r) (fun x _ => hG₂ x)
  have hi1' : CircleIntegrable (k₁ • fun z => log⁺ ‖G₁ z‖) 0 r := hi1.const_smul
  have hi2' : CircleIntegrable (k₂ • fun z => log⁺ ‖G₂ z‖) 0 r := hi2.const_smul
  have hcK : CircleIntegrable (fun _ => K) 0 r := circleIntegrable_const K 0 r
  calc circleAverage (fun z => log⁺ ‖F' z‖) 0 r ≤ circleAverage B 0 r := by
        apply circleAverage_mono
        · exact circleIntegrable_posLog_norm_meromorphicOn (fun x _ => hF'm x)
        · exact (hcK.add hi1').add hi2'
        · exact fun z _ => hpt z
    _ = _ := by
        show circleAverage ((fun _ => K) + (k₁ • fun z => log⁺ ‖G₁ z‖) +
          (k₂ • fun z => log⁺ ‖G₂ z‖)) 0 r = _
        rw [circleAverage_add (hcK.add hi1') hi2', circleAverage_add hcK hi1',
          circleAverage_const, circleAverage_smul, circleAverage_smul, smul_eq_mul, smul_eq_mul]

/-- Intersection of two properties holding outside sets of finite measure. -/
lemma OutsideFiniteMeasure.and {P Q : ℝ → Prop} (hP : OutsideFiniteMeasure P)
    (hQ : OutsideFiniteMeasure Q) : OutsideFiniteMeasure fun r => P r ∧ Q r := by
  obtain ⟨E, hEm, hEv, r₀, hr₀⟩ := hP
  obtain ⟨E', hEm', hEv', r₁, hr₁⟩ := hQ
  refine ⟨E ∪ E', hEm.union hEm', lt_of_le_of_lt (measure_union_le _ _)
    (ENNReal.add_lt_top.2 ⟨hEv, hEv'⟩), max r₀ r₁, fun r hr hrE => ?_⟩
  simp only [mem_union, not_or] at hrE
  exact ⟨hr₀ r (le_trans (le_max_left _ _) hr) hrE.1,
    hr₁ r (le_trans (le_max_right _ _) hr) hrE.2⟩

lemma OutsideFiniteMeasure.mono {P Q : ℝ → Prop} (hP : OutsideFiniteMeasure P)
    (h : ∀ r, 1 ≤ r → P r → Q r) : OutsideFiniteMeasure Q := by
  obtain ⟨E, hEm, hEv, r₀, hr₀⟩ := hP
  exact ⟨E, hEm, hEv, max r₀ 1, fun r hr hrE =>
    h r (le_trans (le_max_right _ _) hr) (hr₀ r (le_trans (le_max_left _ _) hr) hrE)⟩

/-- A bound `T ≤ C (log (e + r T) + log r)` outside a set of finite measure is incompatible
with linear growth of `T`. -/
lemma false_of_linear_growth {T : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hT : ∀ᶠ r in atTop, c * r ≤ T r) {C : ℝ}
    (hb : OutsideFiniteMeasure fun r => T r ≤ C * (Real.log (Real.exp 1 + r * T r) + log r)) :
    False := by
  obtain ⟨E, hEm, hEv, r₀, hr₀⟩ := hb
  have hTtop : Tendsto T atTop atTop :=
    tendsto_atTop_mono' atTop hT (tendsto_id.const_mul_atTop hc)
  have hlim := log_isLittleO_of_linear_growth hc hT
  set K : ℝ := 2 * |C| + 1 with hK
  have hKpos : 0 < K := by positivity
  have hev1 : ∀ᶠ r in atTop, Real.log (Real.exp 1 + r * T r) / T r < 1 / K :=
    hlim.eventually (gt_mem_nhds (by positivity))
  have hev : ∀ᶠ r in atTop, C * (Real.log (Real.exp 1 + r * T r) + log r) < T r := by
    filter_upwards [hev1, hTtop.eventually_ge_atTop 1, eventually_ge_atTop (1 : ℝ)]
      with r h1 hT1 hr1
    have hTpos : 0 < T r := by linarith
    set L := Real.log (Real.exp 1 + r * T r)
    have hL0 : 0 ≤ L := Real.log_nonneg (by nlinarith [Real.add_one_le_exp 1])
    have hlogr : log r ≤ L := Real.log_le_log (by linarith)
      (by nlinarith [Real.exp_pos 1])
    have hKL : K * L < T r := by
      rw [div_lt_div_iff₀ hTpos hKpos] at h1; linarith
    have hlr0 : 0 ≤ log r := Real.log_nonneg hr1
    calc C * (L + log r) ≤ |C| * (L + log r) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
      _ ≤ |C| * (2 * L) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg C)
      _ ≤ K * L := by rw [hK]; nlinarith [abs_nonneg C]
      _ < T r := hKL
  obtain ⟨R, hR⟩ := eventually_atTop.1 hev
  obtain ⟨r₁, hr₁⟩ := exists_not_mem_of_finite_measure hEm hEv
  obtain ⟨r, hr, -, hrE⟩ := hr₁ (max (max R r₀) r₁) (le_max_right _ _)
  have h1 := hr₀ r (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hr) hrE
  have h2 := hR r (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hr)
  linarith

/-- If `F` is constant on a punctured neighbourhood of `x`, so is `F' = 0`. -/
lemma deriv_eventually_zero_of_eventually_const {F : ℂ → ℂ} {x c₀ : ℂ}
    (h : ∀ᶠ y in 𝓝[≠] x, F y = c₀) : ∀ᶠ w in 𝓝[≠] x, deriv F w = 0 := by
  have h2 := eventually_eventually_nhdsWithin.2 h
  filter_upwards [h2, self_mem_nhdsWithin] with w hw hwx
  have hw' : ∀ᶠ y in 𝓝 w, F y = c₀ := by
    rwa [nhdsWithin_eq_nhds.2 (isOpen_compl_singleton.mem_nhds hwx)] at hw
  have hEq : F =ᶠ[𝓝 w] fun _ => c₀ := hw'
  rw [hEq.deriv_eq]; simp

/-- `log (e + r S) ≤ log (e + r T) + log 3 + log r` when `0 ≤ S ≤ 2T + 1`, `r ≥ 1`. -/
lemma log_le_of_le_two_mul_add_one {r S T : ℝ} (hr : 1 ≤ r) (hT : 0 ≤ T) (hS0 : 0 ≤ S)
    (hS : S ≤ 2 * T + 1) :
    Real.log (Real.exp 1 + r * S) ≤ Real.log (Real.exp 1 + r * T) + log 3 + log r := by
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have he1 : 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have a1 : r * S ≤ r * (2 * T + 1) := mul_le_mul_of_nonneg_left hS (by linarith)
  have a2 : Real.exp 1 ≤ Real.exp 1 * r := le_mul_of_one_le_right he.le hr
  have a3 : r ≤ Real.exp 1 * r := le_mul_of_one_le_left (by linarith) he1
  have a4 : 0 ≤ r * T * (3 * r - 2) := mul_nonneg (mul_nonneg (by linarith) hT) (by linarith)
  have h1 : Real.exp 1 + r * S ≤ (Real.exp 1 + r * T) * 3 * r := by nlinarith
  rw [← Real.log_mul (by positivity) (by norm_num), ← Real.log_mul (by positivity) (by positivity)]
  exact Real.log_le_log (by positivity) h1

section PairAux

variable {a : Fin 3 → ℂ} {f g : ℂ → ℂ}

lemma NormalizedPair.meromorphic_auxU (hp : NormalizedPair univ f g a) :
    Meromorphic (auxU a f g) := fun x => by
  have := hp.nonconst_f.meromorphic x; have := (hp.nonconst_f.meromorphic x).deriv
  have := hp.nonconst_g.meromorphic x
  unfold auxU cubicP; fun_prop

lemma NormalizedPair.meromorphic_auxV (hp : NormalizedPair univ f g a) :
    Meromorphic (auxV a f g) := fun x => by
  have := hp.nonconst_f.meromorphic x; have := (hp.nonconst_g.meromorphic x).deriv
  have := hp.nonconst_g.meromorphic x
  unfold auxV cubicP; fun_prop

lemma NormalizedPair.meromorphic_auxPsi (hp : NormalizedPair univ f g a) :
    Meromorphic (auxPsi a f g) := fun x =>
  (hp.meromorphic_auxU x).mul (hp.meromorphic_auxV x)

lemma NormalizedPair.meromorphic_auxPhi (hp : NormalizedPair univ f g a) :
    Meromorphic (auxPhi a f g) := fun x =>
  (hp.meromorphic_auxU x).div (hp.meromorphic_auxV x)

lemma NormalizedPair.eventually_auxU_ne_zero (hp : NormalizedPair univ f g a) :
    ∀ᶠ z in codiscrete ℂ, auxU a f g z ≠ 0 :=
  eventually_ne_zero_of_order_ne_top hp.meromorphic_auxU
    fun z => (hp.order_aux (mem_univ z)).1.2

lemma NormalizedPair.eventually_auxV_ne_zero (hp : NormalizedPair univ f g a) :
    ∀ᶠ z in codiscrete ℂ, auxV a f g z ≠ 0 :=
  eventually_ne_zero_of_order_ne_top hp.meromorphic_auxV
    fun z => (hp.order_aux (mem_univ z)).2.1.2

lemma NormalizedPair.eventually_auxPsi_ne_zero (hp : NormalizedPair univ f g a) :
    ∀ᶠ z in codiscrete ℂ, auxPsi a f g z ≠ 0 :=
  eventually_ne_zero_of_order_ne_top hp.meromorphic_auxPsi
    fun z => (hp.order_aux (mem_univ z)).2.2.2

/-- The logarithmic derivative lemma for the members of a pair, with error `O(L)`. -/
lemma proximity_logDeriv_le_pairL (hp : NormalizedPair univ f g a) (b : ℂ) :
    ∃ C : ℝ, OutsideFiniteMeasure fun r =>
      proximity (fun z => deriv f z / (f z - b)) ⊤ r ≤ C * pairL f g r ∧
      proximity (fun z => deriv g z / (g z - b)) ⊤ r ≤ C * pairL f g r := by
  obtain ⟨Cf, hCf⟩ := log_derivative_estimate hp.nonconst_f b
  obtain ⟨Cg, hCg⟩ := log_derivative_estimate hp.nonconst_g b
  refine ⟨|Cf| + |Cg|, (hCf.and hCg).mono fun r hr ⟨h1, h2⟩ => ⟨?_, ?_⟩⟩
  · have h3 := log_charT_le_pairL_left (f := f) (g := g) hr
    have h4 : 0 ≤ Real.log (Real.exp 1 + r * charT f r) :=
      Real.log_nonneg (by nlinarith [charT_nonneg (h := f) hr, Real.add_one_le_exp 1])
    calc _ ≤ Cf * Real.log (Real.exp 1 + r * charT f r) := h1
      _ ≤ (|Cf| + |Cg|) * Real.log (Real.exp 1 + r * charT f r) :=
          mul_le_mul_of_nonneg_right (by linarith [le_abs_self Cf, abs_nonneg Cg]) h4
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)
  · have h3 := log_charT_le_pairL_right (f := f) (g := g) hr
    have h4 : 0 ≤ Real.log (Real.exp 1 + r * charT g r) :=
      Real.log_nonneg (by nlinarith [charT_nonneg (h := g) hr, Real.add_one_le_exp 1])
    calc _ ≤ Cg * Real.log (Real.exp 1 + r * charT g r) := h2
      _ ≤ (|Cf| + |Cg|) * Real.log (Real.exp 1 + r * charT g r) :=
          mul_le_mul_of_nonneg_right (by linarith [le_abs_self Cg, abs_nonneg Cf]) h4
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)

/-- A normalized pair is distinct off a discrete set. -/
lemma NormalizedPair.eventually_ne (hp : NormalizedPair univ f g a) :
    ∀ᶠ z in codiscrete ℂ, f z ≠ g z := by
  have := eventually_ne_zero_of_order_ne_top (F := fun z => f z - g z)
    (fun x => (hp.nonconst_f.meromorphic x).sub (hp.nonconst_g.meromorphic x))
    fun z => hp.distinct z (mem_univ z)
  exact this.mono fun z hz => sub_ne_zero.1 hz

/-- First main theorem for the entire function `Ψ`: `m(r, 1/Ψ) ≤ m(r, Ψ) + O(1)`. -/
lemma proximity_inv_auxPsi_le (hp : NormalizedPair univ f g a) :
    ∃ K : ℝ, ∀ r : ℝ, 1 ≤ r →
      proximity (fun z => (auxPsi a f g z)⁻¹) ⊤ r ≤ proximity (auxPsi a f g) ⊤ r + K := by
  set Ψ := auxPsi a f g with hΨ
  have hΨm : Meromorphic Ψ := hp.meromorphic_auxPsi
  set H := toMeromorphicNFOn Ψ univ
  have hΨH : Ψ =ᶠ[codiscrete ℂ] H := toMeromorphicNFOn_eqOn_codiscrete (fun x _ => hΨm x)
  have hHa : ∀ x, AnalyticAt ℂ H x := by
    intro x
    apply (meromorphicNFOn_toMeromorphicNFOn Ψ univ (mem_univ x)).meromorphicOrderAt_nonneg_iff_analyticAt.1
    have hΨm' : MeromorphicOn Ψ univ := fun y _ => hΨm y
    rw [meromorphicOrderAt_congr (hΨm'.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ x))]
    exact (hp.order_aux (mem_univ x)).2.2.1
  have hlcH : logCounting H ⊤ = 0 := by
    have := logCounting_add_analyticOn (f := (0 : ℂ → ℂ)) (g := H)
      (fun x => analyticAt_const.meromorphicAt) (fun x _ => (hHa x).analyticWithinAt)
    rw [zero_add] at this
    rw [this, logCounting_const_zero]
  have hlc : logCounting Ψ ⊤ = 0 := by
    rw [logCounting_congr_codiscrete hΨH, hlcH]
  refine ⟨max |log ‖Ψ 0‖| |log ‖meromorphicTrailingCoeffAt Ψ 0‖|, fun r hr => ?_⟩
  have h1 := characteristic_sub_characteristic_inv_le hΨm (R := r)
  have h2 : 0 ≤ logCounting Ψ⁻¹ ⊤ r := logCounting_nonneg hr
  have h3 : characteristic Ψ ⊤ r = proximity Ψ ⊤ r := by
    simp [characteristic, hlc]
  have h4 : characteristic Ψ⁻¹ ⊤ r = proximity Ψ⁻¹ ⊤ r + logCounting Ψ⁻¹ ⊤ r := rfl
  have h5 := neg_abs_le (characteristic Ψ ⊤ r - characteristic Ψ⁻¹ ⊤ r)
  show proximity Ψ⁻¹ ⊤ r ≤ _
  linarith

end PairAux

end ThreeIM
