module

public import RequestProject.ThreeIM.SharedValueCounting
public import RequestProject.ThreeIM.ThetaLocal

/-! # The actual ratio divisor is charged to the Mues zero divisor -/

@[expose] public section

set_option autoImplicit false

open Set Filter ValueDistribution Real Topology

namespace ThreeIM

/-- A logarithmic derivative has at most a simple pole, supported on the
nonzero divisor of its original meromorphic germ. The identically zero
logarithmic derivative has top order and contributes zero pole order. -/
theorem logDeriv_order_negPart_le_abs_order {Φ : ℂ → ℂ} {z : ℂ}
    (hΦ : MeromorphicAt Φ z) (hfin : meromorphicOrderAt Φ z ≠ ⊤) :
    ((meromorphicOrderAt (logDeriv Φ) z).untop₀)⁻ ≤
      ((meromorphicOrderAt Φ z).untop₀)⁺ + ((meromorphicOrderAt Φ z).untop₀)⁻ := by
  by_cases htop : meromorphicOrderAt (logDeriv Φ) z = ⊤
  · simpa [htop] using add_nonneg (posPart_nonneg (meromorphicOrderAt Φ z).untop₀)
      (negPart_nonneg (meromorphicOrderAt Φ z).untop₀)
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hfin
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 htop
  obtain ⟨E, hE, hrep⟩ := logDeriv_local hΦ hn.symm
  have hrep' : ∀ᶠ w in 𝓝[≠] z, logDeriv Φ w = (n : ℂ) / (w - z) + E w := by
    simpa only [logDeriv_apply] using hrep
  have horder := order_of_local_form hE hrep'
  have hm1 : (-1 : ℤ) ≤ m := by
    have h := horder.1
    rw [← hm] at h
    exact WithTop.coe_le_coe.mp h
  have hm0 : n = 0 → (0 : ℤ) ≤ m := by
    intro hn0
    have h := horder.2.1 (by simp [hn0])
    rw [← hm] at h
    exact_mod_cast h
  rw [← hm, ← hn]
  simp only [WithTop.untop₀_coe, posPart_def, negPart_def]
  omega

/-- The pole count of a logarithmic derivative is bounded by the sum of
zero and pole counts of its source, including the compensated origin. -/
theorem logCounting_logDeriv_top_le_zero_pole {Φ : ℂ → ℂ}
    (hΦ : Meromorphic Φ) (hfin : ∀ z, meromorphicOrderAt Φ z ≠ ⊤)
    {r : ℝ} (hr : 1 ≤ r) :
    logCounting (logDeriv Φ) ⊤ r ≤ logCounting Φ 0 r + logCounting Φ ⊤ r := by
  have hA : MeromorphicOn (logDeriv Φ) univ := fun z _ => (hΦ z).deriv.div (hΦ z)
  have hd : (MeromorphicOn.divisor (logDeriv Φ) univ)⁻ ≤
      (MeromorphicOn.divisor Φ univ)⁺ + (MeromorphicOn.divisor Φ univ)⁻ := by
    intro z
    change (MeromorphicOn.divisor (logDeriv Φ) univ)⁻ z ≤
      (MeromorphicOn.divisor Φ univ)⁺ z + (MeromorphicOn.divisor Φ univ)⁻ z
    rw [Function.locallyFinsuppWithin.negPart_apply, Function.locallyFinsuppWithin.posPart_apply,
      Function.locallyFinsuppWithin.negPart_apply, MeromorphicOn.divisor_apply hA (mem_univ z),
      MeromorphicOn.divisor_apply (fun w _ => hΦ w) (mem_univ z)]
    exact logDeriv_order_negPart_le_abs_order (hΦ z) (hfin z)
  have h := Function.locallyFinsuppWithin.logCounting_le hd hr
  rw [map_add] at h
  simpa only [logCounting_top, logCounting_zero, Pi.add_apply] using h

/-- U and V have nonnegative finite orders, so |ord(U/V)| ≤ ord(UV).
The assertion concerns germs and does not evaluate raw auxiliaries at a
marked point. It needs no growth, periodicity, or selection assumption. -/
theorem NormalizedPair.auxPhi_divisor_abs_le_auxPsi
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} (hp : NormalizedPair univ f g a) :
    (MeromorphicOn.divisor (auxPhi a f g) univ)⁺ +
      (MeromorphicOn.divisor (auxPhi a f g) univ)⁻ ≤
        (MeromorphicOn.divisor (auxPsi a f g) univ)⁺ := by
  intro z
  have horders := hp.order_aux (mem_univ z)
  obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.1 horders.1.2
  obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.1 horders.2.1.2
  have hu0 : (0 : ℤ) ≤ u := by
    have h := horders.1.1
    rw [← hu] at h
    exact_mod_cast h
  have hv0 : (0 : ℤ) ≤ v := by
    have h := horders.2.1.1
    rw [← hv] at h
    exact_mod_cast h
  have hPhi : meromorphicOrderAt (auxPhi a f g) z = ((u - v : ℤ) : WithTop ℤ) := by
    have heq : auxPhi a f g = auxU a f g * (auxV a f g)⁻¹ := by
      ext w
      exact div_eq_mul_inv _ _
    rw [heq, meromorphicOrderAt_mul (hp.meromorphic_auxU z) (hp.meromorphic_auxV z).inv,
      meromorphicOrderAt_inv, ← hu, ← hv, ← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add]
    simp only [sub_eq_add_neg]
  have hPsi : meromorphicOrderAt (auxPsi a f g) z = ((u + v : ℤ) : WithTop ℤ) := by
    change meromorphicOrderAt (auxU a f g * auxV a f g) z = _
    rw [meromorphicOrderAt_mul (hp.meromorphic_auxU z) (hp.meromorphic_auxV z),
      ← hu, ← hv, ← WithTop.coe_add]
  change (MeromorphicOn.divisor (auxPhi a f g) univ)⁺ z +
    (MeromorphicOn.divisor (auxPhi a f g) univ)⁻ z ≤
      (MeromorphicOn.divisor (auxPsi a f g) univ)⁺ z
  rw [Function.locallyFinsuppWithin.posPart_apply, Function.locallyFinsuppWithin.negPart_apply,
    Function.locallyFinsuppWithin.posPart_apply,
    MeromorphicOn.divisor_apply (fun w _ => hp.meromorphic_auxPhi w) (mem_univ z),
    MeromorphicOn.divisor_apply (fun w _ => hp.meromorphic_auxPsi w) (mem_univ z), hPhi, hPsi]
  simp only [WithTop.untop₀_coe, posPart_def, negPart_def]
  omega

/-- Both zero and pole counts of the actual ratio are controlled by zeros
of the entire Mues function, with the compensated origin contribution. -/
theorem NormalizedPair.auxPhi_zero_pole_count_le_auxPsi
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} (hp : NormalizedPair univ f g a)
    {r : ℝ} (hr : 1 ≤ r) :
    logCounting (auxPhi a f g) ⊤ r + logCounting (auxPhi a f g)⁻¹ ⊤ r ≤
      logCounting (auxPsi a f g) 0 r := by
  have h := Function.locallyFinsuppWithin.logCounting_le hp.auxPhi_divisor_abs_le_auxPsi hr
  rw [map_add] at h
  rw [logCounting_inv, logCounting_top, logCounting_zero, logCounting_zero]
  simpa only [Pi.add_apply, add_comm] using h

/-- The source coefficient budget's two ratio-count terms are O(pairL),
using the already proved Mues estimate and first main theorem. -/
theorem NormalizedPair.auxPhi_zero_pole_count_le_pairL
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} (hp : NormalizedPair univ f g a) :
    ∃ C : ℝ, OutsideFiniteMeasure fun r =>
      logCounting (auxPhi a f g) ⊤ r + logCounting (auxPhi a f g)⁻¹ ⊤ r ≤ C * pairL f g r := by
  obtain ⟨C, hC⟩ := logCounting_auxPsi_zero_le hp
  exact ⟨C, hC.mono fun r hr h => (hp.auxPhi_zero_pole_count_le_auxPsi hr).trans h⟩

/-- The actual A=Phi'/Phi pole count is also charged to Mues zeros. -/
theorem NormalizedPair.logCounting_logDeriv_auxPhi_le_auxPsi
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} (hp : NormalizedPair univ f g a)
    {r : ℝ} (hr : 1 ≤ r) :
    logCounting (logDeriv (auxPhi a f g)) ⊤ r ≤ logCounting (auxPsi a f g) 0 r := by
  have hfin : ∀ z, meromorphicOrderAt (auxPhi a f g) z ≠ ⊤ := by
    intro z
    have hu := (hp.order_aux (mem_univ z)).1.2
    have hv := (hp.order_aux (mem_univ z)).2.1.2
    have heq : auxPhi a f g = auxU a f g * (auxV a f g)⁻¹ := by
      ext w
      exact div_eq_mul_inv _ _
    rw [heq, meromorphicOrderAt_mul (hp.meromorphic_auxU z) (hp.meromorphic_auxV z).inv,
      meromorphicOrderAt_inv, ← WithTop.coe_untop₀_of_ne_top hu,
      ← WithTop.coe_untop₀_of_ne_top hv, ← WithTop.LinearOrderedAddCommGroup.coe_neg,
      ← WithTop.coe_add]
    exact WithTop.coe_ne_top
  have h := logCounting_logDeriv_top_le_zero_pole hp.meromorphic_auxPhi hfin hr
  have h2 := hp.auxPhi_zero_pole_count_le_auxPsi hr
  rw [logCounting_inv] at h2
  linarith only [h, h2]

end ThreeIM
