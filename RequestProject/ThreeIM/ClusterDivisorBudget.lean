module

public import RequestProject.ThreeIM.ClusterDivisorCount
public import Mathlib.Analysis.Complex.ValueDistribution.CharacteristicFunction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The actual single-radius weighted divisor budget

The source's extraction window gives the factor 8R/Delta. Applying this
to the sum of positive and negative parts of the genuine meromorphic
divisor bounds absolute integer orders by the actual zero and pole
counting functions, including their compensated contribution at zero.
-/

@[expose] public section

set_option autoImplicit false

open Set Metric
open scoped BigOperators

namespace ThreeIM

private theorem zero_pole_count_le_characteristics (F : ℂ → ℂ) (R : ℝ) :
    ValueDistribution.logCounting F 0 R + ValueDistribution.logCounting F ⊤ R ≤
      ValueDistribution.characteristic F ⊤ R + ValueDistribution.characteristic F⁻¹ ⊤ R := by
  have hp : ValueDistribution.logCounting F ⊤ R ≤ ValueDistribution.characteristic F ⊤ R := by
    unfold ValueDistribution.characteristic
    simp only [Pi.add_apply]
    apply le_add_of_nonneg_left
    simpa only [Pi.zero_apply] using ValueDistribution.proximity_nonneg (f := F) (a := ⊤) R
  have hz : ValueDistribution.logCounting F 0 R ≤ ValueDistribution.characteristic F⁻¹ ⊤ R := by
    have hi : ValueDistribution.logCounting F⁻¹ ⊤ R ≤
        ValueDistribution.characteristic F⁻¹ ⊤ R := by
      unfold ValueDistribution.characteristic
      simp only [Pi.add_apply]
      apply le_add_of_nonneg_left
      simpa only [Pi.zero_apply] using ValueDistribution.proximity_nonneg (f := F⁻¹) (a := ⊤) R
    simpa only [ValueDistribution.logCounting_inv] using hi
  linarith

/-- Each unit of inner divisor multiplicity contributes at least
Delta/(8R) to the outer logarithmic count in the extraction window. -/
theorem weighted_divisor_count_le_window (s : Finset ℂ)
    (D : Function.locallyFinsupp ℂ ℤ) {ρ R Δ : ℝ}
    (hD : 0 ≤ D) (hρ : 1 ≤ ρ) (hΔ : 0 < Δ) (hwindow : ρ ≤ R - Δ / 8)
    (hs : ∀ z ∈ s, ‖z‖ ≤ ρ) :
    (∑ z ∈ s, (D z : ℝ)) ≤ 8 * R / Δ * D.logCounting R := by
  have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hρR : ρ < R := by linarith
  have hRpos : 0 < R := hρpos.trans hρR
  have hlog : Δ / (8 * R) ≤ Real.log (R / ρ) := by
    have hgap : Δ / 8 ≤ R - ρ := by linarith
    have hleft : Δ / (8 * R) ≤ (R - ρ) / R := by
      simpa only [div_div] using div_le_div_of_nonneg_right hgap hRpos.le
    have heq : 1 - (R / ρ)⁻¹ = (R - ρ) / R := by
      field_simp [hRpos.ne', hρpos.ne']
    exact hleft.trans (heq ▸ Real.one_sub_inv_le_log_of_pos (div_pos hRpos hρpos))
  have hsum : 0 ≤ ∑ z ∈ s, (D z : ℝ) :=
    Finset.sum_nonneg (fun z _ => by exact_mod_cast hD z)
  have hcount := (mul_le_mul_of_nonneg_left hlog hsum).trans
    (weighted_divisor_count_mul_log_le s D hD hρ hρR hs)
  calc
    (∑ z ∈ s, (D z : ℝ)) ≤ D.logCounting R / (Δ / (8 * R)) :=
      (le_div_iff₀ (by positivity : 0 < Δ / (8 * R))).mpr hcount
    _ = 8 * R / Δ * D.logCounting R := by
      field_simp [hΔ.ne', hRpos.ne']

/-- The absolute orders of an actual meromorphic function in the inner
window are controlled by its zero and pole counting functions at one outer
radius. No values at isolated singularities are used. -/
theorem absolute_meromorphic_orders_le_window (s : Finset ℂ) {F : ℂ → ℂ}
    (hF : MeromorphicOn F univ) {ρ R Δ : ℝ}
    (hρ : 1 ≤ ρ) (hΔ : 0 < Δ) (hwindow : ρ ≤ R - Δ / 8)
    (hs : ∀ z ∈ s, ‖z‖ ≤ ρ) :
    (∑ z ∈ s, |((meromorphicOrderAt F z).untop₀ : ℝ)|) ≤
      8 * R / Δ * (ValueDistribution.logCounting F 0 R + ValueDistribution.logCounting F ⊤ R) := by
  let D := MeromorphicOn.divisor F univ
  have hcoefficient (z : ℂ) : ((D⁺ + D⁻) z : ℝ) =
      |((meromorphicOrderAt F z).untop₀ : ℝ)| := by
    have heq : (D⁺ + D⁻) z = |D z| := by
      simpa only [Function.locallyFinsuppWithin.coe_add, Pi.add_apply,
        Function.locallyFinsuppWithin.posPart_apply, Function.locallyFinsuppWithin.negPart_apply]
        using posPart_add_negPart (D z)
    rw [heq, Int.cast_abs]
    congr 1
    exact_mod_cast MeromorphicOn.divisor_apply hF (mem_univ z)
  have hcounts : (D⁺ + D⁻).logCounting R =
      ValueDistribution.logCounting F 0 R + ValueDistribution.logCounting F ⊤ R := by
    simpa only [ValueDistribution.logCounting_zero, ValueDistribution.logCounting_top, Pi.add_apply]
      using congrFun (map_add Function.locallyFinsuppWithin.logCounting D⁺ D⁻) R
  have hbound := weighted_divisor_count_le_window s (D⁺ + D⁻)
    (add_nonneg (posPart_nonneg D) (negPart_nonneg D)) hρ hΔ hwindow hs
  simpa only [hcoefficient, hcounts] using hbound

/-- The three actual divisors have the single-radius budget appearing in
the finite-disk lemma. The Phi terms are its actual two counting functions;
the A and Psi terms are their characteristics and inverse characteristics. -/
theorem three_absolute_meromorphic_orders_le_window (s : Finset ℂ)
    {Φ A Ψ : ℂ → ℂ} (hΦ : MeromorphicOn Φ univ) (hA : MeromorphicOn A univ)
    (hΨ : MeromorphicOn Ψ univ) {ρ R Δ : ℝ}
    (hρ : 1 ≤ ρ) (hΔ : 0 < Δ) (hwindow : ρ ≤ R - Δ / 8)
    (hs : ∀ z ∈ s, ‖z‖ ≤ ρ) :
    (∑ z ∈ s, (|((meromorphicOrderAt Φ z).untop₀ : ℝ)| +
      |((meromorphicOrderAt A z).untop₀ : ℝ)| + |((meromorphicOrderAt Ψ z).untop₀ : ℝ)|)) ≤
      8 * R / Δ * (ValueDistribution.characteristic A ⊤ R +
        ValueDistribution.characteristic A⁻¹ ⊤ R +
        ValueDistribution.characteristic Ψ ⊤ R +
        ValueDistribution.characteristic Ψ⁻¹ ⊤ R +
        ValueDistribution.logCounting Φ ⊤ R + ValueDistribution.logCounting Φ⁻¹ ⊤ R) := by
  have hRpos : 0 < R := by linarith
  have hκ : 0 ≤ 8 * R / Δ := by positivity
  have hbΦ := absolute_meromorphic_orders_le_window s hΦ hρ hΔ hwindow hs
  have hbA := absolute_meromorphic_orders_le_window s hA hρ hΔ hwindow hs
  have hbΨ := absolute_meromorphic_orders_le_window s hΨ hρ hΔ hwindow hs
  have hcharA := zero_pole_count_le_characteristics A R
  have hcharΨ := zero_pole_count_le_characteristics Ψ R
  calc
    (∑ z ∈ s, (|((meromorphicOrderAt Φ z).untop₀ : ℝ)| +
        |((meromorphicOrderAt A z).untop₀ : ℝ)| + |((meromorphicOrderAt Ψ z).untop₀ : ℝ)|)) =
      (∑ z ∈ s, |((meromorphicOrderAt Φ z).untop₀ : ℝ)|) +
      (∑ z ∈ s, |((meromorphicOrderAt A z).untop₀ : ℝ)|) +
      (∑ z ∈ s, |((meromorphicOrderAt Ψ z).untop₀ : ℝ)|) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ 8 * R / Δ * (ValueDistribution.logCounting Φ 0 R + ValueDistribution.logCounting Φ ⊤ R) +
      8 * R / Δ * (ValueDistribution.logCounting A 0 R + ValueDistribution.logCounting A ⊤ R) +
      8 * R / Δ * (ValueDistribution.logCounting Ψ 0 R + ValueDistribution.logCounting Ψ ⊤ R) :=
      add_le_add (add_le_add hbΦ hbA) hbΨ
    _ = 8 * R / Δ * ((ValueDistribution.logCounting Φ 0 R + ValueDistribution.logCounting Φ ⊤ R) +
      (ValueDistribution.logCounting A 0 R + ValueDistribution.logCounting A ⊤ R) +
      (ValueDistribution.logCounting Ψ 0 R + ValueDistribution.logCounting Ψ ⊤ R)) := by ring
    _ ≤ 8 * R / Δ * ((ValueDistribution.logCounting Φ 0 R + ValueDistribution.logCounting Φ ⊤ R) +
      (ValueDistribution.characteristic A ⊤ R + ValueDistribution.characteristic A⁻¹ ⊤ R) +
      (ValueDistribution.characteristic Ψ ⊤ R + ValueDistribution.characteristic Ψ⁻¹ ⊤ R)) :=
      mul_le_mul_of_nonneg_left (by linarith) hκ
    _ = _ := by rw [ValueDistribution.logCounting_inv]; ring

end ThreeIM
