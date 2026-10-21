module

public import RequestProject.ThreeIM.NevanlinnaBasic
public import RequestProject.ThreeIM.Normalization

/-!
# Bounded changes of characteristic under target coordinates

Multiplication by a nonzero constant and a nondegenerate cross-ratio change
the characteristic by a bounded quantity. These estimates use only the first
main theorem and arithmetic operations, independently of sharing theorems.
-/

@[expose] public section

open Filter Set Topology ValueDistribution Real

namespace ThreeIM

private theorem transform_charT_const_mul_le {f : ℂ → ℂ} (hf : Meromorphic f)
    (hfinite : ∀ z, meromorphicOrderAt f z ≠ ⊤) {c : ℂ} (hc : c ≠ 0)
    {r : ℝ} (hr : 1 ≤ r) :
    charT (fun w => c * f w) r ≤ log⁺ ‖c‖ + charT f r := by
  have h := characteristic_mul_top_le hr (fun z => MeromorphicAt.const c z)
    (fun z => by rw [order_const_eq c hc]; exact WithTop.zero_ne_top) hf hfinite
  change charT (fun w => c * f w) r ≤ charT (fun _ => c) r + charT f r at h
  have hv : charT (fun _ => c) r = log⁺ ‖c‖ := by simp [charT, characteristic]
  rwa [hv] at h

theorem charT_const_mul_abs_le {f : ℂ → ℂ} (hf : Meromorphic f)
    (hfinite : ∀ z, meromorphicOrderAt f z ≠ ⊤) {c : ℂ} (hc : c ≠ 0)
    {r : ℝ} (hr : 1 ≤ r) :
    |charT (fun w => c * f w) r - charT f r| ≤ log⁺ ‖c‖ + log⁺ ‖c⁻¹‖ := by
  have hmf : Meromorphic (fun w => c * f w) := fun z =>
    (MeromorphicAt.const c z).mul (hf z)
  have hmfOrder : ∀ z, meromorphicOrderAt (fun w => c * f w) z ≠ ⊤ := by
    intro z
    change meromorphicOrderAt ((fun _ => c) * f) z ≠ ⊤
    rw [meromorphicOrderAt_mul (MeromorphicAt.const c z) (hf z), order_const_eq c hc,
      zero_add]
    exact hfinite z
  have hupper := transform_charT_const_mul_le hf hfinite hc hr
  have hlower := transform_charT_const_mul_le hmf hmfOrder (inv_ne_zero hc) hr
  have heq : (fun w => c⁻¹ * (c * f w)) = f := by
    ext w
    rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  rw [heq] at hlower
  rw [abs_le]
  constructor <;> linarith [Real.posLog_nonneg (x := ‖c‖), Real.posLog_nonneg (x := ‖c⁻¹‖)]

/-- A nondegenerate cross-ratio preserves Nevanlinna characteristic up to a
bounded function. Its totalized values at the poles are handled codiscretely. -/
theorem charT_crossRatio_abs_le {f : ℂ → ℂ} (hf : IsNonconstMeroOn f univ)
    {b c : ℂ} (hbc : b ≠ c) :
    ∃ C : ℝ, ∀ r : ℝ, 1 ≤ r →
      |charT (fun w => (f w - b) / (f w - c)) r - charT f r| ≤ C := by
  let D : ℂ → ℂ := fun w => f w - c
  let I : ℂ → ℂ := D⁻¹
  let H : ℂ → ℂ := fun w => (c - b) * I w
  let R : ℂ → ℂ := fun w => H w - (-1)
  have hD : Meromorphic D := fun z => (hf.meromorphic z).sub (MeromorphicAt.const c z)
  have hDn : ∀ z, meromorphicOrderAt D z ≠ ⊤ := fun z => hf.2 z (mem_univ z) c
  have hI : Meromorphic I := fun z => (hD z).inv
  have hIn : ∀ z, meromorphicOrderAt I z ≠ ⊤ := by
    intro z
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 (hDn z)
    change meromorphicOrderAt D⁻¹ z ≠ ⊤
    rw [meromorphicOrderAt_inv, ← hn, ← WithTop.LinearOrderedAddCommGroup.coe_neg]
    exact WithTop.coe_ne_top
  have hH : Meromorphic H := fun z => (MeromorphicAt.const (c - b) z).mul (hI z)
  have hDR : (fun w => (f w - b) / (f w - c)) =ᶠ[codiscrete ℂ] R := by
    filter_upwards [eventually_ne_zero_of_order_ne_top hD hDn] with w hw
    change f w - c ≠ 0 at hw
    dsimp only [R, H, I, D, Pi.inv_apply]
    field_simp
    ring
  let K : ℝ := max |log ‖D 0‖| |log ‖meromorphicTrailingCoeffAt D 0‖|
  refine ⟨(log⁺ ‖(-1 : ℂ)‖ + log 2) + (log⁺ ‖c - b‖ + log⁺ ‖(c - b)⁻¹‖) +
    K + (log⁺ ‖c‖ + log 2), fun r hr => ?_⟩
  have hshift := abs_characteristic_sub_characteristic_shift_le (a₀ := c) (r := r) hf.meromorphic
  have hinv := characteristic_sub_characteristic_inv_le (R := r) hD
  have hscale := charT_const_mul_abs_le hI hIn (sub_ne_zero.2 hbc.symm) hr
  have hfinal := abs_characteristic_sub_characteristic_shift_le (a₀ := (-1 : ℂ)) (r := r) hH
  have hratio : charT (fun w => (f w - b) / (f w - c)) r = charT R r :=
    characteristic_congr_codiscrete hDR (by linarith)
  change |charT f r - charT D r| ≤ log⁺ ‖c‖ + log 2 at hshift
  change |charT D r - charT I r| ≤ K at hinv
  change |charT H r - charT I r| ≤ log⁺ ‖c - b‖ + log⁺ ‖(c - b)⁻¹‖ at hscale
  change |charT H r - charT R r| ≤ log⁺ ‖(-1 : ℂ)‖ + log 2 at hfinal
  rw [hratio]
  rw [abs_sub_comm] at hshift hinv hfinal
  have htri1 := abs_sub_le (charT R r) (charT H r) (charT f r)
  have htri2 := abs_sub_le (charT H r) (charT I r) (charT f r)
  have htri3 := abs_sub_le (charT I r) (charT D r) (charT f r)
  linarith

end ThreeIM
