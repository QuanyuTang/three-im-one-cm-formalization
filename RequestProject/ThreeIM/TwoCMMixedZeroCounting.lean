module

public import RequestProject.ThreeIM.TwoCMMixedZeroLocal
public import RequestProject.ThreeIM.TwoCMTargetSwap

/-!
# Characteristic of a reciprocal difference without poles
-/

@[expose] public section

open Filter Set Topology ValueDistribution Real

namespace ThreeIM

theorem twoCM_charT_eq_proximity_of_order_nonneg {H : ℂ → ℂ} (hH : Meromorphic H)
    (hnn : ∀ z, 0 ≤ meromorphicOrderAt H z) (r : ℝ) :
    charT H r = proximity H ⊤ r := by
  have hD : fiberDivisor H ⊤ = 0 := by
    ext z
    rw [fiberDivisor_apply (fun z _ => hH z)]
    change (((-meromorphicOrderAt H z).untop₀.toNat : ℕ) : ℤ) = 0
    have hn := untop₀_toNat_neg_eq_zero_of_nonneg (hnn z)
    exact_mod_cast hn
  have hN : logCounting H ⊤ r = 0 := by
    rw [← fiberDivisor_logCounting, hD]
    simp
  simp only [charT, characteristic, Pi.add_apply, hN, add_zero]

theorem twoCM_proximity_reciprocal_le {f : ℂ → ℂ}
    (hf : IsNonconstMeroOn f univ) (a : ℂ) :
    ∃ K : ℝ, ∀ r : ℝ, 1 ≤ r →
      proximity (fun w => (f w - a)⁻¹) ⊤ r ≤ charT f r - logCounting f (a : Sphere) r + K := by
  obtain ⟨K, hK⟩ := twoCM_charT_targetSwap_abs_le hf a
  refine ⟨K, fun r hr => ?_⟩
  have hc := (abs_le.1 (hK r hr)).2
  have he := congrFun (twoCM_logCounting_targetSwap hf.meromorphic a (a : Sphere)) r
  simp only [mobius_self] at he
  unfold charT characteristic at hc
  simp only [Pi.add_apply] at hc
  rw [he] at hc
  change proximity (fun w => (f w - a)⁻¹) ⊤ r ≤
    (proximity f ⊤ r + logCounting f ⊤ r) - logCounting f (a : Sphere) r + K
  linarith

theorem twoCM_charT_reciprocalDifference_le {f g : ℂ → ℂ}
    (hf : IsNonconstMeroOn f univ) (hg : IsNonconstMeroOn g univ)
    (a k : ℂ) (hcm : SharesCMOn univ f g (a : Sphere))
    (hnn : ∀ z, 0 ≤ meromorphicOrderAt (twoCMReciprocalDifference a k f g) z) :
    ∃ K : ℝ, ∀ r : ℝ, 1 ≤ r →
      charT (twoCMReciprocalDifference a k f g) r ≤
        charT f r + charT g r - 2 * logCounting f (a : Sphere) r + K := by
  obtain ⟨Kf, hKf⟩ := twoCM_proximity_reciprocal_le hf a
  obtain ⟨Kg, hKg⟩ := twoCM_proximity_reciprocal_le hg a
  have hN := twoCM_logCounting_eq_of_sharesCM hf.1 hg.1 hcm
  have hFi : Meromorphic (fun w => (f w - a)⁻¹) := fun z => meromorphicAt_mobius_comp (hf.meromorphic z) a
  have hGi : Meromorphic (fun w => (g w - a)⁻¹) := fun z => meromorphicAt_mobius_comp (hg.meromorphic z) a
  have hmul : Meromorphic (fun w => (-k) * (g w - a)⁻¹) :=
    fun z => (MeromorphicAt.const (-k) z).mul (hGi z)
  have hH := twoCM_meromorphic_reciprocalDifference hf.meromorphic hg.meromorphic a k
  refine ⟨Kf + Kg + log⁺ ‖-k‖ + log 2, fun r hr => ?_⟩
  have hsum := proximity_add_top_le hFi hmul r
  have hscale := proximity_const_mul_le (-k) hGi r
  have hfe := hKf r hr
  have hge := hKg r hr
  rw [← hN] at hge
  have heq : twoCMReciprocalDifference a k f g =
      (fun w => (f w - a)⁻¹) + (fun w => (-k) * (g w - a)⁻¹) := by
    ext w
    simp [twoCMReciprocalDifference, sub_eq_add_neg]
  rw [twoCM_charT_eq_proximity_of_order_nonneg hH hnn, heq]
  simp only [Pi.add_apply] at hsum
  linarith

end ThreeIM
