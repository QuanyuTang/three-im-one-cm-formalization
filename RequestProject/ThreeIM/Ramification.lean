module

public import RequestProject.ThreeIM.Counting
public import RequestProject.ThreeIM.DerivCharacteristic

/-!
# The pole divisor of the derivative

A pole of order `k` becomes a pole of order `k + 1` on differentiation;
elsewhere the derivative has no pole. Keeping the reduced pole count gives
the refinement needed in the second main theorem, rather than the coarser
bound `N(f') ≤ 2 N(f)`.
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

/-- Exact local pole count after differentiating a meromorphic germ. -/
theorem negPart_order_deriv_eq {f : ℂ → ℂ} {z : ℂ} (hf : MeromorphicAt f z) :
    ((meromorphicOrderAt (deriv f) z).untop₀)⁻ =
      ((meromorphicOrderAt f z).untop₀)⁻ +
        if 0 < ((meromorphicOrderAt f z).untop₀)⁻ then 1 else 0 := by
  rcases lt_or_ge (meromorphicOrderAt f z) 0 with hneg | hnonneg
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hneg.ne_top
    have hnneg : n < 0 := by
      rw [← hn] at hneg
      exact_mod_cast hneg
    have hd := order_deriv_of_order_eq (a := 0) hf hnneg.ne
      (by simpa using hn.symm)
    rw [hd, ← hn, WithTop.untop₀_coe, WithTop.untop₀_coe]
    simp only [negPart_eq_neg.2 hnneg.le,
      negPart_eq_neg.2 (show n - 1 ≤ 0 by omega), if_pos (show 0 < -n by omega)]
    omega
  · have hd := order_deriv_nonneg_of_order_nonneg hf hnonneg
    have hzero : ((meromorphicOrderAt f z).untop₀)⁻ = 0 :=
      negPart_eq_zero.2 (WithTop.untop₀_nonneg.2 hnonneg)
    have hd_zero : ((meromorphicOrderAt (deriv f) z).untop₀)⁻ = 0 :=
      negPart_eq_zero.2 (WithTop.untop₀_nonneg.2 hd)
    simp [hzero, hd_zero]

/-- The derivative's pole divisor is the full pole divisor plus its reduction. -/
theorem fiberDivisor_deriv_top_eq {f : ℂ → ℂ} (hf : MeromorphicOn f univ) :
    fiberDivisor (deriv f) ⊤ = fiberDivisor f ⊤ + reducedFiberDivisor f ⊤ := by
  have hdf : MeromorphicOn (deriv f) univ := fun z _ => (hf z (mem_univ z)).deriv
  ext z
  change (MeromorphicOn.divisor (deriv f) univ)⁻ z =
    (MeromorphicOn.divisor f univ)⁻ z +
      truncatePositiveDivisor ((MeromorphicOn.divisor f univ)⁻) z
  rw [truncatePositiveDivisor_apply]
  simp only [Function.locallyFinsuppWithin.negPart_apply,
    MeromorphicOn.divisor_apply hdf (mem_univ z),
    MeromorphicOn.divisor_apply hf (mem_univ z)]
  exact negPart_order_deriv_eq (hf z (mem_univ z))

/-- Exact integrated pole count: `N(r,∞; f') = N(r,∞; f) + N̄(r,∞; f)`. -/
theorem logCounting_deriv_top_eq {f : ℂ → ℂ} (hf : MeromorphicOn f univ)
    {r : ℝ} (hr : 0 ≤ r) :
    ValueDistribution.logCounting (deriv f) ⊤ r =
      ValueDistribution.logCounting f ⊤ r + reducedCounting f ⊤ r := by
  have hcount := congrArg
    (fun D : Function.locallyFinsupp ℂ ℤ => D.logCounting r)
    (fiberDivisor_deriv_top_eq hf)
  rw [map_add] at hcount
  simpa only [Pi.add_apply, fiberDivisor_logCounting,
    ← reducedCounting_eq_reducedFiberDivisor hf ⊤ hr] using hcount

/-- Refined characteristic estimate retaining the reduced pole count. -/
theorem charT_deriv_le_reduced_poles {f : ℂ → ℂ}
    (hf : IsNonconstMeroOn f univ) {r : ℝ} (hr : 1 ≤ r) :
    charT (deriv f) r ≤ charT f r + reducedCounting f ⊤ r +
      ValueDistribution.proximity (fun z => deriv f z / (f z - 0)) ⊤ r := by
  have hprox := proximity_deriv_top_le hf (show r ≠ 0 by linarith)
  have hcount := logCounting_deriv_top_eq hf.1 (le_trans zero_le_one hr)
  simp only [charT, ValueDistribution.characteristic, Pi.add_apply]
  linarith

end ThreeIM
