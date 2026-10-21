module

public import RequestProject.ThreeIM.TransportAnalytic
import Mathlib.Tactic.Ring

/-!
# Reconstructing the original maps from regular transport coordinates

The identities `W = (F-G)/τ` and `h = G/(F-G)` are used as identities of
punctured germs. If `τ`, `W`, and `h` are analytic at a point and `τ,W` are
nonzero there, these germs reconstruct analytic candidates for `F` and `G`.
The local identity theorem for meromorphic normal forms then identifies
their actual values and proves that the normal forms of `F,G` are analytic.
Thus no totalized division is evaluated at a removable singularity.

The last lemma uses the finite-order multiplicity convention of
`SharesIMOn` to deduce `h ≠ 0` from a shared zero fiber. It assumes neither
global holomorphy of the original maps nor global absence of poles.
-/

@[expose] public section

open Filter
open scoped Topology

namespace ThreeIM

/-- Regular transport coordinates reconstruct the original punctured germs.
The quotient identities are not required at the center itself. -/
theorem transport_reconstruction_germs {F G τ W h : ℂ → ℂ} {z : ℂ}
    (hτ : AnalyticAt ℂ τ z) (hτ₀ : τ z ≠ 0)
    (hW : AnalyticAt ℂ W z) (hW₀ : W z ≠ 0)
    (hWgerm : W =ᶠ[𝓝[≠] z] fun w => (F w - G w) / τ w)
    (hhgerm : h =ᶠ[𝓝[≠] z] fun w => G w / (F w - G w)) :
    (F =ᶠ[𝓝[≠] z] fun w => τ w * W w * (1 + h w)) ∧
      (G =ᶠ[𝓝[≠] z] fun w => τ w * W w * h w) := by
  have hτne : ∀ᶠ w in 𝓝[≠] z, τ w ≠ 0 :=
    (hτ.continuousAt.eventually_ne hτ₀).filter_mono nhdsWithin_le_nhds
  have hWne : ∀ᶠ w in 𝓝[≠] z, W w ≠ 0 :=
    (hW.continuousAt.eventually_ne hW₀).filter_mono nhdsWithin_le_nhds
  have hboth : ∀ᶠ w in 𝓝[≠] z,
      F w = τ w * W w * (1 + h w) ∧ G w = τ w * W w * h w := by
    filter_upwards [hτne, hWne, hWgerm, hhgerm] with w hτw hWw hcoordW hcoordh
    have hD : F w - G w ≠ 0 := by
      intro hzero
      apply hWw
      rw [hcoordW, hzero, zero_div]
    obtain ⟨hFvalue, hGvalue⟩ := transport_coordinate_values hD hτw
    rw [← hcoordW, ← hcoordh] at hFvalue hGvalue
    exact ⟨hFvalue, hGvalue⟩
  exact ⟨hboth.mono fun _ hw => hw.1, hboth.mono fun _ hw => hw.2⟩

/-- Reconstruction for meromorphic normal forms. The punctured identities
become neighborhood identities, and hence exact center values, only after
the normal-form local identity theorem has been applied. -/
theorem transport_regular_reconstruction {F G τ W h : ℂ → ℂ} {z : ℂ}
    (hF : MeromorphicNFAt F z) (hG : MeromorphicNFAt G z)
    (hτ : AnalyticAt ℂ τ z) (hτ₀ : τ z ≠ 0)
    (hW : AnalyticAt ℂ W z) (hW₀ : W z ≠ 0) (hh : AnalyticAt ℂ h z)
    (hWgerm : W =ᶠ[𝓝[≠] z] fun w => (F w - G w) / τ w)
    (hhgerm : h =ᶠ[𝓝[≠] z] fun w => G w / (F w - G w)) :
    AnalyticAt ℂ F z ∧ AnalyticAt ℂ G z ∧
      (F =ᶠ[𝓝 z] fun w => τ w * W w * (1 + h w)) ∧
      (G =ᶠ[𝓝 z] fun w => τ w * W w * h w) ∧
      F z = τ z * W z * (1 + h z) ∧ G z = τ z * W z * h z ∧
      F z - G z = τ z * W z ∧ F z - G z ≠ 0 := by
  have hFa : AnalyticAt ℂ (fun w => τ w * W w * (1 + h w)) z :=
    (hτ.mul hW).mul (analyticAt_const.add hh)
  have hGa : AnalyticAt ℂ (fun w => τ w * W w * h w) z := (hτ.mul hW).mul hh
  obtain ⟨hFgerm, hGgerm⟩ := transport_reconstruction_germs hτ hτ₀ hW hW₀ hWgerm hhgerm
  have hFnhds : F =ᶠ[𝓝 z] fun w => τ w * W w * (1 + h w) :=
    (hF.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hFa.meromorphicNFAt).mp hFgerm
  have hGnhds : G =ᶠ[𝓝 z] fun w => τ w * W w * h w :=
    (hG.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hGa.meromorphicNFAt).mp hGgerm
  have hFvalue := hFnhds.eq_of_nhds
  have hGvalue := hGnhds.eq_of_nhds
  have hDvalue : F z - G z = τ z * W z := by rw [hFvalue, hGvalue]; ring
  exact ⟨(analyticAt_congr hFnhds).mpr hFa, (analyticAt_congr hGnhds).mpr hGa,
    hFnhds, hGnhds, hFvalue, hGvalue, hDvalue,
    by rw [hDvalue]; exact mul_ne_zero hτ₀ hW₀⟩

/-- For a finite meromorphic order, the paper's `untop₀.toNat` multiplicity
is positive exactly when the order is positive. The finiteness hypothesis
must not be dropped: `untop₀` sends the top order to zero. -/
theorem transport_order_pos_iff_finite_mult_pos {o : WithTop ℤ} (ho : o ≠ ⊤) :
    0 < o ↔ 0 < o.untop₀.toNat := by
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp ho
  rw [← hk, WithTop.untop₀_coe]
  simp

/-- The shared zero fiber makes the regular transport coordinate nonzero.
The shared-fiber input is exactly positivity of the finite-value
`untop₀.toNat` multiplicities; it can be supplied by `SharesIMOn` after
translating the marked value to zero and preserving the punctured germs. -/
theorem transport_h_ne_zero_of_shared_zero {F G τ W h : ℂ → ℂ} {z : ℂ}
    (hF : MeromorphicNFAt F z) (hG : MeromorphicNFAt G z)
    (hτ : AnalyticAt ℂ τ z) (hτ₀ : τ z ≠ 0)
    (hW : AnalyticAt ℂ W z) (hW₀ : W z ≠ 0) (hh : AnalyticAt ℂ h z)
    (hWgerm : W =ᶠ[𝓝[≠] z] fun w => (F w - G w) / τ w)
    (hhgerm : h =ᶠ[𝓝[≠] z] fun w => G w / (F w - G w))
    (hFfinite : meromorphicOrderAt F z ≠ ⊤)
    (hGfinite : meromorphicOrderAt G z ≠ ⊤)
    (hshare : 0 < (meromorphicOrderAt F z).untop₀.toNat ↔
      0 < (meromorphicOrderAt G z).untop₀.toNat) : h z ≠ 0 := by
  obtain ⟨hFa, hGa, _, _, _, hGvalue, _, hD⟩ :=
    transport_regular_reconstruction hF hG hτ hτ₀ hW hW₀ hh hWgerm hhgerm
  intro hzero
  have hGzero : G z = 0 := by simpa only [hzero, mul_zero] using hGvalue
  have hGorder : meromorphicOrderAt G z ≠ 0 := by
    intro horder
    exact (hG.meromorphicOrderAt_eq_zero_iff.mp horder) hGzero
  have hGpos : 0 < meromorphicOrderAt G z :=
    lt_of_le_of_ne hGa.meromorphicOrderAt_nonneg (Ne.symm hGorder)
  have hsharedOrders : 0 < meromorphicOrderAt F z ↔ 0 < meromorphicOrderAt G z :=
    (transport_order_pos_iff_finite_mult_pos hFfinite).trans
      (hshare.trans (transport_order_pos_iff_finite_mult_pos hGfinite).symm)
  have hFpos := hsharedOrders.mpr hGpos
  have hFzero : F z = 0 := by
    by_contra hnonzero
    have horder := hF.meromorphicOrderAt_eq_zero_iff.mpr hnonzero
    exact not_lt_of_ge (le_of_eq horder) hFpos
  exact hD (by rw [hFzero, hGzero, sub_self])

end ThreeIM
