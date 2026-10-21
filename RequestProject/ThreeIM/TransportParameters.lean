module

public import RequestProject.ThreeIM.TransportProfile
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Existence of the small parameters used by real transport

The two numerical conditions in `transport_profile_continuation` are
simultaneously satisfiable. Fix `0 < r₀ ≤ ‖α‖/4`; taking
`b₀ = δ = η = θ₀ = s` sufficiently small and positive makes the stable
error tend to zero. The logarithmic error tends to
`(r₀/2)/(2‖α‖-r₀) < 1/4`. Thus parameter selection does not require an
additional mathematical hypothesis on the original functions.
-/

@[expose] public section

open Filter
open scoped Topology

namespace ThreeIM

/-- A single sufficiently small positive size supplies all four small
parameters in the explicit profile-to-continuation inequalities. -/
theorem exists_transport_parameters {a₂ a₃ A₀ B₀ : ℂ} {r₀ : ℝ}
    (hr₀ : 0 < r₀) (hrsmall : r₀ ≤ ‖A₀ * (a₂ * a₃)‖ / 4) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧
      let α := A₀ * (a₂ * a₃)
      let C := transportProfileConstant a₂ a₃ α r₀ s
      let eA := ‖A₀‖ * C * (s + s)
      let eB := ‖B₀‖ * C * s * (s + s)
      let qB := ‖B₀ * (a₂ * a₃)‖ * s
      let H := ‖α‖ + eA + qB + eB
      eA + H * s ≤ r₀ / 4 ∧
        (r₀ / 2 + eA + H * s + qB + eB) / (2 * ‖α‖ - r₀) ≤ 1 / 4 := by
  let α := A₀ * (a₂ * a₃)
  let C : ℝ → ℝ := fun s => transportProfileConstant a₂ a₃ α r₀ s
  let eA : ℝ → ℝ := fun s => ‖A₀‖ * C s * (s + s)
  let eB : ℝ → ℝ := fun s => ‖B₀‖ * C s * s * (s + s)
  let qB : ℝ → ℝ := fun s => ‖B₀ * (a₂ * a₃)‖ * s
  let H : ℝ → ℝ := fun s => ‖α‖ + eA s + qB s + eB s
  let f : ℝ → ℝ := fun s => eA s + H s * s
  let g : ℝ → ℝ := fun s =>
    (r₀ / 2 + eA s + H s * s + qB s + eB s) / (2 * ‖α‖ - r₀)
  have hC : Continuous C := by
    dsimp only [C, transportProfileConstant]
    fun_prop
  have hf : Continuous f := by
    dsimp only [f, H, eA, eB, qB]
    fun_prop
  have hg : Continuous g := by
    dsimp only [g, H, eA, eB, qB]
    fun_prop
  have hfzero : f 0 = 0 := by simp [f, H, eA, eB, qB]
  have hgzero : g 0 = (r₀ / 2) / (2 * ‖α‖ - r₀) := by simp [g, H, eA, eB, qB]
  have hden : 0 < 2 * ‖α‖ - r₀ := by
    change r₀ ≤ ‖α‖ / 4 at hrsmall
    linarith
  have hgsmall : g 0 < 1 / 4 := by
    rw [hgzero, div_lt_iff₀ hden]
    linarith
  have hfsmall : f 0 < r₀ / 4 := by rw [hfzero]; linarith
  have hfevent : ∀ᶠ s in 𝓝 (0 : ℝ), f s < r₀ / 4 :=
    hf.continuousAt.eventually (gt_mem_nhds hfsmall)
  have hgevent : ∀ᶠ s in 𝓝 (0 : ℝ), g s < 1 / 4 :=
    hg.continuousAt.eventually (gt_mem_nhds hgsmall)
  have hpos : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s := self_mem_nhdsWithin
  have hone : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < 1 :=
    (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  obtain ⟨s, hspos, hsone, hsF, hsG⟩ :=
    (hpos.and (hone.and ((hfevent.filter_mono nhdsWithin_le_nhds).and
      (hgevent.filter_mono nhdsWithin_le_nhds)))).exists
  exact ⟨s, hspos, hsone.le, hsF.le, hsG.le⟩

end ThreeIM
