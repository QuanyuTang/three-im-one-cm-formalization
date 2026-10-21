module

public import RequestProject.ThreeIM.External
public import RequestProject.ThreeIM.Scalar

/-!
# Normality and small amplitudes (Section 7) — the scalar and tangent equations

This file states the self-contained differential-equation lemmas of Section 7:

* Lemma 7.7: elimination for the amplitude system;
* Lemma 7.8: an entire root from divisible zero orders;
* Lemma 7.9: the autonomous scalar equation has only constant meromorphic solutions;
* Lemma 7.13: classification of the tangent system (stated and proved in `Tangent.lean`).
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

/-- **Lemma 7.7** (elimination for the amplitude system), identities part.  Let `a, b, D, H`
be holomorphic on an open set `Ω`, and put `X = D H`, `Y = D (H - 1)` (so `D = X - Y`) and
`c = a - b`.  If `D X' = a X` and `D Y' = b Y` on `Ω` and the zeros of `D` are nowhere dense
in `Ω`, then `D' = c H + b`, `D H' = -c H (H - 1)` and
`c H (H - 1) H'' - c' H (H - 1) H' - (c (3H - 1) + b) (H')² = 0` on `Ω`. -/
theorem amplitude_elimination {Ω : Set ℂ} (hΩ : IsOpen Ω) {a b D H : ℂ → ℂ}
    (ha : DifferentiableOn ℂ a Ω) (hb : DifferentiableOn ℂ b Ω)
    (hD : DifferentiableOn ℂ D Ω) (hH : DifferentiableOn ℂ H Ω)
    (hzeros : ∀ z ∈ Ω, ∃ᶠ w in 𝓝[≠] z, D w ≠ 0)
    (hX : ∀ z ∈ Ω, D z * deriv (fun w => D w * H w) z = a z * (D z * H z))
    (hY : ∀ z ∈ Ω, D z * deriv (fun w => D w * (H w - 1)) z = b z * (D z * (H z - 1))) :
    (∀ z ∈ Ω, deriv D z = (a z - b z) * H z + b z) ∧
    (∀ z ∈ Ω, D z * deriv H z = -(a z - b z) * H z * (H z - 1)) ∧
    (∀ z ∈ Ω, (a z - b z) * H z * (H z - 1) * deriv (deriv H) z
      - deriv (fun w => a w - b w) z * H z * (H z - 1) * deriv H z
      - ((a z - b z) * (3 * H z - 1) + b z) * deriv H z ^ 2 = 0) := by
  have hDa := hD.analyticOnNhd hΩ
  have hHa := hH.analyticOnNhd hΩ
  have haa := ha.analyticOnNhd hΩ
  have hba := hb.analyticOnNhd hΩ
  have hDd : ∀ z ∈ Ω, DifferentiableAt ℂ D z := fun z hz => (hDa z hz).differentiableAt
  have hHd : ∀ z ∈ Ω, DifferentiableAt ℂ H z := fun z hz => (hHa z hz).differentiableAt
  -- extension of identities from `{D ≠ 0}` to `Ω` by continuity
  have ext : ∀ {F G : ℂ → ℂ}, ContinuousOn F Ω → ContinuousOn G Ω →
      (∀ z ∈ Ω, D z ≠ 0 → F z = G z) → ∀ z ∈ Ω, F z = G z := by
    intro F G hF hG hFG z hz
    have hFz : Tendsto F (𝓝[≠] z) (𝓝 (F z)) :=
      ((hF.continuousAt (hΩ.mem_nhds hz)).tendsto).mono_left nhdsWithin_le_nhds
    have hGz : Tendsto G (𝓝[≠] z) (𝓝 (G z)) :=
      ((hG.continuousAt (hΩ.mem_nhds hz)).tendsto).mono_left nhdsWithin_le_nhds
    refine tendsto_nhds_unique_of_frequently_eq hFz hGz ?_
    have hmem : ∀ᶠ w in 𝓝[≠] z, w ∈ Ω := eventually_nhdsWithin_of_eventually_nhds
      (hΩ.mem_nhds hz)
    exact ((hzeros z hz).and_eventually hmem).mono fun w ⟨h1, h2⟩ => hFG w h2 h1
  -- the two identities on `{D ≠ 0}`
  have key : ∀ z ∈ Ω, D z ≠ 0 → deriv D z = (a z - b z) * H z + b z ∧
      D z * deriv H z = -(a z - b z) * H z * (H z - 1) := by
    intro z hz hDz
    have e1 := hX z hz
    have e2 := hY z hz
    rw [deriv_fun_mul (hDd z hz) (hHd z hz)] at e1
    rw [deriv_fun_mul (hDd z hz) ((hHd z hz).sub_const 1), deriv_sub_const] at e2
    have e1' : deriv D z * H z + D z * deriv H z = a z * H z :=
      mul_left_cancel₀ hDz (by linear_combination e1)
    have e2' : deriv D z * (H z - 1) + D z * deriv H z = b z * (H z - 1) :=
      mul_left_cancel₀ hDz (by linear_combination e2)
    have h1 : deriv D z = (a z - b z) * H z + b z := by linear_combination e1' - e2'
    refine ⟨h1, ?_⟩
    rw [h1] at e1'
    linear_combination e1'
  have hcont : ∀ {F : ℂ → ℂ}, AnalyticOnNhd ℂ F Ω → ContinuousOn F Ω :=
    fun hF => hF.continuousOn
  have I1 : ∀ z ∈ Ω, deriv D z = (a z - b z) * H z + b z :=
    ext (hcont hDa.deriv) (hcont ((haa.sub hba).mul hHa |>.add hba))
      (fun z hz h => (key z hz h).1)
  have I2 : ∀ z ∈ Ω, D z * deriv H z = -(a z - b z) * H z * (H z - 1) :=
    ext (hcont (hDa.mul hHa.deriv))
      (hcont ((((haa.sub hba).neg).mul hHa).mul (hHa.sub analyticOnNhd_const)))
      (fun z hz h => (key z hz h).2)
  refine ⟨I1, I2, fun z hz => ?_⟩
  -- differentiate the second identity
  have hev : (fun w => D w * deriv H w) =ᶠ[𝓝 z]
      (fun w => -(a w - b w) * H w * (H w - 1)) :=
    Filter.eventually_of_mem (hΩ.mem_nhds hz) fun w hw => I2 w hw
  have hd := hev.deriv_eq
  have hHd' : DifferentiableAt ℂ (deriv H) z := (hHa.deriv z hz).differentiableAt
  have hcd : DifferentiableAt ℂ (fun w => a w - b w) z :=
    ((haa z hz).sub (hba z hz)).differentiableAt
  rw [deriv_fun_mul (hDd z hz) hHd'] at hd
  have hd2 : deriv (fun w => -(a w - b w) * H w * (H w - 1)) z =
      -(deriv (fun w => a w - b w) z * H z * (H z - 1) +
        (a z - b z) * (deriv H z * (H z - 1) + H z * deriv H z)) := by
    have e : (fun w => -(a w - b w) * H w * (H w - 1)) =
        fun w => -((a w - b w) * (H w * (H w - 1))) := by ext w; ring
    have hHz := hHd z hz
    have hmul : DifferentiableAt ℂ (fun w => H w * (H w - 1)) z := by fun_prop
    rw [e, deriv.fun_neg, deriv_fun_mul hcd hmul,
      deriv_fun_mul hHz (hHz.sub_const 1), deriv_sub_const]
    ring
  rw [hd2] at hd
  have i1 := I1 z hz
  have i2 := I2 z hz
  linear_combination (-deriv H z) * hd + (deriv H z) ^ 2 * i1 + (deriv (deriv H) z) * i2

/-- **Lemma 7.8** (an entire root from divisible zero orders).  If `h ≢ 0` is entire and every
zero of `h` has order divisible by `p ≥ 1`, then `h = u^p` for an entire function `u`. -/
theorem exists_entire_root {h : ℂ → ℂ} (hh : Differentiable ℂ h) (h0 : ∃ z, h z ≠ 0)
    {p : ℕ} (hp : 1 ≤ p) (hdiv : ∀ z, (p : ℕ∞) ∣ analyticOrderAt h z) :
    ∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ z, u z ^ p = h z :=
  exists_entire_root_of_dvd hh h0 hp hdiv

/-- **Lemma 7.9** (autonomous scalar equation).  For every `k ∈ ℂ`, the only meromorphic
solutions on `ℂ` of `h (h - 1) h'' - (3h - 1 + k) (h')² = 0` are constant.  (The equation is
an identity of meromorphic functions, so it is imposed off a discrete set.) -/
theorem autonomous_scalar_const {h : ℂ → ℂ} (hh : Meromorphic h) (k : ℂ)
    (heq : ∀ᶠ z in codiscrete ℂ,
      h z * (h z - 1) * deriv (deriv h) z - (3 * h z - 1 + k) * deriv h z ^ 2 = 0) :
    ∃ c : ℂ, ∀ᶠ z in codiscrete ℂ, h z = c :=
  autonomous_scalar_const_of_eq hh k heq

/-! Lemma 7.13 (classification of the tangent system) is `tangent_classification` in
`RequestProject/ThreeIM/Tangent.lean`. -/

end ThreeIM
