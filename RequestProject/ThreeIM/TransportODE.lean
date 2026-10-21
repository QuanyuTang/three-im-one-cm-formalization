module

public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.Lattice
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The stable ODE estimate in the transport argument

The transport proof uses `W' = -(W - 2α) / 2 + E` on a real segment.
Its error `E` depends on the other unknown `h`, as well as the small parameters.
Only after bounding `h` on a proposed bootstrap interval does the manuscript
obtain `‖E‖ ≤ r₀ / 4`. The estimate here then improves `‖W - 2α‖ ≤ r₀` to
`‖W - 2α‖ ≤ r₀ / 2`, independently of the segment length.

These lemmas concern differentiable representatives on the real segment; they
make no pointwise assertion about the junk values of meromorphic quotients.
The final lemma supplies the first-exit argument for curves already continuous
on the real segment. Obtaining the ODE and its error bound from meromorphic
representatives, and extending those representatives across possible poles,
remain separate tasks.
-/

@[expose] public section

open Set
open scoped InnerProductSpace

namespace ThreeIM

/-- A stable linear ODE with error at most `κ * R` cannot leave the closed
radius-`R` disk about its equilibrium. No bound depends on the interval length,
and continuity of the error derivative is unnecessary. -/
theorem norm_sub_le_of_stable_ode {W E : ℝ → ℂ} {a b κ R : ℝ} {c : ℂ}
    (hκ : 0 < κ) (hR : 0 ≤ R)
    (hode : ∀ t ∈ Icc a b,
      HasDerivAt W ((-κ) • (W t - c) + E t) t)
    (herror : ∀ t ∈ Ico a b, ‖E t‖ ≤ κ * R)
    (ha : ‖W a - c‖ ≤ R) :
    ∀ t ∈ Icc a b, ‖W t - c‖ ≤ R := by
  let energy' : ℝ → ℝ := fun t =>
    2 * ⟪W t - c, (-κ) • (W t - c) + E t⟫_ℝ
  have hderiv : ∀ t ∈ Icc a b,
      HasDerivAt (fun t => ‖W t - c‖ ^ 2) (energy' t) t := by
    intro t ht
    exact ((hode t ht).sub_const c).norm_sq
  have hcont : ContinuousOn (fun t => ‖W t - c‖ ^ 2) (Icc a b) := by
    intro t ht
    exact (hderiv t ht).continuousAt.continuousWithinAt
  have hbound : ∀ t ∈ Ico a b,
      energy' t ≤ -κ * ‖W t - c‖ ^ 2 + κ * R ^ 2 := by
    intro t ht
    have hinner := real_inner_le_norm (W t - c) (E t)
    have hprod := mul_le_mul_of_nonneg_left (herror t ht) (norm_nonneg (W t - c))
    have hsquare := mul_nonneg hκ.le (sq_nonneg (‖W t - c‖ - R))
    dsimp only [energy']
    rw [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    nlinarith
  have ha_sq : ‖W a - c‖ ^ 2 ≤ R ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hR).2 ha
  have hgron := le_gronwallBound_of_liminf_deriv_right_le hcont
    (fun t ht r hr => by
      simpa only [slope_def_field, div_eq_mul_inv, mul_comm] using
        (hderiv t (Ico_subset_Icc_self ht)).hasDerivWithinAt.liminf_right_slope_le hr)
    ha_sq hbound
  have hdiv : κ * R ^ 2 / (-κ) = -(R ^ 2) := by
    field_simp [hκ.ne']
  intro t ht
  have hconstant : gronwallBound (R ^ 2) (-κ) (κ * R ^ 2) (t - a) = R ^ 2 := by
    rw [gronwallBound, if_neg (neg_ne_zero.mpr hκ.ne'), hdiv]
    ring
  apply (sq_le_sq₀ (norm_nonneg _) hR).1
  simpa only [hconstant] using hgron t ht

/-- The actual `W`-estimate used in the transport bootstrap: an initial error
at most `r₀ / 4` and an ODE error at most `r₀ / 4` keep `W` within `r₀ / 2`
of `2α`, throughout any real segment on which these bounds hold. -/
theorem transport_W_trap {W E : ℝ → ℂ} {a b r₀ : ℝ} {α : ℂ}
    (hr₀ : 0 < r₀)
    (hode : ∀ t ∈ Icc a b,
      HasDerivAt W ((-(1 / 2 : ℝ)) • (W t - 2 * α) + E t) t)
    (herror : ∀ t ∈ Ico a b, ‖E t‖ ≤ r₀ / 4)
    (ha : ‖W a - 2 * α‖ ≤ r₀ / 4) :
    ∀ t ∈ Icc a b, ‖W t - 2 * α‖ ≤ r₀ / 2 := by
  apply norm_sub_le_of_stable_ode (κ := 1 / 2) (R := r₀ / 2)
    (by norm_num) (half_pos hr₀).le hode
  · intro t ht
    have := herror t ht
    linarith
  · linarith

private lemma transport_real_inner_nonpos {z v : ℂ} (hz : z ≠ 0)
    (h : (v / z).re ≤ 0) : ⟪z, v⟫_ℝ ≤ 0 := by
  have hmul := mul_nonpos_of_nonpos_of_nonneg h (Complex.normSq_nonneg z)
  have hidentity : (v / z).re * Complex.normSq z = ⟪z, v⟫_ℝ := by
    rw [Complex.div_re, Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    (field_simp [(Complex.normSq_pos.mpr hz).ne']; ring)
  exact hidentity ▸ hmul

/-- The second transport bootstrap estimate. A nonpositive real logarithmic
derivative prevents the nonzero amplitude `h` from growing on the real segment.
The manuscript's bound `Re(h' / h) ≤ -1/4` in particular implies this estimate.
An initial bound `‖h a‖ ≤ b₀ / 2` therefore retains the strict margin inside
the proposed `b₀` bootstrap region, with no dependence on the segment length. -/
theorem norm_le_initial_of_re_log_deriv_nonpos {h h' : ℝ → ℂ} {a b : ℝ}
    (hderiv : ∀ t ∈ Icc a b, HasDerivAt h (h' t) t)
    (hne : ∀ t ∈ Ico a b, h t ≠ 0)
    (hlog : ∀ t ∈ Ico a b, (h' t / h t).re ≤ 0) :
    ∀ t ∈ Icc a b, ‖h t‖ ≤ ‖h a‖ := by
  have henergy : ∀ t ∈ Icc a b,
      HasDerivAt (fun t => ‖h t‖ ^ 2) (2 * ⟪h t, h' t⟫_ℝ) t := by
    intro t ht
    exact (hderiv t ht).norm_sq
  have hcont : ContinuousOn (fun t => ‖h t‖ ^ 2) (Icc a b) := by
    intro t ht
    exact (henergy t ht).continuousAt.continuousWithinAt
  have hbound : ∀ t ∈ Ico a b,
      2 * ⟪h t, h' t⟫_ℝ ≤ 0 * ‖h t‖ ^ 2 + 0 := by
    intro t ht
    have := transport_real_inner_nonpos (hne t ht) (hlog t ht)
    linarith
  have hgron := le_gronwallBound_of_liminf_deriv_right_le hcont
    (fun t ht r hr => by
      simpa only [slope_def_field, div_eq_mul_inv, mul_comm] using
        (henergy t (Ico_subset_Icc_self ht)).hasDerivWithinAt.liminf_right_slope_le hr)
    (le_refl (‖h a‖ ^ 2)) hbound
  intro t ht
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  simpa only [gronwallBound_K0, zero_mul, add_zero] using hgron t ht

private theorem continuous_no_first_exit {p : ℝ → ℝ} {a b : ℝ}
    (hp : ContinuousOn p (Icc a b)) (ha : p a < 1)
    (himprove : ∀ t ∈ Icc a b, (∀ s ∈ Icc a t, p s ≤ 1) → p t < 1) :
    ∀ t ∈ Icc a b, p t < 1 := by
  intro t ht
  by_contra hbad
  have htbad : 1 ≤ p t := le_of_not_gt hbad
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
  obtain ⟨s, hs, hps⟩ := intermediate_value_Icc ht.1 (hp.mono hsub) ⟨ha.le, htbad⟩
  let S : Set ℝ := Icc a t ∩ p ⁻¹' {1}
  have hSclosed : IsClosed S :=
    (hp.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hScompact : IsCompact S :=
    isCompact_Icc.of_isClosed_subset hSclosed inter_subset_left
  have hSne : S.Nonempty := ⟨s, hs, hps⟩
  obtain ⟨τ, hτ⟩ := hScompact.exists_isLeast hSne
  have hτmem : τ ∈ Icc a t := hτ.1.1
  have hτlevel : p τ = 1 := hτ.1.2
  have hprefix : ∀ v ∈ Icc a τ, p v ≤ 1 := by
    intro v hv
    by_contra hnot
    have hvbad : 1 < p v := lt_of_not_ge hnot
    have hvτ : v < τ := lt_of_le_of_ne hv.2 (by
      intro heq
      rw [heq, hτlevel] at hvbad
      exact lt_irrefl _ hvbad)
    have hvsub : Icc a v ⊆ Icc a b :=
      Icc_subset_Icc le_rfl (hv.2.trans (hτmem.2.trans ht.2))
    obtain ⟨u, hu, hpu⟩ :=
      intermediate_value_Icc hv.1 (hp.mono hvsub) ⟨ha.le, hvbad.le⟩
    have huS : u ∈ S := ⟨⟨hu.1, hu.2.trans (hv.2.trans hτmem.2)⟩, hpu⟩
    have hτu : τ ≤ u := hτ.2 huS
    linarith [hu.2]
  have hstrict := himprove τ (hsub hτmem) hprefix
  rw [hτlevel] at hstrict
  exact lt_irrefl _ hstrict

/-- The coupled first-exit bootstrap on a real segment. The ODE, error bound,
nonvanishing, and logarithmic-derivative condition are required only where
`‖W - 2α‖ ≤ r₀` and `‖h‖ ≤ b₀`. They force the stronger half-radius bounds
everywhere on the segment.

The curves `W` and `h` are assumed already continuous on this whole segment;
the assertion does not extend meromorphic representatives across a pole. -/
theorem transport_bootstrap {W h E v : ℝ → ℂ} {a b r₀ b₀ : ℝ} {α : ℂ}
    (hr₀ : 0 < r₀) (hb₀ : 0 < b₀)
    (hW : ContinuousOn W (Icc a b)) (hh : ContinuousOn h (Icc a b))
    (hode : ∀ t ∈ Icc a b, ‖W t - 2 * α‖ ≤ r₀ → ‖h t‖ ≤ b₀ →
      HasDerivAt W ((-(1 / 2 : ℝ)) • (W t - 2 * α) + E t) t)
    (hderiv : ∀ t ∈ Icc a b, ‖W t - 2 * α‖ ≤ r₀ → ‖h t‖ ≤ b₀ →
      HasDerivAt h (v t) t)
    (herror : ∀ t ∈ Icc a b, ‖W t - 2 * α‖ ≤ r₀ → ‖h t‖ ≤ b₀ →
      ‖E t‖ ≤ r₀ / 4)
    (hne : ∀ t ∈ Icc a b, ‖W t - 2 * α‖ ≤ r₀ → ‖h t‖ ≤ b₀ → h t ≠ 0)
    (hlog : ∀ t ∈ Icc a b, ‖W t - 2 * α‖ ≤ r₀ → ‖h t‖ ≤ b₀ →
      (v t / h t).re ≤ 0)
    (hWa : ‖W a - 2 * α‖ ≤ r₀ / 4) (hha : ‖h a‖ ≤ b₀ / 2) :
    ∀ t ∈ Icc a b, ‖W t - 2 * α‖ ≤ r₀ / 2 ∧ ‖h t‖ ≤ b₀ / 2 := by
  let p : ℝ → ℝ := fun t => max (‖W t - 2 * α‖ / r₀) (‖h t‖ / b₀)
  have hp : ContinuousOn p (Icc a b) := by
    have h₁ : ContinuousOn (fun t => ‖W t - 2 * α‖ / r₀) (Icc a b) :=
      (hW.sub continuousOn_const).norm.div_const r₀
    have h₂ : ContinuousOn (fun t => ‖h t‖ / b₀) (Icc a b) := hh.norm.div_const b₀
    exact h₁.sup h₂
  have hpinitial : p a < 1 := by
    apply max_lt
    · rw [div_lt_iff₀ hr₀]
      linarith
    · rw [div_lt_iff₀ hb₀]
      linarith
  have improve : ∀ t ∈ Icc a b, (∀ s ∈ Icc a t, p s ≤ 1) →
      ∀ s ∈ Icc a t, ‖W s - 2 * α‖ ≤ r₀ / 2 ∧ ‖h s‖ ≤ b₀ / 2 := by
    intro t ht hprefix
    have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
    have hactive : ∀ s ∈ Icc a t, ‖W s - 2 * α‖ ≤ r₀ ∧ ‖h s‖ ≤ b₀ := by
      intro s hs
      have hpref := hprefix s hs
      have hw := (le_max_left (‖W s - 2 * α‖ / r₀) (‖h s‖ / b₀)).trans hpref
      have hh' := (le_max_right (‖W s - 2 * α‖ / r₀) (‖h s‖ / b₀)).trans hpref
      exact ⟨by simpa only [one_mul] using (div_le_iff₀ hr₀).mp hw,
        by simpa only [one_mul] using (div_le_iff₀ hb₀).mp hh'⟩
    have hWtrap := transport_W_trap hr₀
      (fun s hs => hode s (hsub hs) (hactive s hs).1 (hactive s hs).2)
      (fun s hs => herror s (hsub (Ico_subset_Icc_self hs))
        (hactive s (Ico_subset_Icc_self hs)).1 (hactive s (Ico_subset_Icc_self hs)).2) hWa
    have hhtrap := norm_le_initial_of_re_log_deriv_nonpos
      (fun s hs => hderiv s (hsub hs) (hactive s hs).1 (hactive s hs).2)
      (fun s hs => hne s (hsub (Ico_subset_Icc_self hs))
        (hactive s (Ico_subset_Icc_self hs)).1 (hactive s (Ico_subset_Icc_self hs)).2)
      (fun s hs => hlog s (hsub (Ico_subset_Icc_self hs))
        (hactive s (Ico_subset_Icc_self hs)).1 (hactive s (Ico_subset_Icc_self hs)).2)
    intro s hs
    exact ⟨hWtrap s hs, (hhtrap s hs).trans hha⟩
  have hnoexit : ∀ t ∈ Icc a b, p t < 1 :=
    continuous_no_first_exit hp hpinitial (by
      intro t ht hprefix
      obtain ⟨hwt, hht⟩ := improve t ht hprefix t (right_mem_Icc.mpr ht.1)
      have hw : ‖W t - 2 * α‖ / r₀ ≤ 1 / 2 := (div_le_iff₀ hr₀).mpr (by linarith)
      have hh' : ‖h t‖ / b₀ ≤ 1 / 2 := (div_le_iff₀ hb₀).mpr (by linarith)
      have : p t ≤ 1 / 2 := max_le hw hh'
      linarith)
  intro t ht
  have hprefix : ∀ s ∈ Icc a t, p s ≤ 1 := fun s hs =>
    (hnoexit s ⟨hs.1, hs.2.trans ht.2⟩).le
  exact improve t ht hprefix t (right_mem_Icc.mpr ht.1)

end ThreeIM
