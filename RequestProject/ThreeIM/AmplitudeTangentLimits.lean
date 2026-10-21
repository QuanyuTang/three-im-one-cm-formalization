module

public import RequestProject.ThreeIM.AmplitudeSequenceCompactness
public import RequestProject.ThreeIM.TangentScalar

/-!
# The scalar equation and derivative identity in an amplitude limit

Two Cauchy derivative limits pass the true scalar equation to the limit,
including the derivative of its variable coefficient. For the exponential
coefficient profiles this is exactly TanScalar. Classification of that
equation is a separate theorem.
-/

@[expose] public section

open Filter Set Metric Topology

namespace ThreeIM

set_option autoImplicit false

theorem scalar_primitive_limit_equations
    {D H C B : ℕ → ℂ → ℂ} {d h c b : ℂ → ℂ}
    (hseq : ∀ R > 0, ∀ᶠ n in atTop,
      ScalarPrimitiveOn (ball 0 R) (D n) (H n) (C n) (B n))
    (hD : TendstoLocallyUniformlyOn D d atTop univ)
    (hH : TendstoLocallyUniformlyOn H h atTop univ)
    (hC : TendstoLocallyUniformlyOn C c atTop univ)
    (hB : TendstoLocallyUniformlyOn B b atTop univ) :
    (∀ z, c z * h z * (h z - 1) * deriv (deriv h) z
      - deriv c z * h z * (h z - 1) * deriv h z
      - (c z * (3 * h z - 1) + b z) * deriv h z ^ 2 = 0) ∧
      (∀ z, deriv d z = c z * h z + b z) := by
  have hpoint (z : ℂ) :
      c z * h z * (h z - 1) * deriv (deriv h) z
      - deriv c z * h z * (h z - 1) * deriv h z
      - (c z * (3 * h z - 1) + b z) * deriv h z ^ 2 = 0 ∧
      deriv d z = c z * h z + b z := by
    let R : ℝ := ‖z‖ + 1
    have hR : 0 < R := by dsimp only [R]; positivity
    have hz : z ∈ ball (0 : ℂ) R := by
      rw [mem_ball_zero_iff]
      dsimp only [R]
      linarith
    have hHs := (hseq R hR).mono fun n hn => hn.holoH
    have hCs := (hseq R hR).mono fun n hn => hn.holoC
    have hDs := (hseq R hR).mono fun n hn => hn.holoD
    have hHds := hHs.mono fun n hn => (hn.analyticOnNhd isOpen_ball).deriv.differentiableOn
    have hHd := (hH.mono (subset_univ (ball 0 R))).deriv hHs isOpen_ball
    have hHdd := hHd.deriv hHds isOpen_ball
    have hCd := (hC.mono (subset_univ (ball 0 R))).deriv hCs isOpen_ball
    have hDd := (hD.mono (subset_univ (ball 0 R))).deriv hDs isOpen_ball
    have hy := hH.tendsto_at (mem_univ z)
    have hy' := hHd.tendsto_at hz
    have hy'' := hHdd.tendsto_at hz
    have hc := hC.tendsto_at (mem_univ z)
    have hc' := hCd.tendsto_at hz
    have hb := hB.tendsto_at (mem_univ z)
    have hd' := hDd.tendsto_at hz
    have hleft := (((hc.mul hy).mul (hy.sub_const 1)).mul hy'').sub
      (((hc'.mul hy).mul (hy.sub_const 1)).mul hy')
    have hright := ((hc.mul (hy.const_mul 3 |>.sub_const 1)).add hb).mul (hy'.pow 2)
    have hscalar := tendsto_nhds_unique_of_eventuallyEq (hleft.sub hright)
      tendsto_const_nhds ((hseq R hR).mono fun n hn => hn.scalar z hz)
    have hderiv := tendsto_nhds_unique_of_eventuallyEq hd' ((hc.mul hy).add hb)
      ((hseq R hR).mono fun n hn => hn.derivD z hz)
    exact ⟨hscalar, hderiv⟩
  exact ⟨fun z => (hpoint z).1, fun z => (hpoint z).2⟩

theorem amplitude_canonical_tangent_limit
    {X Y a b : ℕ → ℂ → ℂ} {d h : ℂ → ℂ} (α β : ℂ)
    (hseq : ∀ R > 0, ∀ᶠ n in atTop,
      AmplitudeSystemOn (ball 0 R) (X n) (Y n) (a n) (b n))
    (hD : TendstoLocallyUniformlyOn (fun n z => X n z - Y n z) d atTop univ)
    (hH : TendstoLocallyUniformlyOn
      (fun n => amplitudeQuotient (X n) (fun z => X n z - Y n z)) h atTop univ)
    (ha : TendstoLocallyUniformlyOn a (tanA α) atTop univ)
    (hb : TendstoLocallyUniformlyOn b (tanB β) atTop univ) :
    TanScalar α β h ∧ (∀ z, deriv d z = tanC α β z * h z + tanB β z) := by
  have hs : ∀ R > 0, ∀ᶠ n in atTop,
      ScalarPrimitiveOn (ball 0 R) (fun z => X n z - Y n z)
        (amplitudeQuotient (X n) (fun z => X n z - Y n z))
        (fun z => a n z - b n z) (b n) := by
    intro R hR
    exact (hseq R hR).mono fun n hn => (hn.canonical isOpen_ball).1
  have hh := scalar_primitive_limit_equations hs hD hH (ha.sub hb) hb
  refine ⟨?_, hh.2⟩
  intro z
  have he := hh.1 z
  change (tanC α β z) * h z * (h z - 1) * deriv (deriv h) z
    - deriv (tanC α β) z * h z * (h z - 1) * deriv h z
    - (tanC α β z * (3 * h z - 1) + tanB β z) * deriv h z ^ 2 = 0 at he
  rwa [(hasDerivAt_tanC α β z).deriv] at he

end ThreeIM
