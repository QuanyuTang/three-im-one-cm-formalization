module

public import RequestProject.ThreeIM.AmplitudeCanonical

/-!
# Compactness from the actual amplitude equations

The analytic quotient is constructed canonically from X and X-Y. Only the
original amplitude identities, local finite order of the difference, and
marked derivatives are assumed. Holomorphy and these identities need hold
only eventually on each fixed disk. Compactness of both amplitudes is then
derived from the scalar equation and normalized primitive convergence.
-/

@[expose] public section

open Filter Set Metric Topology

namespace ThreeIM

set_option autoImplicit false

structure AmplitudeSystemOn (Ω : Set ℂ) (X Y a b : ℂ → ℂ) : Prop where
  holoX : DifferentiableOn ℂ X Ω
  holoY : DifferentiableOn ℂ Y Ω
  holoA : DifferentiableOn ℂ a Ω
  holoB : DifferentiableOn ℂ b Ω
  nonzeroA : ∀ z ∈ Ω, a z ≠ 0
  finiteDifference : ∀ z ∈ Ω, meromorphicOrderAt (fun w => X w - Y w) z ≠ ⊤
  eqX : ∀ z ∈ Ω, (X z - Y z) * deriv X z = a z * X z
  eqY : ∀ z ∈ Ω, (X z - Y z) * deriv Y z = b z * Y z

theorem AmplitudeSystemOn.canonical {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {X Y a b : ℂ → ℂ} (h : AmplitudeSystemOn Ω X Y a b) :
    ScalarPrimitiveOn Ω (fun w => X w - Y w)
      (amplitudeQuotient X (fun w => X w - Y w)) (fun w => a w - b w) b ∧
      (∀ z ∈ Ω, X z = (X z - Y z) * amplitudeQuotient X (fun w => X w - Y w) z) ∧
      (∀ z ∈ Ω, Y z = (X z - Y z) * (amplitudeQuotient X (fun w => X w - Y w) z - 1)) :=
  scalarPrimitiveOn_amplitudeQuotient hΩ h.holoX h.holoY h.holoA h.holoB
    h.nonzeroA h.finiteDifference h.eqX h.eqY

theorem amplitude_system_subsequence {X Y a b : ℕ → ℂ → ℂ} {A B : ℂ → ℂ}
    (hseq : ∀ R > 0, ∀ᶠ n in atTop, AmplitudeSystemOn (ball 0 R) (X n) (Y n) (a n) (b n))
    (hA : Differentiable ℂ A) (hB : Differentiable ℂ B) (hB0 : ∀ z, B z ≠ 0)
    (ha : TendstoLocallyUniformlyOn a A atTop univ)
    (hb : TendstoLocallyUniformlyOn b B atTop univ)
    (hmarked : ∀ᶠ n in atTop, X n 0 = 0 ∧ Y n 0 = 0 ∧
      deriv (X n) 0 ≠ 0 ∧ deriv (Y n) 0 = 0) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ h d : ℂ → ℂ,
      Differentiable ℂ h ∧ Differentiable ℂ d ∧ h 0 = 1 ∧ d 0 = 0 ∧
      TendstoLocallyUniformlyOn
        (fun n => amplitudeQuotient (X (φ n)) (fun w => X (φ n) w - Y (φ n) w)) h atTop univ ∧
      TendstoLocallyUniformlyOn (fun n w => X (φ n) w - Y (φ n) w) d atTop univ ∧
      TendstoLocallyUniformlyOn (fun n => X (φ n)) (fun w => d w * h w) atTop univ ∧
      TendstoLocallyUniformlyOn (fun n => Y (φ n)) (fun w => d w * (h w - 1)) atTop univ := by
  let D : ℕ → ℂ → ℂ := fun n w => X n w - Y n w
  let H : ℕ → ℂ → ℂ := fun n => amplitudeQuotient (X n) (D n)
  have hs : ∀ R > 0, ∀ᶠ n in atTop, ScalarPrimitiveOn (ball 0 R)
      (D n) (H n) (fun w => a n w - b n w) (b n) := by
    intro R hR
    exact (hseq R hR).mono fun n hn => (hn.canonical isOpen_ball).1
  have hH0 : ∀ᶠ n in atTop, H n 0 = 1 := by
    filter_upwards [hseq 1 one_pos, hmarked] with n hn hm
    have hc := hn.canonical isOpen_ball
    exact amplitude_quotient_eq_one_at_simple_marked isOpen_ball hn.holoX hn.holoY
      hc.1.holoH hc.2.1 (mem_ball_self one_pos) hm.1 hm.2.1 hm.2.2.1 hm.2.2.2
  have hD0 : ∀ᶠ n in atTop, D n 0 = 0 := hmarked.mono fun n hn => by
    simp only [D, hn.1, hn.2.1, sub_self]
  obtain ⟨φ, hφ, h, d, hhd, hdd, hh0, hd0, hHconv, hDconv⟩ :=
    scalar_primitives_subsequence hs (hA.sub hB) hB hB0 (ha.sub hb) hb hH0 hD0
  have hXproduct := hDconv.mul₀ hHconv hdd.continuous.continuousOn hhd.continuous.continuousOn
  have hones : TendstoLocallyUniformlyOn (fun (_ : ℕ) (_ : ℂ) => (1 : ℂ))
      (fun _ => 1) atTop univ := by
    have ht : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1) := tendsto_const_nhds
    exact (ht.tendstoUniformlyOn_const univ).tendstoLocallyUniformlyOn
  have hYproduct := hDconv.mul₀ (hHconv.sub hones) hdd.continuous.continuousOn
    (hhd.continuous.sub continuous_const).continuousOn
  have hXconv : TendstoLocallyUniformlyOn (fun n => X (φ n)) (fun w => d w * h w) atTop univ := by
    apply tendstoLocallyUniformlyOn_congr_locally_eventually hXproduct
    intro z _
    let R : ℝ := ‖z‖ + 1
    have hR : 0 < R := by dsimp only [R]; positivity
    have hz : z ∈ ball (0 : ℂ) R := by
      rw [mem_ball_zero_iff]
      dsimp only [R]
      linarith
    refine ⟨ball 0 R, mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hz), ?_⟩
    filter_upwards [hφ.tendsto_atTop.eventually (hseq R hR)] with n hn w hw
    exact ((hn.canonical isOpen_ball).2.1 w hw).symm
  have hYconv : TendstoLocallyUniformlyOn (fun n => Y (φ n)) (fun w => d w * (h w - 1)) atTop univ := by
    apply tendstoLocallyUniformlyOn_congr_locally_eventually hYproduct
    intro z _
    let R : ℝ := ‖z‖ + 1
    have hR : 0 < R := by dsimp only [R]; positivity
    have hz : z ∈ ball (0 : ℂ) R := by
      rw [mem_ball_zero_iff]
      dsimp only [R]
      linarith
    refine ⟨ball 0 R, mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hz), ?_⟩
    filter_upwards [hφ.tendsto_atTop.eventually (hseq R hR)] with n hn w hw
    exact ((hn.canonical isOpen_ball).2.2 w hw).symm
  exact ⟨φ, hφ, h, d, hhd, hdd, hh0, hd0, hHconv, hDconv, hXconv, hYconv⟩

end ThreeIM
