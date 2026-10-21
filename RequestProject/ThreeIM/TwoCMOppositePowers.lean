module

public import RequestProject.ThreeIM.TwoCMCrossRatio

/-!
# Integral powers forced by an actual shared finite point
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

theorem twoCM_crossRatio_powers_of_quad_ratio {f g : ℂ → ℂ}
    (hf : IsNonconstMeroOn f univ) (hg : IsNonconstMeroOn g univ)
    {b c d z : ℂ} (hbc : b ≠ c) (hd : d = b ∨ d = c)
    (hpf : 0 < mult f (d : Sphere) z) (hpg : 0 < mult g (d : Sphere) z)
    {k : ℂ}
    (hquad : twoCMQuadDerivative b c f =ᶠ[codiscrete ℂ]
      (fun w => k * twoCMQuadDerivative b c g w)) :
    ∃ C : ℂ, C ≠ 0 ∧
      (fun w => twoCMCrossRatio b c f w ^ mult g (d : Sphere) z)
        =ᶠ[codiscrete ℂ]
      (fun w => C * twoCMCrossRatio b c g w ^ mult f (d : Sphere) z) := by
  have hlog : (fun w => deriv (twoCMCrossRatio b c f) w / twoCMCrossRatio b c f w)
      =ᶠ[codiscrete ℂ]
      (fun w => k * (deriv (twoCMCrossRatio b c g) w / twoCMCrossRatio b c g w)) := by
    filter_upwards [twoCM_logDeriv_crossRatio hf b c, twoCM_logDeriv_crossRatio hg b c,
      hquad] with w hwf hwg hw
    rw [hwf, hwg, hw]
    ring
  have hres := twoCM_order_relation_of_log_deriv_eq
    (twoCM_meromorphic_crossRatio hf b c) (twoCM_meromorphic_crossRatio hg b c)
    (twoCM_crossRatio_order_ne_top hf b c) (twoCM_crossRatio_order_ne_top hg b c)
    1 k (by simpa only [one_mul] using hlog) z
  have hmn : (mult f (d : Sphere) z : ℂ) = k * (mult g (d : Sphere) z : ℂ) := by
    rcases hd with rfl | rfl
    · rw [twoCM_crossRatio_order_at_first hf hbc hpf,
        twoCM_crossRatio_order_at_first hg hbc hpg] at hres
      simpa only [one_mul, Int.cast_natCast] using hres
    · rw [twoCM_crossRatio_order_at_second hf hbc hpf,
        twoCM_crossRatio_order_at_second hg hbc hpg] at hres
      push_cast at hres
      linear_combination -hres
  apply twoCM_power_identity_of_log_deriv_eq
    (twoCM_meromorphic_crossRatio hf b c) (twoCM_meromorphic_crossRatio hg b c)
    (twoCM_crossRatio_order_ne_top hf b c) (twoCM_crossRatio_order_ne_top hg b c)
    (mult g (d : Sphere) z) (mult f (d : Sphere) z)
  filter_upwards [hlog] with w hw
  rw [hw, hmn]
  ring

end ThreeIM
