module

public import RequestProject.ThreeIM.SphereFibers
public import RequestProject.ThreeIM.SphereZeroPersistence

/-! # Two distinct bounded preimages persist in a nonconstant rescaling limit -/

@[expose] public section

open Filter Set Metric Topology NoWanderingDomains

namespace ThreeIM

theorem eventually_two_bounded_sphere_fibers {F : ℕ → ℂ → OnePoint ℂ}
    {H : ℂ → OnePoint ℂ} (hH : SphereHolomorphicOn H univ)
    (hnc : ¬ ∃ p : OnePoint ℂ, ∀ z, H z = p)
    (hloc : ∀ z : ℂ, ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
      ∀ᶠ n in atTop, SphereHolomorphicOn (F n) U)
    (hconv : TendstoLocallyUniformlyOn F H atTop univ)
    (a : Fin 3 → OnePoint ℂ) (ha : Function.Injective a) :
    ∃ R : ℝ, 0 < R ∧ ∀ᶠ n in atTop, ∃ x y : ℂ,
      x ∈ ball 0 R ∧ y ∈ ball 0 R ∧ x ≠ y ∧
      (∃ j, F n x = a j) ∧ ∃ k, F n y = a k := by
  obtain ⟨w, v, hwv, hw, hv⟩ := exists_two_sphere_triple_fibers hH hnc
    (a 0) (a 1) (a 2) (ha.ne (by decide)) (ha.ne (by decide)) (ha.ne (by decide))
  have pick : ∀ t : ℂ, (H t = a 0 ∨ H t = a 1 ∨ H t = a 2) → ∃ j, H t = a j := by
    intro t ht
    rcases ht with h | h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
  obtain ⟨j, hj⟩ := pick w hw
  obtain ⟨k, hk⟩ := pick v hv
  let ε : ℝ := dist w v / 3
  have hε : 0 < ε := div_pos (dist_pos.mpr hwv) (by norm_num)
  let R : ℝ := ‖w‖ + ‖v‖ + ε + 1
  have hR : 0 < R := by dsimp only [R]; linarith [norm_nonneg w, norm_nonneg v]
  have hpreW := sphere_eventually_exists_preimage hH hnc hloc hconv hj
    isOpen_ball (mem_ball_self hε)
  have hpreV := sphere_eventually_exists_preimage hH hnc hloc hconv hk
    isOpen_ball (mem_ball_self hε)
  refine ⟨R, hR, ?_⟩
  filter_upwards [hpreW, hpreV] with n hnW hnV
  obtain ⟨x, hx, hxt⟩ := hnW
  obtain ⟨y, hy, hyt⟩ := hnV
  refine ⟨x, y, ?_, ?_, ?_, ⟨j, hxt⟩, ⟨k, hyt⟩⟩
  · rw [mem_ball_zero_iff]
    have hx' : ‖x - w‖ < ε := mem_ball_iff_norm.mp hx
    have hn := norm_sub_norm_le x w
    dsimp only [R]
    linarith [norm_nonneg v]
  · rw [mem_ball_zero_iff]
    have hy' : ‖y - v‖ < ε := mem_ball_iff_norm.mp hy
    have hn := norm_sub_norm_le y v
    dsimp only [R]
    linarith [norm_nonneg w]
  · intro heq
    have hx' := mem_ball.mp hx
    have hy' := mem_ball.mp hy
    rw [← heq] at hy'
    have htri := dist_triangle w x v
    rw [dist_comm w x] at htri
    dsimp only [ε] at hx' hy'
    have hd := dist_pos.mpr hwv
    linarith

end ThreeIM
