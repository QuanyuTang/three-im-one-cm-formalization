module

public import RequestProject.ThreeIM.TransportInitialBounds
public import RequestProject.ThreeIM.TransportNormalFormCoordinates

/-!
# Initial bounds for the global meromorphic continuation coordinates

The original meromorphic maps are replaced by normal forms on their actual
domains. Local reconstruction of the proved tangent coordinates identifies
the normal forms near the starting point. No absence of poles along the
remaining real segment is assumed.
-/

@[expose] public section

open Filter Set Metric Topology

namespace ThreeIM

set_option autoImplicit false

theorem TransportTangentConvergence.exists_normal_form_initial_bounds
    {F G : ℕ → ℂ → ℂ} {ε : ℕ → ℝ} {c α : ℂ}
    (h : TransportTangentConvergence F G ε c α)
    {Ω : ℕ → Set ℂ} (hΩ : ∀ n, IsOpen (Ω n))
    (hF : ∀ n, MeromorphicOn (F n) (Ω n))
    (hG : ∀ n, MeromorphicOn (G n) (Ω n))
    (hε : ∀ n, ε n ≠ 0)
    (hdomain : ∀ R > 0, ∀ᶠ n in atTop, closedBall (0 : ℂ) R ⊆ Ω n)
    {r₀ b₀ θ₀ : ℝ} (hr₀ : 0 < r₀) (hb₀ : 0 < b₀) (hθ₀ : 0 < θ₀)
    (hrα : r₀ < ‖α‖) :
    ∃ a : ℝ, 1 ≤ a ∧ Real.exp (-a) ≤ θ₀ ∧ ∀ᶠ n in atTop,
      (a : ℂ) ∈ Ω n ∧
      AnalyticAt ℂ (transportNormalW (Ω n) (F n) (G n) (transportScale (ε n)) c) (a : ℂ) ∧
      AnalyticAt ℂ (transportNormalH (Ω n) (F n) (G n) c) (a : ℂ) ∧
      ‖transportNormalW (Ω n) (F n) (G n) (transportScale (ε n)) c (a : ℂ) - 2 * α‖ ≤ r₀ / 4 ∧
      ‖transportNormalH (Ω n) (F n) (G n) c (a : ℂ)‖ ≤ b₀ / 2 := by
  obtain ⟨a, ha, hθ, hinit⟩ := h.exists_initial_analytic_bounds hr₀ hb₀ hθ₀
  let R : ℝ := ‖(a : ℂ)‖ + 1
  have hR : 0 < R := by dsimp only [R]; positivity
  have haR : (a : ℂ) ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff]
    dsimp only [R]
    linarith
  refine ⟨a, ha, hθ, ?_⟩
  filter_upwards [hinit, hdomain R hR, h.initial_reconstruction hε hR]
    with n hn hnΩ hnrec
  have haΩ := hnΩ (ball_subset_closedBall haR)
  have hW0 : transportInitialW (F n) (G n) c (ε n) (a : ℂ) ≠ 0 := by
    intro heq
    have hb := hn.2.2.1
    rw [heq, zero_sub, norm_neg, norm_mul] at hb
    norm_num at hb
    linarith [norm_nonneg α]
  have heF := auxiliary_local_of_codiscreteWithin (hΩ n)
    (chartFinite_sphereGerm_eq_codiscreteWithin (hF n)) haΩ
  have heG := auxiliary_local_of_codiscreteWithin (hΩ n)
    (chartFinite_sphereGerm_eq_codiscreteWithin (hG n)) haΩ
  have hrec : ∀ᶠ w in 𝓝[≠] (a : ℂ),
      transportFiniteChart (F n) w - c =
        transportScale (ε n) w * transportInitialW (F n) (G n) c (ε n) w *
          (1 + transportInitialH (F n) (G n) c (ε n) w) ∧
      transportFiniteChart (G n) w - c =
        transportScale (ε n) w * transportInitialW (F n) (G n) c (ε n) w *
          transportInitialH (F n) (G n) c (ε n) w :=
    (Filter.eventually_of_mem (isOpen_ball.mem_nhds haR) hnrec).filter_mono nhdsWithin_le_nhds
  have hFr : (fun w => F n w - c) =ᶠ[𝓝[≠] (a : ℂ)] fun w =>
      transportScale (ε n) w * transportInitialW (F n) (G n) c (ε n) w *
        (1 + transportInitialH (F n) (G n) c (ε n) w) := by
    filter_upwards [heF, hrec] with w hw hr
    rw [hw]
    exact hr.1
  have hGr : (fun w => G n w - c) =ᶠ[𝓝[≠] (a : ℂ)] fun w =>
      transportScale (ε n) w * transportInitialW (F n) (G n) c (ε n) w *
        transportInitialH (F n) (G n) c (ε n) w := by
    filter_upwards [heG, hrec] with w hw hr
    rw [hw]
    exact hr.2
  have hτΩ : MeromorphicOn (transportScale (ε n)) (Ω n) :=
    fun w _ => (analyticAt_transportScale (ε n) w).meromorphicAt
  have hm := transport_normal_form_initial_match (hF n) (hG n) hτΩ haΩ
    (analyticAt_transportScale (ε n) (a : ℂ)) (transportScale_ne_zero (hε n) _)
    hn.1 hW0 hn.2.1 hFr hGr
  refine ⟨haΩ, hm.1, hm.2.1, ?_, ?_⟩
  · rw [hm.2.2.1.eq_of_nhds]
    exact hn.2.2.1
  · rw [hm.2.2.2.eq_of_nhds]
    exact hn.2.2.2

end ThreeIM
