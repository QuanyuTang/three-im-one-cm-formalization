module

public import RequestProject.ThreeIM.TransportInitialNormalForms
public import RequestProject.ThreeIM.TransportNormalFormPairData
public import RequestProject.ThreeIM.TransportSmallParameters
public import RequestProject.ThreeIM.TransportRealSegment

/-!
# Real-segment tracking from the actual tangent subsequence

The tangent convergence is supplied by `transport_tangent_subsequence`.
All initial analytic bounds, regular auxiliary identities, shared zero
fibers, parameter inequalities, and segment inclusions required by the
meromorphic continuation theorem are derived here. Absence of poles on
the growing segment is a conclusion.
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

set_option autoImplicit false

theorem transport_finite_tracking
    {Ω : ℕ → Set ℂ} (hΩ : ∀ n, IsOpen (Ω n))
    {F G u v : ℕ → ℂ → ℂ} {a : Fin 3 → ℂ} {j : Fin 3}
    (pair : ∀ n, NormalizedPair (Ω n) (F n) (G n) a)
    {ε : ℕ → ℝ} (hεpos : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    {A B : ℂ} (hA : A ≠ 0) (hB : B ≠ 0)
    (hu : ∀ n, DifferentiableOn ℂ (u n) (Ω n))
    (hv : ∀ n, DifferentiableOn ℂ (v n) (Ω n))
    (hU : ∀ n, auxU a (F n) (G n) =ᶠ[codiscreteWithin (Ω n)] u n)
    (hV : ∀ n, auxV a (F n) (G n) =ᶠ[codiscreteWithin (Ω n)] v n)
    (hrect : ∀ R > 0, ∀ᶠ n in atTop, transportRect (ε n) R ⊆ Ω n)
    (hprofU : ∀ R > 0, ∀ η > 0, ∀ᶠ n in atTop, ∀ z ∈ transportRect (ε n) R,
      ‖u n z / (ε n * A * Complex.exp (z / 2)) - 1‖ ≤ η)
    (hprofV : ∀ R > 0, ∀ η > 0, ∀ᶠ n in atTop, ∀ z ∈ transportRect (ε n) R,
      ‖v n z / (ε n * B * Complex.exp (-z / 2)) - 1‖ ≤ η)
    (hconv : TransportTangentConvergence F G ε (a j)
      (A * amplitudeRemainder a j (a j)))
    {smax : ℝ} (hsmax : 0 < smax) :
    ∃ r₀ s start : ℝ,
      0 < r₀ ∧ r₀ ≤ ‖A * ((a (j + 1) - a j) * (a (j + 2) - a j))‖ / 4 ∧
      0 < s ∧ s ≤ 1 ∧ s ≤ smax ∧ 1 ≤ start ∧ ∀ᶠ n in atTop,
      start ≤ 2 * Real.log (s / ε n) ∧
      ∀ t ∈ Icc start (2 * Real.log (s / ε n)),
        AnalyticAt ℂ (transportNormalF (Ω n) (F n) (a j)) (t : ℂ) ∧
        AnalyticAt ℂ (transportNormalF (Ω n) (G n) (a j)) (t : ℂ) ∧
        ‖transportNormalW (Ω n) (F n) (G n) (transportScale (ε n)) (a j) (t : ℂ) -
          2 * (A * ((a (j + 1) - a j) * (a (j + 2) - a j)))‖ ≤ r₀ / 2 ∧
        ‖transportNormalH (Ω n) (F n) (G n) (a j) (t : ℂ)‖ ≤ s / 2 ∧
        transportNormalF (Ω n) (F n) (a j) (t : ℂ) =
          transportScale (ε n) (t : ℂ) *
            transportNormalW (Ω n) (F n) (G n) (transportScale (ε n)) (a j) (t : ℂ) *
            (1 + transportNormalH (Ω n) (F n) (G n) (a j) (t : ℂ)) ∧
        transportNormalF (Ω n) (G n) (a j) (t : ℂ) =
          transportScale (ε n) (t : ℂ) *
            transportNormalW (Ω n) (F n) (G n) (transportScale (ε n)) (a j) (t : ℂ) *
            transportNormalH (Ω n) (F n) (G n) (a j) (t : ℂ) ∧
        transportNormalF (Ω n) (F n) (a j) (t : ℂ) -
          transportNormalF (Ω n) (G n) (a j) (t : ℂ) ≠ 0 := by
  let a₂ := a (j + 1) - a j
  let a₃ := a (j + 2) - a j
  let α := A * (a₂ * a₃)
  have hα : α ≠ 0 := by
    have hQ := amplitudeRemainder_nonzero (pair 0).injective j
    rw [amplitudeRemainder_eq_transport_product] at hQ
    exact mul_ne_zero hA hQ
  have hαpos : 0 < ‖α‖ := norm_pos_iff.mpr hα
  have hc : TransportTangentConvergence F G ε (a j) α := by
    simpa only [amplitudeRemainder_eq_transport_product] using hconv
  obtain ⟨r₀, s, hr₀, hrsmall, hs, hs1, hscap, hparams⟩ :=
    exists_bounded_transport_parameters hα hsmax
  have hrα : r₀ < ‖α‖ := by linarith
  obtain ⟨start, hstart, hθstart, hinit⟩ := hc.exists_normal_form_initial_bounds hΩ
    (fun n => (pair n).nonconst_f.1) (fun n => (pair n).nonconst_g.1)
    (fun n => (hεpos n).ne')
    (fun _ hR => eventually_closedBall_subset_transport_domains hεpos hε hrect hR)
    hr₀ hs hs hrα
  have hstart0 : 0 ≤ start := by linarith
  have hseg := eventually_transport_segment_in_domains hεpos hε hs hs1 hstart0
    (hrect 1 (by norm_num))
  refine ⟨r₀, s, start, hr₀, hrsmall, hs, hs1, hscap, hstart, ?_⟩
  filter_upwards [hinit, hseg, hprofU 1 (by norm_num) s hs,
    hprofV 1 (by norm_num) s hs] with n hn hsegment hUprofile hVprofile
  have hnf := transport_normal_form_coordinates (Ω n) (F n) (G n)
    (transportScale (ε n)) (a j)
  have hτmero : MeromorphicOn (transportScale (ε n)) (Ω n) :=
    fun z _ => (analyticAt_transportScale (ε n) z).meromorphicAt
  have hgerm := fun z hz => transport_normal_form_germs (a j)
    (pair n).nonconst_f.1 (pair n).nonconst_g.1 hτmero (z := z) hz
  have haux := transport_normal_form_auxiliary_identities (hΩ n) j
    (pair n).nonconst_f.1 (pair n).nonconst_g.1 (hU n) (hV n)
  have htrack := transport_profile_continuation
    (θ := fun t => Real.exp (-t)) (δ := s) (η := s) (θ₀ := s)
    (hΩ n) hsegment.1 hA hB hr₀ hs hrα
    hnf.1 hnf.2.1 hnf.2.2.1 hnf.2.2.2 hsegment.2
    (fun z _ => analyticAt_transportScale (ε n) z)
    (fun z _ => transportScale_ne_zero (hεpos n).ne' z)
    (fun t _ => hasDerivAt_transportScale_real (ε n) t)
    (fun z hz => (hgerm z hz).2.2.1) (fun z hz => (hgerm z hz).2.2.2)
    (transport_normal_form_nonconst (hΩ n) (pair n).nonconst_f (a j)).2
    (transport_normal_form_nonconst (hΩ n) (pair n).nonconst_g (a j)).2
    (hu n).continuousOn (hv n).continuousOn haux.1 haux.2
    (fun _ hz => transport_normal_form_shared_zero (pair n) j hz)
    (fun _ ht => ⟨(transport_decay_bound ht.1).1,
      (transport_decay_bound ht.1).2.trans hθstart⟩)
    hs.le hs1 (fun _ ht => norm_transportScale_le_endpoint (hεpos n) hs ht.2)
    (fun t ht => by
      rw [transportScale_profile_U_denominator]
      exact hUprofile _ (transport_real_segment_mem_rect (hεpos n) hs hs1 hstart0 ht))
    (fun t ht => by
      rw [transportScale_profile_V_denominator]
      exact hVprofile _ (transport_real_segment_mem_rect (hεpos n) hs hs1 hstart0 ht))
    hparams hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2
  refine ⟨hsegment.1, fun t ht => ?_⟩
  have httrack := htrack t ht
  exact ⟨httrack.1, httrack.2.1, httrack.2.2.1,
    httrack.2.2.2.1.trans hn.2.2.2.2, httrack.2.2.2.2⟩

end ThreeIM
