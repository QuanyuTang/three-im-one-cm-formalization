module

public import RequestProject.ThreeIM.AffineCovariance
public import RequestProject.ThreeIM.SphereRescaling

/-!
# Normalized pairs with prescribed zero-free holomorphic coefficients

These are exactly the local data appearing in the original limit-extraction
statement. Restriction and affine source changes derive the corresponding
data on fixed rescaled disks; no compactness conclusion is assumed.
-/

@[expose] public section

open Filter Set Metric Topology

namespace ThreeIM

structure AuxiliaryPairOn (Ω : Set ℂ) (f g u v : ℂ → ℂ) (a : Fin 3 → ℂ) : Prop where
  pair : NormalizedPair Ω f g a
  holo_u : DifferentiableOn ℂ u Ω
  holo_v : DifferentiableOn ℂ v Ω
  nonzero_u : ∀ z ∈ Ω, u z ≠ 0
  nonzero_v : ∀ z ∈ Ω, v z ≠ 0
  u_eq : auxU a f g =ᶠ[codiscreteWithin Ω] u
  v_eq : auxV a f g =ᶠ[codiscreteWithin Ω] v

theorem AuxiliaryPairOn.restrict {Ω V : Set ℂ} {f g u v : ℂ → ℂ} {a : Fin 3 → ℂ}
    (h : AuxiliaryPairOn Ω f g u v a) (hVΩ : V ⊆ Ω) : AuxiliaryPairOn V f g u v a where
  pair := {
    nonconst_f := ⟨fun z hz => h.pair.nonconst_f.1 z (hVΩ hz),
      fun z hz c => h.pair.nonconst_f.2 z (hVΩ hz) c⟩
    nonconst_g := ⟨fun z hz => h.pair.nonconst_g.1 z (hVΩ hz),
      fun z hz c => h.pair.nonconst_g.2 z (hVΩ hz) c⟩
    distinct := fun z hz => h.pair.distinct z (hVΩ hz)
    injective := h.pair.injective
    im := fun j z hz => h.pair.im j z (hVΩ hz)
    cm_top := fun z hz => h.pair.cm_top z (hVΩ hz) }
  holo_u := h.holo_u.mono hVΩ
  holo_v := h.holo_v.mono hVΩ
  nonzero_u := fun z hz => h.nonzero_u z (hVΩ hz)
  nonzero_v := fun z hz => h.nonzero_v z (hVΩ hz)
  u_eq := h.u_eq.filter_mono (Filter.codiscreteWithin.mono hVΩ)
  v_eq := h.v_eq.filter_mono (Filter.codiscreteWithin.mono hVΩ)

theorem AuxiliaryPairOn.comp_affine {Ω V : Set ℂ} {f g u v : ℂ → ℂ} {a : Fin 3 → ℂ}
    (h : AuxiliaryPairOn Ω f g u v a) (c z₀ : ℂ) (hc : c ≠ 0)
    (hmaps : MapsTo (fun w => z₀ + c * w) V Ω) :
    AuxiliaryPairOn V (fun w => f (z₀ + c * w)) (fun w => g (z₀ + c * w))
      (fun w => c * u (z₀ + c * w)) (fun w => c * v (z₀ + c * w)) a := by
  have hd (w : ℂ) : deriv (fun x : ℂ => z₀ + c * x) w = c := by
    simpa only [id_eq, mul_one] using (((hasDerivAt_id w).const_mul c).const_add z₀).deriv
  have hcov := aux_affine_comp_codiscreteWithin h.pair.nonconst_f.1 h.pair.nonconst_g.1
    a c z₀ hc hmaps
  have hU := codiscreteWithin_comp_source h.u_eq hmaps
    (fun w _ => affine_tendsto_nhdsNE c z₀ w hc)
  have hV := codiscreteWithin_comp_source h.v_eq hmaps
    (fun w _ => affine_tendsto_nhdsNE c z₀ w hc)
  refine ⟨h.pair.comp_source (fun w _ => by fun_prop)
    (fun w _ => by rw [hd]; exact hc) hmaps, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (h.holo_u.comp (by fun_prop) hmaps).const_mul c
  · exact (h.holo_v.comp (by fun_prop) hmaps).const_mul c
  · intro w hw
    exact mul_ne_zero hc (h.nonzero_u _ (hmaps hw))
  · intro w hw
    exact mul_ne_zero hc (h.nonzero_v _ (hmaps hw))
  · filter_upwards [hcov.1, hU] with w hw heq
    exact hw.trans (congrArg (fun x : ℂ => c * x) heq)
  · filter_upwards [hcov.2.1, hV] with w hw heq
    exact hw.trans (congrArg (fun x : ℂ => c * x) heq)

theorem AuxiliaryPairOn.phi_eq {Ω : Set ℂ} {f g u v : ℂ → ℂ} {a : Fin 3 → ℂ}
    (h : AuxiliaryPairOn Ω f g u v a) :
    auxPhi a f g =ᶠ[codiscreteWithin Ω] (fun w => u w / v w) := by
  filter_upwards [h.u_eq, h.v_eq] with w hwU hwV
  simp only [auxPhi, hwU, hwV]

theorem auxiliary_pairs_rescale_locally {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {F G u v : ℕ → ℂ → ℂ} {a : Fin 3 → ℂ}
    (h : ∀ n, AuxiliaryPairOn Ω (F n) (G n) (u n) (v n) a)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) (i : ℕ → ℕ) {z : ℕ → ℂ} {ρ : ℕ → ℝ}
    (hz : Tendsto z atTop (𝓝 z₀)) (hρ : Tendsto ρ atTop (𝓝 0))
    (hρne : ∀ n, ρ n ≠ 0) :
    ∀ w : ℂ, ∃ V : Set ℂ, IsOpen V ∧ w ∈ V ∧ ∀ᶠ n in atTop,
      AuxiliaryPairOn V (fun x => F (i n) (z n + (ρ n : ℂ) * x))
        (fun x => G (i n) (z n + (ρ n : ℂ) * x))
        (fun x => (ρ n : ℂ) * u (i n) (z n + (ρ n : ℂ) * x))
        (fun x => (ρ n : ℂ) * v (i n) (z n + (ρ n : ℂ) * x)) a := by
  intro w
  let R : ℝ := ‖w‖ + 1
  have hw : w ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff]
    dsimp only [R]
    linarith
  refine ⟨ball 0 R, isOpen_ball, hw, ?_⟩
  filter_upwards [eventually_rescale_closedBall_subset hΩ hz₀ hz hρ R] with n hn
  exact (h (i n)).comp_affine (ρ n : ℂ) (z n) (by exact_mod_cast hρne n)
    (fun x hx => hn x (ball_subset_closedBall hx))

end ThreeIM
