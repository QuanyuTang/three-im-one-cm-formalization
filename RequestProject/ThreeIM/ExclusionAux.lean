module

public import RequestProject.ThreeIM.ExponentialRational
public import RequestProject.ThreeIM.Selected

/-!
# Auxiliary facts for Section 10: source changes on disks and uniform convergence
-/

@[expose] public section

open Filter Set Metric Topology

namespace ThreeIM

/-- Precomposition with a holomorphic map with nonvanishing derivative, mapping `Ω` into `Ω'`,
turns a normalized pair on `Ω'` into a normalized pair on `Ω` (Lemma 3.9 on general
domains). -/
theorem NormalizedPair.comp_on {Ω Ω' : Set ℂ} {f g h : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair Ω' f g a) (hh : ∀ z ∈ Ω, AnalyticAt ℂ h z)
    (hh' : ∀ z ∈ Ω, deriv h z ≠ 0) (hmaps : MapsTo h Ω Ω') :
    NormalizedPair Ω (f ∘ h) (g ∘ h) a where
  nonconst_f := hp.nonconst_f.comp hh hh' hmaps
  nonconst_g := hp.nonconst_g.comp hh hh' hmaps
  distinct z hz := by
    have : (fun w => (f ∘ h) w - (g ∘ h) w) = (fun w => f w - g w) ∘ h := rfl
    rw [this, meromorphicOrderAt_comp_of_deriv_ne_zero (hh z hz) (hh' z hz)]
    exact hp.distinct (h z) (hmaps hz)
  injective := hp.injective
  im j z hz := by
    rw [mult_comp_of_deriv_ne_zero (hh z hz) (hh' z hz),
      mult_comp_of_deriv_ne_zero (hh z hz) (hh' z hz)]
    exact hp.im j (h z) (hmaps hz)
  cm_top z hz := by
    rw [mult_comp_of_deriv_ne_zero (hh z hz) (hh' z hz),
      mult_comp_of_deriv_ne_zero (hh z hz) (hh' z hz)]
    exact hp.cm_top (h z) (hmaps hz)

lemma hasDerivAt_const_mul' (c z : ℂ) : HasDerivAt (fun ζ : ℂ => c * ζ) c z := by
  simpa using (hasDerivAt_id z).const_mul c

lemma mapsTo_mul_ball {c : ℂ} (hc : c ≠ 0) (R : ℝ) :
    MapsTo (fun ζ : ℂ => c * ζ) (ball 0 (R / ‖c‖)) (ball 0 R) := by
  intro ζ hζ
  simp only [mem_ball, dist_zero_right, norm_mul] at hζ ⊢
  have hc' : 0 < ‖c‖ := norm_pos_iff.2 hc
  rwa [lt_div_iff₀ hc', mul_comm] at hζ

/-- Rescaling the source of a normalized pair on a disk: `ζ ↦ c ζ`. -/
theorem NormalizedPair.comp_mul_ball {R : ℝ} {F G : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair (ball 0 R) F G a) {c : ℂ} (hc : c ≠ 0) :
    NormalizedPair (ball 0 (R / ‖c‖)) (F ∘ fun ζ => c * ζ) (G ∘ fun ζ => c * ζ) a :=
  hp.comp_on (fun z _ => by fun_prop)
    (fun z _ => by rw [(hasDerivAt_const_mul' c z).deriv]; exact hc) (mapsTo_mul_ball hc R)

/-- Pulling back a property holding off a discrete subset of `Ω'` by a map `φ` sending `Ω`
into `Ω'` and punctured neighbourhoods to punctured neighbourhoods. -/
lemma codiscreteWithin_comp {Ω Ω' : Set ℂ} {p : ℂ → Prop} {φ : ℂ → ℂ}
    (h : ∀ᶠ z in codiscreteWithin Ω', p z) (hmaps : MapsTo φ Ω Ω')
    (hT : ∀ x ∈ Ω, Tendsto φ (𝓝[≠] x) (𝓝[≠] (φ x))) :
    ∀ᶠ z in codiscreteWithin Ω, p (φ z) := by
  rw [Filter.Eventually, mem_codiscreteWithin_iff_forall_mem_nhdsNE] at h ⊢
  intro x hx
  filter_upwards [hT x hx (h (φ x) (hmaps hx))] with z hz
  rcases hz with hz | hz
  · exact Or.inl hz
  · exact Or.inr fun hzΩ => hz (hmaps hzΩ)

/-! ### Uniform convergence -/

lemma norm_mul_sub_one_le {x y : ℂ} {δ : ℝ} (hx : ‖x - 1‖ ≤ δ) (hy : ‖y - 1‖ ≤ δ)
    (hδ : δ ≤ 1) : ‖x * y - 1‖ ≤ 3 * δ := by
  have hy' : ‖y‖ ≤ 2 := by
    calc ‖y‖ = ‖(y - 1) + 1‖ := by ring_nf
      _ ≤ ‖y - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 2 := by simp; linarith
  calc ‖x * y - 1‖ = ‖(x - 1) * y + (y - 1)‖ := by ring_nf
    _ ≤ ‖x - 1‖ * ‖y‖ + ‖y - 1‖ := by
        refine (norm_add_le _ _).trans ?_; rw [norm_mul]
    _ ≤ δ * 2 + δ := by
        gcongr
        · exact (norm_nonneg _).trans hx
    _ = 3 * δ := by ring

/-- If `u_n = u · w_n` on every compact set for large `n`, with `u` continuous and `w_n → 1`
uniformly on compact sets, then `u_n → u` locally uniformly. -/
lemma tendstoLocallyUniformly_of_mul_one {uₙ w : ℕ → ℂ → ℂ} {u : ℂ → ℂ} (hu : Continuous u)
    (hw : ∀ K, IsCompact K → ∀ δ > 0, ∀ᶠ n in atTop, ∀ s ∈ K,
      uₙ n s = u s * w n s ∧ ‖w n s - 1‖ ≤ δ) :
    TendstoLocallyUniformly uₙ u atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨M, hM⟩ := (hK.image hu).isBounded.exists_norm_le
  have hM' : ∀ s ∈ K, ‖u s‖ ≤ max M 1 := fun s hs =>
    (hM _ (mem_image_of_mem u hs)).trans (le_max_left _ _)
  have hMpos : 0 < max M 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  filter_upwards [hw K hK (ε / (2 * max M 1)) (by positivity)] with n hn s hs
  obtain ⟨heq, hsmall⟩ := hn s hs
  rw [dist_eq_norm, heq, show u s - u s * w n s = -(u s * (w n s - 1)) by ring, norm_neg,
    norm_mul]
  calc ‖u s‖ * ‖w n s - 1‖ ≤ max M 1 * (ε / (2 * max M 1)) :=
        mul_le_mul (hM' s hs) hsmall (norm_nonneg _) hMpos.le
    _ = ε / 2 := by field_simp
    _ < ε := half_lt_self hε

end ThreeIM
