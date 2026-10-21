module

public import RequestProject.ThreeIM.TransportTangentModel
public import RequestProject.ThreeIM.TransportScale

/-!
# Actual initial coordinates obtained from the tangent subsequence

The normalized difference divided by exp(z/2) converges to the stable
profile, and the canonical quotient minus one converges to zero. Their
holomorphy and reconstruction identities are derived on exhausting disks.
-/

@[expose] public section

open Filter Set Metric Topology

namespace ThreeIM

set_option autoImplicit false

noncomputable def transportInitialW (F G : ℂ → ℂ) (c : ℂ) (ε : ℝ) (z : ℂ) : ℂ :=
  (transportAmplitude F c ε z - transportAmplitude G c ε z) / Complex.exp (z / 2)

noncomputable def transportInitialH (F G : ℂ → ℂ) (c : ℂ) (ε : ℝ) (z : ℂ) : ℂ :=
  transportTangentQuotient F G c ε z - 1

private theorem initial_constant_family_tlu (D : ℂ → ℂ) :
    TendstoLocallyUniformlyOn (fun _ : ℕ => D) D atTop univ := by
  apply TendstoUniformlyOn.tendstoLocallyUniformlyOn
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  exact Eventually.of_forall fun n z _ => by simpa only [dist_self] using hη

theorem TransportTangentConvergence.initialW_converges
    {F G : ℕ → ℂ → ℂ} {ε : ℕ → ℝ} {c α : ℂ}
    (h : TransportTangentConvergence F G ε c α) :
    TendstoLocallyUniformlyOn (fun n => transportInitialW (F n) (G n) c (ε n))
      (fun z => 2 * α * (1 - Complex.exp (-z / 2))) atTop univ := by
  have hm : Continuous (fun z : ℂ => 2 * α * (Complex.exp (z / 2) - 1)) := by fun_prop
  have he : Continuous (fun z : ℂ => Complex.exp (z / 2)) := by fun_prop
  have ht := h.difference.div₀ (initial_constant_family_tlu (fun z => Complex.exp (z / 2)))
    hm.continuousOn he.continuousOn (fun z _ => Complex.exp_ne_zero _)
  apply ht.congr_right
  intro z _
  change (2 * α * (Complex.exp (z / 2) - 1)) / Complex.exp (z / 2) =
    2 * α * (1 - Complex.exp (-z / 2))
  rw [show -z / 2 = -(z / 2) by ring, Complex.exp_neg]
  field_simp [Complex.exp_ne_zero (z / 2)] <;> ring

theorem TransportTangentConvergence.initialH_converges
    {F G : ℕ → ℂ → ℂ} {ε : ℕ → ℝ} {c α : ℂ}
    (h : TransportTangentConvergence F G ε c α) :
    TendstoLocallyUniformlyOn (fun n => transportInitialH (F n) (G n) c (ε n))
      (fun _ => 0) atTop univ :=
  (h.quotient.sub (initial_constant_family_tlu (fun _ => 1))).congr_right
    (fun _ _ => sub_self (1 : ℂ))

theorem TransportTangentConvergence.initial_holomorphic
    {F G : ℕ → ℂ → ℂ} {ε : ℕ → ℝ} {c α : ℂ}
    (h : TransportTangentConvergence F G ε c α) {R : ℝ} (hR : 0 < R) :
    ∀ᶠ n in atTop,
      DifferentiableOn ℂ (transportInitialW (F n) (G n) c (ε n)) (ball 0 R) ∧
      DifferentiableOn ℂ (transportInitialH (F n) (G n) c (ε n)) (ball 0 R) := by
  filter_upwards [h.holomorphic R hR] with n hn
  have he : DifferentiableOn ℂ (fun z : ℂ => Complex.exp (z / 2)) (ball 0 R) := by fun_prop
  exact ⟨(hn.1.sub hn.2.1).div he (fun z _ => Complex.exp_ne_zero _), hn.2.2.sub_const 1⟩

theorem TransportTangentConvergence.initial_reconstruction
    {F G : ℕ → ℂ → ℂ} {ε : ℕ → ℝ} {c α : ℂ}
    (h : TransportTangentConvergence F G ε c α) (hε : ∀ n, ε n ≠ 0)
    {R : ℝ} (hR : 0 < R) : ∀ᶠ n in atTop, ∀ z ∈ ball 0 R,
    transportFiniteChart (F n) z - c =
      transportScale (ε n) z * transportInitialW (F n) (G n) c (ε n) z *
        (1 + transportInitialH (F n) (G n) c (ε n) z) ∧
    transportFiniteChart (G n) z - c =
      transportScale (ε n) z * transportInitialW (F n) (G n) c (ε n) z *
        transportInitialH (F n) (G n) c (ε n) z := by
  filter_upwards [h.representation R hR] with n hn z hz
  have hεc : (ε n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hε n)
  have hXF : (ε n : ℂ) * transportAmplitude (F n) c (ε n) z =
      transportFiniteChart (F n) z - c := by
    dsimp only [transportAmplitude]
    field_simp [hεc]
  have hYG : (ε n : ℂ) * transportAmplitude (G n) c (ε n) z =
      transportFiniteChart (G n) z - c := by
    dsimp only [transportAmplitude]
    field_simp [hεc]
  have hs : transportScale (ε n) z * transportInitialW (F n) (G n) c (ε n) z =
      (ε n : ℂ) *
        (transportAmplitude (F n) c (ε n) z - transportAmplitude (G n) c (ε n) z) := by
    dsimp only [transportScale, transportInitialW]
    field_simp [Complex.exp_ne_zero (z / 2)] <;> ring
  simp only [hs, transportInitialH]
  constructor
  · linear_combination -hXF + (ε n : ℂ) * (hn z hz).1
  · linear_combination -hYG + (ε n : ℂ) * (hn z hz).2

end ThreeIM
