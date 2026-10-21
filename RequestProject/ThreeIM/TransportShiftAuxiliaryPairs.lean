module

public import RequestProject.ThreeIM.TransportShiftDomains
public import RequestProject.ThreeIM.AuxiliaryPair
public import RequestProject.ThreeIM.AuxiliaryRatioExhaustion

/-! # The actual shifted pairs on exhausting fixed balls -/

@[expose] public section

open Filter Set Metric Topology

namespace ThreeIM

set_option autoImplicit false

theorem transport_eventually_shifted_auxiliary_on_balls
    {Ω : ℕ → Set ℂ} {F G u v : ℕ → ℂ → ℂ} {a : Fin 3 → ℂ}
    (pair : ∀ n, NormalizedPair (Ω n) (F n) (G n) a)
    {ε : ℕ → ℝ} (hεpos : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    {s : ℝ} (hs : 0 < s) {A B : ℂ}
    (hu : ∀ n, DifferentiableOn ℂ (u n) (Ω n))
    (hv : ∀ n, DifferentiableOn ℂ (v n) (Ω n))
    (hU : ∀ n, auxU a (F n) (G n) =ᶠ[codiscreteWithin (Ω n)] u n)
    (hV : ∀ n, auxV a (F n) (G n) =ᶠ[codiscreteWithin (Ω n)] v n)
    (hrect : ∀ R > 0, ∀ᶠ n in atTop, transportRect (ε n) R ⊆ Ω n)
    (hprofU : ∀ R > 0, ∀ η > 0, ∀ᶠ n in atTop, ∀ z ∈ transportRect (ε n) R,
      ‖u n z / (ε n * A * Complex.exp (z / 2)) - 1‖ ≤ η)
    (hprofV : ∀ R > 0, ∀ η > 0, ∀ᶠ n in atTop, ∀ z ∈ transportRect (ε n) R,
      ‖v n z / (ε n * B * Complex.exp (-z / 2)) - 1‖ ≤ η) :
    ∀ R > 0, ∀ᶠ n in atTop,
      AuxiliaryPairOn (ball 0 R)
        (fun z => F n (((2 * Real.log (s / ε n) : ℝ) : ℂ) + z))
        (fun z => G n (((2 * Real.log (s / ε n) : ℝ) : ℂ) + z))
        (fun z => u n (((2 * Real.log (s / ε n) : ℝ) : ℂ) + z))
        (fun z => v n (((2 * Real.log (s / ε n) : ℝ) : ℂ) + z)) a := by
  intro R hR
  let R' : ℝ := R + |2 * Real.log s| + 1
  have hR' : 0 < R' := by dsimp only [R']; positivity
  filter_upwards [eventually_transport_shift_closedBall_subset_rect hεpos hε hs hR,
    hrect R' hR', hprofU R' hR' (1 / 2) (by norm_num),
    hprofV R' hR' (1 / 2) (by norm_num)] with n hshift hrectn hpu hpv
  have hrectpair : AuxiliaryPairOn (transportRect (ε n) R') (F n) (G n) (u n) (v n) a := by
    refine ⟨(pair n).restrict hrectn, (hu n).mono hrectn, (hv n).mono hrectn,
      ?_, ?_, (hU n).filter_mono (Filter.codiscreteWithin.mono hrectn),
      (hV n).filter_mono (Filter.codiscreteWithin.mono hrectn)⟩
    · intro z hz hzero
      have hb := hpu z hz
      simp only [hzero, zero_div, zero_sub, norm_neg, norm_one] at hb
      norm_num at hb
    · intro z hz hzero
      have hb := hpv z hz
      simp only [hzero, zero_div, zero_sub, norm_neg, norm_one] at hb
      norm_num at hb
  have hmaps : MapsTo (fun z : ℂ => ((2 * Real.log (s / ε n) : ℝ) : ℂ) + 1 * z)
      (ball 0 R) (transportRect (ε n) R') := by
    intro z hz
    simpa only [one_mul] using hshift z (ball_subset_closedBall hz)
  simpa only [one_mul] using hrectpair.comp_affine 1
    (((2 * Real.log (s / ε n) : ℝ) : ℂ)) one_ne_zero hmaps

theorem auxiliary_pairs_exhausting_subsequence
    {F G u v : ℕ → ℂ → ℂ} {a : Fin 3 → ℂ}
    (h : ∀ R > 0, ∀ᶠ n in atTop, AuxiliaryPairOn (ball 0 R) (F n) (G n) (u n) (v n) a) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ n : ℕ,
      AuxiliaryPairOn (ball 0 ((n : ℝ) + 1)) (F (σ n)) (G (σ n)) (u (σ n)) (v (σ n)) a := by
  classical
  have hex : ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N,
      AuxiliaryPairOn (ball 0 ((k : ℝ) + 1)) (F n) (G n) (u n) (v n) a :=
    fun k => eventually_atTop.mp (h _ (by positivity))
  choose N hN using hex
  let σ : ℕ → ℕ := Nat.rec (N 0) (fun k q => max (N (k + 1)) (q + 1))
  have hσge : ∀ k, N k ≤ σ k := by
    intro k
    cases k with
    | zero => exact le_rfl
    | succ k => exact le_max_left _ _
  have hσ : StrictMono σ := strictMono_nat_of_lt_succ fun k => by
    change σ k < max (N (k + 1)) (σ k + 1)
    exact (Nat.lt_succ_self _).trans_le (le_max_right _ _)
  exact ⟨σ, hσ, fun k => hN k _ (hσge k)⟩

end ThreeIM
