module

public import RequestProject.ThreeIM.SphereLimits

/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Will (Ziang) Li

Adapted by Codex from the nested subsequence and gluing argument in
NoWanderingDomains.NormalFamilies.Zalcman, upstream commit
0a6497b0cc9ed39a6a705bf013449635894b56d0. The rescaling-specific
index shifts are replaced by a normal family on each fixed disk.
-/

/-! # Diagonal normality on exhausting disks -/

@[expose] public section

open Filter Set Metric Topology OnePoint NoWanderingDomains

namespace ThreeIM

set_option maxHeartbeats 400000 in
theorem sphere_isNormal_of_normal_balls {𝓕 : Set (ℂ → OnePoint ℂ)}
    (hN : ∀ m : ℕ, IsNormal 𝓕 (ball 0 ((m : ℝ) + 1))) : IsNormal 𝓕 univ := by
  classical
  intro Q
  have step : ∀ (m : ℕ) (h : ℕ → ℕ), ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∃ g : ℂ → OnePoint ℂ, TendstoLocallyUniformlyOn
        (fun n => (Q (h (ψ n)) : ℂ → OnePoint ℂ)) g atTop (ball 0 ((m : ℝ) + 1)) := by
    intro m h
    exact hN m (fun n => Q (h n))
  choose ψ hψ g0 hg0 using step
  let τ : ℕ → ℕ → ℕ := fun m =>
    Nat.rec (motive := fun _ => ℕ → ℕ) (ψ 0 id) (fun i ih => ih ∘ ψ (i + 1) ih) m
  let G : ℕ → ℂ → ℂ̂ := fun m =>
    Nat.casesOn (motive := fun _ => ℂ → ℂ̂) m (g0 0 id) (fun i => g0 (i + 1) (τ i))
  have τ_mono : ∀ m, StrictMono (τ m) := by
    intro m
    induction m with
    | zero => exact hψ 0 id
    | succ i ih => exact ih.comp (hψ (i + 1) (τ i))
  have τ_tlu : ∀ m, TendstoLocallyUniformlyOn
      (fun j => (Q (τ m j) : ℂ → OnePoint ℂ)) (G m) atTop (ball 0 ((m : ℝ) + 1)) := by
    intro m
    cases m with
    | zero => exact hg0 0 id
    | succ i => exact hg0 (i + 1) (τ i)
  have τ_refine : ∀ i m, ∃ e : ℕ → ℕ, (∀ k, k ≤ e k) ∧ ∀ k, τ (i + m) k = τ i (e k) := by
    intro i m
    induction m with
    | zero => exact ⟨id, fun k => le_rfl, fun k => rfl⟩
    | succ m ih =>
      obtain ⟨e, he, heq⟩ := ih
      exact ⟨fun k => e (ψ (i + m + 1) (τ (i + m)) k),
        fun k => le_trans (hψ (i + m + 1) (τ (i + m))).le_apply (he _),
        fun k => heq (ψ (i + m + 1) (τ (i + m)) k)⟩
  let d : ℕ → ℕ := fun k => τ k k
  have d_mono : StrictMono d := by
    apply strictMono_nat_of_lt_succ
    intro k
    calc d k = τ k k := rfl
      _ < τ k (k + 1) := τ_mono k (Nat.lt_succ_self k)
      _ ≤ τ k (ψ (k + 1) (τ k) (k + 1)) :=
          (τ_mono k).monotone (hψ (k + 1) (τ k)).le_apply
      _ = d (k + 1) := rfl
  have d_sub : ∀ m k, m ≤ k → ∃ n, k ≤ n ∧ d k = τ m n := by
    intro m k hmk
    obtain ⟨e, he, heq⟩ := τ_refine m (k - m)
    have hk : m + (k - m) = k := Nat.add_sub_cancel' hmk
    have h2 := heq k
    rw [hk] at h2
    exact ⟨e k, he k, h2⟩
  -- the diagonal converges locally uniformly on every stage ball
  have d_tlu : ∀ m, TendstoLocallyUniformlyOn
      (fun k => (Q (d k) : ℂ → OnePoint ℂ))
      (G m) atTop (ball 0 ((m : ℝ) + 1)) := by
    intro m v hv x hx
    obtain ⟨t, ht, hF⟩ := τ_tlu m v hv x hx
    refine ⟨t, ht, ?_⟩
    rw [eventually_atTop] at hF ⊢
    obtain ⟨N, hN⟩ := hF
    refine ⟨max m N, fun k hk => ?_⟩
    obtain ⟨n, hkn, hdn⟩ := d_sub m k (le_trans (le_max_left m N) hk)
    intro y hy
    have h5 := hN n (le_trans (le_trans (le_max_right m N) hk) hkn) y hy
    change (G m y, (Q (d k) : ℂ → OnePoint ℂ) y) ∈ v
    rw [hdn]
    exact h5
  -- ## glue the stage limits into a single limit function
  have hRball : ∀ ζ : ℂ, ∃ m : ℕ, ζ ∈ ball (0 : ℂ) ((m : ℝ) + 1) := by
    intro ζ
    obtain ⟨m, hm⟩ := exists_nat_gt ‖ζ‖
    exact ⟨m, mem_ball_zero_iff.mpr (by linarith)⟩
  have glex : ∀ ζ : ℂ, ∃ wv : ℂ̂, ∀ m : ℕ,
      ζ ∈ ball (0 : ℂ) ((m : ℝ) + 1) → wv = G m ζ := by
    intro ζ
    obtain ⟨i, hi⟩ := hRball ζ
    refine ⟨G i ζ, fun m hm => ?_⟩
    exact tendsto_nhds_unique ((d_tlu i).tendsto_at hi) ((d_tlu m).tendsto_at hm)
  choose gl hgl using glex
  -- locally uniform convergence on all of `ℂ`
  have final_tlu : TendstoLocallyUniformlyOn
      (fun k => (Q (d k) : ℂ → OnePoint ℂ)) gl atTop Set.univ := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
    intro Kc hKcU hKc
    obtain ⟨RK, hRK⟩ := hKc.isBounded.subset_ball 0
    obtain ⟨m, hm⟩ := exists_nat_gt RK
    have hKb : Kc ⊆ ball (0 : ℂ) ((m : ℝ) + 1) :=
      hRK.trans (ball_subset_ball (by linarith))
    have h1 := (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball).mp
      (d_tlu m) Kc hKb hKc
    exact h1.congr_right fun ζ hζ => (hgl ζ m (hKb hζ)).symm
  exact ⟨d, d_mono, gl, final_tlu⟩

end ThreeIM
