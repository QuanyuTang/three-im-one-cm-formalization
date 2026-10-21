module

public import RequestProject.ThreeIM.MathlibImports

/-!
# Holomorphic roots (used for Lemma 7.8)

* a zero-free holomorphic function on a disk has a holomorphic logarithm there;
* an entire function whose zero orders are divisible by `p` has a holomorphic `p`-th root on
  every disk centred at `0`;
* two such roots on a disk differ by a `p`-th root of unity.
-/

@[expose] public section

open Filter Set Metric Topology

namespace ThreeIM

/-- A zero-free holomorphic function on a disk has a holomorphic logarithm on the disk. -/
lemma exists_log_on_ball {g : ℂ → ℂ} {c : ℂ} {R : ℝ} (hg : DifferentiableOn ℂ g (ball c R))
    (hg0 : ∀ z ∈ ball c R, g z ≠ 0) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L (ball c R) ∧ ∀ z ∈ ball c R, Complex.exp (L z) = g z := by
  have ha := hg.analyticOnNhd isOpen_ball
  have hd : DifferentiableOn ℂ (fun z => deriv g z / g z) (ball c R) :=
    (ha.deriv.differentiableOn).div hg hg0
  obtain ⟨F, hF⟩ := hd.isExactOn_ball
  by_cases hR : 0 < R
  swap
  · refine ⟨fun _ => 0, differentiableOn_const _, fun z hz => ?_⟩
    exact absurd (pos_of_mem_ball hz) hR
  have hc : c ∈ ball c R := mem_ball_self hR
  have hderiv : ∀ z ∈ ball c R, HasDerivAt (fun w => g w * Complex.exp (-F w)) 0 z := by
    intro z hz
    have h1 : HasDerivAt g (deriv g z) z :=
      (hg.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
    have h2 := ((hF z hz).neg).cexp
    convert h1.mul h2 using 1
    field_simp [hg0 z hz]
    ring
  have hconst : ∀ z ∈ ball c R, g z * Complex.exp (-F z) = g c * Complex.exp (-F c) := by
    intro z hz
    exact isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c R).isPreconnected
      (fun w hw => (hderiv w hw).differentiableAt.differentiableWithinAt)
      (fun w hw => (hderiv w hw).deriv) hz hc
  set K := g c * Complex.exp (-F c)
  have hK : K ≠ 0 := mul_ne_zero (hg0 c hc) (Complex.exp_ne_zero _)
  refine ⟨fun z => F z + Complex.log K, ?_, fun z hz => ?_⟩
  · exact (fun w hw => ((hF w hw).differentiableAt.add_const _).differentiableWithinAt)
  · rw [Complex.exp_add, Complex.exp_log hK, ← hconst z hz, mul_comm, mul_assoc,
      ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]

/-- An entire function `h ≢ 0` whose zero orders are divisible by `p` has a holomorphic `p`-th
root on every disk `D(0, R)`. -/
lemma exists_root_on_ball {h : ℂ → ℂ} (hh : Differentiable ℂ h) (h0 : ∃ z, h z ≠ 0)
    {p : ℕ} (hp : 1 ≤ p) (hdiv : ∀ z, (p : ℕ∞) ∣ analyticOrderAt h z) (R : ℝ) :
    ∃ u : ℂ → ℂ, DifferentiableOn ℂ u (ball 0 R) ∧ ∀ z ∈ ball 0 R, u z ^ p = h z := by
  set U := closedBall (0 : ℂ) R
  have hmero : MeromorphicOn h U := fun z _ => (hh.analyticAt z).meromorphicAt
  have hntop : ∀ z, meromorphicOrderAt h z ≠ ⊤ := by
    intro z
    obtain ⟨w, hw⟩ := h0
    have hw' : meromorphicOrderAt h w ≠ ⊤ := by
      rw [(hh.analyticAt w).meromorphicOrderAt_eq, (hh.analyticAt w).analyticOrderAt_eq_zero.2 hw]
      simp
    intro hz
    exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      (fun z _ => (hh.analyticAt z).meromorphicAt) isPreconnected_univ
      (mem_univ w) (mem_univ z) hw' hz
  -- factor out the zeros of `h` in the closed disk
  set D := MeromorphicOn.divisor h U
  have hfin : D.support.Finite := D.finiteSupport (isCompact_closedBall 0 R)
  obtain ⟨g, hgan, hg0, heq⟩ := hmero.extract_zeros_poles (fun u => hntop u) hfin
  -- the divisor is nonnegative and divisible by `p`
  have hD : ∀ u, 0 ≤ D u ∧ (p : ℤ) ∣ D u := by
    intro u
    by_cases hu : u ∈ U
    · have hne : analyticOrderAt h u ≠ ⊤ := fun ht => hntop u (by
        rw [(hh.analyticAt u).meromorphicOrderAt_eq, ht]; rfl)
      obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hne
      have hpn : p ∣ n := by
        obtain ⟨c, hc⟩ := hdiv u
        rw [← hn] at hc
        induction c using ENat.recTopCoe with
        | top =>
          exfalso
          rw [ENat.mul_top (by exact_mod_cast (show p ≠ 0 by omega))] at hc
          exact ENat.coe_ne_top n hc
        | coe m => exact ⟨m, by exact_mod_cast hc⟩
      rw [MeromorphicOn.divisor_apply hmero hu, (hh.analyticAt u).meromorphicOrderAt_eq, ← hn]
      simp only [ENat.map_coe, WithTop.untop₀_coe]
      exact ⟨by positivity, by exact_mod_cast hpn⟩
    · simp [D, hu]
  -- the polynomial `w` with `w^p = ∏ (z - u)^{D u}`
  set S := hfin.toFinset
  set w : ℂ → ℂ := fun z => ∏ u ∈ S, (z - u) ^ (D u / p).toNat
  have hw : Differentiable ℂ w := by
    intro z
    simp only [w]
    fun_prop
  have hfac : ∀ z, (∏ᶠ u, (· - u) ^ D u : ℂ → ℂ) z = w z ^ p := by
    intro z
    have hsupp : (Function.mulSupport fun u => ((· - u) ^ D u : ℂ → ℂ)) ⊆ S := by
      intro u hu
      simp only [S, Set.Finite.coe_toFinset, Function.mem_support]
      intro h0
      apply hu
      simp [h0]
    rw [finprod_apply ((S.finite_toSet).subset hsupp),
      finprod_eq_prod_of_mulSupport_subset _ (fun u hu => hsupp (fun h1 => hu (by
        simp only [h1, Pi.one_apply]))), ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun u _ => ?_
    obtain ⟨hD0, k, hk⟩ := hD u
    have hk0 : 0 ≤ k := by
      rcases le_or_gt 0 k with h | h
      · exact h
      · exfalso; nlinarith
    have : D u / p = k := by rw [hk]; exact Int.mul_ediv_cancel_left _ (by omega)
    simp only [Pi.pow_apply, this, ← pow_mul]
    rw [hk, show (p : ℤ) * k = ((k.toNat * p : ℕ) : ℤ) by
      push_cast; rw [Int.toNat_of_nonneg hk0]; ring, zpow_natCast]
  -- `h = w^p g` on the open disk
  have hsub : ball (0 : ℂ) R ⊆ U := ball_subset_closedBall
  have hball : ∀ z ∈ ball (0 : ℂ) R, h z = w z ^ p * g z := by
    intro z hz
    have h1 := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 heq) z (hsub hz)
    have h2 : ∀ᶠ y in 𝓝[≠] z, h y = w y ^ p * g y := by
      filter_upwards [h1, nhdsWithin_le_nhds (isOpen_ball.mem_nhds hz)] with y hy hyb
      rcases hy with hy | hy
      · have hy' : h y = ((∏ᶠ u, (· - u) ^ D u : ℂ → ℂ) • g) y := hy
        rw [hy', Pi.smul_apply', smul_eq_mul, hfac]
      · exact absurd (hsub hyb) hy
    have hc1 : ContinuousAt h z := (hh z).continuousAt
    have hc2 : ContinuousAt (fun y => w y ^ p * g y) z :=
      ((hw z).continuousAt.pow p).mul (hgan z (hsub hz)).continuousAt
    exact tendsto_nhds_unique_of_eventuallyEq (hc1.tendsto.mono_left nhdsWithin_le_nhds)
      (hc2.tendsto.mono_left nhdsWithin_le_nhds) h2
  -- a logarithm of the zero-free factor `g`
  obtain ⟨L, hL, hLg⟩ := exists_log_on_ball (g := g) (c := 0) (R := R)
    (fun z hz => (hgan z (hsub hz)).differentiableAt.differentiableWithinAt)
    (fun z hz => hg0 ⟨z, hsub hz⟩)
  refine ⟨fun z => w z * Complex.exp (L z / p), ?_, fun z hz => ?_⟩
  · intro z hz
    exact ((hw z).differentiableWithinAt).mul (((hL z hz).div_const _).cexp)
  · have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
    rw [mul_pow, ← Complex.exp_nat_mul, mul_div_cancel₀ _ hp0, hLg z hz, hball z hz]

/-- Two holomorphic `p`-th roots of an entire function `h ≢ 0` on a disk differ by a root of
unity. -/
lemma root_unique_on_ball {h : ℂ → ℂ} (hh : Differentiable ℂ h) (h0 : ∃ z, h z ≠ 0)
    {p : ℕ} (hp : 1 ≤ p) {R : ℝ} (hR : 0 < R) {u v : ℂ → ℂ}
    (hu : DifferentiableOn ℂ u (ball 0 R)) (hv : DifferentiableOn ℂ v (ball 0 R))
    (hup : ∀ z ∈ ball 0 R, u z ^ p = h z) (hvp : ∀ z ∈ ball 0 R, v z ^ p = h z) :
    ∃ ζ : ℂ, ζ ^ p = 1 ∧ ∀ z ∈ ball 0 R, v z = ζ * u z := by
  have hdisc : IsDiscrete {x : ℂ | x ^ p = 1} := by
    have : {x : ℂ | x ^ p = 1}.Finite := by
      have := (Polynomial.nthRoots p (1:ℂ)).toFinset.finite_toSet
      convert this using 1
      ext x; simp [Polynomial.mem_nthRoots (by omega : 0 < p)]
    exact Finite.isDiscrete this
  -- a point of the disk where `h ≠ 0`
  obtain ⟨z₀, hz₀, hhz₀⟩ : ∃ z₀ ∈ ball (0 : ℂ) R, h z₀ ≠ 0 := by
    have han : AnalyticOnNhd ℂ h univ := fun z _ => hh.analyticAt z
    rcases (han 0 (mem_univ _)).eventually_eq_zero_or_eventually_ne_zero with h1 | h1
    · exfalso
      obtain ⟨w, hw⟩ := h0
      exact hw (han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
        (mem_univ 0) h1 (mem_univ w))
    · have := (h1.and (eventually_nhdsWithin_of_eventually_nhds
        (isOpen_ball.mem_nhds (mem_ball_self hR)))).exists
      obtain ⟨w, hw1, hw2⟩ := this
      exact ⟨w, hw2, hw1⟩
  have hu0 : u z₀ ≠ 0 := by
    intro h'; apply hhz₀; rw [← hup z₀ hz₀, h', zero_pow (by omega)]
  have huc : ContinuousAt u z₀ := (hu.differentiableAt (isOpen_ball.mem_nhds hz₀)).continuousAt
  -- a small disk around `z₀` inside `D(0,R)` where `u ≠ 0`
  have hev : ∀ᶠ z in 𝓝 z₀, u z ≠ 0 ∧ z ∈ ball (0 : ℂ) R :=
    (huc.eventually_ne hu0).and (isOpen_ball.mem_nhds hz₀)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.eventually_nhds_iff_ball.1 hev
  set ζ := v z₀ / u z₀
  -- on it, `v / u` is a continuous function with values in the discrete set of roots of unity
  have hloc : ∀ z ∈ ball z₀ δ, v z / u z = ζ := by
    intro z hz
    refine (convex_ball z₀ δ).isPreconnected.constant_of_mapsTo hdisc (f := fun z => v z / u z)
      ?_ ?_ hz (mem_ball_self hδ)
    · intro w hw
      have h1 := hδsub w hw
      exact ((hv.differentiableAt (isOpen_ball.mem_nhds h1.2)).continuousAt.div
        (hu.differentiableAt (isOpen_ball.mem_nhds h1.2)).continuousAt h1.1).continuousWithinAt
    · intro w hw
      have h1 := hδsub w hw
      simp only [mem_setOf_eq, div_pow, hup w h1.2, hvp w h1.2]
      exact div_self (by rw [← hup w h1.2]; exact pow_ne_zero _ h1.1)
  refine ⟨ζ, ?_, ?_⟩
  · rw [div_pow, hup z₀ hz₀, hvp z₀ hz₀, div_self hhz₀]
  · have heq : v =ᶠ[𝓝 z₀] fun z => ζ * u z := by
      filter_upwards [Metric.ball_mem_nhds z₀ hδ] with z hz
      rw [← hloc z hz, div_mul_cancel₀ _ (hδsub z hz).1]
    exact (hv.analyticOnNhd isOpen_ball).eqOn_of_preconnected_of_eventuallyEq
      ((hu.const_mul ζ).analyticOnNhd isOpen_ball) (convex_ball 0 R).isPreconnected hz₀ heq

/-- An entire function `h ≢ 0` whose zero orders are divisible by `p` is the `p`-th power of
an entire function (the roots on the disks `D(0, n + 1)` are glued after normalisation by roots of
unity).  This is Lemma 7.8, stated in `Normality.lean`. -/
theorem exists_entire_root_of_dvd {h : ℂ → ℂ} (hh : Differentiable ℂ h) (h0 : ∃ z, h z ≠ 0)
    {p : ℕ} (hp : 1 ≤ p) (hdiv : ∀ z, (p : ℕ∞) ∣ analyticOrderAt h z) :
    ∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ z, u z ^ p = h z := by
  -- compatible roots on the disks `D(0, n + 1)`
  have step : ∀ n : ℕ, ∀ u : ℂ → ℂ, DifferentiableOn ℂ u (ball 0 (n + 1)) →
      (∀ z ∈ ball (0 : ℂ) (n + 1), u z ^ p = h z) →
      ∃ v : ℂ → ℂ, DifferentiableOn ℂ v (ball 0 (((n + 1 : ℕ) : ℝ) + 1)) ∧
        (∀ z ∈ ball (0 : ℂ) (((n + 1 : ℕ) : ℝ) + 1), v z ^ p = h z) ∧
        ∀ z ∈ ball (0 : ℂ) (n + 1), v z = u z := by
    intro n u hu hup
    push_cast
    obtain ⟨w, hw, hwp⟩ := exists_root_on_ball hh h0 hp hdiv (n + 1 + 1)
    have hsub : ball (0 : ℂ) (n + 1) ⊆ ball 0 (n + 1 + 1) := ball_subset_ball (by linarith)
    obtain ⟨ζ, hζ, hwζ⟩ := root_unique_on_ball hh h0 hp (R := n + 1) (by positivity) hu
      (hw.mono hsub) hup (fun z hz => hwp z (hsub hz))
    have hζ0 : ζ ≠ 0 := by rintro rfl; simp [zero_pow (by omega : p ≠ 0)] at hζ
    refine ⟨fun z => ζ⁻¹ * w z, hw.const_mul _, fun z hz => ?_, fun z hz => ?_⟩
    · rw [mul_pow, inv_pow, hζ, inv_one, one_mul, hwp z hz]
    · simp only [hwζ z hz]; field_simp
  let S : ℕ → Type := fun n => {u : ℂ → ℂ // DifferentiableOn ℂ u (ball 0 (n + 1)) ∧
    ∀ z ∈ ball (0 : ℂ) (n + 1), u z ^ p = h z}
  have s0 : S 0 := by
    choose u hu hup using exists_root_on_ball hh h0 hp hdiv (((0 : ℕ) : ℝ) + 1)
    exact ⟨u, hu, hup⟩
  let next : ∀ n, S n → S (n + 1) := fun n u =>
    ⟨(step n u.1 u.2.1 u.2.2).choose, (step n u.1 u.2.1 u.2.2).choose_spec.1,
      (step n u.1 u.2.1 u.2.2).choose_spec.2.1⟩
  have next_eq : ∀ n (u : S n), ∀ z ∈ ball (0 : ℂ) (n + 1), (next n u).1 z = u.1 z :=
    fun n u => (step n u.1 u.2.1 u.2.2).choose_spec.2.2
  let seq : ∀ n, S n := fun n => Nat.rec s0 next n
  have seq_succ : ∀ n, seq (n + 1) = next n (seq n) := fun n => rfl
  -- compatibility
  have compat : ∀ n k : ℕ, ∀ z ∈ ball (0 : ℂ) (n + 1), (seq (n + k)).1 z = (seq n).1 z := by
    intro n k
    induction k with
    | zero => intro z _; rfl
    | succ k ih =>
      intro z hz
      have hz' : z ∈ ball (0 : ℂ) ((n + k : ℕ) + 1) :=
        ball_subset_ball (by push_cast; linarith) hz
      rw [← add_assoc, seq_succ, next_eq _ _ z hz', ih z hz]
  let N : ℂ → ℕ := fun z => ⌈‖z‖⌉₊
  have hN : ∀ z : ℂ, z ∈ ball (0 : ℂ) (N z + 1) := fun z => by
    simp only [mem_ball, dist_zero_right]
    linarith [Nat.le_ceil ‖z‖]
  refine ⟨fun z => (seq (N z)).1 z, ?_, fun z => (seq (N z)).2.2 z (hN z)⟩
  -- the root agrees with `seq n` on `D(0, n + 1)`
  have hagree : ∀ n : ℕ, ∀ z ∈ ball (0 : ℂ) (n + 1), (seq (N z)).1 z = (seq n).1 z := by
    intro n z hz
    rcases le_total n (N z) with hle | hle
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
      rw [hk]; exact compat n k z hz
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
      rw [hk]; exact (compat (N z) k z (hN z)).symm
  intro z
  have hmem : ball (0 : ℂ) ((N z + 1 : ℕ) + 1) ∈ 𝓝 z :=
    isOpen_ball.mem_nhds (ball_subset_ball (by push_cast; linarith) (hN z))
  have hev : (fun w => (seq (N w)).1 w) =ᶠ[𝓝 z] (seq (N z + 1)).1 :=
    Filter.eventually_of_mem hmem fun w hw => hagree _ w hw
  exact (((seq (N z + 1)).2.1.differentiableAt hmem)).congr_of_eventuallyEq hev

end ThreeIM
