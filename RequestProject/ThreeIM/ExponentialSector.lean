module

public import RequestProject.ThreeIM.ExponentialGrowthCore
public import RequestProject.ThreeIM.Growth

/-!
# Omission of the shared values in proper sectors (Lemma 8.4, first part)

For an exponential pair, a shared point `t` with multiplicities `(m, n)` satisfies
`e^{2t} = m/n` (Lemma 8.2).  In a proper right sector `Re t ≥ δ|t|` this forces
`m ≥ e^{2δ|t|}`, and in a proper left sector `n ≥ e^{2δ|t|}`.  On the other hand a zero of
multiplicity `m` of `f - a_j` at `|t| = r` gives `m log 2 ≤ N(2r, a_j; f) ≤ T(2r, f) + O(1)`,
which is `O(r)` by Lemma 8.3.  Hence the three finite shared values are omitted sufficiently far
out in every proper sector.
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

/-- A single point of a nonnegative divisor contributes `D(z) log (r/|z|)` to its logarithmic
counting function. -/
lemma logCounting_ge_single (D : Function.locallyFinsupp ℂ ℤ) (hD : 0 ≤ D) {r : ℝ} (hr : 1 ≤ r)
    {z : ℂ} (hzr : ‖z‖ ≤ r) :
    (D z : ℝ) * Real.log (r * ‖z‖⁻¹) ≤ Function.locallyFinsuppWithin.logCounting D r := by
  have hr0 : 0 < r := by linarith
  have habs : |r| = r := abs_of_pos hr0
  set T := D.toClosedBall r
  have hfin : T.support.Finite := T.finiteSupport (isCompact_closedBall 0 |r|)
  have hterm : ∀ w, 0 ≤ (T w : ℝ) * Real.log (r * ‖w‖⁻¹) := by
    intro w
    by_cases hw : w ∈ Metric.closedBall (0 : ℂ) |r|
    · have hT : T w = D w := Function.locallyFinsuppWithin.toClosedBall_eval_within _ hw
      rw [hT]
      apply mul_nonneg (by exact_mod_cast hD w)
      rcases eq_or_ne w 0 with rfl | hw0
      · simp
      · apply Real.log_nonneg
        rw [Metric.mem_closedBall, dist_zero_right, habs] at hw
        rw [← div_eq_mul_inv, le_div_iff₀ (norm_pos_iff.2 hw0)]; linarith
    · have : T w = 0 := by
        by_contra h
        exact hw (Function.locallyFinsuppWithin.toClosedBall_support_subset_closedBall D h)
      simp [this]
  have hzb : z ∈ Metric.closedBall (0 : ℂ) |r| := by
    rw [Metric.mem_closedBall, dist_zero_right, habs]; exact hzr
  have hTz : T z = D z := Function.locallyFinsuppWithin.toClosedBall_eval_within _ hzb
  unfold Function.locallyFinsuppWithin.logCounting
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset)]
  · have h0 : 0 ≤ (D 0 : ℝ) * Real.log r :=
      mul_nonneg (by exact_mod_cast hD 0) (Real.log_nonneg hr)
    by_cases hzs : z ∈ hfin.toFinset
    · have := Finset.single_le_sum (f := fun w => (T w : ℝ) * Real.log (r * ‖w‖⁻¹))
        (fun w _ => hterm w) hzs
      simp only [hTz] at this
      linarith
    · have hT0 : T z = 0 := by
        simpa [Finite.mem_toFinset, Function.mem_support] using hzs
      rw [hTz] at hT0
      rw [hT0]
      have := Finset.sum_nonneg (s := hfin.toFinset) (fun w _ => hterm w)
      push_cast
      linarith
  · intro w hw
    simp only [Finite.coe_toFinset, Function.mem_support] at hw ⊢
    intro h; apply hw; simp [T] at h; simp [h]

/-- A zero of multiplicity `m` of `h - c` at a point `t` with `|t| = r ≥ 1` gives
`m log 2 ≤ T(2r, h) + O(1)`. -/
lemma mult_log_two_le_charT {h : ℂ → ℂ} (hh : MeromorphicOn h univ) (c : ℂ) :
    ∃ C : ℝ, ∀ t : ℂ, 1 ≤ ‖t‖ →
      (mult h (c : Sphere) t : ℝ) * Real.log 2 ≤ charT h (2 * ‖t‖) + C := by
  obtain ⟨C, hC⟩ := logCounting_fiber_le hh c
  refine ⟨C, fun t ht => ?_⟩
  have ht0 : t ≠ 0 := by
    intro h0; rw [h0, norm_zero] at ht; linarith
  have hpos : 0 < ‖t‖ := norm_pos_iff.2 ht0
  have hD : (0 : Function.locallyFinsupp ℂ ℤ) ≤ (MeromorphicOn.divisor (fun w => h w - c) univ)⁺ :=
    fun z => by simp [posPart_nonneg]
  have h1 := logCounting_ge_single _ hD (r := 2 * ‖t‖) (by linarith) (z := t) (by linarith)
  rw [divisor_posPart_apply hh c t] at h1
  have h2 : Real.log (2 * ‖t‖ * ‖t‖⁻¹) = Real.log 2 := by
    rw [mul_assoc, mul_inv_cancel₀ hpos.ne', mul_one]
  rw [h2] at h1
  push_cast at h1
  linarith [hC (2 * ‖t‖)]

/-- **Lemma 8.4, first part** (omission in proper sectors).  For an exponential pair and every
`δ > 0`, the three finite shared values are omitted by `f` (and by `g`) at all points `t` with
`|Re t| ≥ δ |t|` and `|t|` sufficiently large. -/
theorem ExponentialPair.omits_shared_in_sectors {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ}
    (h : ExponentialPair a f g κ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ R : ℝ, ∀ t : ℂ, R ≤ ‖t‖ → δ * ‖t‖ ≤ |t.re| →
      ∀ j, mult f (a j : Sphere) t = 0 ∧ mult g (a j : Sphere) t = 0 := by
  have hP := h.pair
  obtain ⟨K, hK⟩ := h.linear_growth
  obtain ⟨r₁, hr₁⟩ := eventually_atTop.1 hK
  choose Cf hCf using fun j => mult_log_two_le_charT hP.nonconst_f.1 (a j)
  choose Cg hCg using fun j => mult_log_two_le_charT hP.nonconst_g.1 (a j)
  set C : ℝ := ∑ j, (|Cf j| + |Cg j|) with hCdef
  have hCf_le : ∀ j, Cf j ≤ C := fun j => by
    have := Finset.single_le_sum (f := fun j => |Cf j| + |Cg j|)
      (fun j _ => by positivity) (Finset.mem_univ j)
    have := le_abs_self (Cf j); have := abs_nonneg (Cg j)
    simp only [hCdef]; linarith
  have hCg_le : ∀ j, Cg j ≤ C := fun j => by
    have := Finset.single_le_sum (f := fun j => |Cf j| + |Cg j|)
      (fun j _ => by positivity) (Finset.mem_univ j)
    have := le_abs_self (Cg j); have := abs_nonneg (Cf j)
    simp only [hCdef]; linarith
  have hC0 : 0 ≤ C := Finset.sum_nonneg (fun j _ => by positivity)
  set R : ℝ := max (max r₁ 1) ((4 * |K| + 2 * C + 2) / δ ^ 2) with hRdef
  refine ⟨R, fun t htR hsec j => ?_⟩
  set r := ‖t‖ with hr
  have hr1 : 1 ≤ r := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) htR
  have hrr₁ : r₁ ≤ 2 * r := by
    have : r₁ ≤ R := le_trans (le_max_left _ _) (le_max_left _ _)
    linarith
  have hRδ : (4 * |K| + 2 * C + 2) / δ ^ 2 ≤ r := le_trans (le_max_right _ _) htR
  have hδr : 4 * |K| + 2 * C + 2 ≤ δ ^ 2 * r := by
    rw [div_le_iff₀ (by positivity)] at hRδ; linarith
  -- the key growth contradiction: a multiplicity `≥ e^{2δr}` cannot be `≤ (T(2r) + C)/log 2`
  have hbig : ∀ M : ℝ, Real.exp (2 * δ * r) ≤ M → M * Real.log 2 ≤ 2 * K * r + C → False := by
    intro M hM hMle
    have hl2 : (1 / 2 : ℝ) < Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    have he : (1 + δ * r) ^ 2 ≤ Real.exp (2 * δ * r) := by
      have h1 := Real.add_one_le_exp (δ * r)
      have h2 : Real.exp (2 * δ * r) = Real.exp (δ * r) ^ 2 := by
        rw [← Real.exp_nat_mul]; push_cast; ring_nf
      rw [h2]
      have : 0 ≤ 1 + δ * r := by positivity
      nlinarith
    have hM0 : 0 ≤ M := le_trans (Real.exp_pos _).le hM
    have hsq : δ ^ 2 * r * r ≤ (1 + δ * r) ^ 2 := by nlinarith [mul_pos hδ (by linarith : (0:ℝ) < r)]
    have h3 : (4 * |K| + 2 * C + 2) * r ≤ M := by nlinarith
    have hK' : K ≤ |K| := le_abs_self K
    nlinarith
  have hfK : charT f (2 * r) ≤ K * (2 * r) := (hr₁ (2 * r) hrr₁).1
  have hgK : charT g (2 * r) ≤ K * (2 * r) := (hr₁ (2 * r) hrr₁).2
  by_contra hne
  have hfpos : 0 < mult f (a j : Sphere) t := by
    by_contra h0
    push_neg at h0
    have hf0 : mult f (a j : Sphere) t = 0 := by omega
    have hg0 : mult g (a j : Sphere) t = 0 := by
      have := (hP.im j t (mem_univ t))
      by_contra hg
      have := this.2 (Nat.pos_of_ne_zero hg); omega
    exact hne ⟨hf0, hg0⟩
  have hgpos : 0 < mult g (a j : Sphere) t := (hP.im j t (mem_univ t)).1 hfpos
  obtain ⟨-, hexp⟩ := h.shared_point hfpos
  set m := mult f (a j : Sphere) t
  set n := mult g (a j : Sphere) t
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hfpos
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hgpos
  have hnorm : Real.exp (2 * t.re) = (m : ℝ) / n := by
    have := congrArg norm hexp
    rw [Complex.norm_exp] at this
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero] at this
    rw [this, norm_div]
    simp
  rcases le_abs'.1 hsec with hneg | hpos
  · -- left sector: `n ≥ e^{2δr}`
    have hn : Real.exp (2 * δ * r) ≤ n := by
      have h1 : Real.exp (2 * t.re) ≤ Real.exp (-(2 * δ * r)) := Real.exp_le_exp.2 (by linarith)
      rw [hnorm, Real.exp_neg] at h1
      have hE := Real.exp_pos (2 * δ * r)
      have h2 : (m : ℝ) * Real.exp (2 * δ * r) ≤ n :=
        calc (m : ℝ) * Real.exp (2 * δ * r) = ((m : ℝ) / n) * n * Real.exp (2 * δ * r) := by
              field_simp
          _ ≤ (Real.exp (2 * δ * r))⁻¹ * n * Real.exp (2 * δ * r) := by gcongr
          _ = n := by field_simp
      nlinarith [Real.exp_pos (2 * δ * r)]
    exact hbig n hn (by linarith [hCg j t hr1, hCg_le j])
  · -- right sector: `m ≥ e^{2δr}`
    have hm : Real.exp (2 * δ * r) ≤ m := by
      have h1 : Real.exp (2 * δ * r) ≤ Real.exp (2 * t.re) := Real.exp_le_exp.2 (by linarith)
      rw [hnorm, le_div_iff₀ (by linarith)] at h1
      nlinarith [Real.exp_pos (2 * δ * r)]
    exact hbig m hm (by linarith [hCf j t hr1, hCf_le j])

end ThreeIM
