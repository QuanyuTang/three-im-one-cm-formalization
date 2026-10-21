module

public import RequestProject.ThreeIM.RationalMomentsFull

/-!
# Rational functions as functions, and the zero–pole count on the sphere

`IsRatFun φ` says that `φ : ℂ → ℂ` agrees with a quotient of polynomials `p/q` off a finite
set.  This class is closed under the field operations and under differentiation.  For such a
function which is finite at `∞`, the number of zeros in `ℂ` (counted with order) is at most the
total pole order in `ℂ` (`card_le_of_ratFun`): this is the statement that a rational function
has as many zeros as poles on the Riemann sphere.
-/

@[expose] public section

open Filter Set Topology Polynomial

namespace ThreeIM

/-- `φ` agrees off a finite set with a quotient of polynomials. -/
def IsRatFun (φ : ℂ → ℂ) : Prop :=
  ∃ p q : ℂ[X], q ≠ 0 ∧ φ =ᶠ[cofinite] fun t => p.eval t / q.eval t

namespace IsRatFun

lemma eventually_ne {q : ℂ[X]} (hq : q ≠ 0) : ∀ᶠ t in cofinite, q.eval t ≠ 0 :=
  (q.finite_setOf_isRoot hq).compl_mem_cofinite

lemma congr {φ ψ : ℂ → ℂ} (h : IsRatFun φ) (e : φ =ᶠ[cofinite] ψ) : IsRatFun ψ := by
  obtain ⟨p, q, hq, hφ⟩ := h
  exact ⟨p, q, hq, e.symm.trans hφ⟩

lemma const (c : ℂ) : IsRatFun fun _ => c :=
  ⟨C c, 1, one_ne_zero, Eventually.of_forall fun t => by simp⟩

lemma id : IsRatFun fun t => t :=
  ⟨X, 1, one_ne_zero, Eventually.of_forall fun t => by simp⟩

lemma ratEval (R : RatFunc ℂ) : IsRatFun (ThreeIM.ratEval R) :=
  ⟨R.num, R.denom, R.denom_ne_zero, Eventually.of_forall fun t => ratEval_eq R t⟩

lemma add {φ ψ : ℂ → ℂ} (h₁ : IsRatFun φ) (h₂ : IsRatFun ψ) : IsRatFun fun t => φ t + ψ t := by
  obtain ⟨p, q, hq, e₁⟩ := h₁
  obtain ⟨p', q', hq', e₂⟩ := h₂
  refine ⟨p * q' + p' * q, q * q', mul_ne_zero hq hq', ?_⟩
  filter_upwards [e₁, e₂, eventually_ne hq, eventually_ne hq'] with t h1 h2 h3 h4
  rw [h1, h2]; simp only [eval_add, eval_mul]; field_simp

lemma neg {φ : ℂ → ℂ} (h : IsRatFun φ) : IsRatFun fun t => -φ t := by
  obtain ⟨p, q, hq, e⟩ := h
  refine ⟨-p, q, hq, ?_⟩
  filter_upwards [e] with t h1
  rw [h1]; simp [neg_div]

lemma sub {φ ψ : ℂ → ℂ} (h₁ : IsRatFun φ) (h₂ : IsRatFun ψ) : IsRatFun fun t => φ t - ψ t := by
  simpa [sub_eq_add_neg] using h₁.add h₂.neg

lemma mul {φ ψ : ℂ → ℂ} (h₁ : IsRatFun φ) (h₂ : IsRatFun ψ) : IsRatFun fun t => φ t * ψ t := by
  obtain ⟨p, q, hq, e₁⟩ := h₁
  obtain ⟨p', q', hq', e₂⟩ := h₂
  refine ⟨p * p', q * q', mul_ne_zero hq hq', ?_⟩
  filter_upwards [e₁, e₂] with t h1 h2
  rw [h1, h2]; simp only [eval_mul]; rw [div_mul_div_comm]

lemma inv {φ : ℂ → ℂ} (h : IsRatFun φ) : IsRatFun fun t => (φ t)⁻¹ := by
  obtain ⟨p, q, hq, e⟩ := h
  by_cases hp : p = 0
  · refine ⟨0, 1, one_ne_zero, ?_⟩
    filter_upwards [e] with t h1
    simp [h1, hp]
  · refine ⟨q, p, hp, ?_⟩
    filter_upwards [e] with t h1
    rw [h1, inv_div]

lemma div {φ ψ : ℂ → ℂ} (h₁ : IsRatFun φ) (h₂ : IsRatFun ψ) : IsRatFun fun t => φ t / ψ t := by
  simpa [div_eq_mul_inv] using h₁.mul h₂.inv

lemma pow {φ : ℂ → ℂ} (h : IsRatFun φ) (n : ℕ) : IsRatFun fun t => φ t ^ n := by
  induction n with
  | zero => simpa using const 1
  | succ n ih => simpa [pow_succ] using ih.mul h

/-- The derivative of a rational function is rational. -/
lemma deriv {φ : ℂ → ℂ} (h : IsRatFun φ) : IsRatFun (_root_.deriv φ) := by
  obtain ⟨p, q, hq, e⟩ := h
  refine ⟨p.derivative * q - p * q.derivative, q * q, mul_ne_zero hq hq, ?_⟩
  -- the exceptional set
  obtain ⟨F, hF, hFe⟩ : ∃ F : Set ℂ, F.Finite ∧ ∀ t ∉ F, φ t = p.eval t / q.eval t ∧
      q.eval t ≠ 0 := by
    refine ⟨{t | ¬ (φ t = p.eval t / q.eval t ∧ q.eval t ≠ 0)}, ?_, fun t ht => ?_⟩
    · have := (e.and (eventually_ne hq))
      exact this
    · simpa using ht
  filter_upwards [hF.compl_mem_cofinite] with t ht
  have hopen : IsOpen Fᶜ := hF.isClosed.isOpen_compl
  have hloc : φ =ᶠ[𝓝 t] fun t => p.eval t / q.eval t := by
    filter_upwards [hopen.mem_nhds ht] with s hs
    exact (hFe s hs).1
  have hqt := (hFe t ht).2
  have hd : HasDerivAt (fun t => p.eval t / q.eval t)
      ((p.derivative.eval t * q.eval t - p.eval t * q.derivative.eval t) / q.eval t ^ 2) t :=
    (p.hasDerivAt t).div (q.hasDerivAt t) hqt
  rw [hloc.deriv_eq, hd.deriv]
  simp only [eval_sub, eval_mul]
  ring

lemma meromorphicAt_quot (p q : ℂ[X]) (x : ℂ) :
    MeromorphicAt (fun t => p.eval t / q.eval t) x :=
  (p.differentiable.analyticAt x).meromorphicAt.div (q.differentiable.analyticAt x).meromorphicAt

end IsRatFun

/-! ### Orders of a quotient of polynomials -/

/-- The order of `p/q` at `z` is `μ_p(z) - μ_q(z)`. -/
lemma order_quot (p q : ℂ[X]) (hp : p ≠ 0) (hq : q ≠ 0) (z : ℂ) :
    meromorphicOrderAt (fun t => p.eval t / q.eval t) z =
      (((p.rootMultiplicity z : ℤ) - q.rootMultiplicity z : ℤ) : WithTop ℤ) := by
  obtain ⟨r, hr, hdr⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp z
  obtain ⟨r', hr', hdr'⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd q hq z
  have hrz : r.eval z ≠ 0 := fun h => hdr (dvd_iff_isRoot.2 h)
  have hrz' : r'.eval z ≠ 0 := fun h => hdr' (dvd_iff_isRoot.2 h)
  rw [meromorphicOrderAt_eq_int_iff (IsRatFun.meromorphicAt_quot p q z)]
  refine ⟨fun w => r.eval w / r'.eval w,
    (r.differentiable.analyticAt z).div (r'.differentiable.analyticAt z) hrz',
    by simp [hrz, hrz'], ?_⟩
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hw' : w - z ≠ 0 := sub_ne_zero.2 hw
  conv_lhs => rw [hr, hr']
  simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, smul_eq_mul]
  rw [zpow_sub₀ hw', zpow_natCast, zpow_natCast]
  have : r'.eval w ≠ 0 ∨ r'.eval w = 0 := (em' _)
  rcases this with h | h
  · field_simp
  · simp [h]

/-- The order at `0` of `s ↦ p(1/s)/q(1/s)` is `deg q - deg p`. -/
lemma order_quot_inv (p q : ℂ[X]) (hp : p ≠ 0) (hq : q ≠ 0) :
    meromorphicOrderAt (fun s => p.eval s⁻¹ / q.eval s⁻¹) 0 =
      (((q.natDegree : ℤ) - p.natDegree : ℤ) : WithTop ℤ) := by
  set P := reflect p.natDegree p
  set Q := reflect q.natDegree q
  have hP0 : P.eval 0 ≠ 0 := by
    rw [eval_reflect_zero]; exact leadingCoeff_ne_zero.2 hp
  have hQ0 : Q.eval 0 ≠ 0 := by
    rw [eval_reflect_zero]; exact leadingCoeff_ne_zero.2 hq
  have h2 : ∀ r : ℂ[X], MeromorphicAt (fun s => r.eval s⁻¹) 0 := fun r => by
    have hm' : MeromorphicAt (fun s : ℂ => s ^ (-(r.natDegree : ℤ)) *
        (reflect r.natDegree r).eval s) 0 :=
      (analyticAt_id.meromorphicAt.zpow _).mul
        ((reflect r.natDegree r).differentiable.analyticAt 0).meromorphicAt
    refine hm'.congr ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : s ≠ 0 := hs
    rw [eval_reflect_of_ne_zero le_rfl hs', zpow_neg, zpow_natCast, ← mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero _ hs'), one_mul]
  have hm : MeromorphicAt (fun s => p.eval s⁻¹ / q.eval s⁻¹) 0 := (h2 p).div (h2 q)
  rw [meromorphicOrderAt_eq_int_iff hm]
  refine ⟨fun s => P.eval s / Q.eval s,
    (P.differentiable.analyticAt 0).div (Q.differentiable.analyticAt 0) hQ0,
    by simp [hP0, hQ0], ?_⟩
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : s ≠ 0 := hs
  simp only [sub_zero, smul_eq_mul]
  rw [eval_reflect_of_ne_zero le_rfl hs', eval_reflect_of_ne_zero le_rfl hs', zpow_sub₀ hs',
    zpow_natCast, zpow_natCast]
  have hps : p.eval s⁻¹ ≠ 0 ∨ p.eval s⁻¹ = 0 := em' _
  have hqs : q.eval s⁻¹ ≠ 0 ∨ q.eval s⁻¹ = 0 := em' _
  rcases hqs with hq' | hq'
  · field_simp
  · simp [hq']

/-! ### Zeros and poles -/

/-- **Zeros versus poles of a rational function.**  Let `φ = p/q` off a finite set, with
`p, q ≠ 0`, and assume `φ` is finite at `∞`.  If `φ` has positive order at every point of `A`,
has no poles outside `P`, and has poles of order at most `2` at the points of `P`, then
`#A ≤ 2 #P`. -/
theorem card_le_of_ratFun {φ : ℂ → ℂ} (hφ : IsRatFun φ)
    (hne : ∃ z, meromorphicOrderAt φ z ≠ ⊤)
    (A P : Finset ℂ) (hA : ∀ z ∈ A, 0 < meromorphicOrderAt φ z)
    (hP : ∀ z ∉ P, 0 ≤ meromorphicOrderAt φ z)
    (hP2 : ∀ z ∈ P, ((-2 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt φ z)
    (hinf : 0 ≤ meromorphicOrderAt (fun s => φ s⁻¹) 0) :
    A.card ≤ 2 * P.card := by
  classical
  obtain ⟨p, q, hq, e⟩ := hφ
  have hord : ∀ z, meromorphicOrderAt φ z =
      meromorphicOrderAt (fun t => p.eval t / q.eval t) z :=
    fun z => meromorphicOrderAt_congr (eventually_nhdsNE_of_cofinite e z)
  have hp : p ≠ 0 := by
    rintro rfl
    obtain ⟨z, hz⟩ := hne
    apply hz
    rw [hord z]
    simp only [eval_zero, zero_div]
    rw [meromorphicOrderAt_eq_top_iff]
    exact Eventually.of_forall fun _ => rfl
  have hinf' : 0 ≤ meromorphicOrderAt (fun s => p.eval s⁻¹ / q.eval s⁻¹) 0 := by
    have e' := (tendsto_inv_cocompact.mono_right cocompact_le_cofinite).eventually
      (p := fun t => φ t = p.eval t / q.eval t) e
    rw [← meromorphicOrderAt_congr e']
    exact hinf
  rw [order_quot_inv p q hp hq] at hinf'
  have hdeg : p.natDegree ≤ q.natDegree := by
    have : (0 : ℤ) ≤ q.natDegree - p.natDegree := by exact_mod_cast hinf'
    omega
  set μp : ℂ → ℤ := fun z => p.rootMultiplicity z
  set μq : ℂ → ℤ := fun z => q.rootMultiplicity z
  have hz : ∀ z, meromorphicOrderAt φ z = ((μp z - μq z : ℤ) : WithTop ℤ) := fun z => by
    rw [hord z, order_quot p q hp hq z]
  set Z := p.roots.toFinset ∪ q.roots.toFinset ∪ A ∪ P
  have hsum : ∀ r : ℂ[X], r ≠ 0 → r.roots.toFinset ⊆ Z →
      ∑ z ∈ Z, (r.rootMultiplicity z : ℤ) = r.natDegree := by
    intro r hr hsub
    rw [← Finset.sum_subset hsub (fun x _ hx => by
      rw [Multiset.mem_toFinset, mem_roots hr] at hx
      simp [rootMultiplicity_eq_zero hx])]
    have : ∑ z ∈ r.roots.toFinset, r.rootMultiplicity z = r.natDegree := by
      rw [← IsAlgClosed.card_roots_eq_natDegree, ← Multiset.toFinset_sum_count_eq]
      simp [count_roots]
    exact_mod_cast this
  have hZp := hsum p hp (fun x hx => by simp [Z, hx])
  have hZq := hsum q hq (fun x hx => by simp [Z, hx])
  have hlow : ∀ z ∈ Z, (if z ∈ A then 1 else 0) - (if z ∈ P then 2 else 0) ≤ μp z - μq z := by
    intro z _
    by_cases hA' : z ∈ A
    · have := hA z hA'
      rw [hz z] at this
      have h1 : (0 : ℤ) < μp z - μq z := by exact_mod_cast this
      split_ifs <;> omega
    · by_cases hP' : z ∈ P
      · have := hP2 z hP'
        rw [hz z] at this
        have h1 : (-2 : ℤ) ≤ μp z - μq z := by exact_mod_cast this
        simp [hA', hP']; omega
      · have := hP z hP'
        rw [hz z] at this
        have h1 : (0 : ℤ) ≤ μp z - μq z := by exact_mod_cast this
        simp [hA', hP']; omega
  have h1 := Finset.sum_le_sum hlow
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem,
    Finset.inter_eq_right.2 (by intro x hx; simp [Z, hx]),
    Finset.inter_eq_right.2 (by intro x hx; simp [Z, hx])] at h1
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h1
  have e1 : ∑ z ∈ Z, μp z = p.natDegree := hZp
  have e2 : ∑ z ∈ Z, μq z = q.natDegree := hZq
  rw [e1, e2] at h1
  have : (A.card : ℤ) ≤ 2 * P.card := by
    have := h1; push_cast at this ⊢; omega
  exact_mod_cast this

end ThreeIM
