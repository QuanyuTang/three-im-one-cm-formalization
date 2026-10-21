module

public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp
public import RequestProject.ThreeIM.ExponentialData
public import RequestProject.ThreeIM.SphereZeroPersistence
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-! # The discrete multiplicity data in an exponential pair

After the actual finite fiber support is fixed along a connected phase
family, its multiplicities do not need a second analytic stability argument.
The common coefficient value fixes the ratio, and the already-proved
minimum-one property uniquely fixes the ordered pair of multiplicities.
-/

@[expose] public section

namespace ThreeIM

set_option autoImplicit false

theorem nat_pair_eq_of_min_one_of_cross_mul_eq {m n p q : ℕ}
    (hmn : min m n = 1) (hpq : min p q = 1) (hcross : m * q = p * n) :
    m = p ∧ n = q := by
  have hmn' : m = 1 ∨ n = 1 := by
    rcases le_total m n with h | h
    · left
      simpa only [Nat.min_eq_left h] using hmn
    · right
      simpa only [Nat.min_eq_right h] using hmn
  have hpq' : p = 1 ∨ q = 1 := by
    rcases le_total p q with h | h
    · left
      simpa only [Nat.min_eq_left h] using hpq
    · right
      simpa only [Nat.min_eq_right h] using hpq
  rcases hmn' with rfl | rfl <;> rcases hpq' with rfl | rfl
  · simp only [one_mul] at hcross
    exact ⟨rfl, hcross.symm⟩
  · have hpn : p * n = 1 := by simpa only [one_mul] using hcross.symm
    have hp := Nat.eq_one_of_mul_eq_one_right hpn
    have hn := Nat.eq_one_of_mul_eq_one_left hpn
    subst p
    subst n
    exact ⟨rfl, rfl⟩
  · have hmq : m * q = 1 := by simpa only [mul_one] using hcross
    have hm := Nat.eq_one_of_mul_eq_one_right hmq
    have hq := Nat.eq_one_of_mul_eq_one_left hmq
    subst m
    subst q
    exact ⟨rfl, rfl⟩
  · simp only [mul_one] at hcross
    exact ⟨hcross, rfl⟩

theorem nat_pair_eq_of_min_one_of_complex_ratio_eq {m n p q : ℕ}
    (hmn : min m n = 1) (hpq : min p q = 1)
    (hratio : (m : ℂ) / (n : ℂ) = (p : ℂ) / (q : ℂ)) :
    m = p ∧ n = q := by
  have hn : n ≠ 0 := by
    intro h
    subst n
    simp at hmn
  have hq : q ≠ 0 := by
    intro h
    subst q
    simp at hpq
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have hcrossC : (m : ℂ) * (q : ℂ) = (p : ℂ) * (n : ℂ) :=
    (div_eq_div_iff hnC hqC).mp hratio
  have hcross : m * q = p * n := by exact_mod_cast hcrossC
  exact nat_pair_eq_of_min_one_of_cross_mul_eq hmn hpq hcross

end ThreeIM

end

/-!
# The fixed locally finite source locus for exponential-pair fibers

The two integer branches are handled by boundedness of exp(2z) and
exp(-2z) on compact sets. Each remaining fixed fiber is finite there,
using its actual divisor and its nonzero derivative.
-/

@[expose] public section

set_option autoImplicit false

open Set Filter Metric Topology

namespace ThreeIM

def exponentialFiberLattice : Set ℂ :=
  {z | ∃ m : ℕ, 1 ≤ m ∧
    (Complex.exp (2 * z) = (m : ℂ) ∨ Complex.exp (2 * z) = (m : ℂ)⁻¹)}

/-- A globally analytic function with nonvanishing derivative has only
finitely many points of any fixed fiber in a compact source set. -/
theorem finite_fiber_inter_compact_of_deriv_ne_zero {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) (hdf : ∀ z, deriv f z ≠ 0)
    {K : Set ℂ} (hK : IsCompact K) (c : ℂ) :
    Set.Finite {z | z ∈ K ∧ f z = c} := by
  let D := MeromorphicOn.divisor (fun z => f z - c) K
  have hD : Set.Finite D.support := D.finiteSupport hK
  apply hD.subset
  rintro z ⟨hzK, hzc⟩
  have ha : AnalyticAt ℂ (fun w => f w - c) z :=
    (hf z (mem_univ z)).sub analyticAt_const
  have horder : analyticOrderAt (fun w => f w - c) z = 1 := by
    simpa only [hzc] using
      (hf z (mem_univ z)).analyticOrderAt_sub_eq_one_of_deriv_ne_zero (hdf z)
  have hm : MeromorphicOn (fun w => f w - c) K :=
    fun w _ => ((hf w (mem_univ w)).sub analyticAt_const).meromorphicAt
  change D z ≠ 0
  dsimp only [D]
  rw [MeromorphicOn.divisor_apply hm hzK, ha.meromorphicOrderAt_eq, horder]
  simp

theorem finite_exp_two_fiber_inter_compact {K : Set ℂ} (hK : IsCompact K) (c : ℂ) :
    Set.Finite {z | z ∈ K ∧ Complex.exp (2 * z) = c} := by
  apply finite_fiber_inter_compact_of_deriv_ne_zero (f := fun z => Complex.exp (2 * z))
    (by intro z _; fun_prop) (fun z => ?_) hK c
  have hd : HasDerivAt (fun w : ℂ => Complex.exp (2 * w))
      (Complex.exp (2 * z) * 2) z := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id z).const_mul (2 : ℂ)).cexp
  rw [hd.deriv]
  exact mul_ne_zero (Complex.exp_ne_zero _) (by norm_num)

theorem finite_exp_neg_two_fiber_inter_compact {K : Set ℂ} (hK : IsCompact K) (c : ℂ) :
    Set.Finite {z | z ∈ K ∧ Complex.exp (-2 * z) = c} := by
  apply finite_fiber_inter_compact_of_deriv_ne_zero (f := fun z => Complex.exp (-2 * z))
    (by intro z _; fun_prop) (fun z => ?_) hK c
  have hd : HasDerivAt (fun w : ℂ => Complex.exp (-2 * w))
      (Complex.exp (-2 * z) * (-2)) z := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id z).const_mul (-2 : ℂ)).cexp
  rw [hd.deriv]
  exact mul_ne_zero (Complex.exp_ne_zero _) (by norm_num)

/-- Compact source sets meet the integer/reciprocal-integer locus in a
finite set. No explicit logarithm branches or imaginary indices are used. -/
theorem exponentialFiberLattice_finite_inter_compact {K : Set ℂ} (hK : IsCompact K) :
    Set.Finite (K ∩ exponentialFiberLattice) := by
  classical
  have hp : Continuous (fun z : ℂ => Complex.exp (2 * z)) := by fun_prop
  have hn : Continuous (fun z : ℂ => Complex.exp (-2 * z)) := by fun_prop
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp (hK.image hp).isBounded
  obtain ⟨N, hN⟩ := isBounded_iff_forall_norm_le.mp (hK.image hn).isBounded
  obtain ⟨B, hB⟩ := exists_nat_gt (max M N)
  let S : Set ℂ := ⋃ m : Fin B,
    ({z | z ∈ K ∧ Complex.exp (2 * z) = (m.val : ℂ)} ∪
      {z | z ∈ K ∧ Complex.exp (-2 * z) = (m.val : ℂ)})
  have hS : Set.Finite S := Set.finite_iUnion fun m : Fin B =>
    (finite_exp_two_fiber_inter_compact hK (m.val : ℂ)).union
      (finite_exp_neg_two_fiber_inter_compact hK (m.val : ℂ))
  apply hS.subset
  rintro z ⟨hzK, m, hm, hzm | hzm⟩
  · have hmM : (m : ℝ) ≤ M := by
      have hh := hM (Complex.exp (2 * z)) ⟨z, hzK, rfl⟩
      simpa only [hzm, Complex.norm_natCast] using hh
    have hmB : m < B := by
      exact_mod_cast (hmM.trans (le_max_left M N)).trans_lt hB
    exact Set.mem_iUnion.mpr ⟨⟨m, hmB⟩, Or.inl ⟨hzK, hzm⟩⟩
  · have hzneg : Complex.exp (-2 * z) = (m : ℂ) := by
      rw [show (-2 : ℂ) * z = -(2 * z) by ring, Complex.exp_neg, hzm, inv_inv]
    have hmN : (m : ℝ) ≤ N := by
      have hh := hN (Complex.exp (-2 * z)) ⟨z, hzK, rfl⟩
      simpa only [hzneg, Complex.norm_natCast] using hh
    have hmB : m < B := by
      exact_mod_cast (hmN.trans (le_max_right M N)).trans_lt hB
    exact Set.mem_iUnion.mpr ⟨⟨m, hmB⟩, Or.inr ⟨hzK, hzneg⟩⟩

/-- Every source point has a disk containing no other point of the fixed
locus. This is the local input for phase-support persistence by Hurwitz. -/
theorem exponentialFiberLattice_isolated (z : ℂ) :
    ∃ δ > 0, ∀ w ∈ ball z δ, w ∈ exponentialFiberLattice → w = z := by
  let S : Set ℂ := (closedBall z 1 ∩ exponentialFiberLattice) \ {z}
  have hS : Set.Finite S :=
    (exponentialFiberLattice_finite_inter_compact (isCompact_closedBall z 1)).diff
  have hzS : z ∉ S := by simp [S]
  have hU : Sᶜ ∩ ball z 1 ∈ 𝓝 z := inter_mem
    (hS.isClosed.isOpen_compl.mem_nhds hzS) (isOpen_ball.mem_nhds (mem_ball_self (by norm_num)))
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨δ, hδ, fun w hw hwΛ => ?_⟩
  by_contra hwz
  have hwU := hδU hw
  exact hwU.1 ⟨⟨ball_subset_closedBall hwU.2, hwΛ⟩, by simpa using hwz⟩

end ThreeIM

end

/-!
# Exact three-CM rigidity of a continuous exponential phase family

Hurwitz fixes each fiber's support inside the fixed locally finite source
locus. The coefficient value and the minimum-one identity then fix both
multiplicities by arithmetic. This avoids a separate multiplicity-limit
theorem and never evaluates raw functions at removable singularities.
-/

@[expose] public section

set_option autoImplicit false

open Set Filter Metric Topology NoWanderingDomains

namespace ThreeIM

theorem ExponentialPair.finite_fiber_mem_lattice
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ} (h : ExponentialPair a f g κ)
    {z : ℂ} {j : Fin 3} (hj : 0 < mult f (a j : Sphere) z) :
    z ∈ exponentialFiberLattice := by
  obtain ⟨hmin, hratio⟩ := h.shared_point hj
  have hcases : mult f (a j : Sphere) z = 1 ∨ mult g (a j : Sphere) z = 1 := by omega
  rcases hcases with hm | hn
  · refine ⟨mult g (a j : Sphere) z, by omega, Or.inr ?_⟩
    simpa only [hm, Nat.cast_one, one_div] using hratio
  · refine ⟨mult f (a j : Sphere) z, by omega, Or.inl ?_⟩
    simpa only [hn, Nat.cast_one, div_one] using hratio

theorem ExponentialPair.spherical_finite_fiber_mem_lattice
    {a : Fin 3 → ℂ} {f g : ℂ → ℂ} {κ : ℂ} (h : ExponentialPair a f g κ)
    {z : ℂ} {j : Fin 3} (hj : sphereGermValue f z = ((a j : ℂ) : OnePoint ℂ)) :
    z ∈ exponentialFiberLattice := by
  apply h.finite_fiber_mem_lattice
  exact (mult_finite_pos_iff_sphereGermValue_eq
    (h.pair.nonconst_f.1 z (mem_univ z)) (h.pair.nonconst_f.2 z (mem_univ z) (a j))).2 hj

/-- Unique subsequential limits suffice; there is no need to put a
locally-uniform-convergence topology on the entire function space. -/
theorem continuous_spherical_evaluation_of_unique_subseq_limits
    {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    {F : P → ℂ → OnePoint ℂ}
    (hsub : ∀ p (s : ℕ → P), Tendsto s atTop (𝓝 p) →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        TendstoLocallyUniformlyOn (fun n => F (s (ψ n))) (F p) atTop univ)
    (z : ℂ) : Continuous (fun p => F p z) := by
  apply SeqContinuous.continuous
  intro s p hs
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ψ, -, hc⟩ := hsub p (fun n => s (ns n)) (hs.comp hns)
  exact ⟨ψ, hc.tendsto_at (mem_univ z)⟩

theorem isClopen_spherical_fiber_support_of_lattice_of_subseq
    {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    {F : P → ℂ → OnePoint ℂ} {b : OnePoint ℂ}
    (hF : ∀ p, SphereHolomorphicOn (F p) univ)
    (hnc : ∀ p, ¬ ∃ c : OnePoint ℂ, ∀ z, F p z = c)
    (hsub : ∀ p (s : ℕ → P), Tendsto s atTop (𝓝 p) →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        TendstoLocallyUniformlyOn (fun n => F (s (ψ n))) (F p) atTop univ)
    (hlattice : ∀ p z, F p z = b → z ∈ exponentialFiberLattice) (z : ℂ) :
    IsClopen {p | F p z = b} := by
  have hcont := continuous_spherical_evaluation_of_unique_subseq_limits hsub z
  refine ⟨isClosed_eq hcont continuous_const, isOpen_iff_mem_nhds.mpr ?_⟩
  intro p hp
  by_contra hnot
  change ¬ ∀ᶠ q in 𝓝 p, F q z = b at hnot
  obtain ⟨s, hs, hsnot⟩ := exists_seq_forall_of_frequently (not_eventually.mp hnot)
  obtain ⟨ψ, -, hc⟩ := hsub p s hs
  obtain ⟨δ, hδ, hisolate⟩ := exponentialFiberLattice_isolated z
  have hpre := sphere_eventually_exists_preimage (hF p) (hnc p)
    (fun w => ⟨univ, isOpen_univ, mem_univ w,
      Eventually.of_forall fun n => hF (s (ψ n))⟩)
    hc hp isOpen_ball (mem_ball_self hδ)
  obtain ⟨n, w, hw, hwb⟩ := hpre.exists
  have hwz := hisolate w hw (hlattice (s (ψ n)) w hwb)
  exact hsnot (ψ n) (hwz ▸ hwb)

theorem spherical_fiber_support_eq_of_connected_lattice_of_subseq
    {P : Type*} [TopologicalSpace P] [FirstCountableTopology P] [PreconnectedSpace P]
    {F : P → ℂ → OnePoint ℂ} {b : OnePoint ℂ}
    (hF : ∀ p, SphereHolomorphicOn (F p) univ)
    (hnc : ∀ p, ¬ ∃ c : OnePoint ℂ, ∀ z, F p z = c)
    (hsub : ∀ p (s : ℕ → P), Tendsto s atTop (𝓝 p) →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        TendstoLocallyUniformlyOn (fun n => F (s (ψ n))) (F p) atTop univ)
    (hlattice : ∀ p z, F p z = b → z ∈ exponentialFiberLattice)
    (p q : P) (z : ℂ) : (F p z = b ↔ F q z = b) := by
  have hc := isClopen_spherical_fiber_support_of_lattice_of_subseq hF hnc hsub hlattice z
  constructor
  · intro hp
    have hall := hc.eq_univ ⟨p, hp⟩
    change q ∈ {p | F p z = b}
    rw [hall]
    exact mem_univ q
  · intro hq
    have hall := hc.eq_univ ⟨q, hq⟩
    change p ∈ {p | F p z = b}
    rw [hall]
    exact mem_univ p

/-- Once support has been fixed, the two exact multiplicities are forced
by the same exp(2z) value and the already-proved minimum-one property. -/
theorem ExponentialPair.mult_eq_of_shared_support
    {a : Fin 3 → ℂ} {f g F G : ℂ → ℂ} {κ κ' : ℂ}
    (h : ExponentialPair a f g κ) (h' : ExponentialPair a F G κ')
    {j : Fin 3} {z : ℂ}
    (hsupport : 0 < mult f (a j : Sphere) z ↔ 0 < mult F (a j : Sphere) z) :
    mult f (a j : Sphere) z = mult F (a j : Sphere) z ∧
      mult g (a j : Sphere) z = mult G (a j : Sphere) z := by
  by_cases hf : 0 < mult f (a j : Sphere) z
  · have hF := hsupport.mp hf
    have hp := h.shared_point hf
    have hp' := h'.shared_point hF
    exact nat_pair_eq_of_min_one_of_complex_ratio_eq hp.1 hp'.1 (hp.2.symm.trans hp'.2)
  · have hF : ¬ 0 < mult F (a j : Sphere) z := fun hF => hf (hsupport.mpr hF)
    have hg : ¬ 0 < mult g (a j : Sphere) z :=
      fun hg => hf ((h.pair.im j z (mem_univ z)).mpr hg)
    have hG : ¬ 0 < mult G (a j : Sphere) z :=
      fun hG => hF ((h'.pair.im j z (mem_univ z)).mpr hG)
    exact ⟨by omega, by omega⟩

theorem exponential_phase_three_cm_of_subseq
    {P : Type*} [TopologicalSpace P] [FirstCountableTopology P] [PreconnectedSpace P]
    {a : Fin 3 → ℂ} {f g : P → ℂ → ℂ} {κ : P → ℂ}
    (hpair : ∀ p, ExponentialPair a (f p) (g p) (κ p))
    (hsub : ∀ p (s : ℕ → P), Tendsto s atTop (𝓝 p) →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        TendstoLocallyUniformlyOn (fun n => sphereGermValue (f (s (ψ n))))
          (sphereGermValue (f p)) atTop univ)
    (p q : P) (j : Fin 3) (z : ℂ) :
    mult (f p) (a j : Sphere) z = mult (f q) (a j : Sphere) z ∧
      mult (g p) (a j : Sphere) z = mult (g q) (a j : Sphere) z := by
  have hs := spherical_fiber_support_eq_of_connected_lattice_of_subseq
    (b := ((a j : ℂ) : OnePoint ℂ))
    (fun p => sphereHolomorphicOn_sphereGermValue isOpen_univ (hpair p).pair.nonconst_f.1)
    (fun p => sphereGermValue_nonconstant (hpair p).pair.nonconst_f) hsub
    (fun p z hz => (hpair p).spherical_finite_fiber_mem_lattice hz) p q z
  apply (hpair p).mult_eq_of_shared_support (hpair q)
  rw [mult_finite_pos_iff_sphereGermValue_eq
      ((hpair p).pair.nonconst_f.1 z (mem_univ z))
      ((hpair p).pair.nonconst_f.2 z (mem_univ z) (a j)),
    mult_finite_pos_iff_sphereGermValue_eq
      ((hpair q).pair.nonconst_f.1 z (mem_univ z))
      ((hpair q).pair.nonconst_f.2 z (mem_univ z) (a j))]
  exact hs

end ThreeIM

end
