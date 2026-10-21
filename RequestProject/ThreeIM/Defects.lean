module

public import RequestProject.ThreeIM.External
public import RequestProject.ThreeIM.Growth

/-!
# Defect counting and preliminary reductions (Section 4) — elementary parts

* Lemma 4.2: a defect in each finite fiber (from External theorem 2.5);
* Lemma 4.8 (second part): linear growth of `T` forces `L(r) = o(T(r))`;
* Lemma 4.9: the monic polynomial root bound;
* the step of Lemma 4.12 showing that a periodic polynomial is constant.
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

/-- IM sharing without defects is CM sharing. -/
lemma sharesCMOn_of_sharesIMOn_of_no_defect {Ω : Set ℂ} {f g : ℂ → ℂ} {b : Sphere}
    (him : SharesIMOn Ω f g b) (hnd : ∀ z ∈ Ω, ¬ IsDefect f g b z) : SharesCMOn Ω f g b := by
  intro z hz
  by_contra hne
  apply hnd z hz
  have hiff := him z hz
  refine ⟨?_, ?_, hne⟩
  · by_contra h0
    have h1 : mult f b z = 0 := by omega
    have h2 : mult g b z = 0 := by
      by_contra h3; exact h0 (hiff.2 (Nat.pos_of_ne_zero h3))
    exact hne (h1.trans h2.symm)
  · by_contra h0
    have h1 : mult g b z = 0 := by omega
    have h2 : mult f b z = 0 := by
      by_contra h3; exact h0 (hiff.1 (Nat.pos_of_ne_zero h3))
    exact hne (h2.trans h1.symm)

/-- **Lemma 4.2** (a defect in each finite fiber).  If a normalized pair on `ℂ` does not share
all four values CM, each of its three finite shared values has a defect. -/
theorem NormalizedPair.exists_defect {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (h : NormalizedPair univ f g a) (hnot : ¬ ∀ j, SharesCMOn univ f g (a j : Sphere)) :
    ∀ j, ∃ z, IsDefect f g (a j : Sphere) z := by
  intro j
  by_contra hj
  push_neg at hj
  have hcmj : SharesCMOn univ f g (a j : Sphere) :=
    sharesCMOn_of_sharesIMOn_of_no_defect (h.im j) fun z _ => hj z
  let a4 : Fin 4 → Sphere := ![(a 0 : Sphere), (a 1 : Sphere), (a 2 : Sphere), ⊤]
  have ha4 : Function.Injective a4 := by
    intro x y hxy
    have hinj := h.injective
    fin_cases x <;> fin_cases y <;> simp_all [a4, hinj.eq_iff]
  have him : ∀ i, SharesIMOn univ f g (a4 i) := by
    intro i
    fin_cases i
    · exact h.im 0
    · exact h.im 1
    · exact h.im 2
    · exact h.cm_top.sharesIMOn
  have hcm := ext_two_cm h.nonconst_f h.nonconst_g a4 ha4 him
    (i₁ := j.castSucc) (i₂ := 3) (by simp [Fin.ext_iff]; omega)
    (by fin_cases j <;> simpa [a4] using hcmj) (by simpa [a4] using h.cm_top)
  apply hnot
  intro i
  fin_cases i
  · simpa [a4] using hcm 0
  · simpa [a4] using hcm 1
  · simpa [a4] using hcm 2

/-- **Lemma 4.9** (monic polynomial root bound).  If `w^d + c_{d-1} w^{d-1} + ⋯ + c_0 = 0`
with `d ≥ 1` and `|c_j| ≤ M`, then `|w| ≤ 1 + M`. -/
theorem norm_le_of_monic_root {d : ℕ} (hd : 1 ≤ d) {c : ℕ → ℂ} {M : ℝ}
    (hM : ∀ j < d, ‖c j‖ ≤ M) {w : ℂ}
    (hw : w ^ d + ∑ j ∈ Finset.range d, c j * w ^ j = 0) : ‖w‖ ≤ 1 + M := by
  by_contra hlt
  push_neg at hlt
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 hd)
  set x := ‖w‖ with hx
  have hx1 : 1 < x := by linarith
  have hgeom : (∑ j ∈ Finset.range d, x ^ j) * (x - 1) = x ^ d - 1 := geom_sum_mul x d
  have hpos : 0 < ∑ j ∈ Finset.range d, x ^ j :=
    Finset.sum_pos (fun j _ => pow_pos (by linarith) j) (by simp; omega)
  have hsum : ‖∑ j ∈ Finset.range d, c j * w ^ j‖ ≤ M * ∑ j ∈ Finset.range d, x ^ j := by
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right (hM j (Finset.mem_range.1 hj)) (pow_nonneg (by linarith) j)
  have hlt2 : M * ∑ j ∈ Finset.range d, x ^ j < x ^ d := by
    have : M * ∑ j ∈ Finset.range d, x ^ j < (x - 1) * ∑ j ∈ Finset.range d, x ^ j :=
      mul_lt_mul_of_pos_right (by linarith) hpos
    linarith
  have heq : w ^ d = -∑ j ∈ Finset.range d, c j * w ^ j := eq_neg_of_add_eq_zero_left hw
  have : x ^ d = ‖∑ j ∈ Finset.range d, c j * w ^ j‖ := by
    rw [hx, ← norm_pow, heq, norm_neg]
  linarith

/-- Step of **Lemma 4.12**: a complex polynomial with a nonzero period is constant. -/
theorem polynomial_eq_C_of_periodic {p : Polynomial ℂ} {ω : ℂ} (hω : ω ≠ 0)
    (hp : ∀ z, p.eval (z + ω) = p.eval z) : p = Polynomial.C (p.eval 0) := by
  have hroot : ∀ n : ℕ, (p - Polynomial.C (p.eval 0)).IsRoot (n * ω) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_C] at ih ⊢
      push_cast
      rw [add_mul, one_mul, hp]; exact ih
  have hinf : {x | (p - Polynomial.C (p.eval 0)).IsRoot x}.Infinite := by
    apply Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (n : ℂ) * ω)
    · intro m n hmn
      simpa [hω] using hmn
    · exact hroot
  exact sub_eq_zero.1 (Polynomial.eq_zero_of_infinite_isRoot _ hinf)


end ThreeIM
