module

public import RequestProject.ThreeIM.Holomorphic

/-!
# Affine relations force CM sharing

The conclusion is formulated through punctured germs, so arbitrary values at
poles and removable points do not affect this elementary two-CM branch.
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

private lemma twoCM_order_const_mul {f : ℂ → ℂ} {z A : ℂ}
    (hf : MeromorphicAt f z) (hA : A ≠ 0) :
    meromorphicOrderAt (fun w => A * f w) z = meromorphicOrderAt f z := by
  have heq : (fun w => A * f w) = (fun _ => A) * f := rfl
  rw [heq, meromorphicOrderAt_mul (MeromorphicAt.const _ _) hf, order_const_eq _ hA,
    zero_add]

/-- At a shared finite value an invertible affine germ relation forces equal
multiplicities. The value may also be omitted by both functions. -/
theorem twoCM_mult_finite_of_affine_germ {f g : ℂ → ℂ} {z A B b : ℂ}
    (hf : MeromorphicAt f z) (hA : A ≠ 0)
    (hfg : g =ᶠ[𝓝[≠] z] fun w => A * f w + B)
    (him : 0 < mult f (b : Sphere) z ↔ 0 < mult g (b : Sphere) z) :
    mult f (b : Sphere) z = mult g (b : Sphere) z := by
  have hfm : MeromorphicAt (fun w => f w - b) z := hf.sub (MeromorphicAt.const _ _)
  by_cases hfixed : A * b + B = b
  · have heq : (fun w => g w - b) =ᶠ[𝓝[≠] z] (fun w => A * (f w - b)) := by
      filter_upwards [hfg] with w hw
      rw [hw]
      linear_combination hfixed
    simp only [mult_coe]
    rw [meromorphicOrderAt_congr heq, twoCM_order_const_mul hfm hA]
  · have hzero : mult f (b : Sphere) z = 0 := by
      by_contra hne
      have hpos := Nat.pos_of_ne_zero hne
      have horder : 0 < meromorphicOrderAt (fun w => f w - b) z := by
        rw [order_sub_eq_mult hpos]
        exact_mod_cast hpos
      have hconst : A * b + B - b ≠ 0 := sub_ne_zero.2 hfixed
      have hscaled : 0 < meromorphicOrderAt (fun w => A * (f w - b)) z := by
        rwa [twoCM_order_const_mul hfm hA]
      have heq : (fun w => g w - b) =ᶠ[𝓝[≠] z]
          ((fun _ => A * b + B - b) + fun w => A * (f w - b)) := by
        filter_upwards [hfg] with w hw
        simp only [Pi.add_apply]
        rw [hw]
        ring
      have hgo : meromorphicOrderAt (fun w => g w - b) z = 0 := by
        have hm : MeromorphicAt (fun w => A * (f w - b)) z := by fun_prop
        have hl : meromorphicOrderAt (fun _ : ℂ => A * b + B - b) z <
            meromorphicOrderAt (fun w => A * (f w - b)) z := by
          rwa [order_const_eq _ hconst]
        rw [meromorphicOrderAt_congr heq,
          meromorphicOrderAt_add_eq_left_of_lt (f₁ := fun _ => A * b + B - b)
            (f₂ := fun w => A * (f w - b)) hm hl, order_const_eq _ hconst]
      have hgzero : mult g (b : Sphere) z = 0 := by simp [mult_coe, hgo]
      have := him.1 hpos
      omega
    have hgzero : mult g (b : Sphere) z = 0 := by
      by_contra hg
      have := him.2 (Nat.pos_of_ne_zero hg)
      omega
    exact hzero.trans hgzero.symm

/-- An invertible affine germ relation always preserves pole multiplicities. -/
theorem twoCM_mult_top_of_affine_germ {f g : ℂ → ℂ} {z A B : ℂ}
    (hf : MeromorphicAt f z) (hA : A ≠ 0)
    (hfg : g =ᶠ[𝓝[≠] z] fun w => A * f w + B) : mult f ⊤ z = mult g ⊤ z := by
  have hAf : MeromorphicAt (fun w => A * f w) z := (MeromorphicAt.const _ _).mul hf
  have ho := twoCM_order_const_mul hf hA
  have heq : (fun w => A * f w + B) = (fun w => A * f w) + fun _ => B := rfl
  simp only [mult_top]
  rw [meromorphicOrderAt_congr hfg, heq]
  rcases lt_or_ge (meromorphicOrderAt f z) 0 with hneg | hnn
  · have hlt : meromorphicOrderAt (fun w => A * f w) z <
        meromorphicOrderAt (fun _ : ℂ => B) z :=
      ho ▸ lt_of_lt_of_le hneg (order_const_nonneg _)
    rw [meromorphicOrderAt_add_eq_left_of_lt (MeromorphicAt.const _ _) hlt, ho]
  · have hsum : 0 ≤ meromorphicOrderAt ((fun w => A * f w) + fun _ => B) z :=
      (le_min (ho ▸ hnn) (order_const_nonneg B)).trans
        (meromorphicOrderAt_add hAf (MeromorphicAt.const _ _))
    rw [untop₀_toNat_neg_eq_zero_of_nonneg hnn,
      untop₀_toNat_neg_eq_zero_of_nonneg hsum]

/-- Every IM-shared sphere value is CM-shared for an invertible affine germ
relation. In particular no two-CM theorem is needed for this branch. -/
theorem twoCM_sharesCM_of_affine_germs {f g : ℂ → ℂ} {A B : ℂ}
    (hf : MeromorphicOn f univ) (hA : A ≠ 0)
    (hfg : ∀ z, g =ᶠ[𝓝[≠] z] fun w => A * f w + B) {b : Sphere}
    (him : SharesIMOn univ f g b) : SharesCMOn univ f g b := by
  intro z hz
  induction b using WithTop.recTopCoe with
  | top => exact twoCM_mult_top_of_affine_germ (hf z hz) hA (hfg z)
  | coe c => exact twoCM_mult_finite_of_affine_germ (hf z hz) hA (hfg z) (him z hz)

end ThreeIM
