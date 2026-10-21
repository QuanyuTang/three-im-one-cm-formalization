module

public import RequestProject.ThreeIM.TwoCMMixedMultiplicity

/-!
# A weighted differential identity forces the remaining CM values
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

noncomputable def twoCMWeightedDerivative (a b c : ℂ) (h : ℂ → ℂ) : ℂ → ℂ :=
  fun z => deriv h z * (h z - b) / ((h z - a) * (h z - c))

theorem twoCM_meromorphic_weightedDerivative {h : ℂ → ℂ}
    (hh : Meromorphic h) (a b c : ℂ) : Meromorphic (twoCMWeightedDerivative a b c h) := by
  intro z
  exact ((hh z).deriv.mul ((hh z).sub (MeromorphicAt.const b z))).div
    (((hh z).sub (MeromorphicAt.const a z)).mul ((hh z).sub (MeromorphicAt.const c z)))

theorem twoCM_weightedDerivative_order_at_middle {h : ℂ → ℂ}
    (hh : IsNonconstMeroOn h univ) {a b c z : ℂ} (hba : b ≠ a) (hbc : b ≠ c)
    (hpos : 0 < mult h (b : Sphere) z) :
    meromorphicOrderAt (twoCMWeightedDerivative a b c h) z =
      ((2 * (mult h (b : Sphere) z : ℤ) - 1 : ℤ) : WithTop ℤ) := by
  have hm := hh.meromorphic z
  have ham : MeromorphicAt (fun w => h w - a) z := hm.sub (MeromorphicAt.const a z)
  have hbm : MeromorphicAt (fun w => h w - b) z := hm.sub (MeromorphicAt.const b z)
  have hcm : MeromorphicAt (fun w => h w - c) z := hm.sub (MeromorphicAt.const c z)
  have hbp : 0 < meromorphicOrderAt (fun w => h w - b) z := by
    rw [order_sub_eq_mult hpos]
    exact_mod_cast hpos
  have ha := order_sub_const_eq_zero_of_pos hm hba hbp
  have hc := order_sub_const_eq_zero_of_pos hm hbc hbp
  have hb := order_sub_eq_mult hpos
  have hd := order_deriv_of_order_eq hm (a := b) (by omega : (mult h (b : Sphere) z : ℤ) ≠ 0) hb
  have heq : twoCMWeightedDerivative a b c h =
      (deriv h * (fun w => h w - b)) * ((fun w => h w - a) * (fun w => h w - c))⁻¹ := by
    ext w
    simp [twoCMWeightedDerivative, div_eq_mul_inv]
  rw [heq, meromorphicOrderAt_mul (hm.deriv.mul hbm) (ham.mul hcm).inv,
    meromorphicOrderAt_mul hm.deriv hbm, meromorphicOrderAt_inv,
    meromorphicOrderAt_mul ham hcm, hd, hb, ha, hc, zero_add, neg_zero,
    add_zero, ← WithTop.coe_add]
  congr 1
  ring

theorem twoCM_weightedDerivative_partial_fraction {h : ℂ → ℂ} {a b c z : ℂ}
    (hac : a ≠ c) (ha : h z ≠ a) (hc : h z ≠ c) :
    twoCMWeightedDerivative a b c h z =
      ((a - b) / (a - c)) * (deriv h z / (h z - a)) +
      ((c - b) / (c - a)) * (deriv h z / (h z - c)) := by
  simp only [twoCMWeightedDerivative]
  field_simp [sub_ne_zero.2 hac, sub_ne_zero.2 hac.symm, sub_ne_zero.2 ha, sub_ne_zero.2 hc]
  ring

theorem twoCM_sharesCM_middle_of_weightedDerivative_eq {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair univ f g a) (j i k : Fin 3) (hij : i ≠ j) (hik : i ≠ k)
    (heq : twoCMWeightedDerivative (a j) (a i) (a k) f =ᶠ[codiscrete ℂ]
      twoCMWeightedDerivative (a j) (a i) (a k) g) :
    SharesCMOn univ f g (a i : Sphere) := by
  have hba : a i ≠ a j := hp.injective.ne hij
  have hbc : a i ≠ a k := hp.injective.ne hik
  intro z hz
  by_cases hpos : 0 < mult f (a i : Sphere) z
  · have hposg := (hp.im i z hz).1 hpos
    have ho := meromorphicOrderAt_congr (codiscrete_iff_nhdsNE.1 heq z)
    rw [twoCM_weightedDerivative_order_at_middle hp.nonconst_f hba hbc hpos,
      twoCM_weightedDerivative_order_at_middle hp.nonconst_g hba hbc hposg] at ho
    have hi : 2 * (mult f (a i : Sphere) z : ℤ) - 1 =
        2 * (mult g (a i : Sphere) z : ℤ) - 1 := WithTop.coe_injective ho
    omega
  · have hf0 : mult f (a i : Sphere) z = 0 := by omega
    have hg0 : mult g (a i : Sphere) z = 0 := by
      by_contra hn
      exact hpos ((hp.im i z hz).2 (Nat.pos_of_ne_zero hn))
    rw [hf0, hg0]

theorem twoCM_sharesCM_last_of_weightedDerivative_eq {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair univ f g a) (j i k : Fin 3) (hjk : j ≠ k) (hki : k ≠ i)
    (hcm : SharesCMOn univ f g (a j : Sphere))
    (heq : twoCMWeightedDerivative (a j) (a i) (a k) f =ᶠ[codiscrete ℂ]
      twoCMWeightedDerivative (a j) (a i) (a k) g) :
    SharesCMOn univ f g (a k : Sphere) := by
  let A := a j
  let b := a i
  let c := a k
  let B := (A - b) / (A - c)
  let C := (c - b) / (c - A)
  have hac : A ≠ c := hp.injective.ne hjk
  have hcb : c ≠ b := hp.injective.ne hki
  have hC : C ≠ 0 := div_ne_zero (sub_ne_zero.2 hcb) (sub_ne_zero.2 hac.symm)
  have hlog : twoCMLogDiff c f g =ᶠ[codiscrete ℂ]
      (fun z => (-(B / C)) * twoCMLogDiff A f g z) := by
    filter_upwards [heq, hp.nonconst_f.eventually_ne A, hp.nonconst_f.eventually_ne c,
      hp.nonconst_g.eventually_ne A, hp.nonconst_g.eventually_ne c] with z he hfA hfc hgA hgc
    rw [twoCM_weightedDerivative_partial_fraction hac hfA hfc,
      twoCM_weightedDerivative_partial_fraction hac hgA hgc] at he
    change B * (deriv f z / (f z - A)) + C * (deriv f z / (f z - c)) =
      B * (deriv g z / (g z - A)) + C * (deriv g z / (g z - c)) at he
    change deriv f z / (f z - c) - deriv g z / (g z - c) =
      -(B / C) * (deriv f z / (f z - A) - deriv g z / (g z - A))
    have hcoeff : C * (-(B / C)) = -B := by
      calc
        C * (-(B / C)) = -(B / C * C) := by ring
        _ = -B := by rw [div_mul_cancel₀ _ hC]
    apply (mul_left_cancel₀ hC)
    rw [← mul_assoc, hcoeff]
    linear_combination he
  intro z hz
  have hlognn : 0 ≤ meromorphicOrderAt (twoCMLogDiff c f g) z := by
    rw [meromorphicOrderAt_congr (codiscrete_iff_nhdsNE.1 hlog z)]
    change 0 ≤ meromorphicOrderAt ((fun _ => -(B / C)) * twoCMLogDiff A f g) z
    rw [meromorphicOrderAt_mul (MeromorphicAt.const _ z) (twoCM_meromorphic_logDiff hp A z)]
    exact add_nonneg (order_const_nonneg _) (twoCM_logDiff_order_nonneg hp j hcm z)
  have hfm : Meromorphic (fun w => f w - c) := fun w => (hp.nonconst_f.meromorphic w).sub (MeromorphicAt.const c w)
  have hgm : Meromorphic (fun w => g w - c) := fun w => (hp.nonconst_g.meromorphic w).sub (MeromorphicAt.const c w)
  have hlogfun : twoCMLogDiff c f g =
      (fun w => deriv f w / (f w - c) - deriv g w / (g w - c)) := by
    funext w
    rfl
  rw [hlogfun] at hlognn
  have hres := twoCM_order_relation_of_log_deriv_nonneg hfm hgm
    (fun w => hp.nonconst_f.2 w (mem_univ w) c) (fun w => hp.nonconst_g.2 w (mem_univ w) c)
    1 1 z (by simpa only [one_mul, deriv_sub_const] using hlognn)
  simp only [one_mul] at hres
  have hi : ordZ (fun w => f w - c) z = ordZ (fun w => g w - c) z := by exact_mod_cast hres
  change ((meromorphicOrderAt (fun w => f w - c) z).untop₀.toNat) =
    ((meromorphicOrderAt (fun w => g w - c) z).untop₀.toNat)
  exact congrArg Int.toNat hi

theorem twoCM_false_of_weightedDerivative_eq {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair univ f g a) (j i k : Fin 3)
    (hij : i ≠ j) (hkj : k ≠ j) (hik : i ≠ k)
    (hcm : SharesCMOn univ f g (a j : Sphere))
    (hdefect : ∃ d z, IsDefect f g (a d : Sphere) z)
    (heq : twoCMWeightedDerivative (a j) (a i) (a k) f =ᶠ[codiscrete ℂ]
      twoCMWeightedDerivative (a j) (a i) (a k) g) : False := by
  obtain ⟨d, z, hd⟩ := hdefect
  have hall : ∀ l : Fin 3, SharesCMOn univ f g (a l : Sphere) := by
    intro l
    have hindex : l = j ∨ l = i ∨ l = k := by
      fin_cases j <;> fin_cases i <;> fin_cases k <;> fin_cases l <;> simp_all
    rcases hindex with h | h | h
    · rw [h]
      exact hcm
    · rw [h]
      exact twoCM_sharesCM_middle_of_weightedDerivative_eq hp j i k hij hik heq
    · rw [h]
      exact twoCM_sharesCM_last_of_weightedDerivative_eq hp j i k hkj.symm hik.symm hcm heq
  exact hd.2.2 (hall d z (mem_univ z))

end ThreeIM
