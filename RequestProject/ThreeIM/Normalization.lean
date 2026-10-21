module

public import RequestProject.ThreeIM.Basic

/-!
# Common target normalization (Lemma 3.4)

A common Möbius transformation preserves IM and CM sharing and all local degrees.  We only
need the transformations `w ↦ 1/(w - c)`, which send `c` to `∞`.
-/

@[expose] public section

open Filter Set

namespace ThreeIM

/-- The Möbius map `w ↦ 1 / (w - c)` on the Riemann sphere. -/
noncomputable def mobius (c : ℂ) (b : Sphere) : Sphere :=
  WithTop.recTopCoe (0 : ℂ) (fun d : ℂ => if d = c then ⊤ else (((d - c)⁻¹ : ℂ) : Sphere)) b

@[simp] lemma mobius_top (c : ℂ) : mobius c ⊤ = ((0 : ℂ) : Sphere) := rfl

@[simp] lemma mobius_self (c : ℂ) : mobius c (c : Sphere) = ⊤ := by
  simp [mobius]

lemma mobius_coe_of_ne {c d : ℂ} (h : d ≠ c) :
    mobius c (d : Sphere) = (((d - c)⁻¹ : ℂ) : Sphere) := by
  simp [mobius, h]

lemma mobius_injective (c : ℂ) : Function.Injective (mobius c) := by
  intro x y hxy
  induction x using WithTop.recTopCoe <;> induction y using WithTop.recTopCoe
  · rfl
  · rename_i d
    by_cases hd : d = c
    · subst hd; simp at hxy
    · rw [mobius_top, mobius_coe_of_ne hd] at hxy
      have := WithTop.coe_injective hxy
      exact (hd (sub_eq_zero.1 (inv_eq_zero.1 this.symm))).elim
  · rename_i d
    by_cases hd : d = c
    · subst hd; simp at hxy
    · rw [mobius_top, mobius_coe_of_ne hd] at hxy
      have := WithTop.coe_injective hxy
      exact (hd (sub_eq_zero.1 (inv_eq_zero.1 this))).elim
  · rename_i d e
    by_cases hd : d = c <;> by_cases he : e = c
    · rw [hd, he]
    · subst hd; rw [mobius_self, mobius_coe_of_ne he] at hxy; simp at hxy
    · subst he; rw [mobius_self, mobius_coe_of_ne hd] at hxy; simp at hxy
    · rw [mobius_coe_of_ne hd, mobius_coe_of_ne he] at hxy
      have := WithTop.coe_injective hxy
      rw [inv_inj, sub_left_inj] at this
      rw [this]

section OrderLemmas

variable {f : ℂ → ℂ} {z : ℂ}

lemma order_const_eq (c : ℂ) (hc : c ≠ 0) :
    meromorphicOrderAt (fun _ : ℂ => c) z = 0 := by
  classical
  rw [meromorphicOrderAt_const]; simp [hc]

lemma order_const_nonneg (c : ℂ) :
    0 ≤ meromorphicOrderAt (fun _ : ℂ => c) z := by
  classical
  rw [meromorphicOrderAt_const]; split_ifs <;> simp

/-- Subtracting a constant does not change a negative order. -/
lemma order_sub_const_of_neg (hneg : meromorphicOrderAt f z < 0)
    (c : ℂ) : meromorphicOrderAt (fun w => f w - c) z = meromorphicOrderAt f z := by
  have h := meromorphicOrderAt_add_eq_left_of_lt (f₁ := f) (f₂ := fun _ => -c) (x := z)
    (MeromorphicAt.const _ _) (lt_of_lt_of_le hneg (order_const_nonneg _))
  have h2 : (fun w => f w - c) = f + fun _ => -c := by ext; simp [sub_eq_add_neg]
  rw [h2]
  exact h

/-- Subtracting a constant keeps a nonnegative order nonnegative. -/
lemma order_sub_const_nonneg (hf : MeromorphicAt f z) (hnn : 0 ≤ meromorphicOrderAt f z)
    (c : ℂ) : 0 ≤ meromorphicOrderAt (fun w => f w - c) z := by
  have h := meromorphicOrderAt_add (f₁ := f) (f₂ := fun _ => -c) (x := z) hf
    (MeromorphicAt.const _ _)
  have h2 : (fun w => f w - c) = f + fun _ => -c := by ext; simp [sub_eq_add_neg]
  rw [h2]
  exact le_trans (le_min hnn (order_const_nonneg _)) h

/-- At a `b`-point, `f - c` has order zero for every `c ≠ b`. -/
lemma order_sub_const_eq_zero_of_pos (hf : MeromorphicAt f z) {b c : ℂ} (hbc : b ≠ c)
    (hpos : 0 < meromorphicOrderAt (fun w => f w - b) z) :
    meromorphicOrderAt (fun w => f w - c) z = 0 := by
  have hm : MeromorphicAt (fun w => f w - b) z := hf.sub (MeromorphicAt.const _ _)
  have h := meromorphicOrderAt_add_eq_left_of_lt (f₁ := fun _ => b - c)
    (f₂ := fun w => f w - b) (x := z) hm (by rwa [order_const_eq _ (sub_ne_zero.2 hbc)])
  have h2 : (fun w => f w - c) = (fun _ => b - c) + fun w => f w - b := by ext; simp
  rw [h2, h, order_const_eq _ (sub_ne_zero.2 hbc)]

lemma meromorphicAt_mobius_comp (hf : MeromorphicAt f z) (c : ℂ) :
    MeromorphicAt (fun w => (f w - c)⁻¹) z :=
  (hf.sub (MeromorphicAt.const _ _)).inv

lemma order_mobius_comp (c : ℂ) :
    meromorphicOrderAt (fun w => (f w - c)⁻¹) z =
      -meromorphicOrderAt (fun w => f w - c) z := by
  have : (fun w => (f w - c)⁻¹) = (fun w => f w - c)⁻¹ := rfl
  rw [this, meromorphicOrderAt_inv]

end OrderLemmas

lemma untop₀_toNat_eq_zero_of_nonpos {x : WithTop ℤ} (h : x ≤ 0) : x.untop₀.toNat = 0 := by
  induction x using WithTop.recTopCoe
  · simp
  · simp only [WithTop.untop₀_coe]
    exact Int.toNat_eq_zero.2 (by exact_mod_cast h)

lemma untop₀_toNat_neg_eq_zero_of_nonneg {x : WithTop ℤ} (h : 0 ≤ x) :
    (-x).untop₀.toNat = 0 := by
  induction x using WithTop.recTopCoe
  · simp
  · rename_i n
    rw [← WithTop.LinearOrderedAddCommGroup.coe_neg, WithTop.untop₀_coe]
    have : (0 : ℤ) ≤ n := by exact_mod_cast h
    exact Int.toNat_eq_zero.2 (by omega)

/-- **Lemma 3.4** (local degrees are invariant under the Möbius map `w ↦ 1/(w - c)`). -/
theorem mult_mobius {f : ℂ → ℂ} {z : ℂ} (hf : MeromorphicAt f z) (c : ℂ) (b : Sphere) :
    mult (fun w => (f w - c)⁻¹) (mobius c b) z = mult f b z := by
  induction b using WithTop.recTopCoe with
  | top =>
    simp only [mobius_top, mult_coe, sub_zero, mult_top]
    rw [order_mobius_comp]
    rcases lt_or_ge (meromorphicOrderAt f z) 0 with h | h
    · rw [order_sub_const_of_neg h]
    · rw [untop₀_toNat_neg_eq_zero_of_nonneg h,
        untop₀_toNat_neg_eq_zero_of_nonneg (order_sub_const_nonneg hf h c)]
  | coe d =>
    by_cases hdc : d = c
    · subst hdc
      simp only [mobius_self, mult_top, mult_coe]
      rw [order_mobius_comp, neg_neg]
    · rw [mobius_coe_of_ne hdc]
      simp only [mult_coe]
      have hm1 : MeromorphicAt (fun w => f w - d) z := hf.sub (MeromorphicAt.const _ _)
      have hm2 : MeromorphicAt (fun w => f w - c) z := hf.sub (MeromorphicAt.const _ _)
      have hdc' : d - c ≠ 0 := sub_ne_zero.2 hdc
      rcases hm2.eventually_eq_zero_or_eventually_ne_zero with hz | hnz
      · -- `f ≡ c` near `z`: both multiplicities vanish
        have h1 : meromorphicOrderAt (fun w => (f w - c)⁻¹ - (d - c)⁻¹) z = 0 := by
          rw [meromorphicOrderAt_congr (f₂ := fun _ => -(d - c)⁻¹)
            (hz.mono fun w hw => by simp [hw]),
            order_const_eq _ (neg_ne_zero.2 (inv_ne_zero hdc'))]
        have h2 : meromorphicOrderAt (fun w => f w - d) z = 0 := by
          rw [meromorphicOrderAt_congr (f₂ := fun _ => c - d)
            (hz.mono fun w hw => by simp only; rw [sub_eq_zero.1 hw]),
            order_const_eq _ (sub_ne_zero.2 (Ne.symm hdc))]
        rw [h1, h2]
      · -- `(f - c)⁻¹ - (d - c)⁻¹ = (f - d) * (f - c)⁻¹ * (-(d - c)⁻¹)` near `z`
        have hfun : (fun w => (f w - c)⁻¹ - (d - c)⁻¹) =ᶠ[nhdsWithin z {z}ᶜ]
            ((fun w => f w - d) * (fun w => f w - c)⁻¹) * (fun _ => -(d - c)⁻¹) := by
          filter_upwards [hnz] with w hw
          simp only [Pi.mul_apply, Pi.inv_apply]
          field_simp
          ring
        rw [meromorphicOrderAt_congr hfun,
          meromorphicOrderAt_mul (hm1.mul hm2.inv) (MeromorphicAt.const _ _),
          meromorphicOrderAt_mul hm1 hm2.inv, meromorphicOrderAt_inv,
          order_const_eq _ (neg_ne_zero.2 (inv_ne_zero hdc')), add_zero]
        rcases lt_trichotomy (meromorphicOrderAt (fun w => f w - d) z) 0 with h | h | h
        · have hfneg : meromorphicOrderAt f z < 0 := by
            by_contra hcon
            push_neg at hcon
            exact absurd (order_sub_const_nonneg hf hcon d) (not_le.2 h)
          rw [order_sub_const_of_neg hfneg d] at h ⊢
          rw [order_sub_const_of_neg hfneg c, untop₀_toNat_eq_zero_of_nonpos h.le]
          have : meromorphicOrderAt f z ≠ ⊤ := ne_top_of_lt hfneg
          obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 this
          rw [← hn, ← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add,
            add_neg_cancel, WithTop.untop₀_coe]
          rfl
        · rw [h, zero_add, untop₀_toNat_eq_zero_of_nonpos le_rfl]
          have hfnn : 0 ≤ meromorphicOrderAt f z := by
            by_contra hcon
            push_neg at hcon
            rw [order_sub_const_of_neg hcon] at h
            exact absurd h (ne_of_lt hcon)
          exact untop₀_toNat_neg_eq_zero_of_nonneg (order_sub_const_nonneg hf hfnn c)
        · rw [order_sub_const_eq_zero_of_pos hf hdc h, neg_zero, add_zero]

end ThreeIM
