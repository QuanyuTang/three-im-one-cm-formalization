module

public import RequestProject.ThreeIM.MathlibImports

/-!
# A short-radius growth bound (Lemma 6.1)
-/

@[expose] public section

open Filter Set MeasureTheory

namespace ThreeIM

/-- **Lemma 6.1** (a short-radius growth bound).  Let `L : [1, ∞) → [1, ∞)` be nondecreasing and
unbounded.  There is a measurable set `E₀` of finite linear measure such that
`L(r + 1/L(r)) ≤ 2 L(r)` for every `r ≥ 1` outside `E₀`.

(The paper also assumes that `L` is unbounded; this hypothesis turns out to be unnecessary.) -/
theorem short_growth {L : ℝ → ℝ} (hmono : MonotoneOn L (Ici 1)) (hge : ∀ r ≥ 1, 1 ≤ L r) :
    ∃ E₀ : Set ℝ, MeasurableSet E₀ ∧ volume E₀ < ⊤ ∧
      ∀ r ≥ 1, r ∉ E₀ → L (r + 1 / L r) ≤ 2 * L r := by
  -- `t j` is the first radius at which `L` reaches `2^(j+1)`
  let S : ℕ → Set ℝ := fun j => {r | 1 ≤ r ∧ (2 : ℝ) ^ (j + 1) ≤ L r}
  let t : ℕ → ℝ := fun j => sInf (S j)
  let E₀ : Set ℝ := ⋃ j : ℕ, Icc (t j - (2 : ℝ)⁻¹ ^ j) (t j)
  refine ⟨E₀, MeasurableSet.iUnion fun j => measurableSet_Icc, ?_, ?_⟩
  · calc volume E₀ ≤ ∑' j : ℕ, volume (Icc (t j - (2 : ℝ)⁻¹ ^ j) (t j)) := measure_iUnion_le _
      _ = ∑' j : ℕ, ENNReal.ofReal ((2 : ℝ)⁻¹ ^ j) := by
        congr 1; ext j; rw [Real.volume_Icc]; congr 1; ring
      _ = ∑' j : ℕ, ((2 : ENNReal)⁻¹) ^ j := by
        congr 1; ext j
        rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]
        simp
      _ = (1 - (2 : ENNReal)⁻¹)⁻¹ := ENNReal.tsum_geometric _
      _ < ⊤ := by
        rw [ENNReal.inv_lt_top]
        exact tsub_pos_of_lt (ENNReal.inv_lt_one.2 (by norm_num))
  · intro r hr hrE
    by_contra hcon
    push_neg at hcon
    have hLr : 1 ≤ L r := hge r hr
    -- choose `j` with `2^j ≤ L r < 2^(j+1)`
    obtain ⟨j, hj1, hj2⟩ : ∃ j : ℕ, (2 : ℝ) ^ j ≤ L r ∧ L r < 2 ^ (j + 1) := by
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (L r) (by norm_num : (1 : ℝ) < 2)
      classical
      let j := Nat.find (⟨n, hn⟩ : ∃ n : ℕ, L r < 2 ^ n)
      have hjpos : j ≠ 0 := by
        intro h0
        have := Nat.find_spec (⟨n, hn⟩ : ∃ n : ℕ, L r < 2 ^ n)
        rw [show Nat.find (⟨n, hn⟩ : ∃ n : ℕ, L r < 2 ^ n) = 0 from h0] at this
        simp at this; linarith
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hjpos
      refine ⟨k, ?_, ?_⟩
      · have := Nat.find_min (⟨n, hn⟩ : ∃ n : ℕ, L r < 2 ^ n) (m := k)
          (by rw [show Nat.find (⟨n, hn⟩ : ∃ n : ℕ, L r < 2 ^ n) = k + 1 from hk]; omega)
        push_neg at this; exact this
      · have := Nat.find_spec (⟨n, hn⟩ : ∃ n : ℕ, L r < 2 ^ n)
        rwa [show Nat.find (⟨n, hn⟩ : ∃ n : ℕ, L r < 2 ^ n) = k + 1 from hk] at this
    have hpos : 0 < L r := by linarith
    have hstep : 0 < 1 / L r := by positivity
    -- the radius `r + 1/L r` belongs to `S j`
    have h2j : (2 : ℝ) ^ (j + 1) = 2 * 2 ^ j := by ring
    have hmem : r + 1 / L r ∈ S j := ⟨by linarith, by linarith⟩
    have hbdd : BddBelow (S j) := ⟨1, fun x hx => hx.1⟩
    have ht_le : t j ≤ r + 1 / L r := csInf_le hbdd hmem
    -- every element of `S j` exceeds `r`
    have ht_ge : r ≤ t j := by
      apply le_csInf ⟨_, hmem⟩
      intro s hs
      by_contra hsr
      push_neg at hsr
      have := hmono hs.1 hr hsr.le
      linarith [hs.2]
    have hinv : 1 / L r ≤ (2 : ℝ)⁻¹ ^ j := by
      rw [inv_pow, one_div]
      exact inv_anti₀ (by positivity) hj1
    exact hrE (mem_iUnion.2 ⟨j, ⟨by linarith, ht_ge⟩⟩)

end ThreeIM
