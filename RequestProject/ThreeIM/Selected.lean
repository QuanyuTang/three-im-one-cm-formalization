module

public import RequestProject.ThreeIM.Basic

/-!
# Selected configurations (Definition 10.2) and their uniform control (Lemma 10.3)
-/

@[expose] public section

open Filter Set Metric Topology

namespace ThreeIM

/-- A *selected configuration* (Definition 10.2).

* three distinct finite values `a`, a marked value `a j`, an integer `2 ≤ m ≤ 30`,
  `q = 1/m`;
* radii `B n → ∞` and normalized pairs `(F n, G n)` on the disks `D(0, B n ^ 6 / 2)`, each with
  a marked `(1, m)`-point over `a j` at `0`;
* zero-free holomorphic functions `k n` on these disks with
  `U_n(s) = √q e^{s/2} / k_n(s)`, `V_n(s) = q^{-1/2} e^{-s/2} / k_n(s)`,
  `|log |k_n(0)|| ≤ 9 B_n²`, and `|log (k_n(s)/k_n(0))| ≤ 12 B_n⁻³` on the disk, for the
  branch of the logarithm vanishing at `0`.

The identities for `U_n, V_n` are identities of meromorphic functions, so they are required
to hold off a discrete subset of the disk. -/
structure SelectedConfiguration where
  a : Fin 3 → ℂ
  j : Fin 3
  m : ℕ
  two_le_m : 2 ≤ m
  m_le_thirty : m ≤ 30
  B : ℕ → ℝ
  B_pos : ∀ n, 0 < B n
  tendsto_B : Tendsto B atTop atTop
  F : ℕ → ℂ → ℂ
  G : ℕ → ℂ → ℂ
  k : ℕ → ℂ → ℂ
  pair : ∀ n, NormalizedPair (ball 0 (B n ^ 6 / 2)) (F n) (G n) a
  marked_F : ∀ n, mult (F n) (a j : Sphere) 0 = 1
  marked_G : ∀ n, mult (G n) (a j : Sphere) 0 = m
  k_holo : ∀ n, DifferentiableOn ℂ (k n) (ball 0 (B n ^ 6 / 2))
  k_ne_zero : ∀ n, ∀ s ∈ ball (0 : ℂ) (B n ^ 6 / 2), k n s ≠ 0
  coeff_U : ∀ n, ∀ᶠ s in codiscreteWithin (ball (0 : ℂ) (B n ^ 6 / 2)),
    auxU a (F n) (G n) s = (Real.sqrt (1 / m) : ℂ) * Complex.exp (s / 2) / k n s
  coeff_V : ∀ n, ∀ᶠ s in codiscreteWithin (ball (0 : ℂ) (B n ^ 6 / 2)),
    auxV a (F n) (G n) s = (Real.sqrt (1 / m) : ℂ)⁻¹ * Complex.exp (-s / 2) / k n s
  control_center : ∀ n, |Real.log ‖k n 0‖| ≤ 9 * B n ^ 2
  control_log : ∀ n, ∃ ℓ : ℂ → ℂ, DifferentiableOn ℂ ℓ (ball 0 (B n ^ 6 / 2)) ∧ ℓ 0 = 0 ∧
    ∀ s ∈ ball (0 : ℂ) (B n ^ 6 / 2),
      Complex.exp (ℓ s) = k n s / k n 0 ∧ ‖ℓ s‖ ≤ 12 * (B n)⁻¹ ^ 3

namespace SelectedConfiguration

variable (S : SelectedConfiguration)

/-- The normalised coefficients `c_n = k_n(0)`. -/
noncomputable def c (n : ℕ) : ℂ := S.k n 0

/-- **Lemma 10.3** (uniform constancy of the normalized coefficient):
`sup |k_n/c_n - 1| → 0` and `sup |c_n/k_n - 1| → 0` over the disks, and
`|log |c_n|| ≤ 9 B_n²`. -/
theorem uniform (S : SelectedConfiguration) :
    (∀ ε > 0, ∀ᶠ n in atTop, ∀ s ∈ ball (0 : ℂ) (S.B n ^ 6 / 2),
      ‖S.k n s / S.c n - 1‖ ≤ ε ∧ ‖S.c n / S.k n s - 1‖ ≤ ε) ∧
    ∀ n, |Real.log ‖S.c n‖| ≤ 9 * S.B n ^ 2 := by
  refine ⟨fun ε hε => ?_, S.control_center⟩
  -- `12 B_n⁻³ → 0`
  have hlim : Tendsto (fun n => 12 * (S.B n)⁻¹ ^ 3) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.comp S.tendsto_B).pow 3
    simpa using this.const_mul 12
  have hev : ∀ᶠ n in atTop, 12 * (S.B n)⁻¹ ^ 3 ≤ min 1 (ε / 2) :=
    hlim.eventually (ge_mem_nhds (lt_min one_pos (half_pos hε)))
  filter_upwards [hev] with n hn s hs
  obtain ⟨ℓ, -, -, hℓ⟩ := S.control_log n
  obtain ⟨hexp, hbd⟩ := hℓ s hs
  have hk0 : S.k n 0 ≠ 0 := S.k_ne_zero n 0 (by simp [S.B_pos n])
  have hks : S.k n s ≠ 0 := S.k_ne_zero n s hs
  have hsmall : ‖ℓ s‖ ≤ 1 := hbd.trans (hn.trans (min_le_left _ _))
  have hsmall' : ‖-ℓ s‖ ≤ 1 := by rwa [norm_neg]
  have h2 : 2 * ‖ℓ s‖ ≤ ε := by
    have := hbd.trans (hn.trans (min_le_right _ _)); linarith
  constructor
  · rw [SelectedConfiguration.c, ← hexp]
    exact (Complex.norm_exp_sub_one_le hsmall).trans h2
  · have : S.c n / S.k n s = Complex.exp (-ℓ s) := by
      rw [Complex.exp_neg, hexp, SelectedConfiguration.c, inv_div]
    rw [this]
    exact (Complex.norm_exp_sub_one_le hsmall').trans (by rwa [norm_neg])

end SelectedConfiguration

end ThreeIM
