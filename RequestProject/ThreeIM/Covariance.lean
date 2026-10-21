module

public import RequestProject.ThreeIM.Holomorphic

/-!
# Source covariance (Lemma 3.9) and the exponential precomposition of Lemma 4.12
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

/-- **Lemma 3.9** (multiplicities).  Precomposition with a holomorphic map `h` with `h'(z) ≠ 0`
(local degree one) preserves local degrees: `e_z(f ∘ h) = e_{h(z)}(f)` over every target. -/
theorem mult_comp_of_deriv_ne_zero {f h : ℂ → ℂ} {z : ℂ} (hh : AnalyticAt ℂ h z)
    (hh' : deriv h z ≠ 0) (b : Sphere) : mult (f ∘ h) b z = mult f b (h z) := by
  induction b using WithTop.recTopCoe with
  | top =>
    simp only [mult_top]
    rw [meromorphicOrderAt_comp_of_deriv_ne_zero hh hh']
  | coe c =>
    simp only [mult_coe]
    have : (fun w => (f ∘ h) w - c) = (fun w => f w - c) ∘ h := rfl
    rw [this, meromorphicOrderAt_comp_of_deriv_ne_zero hh hh']

/-- **Lemma 3.9** (auxiliary functions).  Where the chain rule applies,
`U_{f∘h, g∘h} = h' · U ∘ h`. -/
theorem auxU_comp {a : Fin 3 → ℂ} {f g h : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f (h z))
    (hh : DifferentiableAt ℂ h z) :
    auxU a (f ∘ h) (g ∘ h) z = deriv h z * auxU a f g (h z) := by
  simp only [auxU, Function.comp, deriv_comp z hf hh]
  ring

/-- **Lemma 3.9** (auxiliary functions).  Where the chain rule applies,
`V_{f∘h, g∘h} = h' · V ∘ h`. -/
theorem auxV_comp {a : Fin 3 → ℂ} {f g h : ℂ → ℂ} {z : ℂ} (hg : DifferentiableAt ℂ g (h z))
    (hh : DifferentiableAt ℂ h z) :
    auxV a (f ∘ h) (g ∘ h) z = deriv h z * auxV a f g (h z) := by
  simp only [auxV, Function.comp_apply, deriv_comp z hg hh]
  ring

/-- **Lemma 3.9** (auxiliary functions): `Ψ_{f∘h, g∘h} = (h')² · Ψ ∘ h` and, where `h' ≠ 0`,
`Φ_{f∘h, g∘h} = Φ ∘ h`. -/
theorem auxPsi_auxPhi_comp {a : Fin 3 → ℂ} {f g h : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f (h z)) (hg : DifferentiableAt ℂ g (h z))
    (hh : DifferentiableAt ℂ h z) :
    auxPsi a (f ∘ h) (g ∘ h) z = deriv h z ^ 2 * auxPsi a f g (h z) ∧
      (deriv h z ≠ 0 → auxPhi a (f ∘ h) (g ∘ h) z = auxPhi a f g (h z)) := by
  refine ⟨?_, fun hne => ?_⟩
  · simp only [auxPsi, auxU_comp hf hh, auxV_comp hg hh]; ring
  · simp only [auxPhi, auxU_comp hf hh, auxV_comp hg hh]
    rw [mul_div_mul_left _ _ hne]

/-- **Lemma 3.9** (sharing).  Precomposition with an entire map with nowhere-vanishing derivative
preserves IM sharing. -/
theorem SharesIMOn.comp {f g h : ℂ → ℂ} {b : Sphere} (hfg : SharesIMOn univ f g b)
    (hh : ∀ z, AnalyticAt ℂ h z) (hh' : ∀ z, deriv h z ≠ 0) :
    SharesIMOn univ (f ∘ h) (g ∘ h) b := by
  intro z _
  rw [mult_comp_of_deriv_ne_zero (hh z) (hh' z), mult_comp_of_deriv_ne_zero (hh z) (hh' z)]
  exact hfg (h z) (mem_univ _)

/-- **Lemma 3.9** (sharing).  Precomposition with an entire map with nowhere-vanishing derivative
preserves CM sharing. -/
theorem SharesCMOn.comp {f g h : ℂ → ℂ} {b : Sphere} (hfg : SharesCMOn univ f g b)
    (hh : ∀ z, AnalyticAt ℂ h z) (hh' : ∀ z, deriv h z ≠ 0) :
    SharesCMOn univ (f ∘ h) (g ∘ h) b := by
  intro z _
  rw [mult_comp_of_deriv_ne_zero (hh z) (hh' z), mult_comp_of_deriv_ne_zero (hh z) (hh' z)]
  exact hfg (h z) (mem_univ _)

/-- Precomposition of a normalized pair on `ℂ` with an entire map with nowhere-vanishing
derivative is a normalized pair. -/
theorem NormalizedPair.comp {f g h : ℂ → ℂ} {a : Fin 3 → ℂ} (hp : NormalizedPair univ f g a)
    (hh : ∀ z, AnalyticAt ℂ h z) (hh' : ∀ z, deriv h z ≠ 0) :
    NormalizedPair univ (f ∘ h) (g ∘ h) a where
  nonconst_f := ⟨fun z _ => (hp.nonconst_f.1 (h z) (mem_univ _)).comp_analyticAt (hh z),
    fun z _ c => by
      have : (fun w => (f ∘ h) w - c) = (fun w => f w - c) ∘ h := rfl
      rw [this, meromorphicOrderAt_comp_of_deriv_ne_zero (hh z) (hh' z)]
      exact hp.nonconst_f.2 (h z) (mem_univ _) c⟩
  nonconst_g := ⟨fun z _ => (hp.nonconst_g.1 (h z) (mem_univ _)).comp_analyticAt (hh z),
    fun z _ c => by
      have : (fun w => (g ∘ h) w - c) = (fun w => g w - c) ∘ h := rfl
      rw [this, meromorphicOrderAt_comp_of_deriv_ne_zero (hh z) (hh' z)]
      exact hp.nonconst_g.2 (h z) (mem_univ _) c⟩
  distinct z _ := by
    have : (fun w => (f ∘ h) w - (g ∘ h) w) = (fun w => f w - g w) ∘ h := rfl
    rw [this, meromorphicOrderAt_comp_of_deriv_ne_zero (hh z) (hh' z)]
    exact hp.distinct (h z) (mem_univ _)
  injective := hp.injective
  im j := (hp.im j).comp hh hh'
  cm_top := hp.cm_top.comp hh hh'

/-- The map `t ↦ z⋆ - 1 + e^t` used in Lemmas 4.10 and 4.12. -/
noncomputable def expShift (zs : ℂ) (t : ℂ) : ℂ := zs - 1 + Complex.exp t

lemma expShift_analyticAt (zs t : ℂ) : AnalyticAt ℂ (expShift zs) t := by
  unfold expShift; fun_prop

lemma deriv_expShift (zs t : ℂ) : deriv (expShift zs) t = Complex.exp t := by
  unfold expShift
  simp

lemma expShift_two_pi_I_mul (zs : ℂ) (k : ℤ) :
    expShift zs (2 * Real.pi * Complex.I * k) = zs := by
  unfold expShift
  rw [show (2 * Real.pi * Complex.I * k : ℂ) = k * (2 * Real.pi * Complex.I) by ring,
    Complex.exp_int_mul_two_pi_mul_I]
  ring

lemma expShift_periodic (zs t : ℂ) :
    expShift zs (t + 2 * Real.pi * Complex.I) = expShift zs t := by
  unfold expShift
  rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- **Lemma 4.12** (construction step).  Precomposing a normalized pair on `ℂ` having a defect
at `z⋆` with `h(t) = z⋆ - 1 + e^t` gives a `2πi`-periodic normalized pair which has the same
defect at every point `2πik`, `k ∈ ℤ`. -/
theorem NormalizedPair.comp_expShift {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (hp : NormalizedPair univ f g a) {zs : ℂ} {j : Fin 3} (hd : IsDefect f g (a j : Sphere) zs) :
    NormalizedPair univ (f ∘ expShift zs) (g ∘ expShift zs) a ∧
      (∀ t, (f ∘ expShift zs) (t + 2 * Real.pi * Complex.I) = (f ∘ expShift zs) t) ∧
      (∀ t, (g ∘ expShift zs) (t + 2 * Real.pi * Complex.I) = (g ∘ expShift zs) t) ∧
      ∀ k : ℤ, IsDefect (f ∘ expShift zs) (g ∘ expShift zs) (a j : Sphere)
        (2 * Real.pi * Complex.I * k) := by
  have hh := expShift_analyticAt zs
  have hh' : ∀ t, deriv (expShift zs) t ≠ 0 := fun t => by
    rw [deriv_expShift]; exact Complex.exp_ne_zero t
  refine ⟨hp.comp hh hh', fun t => by simp [expShift_periodic],
    fun t => by simp [expShift_periodic], fun k => ?_⟩
  unfold IsDefect
  rw [mult_comp_of_deriv_ne_zero (hh _) (hh' _), mult_comp_of_deriv_ne_zero (hh _) (hh' _),
    expShift_two_pi_I_mul]
  exact hd

end ThreeIM
