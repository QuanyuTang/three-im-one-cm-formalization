module

public import RequestProject.ThreeIM.RationalDegree

/-!
# Opposite endpoint poles without the assumption of Lemma 9.2 (Lemma 9.5, first part)

For a rational sharing datum `R, S` (a normalized pair on `ℂ*`), Lemma 9.2 (now proved in
`RationalDegree.lean`) shows that both endpoints lie over `{a 0, a 1, a 2, ∞}` for both maps and
that there is no coincidence at `0` or `∞`.  If the finite endpoint case (Lemma 9.4) does not
apply, then, after possibly interchanging `R` and `S`, `R` is finite at `0` with value in
`{a 0, a 1, a 2}`, `S` has a pole at `0`, `R` has a pole at `∞` and `S` is finite at `∞` with value
in `{a 0, a 1, a 2}`; the two pole orders are a common `ρ ≥ 1`, and `U = α t^{-ρ}`, `V = β t^ρ`.
-/

@[expose] public section

open Filter Set Topology Polynomial

namespace ThreeIM

variable {R S : RatFunc ℂ} {a : Fin 3 → ℂ}

/-- At a zero of the denominator, `R` has a pole of order the root multiplicity of the
denominator. -/
lemma order_ratEval_of_denom_eq_zero {t : ℂ} (hd : R.denom.eval t = 0) :
    0 < R.denom.rootMultiplicity t ∧
      meromorphicOrderAt (ratEval R) t =
        ((-(R.denom.rootMultiplicity t : ℤ) : ℤ) : WithTop ℤ) := by
  have hn : R.num.eval t ≠ 0 := (num_or_denom_ne_zero R t).resolve_right (not_not.2 hd)
  refine ⟨(rootMultiplicity_pos R.denom_ne_zero).2 hd, ?_⟩
  rw [funext (ratEval_eq R)]
  exact order_polyQuot R.denom_ne_zero hn

/-- If `R(∞) = ∞`, then `t ↦ R(1/t)` has a pole at `0`. -/
lemma order_ratEval_inv_of_infVal_eq_top (hR : ∀ c : ℂ, R ≠ RatFunc.C c)
    (h : infVal R.num R.denom = ⊤) :
    0 < (reflect (ratDeg R) R.denom).rootMultiplicity 0 ∧
      meromorphicOrderAt (fun t => ratEval R t⁻¹) 0 =
        ((-((reflect (ratDeg R) R.denom).rootMultiplicity 0 : ℤ) : ℤ) : WithTop ℤ) := by
  unfold infVal at h
  by_cases h1 : R.denom.natDegree < max R.num.natDegree R.denom.natDegree
  swap
  · rw [if_neg h1] at h; exact absurd h WithTop.coe_ne_top
  have hnum : R.num.natDegree = ratDeg R := by
    unfold ratDeg at h1 ⊢
    rcases le_total R.num.natDegree R.denom.natDegree with h2 | h2
    · rw [max_eq_right h2] at h1; omega
    · rw [max_eq_left h2]
  have hP0 : (reflect (ratDeg R) R.num).eval 0 ≠ 0 := by
    rw [eval_reflect_zero, ← hnum]
    exact leadingCoeff_ne_zero.2 (num_ne_zero_of_nonconst hR)
  have hQ0 : (reflect (ratDeg R) R.denom).eval 0 = 0 := by
    rw [eval_reflect_zero]; exact coeff_eq_zero_of_natDegree_lt h1
  refine ⟨(rootMultiplicity_pos (reflect_denom_ne_zero R)).2 hQ0, ?_⟩
  have heq : (fun t => ratEval R t⁻¹) =ᶠ[𝓝[≠] 0] ratInvFun R := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (ratInvFun_eq R hs).symm
  rw [meromorphicOrderAt_congr heq]
  exact order_polyQuot (reflect_denom_ne_zero R) hP0

/-- The endpoint data of **Lemma 9.5** for the ordered pair `(R, S)`, with explicit parameters:
`R` is finite at `0` with `R(0) = a j`, `S` has a pole of order `ρ ≥ 1` at `0`, `R` has a pole of
order `ρ` at `∞` (`t ↦ R(1/t)` has a pole of order `ρ` at `0`), `S(t) → a k` as `t → ∞`, and
`t·U(t) = α t^{-ρ}`, `t·V(t) = β t^ρ` with `α, β ≠ 0` (off a finite set). -/
structure OppositeData (a : Fin 3 → ℂ) (R S : RatFunc ℂ) (j k : Fin 3) (ρ : ℕ) (α β : ℂ) :
    Prop where
  rho_pos : 0 < ρ
  alpha_ne : α ≠ 0
  beta_ne : β ≠ 0
  denom_zero : R.denom.eval 0 ≠ 0
  value_zero : ratEval R 0 = a j
  order_zero : meromorphicOrderAt (ratEval S) 0 = ((-(ρ : ℤ) : ℤ) : WithTop ℤ)
  order_infty : meromorphicOrderAt (fun t => ratEval R t⁻¹) 0 = ((-(ρ : ℤ) : ℤ) : WithTop ℤ)
  tendsto_infty : Tendsto (ratEval S) (cocompact ℂ) (𝓝 (a k))
  aux_U : ∀ᶠ t in cofinite, t * auxU a (ratEval R) (ratEval S) t = α * t ^ (-(ρ : ℤ))
  aux_V : ∀ᶠ t in cofinite, t * auxV a (ratEval R) (ratEval S) t = β * t ^ (ρ : ℤ)

/-- The endpoint configuration of **Lemma 9.5** for the ordered pair `(R, S)`: `OppositeData`
holds for some parameters. -/
def OppositeEndpoints (a : Fin 3 → ℂ) (R S : RatFunc ℂ) : Prop :=
  ∃ (j k : Fin 3) (ρ : ℕ) (α β : ℂ), OppositeData a R S j k ρ α β

/-- One half of the case analysis: if `S` has a pole at `0`, `R` is finite at `0`, `R` is
infinite at `∞` and `S` is finite at `∞`, the configuration `OppositeEndpoints a R S` holds. -/
lemma oppositeEndpoints_of_poles (hpair : NormalizedPair {0}ᶜ (ratEval R) (ratEval S) a)
    (hR0 : R.denom.eval 0 ≠ 0) (hS0 : S.denom.eval 0 = 0)
    (hRi : infVal R.num R.denom = ⊤) (hSi : infVal S.num S.denom ≠ ⊤) :
    OppositeEndpoints a R S := by
  have hRnc := ne_C_of_nonconst hpair.nonconst_f
  obtain ⟨hR, -, -, -⟩ := rational_endpoint_zero hpair
  obtain ⟨j, hj⟩ := hR.resolve_left hR0
  obtain ⟨-, hS, -⟩ := rational_endpoint_infty hpair
  obtain ⟨k, hk⟩ := (mem_valueSet.1 hS).resolve_right hSi
  obtain ⟨hs, hSo⟩ := order_ratEval_of_denom_eq_zero hS0
  obtain ⟨hr, hRo⟩ := order_ratEval_inv_of_infVal_eq_top hRnc hRi
  have hSk := tendsto_ratEval_of_infVal hk
  obtain ⟨hrs, α, β, hα, hβ, hU, hV⟩ := rational_endpoint_exponents hpair
    (rational_coincidenceSimple hpair) hR0 hj hs hSo hr hRo hSk
  refine ⟨j, k, _, α, β, ⟨hs, hα, hβ, hR0, hj, hSo, ?_, hSk, hU, hV⟩⟩
  rw [hRo, hrs]

/-- **Lemma 9.5** (opposite endpoint poles), first part, without the assumption of Lemma 9.2:
if the finite endpoint case of Lemma 9.4 does not apply (the maps are not both finite at `0`,
and not both finite at `∞`), then after possibly interchanging `R` and `S`, the endpoint
configuration `OppositeEndpoints` holds: `R(0) ∈ {a j}`, `S(0) = ∞`, `R(∞) = ∞`,
`S(∞) ∈ {a j}`, both poles of a common order `ρ ≥ 1`, `U = α t^{-ρ}` and `V = β t^ρ`. -/
theorem rational_opposite_endpoints (hpair : NormalizedPair {0}ᶜ (ratEval R) (ratEval S) a)
    (hnot : ¬ ((R.denom.eval 0 ≠ 0 ∧ S.denom.eval 0 ≠ 0) ∨
      (infVal R.num R.denom ≠ ⊤ ∧ infVal S.num S.denom ≠ ⊤))) :
    OppositeEndpoints a R S ∨ OppositeEndpoints a S R := by
  have hRnc := ne_C_of_nonconst hpair.nonconst_f
  have hSnc := ne_C_of_nonconst hpair.nonconst_g
  push_neg at hnot
  obtain ⟨h0, hinf⟩ := hnot
  obtain ⟨hR, hS, hboth, -⟩ := rational_endpoint_zero hpair
  obtain ⟨-, -, hne⟩ := rational_endpoint_infty hpair
  by_cases hR0 : R.denom.eval 0 = 0
  · have hS0 : S.denom.eval 0 ≠ 0 := fun h => hboth ⟨hR0, h⟩
    by_cases hRi : infVal R.num R.denom = ⊤
    · exfalso
      have hSi : infVal S.num S.denom ≠ ⊤ := fun h => hne (hRi.trans h.symm)
      obtain ⟨k, hk⟩ := hS.resolve_left hS0
      obtain ⟨k', hk'⟩ := (mem_valueSet.1 (rational_endpoint_infty hpair).2.1).resolve_right hSi
      obtain ⟨hs, hRo⟩ := order_ratEval_of_denom_eq_zero hR0
      obtain ⟨hr, hRo'⟩ := order_ratEval_inv_of_infVal_eq_top hRnc hRi
      exact rational_not_pole_both_endpoints hpair (rational_coincidenceSimple hpair) hs hRo hS0
        hk hr hRo' (tendsto_ratEval_of_infVal hk')
    · exact Or.inr (oppositeEndpoints_of_poles hpair.symm hS0 hR0 (hinf hRi) hRi)
  · have hS0 : S.denom.eval 0 = 0 := h0 hR0
    by_cases hRi : infVal R.num R.denom = ⊤
    · exact Or.inl (oppositeEndpoints_of_poles hpair hR0 hS0 hRi
        (fun h => hne (hRi.trans h.symm)))
    · exfalso
      have hSi := hinf hRi
      obtain ⟨k, hk⟩ := hR.resolve_left hR0
      obtain ⟨k', hk'⟩ := (mem_valueSet.1 (rational_endpoint_infty hpair).1).resolve_right hRi
      obtain ⟨hs, hSo⟩ := order_ratEval_of_denom_eq_zero hS0
      obtain ⟨hr, hSo'⟩ := order_ratEval_inv_of_infVal_eq_top hSnc hSi
      exact rational_not_pole_both_endpoints hpair.symm (rational_coincidenceSimple hpair.symm)
        hs hSo hR0 hk hr hSo' (tendsto_ratEval_of_infVal hk')

end ThreeIM

namespace ThreeIM

/-- **Lemmas 9.26 + 9.27 and the conclusion of Proposition 9.28** for a pair with endpoint pole
order `ρ = 1`, without the assumption of Lemma 9.2 (which is now proved): a normalized pair on
`ℂ*` for the values `0, 1, c` (`c < 0`) with `U = κ t^{-1}`, `V = κ t` (`κ > 0`), `R(0) = 0`,
`R(t) ∼ t/κ` at `∞`, `S(∞) = 0` and `S(t) ∼ 1/(κ t)` at `0` shares all four values CM on
`ℂ*`. -/
theorem rational_cm_rho_one_of_pair {R S : RatFunc ℂ} {c κ : ℝ} (hc : c < 0) (hκ : 0 < κ)
    (hpair : NormalizedPair {0}ᶜ (ratEval R) (ratEval S) ![0, 1, (c : ℂ)])
    (hU : ∀ᶠ t in cofinite,
      t * auxU ![0, 1, (c : ℂ)] (ratEval R) (ratEval S) t = κ * t ^ (-1 : ℤ))
    (hV : ∀ᶠ t in cofinite,
      t * auxV ![0, 1, (c : ℂ)] (ratEval R) (ratEval S) t = κ * t ^ (1 : ℤ))
    (hR0 : R.num.eval 0 = 0) (hdeg : R.num.natDegree = R.denom.natDegree + 1)
    (hlc : R.num.leadingCoeff / R.denom.leadingCoeff = 1 / κ)
    (hS0 : S.denom.eval 0 = 0) (hres : S.num.eval 0 / S.denom.derivative.eval 0 = 1 / κ)
    (hSinf : S.num.natDegree < S.denom.natDegree) :
    ∀ i : Fin 4, SharesCMOn {0}ᶜ (ratEval R) (ratEval S)
      (![((0 : ℂ) : Sphere), ((1 : ℂ) : Sphere), ((c : ℂ) : Sphere), ⊤] i) :=
  rational_cm_rho_one hc hκ hpair (rational_coincidenceSimple hpair) hU hV hR0 hdeg hlc hS0 hres
    hSinf

end ThreeIM
