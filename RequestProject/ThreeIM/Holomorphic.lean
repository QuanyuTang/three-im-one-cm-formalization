module

public import RequestProject.ThreeIM.Local

/-!
# Holomorphicity of the auxiliary functions (Lemmas 3.7 and 3.8)

For a normalized pair, `U`, `V` and `Ψ = UV` have nonnegative order at every point (they are
holomorphic after removing removable singularities) and finite order (they are not
identically zero).
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

/-- If `f - a` has order `n ≠ 0` at `z₀` (a zero or a pole), then `f'` has order `n - 1`. -/
theorem order_deriv_of_order_eq {f : ℂ → ℂ} {z₀ a : ℂ} (hf : MeromorphicAt f z₀) {n : ℤ}
    (hn0 : n ≠ 0) (hn : meromorphicOrderAt (fun w => f w - a) z₀ = n) :
    meromorphicOrderAt (deriv f) z₀ = ((n - 1 : ℤ) : WithTop ℤ) := by
  obtain ⟨g, hga, hg0, hfg⟩ :=
    (meromorphicOrderAt_eq_int_iff (hf.sub (MeromorphicAt.const a z₀))).1 hn
  set F : ℂ → ℂ := fun w => (w - z₀) ^ n * g w with hF
  have hfF : (fun w => f w - a) =ᶠ[𝓝[≠] z₀] F :=
    hfg.mono fun w hw => by simpa [hF] using hw
  have hderiv : deriv (fun w => f w - a) =ᶠ[𝓝[≠] z₀] deriv F := hfF.nhdsNE_deriv
  have hderiv' : deriv f =ᶠ[𝓝[≠] z₀] deriv F := by
    have : deriv (fun w => f w - a) = deriv f := funext fun w => deriv_sub_const a
    rwa [this] at hderiv
  set G : ℂ → ℂ := fun w => (n : ℂ) * g w + (w - z₀) * deriv g w with hG
  have hGa : AnalyticAt ℂ G z₀ := by
    have := hga.deriv
    simp only [hG]
    fun_prop
  have hG0 : G z₀ ≠ 0 := by
    simp only [hG, sub_self, zero_mul, add_zero]
    exact mul_ne_zero (by exact_mod_cast hn0) hg0
  have hFG : ∀ᶠ w in 𝓝[≠] z₀, deriv F w = (w - z₀) ^ (n - 1) * G w := by
    filter_upwards [nhdsWithin_le_nhds hga.eventually_analyticAt, self_mem_nhdsWithin]
      with w hw hwz
    have hwz' : w - z₀ ≠ 0 := sub_ne_zero.2 hwz
    have hd : DifferentiableAt ℂ (fun w => (w - z₀) ^ n) w :=
      ((differentiableAt_zpow).2 (Or.inl hwz')).comp w (differentiableAt_id.sub_const z₀)
    rw [hF, deriv_fun_mul hd hw.differentiableAt]
    have : deriv (fun w => (w - z₀) ^ n) w = (n : ℂ) * (w - z₀) ^ (n - 1) := by
      rw [deriv_comp_sub_const (f := fun x : ℂ => x ^ n)]
      simp [deriv_zpow]
    rw [this, hG]
    have : (w - z₀) ^ n = (w - z₀) ^ (n - 1) * (w - z₀) := by
      rw [← zpow_add_one₀ hwz', sub_add_cancel]
    rw [this]
    ring
  rw [meromorphicOrderAt_eq_int_iff hf.deriv]
  refine ⟨G, hGa, hG0, ?_⟩
  filter_upwards [hderiv', hFG] with w h1 h2
  rw [h1, h2, smul_eq_mul]

lemma order_neg_eq (h : ℂ → ℂ) (z : ℂ) :
    meromorphicOrderAt (fun w => -h w) z = meromorphicOrderAt h z := by
  by_cases hm : MeromorphicAt h z
  · have : (fun w => -h w) = (fun _ => (-1 : ℂ)) * h := by ext w; simp
    rw [this, meromorphicOrderAt_mul (MeromorphicAt.const _ _) hm,
      order_const_eq _ (by norm_num), zero_add]
  · have hm' : ¬ MeromorphicAt (fun w => -h w) z := fun h' => hm (by
      have := h'.neg
      convert this using 1
      ext w; simp)
    rw [meromorphicOrderAt_of_not_meromorphicAt hm, meromorphicOrderAt_of_not_meromorphicAt hm']

/-- A positive multiplicity over a finite value is the order of `f - c`. -/
lemma order_sub_eq_mult {f : ℂ → ℂ} {z c : ℂ}
    (hpos : 0 < mult f (c : Sphere) z) :
    meromorphicOrderAt (fun w => f w - c) z = ((mult f (c : Sphere) z : ℕ) : ℤ) := by
  simp only [mult_coe] at hpos ⊢
  induction h : meromorphicOrderAt (fun w => f w - c) z using WithTop.recTopCoe with
  | top => rw [h] at hpos; simp at hpos
  | coe k =>
    rw [h] at hpos
    simp only [WithTop.untop₀_coe] at hpos ⊢
    congr 1; omega

/-- A positive multiplicity over `∞` is minus the order of `f`. -/
lemma order_eq_neg_mult_top {f : ℂ → ℂ} {z : ℂ} (hpos : 0 < mult f ⊤ z) :
    meromorphicOrderAt f z = ((-(mult f ⊤ z : ℕ) : ℤ) : WithTop ℤ) := by
  simp only [mult_top] at hpos ⊢
  induction h : meromorphicOrderAt f z using WithTop.recTopCoe with
  | top => rw [h] at hpos; simp at hpos
  | coe k =>
    rw [h] at hpos
    rw [← WithTop.LinearOrderedAddCommGroup.coe_neg, WithTop.untop₀_coe] at hpos ⊢
    congr 1; omega

/-- Zero multiplicity over a finite value forces nonpositive order (when finite). -/
lemma order_sub_nonpos_of_mult_eq_zero {f : ℂ → ℂ} {z c : ℂ}
    (h0 : mult f (c : Sphere) z = 0) (hne : meromorphicOrderAt (fun w => f w - c) z ≠ ⊤) :
    meromorphicOrderAt (fun w => f w - c) z ≤ 0 := by
  simp only [mult_coe] at h0
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 hne
  rw [← hk] at h0 ⊢
  simp only [WithTop.untop₀_coe] at h0
  exact_mod_cast (by omega : k ≤ 0)

/-- Zero multiplicity over `∞` forces nonnegative order (when finite). -/
lemma order_nonneg_of_mult_top_eq_zero {f : ℂ → ℂ} {z : ℂ}
    (h0 : mult f ⊤ z = 0) (hne : meromorphicOrderAt f z ≠ ⊤) :
    0 ≤ meromorphicOrderAt f z := by
  simp only [mult_top] at h0
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 hne
  rw [← hk] at h0 ⊢
  rw [← WithTop.LinearOrderedAddCommGroup.coe_neg, WithTop.untop₀_coe] at h0
  exact_mod_cast (by omega : 0 ≤ k)

lemma order_ne_top_of_nonconst {f : ℂ → ℂ} {Ω : Set ℂ} (hf : IsNonconstMeroOn f Ω) {z : ℂ}
    (hz : z ∈ Ω) : meromorphicOrderAt f z ≠ ⊤ := by
  have := hf.2 z hz 0
  simpa using this

/-- For a nonconstant meromorphic function, the derivative has finite order, and nonnegative
order wherever `f` has no pole. -/
lemma order_deriv_of_nonconst {f : ℂ → ℂ} {Ω : Set ℂ} (hf : IsNonconstMeroOn f Ω) {z : ℂ}
    (hz : z ∈ Ω) :
    meromorphicOrderAt (deriv f) z ≠ ⊤ ∧
      (0 ≤ meromorphicOrderAt f z → 0 ≤ meromorphicOrderAt (deriv f) z) := by
  have hm := hf.1 z hz
  rcases lt_or_ge (meromorphicOrderAt f z) 0 with hneg | hnn
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 (order_ne_top_of_nonconst hf hz)
    have hn' : meromorphicOrderAt (fun w => f w - 0) z = n := by simpa using hn.symm
    have hn0 : n ≠ 0 := by rintro rfl; rw [← hn] at hneg; exact lt_irrefl _ hneg
    rw [order_deriv_of_order_eq hm hn0 hn']
    exact ⟨WithTop.coe_ne_top, fun h => absurd h (not_le.2 hneg)⟩
  · obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hm hnn
    have hpos : 0 < meromorphicOrderAt (fun w => f w - c) z :=
      (tendsto_zero_iff_meromorphicOrderAt_pos (f := fun w => f w - c)
        (hm.sub (MeromorphicAt.const c z))).1 (by simpa using hc.sub_const c)
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 (hf.2 z hz c)
    have hk0 : 0 < k := by rw [← hk] at hpos; exact_mod_cast hpos
    rw [order_deriv_of_order_eq hm hk0.ne' hk.symm]
    refine ⟨WithTop.coe_ne_top, fun _ => ?_⟩
    exact_mod_cast (by omega : (0 : ℤ) ≤ k - 1)

/-- Order of `P ∘ f` at a pole of `f` of order `k`. -/
lemma order_cubicP_comp_of_neg {f : ℂ → ℂ} {z : ℂ} (hf : MeromorphicAt f z) (a : Fin 3 → ℂ)
    {k : ℤ} (hneg : k < 0) (hk : meromorphicOrderAt f z = k) :
    meromorphicOrderAt (fun w => cubicP a (f w)) z = ((3 * k : ℤ) : WithTop ℤ) := by
  have hneg' : meromorphicOrderAt f z < 0 := by rw [hk]; exact_mod_cast hneg
  have hmer : ∀ i, MeromorphicAt (fun w => f w - a i) z :=
    fun i => hf.sub (MeromorphicAt.const _ _)
  have hfun : (fun w => cubicP a (f w)) =
      ((fun w => f w - a 0) * (fun w => f w - a 1)) * (fun w => f w - a 2) := by
    ext w; simp [cubicP]
  rw [hfun, meromorphicOrderAt_mul ((hmer 0).mul (hmer 1)) (hmer 2),
    meromorphicOrderAt_mul (hmer 0) (hmer 1), order_sub_const_of_neg hneg',
    order_sub_const_of_neg hneg', order_sub_const_of_neg hneg', hk,
    ← WithTop.coe_add, ← WithTop.coe_add]
  congr 1; ring

/-- Order of `P ∘ f` at a point that is neither a pole nor an `a_j`-point. -/
lemma order_cubicP_comp_eq_zero {f : ℂ → ℂ} {z : ℂ} (hf : MeromorphicAt f z)
    (a : Fin 3 → ℂ) (h : ∀ i, meromorphicOrderAt (fun w => f w - a i) z = 0) :
    meromorphicOrderAt (fun w => cubicP a (f w)) z = 0 := by
  have hmer : ∀ i, MeromorphicAt (fun w => f w - a i) z :=
    fun i => hf.sub (MeromorphicAt.const _ _)
  have hfun : (fun w => cubicP a (f w)) =
      ((fun w => f w - a 0) * (fun w => f w - a 1)) * (fun w => f w - a 2) := by
    ext w; simp [cubicP]
  rw [hfun, meromorphicOrderAt_mul ((hmer 0).mul (hmer 1)) (hmer 2),
    meromorphicOrderAt_mul (hmer 0) (hmer 1), h 0, h 1, h 2]
  simp

/-- **Lemma 3.8** (holomorphicity), for `U`: for a normalized pair, `U = (f - g) f'/P(f)` has
nonnegative and finite order at every point, i.e. it is holomorphic (after removing removable
singularities) and not identically zero near any point.  At a common pole this is
Lemma 3.7. -/
theorem NormalizedPair.order_auxU {Ω : Set ℂ} {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (h : NormalizedPair Ω f g a) {z : ℂ} (hz : z ∈ Ω) :
    0 ≤ meromorphicOrderAt (auxU a f g) z ∧ meromorphicOrderAt (auxU a f g) z ≠ ⊤ := by
  have hfm := h.nonconst_f.1 z hz
  have hgm := h.nonconst_g.1 z hz
  have hfg : MeromorphicAt (fun w => f w - g w) z := hfm.sub hgm
  have hPf : MeromorphicAt (fun w => cubicP a (f w)) z := by unfold cubicP; fun_prop
  have hU : auxU a f g = ((fun w => f w - g w) * deriv f) * (fun w => cubicP a (f w))⁻¹ := by
    ext w; simp [auxU, div_eq_mul_inv]
  have hd := h.distinct z hz
  obtain ⟨dd, hdd⟩ := WithTop.ne_top_iff_exists.1 hd
  have hD := order_deriv_of_nonconst h.nonconst_f hz
  obtain ⟨e, he⟩ := WithTop.ne_top_iff_exists.1 hD.1
  by_cases hpole : 0 < mult f ⊤ z
  · -- common pole of order `k`
    have hpole' : 0 < mult g ⊤ z := by rw [← h.cm_top z hz]; exact hpole
    set k := mult f ⊤ z with hk
    have hof := order_eq_neg_mult_top hpole
    have hog := order_eq_neg_mult_top hpole'
    rw [← h.cm_top z hz] at hog
    have hkpos : (0 : ℤ) < k := by exact_mod_cast hpole
    -- orders of the three factors
    have h1 : ((-k : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (fun w => f w - g w) z := by
      have : (fun w => f w - g w) = f + fun w => -g w := by ext w; simp [sub_eq_add_neg]
      rw [this]
      refine le_trans ?_ (meromorphicOrderAt_add hfm hgm.neg)
      rw [order_neg_eq, hof, hog, min_self]
    have h2 : meromorphicOrderAt (deriv f) z = ((-k - 1 : ℤ) : WithTop ℤ) := by
      have : meromorphicOrderAt (fun w => f w - 0) z = ((-k : ℤ) : WithTop ℤ) := by
        rw [show (fun w => f w - 0) = f by ext; simp]; exact hof
      exact order_deriv_of_order_eq hfm (by omega) this
    have h3 := order_cubicP_comp_of_neg hfm a (by omega : -(k : ℤ) < 0) hof
    rw [hU, meromorphicOrderAt_mul (hfg.mul hfm.deriv) hPf.inv,
      meromorphicOrderAt_mul hfg hfm.deriv, meromorphicOrderAt_inv, h2, h3, ← hdd]
    rw [← hdd] at h1
    have h1' : -(k : ℤ) ≤ dd := by exact_mod_cast h1
    rw [← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add, ← WithTop.coe_add]
    exact ⟨by exact_mod_cast (by omega : (0 : ℤ) ≤ dd + (-k - 1) + -(3 * -k)),
      WithTop.coe_ne_top⟩
  · by_cases hshared : ∃ j, 0 < mult f (a j : Sphere) z
    · obtain ⟨j, hj⟩ := hshared
      have hj' : 0 < mult g (a j : Sphere) z := (h.im j z hz).1 hj
      have hm := order_sub_eq_mult hj
      have hn := order_sub_eq_mult hj'
      -- `f - g` vanishes at `z`
      have hd1 : (1 : ℤ) ≤ dd := by
        have hmin : min (meromorphicOrderAt (fun w => f w - a j) z)
            (meromorphicOrderAt (fun w => -(g w - a j)) z) ≤
            meromorphicOrderAt (fun w => f w - g w) z := by
          have : (fun w => f w - g w) =
              (fun w => f w - a j) + fun w => -(g w - a j) := by ext w; simp
          rw [this]
          exact meromorphicOrderAt_add (hfm.sub (MeromorphicAt.const _ _))
            (hgm.sub (MeromorphicAt.const _ _)).neg
        rw [order_neg_eq (fun w => g w - a j), hm, hn, ← hdd] at hmin
        have h1 : (1 : ℤ) ≤ (mult f (a j : Sphere) z : ℤ) := by exact_mod_cast hj
        have h2 : (1 : ℤ) ≤ (mult g (a j : Sphere) z : ℤ) := by exact_mod_cast hj'
        rcases le_total (mult f (a j : Sphere) z) (mult g (a j : Sphere) z) with hle | hle
        · rw [min_eq_left (by exact_mod_cast hle)] at hmin
          have : ((mult f (a j : Sphere) z : ℕ) : ℤ) ≤ dd := by exact_mod_cast hmin
          omega
        · rw [min_eq_right (by exact_mod_cast hle)] at hmin
          have : ((mult g (a j : Sphere) z : ℕ) : ℤ) ≤ dd := by exact_mod_cast hmin
          omega
      have := (order_aux_at_shared hfm hgm h.injective hj hj' hm hn hdd.symm).1
      rw [this]
      exact ⟨by exact_mod_cast (by omega : (0 : ℤ) ≤ dd - 1), WithTop.coe_ne_top⟩
    · push_neg at hshared
      have hpole0 : mult f ⊤ z = 0 := by omega
      have hfnn := order_nonneg_of_mult_top_eq_zero hpole0 (order_ne_top_of_nonconst
        h.nonconst_f hz)
      have hgnn := order_nonneg_of_mult_top_eq_zero (by rw [← h.cm_top z hz]; exact hpole0)
        (order_ne_top_of_nonconst h.nonconst_g hz)
      have hzero : ∀ i, meromorphicOrderAt (fun w => f w - a i) z = 0 := by
        intro i
        exact le_antisymm (order_sub_nonpos_of_mult_eq_zero (by have := hshared i; omega)
          (h.nonconst_f.2 z hz (a i))) (order_sub_const_nonneg hfm hfnn (a i))
      have h3 := order_cubicP_comp_eq_zero hfm a hzero
      have h1 : 0 ≤ meromorphicOrderAt (fun w => f w - g w) z := by
        have : (fun w => f w - g w) = f + fun w => -g w := by ext w; simp [sub_eq_add_neg]
        rw [this]
        refine le_trans ?_ (meromorphicOrderAt_add hfm hgm.neg)
        rw [order_neg_eq]
        exact le_min hfnn hgnn
      have h2 := hD.2 hfnn
      rw [hU, meromorphicOrderAt_mul (hfg.mul hfm.deriv) hPf.inv,
        meromorphicOrderAt_mul hfg hfm.deriv, meromorphicOrderAt_inv, h3, ← hdd, ← he]
      rw [← hdd] at h1
      rw [← he] at h2
      have h1' : (0 : ℤ) ≤ dd := by exact_mod_cast h1
      have h2' : (0 : ℤ) ≤ e := by exact_mod_cast h2
      simp only [neg_zero, add_zero, ← WithTop.coe_add]
      exact ⟨by exact_mod_cast (by omega : (0 : ℤ) ≤ dd + e), WithTop.coe_ne_top⟩

/-- Swapping the members of a normalized pair. -/
lemma NormalizedPair.symm {Ω : Set ℂ} {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (h : NormalizedPair Ω f g a) : NormalizedPair Ω g f a where
  nonconst_f := h.nonconst_g
  nonconst_g := h.nonconst_f
  distinct z hz := by
    have := h.distinct z hz
    rw [← order_neg_eq, show (fun w => -(g w - f w)) = fun w => f w - g w by ext; ring]
    exact this
  injective := h.injective
  im j z hz := (h.im j z hz).symm
  cm_top z hz := (h.cm_top z hz).symm

/-- **Lemma 3.8** (holomorphicity): for a normalized pair, `U`, `V` and `Ψ` have nonnegative
and finite order at every point of the domain. -/
theorem NormalizedPair.order_aux {Ω : Set ℂ} {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (h : NormalizedPair Ω f g a) {z : ℂ} (hz : z ∈ Ω) :
    (0 ≤ meromorphicOrderAt (auxU a f g) z ∧ meromorphicOrderAt (auxU a f g) z ≠ ⊤) ∧
    (0 ≤ meromorphicOrderAt (auxV a f g) z ∧ meromorphicOrderAt (auxV a f g) z ≠ ⊤) ∧
    (0 ≤ meromorphicOrderAt (auxPsi a f g) z ∧ meromorphicOrderAt (auxPsi a f g) z ≠ ⊤) := by
  have hU := h.order_auxU hz
  have hV' := h.symm.order_auxU hz
  have hVeq : auxV a f g = fun w => -auxU a g f w := by
    ext w; simp only [auxV, auxU]; ring
  have hV : 0 ≤ meromorphicOrderAt (auxV a f g) z ∧ meromorphicOrderAt (auxV a f g) z ≠ ⊤ := by
    rw [hVeq, order_neg_eq]; exact hV'
  refine ⟨hU, hV, ?_⟩
  have hfm := h.nonconst_f.1 z hz
  have hgm := h.nonconst_g.1 z hz
  have hUm : MeromorphicAt (auxU a f g) z := by
    unfold auxU cubicP; fun_prop
  have hVm : MeromorphicAt (auxV a f g) z := by
    unfold auxV cubicP; fun_prop
  have : auxPsi a f g = auxU a f g * auxV a f g := rfl
  rw [this, meromorphicOrderAt_mul hUm hVm]
  obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.1 hU.2
  obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.1 hV.2
  have hu0 : (0 : ℤ) ≤ u := by have := hU.1; rw [← hu] at this; exact_mod_cast this
  have hv0 : (0 : ℤ) ≤ v := by have := hV.1; rw [← hv] at this; exact_mod_cast this
  rw [← hu, ← hv, ← WithTop.coe_add]
  exact ⟨by exact_mod_cast (by omega : (0 : ℤ) ≤ u + v), WithTop.coe_ne_top⟩

end ThreeIM

namespace ThreeIM

/-- At a common `c`-point, `ord (f - g) ≥ min(m, n)`. -/
lemma min_mult_le_order_sub {f g : ℂ → ℂ} {z c : ℂ} (hfm : MeromorphicAt f z)
    (hgm : MeromorphicAt g z) (hj : 0 < mult f (c : Sphere) z) (hj' : 0 < mult g (c : Sphere) z) :
    (((min (mult f (c : Sphere) z) (mult g (c : Sphere) z) : ℕ) : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt (fun w => f w - g w) z := by
  have hmin : min (meromorphicOrderAt (fun w => f w - c) z)
      (meromorphicOrderAt (fun w => -(g w - c)) z) ≤
      meromorphicOrderAt (fun w => f w - g w) z := by
    have : (fun w => f w - g w) = (fun w => f w - c) + fun w => -(g w - c) := by ext w; simp
    rw [this]
    exact meromorphicOrderAt_add (hfm.sub (MeromorphicAt.const _ _))
      (hgm.sub (MeromorphicAt.const _ _)).neg
  rw [order_neg_eq (fun w => g w - c), order_sub_eq_mult hj, order_sub_eq_mult hj'] at hmin
  refine le_trans ?_ hmin
  rcases le_total (mult f (c : Sphere) z) (mult g (c : Sphere) z) with hle | hle
  · rw [min_eq_left hle, min_eq_left (by exact_mod_cast hle)]
  · rw [min_eq_right hle, min_eq_right (by exact_mod_cast hle)]

/-- **Lemma 3.8** (last assertion, finite part): for a normalized pair, at a finite shared point
where `Ψ` does not vanish, one of the two multiplicities equals one. -/
theorem NormalizedPair.min_mult_eq_one_of_psi {Ω : Set ℂ} {f g : ℂ → ℂ} {a : Fin 3 → ℂ}
    (h : NormalizedPair Ω f g a) {z : ℂ} (hz : z ∈ Ω) {j : Fin 3}
    (hj : 0 < mult f (a j : Sphere) z) (hpsi : meromorphicOrderAt (auxPsi a f g) z = 0) :
    min (mult f (a j : Sphere) z) (mult g (a j : Sphere) z) = 1 := by
  have hfm := h.nonconst_f.1 z hz
  have hgm := h.nonconst_g.1 z hz
  have hj' : 0 < mult g (a j : Sphere) z := (h.im j z hz).1 hj
  obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.1 (h.distinct z hz)
  have h3 := (order_aux_at_shared hfm hgm h.injective hj hj' (order_sub_eq_mult hj)
    (order_sub_eq_mult hj') hd.symm).2.2
  rw [hpsi] at h3
  have hd1 : d = 1 := by
    have : (0 : ℤ) = 2 * d - 2 := by exact_mod_cast h3
    omega
  have hle := min_mult_le_order_sub hfm hgm hj hj'
  rw [← hd, hd1] at hle
  have : ((min (mult f (a j : Sphere) z) (mult g (a j : Sphere) z) : ℕ) : ℤ) ≤ 1 := by
    exact_mod_cast hle
  have h1 : 1 ≤ min (mult f (a j : Sphere) z) (mult g (a j : Sphere) z) := le_min hj hj'
  omega

end ThreeIM
