module

public import RequestProject.ThreeIM.TangentConst

/-!
# Classification of the tangent system (Lemma 7.13)

Reduction of Lemma 7.13 to the main step `tanScalar_const`:

* the system has no poles (`tangent_local_no_pole`, via the simple zeros of `c`);
* `H = X / D` is entire (`amplitude_quotient_entire`, Lemma 7.7);
* `H` is constant (`tanScalar_const`), so `c H (H - 1) = 0` and `H ∈ {0, 1}`;
* integration of `D' = c H + b`.
-/

@[expose] public section

open Filter Set Topology

namespace ThreeIM

lemma order_eq_zero_of_analyticAt {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (h0 : f z ≠ 0) :
    meromorphicOrderAt f z = 0 := by
  rw [hf.meromorphicOrderAt_eq, (hf.analyticOrderAt_eq_zero).2 h0]
  rfl

/-- The order of an analytic function at a zero is a positive integer (or `⊤`). -/
lemma order_pos_of_analyticAt {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (h0 : f z = 0)
    {n : ℤ} (hn : meromorphicOrderAt f z = n) : 1 ≤ n := by
  rw [hf.meromorphicOrderAt_eq] at hn
  have hne : analyticOrderAt f z ≠ 0 := fun h => ((hf.analyticOrderAt_eq_zero).1 h) h0
  induction h : analyticOrderAt f z using ENat.recTopCoe with
  | top => rw [h] at hn; simp at hn
  | coe m =>
    rw [h] at hn hne
    simp only [ENat.map_coe] at hn
    have hm : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm; exact absurd rfl hne
      · exact hm
    have : ((m : ℤ) : WithTop ℤ) = (n : WithTop ℤ) := hn
    have := WithTop.coe_injective this
    omega

lemma deriv_tanC_eq (α β : ℂ) : deriv (tanC α β) = tanC' α β :=
  funext fun z => (hasDerivAt_tanC α β z).deriv

/-- `c` has order at most one at every point (its zeros are simple). -/
lemma tanC_order_le_one {α β : ℂ} (hα : α ≠ 0) (z : ℂ) :
    meromorphicOrderAt (tanC α β) z ≤ 1 := by
  have ha : AnalyticAt ℂ (tanC α β) z := (differentiable_tanC α β).analyticAt z
  by_cases h0 : tanC α β z = 0
  · have hc' := tanC'_ne_zero_of_tanC_eq_zero hα h0
    have hne : meromorphicOrderAt (tanC α β) z ≠ ⊤ := by
      intro htop
      have h1 : ∀ᶠ w in 𝓝[≠] z, tanC α β w = 0 := meromorphicOrderAt_eq_top_iff.1 htop
      have h2 : tanC α β =ᶠ[𝓝 z] fun _ => 0 := by
        rw [eventually_nhdsWithin_iff] at h1
        filter_upwards [h1] with w hw
        by_cases hwz : w = z
        · rw [hwz]; exact h0
        · exact hw hwz
      have := h2.deriv_eq
      rw [deriv_tanC_eq, deriv_const] at this
      exact hc' this
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hne
    have hn1 := order_pos_of_analyticAt ha h0 hn.symm
    have hd := order_deriv_of_order_eq (a := 0) ha.meromorphicAt (n := n) (by omega)
      (by simpa using hn.symm)
    rw [deriv_tanC_eq] at hd
    have hc'a : AnalyticAt ℂ (tanC' α β) z := by
      have : tanC' α β = deriv (tanC α β) := (deriv_tanC_eq α β).symm
      rw [this]; exact ha.deriv
    rw [order_eq_zero_of_analyticAt hc'a hc'] at hd
    have : ((0 : ℤ) : WithTop ℤ) = ((n - 1 : ℤ) : WithTop ℤ) := hd
    have := WithTop.coe_injective this
    rw [← hn]
    exact_mod_cast (by omega : n ≤ 1)
  · rw [order_eq_zero_of_analyticAt ha h0]
    exact_mod_cast (by norm_num : (0 : ℤ) ≤ 1)

lemma int_of_order_ne_top {f : ℂ → ℂ} {z : ℂ} (h : meromorphicOrderAt f z ≠ ⊤) :
    ∃ n : ℤ, meromorphicOrderAt f z = n := by
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 h
  exact ⟨n, hn.symm⟩

/-- **Lemma 7.13, first step** (local form).  Let `a, b` be analytic at `z₀` with `a(z₀) ≠ 0` and
`ord_{z₀}(a - b) ≤ 1`.  If `X, Y` are meromorphic at `z₀` with `D = X - Y` of finite order and
`D X' = a X`, `D Y' = b Y` near `z₀`, then `X` has no pole at `z₀`. -/
lemma tangent_local_no_pole {X Y a b : ℂ → ℂ} {z₀ : ℂ} (hX : MeromorphicAt X z₀)
    (hY : MeromorphicAt Y z₀) (ha : AnalyticAt ℂ a z₀) (ha0 : a z₀ ≠ 0) (hb : AnalyticAt ℂ b z₀)
    (hc : meromorphicOrderAt (fun z => a z - b z) z₀ ≤ 1)
    (hD : meromorphicOrderAt (fun z => X z - Y z) z₀ ≠ ⊤)
    (hXeq : ∀ᶠ z in 𝓝[≠] z₀, (X z - Y z) * deriv X z = a z * X z)
    (hYeq : ∀ᶠ z in 𝓝[≠] z₀, (X z - Y z) * deriv Y z = b z * Y z) :
    0 ≤ meromorphicOrderAt X z₀ := by
  by_contra hneg
  push_neg at hneg
  obtain ⟨n, hn⟩ := int_of_order_ne_top (ne_top_of_lt hneg)
  have hn0 : n < 0 := by
    rw [hn] at hneg; exact_mod_cast hneg
  set D : ℂ → ℂ := fun z => X z - Y z with hDdef
  have hDm : MeromorphicAt D z₀ := hX.sub hY
  obtain ⟨d, hd⟩ := int_of_order_ne_top hD
  have hX' : meromorphicOrderAt (deriv X) z₀ = ((n - 1 : ℤ) : WithTop ℤ) :=
    order_deriv_of_order_eq (a := 0) hX (ne_of_lt hn0) (by simpa using hn)
  have ha_ord : meromorphicOrderAt a z₀ = 0 := order_eq_zero_of_analyticAt ha ha0
  -- `ord D = 1`
  have h1 : meromorphicOrderAt (D * deriv X) z₀ = meromorphicOrderAt (a * X) z₀ :=
    meromorphicOrderAt_congr (hXeq.mono fun z hz => by simpa [hDdef] using hz)
  rw [meromorphicOrderAt_mul hDm hX.deriv, meromorphicOrderAt_mul ha.meromorphicAt hX, hd, hX',
    ha_ord, hn] at h1
  have hd1 : d = 1 := by
    have h2 : ((d + (n - 1) : ℤ) : WithTop ℤ) = ((0 + n : ℤ) : WithTop ℤ) := by
      push_cast; exact h1
    have := WithTop.coe_injective h2
    omega
  subst hd1
  -- `ord Y = n`
  have hYord : meromorphicOrderAt Y z₀ = n := by
    have hYe : Y = X + -D := by ext z; simp [hDdef]
    have hnegD : meromorphicOrderAt (-D) z₀ = meromorphicOrderAt D z₀ := order_neg_eq D z₀
    rw [hYe, meromorphicOrderAt_add_eq_left_of_lt hDm.neg, hn]
    rw [hnegD, hd, hn]
    exact_mod_cast (by omega : n < 1)
  -- the quotient `u = D / Y`
  set u : ℂ → ℂ := fun z => D z / Y z with hudef
  have hum : MeromorphicAt u z₀ := hDm.div hY
  have huord : meromorphicOrderAt u z₀ = ((1 - n : ℤ) : WithTop ℤ) := by
    have : u = D * Y⁻¹ := by ext z; simp [hudef, div_eq_mul_inv]
    rw [this, meromorphicOrderAt_mul hDm hY.inv, meromorphicOrderAt_inv, hd, hYord]
    push_cast; rfl
  have hu' : meromorphicOrderAt (deriv u) z₀ = ((1 - n - 1 : ℤ) : WithTop ℤ) :=
    order_deriv_of_order_eq (a := 0) hum (by omega) (by simpa using huord)
  -- the key identity `c X Y = D Y² u'` near `z₀`
  have hXne : ∀ᶠ z in 𝓝[≠] z₀, X z ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hX).1 (by rw [hn]; simp)
  have hYne : ∀ᶠ z in 𝓝[≠] z₀, Y z ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hY).1 (by rw [hYord]; simp)
  have hkey : (fun z => a z - b z) * X * Y =ᶠ[𝓝[≠] z₀] D * (Y * Y) * deriv u := by
    filter_upwards [hXeq, hYeq, hX.eventually_analyticAt, hY.eventually_analyticAt, hYne]
      with z hxe hye hxa hya hyz
    have hdD : deriv D z = deriv X z - deriv Y z :=
      deriv_sub hxa.differentiableAt hya.differentiableAt
    have hdu : deriv u z = (deriv D z * Y z - D z * deriv Y z) / Y z ^ 2 :=
      deriv_div (hxa.differentiableAt.sub hya.differentiableAt) hya.differentiableAt hyz
    simp only [Pi.mul_apply]
    rw [hdu, hdD]
    field_simp
    simp only [hDdef] at hxe hye ⊢
    linear_combination (-(Y z)) * hxe + (X z) * hye
  have hord := meromorphicOrderAt_congr hkey
  have hcm : MeromorphicAt (fun z => a z - b z) z₀ := (ha.sub hb).meromorphicAt
  rw [meromorphicOrderAt_mul (hcm.mul hX) hY, meromorphicOrderAt_mul hcm hX,
    meromorphicOrderAt_mul (hDm.mul (hY.mul hY)) hum.deriv, meromorphicOrderAt_mul hDm (hY.mul hY),
    meromorphicOrderAt_mul hY hY, hn, hYord, hd, hu'] at hord
  obtain ⟨e, he⟩ : ∃ e : ℤ, meromorphicOrderAt (fun z => a z - b z) z₀ = e := by
    apply int_of_order_ne_top
    intro htop
    rw [htop] at hord
    simp at hord
    exact WithTop.coe_ne_top hord.symm
  rw [he] at hord hc
  have h3 : ((e + n + n : ℤ) : WithTop ℤ) = ((1 + (n + n) + (1 - n - 1) : ℤ) : WithTop ℤ) := by
    push_cast; exact hord
  have := WithTop.coe_injective h3
  have hc' : e ≤ 1 := by exact_mod_cast hc
  omega

/-- An entire function that does not vanish identically has finite order everywhere. -/
lemma entire_order_ne_top {D : ℂ → ℂ} (hD : Differentiable ℂ D) (hD0 : ∃ z, D z ≠ 0) (z : ℂ) :
    meromorphicOrderAt D z ≠ ⊤ := by
  obtain ⟨z₁, hz₁⟩ := hD0
  have h1 : meromorphicOrderAt D z₁ ≠ ⊤ := by
    rw [order_eq_zero_of_analyticAt (hD.analyticAt z₁) hz₁]; simp
  exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
    (fun w _ => (hD.analyticAt w).meromorphicAt) isPreconnected_univ (mem_univ z₁) (mem_univ z) h1

/-- An entire representative of a meromorphic function without poles. -/
lemma exists_entire_rep {X : ℂ → ℂ} (hX : Meromorphic X)
    (hnn : ∀ z, 0 ≤ meromorphicOrderAt X z) :
    ∃ X' : ℂ → ℂ, Differentiable ℂ X' ∧ ∀ x, X' =ᶠ[𝓝[≠] x] X := by
  have hmo : MeromorphicOn X univ := fun z _ => hX z
  refine ⟨toMeromorphicNFOn X univ, fun x => ?_, fun x =>
    hmo.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ x)⟩
  apply AnalyticAt.differentiableAt
  apply (meromorphicNFOn_toMeromorphicNFOn X univ (mem_univ x)).meromorphicOrderAt_nonneg_iff_analyticAt.1
  rw [meromorphicOrderAt_congr (hmo.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ x))]
  exact hnn x

/-- **Lemma 7.7** (elimination for the amplitude system), divisibility part: if `X, D, a` are
entire, `a` is zero-free, `D ≢ 0` and `D X' = a X`, then every zero of `D` is a simple zero and
a zero of `X`, so `H = X / D` extends to an entire function. -/
lemma amplitude_quotient_entire {X D a : ℂ → ℂ} (hX : Differentiable ℂ X)
    (hD : Differentiable ℂ D) (ha : Differentiable ℂ a) (ha0 : ∀ z, a z ≠ 0)
    (hD0 : ∃ z, D z ≠ 0) (heq : ∀ z, D z * deriv X z = a z * X z) :
    ∃ H : ℂ → ℂ, Differentiable ℂ H ∧ ∀ z, X z = D z * H z := by
  have hDne := entire_order_ne_top hD hD0
  set Q : ℂ → ℂ := fun w => X w / D w with hQdef
  have hQe : Q = X * D⁻¹ := by ext w; simp [hQdef, div_eq_mul_inv]
  have hQm : Meromorphic Q := fun z =>
    ((hX.analyticAt z).meromorphicAt).div (hD.analyticAt z).meromorphicAt
  have hnn : ∀ z, 0 ≤ meromorphicOrderAt Q z := by
    intro z
    have hXa := hX.analyticAt z
    have hDa := hD.analyticAt z
    obtain ⟨d, hd⟩ := int_of_order_ne_top (hDne z)
    rw [hQe, meromorphicOrderAt_mul hXa.meromorphicAt hDa.meromorphicAt.inv,
      meromorphicOrderAt_inv, hd]
    by_cases hXt : meromorphicOrderAt X z = ⊤
    · rw [hXt]; simp
    obtain ⟨p, hp⟩ := int_of_order_ne_top hXt
    rw [hp]
    by_cases hDz : D z = 0
    · have hXz : X z = 0 := by
        have := heq z
        rw [hDz, zero_mul] at this
        exact (mul_eq_zero.1 this.symm).resolve_left (ha0 z)
      have hp1 := order_pos_of_analyticAt hXa hXz hp
      have hX' : meromorphicOrderAt (deriv X) z = ((p - 1 : ℤ) : WithTop ℤ) :=
        order_deriv_of_order_eq (a := 0) hXa.meromorphicAt (by omega) (by simpa using hp)
      have h1 : meromorphicOrderAt (D * deriv X) z = meromorphicOrderAt (a * X) z := by
        congr 1; ext w; exact heq w
      rw [meromorphicOrderAt_mul hDa.meromorphicAt hXa.meromorphicAt.deriv,
        meromorphicOrderAt_mul (ha.analyticAt z).meromorphicAt hXa.meromorphicAt, hd, hX',
        order_eq_zero_of_analyticAt (ha.analyticAt z) (ha0 z), hp] at h1
      have h2 : ((d + (p - 1) : ℤ) : WithTop ℤ) = ((0 + p : ℤ) : WithTop ℤ) := by
        push_cast; exact h1
      have := WithTop.coe_injective h2
      exact_mod_cast (by omega : (0 : ℤ) ≤ p + -d)
    · have hd0 : d = 0 := by
        have := order_eq_zero_of_analyticAt hDa hDz
        rw [hd] at this
        exact_mod_cast this
      have hp0 : 0 ≤ p := by
        have := hXa.meromorphicOrderAt_nonneg
        rw [hp] at this; exact_mod_cast this
      exact_mod_cast (by omega : (0 : ℤ) ≤ p + -d)
  obtain ⟨H, hH, hHQ⟩ := exists_entire_rep hQm hnn
  refine ⟨H, hH, fun z => ?_⟩
  have hDev : ∀ᶠ w in 𝓝[≠] z, D w ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hD.analyticAt z).meromorphicAt).1 (hDne z)
  have hcont : ContinuousAt (fun w => X w - D w * H w) z :=
    (hX.continuous.sub (hD.continuous.mul hH.continuous)).continuousAt
  have := eq_zero_of_nhdsNE hcont (by
    filter_upwards [hDev, hHQ z] with w hw hHw
    rw [hHw, hQdef]
    field_simp
    ring)
  exact sub_eq_zero.1 this

/-- **Lemma 7.13** (classification of the tangent system).  Let `X, Y` be meromorphic on `ℂ`
with `(X - Y) X' = α e^{z/2} X` and `(X - Y) Y' = β e^{-z/2} Y`, `αβ ≠ 0`.  Apart from
`(0, 0)`, the solutions are `(2α e^{z/2} + C, 0)` and `(0, 2β e^{-z/2} + C)`, `C ∈ ℂ`.
(All identities are identities of meromorphic functions, imposed off a discrete set.) -/
theorem tangent_classification {X Y : ℂ → ℂ} (hX : Meromorphic X) (hY : Meromorphic Y)
    {α β : ℂ} (hα : α ≠ 0) (hβ : β ≠ 0)
    (hXeq : ∀ᶠ z in codiscrete ℂ,
      (X z - Y z) * deriv X z = α * Complex.exp (z / 2) * X z)
    (hYeq : ∀ᶠ z in codiscrete ℂ,
      (X z - Y z) * deriv Y z = β * Complex.exp (-z / 2) * Y z) :
    (∀ᶠ z in codiscrete ℂ, X z = 0 ∧ Y z = 0) ∨
    (∃ C : ℂ, ∀ᶠ z in codiscrete ℂ, X z = 2 * α * Complex.exp (z / 2) + C ∧ Y z = 0) ∨
    (∃ C : ℂ, ∀ᶠ z in codiscrete ℂ, X z = 0 ∧ Y z = 2 * β * Complex.exp (-z / 2) + C) := by
  have hXL : ∀ x, ∀ᶠ z in 𝓝[≠] x, (X z - Y z) * deriv X z = tanA α z * X z := fun x => by
    filter_upwards [codiscrete_iff_nhdsNE.1 hXeq x] with z hz
    rw [hz, tanA]
  have hYL : ∀ x, ∀ᶠ z in 𝓝[≠] x, (X z - Y z) * deriv Y z = tanB β z * Y z := fun x => by
    filter_upwards [codiscrete_iff_nhdsNE.1 hYeq x] with z hz
    rw [hz, tanB]
  set D : ℂ → ℂ := fun z => X z - Y z with hDdef
  have hDm : Meromorphic D := fun z => (hX z).sub (hY z)
  by_cases hDtop : ∃ z₀, meromorphicOrderAt D z₀ = ⊤
  · -- `D ≡ 0` forces `X = Y = 0`
    left
    obtain ⟨z₀, hz₀⟩ := hDtop
    have hall : ∀ x, meromorphicOrderAt D x = ⊤ := by
      intro x
      by_contra hx
      exact (MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected (fun w _ => hDm w)
        isPreconnected_univ (mem_univ x) (mem_univ z₀) hx) hz₀
    rw [codiscrete_iff_nhdsNE]
    intro x
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 (hall x), hXL x, hYL x] with z hD hx hy
    simp only [hDdef] at hD
    rw [hD, zero_mul] at hx hy
    exact ⟨(mul_eq_zero.1 hx.symm).resolve_left (tanA_ne_zero hα z),
      (mul_eq_zero.1 hy.symm).resolve_left (tanB_ne_zero hβ z)⟩
  push_neg at hDtop
  -- no poles
  have hXnn : ∀ z, 0 ≤ meromorphicOrderAt X z := fun z =>
    tangent_local_no_pole (hX z) (hY z) ((differentiable_tanA α).analyticAt z)
      (tanA_ne_zero hα z) ((differentiable_tanB β).analyticAt z) (tanC_order_le_one hα z)
      (hDtop z) (hXL z) (hYL z)
  have hYnn : ∀ z, 0 ≤ meromorphicOrderAt Y z := by
    intro z
    refine tangent_local_no_pole (X := Y) (Y := X) (a := fun w => -tanB β w)
      (b := fun w => -tanA α w) (hY z) (hX z) ((differentiable_tanB β).analyticAt z).neg
      (neg_ne_zero.2 (tanB_ne_zero hβ z)) ((differentiable_tanA α).analyticAt z).neg ?_ ?_ ?_ ?_
    · have : (fun w => -tanB β w - -tanA α w) = tanC α β := by ext w; simp [tanC]; ring
      rw [this]; exact tanC_order_le_one hα z
    · have : (fun w => Y w - X w) = fun w => -(D w) := by ext w; simp [hDdef]
      rw [this, order_neg_eq]; exact hDtop z
    · filter_upwards [hYL z] with w hw; linear_combination -hw
    · filter_upwards [hXL z] with w hw; linear_combination -hw
  -- entire representatives
  obtain ⟨X₁, hX₁, hX₁X⟩ := exists_entire_rep hX hXnn
  obtain ⟨Y₁, hY₁, hY₁Y⟩ := exists_entire_rep hY hYnn
  have hX₁d : Differentiable ℂ (deriv X₁) := fun z => ((hX₁.analyticAt z).deriv).differentiableAt
  have hY₁d : Differentiable ℂ (deriv Y₁) := fun z => ((hY₁.analyticAt z).deriv).differentiableAt
  have hEX : ∀ z, (X₁ z - Y₁ z) * deriv X₁ z = tanA α z * X₁ z := by
    intro z
    have hcont : ContinuousAt (fun w => (X₁ w - Y₁ w) * deriv X₁ w - tanA α w * X₁ w) z :=
      (((hX₁.continuous.sub hY₁.continuous).mul hX₁d.continuous).sub
        ((differentiable_tanA α).continuous.mul hX₁.continuous)).continuousAt
    have := eq_zero_of_nhdsNE hcont (by
      filter_upwards [eventually_nhds_of_nhdsNE (hX₁X z), eventually_nhds_of_nhdsNE (hY₁Y z),
        hXL z] with w hxw hyw hw
      rw [hxw.self_of_nhds, hyw.self_of_nhds, Filter.EventuallyEq.deriv_eq hxw, hw, sub_self])
    exact sub_eq_zero.1 this
  have hEY : ∀ z, (X₁ z - Y₁ z) * deriv Y₁ z = tanB β z * Y₁ z := by
    intro z
    have hcont : ContinuousAt (fun w => (X₁ w - Y₁ w) * deriv Y₁ w - tanB β w * Y₁ w) z :=
      (((hX₁.continuous.sub hY₁.continuous).mul hY₁d.continuous).sub
        ((differentiable_tanB β).continuous.mul hY₁.continuous)).continuousAt
    have := eq_zero_of_nhdsNE hcont (by
      filter_upwards [eventually_nhds_of_nhdsNE (hX₁X z), eventually_nhds_of_nhdsNE (hY₁Y z),
        hYL z] with w hxw hyw hw
      rw [hxw.self_of_nhds, hyw.self_of_nhds, Filter.EventuallyEq.deriv_eq hyw, hw, sub_self])
    exact sub_eq_zero.1 this
  set D₁ : ℂ → ℂ := fun z => X₁ z - Y₁ z with hD₁def
  have hD₁ : Differentiable ℂ D₁ := hX₁.sub hY₁
  have hD₁0 : ∃ z, D₁ z ≠ 0 := by
    by_contra h
    push_neg at h
    apply hDtop 0
    rw [meromorphicOrderAt_eq_top_iff]
    filter_upwards [hX₁X 0, hY₁Y 0] with w h1 h2
    simp only [hDdef]
    rw [← h1, ← h2]
    exact h w
  obtain ⟨H, hH, hXH⟩ := amplitude_quotient_entire hX₁ hD₁ (differentiable_tanA α)
    (tanA_ne_zero hα) hD₁0 hEX
  have hYH : ∀ z, Y₁ z = D₁ z * (H z - 1) := fun z => by
    rw [mul_sub, ← hXH]; simp [hD₁def]
  have hfunX : (fun w => D₁ w * H w) = X₁ := funext fun w => (hXH w).symm
  have hfunY : (fun w => D₁ w * (H w - 1)) = Y₁ := funext fun w => (hYH w).symm
  obtain ⟨hA1, hA2, hA3⟩ := amplitude_elimination isOpen_univ (a := tanA α) (b := tanB β)
    (D := D₁) (H := H) (differentiable_tanA α).differentiableOn
    (differentiable_tanB β).differentiableOn hD₁.differentiableOn hH.differentiableOn
    (fun z _ => ((meromorphicOrderAt_ne_top_iff_eventually_ne_zero
      (hD₁.analyticAt z).meromorphicAt).1 (entire_order_ne_top hD₁ hD₁0 z)).frequently)
    (fun z _ => by rw [hfunX, ← hXH z]; exact hEX z)
    (fun z _ => by rw [hfunY, ← hYH z]; exact hEY z)
  have hscalar : TanScalar α β H := by
    intro z
    have h := hA3 z (mem_univ z)
    have hdc : deriv (fun w => tanA α w - tanB β w) z = tanC' α β z :=
      (hasDerivAt_tanC α β z).deriv
    rw [hdc] at h
    simp only [tanC]
    linear_combination h
  have hHc := tanScalar_const hα hβ hH hscalar
  set h₀ := H 0 with hh₀
  have hderH : ∀ z, deriv H z = 0 := by
    have : H = fun _ => h₀ := funext hHc
    intro z; rw [this, deriv_const]
  have hc0 : ∃ z, tanC α β z ≠ 0 := by
    by_contra hc
    push_neg at hc
    have h1 := tanC_order_le_one (β := β) hα 0
    rw [meromorphicOrderAt_eq_top_iff.2 (Eventually.of_forall hc)] at h1
    exact absurd h1 (by simp)
  obtain ⟨z₁, hz₁⟩ := hc0
  have hh : h₀ * (h₀ - 1) = 0 := by
    have := hA2 z₁ (mem_univ z₁)
    rw [hderH, mul_zero, hHc z₁] at this
    have : tanC α β z₁ * (h₀ * (h₀ - 1)) = 0 := by
      simp only [tanC]; linear_combination this
    exact (mul_eq_zero.1 this).resolve_left hz₁
  rcases mul_eq_zero.1 hh with h0 | h1
  · -- `H = 0`: `X = 0` and `D' = b`
    right; right
    set K : ℂ → ℂ := fun z => D₁ z + 2 * tanB β z with hKdef
    have hK : ∀ z, HasDerivAt K 0 z := by
      intro z
      have h1 : HasDerivAt D₁ (tanB β z) z := by
        have := (hD₁ z).hasDerivAt
        rwa [hA1 z (mem_univ z), hHc z, h0, mul_zero, zero_add] at this
      have := h1.add ((hasDerivAt_tanB β z).const_mul 2)
      convert this using 1; ring
    have hKc : ∀ z, K z = K 0 := fun z =>
      is_const_of_deriv_eq_zero (fun w => (hK w).differentiableAt) (fun w => (hK w).deriv) z 0
    refine ⟨-K 0, codiscrete_iff_nhdsNE.2 fun x => ?_⟩
    filter_upwards [hX₁X x, hY₁Y x] with z h1 h2
    have hKz := hKc z
    simp only [hKdef, tanB] at hKz
    refine ⟨?_, ?_⟩
    · rw [← h1, hXH z, hHc z, h0, mul_zero]
    · rw [← h2, hYH z, hHc z, h0]
      simp only [hKdef, tanB]
      linear_combination -hKz
  · -- `H = 1`: `Y = 0` and `D' = a`
    right; left
    have h₀1 : h₀ = 1 := sub_eq_zero.1 h1
    set K : ℂ → ℂ := fun z => D₁ z - 2 * tanA α z with hKdef
    have hK : ∀ z, HasDerivAt K 0 z := by
      intro z
      have h1 : HasDerivAt D₁ (tanA α z) z := by
        have := (hD₁ z).hasDerivAt
        rwa [hA1 z (mem_univ z), hHc z, h₀1, mul_one, sub_add_cancel] at this
      have := h1.sub ((hasDerivAt_tanA α z).const_mul 2)
      convert this using 1; ring
    have hKc : ∀ z, K z = K 0 := fun z =>
      is_const_of_deriv_eq_zero (fun w => (hK w).differentiableAt) (fun w => (hK w).deriv) z 0
    refine ⟨K 0, codiscrete_iff_nhdsNE.2 fun x => ?_⟩
    filter_upwards [hX₁X x, hY₁Y x] with z h1 h2
    have hKz := hKc z
    simp only [hKdef, tanA] at hKz
    refine ⟨?_, ?_⟩
    · rw [← h1, hXH z, hHc z, h₀1, mul_one]
      simp only [hKdef, tanA]
      linear_combination hKz
    · rw [← h2, hYH z, hHc z, h₀1, sub_self, mul_zero]

end ThreeIM
