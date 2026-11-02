import Mathlib

/-!
# Paper I, Lemma 6.5 (`lem:hardy`): Hardy inequality in field space

Paper I is arXiv:2610.34122. A real analysis lemma on `ℝ^d`: a ground state substitution with an
integration by parts.
Done here: the inequality with the regularisation `ε > 0`, for real `ψ ∈ C¹_c`, including the
pointwise bound `div V - |V|² ≥ g_S²/(4‖G_S‖(u+ε))` for the paper's choice `t = g_S/(2‖G_S‖)`;
and the elementary monotonicity step of Corollary 6.7 (`cor:hardy`) (b).
NOT done: the extension to the form domain (density of `C_c^∞`), `ε ↓ 0`, complex `ψ`.

`S` is the span of `e i`; `Gn` is any upper bound for `‖G_S‖`, in the form
`∑ i, ⟪r (e i), y⟫ ^ 2 ≤ Gn * ‖y‖ ^ 2`.
-/

open MeasureTheory Real
open scoped InnerProductSpace

namespace PauliFierzUV.PaperI

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {μ : Measure E} [μ.IsAddHaarMeasure]

lemma contDiff_fderiv_apply {f : E → ℝ} (hf : ContDiff ℝ 1 f) (v : E) :
    Continuous fun x => fderiv ℝ f x v :=
  (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const

lemma hcs_sq {ψ : E → ℝ} (hc : HasCompactSupport ψ) : HasCompactSupport (fun x => ψ x ^ 2) := by
  have : (fun x => ψ x ^ 2) = fun x => ψ x * ψ x := by funext x; ring
  rw [this]
  exact hc.mul_left

/-- Integration by parts. -/
lemma ibp {V ψ : E → ℝ} (hV : ContDiff ℝ 1 V) (hψ : ContDiff ℝ 1 ψ)
    (hc : HasCompactSupport ψ) (v : E) :
    ∫ x, 2 * V x * ψ x * fderiv ℝ ψ x v ∂μ = - ∫ x, fderiv ℝ V x v * ψ x ^ 2 ∂μ := by
  have hg : ContDiff ℝ 1 (fun x => ψ x ^ 2) := hψ.pow 2
  have hcg := hcs_sq hc
  have hdg : ∀ x, fderiv ℝ (fun x => ψ x ^ 2) x v = 2 * ψ x * fderiv ℝ ψ x v := by
    intro x
    have hd : HasFDerivAt ψ (fderiv ℝ ψ x) x := (hψ.differentiable (by norm_num) x).hasFDerivAt
    have := (hd.pow 2).fderiv
    rw [this]
    simp
  have hcdg : HasCompactSupport (fun x => fderiv ℝ (fun x => ψ x ^ 2) x v) :=
    HasCompactSupport.comp_left (g := fun L : E →L[ℝ] ℝ => L v) (hcg.fderiv (𝕜 := ℝ)) (by simp)
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := μ) (f := V)
    (g := fun x => ψ x ^ 2) (v := v)
    (((contDiff_fderiv_apply hV v).mul hg.continuous).integrable_of_hasCompactSupport hcg.mul_left)
    ((hV.continuous.mul (contDiff_fderiv_apply hg v)).integrable_of_hasCompactSupport
      hcdg.mul_left)
    ((hV.continuous.mul hg.continuous).integrable_of_hasCompactSupport hcg.mul_left)
    (fun x _ => hV.differentiable (by norm_num) x)
    (fun x _ => hg.differentiable (by norm_num) x)
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [hdg]
  ring

/-- The vector field `V = t Y* r / (|r|² + ε)`, one component. -/
noncomputable def fieldV (r : E →L[ℝ] F) (a : F) (t ε : ℝ) (q : E) : ℝ :=
  t * ⟪a, r q⟫_ℝ * (‖r q‖ ^ 2 + ε)⁻¹

lemma contDiff_fieldV (r : E →L[ℝ] F) (a : F) (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ 1 (fieldV r a t ε) := by
  have hD : ContDiff ℝ 1 (fun q => ‖r q‖ ^ 2 + ε) :=
    (r.contDiff.norm_sq ℝ).add contDiff_const
  have hne : ∀ q, ‖r q‖ ^ 2 + ε ≠ 0 := fun q => by positivity
  exact (contDiff_const.mul (contDiff_const.inner ℝ r.contDiff)).mul (hD.inv hne)

lemma fderiv_fieldV (r : E →L[ℝ] F) (a : F) (t : ℝ) {ε : ℝ} (hε : 0 < ε) (q v : E) :
    fderiv ℝ (fieldV r a t ε) q v
      = t * ⟪a, r v⟫_ℝ / (‖r q‖ ^ 2 + ε)
        - 2 * t * ⟪a, r q⟫_ℝ * ⟪r q, r v⟫_ℝ / (‖r q‖ ^ 2 + ε) ^ 2 := by
  have hne : ‖r q‖ ^ 2 + ε ≠ 0 := by positivity
  have hw : HasFDerivAt (fun q => ⟪a, r q⟫_ℝ) ((innerSL ℝ a).comp r) q :=
    ((innerSL ℝ a).comp r).hasFDerivAt
  have hD : HasFDerivAt (fun q => ‖r q‖ ^ 2 + ε)
      ((2 : ℕ) • (innerSL ℝ (r q)).comp r) q :=
    (r.hasFDerivAt.norm_sq).add_const ε
  have hDi := (hasDerivAt_inv hne).comp_hasFDerivAt q hD
  have h := (hw.const_mul t).mul hDi
  have hF : HasFDerivAt (fieldV r a t ε) _ q := h
  rw [hF.fderiv]
  simp
  field_simp
  ring

/-- The pointwise bound `div V - |V|² ≥ g²/(4 Gn (u + ε))`. -/
lemma pointwise {n : ℕ} (e : Fin n → E) (r : E →L[ℝ] F) {Gn ε : ℝ} (hGn : 0 < Gn) (hε : 0 < ε)
    (hG : ∀ y : F, ∑ i, ⟪r (e i), y⟫_ℝ ^ 2 ≤ Gn * ‖y‖ ^ 2)
    {g : ℝ} (hg0 : 0 < g) (hg : g = ∑ i, ‖r (e i)‖ ^ 2 - 2 * Gn) (q : E) :
    g ^ 2 / (4 * Gn * (‖r q‖ ^ 2 + ε))
      ≤ ∑ i, (fderiv ℝ (fieldV r (r (e i)) (g / (2 * Gn)) ε) q (e i)
          - fieldV r (r (e i)) (g / (2 * Gn)) ε q ^ 2) := by
  set t : ℝ := g / (2 * Gn) with ht
  have ht0 : 0 < t := by positivity
  set u : ℝ := ‖r q‖ ^ 2 with hu
  have hu0 : 0 ≤ u := by positivity
  set D : ℝ := u + ε with hD
  have hD0 : 0 < D := by positivity
  set S : ℝ := ∑ i, ⟪r (e i), r q⟫_ℝ ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => by positivity
  have hSb : S ≤ Gn * D := by
    have := hG (r q)
    have h2 : Gn * u ≤ Gn * D := mul_le_mul_of_nonneg_left (by rw [hD]; linarith) hGn.le
    calc S ≤ Gn * u := this
      _ ≤ Gn * D := h2
  have term : ∀ i, fderiv ℝ (fieldV r (r (e i)) t ε) q (e i) - fieldV r (r (e i)) t ε q ^ 2
      = t * ‖r (e i)‖ ^ 2 / D - (2 * t + t ^ 2) * ⟪r (e i), r q⟫_ℝ ^ 2 / D ^ 2 := by
    intro i
    have hcomm : ⟪r q, r (e i)⟫_ℝ = ⟪r (e i), r q⟫_ℝ := real_inner_comm _ _
    rw [fderiv_fieldV r _ t hε, real_inner_self_eq_norm_sq, hcomm]
    simp only [fieldV]
    rw [← hu, ← hD]
    field_simp
    ring
  simp only [term]
  rw [Finset.sum_sub_distrib]
  have e1 : ∑ i, t * ‖r (e i)‖ ^ 2 / D = t * (g + 2 * Gn) / D := by
    rw [← Finset.sum_div, ← Finset.mul_sum]
    congr 2
    linarith
  have e2 : ∑ i, (2 * t + t ^ 2) * ⟪r (e i), r q⟫_ℝ ^ 2 / D ^ 2 = (2 * t + t ^ 2) * S / D ^ 2 := by
    rw [← Finset.sum_div, ← Finset.mul_sum]
  rw [e1, e2]
  have hb : (2 * t + t ^ 2) * S / D ^ 2 ≤ (2 * t + t ^ 2) * Gn / D := by
    rw [div_le_div_iff₀ (by positivity) hD0]
    have : (2 * t + t ^ 2) * S * D ≤ (2 * t + t ^ 2) * (Gn * D) * D := by
      apply mul_le_mul_of_nonneg_right _ hD0.le
      exact mul_le_mul_of_nonneg_left hSb (by positivity)
    nlinarith
  have hk : g ^ 2 / (4 * Gn * D) = t * (g + 2 * Gn) / D - (2 * t + t ^ 2) * Gn / D := by
    rw [ht]
    field_simp
    ring
  rw [hk]
  linarith

/-- **Hardy inequality in field space**, regularised, for real `ψ ∈ C¹_c(E)`. -/
theorem hardy_field {n : ℕ} (e : Fin n → E) (r : E →L[ℝ] F) {Gn ε : ℝ} (hGn : 0 < Gn) (hε : 0 < ε)
    (hG : ∀ y : F, ∑ i, ⟪r (e i), y⟫_ℝ ^ 2 ≤ Gn * ‖y‖ ^ 2)
    {g : ℝ} (hg0 : 0 < g) (hg : g = ∑ i, ‖r (e i)‖ ^ 2 - 2 * Gn)
    {ψ : E → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    ∫ q, g ^ 2 / (4 * Gn * (‖r q‖ ^ 2 + ε)) * ψ q ^ 2 ∂μ
      ≤ ∑ i, ∫ q, fderiv ℝ ψ q (e i) ^ 2 ∂μ := by
  set t : ℝ := g / (2 * Gn) with ht
  have hψ2 := hcs_sq hc
  let V : Fin n → E → ℝ := fun i => fieldV r (r (e i)) t ε
  have hV : ∀ i, ContDiff ℝ 1 (V i) := fun i => contDiff_fieldV r _ t hε
  have hdψ : ∀ i, Continuous fun q => fderiv ℝ ψ q (e i) := fun i => contDiff_fderiv_apply hψ _
  have hcdψ : ∀ i, HasCompactSupport fun q => fderiv ℝ ψ q (e i) := fun i =>
    HasCompactSupport.comp_left (g := fun L : E →L[ℝ] ℝ => L (e i)) (hc.fderiv (𝕜 := ℝ)) (by simp)
  have cont_ψ := hψ.continuous
  have int1 : ∀ i, Integrable (fun q => fderiv ℝ ψ q (e i) ^ 2) μ := fun i =>
    ((hdψ i).pow 2).integrable_of_hasCompactSupport (hcs_sq (hcdψ i))
  have int2 : ∀ i, Integrable (fun q => 2 * V i q * ψ q * fderiv ℝ ψ q (e i)) μ := fun i =>
    (((continuous_const.mul (hV i).continuous).mul cont_ψ).mul (hdψ i)).integrable_of_hasCompactSupport
      (hcdψ i).mul_left
  have int3 : ∀ i, Integrable (fun q => V i q ^ 2 * ψ q ^ 2) μ := fun i =>
    (((hV i).continuous.pow 2).mul (cont_ψ.pow 2)).integrable_of_hasCompactSupport hψ2.mul_left
  have int4 : ∀ i, Integrable (fun q => fderiv ℝ (V i) q (e i) * ψ q ^ 2) μ := fun i =>
    ((contDiff_fderiv_apply (hV i) _).mul (cont_ψ.pow 2)).integrable_of_hasCompactSupport
      hψ2.mul_left
  -- one component: `∫ (div V - V²) ψ² ≤ ∫ (∂ψ)²`
  have comp : ∀ i, ∫ q, (fderiv ℝ (V i) q (e i) - V i q ^ 2) * ψ q ^ 2 ∂μ
      ≤ ∫ q, fderiv ℝ ψ q (e i) ^ 2 ∂μ := by
    intro i
    have h0 : 0 ≤ ∫ q, (fderiv ℝ ψ q (e i) + V i q * ψ q) ^ 2 ∂μ :=
      integral_nonneg fun q => by positivity
    have hexp : ∫ q, (fderiv ℝ ψ q (e i) + V i q * ψ q) ^ 2 ∂μ
        = ∫ q, fderiv ℝ ψ q (e i) ^ 2 ∂μ + ∫ q, 2 * V i q * ψ q * fderiv ℝ ψ q (e i) ∂μ
          + ∫ q, V i q ^ 2 * ψ q ^ 2 ∂μ := by
      have i12 : Integrable (fun q => fderiv ℝ ψ q (e i) ^ 2
          + 2 * V i q * ψ q * fderiv ℝ ψ q (e i)) μ := (int1 i).add (int2 i)
      have hcong : ∫ q, (fderiv ℝ ψ q (e i) + V i q * ψ q) ^ 2 ∂μ
          = ∫ q, (fderiv ℝ ψ q (e i) ^ 2 + 2 * V i q * ψ q * fderiv ℝ ψ q (e i))
            + V i q ^ 2 * ψ q ^ 2 ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
        simp only
        ring
      rw [hcong, integral_add i12 (int3 i), integral_add (int1 i) (int2 i)]
    have hsplit : ∫ q, (fderiv ℝ (V i) q (e i) - V i q ^ 2) * ψ q ^ 2 ∂μ
        = ∫ q, fderiv ℝ (V i) q (e i) * ψ q ^ 2 ∂μ - ∫ q, V i q ^ 2 * ψ q ^ 2 ∂μ := by
      rw [← integral_sub (int4 i) (int3 i)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
      simp only
      ring
    rw [hsplit]
    have hibp := ibp (μ := μ) (hV i) hψ hc (e i)
    linarith
  -- the pointwise bound
  have hDc : Continuous fun q => ‖r q‖ ^ 2 + ε := by fun_prop
  have hne : ∀ q, ‖r q‖ ^ 2 + ε ≠ 0 := fun q => by positivity
  have hsumint : ∀ i ∈ Finset.univ,
      Integrable (fun q => (fderiv ℝ (V i) q (e i) - V i q ^ 2) * ψ q ^ 2) μ := fun i _ => by
    have := (int4 i).sub (int3 i)
    refine this.congr (Filter.Eventually.of_forall fun q => ?_)
    simp only [Pi.sub_apply]
    ring
  have lhsint : Integrable (fun q => g ^ 2 / (4 * Gn * (‖r q‖ ^ 2 + ε)) * ψ q ^ 2) μ := by
    have hc1 : Continuous fun q => g ^ 2 / (4 * Gn * (‖r q‖ ^ 2 + ε)) :=
      continuous_const.div (continuous_const.mul hDc) fun q =>
        mul_ne_zero (by positivity) (hne q)
    exact (hc1.mul (cont_ψ.pow 2)).integrable_of_hasCompactSupport hψ2.mul_left
  calc ∫ q, g ^ 2 / (4 * Gn * (‖r q‖ ^ 2 + ε)) * ψ q ^ 2 ∂μ
      ≤ ∫ q, ∑ i, (fderiv ℝ (V i) q (e i) - V i q ^ 2) * ψ q ^ 2 ∂μ := by
        refine integral_mono lhsint (integrable_finsetSum _ hsumint) fun q => ?_
        simp only
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right (pointwise e r hGn hε hG hg0 hg q) (by positivity)
    _ = ∑ i, ∫ q, (fderiv ℝ (V i) q (e i) - V i q ^ 2) * ψ q ^ 2 ∂μ :=
        integral_finsetSum _ hsumint
    _ ≤ ∑ i, ∫ q, fderiv ℝ ψ q (e i) ^ 2 ∂μ := Finset.sum_le_sum fun i _ => comp i

/-- Corollary `cor:hardy` (b), last step: `x ↦ (T - 2x)²/x` is antitone on `(0, T/2]`. -/
theorem hardy_ratio_antitone {T : ℝ} :
    AntitoneOn (fun x : ℝ => (T - 2 * x) ^ 2 / x) (Set.Ioc 0 (T / 2)) := by
  intro x hx y hy hxy
  simp only
  have hx0 : 0 < x := hx.1
  have hy0 : 0 < y := hy.1
  have h1 : 0 ≤ T - 2 * y := by linarith [hy.2]
  have h2 : T - 2 * y ≤ T - 2 * x := by linarith
  rw [div_le_div_iff₀ hy0 hx0]
  have : (T - 2 * y) ^ 2 ≤ (T - 2 * x) ^ 2 := pow_le_pow_left₀ h1 h2 2
  nlinarith [sq_nonneg (T - 2 * y)]

/-- Corollary `cor:hardy` (b): if `‖G'‖ ≤ 1` and `T = tr G' ≥ 2`, then
`g'²/‖G'‖ ≥ (T - 2)²` with `g' = T - 2‖G'‖`. -/
theorem hardy_ratio_ge {T Gn : ℝ} (hG0 : 0 < Gn) (hG1 : Gn ≤ 1) (hT : 2 ≤ T) :
    (T - 2) ^ 2 ≤ (T - 2 * Gn) ^ 2 / Gn := by
  have h := hardy_ratio_antitone (T := T) ⟨hG0, by linarith⟩ ⟨one_pos, by linarith⟩ hG1
  simpa using h

end PauliFierzUV.PaperI
