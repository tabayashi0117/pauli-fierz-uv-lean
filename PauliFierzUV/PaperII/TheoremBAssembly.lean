import PauliFierzUV.PaperII.MassRenormalization

/-!
# Paper II, Section 10: the final step of the proof of Theorem B (Theorem 2.5, `thm:main`)

Paper II is arXiv:2610.34125. In the proof of Theorem 2.5 (Section 10.3),
Lemma 6.2 (`lem:consumer`) and Proposition 10.2 (`prop:expect`) give, for every `0 < κ < 1`, constants
`C_κ > 0` and `λ₁(κ)` with

  `c / h(λ) ≤ C_κ ℓ^(κ-1) (log λ)²`  for `λ ≥ λ₁(κ)`,

where `c = λ/π` and `ℓ = (λ/(π ā))^(1/7)`. The paper then puts `κ := min(7ε/2, 1/2)` and
concludes `h(λ) ≥ λ^(8/7-ε)` for large `λ`, hence `h(λ)/λ → ∞` and `ι_PF > 0`.

This file proves exactly that last step: **assuming** the displayed bound (the hypothesis
`CurvatureBound`), it derives the three conclusions. It does not prove the hypothesis, which is
the analytic content of Part II of Paper II (Sections 6–11). The result is therefore of the form
"hypothesis ⇒ conclusion".
-/

open Real Filter Topology

namespace PauliFierzUV.PaperII

/-- The input of the last step: for every `0 < κ < 1` there are `C_κ > 0` and `λ₁(κ)` with
`(λ/π)/h(λ) ≤ C_κ ℓ^(κ-1) (log λ)²` for `λ ≥ λ₁`, `ℓ = (λ/(π ā))^(1/7)`. -/
def CurvatureBound (h : ℝ → ℝ) (abar : ℝ) : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 1 → ∃ C l1 : ℝ, 0 < C ∧ ∀ l : ℝ, l1 ≤ l →
    (l / π) / h l ≤ C * ((l / (π * abar)) ^ (1 / 7 : ℝ)) ^ (κ - 1) * Real.log l ^ 2

/-- `(log λ)² ≤ A λ^(ε/2)` for large `λ`. -/
lemma eventually_log_sq_le {A ε : ℝ} (hA : 0 < A) (hε : 0 < ε) :
    ∀ᶠ l : ℝ in atTop, Real.log l ^ 2 ≤ A * l ^ (ε / 2) := by
  have h1 := (isLittleO_log_rpow_atTop (show 0 < ε / 4 by positivity)).pow (n := 2) (by norm_num)
  filter_upwards [h1.def hA, eventually_ge_atTop (1 : ℝ)] with l hl hl1
  have hl0 : 0 ≤ l := by linarith
  have e : (l ^ (ε / 4)) ^ 2 = l ^ (ε / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hl0]; norm_num; ring_nf
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), e] at hl
  exact hl

/-- **Theorem B, final step** (Paper II, proof of `thm:main`): from `CurvatureBound`,
`h(λ) ≥ λ^(8/7-ε)` for all large `λ`. -/
theorem growth_of_curvatureBound {h : ℝ → ℝ} {abar : ℝ} (habar : 0 < abar)
    (hpos : ∀ l, 0 < l → 0 < h l) (hb : CurvatureBound h abar) {ε : ℝ} (hε : 0 < ε) :
    ∃ lε : ℝ, ∀ l : ℝ, lε ≤ l → l ^ (8 / 7 - ε) ≤ h l := by
  set κ : ℝ := min (7 * ε / 2) (1 / 2) with hκ
  have hκ0 : 0 < κ := lt_min (by positivity) (by norm_num)
  have hκ1 : κ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hκε : κ / 7 ≤ ε / 2 := by
    have : κ ≤ 7 * ε / 2 := min_le_left _ _
    linarith
  obtain ⟨C, l1, hC, hbound⟩ := hb κ hκ0 hκ1
  have hpa : 0 < π * abar := by positivity
  set A : ℝ := (π * abar) ^ ((κ - 1) / 7) / (π * C) with hA
  have hA0 : 0 < A := by positivity
  obtain ⟨l2, hl2⟩ := eventually_atTop.1 (eventually_log_sq_le hA0 hε)
  refine ⟨max (max l1 l2) 2, fun l hl => ?_⟩
  have hl1 : l1 ≤ l := (le_max_left _ _).trans ((le_max_left _ _).trans hl)
  have hl2' : l2 ≤ l := (le_max_right _ _).trans ((le_max_left _ _).trans hl)
  have hlge : 2 ≤ l := (le_max_right _ _).trans hl
  have hl0 : 0 < l := by linarith
  have hlog : 0 < Real.log l := Real.log_pos (by linarith)
  have hL : 0 < Real.log l ^ 2 := by positivity
  have hh := hpos l hl0
  -- Step 1: `h ≥ A λ^(8/7-κ/7) / (log λ)²`
  set B : ℝ := C * ((l / (π * abar)) ^ (1 / 7 : ℝ)) ^ (κ - 1) * Real.log l ^ 2 with hB
  have hB0 : 0 < B := by positivity
  have step1 : (l / π) / B ≤ h l := by
    have := hbound l hl1
    rw [div_le_iff₀ hh] at this
    rw [div_le_iff₀ hB0]
    linarith
  have epow : ((l / (π * abar)) ^ (1 / 7 : ℝ)) ^ (κ - 1)
      = l ^ ((κ - 1) / 7) / (π * abar) ^ ((κ - 1) / 7) := by
    rw [← Real.rpow_mul (by positivity), Real.div_rpow hl0.le hpa.le]
    congr 2 <;> ring
  have esplit : l ^ (8 / 7 - κ / 7) * l ^ ((κ - 1) / 7) = l := by
    rw [← Real.rpow_add hl0]
    have : 8 / 7 - κ / 7 + (κ - 1) / 7 = 1 := by ring
    rw [this, Real.rpow_one]
  have hlk : 0 < l ^ ((κ - 1) / 7) := by positivity
  have hpak : 0 < (π * abar) ^ ((κ - 1) / 7) := by positivity
  have e1 : (l / π) / B = A * l ^ (8 / 7 - κ / 7) / Real.log l ^ 2 := by
    rw [hB, epow, hA]
    nth_rewrite 1 [← esplit]
    field_simp
  rw [e1] at step1
  -- Step 2: `λ^(8/7-ε) λ^(ε/2) ≤ λ^(8/7-κ/7)`
  have step2 : l ^ (8 / 7 - ε) * l ^ (ε / 2) ≤ l ^ (8 / 7 - κ / 7) := by
    rw [← Real.rpow_add hl0]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  -- Step 3: `(log λ)² ≤ A λ^(ε/2)`
  have step3 := hl2 l hl2'
  have hp : 0 < l ^ (8 / 7 - ε) := by positivity
  calc l ^ (8 / 7 - ε) = l ^ (8 / 7 - ε) * Real.log l ^ 2 / Real.log l ^ 2 := by
        field_simp
    _ ≤ l ^ (8 / 7 - ε) * (A * l ^ (ε / 2)) / Real.log l ^ 2 := by
        gcongr
    _ = A * (l ^ (8 / 7 - ε) * l ^ (ε / 2)) / Real.log l ^ 2 := by ring
    _ ≤ A * l ^ (8 / 7 - κ / 7) / Real.log l ^ 2 := by gcongr
    _ ≤ h l := step1

/-- From `CurvatureBound`: `h(λ)/λ → ∞` (Theorem B, first assertion). -/
theorem tendsto_ratio_of_curvatureBound {h : ℝ → ℝ} {abar : ℝ} (habar : 0 < abar)
    (hpos : ∀ l, 0 < l → 0 < h l) (hb : CurvatureBound h abar) :
    Tendsto (fun l => h l / l) atTop atTop := by
  obtain ⟨l0, hl0⟩ := growth_of_curvatureBound habar hpos hb (ε := 1 / 14) (by norm_num)
  refine tendsto_atTop_mono' atTop ?_ (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 14 by norm_num))
  filter_upwards [eventually_ge_atTop l0, eventually_gt_atTop (0 : ℝ)] with l hl hlpos
  have h1 := hl0 l hl
  rw [le_div_iff₀ hlpos]
  have : l ^ (1 / 14 : ℝ) * l = l ^ (8 / 7 - 1 / 14 : ℝ) := by
    rw [← Real.rpow_add_one hlpos.ne']
    norm_num
  linarith

/-- From `CurvatureBound` and `h ≥ 1`: `ι_PF = inf_{λ>0} h(λ)/λ > 0` (Theorem B, "in
particular"). -/
theorem iota_pos_of_curvatureBound {h : ℝ → ℝ} {abar : ℝ} (habar : 0 < abar)
    (hh : ∀ l, 0 < l → 1 ≤ h l) (hb : CurvatureBound h abar) : 0 < iota h :=
  iota_pos_of_tendsto hh (tendsto_ratio_of_curvatureBound habar
    (fun l hl => lt_of_lt_of_le one_pos (hh l hl)) hb)

end PauliFierzUV.PaperII
