import Mathlib

/-!
# Paper I, Lemma 7.5 (`lem:weakfloor`, weak fields): the scalar part of the proof

Paper I is arXiv:2610.34122. In the proof of `lem:weakfloor`, `v = c + f` with `c` constant and
`∫_Q f = 0`, `t := S_*² ‖b‖₃²`, `V := |b|²`, and the analytic inputs are

* the cross term containing `c` vanishes, the other is `≥ -2√t ‖∇f‖²`,
* `∫ V |f|² ≤ t ‖∇f‖²`,
* `|c + f|² ≥ (1-η)|c|² - (η⁻¹-1)|f|²` (pointwise),
* `|c|² ‖b‖₂² ≥ μ̂_b - t ‖∇f‖²` (Neumann gap, Hölder and `S_* ≥ 1/π`).

From these the proof concludes
`∫ |(∇+ib)v|² ≥ (1-η) μ̂_b + (1 - 2√t - t/η + ηt) ‖∇f‖²` and, for `t ≤ η/8`,
that the bracket is `≥ 1 - 2/√8 - 1/8 > 0`.

This file proves the pointwise inequality (for complex numbers), the algebraic combination and
the bound on the bracket. The analytic inputs (Hölder, Sobolev, Neumann gap) are hypotheses.
-/

open Real

namespace PauliFierzUV.PaperI

/-- The pointwise inequality `|c + f|² ≥ (1-η)|c|² - (η⁻¹-1)|f|²` for `0 < η ≤ 1`. -/
theorem norm_add_sq_ge {c f : ℂ} {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    (1 - η) * ‖c‖ ^ 2 - (η⁻¹ - 1) * ‖f‖ ^ 2 ≤ ‖c + f‖ ^ 2 := by
  -- `‖c+f‖ ≥ ‖c‖ - ‖f‖`, and `(x-y)² ≥ (1-η)x² - (η⁻¹-1)y²`
  have htri : ‖c‖ - ‖f‖ ≤ ‖c + f‖ := by
    have := norm_sub_norm_le c (-f); simpa using this
  set x := ‖c‖
  set y := ‖f‖
  have hx : 0 ≤ x := norm_nonneg _
  have hy : 0 ≤ y := norm_nonneg _
  have key : (1 - η) * x ^ 2 - (η⁻¹ - 1) * y ^ 2 ≤ (x - y) ^ 2 := by
    have h : 0 ≤ (η * x - y) ^ 2 / η := by positivity
    have e : (x - y) ^ 2 - ((1 - η) * x ^ 2 - (η⁻¹ - 1) * y ^ 2) = (η * x - y) ^ 2 / η := by
      field_simp; ring
    linarith
  by_cases hxy : y ≤ x
  · have : (x - y) ^ 2 ≤ ‖c + f‖ ^ 2 := pow_le_pow_left₀ (by linarith) htri 2
    linarith
  · -- if `x < y`, the left side is `≤ 0`
    push Not at hxy
    have h1 : (1 - η) * x ^ 2 ≤ (η⁻¹ - 1) * y ^ 2 := by
      have hη' : 1 - η ≤ η⁻¹ - 1 := by
        have : 1 ≤ η⁻¹ := one_le_inv_iff₀.2 ⟨hη, hη1⟩
        nlinarith [mul_inv_cancel₀ hη.ne']
      have hx2 : x ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hx hxy.le 2
      have h0 : 0 ≤ 1 - η := by linarith
      nlinarith
    nlinarith [sq_nonneg ‖c + f‖]

/-- The combination step of `lem:weakfloor`: with `G = ‖∇f‖²`, `P = ∫ V|c+f|²`,
`Vf = ∫ V|f|²`, `Cb = |c|²‖b‖₂²` and `Kin` the left side,
`Kin ≥ (1-η) μ̂ + (1 - 2√t - t/η + ηt) G`. -/
theorem weakfloor_combination {Kin G P Vf Cb μhat t η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hKin : G + P - 2 * √t * G ≤ Kin)
    (hP : (1 - η) * Cb - (η⁻¹ - 1) * Vf ≤ P)
    (hVf : Vf ≤ t * G)
    (hCb : μhat - t * G ≤ Cb) :
    (1 - η) * μhat + (1 - 2 * √t - t / η + η * t) * G ≤ Kin := by
  have h1 : 0 ≤ 1 - η := by linarith
  have h2 : 0 ≤ η⁻¹ - 1 := by
    have : 1 ≤ η⁻¹ := one_le_inv_iff₀.2 ⟨hη, hη1⟩
    linarith
  have a1 : (1 - η) * (μhat - t * G) ≤ (1 - η) * Cb := mul_le_mul_of_nonneg_left hCb h1
  have a2 : (η⁻¹ - 1) * Vf ≤ (η⁻¹ - 1) * (t * G) := mul_le_mul_of_nonneg_left hVf h2
  have e : (1 - η) * μhat + (1 - 2 * √t - t / η + η * t) * G
      = G - 2 * √t * G + ((1 - η) * (μhat - t * G) - (η⁻¹ - 1) * (t * G)) := by
    field_simp; ring
  rw [e]
  linarith

/-- The bracket of `lem:weakfloor`: for `0 ≤ t ≤ η/8` and `0 < η ≤ 1`,
`1 - 2√t - t/η + ηt ≥ 1 - 2/√8 - 1/8 > 0`. -/
theorem weakfloor_bracket {t η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (ht : 0 ≤ t) (htη : t ≤ η / 8) :
    1 - 2 / √8 - 1 / 8 ≤ 1 - 2 * √t - t / η + η * t ∧ 0 < 1 - 2 / √8 - 1 / 8 := by
  have h8 : 0 < √8 := by positivity
  have hs8 : √8 ^ 2 = 8 := Real.sq_sqrt (by norm_num)
  have hst : √t ≤ 1 / √8 := by
    rw [Real.sqrt_le_left (by positivity), div_pow, hs8]
    linarith
  have htη' : t / η ≤ 1 / 8 := by rw [div_le_iff₀ hη]; linarith
  constructor
  · have : 2 * √t ≤ 2 / √8 := by
      have := mul_le_mul_of_nonneg_left hst (show (0 : ℝ) ≤ 2 by norm_num)
      rw [mul_one_div] at this
      exact this
    nlinarith [mul_nonneg hη.le ht]
  · have : 2 / √8 < 7 / 8 := by
      rw [div_lt_iff₀ h8]
      nlinarith [Real.sqrt_nonneg 8]
    linarith

/-- Conclusion of `lem:weakfloor` from the inputs: `Kin ≥ (1-η) μ̂_b` when `t ≤ η/8`. -/
theorem weakfloor_conclusion {Kin G P Vf Cb μhat t η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hG : 0 ≤ G) (ht : 0 ≤ t) (htη : t ≤ η / 8)
    (hKin : G + P - 2 * √t * G ≤ Kin)
    (hP : (1 - η) * Cb - (η⁻¹ - 1) * Vf ≤ P)
    (hVf : Vf ≤ t * G)
    (hCb : μhat - t * G ≤ Cb) :
    (1 - η) * μhat ≤ Kin := by
  have h := weakfloor_combination hη hη1 hKin hP hVf hCb
  obtain ⟨hb1, hb2⟩ := weakfloor_bracket hη hη1 ht htη
  have : 0 ≤ (1 - 2 * √t - t / η + η * t) * G := mul_nonneg (by linarith) hG
  linarith

end PauliFierzUV.PaperI
