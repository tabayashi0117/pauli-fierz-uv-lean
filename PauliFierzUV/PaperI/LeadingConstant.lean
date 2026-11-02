import PauliFierzUV.PaperI.MinimizerIntegrals
import PauliFierzUV.PaperI.ScaleMinimization

/-!
# Paper I, Appendix B (`app:constants`) and Section 3: the leading constant

Paper I is arXiv:2610.34122.

**Proposition B.1 (`prop:F1`) (b).** From the radial integrals of `MinimizerIntegrals`
(`∫ u r² = x³/3`, `∫ u² r² = 5x³/6`, `∫ |u'|² r² = x³/2`, where `tan x = x`) we derive

* `a = ½‖∇u‖²/‖u‖₂² = 3/10`, `b = ‖u‖₁/‖u‖₂ = (4π/3) √(3/(10π)) x^(3/2)`,
* `t_*^(7/2) = 3b/(4a) = ‖u‖₂`,
* `(7/3) a^(3/7) (¾ b)^(4/7) = (7/3)(3/10)^(3/7)(3π/10)^(2/7) x^(6/7)` (first expression for `F[1]`),
* `= (7/4)(2/3)^(3/7) C_N^(-3/7)` with `C_N = 5^(5/3) / (2^(2/3)·3x²(4π/3)^(2/3))` (second
  expression, from the sharp Nash inequality),
* and `min_{y>0} (y^(-4/3)/(2C_N) + y) = (7/4)(2/3)^(3/7) C_N^(-3/7)` (the Nash step).

Here `‖u‖₁ := 4π ∫₀^x u r² dr`, `‖u‖₂² := 4π ∫₀^x u² r² dr`, `‖∇u‖² := 4π ∫₀^x |u'|² r² dr`: the
passage to polar coordinates in `ℝ³`, the sign `u ≥ 0` (needed for `‖u‖₁ = ∫ u`), and the
minimality of `u` (which rests on the cited sharp Nash inequality) are **not** formalized.

**Equations `eq:calpha`, `eq:coeff`, `eq:params`, Remark 3.6 (`rem:window`), proof of Corollary 1.2.** Identities between the
physical and the working conventions: `F[1] β_*^(4/7) = c_α α^(2/7) Λ^(12/7) = (Λ/π) F_λ[β]`,
`F_λ[β] = c_F e² ℓ⁵`, the crossover ratio, and the expressions of `Ξ` and `ℓ` in `α, Λ`.
-/

open Real

namespace PauliFierzUV.PaperI

lemma log_four : log 4 = 2 * log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num

lemma log_six : log 6 = log 2 + log 3 := by
  rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num

lemma log_ten : log 10 = log 2 + log 5 := by
  rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num

/-! ### Proposition `prop:F1` (b) -/

/-- `‖u‖₁ = 4π ∫₀^x u r² dr`. -/
noncomputable def normL1 (x : ℝ) : ℝ := 4 * π * ∫ r in (0 : ℝ)..x, uProfile x r * r ^ 2

/-- `‖u‖₂² = 4π ∫₀^x u² r² dr`. -/
noncomputable def normL2sq (x : ℝ) : ℝ := 4 * π * ∫ r in (0 : ℝ)..x, uProfile x r ^ 2 * r ^ 2

/-- `‖∇u‖² = 4π ∫₀^x |u'|² r² dr`, with `r² |u'(r)|² = (cos r - sinc r)²/cos² x`. -/
noncomputable def gradSq (x : ℝ) : ℝ :=
  4 * π * ∫ r in (0 : ℝ)..x, (Real.cos r - Real.sinc r) ^ 2 / Real.cos x ^ 2

/-- The Nash constant `C_N` in terms of `x₁`. -/
noncomputable def nashConst (x : ℝ) : ℝ :=
  (5 : ℝ) ^ (5 / 3 : ℝ) / ((2 : ℝ) ^ (2 / 3 : ℝ) * 3 * x ^ 2 * (4 * π / 3) ^ (2 / 3 : ℝ))

section
variable {x : ℝ} (hx0 : 0 < x) (hx : Real.sin x = x * Real.cos x) (hc : Real.cos x ≠ 0)
include hx0 hx hc

theorem normL1_eq : normL1 x = 4 * π / 3 * x ^ 3 := by
  rw [normL1, integral_u hx hc]; ring

theorem normL2sq_eq : normL2sq x = 10 * π / 3 * x ^ 3 := by
  rw [normL2sq, integral_u_sq hx hc]; ring

theorem gradSq_eq : gradSq x = 2 * π * x ^ 3 := by
  rw [gradSq, integral_du_sq hx0 hx hc]; ring

/-- `a = ½ ‖∇u‖² / ‖u‖₂² = 3/10`. -/
theorem a_eq : (1 / 2) * gradSq x / normL2sq x = 3 / 10 := by
  rw [gradSq_eq hx0 hx hc, normL2sq_eq hx0 hx hc]
  have := Real.pi_pos
  field_simp

/-- `b = ‖u‖₁ / ‖u‖₂ = (4π/3) √(3/(10π)) x^(3/2)`. -/
theorem b_eq : normL1 x / √(normL2sq x) = 4 * π / 3 * √(3 / (10 * π)) * x ^ (3 / 2 : ℝ) := by
  rw [normL1_eq hx0 hx hc, normL2sq_eq hx0 hx hc]
  have hpi := Real.pi_pos
  apply Real.log_injOn_pos (Set.mem_Ioi.2 (by positivity)) (Set.mem_Ioi.2 (by positivity))
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow, Real.log_pow,
    Real.log_sqrt]
  push_cast
  ring

/-- `t_*^(7/2) = 3b/(4a) = ‖u‖₂`. -/
theorem tstar_eq :
    3 * (normL1 x / √(normL2sq x)) / (4 * ((1 / 2) * gradSq x / normL2sq x))
      = √(normL2sq x) := by
  rw [a_eq hx0 hx hc, b_eq hx0 hx hc, normL2sq_eq hx0 hx hc]
  have hpi := Real.pi_pos
  apply Real.log_injOn_pos (Set.mem_Ioi.2 (by positivity)) (Set.mem_Ioi.2 (by positivity))
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow, Real.log_pow,
    Real.log_sqrt, log_ten, log_four]
  push_cast
  ring

/-- The first expression for `F[1]` in `prop:F1` (b): the minimum
`(7/3) a^(3/7) (¾ b)^(4/7)` of `a t² + b t^(-3/2)` equals
`(7/3)(3/10)^(3/7)(3π/10)^(2/7) x^(6/7)`. -/
theorem F1_first_expression :
    7 / 3 * ((1 / 2) * gradSq x / normL2sq x) ^ (3 / 7 : ℝ)
        * (3 / 4 * (normL1 x / √(normL2sq x))) ^ (4 / 7 : ℝ)
      = 7 / 3 * (3 / 10 : ℝ) ^ (3 / 7 : ℝ) * (3 * π / 10) ^ (2 / 7 : ℝ) * x ^ (6 / 7 : ℝ) := by
  rw [a_eq hx0 hx hc, b_eq hx0 hx hc]
  have hpi := Real.pi_pos
  apply Real.log_injOn_pos (Set.mem_Ioi.2 (by positivity)) (Set.mem_Ioi.2 (by positivity))
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow, Real.log_pow,
    Real.log_sqrt, log_ten, log_four]
  push_cast
  ring

omit hx hc in
/-- The two expressions for `F[1]` in `prop:F1` (b) agree. -/
theorem F1_two_expressions :
    7 / 3 * (3 / 10 : ℝ) ^ (3 / 7 : ℝ) * (3 * π / 10) ^ (2 / 7 : ℝ) * x ^ (6 / 7 : ℝ)
      = 7 / 4 * (2 / 3 : ℝ) ^ (3 / 7 : ℝ) * nashConst x ^ (-(3 / 7) : ℝ) := by
  have hpi := Real.pi_pos
  unfold nashConst
  apply Real.log_injOn_pos (Set.mem_Ioi.2 (by positivity)) (Set.mem_Ioi.2 (by positivity))
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow, Real.log_pow,
    log_ten, log_four]
  push_cast
  ring

/-- The scale minimisation `F₁(u_t) = a t² + b t^(-3/2) ≥ (7/3) a^(3/7)(¾b)^(4/7)` with the
values of `a, b` above, for every `t > 0`. -/
theorem F1_scale_lower {t : ℝ} (ht : 0 < t) :
    7 / 3 * (3 / 10 : ℝ) ^ (3 / 7 : ℝ) * (3 * π / 10) ^ (2 / 7 : ℝ) * x ^ (6 / 7 : ℝ)
      ≤ (1 / 2) * gradSq x / normL2sq x * t ^ (2 : ℝ)
        + normL1 x / √(normL2sq x) * t ^ (-(3 / 2) : ℝ) := by
  have hpi := Real.pi_pos
  have ha : 0 < (1 / 2) * gradSq x / normL2sq x := by rw [a_eq hx0 hx hc]; norm_num
  have hb : 0 < normL1 x / √(normL2sq x) := by rw [b_eq hx0 hx hc]; positivity
  rw [← F1_first_expression hx0 hx hc]
  exact scale_lower ha hb ht

end

/-- **Nash step** (`prop:F1`, paragraph after it): for `C > 0` and `y > 0`,
`y^(-4/3)/(2C) + y ≥ (7/4)(2/3)^(3/7) C^(-3/7)`. -/
theorem nash_min_lower {C y : ℝ} (hC : 0 < C) (hy : 0 < y) :
    7 / 4 * (2 / 3 : ℝ) ^ (3 / 7 : ℝ) * C ^ (-(3 / 7) : ℝ) ≤ y ^ (-(4 / 3) : ℝ) / (2 * C) + y := by
  have hp1 : 0 ≤ (7 / 3) * (y ^ (-(4 / 3) : ℝ) / (2 * C)) := by positivity
  have hp2 : 0 ≤ (7 / 4) * y := by positivity
  have key := Real.geom_mean_le_arith_mean2_weighted (w₁ := 3 / 7) (w₂ := 4 / 7)
    (by norm_num) (by norm_num) hp1 hp2 (by norm_num)
  have e : ((7 / 3) * (y ^ (-(4 / 3) : ℝ) / (2 * C))) ^ (3 / 7 : ℝ) * ((7 / 4) * y) ^ (4 / 7 : ℝ)
      = 7 / 4 * (2 / 3 : ℝ) ^ (3 / 7 : ℝ) * C ^ (-(3 / 7) : ℝ) := by
    apply Real.log_injOn_pos (Set.mem_Ioi.2 (by positivity)) (Set.mem_Ioi.2 (by positivity))
    simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow, Real.log_pow,
      log_four]
    push_cast
    ring
  rw [e] at key
  linarith

/-- The Nash step is attained at `y = (2/(3C))^(3/7)`. -/
theorem nash_min_attained {C : ℝ} (hC : 0 < C) :
    ((2 / (3 * C)) ^ (3 / 7 : ℝ)) ^ (-(4 / 3) : ℝ) / (2 * C) + (2 / (3 * C)) ^ (3 / 7 : ℝ)
      = 7 / 4 * (2 / 3 : ℝ) ^ (3 / 7 : ℝ) * C ^ (-(3 / 7) : ℝ) := by
  set y := (2 / (3 * C)) ^ (3 / 7 : ℝ) with hy
  have hy0 : 0 < y := by positivity
  have h1 : y ^ (-(4 / 3) : ℝ) / (2 * C) = 3 / 4 * y := by
    apply Real.log_injOn_pos (Set.mem_Ioi.2 (by positivity)) (Set.mem_Ioi.2 (by positivity))
    rw [hy]
    simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow, Real.log_pow,
      log_four]
    push_cast
    ring
  rw [h1]
  have h2 : 7 / 4 * y = 7 / 4 * (2 / 3 : ℝ) ^ (3 / 7 : ℝ) * C ^ (-(3 / 7) : ℝ) := by
    apply Real.log_injOn_pos (Set.mem_Ioi.2 (by positivity)) (Set.mem_Ioi.2 (by positivity))
    rw [hy]
    simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow, Real.log_pow]
    push_cast
    ring
  linarith

/-! ### The leading coefficient: `eq:calpha`, `eq:coeff`, `eq:params`, `rem:window` -/

/-- `c_α = (6π²)^(-4/7) (4π)^(2/7) F[1]` (`eq:calpha`), as a function of the value `F[1]`. -/
noncomputable def cAlpha (F1 : ℝ) : ℝ := (6 * π ^ 2) ^ (-(4 / 7) : ℝ) * (4 * π) ^ (2 / 7 : ℝ) * F1

/-- `c_F = (π/6)^(4/7) F[1]` (`eq:coeff`). -/
noncomputable def cF (F1 : ℝ) : ℝ := (π / 6) ^ (4 / 7 : ℝ) * F1

section coeff
variable {F1 e Λ : ℝ} (hF : 0 < F1) (he : 0 < e) (hΛ : 0 < Λ)
include hF he hΛ

/-- `eq:coeff`, first equality: with `β_* = eΛ³/(6π²)` and `α = e²/(4π)`,
`F[1] β_*^(4/7) = c_α α^(2/7) Λ^(12/7)`. -/
theorem coeff_physical :
    F1 * (e * Λ ^ 3 / (6 * π ^ 2)) ^ (4 / 7 : ℝ)
      = cAlpha F1 * (e ^ 2 / (4 * π)) ^ (2 / 7 : ℝ) * Λ ^ (12 / 7 : ℝ) := by
  have hpi := Real.pi_pos
  unfold cAlpha
  apply Real.log_injOn_pos (Set.mem_Ioi.2 (by positivity)) (Set.mem_Ioi.2 (by positivity))
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow, Real.log_pow]
  push_cast
  ring

/-- `eq:coeff`, second equality: with `λ = Λ/π`, `β = (π/6) e √λ` and
`F_λ[β] = λ^(3/7) β^(4/7) F[1]`, one has `F[1] β_*^(4/7) = (Λ/π) F_λ[β]`. -/
theorem coeff_working :
    F1 * (e * Λ ^ 3 / (6 * π ^ 2)) ^ (4 / 7 : ℝ)
      = Λ / π * ((Λ / π) ^ (3 / 7 : ℝ) * (π / 6 * e * √(Λ / π)) ^ (4 / 7 : ℝ) * F1) := by
  have hpi := Real.pi_pos
  apply Real.log_injOn_pos (Set.mem_Ioi.2 (by positivity)) (Set.mem_Ioi.2 (by positivity))
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow, Real.log_pow,
    Real.log_sqrt, log_six]
  push_cast
  ring

/-- `eq:coeff`, last part: `F_λ[β] = c_F e² ℓ⁵` with `ℓ = (λ/e²)^(1/7)` (`eq:params`). -/
theorem coeff_cF :
    (Λ / π) ^ (3 / 7 : ℝ) * (π / 6 * e * √(Λ / π)) ^ (4 / 7 : ℝ) * F1
      = cF F1 * e ^ 2 * ((Λ / π / e ^ 2) ^ (1 / 7 : ℝ)) ^ 5 := by
  have hpi := Real.pi_pos
  unfold cF
  apply Real.log_injOn_pos (Set.mem_Ioi.2 (by positivity)) (Set.mem_Ioi.2 (by positivity))
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow, Real.log_pow,
    Real.log_sqrt]
  push_cast
  ring

end coeff

lemma working_functional_scaling_pos {lam β F1 : ℝ} (hl : 0 < lam) (hβ : 0 < β) (hF : 0 < F1) :
    lam * ((β / lam) ^ (4 / 7 : ℝ) * F1) = lam ^ (3 / 7 : ℝ) * β ^ (4 / 7 : ℝ) * F1 := by
  apply Real.log_injOn_pos (Set.mem_Ioi.2 (by positivity)) (Set.mem_Ioi.2 (by positivity))
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow]
  ring

/-- The scaling `F_λ[β] = λ F[β/λ] = λ^(3/7) β^(4/7) F[1]` (Section 3), given
`F[β'] = β'^(4/7) F[1]`. -/
theorem working_functional_scaling {lam β F1 : ℝ} (hl : 0 < lam) (hβ : 0 < β) :
    lam * ((β / lam) ^ (4 / 7 : ℝ) * F1) = lam ^ (3 / 7 : ℝ) * β ^ (4 / 7 : ℝ) * F1 := by
  rcases lt_trichotomy F1 0 with hF | hF | hF
  · have h := working_functional_scaling_pos hl hβ (F1 := -F1) (by linarith)
    linarith
  · subst hF; simp
  · exact working_functional_scaling_pos hl hβ hF

/-- Remark `rem:window`: the vacuum energy `e²Λ²/(8π²) = αΛ²/(2π)` and the crossover ratio
`(αΛ²/(2π)) / (c_α α^(2/7) Λ^(12/7)) = (α^(5/2) Λ)^(2/7) / (2π c_α)`. -/
theorem crossover_ratio {F1 α Λ : ℝ} (hF : 0 < F1) (hα : 0 < α) (hΛ : 0 < Λ) :
    (α * Λ ^ 2 / (2 * π)) / (cAlpha F1 * α ^ (2 / 7 : ℝ) * Λ ^ (12 / 7 : ℝ))
      = (α ^ (5 / 2 : ℝ) * Λ) ^ (2 / 7 : ℝ) / (2 * π * cAlpha F1) := by
  have hpi := Real.pi_pos
  unfold cAlpha
  apply Real.log_injOn_pos (Set.mem_Ioi.2 (by positivity)) (Set.mem_Ioi.2 (by positivity))
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow, Real.log_pow]
  push_cast
  ring

theorem vacuum_energy {e α Λ : ℝ} (hα : e ^ 2 = 4 * π * α) :
    e ^ 2 * Λ ^ 2 / (8 * π ^ 2) = α * Λ ^ 2 / (2 * π) := by
  have := Real.pi_pos
  rw [hα]; field_simp; ring

/-- `eq:calpha` (and the proof of `cor:limit`): with `ℓ = (Λ/(πe²))^(1/7)`, `Ξ = e²ℓ²` and
`e² = 4πα`: `Ξ = π^(-2/7) (e⁵Λ)^(2/7)`, `ℓ⁷ = Λ/(4π²α)` and
`ℓ^(1/3) = (4π²)^(-1/21) (Λ/α)^(1/21)`. -/
theorem params_identities {e α Λ : ℝ} (he : 0 < e) (hΛ : 0 < Λ) (hα : e ^ 2 = 4 * π * α) :
    e ^ 2 * ((Λ / (π * e ^ 2)) ^ (1 / 7 : ℝ)) ^ 2 = π ^ (-(2 / 7) : ℝ) * (e ^ 5 * Λ) ^ (2 / 7 : ℝ)
    ∧ ((Λ / (π * e ^ 2)) ^ (1 / 7 : ℝ)) ^ 7 = Λ / (4 * π ^ 2 * α)
    ∧ ((Λ / (π * e ^ 2)) ^ (1 / 7 : ℝ)) ^ (1 / 3 : ℝ)
        = (4 * π ^ 2) ^ (-(1 / 21) : ℝ) * (Λ / α) ^ (1 / 21 : ℝ) := by
  have hpi := Real.pi_pos
  have hα0 : 0 < α := by
    have : 0 < e ^ 2 := by positivity
    rw [hα] at this; nlinarith
  have hαe : α = e ^ 2 / (4 * π) := by field_simp; linarith
  refine ⟨?_, ?_, ?_⟩
  · apply Real.log_injOn_pos (Set.mem_Ioi.2 (by positivity)) (Set.mem_Ioi.2 (by positivity))
    simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow, Real.log_pow]
    push_cast
    ring
  · rw [hαe]
    apply Real.log_injOn_pos (Set.mem_Ioi.2 (by positivity)) (Set.mem_Ioi.2 (by positivity))
    simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow, Real.log_pow,
      log_four]
    push_cast
    ring
  · rw [hαe]
    apply Real.log_injOn_pos (Set.mem_Ioi.2 (by positivity)) (Set.mem_Ioi.2 (by positivity))
    simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow, Real.log_pow,
      log_four]
    push_cast
    ring

end PauliFierzUV.PaperI
