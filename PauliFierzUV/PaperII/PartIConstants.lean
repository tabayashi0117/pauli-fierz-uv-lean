import PauliFierzUV.Common

/-!
# Paper II, Part I: the constants of Theorem A

Paper II is arXiv:2610.34125. Section 3 (`sec:partI-result`) defines, for `σ = K/(2m) > 0`,

* `x_K = (4α/3π) log(1+σ)`,
* `t_K = (3πα / (16 log(1+σ))) L(σ)²`,
* `q_K = (2 / log(1+σ)) (log(1+σ) - σ/(1+σ))`,
* `ρ_K = 2 √(q_K t_K) + 2 t_K`,
* `L(σ) = ∫₀^σ √(t/(1+t)) dt = √(σ(1+σ)) - arsinh √σ`,

and Theorem 3.1 (`thm:partI`) states `h ≥ 1 + 2x_K/(1+ρ_K)`. This file proves, with these definitions:

* the closed form of `L` and the two closed-form integrals of Appendix C (`app:integrals`),
  and the identities `t_K = 𝖺_K²/(m S(0))`, `q_K = 𝖭_K/(m S(0))` stated there;
* Corollary 3.2 (`cor:partI-explicit`, = Theorem A, first part) **from** `thm:partI`:
  for `σ = 1/2`, `2x/(1+ρ) ≥ 0.3441 α / (1 + 0.2985 √α + 0.1252 α)` for all `α ≥ 0`
  (the numerical constants are proved in Lean, not taken from the interval computation).

Theorem `thm:partI` itself (an operator inequality) is not formalized; the corollaries are of
the form "`thm:partI` ⇒ conclusion". The asymptotic corollaries are in `PartIAsymptotics`.
-/

open Real Filter Topology intervalIntegral

namespace PauliFierzUV.PaperII

/-- `L(σ) = √(σ(1+σ)) - arsinh √σ`. -/
noncomputable def Lfun (σ : ℝ) : ℝ := √(σ * (1 + σ)) - arsinh (√σ)

/-- `x_K` as a function of `α` and `σ = K/(2m)`. -/
noncomputable def xK (α σ : ℝ) : ℝ := 4 * α / (3 * π) * log (1 + σ)

/-- `t_K` as a function of `α` and `σ = K/(2m)`. -/
noncomputable def tK (α σ : ℝ) : ℝ := 3 * π * α / (16 * log (1 + σ)) * Lfun σ ^ 2

/-- `q_K` as a function of `σ = K/(2m)`. -/
noncomputable def qK (σ : ℝ) : ℝ := 2 / log (1 + σ) * (log (1 + σ) - σ / (1 + σ))

/-- `ρ_K = 2√(q_K t_K) + 2 t_K`. -/
noncomputable def ρK (α σ : ℝ) : ℝ := 2 * √(qK σ * tK α σ) + 2 * tK α σ

/-- The right-hand side `1 + 2x_K/(1+ρ_K)` of Theorem `thm:partI`. -/
noncomputable def partIBound (α σ : ℝ) : ℝ := 1 + 2 * xK α σ / (1 + ρK α σ)

lemma xK_eq (α σ : ℝ) : xK α σ = α * xK 1 σ := by unfold xK; ring

lemma tK_eq (α σ : ℝ) : tK α σ = α * tK 1 σ := by unfold tK; ring

lemma tK_nonneg {α σ : ℝ} (hα : 0 ≤ α) (hσ : 0 < σ) : 0 ≤ tK α σ := by
  unfold tK
  have : 0 < log (1 + σ) := Real.log_pos (by linarith)
  positivity

lemma ρK_nonneg {α σ : ℝ} (hα : 0 ≤ α) (hσ : 0 < σ) : 0 ≤ ρK α σ := by
  unfold ρK
  have := tK_nonneg hα hσ
  positivity

/-- For `α > 0` the bound of `thm:partI` is strictly larger than `1` (`thm:partI`, last
sentence). -/
lemma one_lt_partIBound {α σ : ℝ} (hα : 0 < α) (hσ : 0 < σ) : 1 < partIBound α σ := by
  unfold partIBound
  have hρ := ρK_nonneg hα.le hσ
  have : 0 < xK α σ := by
    unfold xK
    have : 0 < log (1 + σ) := Real.log_pos (by linarith)
    positivity
  have : 0 < 2 * xK α σ / (1 + ρK α σ) := by positivity
  linarith

/-! ### The closed forms of Appendix `app:integrals` -/

lemma hasDerivAt_Lfun {t : ℝ} (ht : 0 < t) : HasDerivAt Lfun (√(t / (1 + t))) t := by
  have h1 : HasDerivAt (fun y => y * (1 + y)) (1 * (1 + t) + t * 1) t :=
    (hasDerivAt_id' t).mul ((hasDerivAt_id' t).const_add 1)
  have h2 := h1.sqrt (by positivity)
  have h3 := (Real.hasDerivAt_arsinh (√t)).comp t (Real.hasDerivAt_sqrt ht.ne')
  have h := h2.sub h3
  convert h using 1
  · funext y; simp [Lfun]
  have hs : 0 < √t := Real.sqrt_pos.2 ht
  have hs1 : 0 < √(1 + t) := Real.sqrt_pos.2 (by linarith)
  rw [Real.sq_sqrt ht.le, Real.sqrt_mul ht.le, Real.sqrt_div ht.le]
  have ht2 : √t ^ 2 = t := Real.sq_sqrt ht.le
  field_simp
  nlinarith [ht2]

lemma continuous_Lfun : Continuous Lfun := by
  unfold Lfun
  exact (by fun_prop : Continuous fun σ : ℝ => √(σ * (1 + σ))).sub
    (Real.continuous_arsinh.comp Real.continuous_sqrt)

lemma Lfun_zero : Lfun 0 = 0 := by simp [Lfun]

/-- `L(σ) = ∫₀^σ √(t/(1+t)) dt` (Section `sec:partI-result`). -/
theorem integral_Lfun {σ : ℝ} (hσ : 0 < σ) :
    ∫ t in (0 : ℝ)..σ, √(t / (1 + t)) = Lfun σ := by
  have hint : IntervalIntegrable (fun t : ℝ => √(t / (1 + t))) MeasureTheory.volume 0 σ := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le hσ.le] at ht
    have : 1 + t ≠ 0 := by linarith [ht.1]
    exact (Real.continuous_sqrt.continuousAt.comp
      (continuousAt_id.div (continuousAt_const.add continuousAt_id) this)).continuousWithinAt
  have h0 : Tendsto Lfun (𝓝[>] 0) (𝓝 (Lfun 0)) :=
    continuous_Lfun.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h1 : Tendsto Lfun (𝓝[<] σ) (𝓝 (Lfun σ)) :=
    continuous_Lfun.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  rw [integral_eq_sub_of_hasDerivAt_of_tendsto hσ (fun t ht => hasDerivAt_Lfun ht.1) hint h0 h1,
    Lfun_zero, sub_zero]

/-- First closed form of Appendix `app:integrals`: with `σ = K/(2m)`,
`∫₀^K m √(k/(2m+k)) dk = 2 m² L(σ)`. -/
theorem integral_amplitude {m K : ℝ} (hm : 0 < m) (hK : 0 < K) :
    ∫ k in (0 : ℝ)..K, m * √(k / (2 * m + k)) = 2 * m ^ 2 * Lfun (K / (2 * m)) := by
  have hc : (2 * m) ≠ 0 := by positivity
  have hsub := intervalIntegral.integral_comp_mul_left
    (fun k => m * √(k / (2 * m + k))) hc (a := 0) (b := K / (2 * m))
  have e1 : 2 * m * (K / (2 * m)) = K := by field_simp
  rw [mul_zero, e1] at hsub
  have e2 : ∀ t : ℝ, m * √(2 * m * t / (2 * m + 2 * m * t)) = m * √(t / (1 + t)) := by
    intro t
    congr 2
    have : 2 * m + 2 * m * t = 2 * m * (1 + t) := by ring
    rw [this, mul_div_mul_left _ _ hc]
  simp only [e2] at hsub
  rw [intervalIntegral.integral_const_mul, integral_Lfun (by positivity)] at hsub
  rw [smul_eq_mul] at hsub
  have : ∫ k in (0 : ℝ)..K, m * √(k / (2 * m + k)) = 2 * m * (m * Lfun (K / (2 * m))) := by
    rw [hsub]; field_simp
  rw [this]; ring

/-- Second closed form of Appendix `app:integrals`: with `σ = K/(2m)`,
`∫₀^K 4m²k/(2m+k)² dk = 4m² (log(1+σ) - σ/(1+σ))`. -/
theorem integral_recoil {m K : ℝ} (hm : 0 < m) (hK : 0 < K) :
    ∫ k in (0 : ℝ)..K, 4 * m ^ 2 * k / (2 * m + k) ^ 2
      = 4 * m ^ 2 * (log (1 + K / (2 * m)) - (K / (2 * m)) / (1 + K / (2 * m))) := by
  have hd : ∀ k ∈ Set.uIcc (0 : ℝ) K, HasDerivAt
      (fun k => 4 * m ^ 2 * (log (2 * m + k) + 2 * m / (2 * m + k)))
      (4 * m ^ 2 * k / (2 * m + k) ^ 2) k := by
    intro k hk
    rw [Set.uIcc_of_le hK.le] at hk
    have hpos : 0 < 2 * m + k := by linarith [hk.1]
    have h1 := ((hasDerivAt_id' k).const_add (2 * m)).log hpos.ne'
    have h2 := ((hasDerivAt_id' k).const_add (2 * m)).inv hpos.ne'
    have h := ((h1.add (h2.const_mul (2 * m))).const_mul (4 * m ^ 2))
    convert h using 1
    · funext y; simp [div_eq_mul_inv]
    · field_simp; ring
  have hcont : IntervalIntegrable (fun k => 4 * m ^ 2 * k / (2 * m + k) ^ 2)
      MeasureTheory.volume 0 K := by
    apply ContinuousOn.intervalIntegrable
    intro k hk
    rw [Set.uIcc_of_le hK.le] at hk
    have hpos : (2 * m + k) ^ 2 ≠ 0 := by have : 0 < 2 * m + k := by linarith [hk.1]
                                          positivity
    exact ((continuousAt_const.mul continuousAt_id).div
      ((continuousAt_const.add continuousAt_id).pow 2) hpos).continuousWithinAt
  rw [integral_eq_sub_of_hasDerivAt hd hcont]
  have h2m : 0 < 2 * m := by positivity
  have hlog : log (2 * m + K) - log (2 * m) = log (1 + K / (2 * m)) := by
    rw [← Real.log_div (by positivity) h2m.ne']
    congr 1; field_simp
  simp only [add_zero]
  have : 4 * m ^ 2 * (log (2 * m + K) + 2 * m / (2 * m + K))
      - 4 * m ^ 2 * (log (2 * m) + 2 * m / (2 * m))
      = 4 * m ^ 2 * ((log (2 * m + K) - log (2 * m)) + (2 * m / (2 * m + K) - 1)) := by
    rw [div_self h2m.ne']; ring
  rw [this, hlog]
  congr 2
  field_simp
  ring

/-- Normalisations of Appendix `app:integrals`: with `𝖺_K = |e|/(16πm) · 2m² L(σ)`,
`m S(0) = m²/(3π²) · log(1+σ)` and `e² = 4πα`, one has `𝖺_K²/(m S(0)) = t_K`. -/
theorem tK_from_amplitude {e α m σ : ℝ} (hm : 0 < m) (hσ : 0 < σ) (he : e ^ 2 = 4 * π * α) :
    (|e| / (16 * π * m) * (2 * m ^ 2 * Lfun σ)) ^ 2 / (m ^ 2 / (3 * π ^ 2) * log (1 + σ))
      = tK α σ := by
  have hl : 0 < log (1 + σ) := Real.log_pos (by linarith)
  unfold tK
  rw [show (|e| / (16 * π * m) * (2 * m ^ 2 * Lfun σ)) ^ 2
      = |e| ^ 2 * (m ^ 2 * Lfun σ ^ 2 / (64 * π ^ 2)) by field_simp; ring, sq_abs, he]
  field_simp
  ring

/-- With `𝖭_K = (1/(6π²)) · 4m²(log(1+σ) - σ/(1+σ))`, `𝖭_K/(m S(0)) = q_K`. -/
theorem qK_from_recoil {m σ : ℝ} (hm : 0 < m) (hσ : 0 < σ) :
    (1 / (6 * π ^ 2) * (4 * m ^ 2 * (log (1 + σ) - σ / (1 + σ))))
        / (m ^ 2 / (3 * π ^ 2) * log (1 + σ)) = qK σ := by
  have hl : 0 < log (1 + σ) := Real.log_pos (by linarith)
  unfold qK
  field_simp
  ring

/-! ### Numerical bounds at `σ = 1/2` (i.e. `K = m`) -/

lemma log_three_halves_bounds : 0.405464 < log (3 / 2) ∧ log (3 / 2) < 0.405466 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := 1 / 3) (by norm_num) 14
  have e : log (1 - 1 / 3) = -log (3 / 2) := by
    rw [show (1 : ℝ) - 1 / 3 = (3 / 2)⁻¹ by norm_num, Real.log_inv]
  rw [e] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  obtain ⟨h1, h2⟩ := abs_le.1 h
  constructor <;> linarith

/-- Lower bound for `log` from partial sums of `log((1+x)/(1-x)) = 2 artanh x`. -/
lemma log_ge_partial {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (n : ℕ) :
    ∑ k ∈ Finset.range n, 2 * (1 / (2 * (k : ℝ) + 1)) * x ^ (2 * k + 1)
      ≤ log ((1 + x) / (1 - x)) := by
  rw [Real.log_div (by linarith) (by linarith)]
  exact sum_le_hasSum (Finset.range n) (fun i _ => by positivity)
    (Real.hasSum_log_sub_log_of_abs_lt_one (by rw [abs_of_nonneg hx0]; exact hx1))

lemma arsinh_sqrt_half_gt : 0.658473 < arsinh (√(1 / 2)) := by
  have hs1 : (0.70710678 : ℝ) ≤ √(1 / 2) := Real.le_sqrt_of_sq_le (by norm_num)
  have hs2 : (1.22474487 : ℝ) ≤ √(3 / 2) := Real.le_sqrt_of_sq_le (by norm_num)
  have hu : arsinh (√(1 / 2)) = log (√(1 / 2) + √(3 / 2)) := by
    rw [Real.arsinh, Real.sq_sqrt (by norm_num)]; norm_num
  set x0 : ℝ := 0.317835
  have hx : (1 + x0) / (1 - x0) ≤ √(1 / 2) + √(3 / 2) := by
    have : (1 + x0) / (1 - x0) ≤ 0.70710678 + 1.22474487 := by norm_num [x0]
    linarith
  have hlog : log ((1 + x0) / (1 - x0)) ≤ log (√(1 / 2) + √(3 / 2)) :=
    Real.log_le_log (by norm_num [x0]) hx
  have hp := log_ge_partial (x := x0) (by norm_num [x0]) (by norm_num [x0]) 8
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hp
  norm_num [x0] at hp
  rw [hu]
  linarith

lemma Lfun_half_lt : Lfun (1 / 2) < 0.2075525 := by
  have h1 : √(1 / 2 * (1 + 1 / 2) : ℝ) ≤ 0.8660255 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have h2 := arsinh_sqrt_half_gt
  unfold Lfun
  linarith

lemma Lfun_half_pos : 0 < Lfun (1 / 2) := by
  rw [← integral_Lfun (by norm_num)]
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le (by norm_num)] at ht
    have : 1 + t ≠ 0 := by linarith [ht.1]
    exact (Real.continuous_sqrt.continuousAt.comp
      (continuousAt_id.div (continuousAt_const.add continuousAt_id) this)).continuousWithinAt
  · intro t ht
    have : 0 < t / (1 + t) := div_pos ht.1 (by linarith [ht.1])
    exact Real.sqrt_pos.2 this
  · norm_num

/-- `2x_m/α = (8/3π) log(3/2) ≥ 0.3441` (Table `tab:partI-values`). -/
lemma two_xK_half_ge : 0.3441 ≤ 2 * xK 1 (1 / 2) := by
  obtain ⟨hl, -⟩ := log_three_halves_bounds
  have hpi := Real.pi_lt_d6
  have hpi0 := Real.pi_pos
  unfold xK
  rw [show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num]
  rw [show 2 * (4 * 1 / (3 * π) * log (3 / 2)) = 8 * log (3 / 2) / (3 * π) by ring,
    le_div_iff₀ (by positivity)]
  nlinarith

/-- `2t_m/α ≤ 0.1252` (Table `tab:partI-values`). -/
lemma two_tK_half_le : 2 * tK 1 (1 / 2) ≤ 0.1252 := by
  obtain ⟨hl, -⟩ := log_three_halves_bounds
  have hpi := Real.pi_lt_d6
  have hpi0 := Real.pi_pos
  have hL := Lfun_half_lt
  have hL0 := Lfun_half_pos
  have hL2 : Lfun (1 / 2) ^ 2 ≤ 0.2075525 ^ 2 := pow_le_pow_left₀ hL0.le hL.le 2
  unfold tK
  rw [show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num]
  have hlp : 0 < log (3 / 2 : ℝ) := by linarith
  rw [show 2 * (3 * π * 1 / (16 * log (3 / 2)) * Lfun (1 / 2) ^ 2)
      = 3 * π * Lfun (1 / 2) ^ 2 / (8 * log (3 / 2)) by field_simp; ring,
    div_le_iff₀ (by positivity)]
  have : 3 * π * Lfun (1 / 2) ^ 2 ≤ 3 * 3.141593 * 0.2075525 ^ 2 := by
    have := mul_le_mul (by linarith : 3 * π ≤ 3 * 3.141593) hL2 (by positivity) (by norm_num)
    linarith
  nlinarith

lemma qK_half_le : qK (1 / 2) ≤ 0.35581 := by
  obtain ⟨hl, hu⟩ := log_three_halves_bounds
  unfold qK
  rw [show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num]
  have hlp : 0 < log (3 / 2 : ℝ) := by linarith
  rw [show 2 / log (3 / 2) * (log (3 / 2) - 1 / 2 / (3 / 2)) = 2 - 2 / (3 * log (3 / 2)) by
    field_simp]
  have : 2 / (3 * 0.405466) ≤ 2 / (3 * log (3 / 2 : ℝ)) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  norm_num at this ⊢
  linarith

lemma qK_half_nonneg : 0 ≤ qK (1 / 2) := by
  obtain ⟨hl, -⟩ := log_three_halves_bounds
  unfold qK
  rw [show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num]
  have hlp : 0 < log (3 / 2 : ℝ) := by linarith
  have : 0 ≤ log (3 / 2 : ℝ) - 1 / 2 / (3 / 2) := by norm_num; linarith
  positivity

/-- `2√(q_m t_m/α) ≤ 0.2985` (Table `tab:partI-values`). -/
lemma two_sqrt_qt_half_le : 2 * √(qK (1 / 2) * tK 1 (1 / 2)) ≤ 0.2985 := by
  have hq := qK_half_le
  have hq0 := qK_half_nonneg
  have ht := two_tK_half_le
  have ht0 : 0 ≤ tK 1 (1 / 2) := tK_nonneg (by norm_num) (by norm_num)
  have hprod : qK (1 / 2) * tK 1 (1 / 2) ≤ 0.35581 * 0.0626 :=
    mul_le_mul hq (by linarith) ht0 (by norm_num)
  have : √(qK (1 / 2) * tK 1 (1 / 2)) ≤ 0.14925 := by
    rw [Real.sqrt_le_left (by norm_num)]
    linarith [show (0.35581 : ℝ) * 0.0626 ≤ 0.14925 ^ 2 by norm_num]
  linarith

/-- **Corollary `cor:partI-explicit`, arithmetic part.** For all `α ≥ 0` and `σ = 1/2`
(the band `K = m`),
`0.3441 α / (1 + 0.2985 √α + 0.1252 α) ≤ 2x_K / (1 + ρ_K)`. -/
theorem partI_explicit_arith {α : ℝ} (hα : 0 ≤ α) :
    0.3441 * α / (1 + 0.2985 * √α + 0.1252 * α) ≤ 2 * xK α (1 / 2) / (1 + ρK α (1 / 2)) := by
  have hx := two_xK_half_ge
  have ht := two_tK_half_le
  have hr := two_sqrt_qt_half_le
  have ht0 : 0 ≤ tK 1 (1 / 2) := tK_nonneg (by norm_num) (by norm_num)
  have hρ : ρK α (1 / 2)
      = 2 * √(qK (1 / 2) * tK 1 (1 / 2)) * √α + 2 * tK 1 (1 / 2) * α := by
    unfold ρK
    rw [tK_eq α, show qK (1 / 2) * (α * tK 1 (1 / 2)) = (qK (1 / 2) * tK 1 (1 / 2)) * α by ring,
      Real.sqrt_mul' _ hα]
    ring
  have hsa := Real.sqrt_nonneg α
  have hden : 1 + ρK α (1 / 2) ≤ 1 + 0.2985 * √α + 0.1252 * α := by
    rw [hρ]
    nlinarith [mul_le_mul_of_nonneg_right hr hsa, mul_le_mul_of_nonneg_right ht hα]
  have hden0 : 0 < 1 + ρK α (1 / 2) := by
    have := ρK_nonneg hα (show (0 : ℝ) < 1 / 2 by norm_num); linarith
  rw [xK_eq α]
  calc 0.3441 * α / (1 + 0.2985 * √α + 0.1252 * α)
      ≤ 0.3441 * α / (1 + ρK α (1 / 2)) :=
        div_le_div_of_nonneg_left (by positivity) hden0 hden
    _ ≤ 2 * (α * xK 1 (1 / 2)) / (1 + ρK α (1 / 2)) := by
        apply div_le_div_of_nonneg_right _ hden0.le
        nlinarith

/-- **Corollary `cor:partI-explicit`** (= Theorem A, first part) **from Theorem `thm:partI`**:
if `h ≥ 1 + 2x_K/(1+ρ_K)` for the band `K = m` (`σ = 1/2`), then
`h ≥ 1 + 0.3441 α / (1 + 0.2985 √α + 0.1252 α)`. -/
theorem theoremA_explicit_of_partI {α hval : ℝ} (hα : 0 ≤ α)
    (hpartI : partIBound α (1 / 2) ≤ hval) :
    1 + 0.3441 * α / (1 + 0.2985 * √α + 0.1252 * α) ≤ hval := by
  unfold partIBound at hpartI
  linarith [partI_explicit_arith hα]

end PauliFierzUV.PaperII
