import Mathlib

/-!
# Paper I, proof of Proposition B.1 (`prop:F1`) (b): the radial integrals of the minimiser

Paper I is arXiv:2610.34122.

`u r = 1 - sin r / (r cos x)` on `[0, x]`, where `tan x = x`. Then
`∫ u r² = x³/3`, `∫ |u'|² r² = x³/2`, `∫ u² r² = (5/6) x³`, hence `a = 3/10`.
Also the existence of the root `x ∈ (π, 3π/2)`. Numerical enclosures of `x₁` and `F[1]` are NOT done here.
-/

open Real Filter Topology intervalIntegral

namespace PauliFierzUV.PaperI

variable {x : ℝ}

/-- The radial profile. `sinc 0 = 1` takes care of the origin. -/
noncomputable def uProfile (x r : ℝ) : ℝ := 1 - Real.sinc r / Real.cos x

lemma sq_mul_sinc (r : ℝ) : r ^ 2 * Real.sinc r = r * Real.sin r := by
  by_cases h : r = 0
  · simp [h]
  · rw [Real.sinc_of_ne_zero h]; field_simp

theorem integral_u (hx : Real.sin x = x * Real.cos x) (hc : Real.cos x ≠ 0) :
    ∫ r in (0 : ℝ)..x, uProfile x r * r ^ 2 = x ^ 3 / 3 := by
  set c := Real.cos x with hcdef
  have hd : ∀ r : ℝ, HasDerivAt (fun r => r ^ 3 / 3 - (Real.sin r - r * Real.cos r) / c)
      (r ^ 2 - r * Real.sin r / c) r := by
    intro r
    have h := ((hasDerivAt_pow 3 r).div_const 3).sub
      (((Real.hasDerivAt_sin r).sub ((hasDerivAt_id' r).mul (Real.hasDerivAt_cos r))).div_const c)
    convert h using 1
    field_simp
    ring
  have e : (fun r => uProfile x r * r ^ 2) = fun r => r ^ 2 - r * Real.sin r / c := by
    funext r
    have := sq_mul_sinc r
    simp only [uProfile]
    rw [← hcdef, ← this]
    field_simp
  rw [e, integral_eq_sub_of_hasDerivAt (fun r _ => hd r)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp only [Real.sin_zero, Real.cos_zero]
  rw [hx, ← hcdef]
  field_simp
  ring

theorem integral_u_sq (hx : Real.sin x = x * Real.cos x) (hc : Real.cos x ≠ 0) :
    ∫ r in (0 : ℝ)..x, uProfile x r ^ 2 * r ^ 2 = 5 / 6 * x ^ 3 := by
  set c := Real.cos x with hcdef
  have hd : ∀ r : ℝ, HasDerivAt
      (fun r => r ^ 3 / 3 - 2 * (Real.sin r - r * Real.cos r) / c
        + (r / 2 - Real.sin r * Real.cos r / 2) / c ^ 2)
      (r ^ 2 - 2 * (r * Real.sin r) / c + Real.sin r ^ 2 / c ^ 2) r := by
    intro r
    have h1 := (hasDerivAt_pow 3 r).div_const 3
    have h2 := (((Real.hasDerivAt_sin r).sub ((hasDerivAt_id' r).mul
      (Real.hasDerivAt_cos r))).const_mul 2).div_const c
    have h3 := (((hasDerivAt_id' r).div_const 2).sub
      (((Real.hasDerivAt_sin r).mul (Real.hasDerivAt_cos r)).div_const 2)).div_const (c ^ 2)
    convert (h1.sub h2).add h3 using 1
    have := Real.sin_sq_add_cos_sq r
    have hcs : Real.cos r ^ 2 = 1 - Real.sin r ^ 2 := by linarith
    field_simp
    ring_nf
    rw [hcs]
    ring
  have e : (fun r => uProfile x r ^ 2 * r ^ 2)
      = fun r => r ^ 2 - 2 * (r * Real.sin r) / c + Real.sin r ^ 2 / c ^ 2 := by
    funext r
    simp only [uProfile]
    rw [← hcdef]
    by_cases h : r = 0
    · simp [h]
    · rw [Real.sinc_of_ne_zero h]; field_simp; ring
  rw [e, integral_eq_sub_of_hasDerivAt (fun r _ => hd r)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp only [Real.sin_zero, Real.cos_zero]
  rw [hx, ← hcdef]
  have hs : x ^ 2 * c ^ 2 = 1 - c ^ 2 := by
    have := Real.sin_sq_add_cos_sq x
    rw [hx, ← hcdef] at this
    nlinarith
  have hfinal : (x / 2 - x * c * c / 2) / c ^ 2 = x ^ 3 / 2 := by
    rw [div_eq_iff (pow_ne_zero 2 hc)]
    have : x / 2 - x * c * c / 2 = x / 2 * (1 - c ^ 2) := by ring
    rw [this, ← hs]
    ring
  have h0 : ((0 : ℝ) / 2 - 0 * 1 / 2) / c ^ 2 = 0 := by simp
  simp only [zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_div, zero_mul, sub_zero,
    mul_zero, add_zero]
  have hmid : x * c - x * c = 0 := sub_self _
  rw [hmid, hfinal]
  simp
  ring

/-- `r² |u'(r)|² = (cos r - sinc r)² / c²`; the antiderivative is singular at `0`. -/
theorem integral_du_sq (hx0 : 0 < x) (hx : Real.sin x = x * Real.cos x) (hc : Real.cos x ≠ 0) :
    ∫ r in (0 : ℝ)..x, (Real.cos r - Real.sinc r) ^ 2 / Real.cos x ^ 2 = x ^ 3 / 2 := by
  set c := Real.cos x with hcdef
  set G : ℝ → ℝ := fun r => r / 2 + Real.sin r * Real.cos r / 2 - Real.sin r ^ 2 / r with hG
  have hd : ∀ r ∈ Set.Ioo (0 : ℝ) x, HasDerivAt G ((Real.cos r - Real.sinc r) ^ 2) r := by
    intro r hr
    have hr0 : r ≠ 0 := hr.1.ne'
    have h1 := ((hasDerivAt_id' r).div_const 2).add
      (((Real.hasDerivAt_sin r).mul (Real.hasDerivAt_cos r)).div_const 2)
    have h2 := ((Real.hasDerivAt_sin r).pow 2).div (hasDerivAt_id' r) hr0
    convert h1.sub h2 using 1
    rw [Real.sinc_of_ne_zero hr0]
    simp only [Pi.pow_apply]
    have := Real.sin_sq_add_cos_sq r
    have hsn : Real.cos r ^ 2 = 1 - Real.sin r ^ 2 := by linarith
    field_simp
    norm_num
    linear_combination r ^ 2 * this
  have hint : IntervalIntegrable (fun r => (Real.cos r - Real.sinc r) ^ 2) MeasureTheory.volume 0 x :=
    Continuous.intervalIntegrable (by have := Real.continuous_sinc; fun_prop) _ _
  have hGcont_right : Tendsto G (𝓝[>] 0) (𝓝 0) := by
    have e : ∀ r, G r = r / 2 + Real.sin r * Real.cos r / 2 - Real.sin r * Real.sinc r := by
      intro r
      simp only [hG]
      by_cases h : r = 0
      · simp [h]
      · rw [Real.sinc_of_ne_zero h]; field_simp
    have hc' : Continuous (fun r => r / 2 + Real.sin r * Real.cos r / 2
        - Real.sin r * Real.sinc r) := by
      have := Real.continuous_sinc; fun_prop
    have ht := hc'.tendsto 0
    simp only [Real.sin_zero, zero_div, zero_mul, add_zero, sub_zero] at ht
    have : G = fun r => r / 2 + Real.sin r * Real.cos r / 2 - Real.sin r * Real.sinc r := funext e
    rw [this]
    exact ht.mono_left nhdsWithin_le_nhds
  have hGcont_left : Tendsto G (𝓝[<] x) (𝓝 (G x)) := by
    have : ContinuousAt G x := by
      simp only [hG]
      have hx' : x ≠ 0 := hx0.ne'
      fun_prop (disch := assumption)
    exact this.tendsto.mono_left nhdsWithin_le_nhds
  have main := integral_eq_sub_of_hasDerivAt_of_tendsto hx0 hd hint hGcont_right hGcont_left
  rw [intervalIntegral.integral_div, main]
  simp only [hG, sub_zero]
  rw [hx, ← hcdef]
  have hs : x ^ 2 * c ^ 2 = 1 - c ^ 2 := by
    have := Real.sin_sq_add_cos_sq x
    rw [hx, ← hcdef] at this
    nlinarith
  have hx' : x ≠ 0 := hx0.ne'
  rw [div_eq_iff (pow_ne_zero 2 hc)]
  have e1 : (x * c) ^ 2 / x = x * c ^ 2 := by field_simp
  rw [e1]
  have : x / 2 + x * c * c / 2 - x * c ^ 2 = x / 2 * (1 - c ^ 2) := by ring
  rw [this, ← hs]
  ring

/-- The derivative of the profile away from the origin: `r u'(r) = -(cos r - sinc r)/c`. -/
theorem hasDerivAt_uProfile {r : ℝ} (hr : r ≠ 0) (hc : Real.cos x ≠ 0) :
    HasDerivAt (uProfile x) (-(Real.cos r - Real.sinc r) / (r * Real.cos x)) r := by
  have hs : uProfile x =ᶠ[𝓝 r] fun t => 1 - Real.sin t / t / Real.cos x := by
    filter_upwards [isOpen_ne.mem_nhds hr] with t ht
    simp only [uProfile]
    rw [Real.sinc_of_ne_zero ht]
  refine HasDerivAt.congr_of_eventuallyEq ?_ hs
  have h := (((Real.hasDerivAt_sin r).div (hasDerivAt_id' r) hr).div_const (Real.cos x)).const_sub 1
  convert h using 1
  rw [Real.sinc_of_ne_zero hr]
  field_simp

/-- `a :=½ ‖∇u‖² / ‖u‖² = 3/10`, the radial weights cancelling. -/
theorem a_value (hx0 : 0 < x) (hx : Real.sin x = x * Real.cos x) (hc : Real.cos x ≠ 0) :
    (1 / 2) * (∫ r in (0 : ℝ)..x, (Real.cos r - Real.sinc r) ^ 2 / Real.cos x ^ 2)
      / (∫ r in (0 : ℝ)..x, uProfile x r ^ 2 * r ^ 2) = 3 / 10 := by
  rw [integral_du_sq hx0 hx hc, integral_u_sq hx hc]
  field_simp
  norm_num

/-- Existence of the first root of `tan x = x`, in the form used above. -/
theorem exists_root : ∃ x ∈ Set.Ioo Real.pi (3 * Real.pi / 2),
    Real.sin x = x * Real.cos x ∧ Real.cos x ≠ 0 := by
  have hpi := Real.pi_pos
  set g : ℝ → ℝ := fun t => t * Real.cos t - Real.sin t with hg
  have hcont : ContinuousOn g (Set.Icc Real.pi (3 * Real.pi / 2)) :=
    (by fun_prop : Continuous g).continuousOn
  have h1 : g Real.pi < 0 := by simp [hg]; linarith
  have h2 : 0 < g (3 * Real.pi / 2) := by
    have hc : Real.cos (3 * Real.pi / 2) = 0 := by
      have : 3 * Real.pi / 2 = Real.pi / 2 + Real.pi := by ring
      rw [this, Real.cos_add_pi, Real.cos_pi_div_two]; simp
    have hs : Real.sin (3 * Real.pi / 2) = -1 := by
      have : 3 * Real.pi / 2 = Real.pi / 2 + Real.pi := by ring
      rw [this, Real.sin_add_pi, Real.sin_pi_div_two]
    simp [hg, hc, hs]
  obtain ⟨x, hx, hgx⟩ := intermediate_value_Ioo (by linarith) hcont ⟨h1, h2⟩
  have hgx' : x * Real.cos x - Real.sin x = 0 := hgx
  refine ⟨x, hx, by linarith, ?_⟩
  intro hc0
  have hs : Real.sin x = 0 := by rw [hc0] at hgx'; linarith
  have := Real.sin_sq_add_cos_sq x
  rw [hs, hc0] at this
  norm_num at this

end PauliFierzUV.PaperI
