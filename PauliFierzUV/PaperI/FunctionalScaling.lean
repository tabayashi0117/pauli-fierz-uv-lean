import Mathlib

/-!
# Paper I, Section 3: the scaling of the comparison functional

Paper I is arXiv:2610.34122. Section 3 ("The comparison functional") defines
`𝓕_β(φ) = ½‖∇φ‖² + β‖φ‖₁`, `F[β] = inf {𝓕_β(φ) : φ = |φ|, ‖φ‖₂ = 1}`, and states that the
scaling `φ_R = R^(-3/2) φ(·/R)` with `R = β^(-2/7)` gives

  `F[β] = β^(4/7) F[1]`  and  `F_λ[β] := inf {(λ/2)‖∇φ‖² + β‖φ‖₁} = λ^(3/7) β^(4/7) F[1]`.

We prove this for the infimum over the class of nonnegative `C¹` functions with compact support
and `‖φ‖₂ = 1` on a `d`-dimensional real inner product space with an additive Haar measure. For a
general dimension `d` the exponents are `d/(d+4)` and `4/(d+4)`; for `d = 3` they are `3/7` and
`4/7`. The paper's `F[β]` is the infimum over `H¹ ∩ L¹`; the two infima agree by density, which
is **not** formalized here, so the result is the scaling identity for the `C¹_c` infimum. The
proof is the same dilation argument and applies verbatim to any dilation-invariant class.
-/

open MeasureTheory
open scoped Pointwise

namespace PauliFierzUV.PaperI.Scaling

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- The admissible class: nonnegative `C¹` functions with compact support and `‖φ‖₂ = 1`. -/
def Admissible (φ : E → ℝ) : Prop :=
  ContDiff ℝ 1 φ ∧ HasCompactSupport φ ∧ (∀ x, 0 ≤ φ x) ∧ ∫ x, φ x ^ 2 ∂μ = 1

/-- `‖∇φ‖²`. -/
noncomputable def kinetic (φ : E → ℝ) : ℝ := ∫ x, ‖fderiv ℝ φ x‖ ^ 2 ∂μ

/-- `‖φ‖₁ = ∫ φ` for `φ ≥ 0`. -/
noncomputable def mass (φ : E → ℝ) : ℝ := ∫ x, φ x ∂μ

/-- `(κ/2)‖∇φ‖² + β‖φ‖₁`; `κ = 1` gives `𝓕_β`, `κ = λ` the functional of `F_λ[β]`. -/
noncomputable def energy (κ β : ℝ) (φ : E → ℝ) : ℝ := κ / 2 * kinetic μ φ + β * mass μ φ

/-- `F_κ[β] = inf {(κ/2)‖∇φ‖² + β‖φ‖₁ : φ admissible}`; `F[β] = Finf μ 1 β`. -/
noncomputable def Finf (κ β : ℝ) : ℝ := sInf (energy μ κ β '' {φ | Admissible μ φ})

/-- The `L²`-normalised dilation `φ_R(x) = R^(-d/2) φ(x/R)`. -/
noncomputable def dilate (R : ℝ) (φ : E → ℝ) : E → ℝ :=
  fun x => R ^ (-(Module.finrank ℝ E : ℝ) / 2) * φ (R⁻¹ • x)

local notation "d" => (Module.finrank ℝ E : ℝ)

variable {μ}

lemma dilate_dilate_inv {R : ℝ} (hR : 0 < R) (φ : E → ℝ) : dilate R (dilate R⁻¹ φ) = φ := by
  funext x
  simp only [dilate, inv_inv, smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
  rw [← mul_assoc, Real.inv_rpow hR.le, mul_inv_cancel₀ (by positivity), one_mul]

lemma rpow_d_aux {R : ℝ} (hR : 0 < R) :
    (R ^ (-d / 2)) ^ 2 * R ^ (Module.finrank ℝ E) = 1 := by
  rw [← Real.rpow_natCast R, ← Real.rpow_natCast (R ^ (-d / 2)), ← Real.rpow_mul hR.le,
    ← Real.rpow_add hR]
  norm_num

lemma admissible_dilate {R : ℝ} (hR : 0 < R) {φ : E → ℝ} (hφ : Admissible μ φ) :
    Admissible μ (dilate R φ) := by
  obtain ⟨h1, h2, h3, h4⟩ := hφ
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact contDiff_const.mul (h1.comp (contDiff_id.const_smul R⁻¹))
  · have : HasCompactSupport fun x => φ (R⁻¹ • x) := h2.comp_smul (inv_ne_zero hR.ne')
    exact this.mul_left (f := fun _ => R ^ (-d / 2))
  · intro x
    exact mul_nonneg (by positivity) (h3 _)
  · simp only [dilate, mul_pow]
    rw [integral_const_mul,
      Measure.integral_comp_inv_smul_of_nonneg μ (fun y => φ y ^ 2) hR.le, h4, smul_eq_mul,
      mul_one, rpow_d_aux hR]

lemma hasFDerivAt_dilate {R : ℝ} {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ) (x : E) :
    HasFDerivAt (dilate R φ) ((R ^ (-d / 2) * R⁻¹) • fderiv ℝ φ (R⁻¹ • x)) x := by
  have hd : HasFDerivAt φ (fderiv ℝ φ (R⁻¹ • x)) (R⁻¹ • x) :=
    ((hφ.differentiable (by norm_num)) _).hasFDerivAt
  have hl : HasFDerivAt (fun y : E => R⁻¹ • y) (R⁻¹ • ContinuousLinearMap.id ℝ E) x :=
    ((ContinuousLinearMap.id ℝ E).hasFDerivAt).const_smul R⁻¹
  have h := (hd.comp x hl).const_mul (R ^ (-d / 2))
  refine h.congr_fderiv ?_
  ext v
  simp [smul_smul, mul_comm]

lemma kinetic_dilate {R : ℝ} (hR : 0 < R) {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ) :
    kinetic μ (dilate R φ) = R ^ (-2 : ℝ) * kinetic μ φ := by
  unfold kinetic
  have e : ∀ x, ‖fderiv ℝ (dilate R φ) x‖ ^ 2
      = (R ^ (-d / 2) * R⁻¹) ^ 2 * ‖fderiv ℝ φ (R⁻¹ • x)‖ ^ 2 := by
    intro x
    rw [(hasFDerivAt_dilate hφ x).fderiv, norm_smul, Real.norm_of_nonneg (by positivity), mul_pow]
  simp only [e]
  rw [integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg μ (fun y => ‖fderiv ℝ φ y‖ ^ 2) hR.le, smul_eq_mul,
    ← mul_assoc]
  congr 1
  rw [mul_pow, mul_comm (_ ^ 2) (R⁻¹ ^ 2), mul_assoc, rpow_d_aux hR, mul_one, inv_pow,
    Real.rpow_neg hR.le]
  norm_num

lemma mass_dilate {R : ℝ} (hR : 0 < R) (φ : E → ℝ) :
    mass μ (dilate R φ) = R ^ (d / 2) * mass μ φ := by
  unfold mass dilate
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg μ φ hR.le, smul_eq_mul,
    ← mul_assoc]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_add hR]
  congr 1
  ring

/-- The dilation exponent: with `R = (κ/β)^(2/(d+4))`, both terms scale by
`s = κ^(d/(d+4)) β^(4/(d+4))`. -/
lemma energy_dilate {κ β : ℝ} (hκ : 0 < κ) (hβ : 0 < β) {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ) :
    energy μ κ β (dilate ((κ / β) ^ (2 / (d + 4))) φ)
      = κ ^ (d / (d + 4)) * β ^ (4 / (d + 4)) * energy μ 1 1 φ := by
  set R := (κ / β) ^ (2 / (d + 4)) with hRdef
  have hR : 0 < R := by positivity
  have hd4 : 0 < d + 4 := by positivity
  have c1 : κ * R ^ (-2 : ℝ) = κ ^ (d / (d + 4)) * β ^ (4 / (d + 4)) := by
    apply Real.log_injOn_pos (Set.mem_Ioi.2 (by positivity)) (Set.mem_Ioi.2 (by positivity))
    rw [hRdef]
    simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow]
    field_simp
    ring
  have c2 : β * R ^ (d / 2) = κ ^ (d / (d + 4)) * β ^ (4 / (d + 4)) := by
    apply Real.log_injOn_pos (Set.mem_Ioi.2 (by positivity)) (Set.mem_Ioi.2 (by positivity))
    rw [hRdef]
    simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow]
    field_simp
    ring
  unfold energy
  rw [kinetic_dilate hR hφ, mass_dilate hR]
  calc κ / 2 * (R ^ (-2 : ℝ) * kinetic μ φ) + β * (R ^ (d / 2) * mass μ φ)
      = (κ * R ^ (-2 : ℝ)) / 2 * kinetic μ φ + (β * R ^ (d / 2)) * mass μ φ := by ring
    _ = _ := by rw [c1, c2]; ring

/-- `F_κ[β] = κ^(d/(d+4)) β^(4/(d+4)) F_1[1]` for `κ, β > 0`. -/
theorem Finf_scaling {κ β : ℝ} (hκ : 0 < κ) (hβ : 0 < β) :
    Finf μ κ β = κ ^ (d / (d + 4)) * β ^ (4 / (d + 4)) * Finf μ 1 1 := by
  set s := κ ^ (d / (d + 4)) * β ^ (4 / (d + 4)) with hs
  set R := (κ / β) ^ (2 / (d + 4)) with hRdef
  have hR : 0 < R := by positivity
  have hset : energy μ κ β '' {φ | Admissible μ φ} = s • (energy μ 1 1 '' {φ | Admissible μ φ}) := by
    ext v
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_smul_set, smul_eq_mul]
    constructor
    · rintro ⟨φ, hφ, rfl⟩
      refine ⟨energy μ 1 1 (dilate R⁻¹ φ), ⟨dilate R⁻¹ φ, admissible_dilate (inv_pos.2 hR) hφ, rfl⟩,
        ?_⟩
      have h := energy_dilate (μ := μ) hκ hβ (admissible_dilate (inv_pos.2 hR) hφ).1
      rw [← hRdef, dilate_dilate_inv hR] at h
      rw [h]
    · rintro ⟨w, ⟨φ, hφ, rfl⟩, rfl⟩
      exact ⟨dilate R φ, admissible_dilate hR hφ, energy_dilate hκ hβ hφ.1⟩
  unfold Finf
  rw [hset, Real.sInf_smul_of_nonneg (by positivity), smul_eq_mul]

/-- **Section 3 of Paper I, in dimension 3**: `F[β] = β^(4/7) F[1]`. -/
theorem F_scaling_dim3 (h3 : Module.finrank ℝ E = 3) {β : ℝ} (hβ : 0 < β) :
    Finf μ 1 β = β ^ (4 / 7 : ℝ) * Finf μ 1 1 := by
  rw [Finf_scaling one_pos hβ, h3]
  norm_num

/-- **Section 3 of Paper I, in dimension 3**: `F_λ[β] = λ F[β/λ] = λ^(3/7) β^(4/7) F[1]`. -/
theorem F_lambda_scaling_dim3 (h3 : Module.finrank ℝ E = 3) {lam β : ℝ} (hl : 0 < lam)
    (hβ : 0 < β) :
    Finf μ lam β = lam ^ (3 / 7 : ℝ) * β ^ (4 / 7 : ℝ) * Finf μ 1 1 := by
  rw [Finf_scaling hl hβ, h3]
  norm_num

end PauliFierzUV.PaperI.Scaling
