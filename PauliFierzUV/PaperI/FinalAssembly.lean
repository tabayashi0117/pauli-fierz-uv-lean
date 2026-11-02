import Mathlib

/-!
# Paper I, Section 8: the final assembly of Theorem 1.1 (`thm:main`) (b)

Paper I is arXiv:2610.34122. **This is a "hypothesis ⇒ conclusion" result.** Everything analytic
is abstracted into the hypothesis `RelErr`, which is the statement of Proposition 8.3 (`prop:relerr`)
(with `K_V` replaced by its stated upper bound `C(1+s+log(1+λe²))⁶`). From it we derive the
conclusion of `thm:main` (b) in working units (`1 - E₀(H^(λ))/F_λ[β] ≤ ε`), following the order of
choices of Table `tab:choices`: `ε ↦ (s, ν, η, M) ↦ (Ξ₀, κ₀, ℓ₀)`, and the elementary limits.
`prop:relerr` itself (the analytic core of Paper I) is NOT proved here, and the return to physical
units (Lemma `lem:scaling` and `eq:coeff`) is a separate step; see `LeadingConstant.coeff_*`.

`Rel e2 ℓ` stands for `1 - E₀(H^(λ)) / F_λ[β]`, with `e2 = e²`, `λ = e² ℓ⁷`.
-/

open Real Filter Topology

namespace PauliFierzUV.PaperI

/-- Proposition `prop:relerr`, with `K_V` replaced by its stated upper bound. -/
def RelErr (Rel : ℝ → ℝ → ℝ) (s₀ : ℕ) (C : ℝ) : Prop :=
  ∀ e2 ℓ : ℝ, 0 < e2 → 0 < ℓ → ∀ (s ν : ℕ) (η M : ℝ),
    s₀ ≤ s → 1 ≤ s → 1 ≤ ν → 0 < η → η < 1 → 1 ≤ M → (s : ℝ) ≤ M * ℓ →
    1 / (ν : ℝ) ^ 2 + η + C * Real.log (2 + s) / s ≤ 1 →
    Rel e2 ℓ ≤ 1 / (ν : ℝ) ^ 2 + η + C * Real.log (2 + s) / s
      + C * (M ^ 3 / (e2 * ℓ ^ 2) + 1 / M ^ 2
        + (ν : ℝ) ^ 2 * M ^ 3 * s ^ 2
          * (C * (1 + s + Real.log (1 + e2 * (e2 * ℓ ^ 7))) ^ 6) / (η * ℓ ^ 2))

/-- `1 + e⁴ ℓ⁷ ≤ (2 + e²)² (1 + ℓ)⁷`, in logarithmic form. -/
lemma log_bound {e2 ℓ : ℝ} (he : 0 < e2) (hℓ : 0 < ℓ) :
    Real.log (1 + e2 * (e2 * ℓ ^ 7)) ≤ 7 * Real.log (1 + ℓ) + 2 * Real.log (2 + e2) := by
  have hpos : 0 < 1 + e2 * (e2 * ℓ ^ 7) := by positivity
  have h1 : 1 + e2 * (e2 * ℓ ^ 7) ≤ (1 + ℓ) ^ 7 * (2 + e2) ^ 2 := by
    have a : ℓ ^ 7 ≤ (1 + ℓ) ^ 7 := pow_le_pow_left₀ hℓ.le (by linarith) 7
    have b : 1 ≤ (1 + ℓ) ^ 7 := one_le_pow₀ (by linarith)
    have c : e2 ^ 2 + 1 ≤ (2 + e2) ^ 2 := by nlinarith
    calc 1 + e2 * (e2 * ℓ ^ 7) = 1 + e2 ^ 2 * ℓ ^ 7 := by ring
      _ ≤ (1 + ℓ) ^ 7 * 1 + (1 + ℓ) ^ 7 * e2 ^ 2 := by
          have : e2 ^ 2 * ℓ ^ 7 ≤ e2 ^ 2 * (1 + ℓ) ^ 7 :=
            mul_le_mul_of_nonneg_left a (by positivity)
          nlinarith
      _ = (1 + ℓ) ^ 7 * (e2 ^ 2 + 1) := by ring
      _ ≤ (1 + ℓ) ^ 7 * (2 + e2) ^ 2 := mul_le_mul_of_nonneg_left c (by positivity)
  calc Real.log (1 + e2 * (e2 * ℓ ^ 7))
      ≤ Real.log ((1 + ℓ) ^ 7 * (2 + e2) ^ 2) := Real.log_le_log hpos h1
    _ = 7 * Real.log (1 + ℓ) + 2 * Real.log (2 + e2) := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
        norm_num

/-- `log(2+s)/s → 0`. -/
lemma tendsto_log_div : Tendsto (fun s : ℕ => Real.log (2 + (s : ℝ)) / (s : ℝ)) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have h2 : Tendsto (fun s : ℕ => (2 + (s : ℝ))) atTop atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
  have h3 := h.comp h2
  have h4 : Tendsto (fun s : ℕ => (2 + (s : ℝ)) / (s : ℝ)) atTop (𝓝 1) := by
    have : Tendsto (fun s : ℕ => 2 / (s : ℝ) + 1) atTop (𝓝 (0 + 1)) :=
      (tendsto_const_div_atTop_nhds_zero_nat 2).add tendsto_const_nhds
    refine (this.congr' ?_).trans (by simp)
    filter_upwards [eventually_gt_atTop 0] with s hs
    have : (s : ℝ) ≠ 0 := by positivity
    field_simp
  have h5 := h3.mul h4
  simp only [zero_mul] at h5
  refine h5.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with s hs
  have h1 : (s : ℝ) ≠ 0 := by positivity
  have h2' : (2 + (s : ℝ)) ≠ 0 := by positivity
  simp only [Function.comp]
  field_simp

/-- Theorem main (b) of Paper I, in working units, from `RelErr`. -/
theorem main_lower_from_relerr (Rel : ℝ → ℝ → ℝ) (s₀ : ℕ) (C : ℝ) (hC : 0 < C)
    (hrel : RelErr Rel s₀ C) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ ℓ₀ Ξ₀ κ₀ : ℝ, 0 < ℓ₀ ∧ 0 < Ξ₀ ∧ 0 < κ₀ ∧ ∀ e2 ℓ : ℝ, 0 < e2 → ℓ₀ ≤ ℓ → Ξ₀ ≤ e2 * ℓ ^ 2 →
      Real.log (2 + e2) ≤ κ₀ * ℓ ^ (1 / 3 : ℝ) → Rel e2 ℓ ≤ ε := by
  -- step 2 of Table `tab:choices`: s, ν, η, M depend only on ε
  obtain ⟨ν, hν1, hν⟩ : ∃ ν : ℕ, 1 ≤ ν ∧ 1 / (ν : ℝ) ^ 2 ≤ ε / 16 := by
    obtain ⟨n, hn⟩ := exists_nat_gt (16 / ε)
    have hn0 : (0 : ℝ) < n := lt_trans (by positivity) hn
    have hn1 : 1 ≤ n := by exact_mod_cast hn0
    refine ⟨n, hn1, ?_⟩
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have h2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    have h3 : 16 / ε ≤ (n : ℝ) ^ 2 := by linarith
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hε] at h3
    linarith
  obtain ⟨s, hs0, hs1, hs⟩ : ∃ s : ℕ, s₀ ≤ s ∧ 1 ≤ s ∧ C * Real.log (2 + s) / s ≤ ε / 16 := by
    have h := (tendsto_log_div.const_mul C)
    simp only [mul_zero] at h
    have ev := h.eventually (ge_mem_nhds (show (0 : ℝ) < ε / 16 by positivity))
    obtain ⟨s, hs, hs0, hs1⟩ := (ev.and ((eventually_ge_atTop s₀).and (eventually_ge_atTop 1))).exists
    exact ⟨s, hs0, hs1, by rw [mul_div_assoc]; exact hs⟩
  set η : ℝ := ε / 16 with hηdef
  have hη : 0 < η := by positivity
  have hη1 : η < 1 := by rw [hηdef]; linarith
  set M : ℝ := 1 + 16 * C / ε with hMdef
  have hM1 : 1 ≤ M := by
    have : 0 ≤ 16 * C / ε := by positivity
    linarith
  have hM0 : 0 < M := by linarith
  have hMc : C * (1 / M ^ 2) ≤ ε / 16 := by
    have h1 : 16 * C / ε ≤ M := by rw [hMdef]; linarith
    have h2 : M ≤ M ^ 2 := by nlinarith
    have h3 : 16 * C ≤ ε * M ^ 2 := by
      rw [div_le_iff₀ hε] at h1
      nlinarith
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    linarith
  -- step 3: Ξ₀, κ₀, ℓ₀
  set Ξ₀ : ℝ := 8 * C * M ^ 3 / ε with hΞdef
  have hΞ : 0 < Ξ₀ := by positivity
  set A : ℝ := C * ((ν : ℝ) ^ 2 * M ^ 3 * (s : ℝ) ^ 2 * C / η) with hAdef
  have hν0 : (0 : ℝ) < ν := by exact_mod_cast hν1
  have hs0' : (0 : ℝ) < s := by exact_mod_cast hs1
  have hA : 0 < A := by positivity
  set κ : ℝ := min (1 / 10) (ε / (80 * A)) with hκdef
  have hκ : 0 < κ := by
    rw [hκdef]; exact lt_min (by norm_num) (by positivity)
  have hκ10 : 10 * κ ≤ 1 := by
    have : κ ≤ 1 / 10 := min_le_left _ _
    linarith
  have hκA : A * (10 * κ) ≤ ε / 8 := by
    have : κ ≤ ε / (80 * A) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith
  have hpow6 : A * (10 * κ) ^ 6 ≤ ε / 8 := by
    have : (10 * κ) ^ 6 ≤ 10 * κ := by
      have h0 : 0 ≤ 10 * κ := by positivity
      exact pow_le_of_le_one h0 hκ10 (by norm_num)
    calc A * (10 * κ) ^ 6 ≤ A * (10 * κ) := mul_le_mul_of_nonneg_left this hA.le
      _ ≤ ε / 8 := hκA
  -- large `ℓ`
  have hlog : ∀ᶠ ℓ : ℝ in atTop, Real.log (1 + ℓ) ≤ κ * ℓ ^ (1 / 3 : ℝ) := by
    -- `log (1 + ℓ) ≤ log (2 ℓ) = log 2 + log ℓ`
    have h1 := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 3 by norm_num)).def
      (show 0 < κ / 2 by positivity)
    have h2 : Tendsto (fun ℓ : ℝ => ℓ ^ (1 / 3 : ℝ)) atTop atTop :=
      tendsto_rpow_atTop (by norm_num)
    have h3 := h2.eventually_ge_atTop (2 * Real.log 2 / κ)
    filter_upwards [h1, h3, eventually_ge_atTop (1 : ℝ)] with ℓ h1 h3 hℓ
    have hp : 0 < ℓ ^ (1 / 3 : ℝ) := by positivity
    have hlogℓ : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ
    rw [Real.norm_of_nonneg hlogℓ, Real.norm_of_nonneg hp.le] at h1
    have h4 : Real.log (1 + ℓ) ≤ Real.log 2 + Real.log ℓ := by
      rw [← Real.log_mul (by norm_num) (by positivity)]
      exact Real.log_le_log (by positivity) (by linarith)
    have h5 : 2 * Real.log 2 ≤ κ * ℓ ^ (1 / 3 : ℝ) := by
      rw [div_le_iff₀ hκ] at h3
      linarith
    linarith
  have hsmall : ∀ᶠ ℓ : ℝ in atTop, 1 + (s : ℝ) ≤ κ * ℓ ^ (1 / 3 : ℝ) := by
    have h2 : Tendsto (fun ℓ : ℝ => ℓ ^ (1 / 3 : ℝ)) atTop atTop :=
      tendsto_rpow_atTop (by norm_num)
    filter_upwards [h2.eventually_ge_atTop ((1 + (s : ℝ)) / κ)] with ℓ h
    rw [div_le_iff₀ hκ] at h
    linarith
  obtain ⟨ℓ₁, hℓ₁⟩ := eventually_atTop.1 (hlog.and hsmall)
  set ℓ₀ : ℝ := max (max ℓ₁ 1) (s : ℝ) with hℓ₀def
  have hℓ₀ : 0 < ℓ₀ := lt_of_lt_of_le one_pos ((le_max_right _ _).trans (le_max_left _ _))
  refine ⟨ℓ₀, Ξ₀, κ, hℓ₀, hΞ, hκ, ?_⟩
  intro e2 ℓ he hℓ hΞℓ hκℓ
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le hℓ₀ hℓ
  have hℓ1 : ℓ₁ ≤ ℓ := ((le_max_left _ _).trans (le_max_left _ _)).trans hℓ
  have hℓs : (s : ℝ) ≤ ℓ := (le_max_right _ _).trans hℓ
  obtain ⟨hL, hS⟩ := hℓ₁ ℓ hℓ1
  have hsM : (s : ℝ) ≤ M * ℓ := hℓs.trans (le_mul_of_one_le_left hℓ0.le hM1)
  have ha : 1 / (ν : ℝ) ^ 2 + η + C * Real.log (2 + s) / s ≤ 3 * ε / 16 := by
    rw [hηdef]; linarith
  have hrel' := hrel e2 ℓ he hℓ0 s ν η M hs0 hs1 hν1 hη hη1 hM1 hsM (by linarith)
  -- the term `M³/Ξ`
  have hX : 0 < e2 * ℓ ^ 2 := by positivity
  have hT1 : C * (M ^ 3 / (e2 * ℓ ^ 2)) ≤ ε / 8 := by
    rw [mul_div_assoc', div_le_iff₀ hX]
    rw [hΞdef, div_le_iff₀ hε] at hΞℓ
    linarith
  -- the term with `K_V`
  set p : ℝ := ℓ ^ (1 / 3 : ℝ) with hpdef
  have hp : 0 < p := by positivity
  have hp6 : p ^ 6 = ℓ ^ 2 := by
    rw [hpdef, ← Real.rpow_natCast, ← Real.rpow_mul hℓ0.le, ← Real.rpow_natCast]
    norm_num
  set L : ℝ := Real.log (1 + e2 * (e2 * ℓ ^ 7)) with hLdef
  have hLnn : 0 ≤ L := Real.log_nonneg (by
    have : 0 ≤ e2 * (e2 * ℓ ^ 7) := by positivity
    linarith)
  have hLb : L ≤ 9 * κ * p := by
    have := log_bound he hℓ0
    linarith
  have hsum : 1 + (s : ℝ) + L ≤ 10 * κ * p := by linarith
  have hsum6 : (1 + (s : ℝ) + L) ^ 6 ≤ (10 * κ) ^ 6 * ℓ ^ 2 := by
    calc (1 + (s : ℝ) + L) ^ 6 ≤ (10 * κ * p) ^ 6 :=
          pow_le_pow_left₀ (by positivity) hsum 6
      _ = (10 * κ) ^ 6 * ℓ ^ 2 := by rw [mul_pow, hp6]
  have hT2 : C * ((ν : ℝ) ^ 2 * M ^ 3 * s ^ 2 * (C * (1 + s + L) ^ 6) / (η * ℓ ^ 2)) ≤ ε / 8 := by
    have hℓ2 : 0 < ℓ ^ 2 := by positivity
    have e : C * ((ν : ℝ) ^ 2 * M ^ 3 * s ^ 2 * (C * (1 + s + L) ^ 6) / (η * ℓ ^ 2))
        = A * ((1 + s + L) ^ 6 / ℓ ^ 2) := by
      rw [hAdef]; field_simp
    rw [e]
    have : (1 + (s : ℝ) + L) ^ 6 / ℓ ^ 2 ≤ (10 * κ) ^ 6 := by
      rw [div_le_iff₀ hℓ2]; exact hsum6
    calc A * ((1 + s + L) ^ 6 / ℓ ^ 2) ≤ A * (10 * κ) ^ 6 :=
          mul_le_mul_of_nonneg_left this hA.le
      _ ≤ ε / 8 := hpow6
  have htot : C * (M ^ 3 / (e2 * ℓ ^ 2) + 1 / M ^ 2
      + (ν : ℝ) ^ 2 * M ^ 3 * s ^ 2 * (C * (1 + s + L) ^ 6) / (η * ℓ ^ 2))
      = C * (M ^ 3 / (e2 * ℓ ^ 2)) + C * (1 / M ^ 2)
        + C * ((ν : ℝ) ^ 2 * M ^ 3 * s ^ 2 * (C * (1 + s + L) ^ 6) / (η * ℓ ^ 2)) := by ring
  rw [htot] at hrel'
  linarith

end PauliFierzUV.PaperI
