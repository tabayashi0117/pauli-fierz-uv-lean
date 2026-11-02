import PauliFierzUV.PaperII.PartIConstants

/-!
# Paper II, Part I: the two asymptotic consequences of Theorem `thm:partI`

Paper II is arXiv:2610.34125. Both results below are derived **from** Theorem `thm:partI`,
which is taken as a hypothesis (`h ≥ 1 + 2x_K/(1+ρ_K)` for the admissible bands `0 < K ≤ Λ`,
i.e. `0 < σ ≤ λ/2` with `σ = K/(2m)` and `λ = Λ/m`).

* Corollary 3.3 (`cor:partI-first-order`): `liminf_{α→0} (h-1)/α ≥ (8/3π) log(1 + λ/2)`
  (take `K = Λ`, i.e. `σ = λ/2`).
* Remark 3.4 (`rem:partI-values`) (ii): `liminf_{α→∞} h/√α ≥ (4/3π) √(6/π)`
  (take `σ = √(6/(πα))`). This file also proves the elementary inequalities used there:
  `log(1+σ) ≥ σ - σ²/2`, `L(σ) ≤ (2/3) σ^(3/2)`, `t_K ≤ 1/(2-σ)` and `q_K ≤ 2σ`.

The `liminf`s are in `EReal`, and `h` is any real function of `α` satisfying the hypothesis.
-/

open Real Filter Topology intervalIntegral

namespace PauliFierzUV.PaperII

/-- `log(1+σ) ≥ σ - σ²/2` for `σ ≥ 0`. -/
lemma log_one_add_ge {σ : ℝ} (hσ : 0 ≤ σ) : σ - σ ^ 2 / 2 ≤ log (1 + σ) := by
  set f : ℝ → ℝ := fun s => log (1 + s) - s + s ^ 2 / 2 with hf
  have hd : ∀ x : ℝ, 0 ≤ x → HasDerivAt f (x ^ 2 / (1 + x)) x := by
    intro x hx
    have h1 := ((hasDerivAt_id' x).const_add 1).log (by linarith)
    have h := (h1.sub (hasDerivAt_id' x)).add ((hasDerivAt_pow 2 x).div_const 2)
    convert h using 1
    field_simp
    ring
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · intro x hx
      exact (hd x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      exact (hd x (le_of_lt hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hd x (le_of_lt hx)).deriv]
      have : (0 : ℝ) < 1 + x := by linarith [Set.mem_Ioi.1 hx]
      positivity
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hσ) hσ
  simp only [hf, add_zero, Real.log_one] at this
  linarith

lemma intervalIntegrable_Lintegrand {σ : ℝ} (hσ : 0 ≤ σ) :
    IntervalIntegrable (fun t : ℝ => √(t / (1 + t))) MeasureTheory.volume 0 σ := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  rw [Set.uIcc_of_le hσ] at ht
  have : 1 + t ≠ 0 := by linarith [ht.1]
  exact (Real.continuous_sqrt.continuousAt.comp
    (continuousAt_id.div (continuousAt_const.add continuousAt_id) this)).continuousWithinAt

lemma Lfun_nonneg {σ : ℝ} (hσ : 0 < σ) : 0 ≤ Lfun σ := by
  rw [← integral_Lfun hσ]
  exact intervalIntegral.integral_nonneg hσ.le fun t _ => Real.sqrt_nonneg _

/-- `L(σ) ≤ ∫₀^σ √t dt = (2/3) σ^(3/2)`. -/
lemma Lfun_le {σ : ℝ} (hσ : 0 < σ) : Lfun σ ≤ 2 / 3 * σ ^ (3 / 2 : ℝ) := by
  rw [← integral_Lfun hσ]
  calc ∫ t in (0 : ℝ)..σ, √(t / (1 + t))
      ≤ ∫ t in (0 : ℝ)..σ, t ^ (1 / 2 : ℝ) := by
        apply intervalIntegral.integral_mono_on hσ.le (intervalIntegrable_Lintegrand hσ.le)
          (intervalIntegral.intervalIntegrable_rpow' (by norm_num))
        intro t ht
        rw [← Real.sqrt_eq_rpow]
        exact Real.sqrt_le_sqrt (div_le_self ht.1 (by linarith [ht.1]))
    _ = 2 / 3 * σ ^ (3 / 2 : ℝ) := by
        rw [integral_rpow (Or.inl (by norm_num))]
        rw [Real.zero_rpow (by norm_num)]
        norm_num
        ring

lemma Lfun_sq_le {σ : ℝ} (hσ : 0 < σ) : Lfun σ ^ 2 ≤ 4 / 9 * σ ^ 3 := by
  have h := pow_le_pow_left₀ (Lfun_nonneg hσ) (Lfun_le hσ) 2
  have e : (σ ^ (3 / 2 : ℝ)) ^ 2 = σ ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hσ.le]; norm_num
  calc Lfun σ ^ 2 ≤ (2 / 3 * σ ^ (3 / 2 : ℝ)) ^ 2 := h
    _ = 4 / 9 * σ ^ 3 := by rw [mul_pow, e]; norm_num

/-- `q_K ≤ 2σ/(1+σ) ≤ 2σ` (Remark `rem:partI-values` (ii)). -/
lemma qK_le {σ : ℝ} (hσ : 0 < σ) : qK σ ≤ 2 * σ := by
  have hl : 0 < log (1 + σ) := Real.log_pos (by linarith)
  have hls : log (1 + σ) ≤ σ := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + σ by linarith); linarith
  unfold qK
  have e : 2 / log (1 + σ) * (log (1 + σ) - σ / (1 + σ))
      = 2 - 2 * σ / ((1 + σ) * log (1 + σ)) := by field_simp
  rw [e]
  have h1 : 2 * σ / ((1 + σ) * σ) ≤ 2 * σ / ((1 + σ) * log (1 + σ)) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left hls (by linarith))
  have h2 : 2 * σ / ((1 + σ) * σ) = 2 / (1 + σ) := by field_simp
  rw [h2] at h1
  have h3 : 2 - 2 / (1 + σ) ≤ 2 * σ := by
    rw [sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ (by linarith)]
    nlinarith
  linarith

/-- With `π α σ² = 6` and `0 < σ ≤ 1`: `t_K ≤ 1/(2-σ)` (Remark `rem:partI-values` (ii)). -/
lemma tK_le {α σ : ℝ} (hα : 0 < α) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hs : π * α * σ ^ 2 = 6) :
    tK α σ ≤ 1 / (2 - σ) := by
  have hlow := log_one_add_ge hσ.le
  have hl : 0 < log (1 + σ) := Real.log_pos (by linarith)
  have hL := Lfun_sq_le hσ
  have h2s : 0 < 2 - σ := by linarith
  unfold tK
  rw [le_div_iff₀ h2s]
  have hpa : 0 < π * α := by positivity
  have key : 3 * π * α * Lfun σ ^ 2 * (2 - σ) ≤ 8 * σ * (2 - σ) := by
    calc 3 * π * α * Lfun σ ^ 2 * (2 - σ) ≤ 3 * π * α * (4 / 9 * σ ^ 3) * (2 - σ) := by
          gcongr
      _ = 4 / 3 * (π * α * σ ^ 2) * σ * (2 - σ) := by ring
      _ = 8 * σ * (2 - σ) := by rw [hs]; ring
  have hlg : 8 * σ * (2 - σ) ≤ 16 * log (1 + σ) := by nlinarith
  rw [show 3 * π * α / (16 * log (1 + σ)) * Lfun σ ^ 2 * (2 - σ)
      = (3 * π * α * Lfun σ ^ 2 * (2 - σ)) / (16 * log (1 + σ)) by ring,
    div_le_one (by positivity)]
  linarith

/-! ### Corollary `cor:partI-first-order` -/

/-- **Corollary `cor:partI-first-order`** from `thm:partI` with `K = Λ` (`σ = λ/2`):
for every `c < (8/3π) log(1+σ)`, eventually as `α → 0⁺`, `(h(α) - 1)/α ≥ c`. -/
theorem partI_first_order {σ : ℝ} (hσ : 0 < σ) {H : ℝ → ℝ}
    (hH : ∀ α, 0 < α → partIBound α σ ≤ H α) :
    ∀ c : ℝ, c < 8 / (3 * π) * log (1 + σ) → ∀ᶠ α in 𝓝[>] 0, c ≤ (H α - 1) / α := by
  intro c hc
  set a : ℝ := 2 * xK 1 σ with ha
  have hae : a = 8 / (3 * π) * log (1 + σ) := by rw [ha]; unfold xK; ring
  set q := qK σ
  set t := tK 1 σ
  have ht0 : 0 ≤ t := tK_nonneg zero_le_one hσ
  set g : ℝ → ℝ := fun α => a / (1 + (2 * √(q * (α * t)) + 2 * (α * t))) with hg
  have hgc : ContinuousAt g 0 := by
    apply ContinuousAt.div continuousAt_const (by fun_prop)
    simp
  have hg0 : g 0 = a := by simp [hg]
  have htend : Tendsto g (𝓝[>] 0) (𝓝 a) := by
    rw [← hg0]; exact hgc.tendsto.mono_left nhdsWithin_le_nhds
  have hev := htend.eventually_const_lt (show c < a by rw [hae]; exact hc)
  filter_upwards [hev, self_mem_nhdsWithin] with α hα hαpos
  have hαpos' : 0 < α := hαpos
  have hb := hH α hαpos'
  unfold partIBound at hb
  have hρ : ρK α σ = 2 * √(q * (α * t)) + 2 * (α * t) := by
    unfold ρK; rw [tK_eq α σ]
  have hρ0 := ρK_nonneg hαpos'.le hσ
  rw [hρ] at hb hρ0
  rw [xK_eq α σ] at hb
  rw [le_div_iff₀ hαpos']
  have : c * α ≤ 2 * (α * xK 1 σ) / (1 + (2 * √(q * (α * t)) + 2 * (α * t))) := by
    rw [le_div_iff₀ (by linarith)]
    have hga : c < a / (1 + (2 * √(q * (α * t)) + 2 * (α * t))) := hα
    rw [lt_div_iff₀ (by linarith)] at hga
    nlinarith
  linarith

/-- `cor:partI-first-order` in `liminf` form:
`liminf_{α→0⁺} (h(α)-1)/α ≥ (8/3π) log(1+σ)`, with `σ = λ/2`. -/
theorem partI_first_order_liminf {σ : ℝ} (hσ : 0 < σ) {H : ℝ → ℝ}
    (hH : ∀ α, 0 < α → partIBound α σ ≤ H α) :
    ((8 / (3 * π) * log (1 + σ) : ℝ) : EReal)
      ≤ liminf (fun α => (((H α - 1) / α : ℝ) : EReal)) (𝓝[>] 0) :=
  le_liminf_ereal_of_forall (partI_first_order hσ hH)

/-! ### Remark `rem:partI-values` (ii) -/

/-- **Remark `rem:partI-values` (ii)** from `thm:partI`: at fixed `λ > 0`, for every
`c < (4/3π) √(6/π)`, eventually as `α → ∞`, `h(α)/√α ≥ c`. The hypothesis is `thm:partI` for
all bands `0 < σ ≤ λ/2`. -/
theorem partI_large_coupling {lam : ℝ} (hlam : 0 < lam) {H : ℝ → ℝ}
    (hH : ∀ α, 0 < α → ∀ σ, 0 < σ → σ ≤ lam / 2 → partIBound α σ ≤ H α) :
    ∀ c : ℝ, c < 4 / (3 * π) * √(6 / π) → ∀ᶠ α in atTop, c ≤ H α / √α := by
  intro c hc
  have hpi := Real.pi_pos
  set k : ℝ := 8 / (3 * π) * √(6 / π) with hk
  set R : ℝ → ℝ := fun s => 2 * √(2 * s / (2 - s)) + 2 / (2 - s) with hR
  set φ : ℝ → ℝ := fun s => k * (1 - s / 2) / (1 + R s) with hφ
  have hφc : ContinuousAt φ 0 := by
    have h2 : ContinuousAt (fun s : ℝ => 2 - s) 0 := by fun_prop
    have hne : (2 : ℝ) - 0 ≠ 0 := by norm_num
    apply ContinuousAt.div (by fun_prop)
    · exact continuousAt_const.add
        ((continuousAt_const.mul (Real.continuous_sqrt.continuousAt.comp
          ((continuousAt_const.mul continuousAt_id).div h2 hne))).add
          (continuousAt_const.div h2 hne))
    · simp [hR]
  have hφ0 : φ 0 = 4 / (3 * π) * √(6 / π) := by
    simp [hφ, hR, hk]; ring
  set σf : ℝ → ℝ := fun α => √(6 / (π * α)) with hσf
  have hσt : Tendsto σf atTop (𝓝 0) := by
    have h1 : Tendsto (fun α : ℝ => 6 / (π * α)) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := (6 : ℝ))).div_atTop
        (tendsto_id.const_mul_atTop hpi)
      simpa using this
    have := (Real.continuous_sqrt.tendsto 0).comp h1
    rw [Real.sqrt_zero] at this
    exact this
  have hev : ∀ᶠ α in atTop, c < φ (σf α) :=
    (((hφc.tendsto).comp hσt)).eventually_const_lt (by rw [hφ0]; exact hc)
  filter_upwards [hev, eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (6 / π),
    eventually_ge_atTop (24 / (π * lam ^ 2))] with α hcφ hα hα1 hα2
  -- the choice `σ = √(6/(πα))`
  set s := σf α with hs
  have hpa : 0 < π * α := by positivity
  have hs0 : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hs2 : s ^ 2 = 6 / (π * α) := Real.sq_sqrt (by positivity)
  have hpas : π * α * s ^ 2 = 6 := by rw [hs2]; field_simp
  have hs1 : s ≤ 1 := by
    have : 6 / (π * α) ≤ 1 := by
      rw [div_le_one hpa]
      have := (div_le_iff₀ hpi).1 hα1
      linarith
    nlinarith
  have hslam : s ≤ lam / 2 := by
    have : 6 / (π * α) ≤ (lam / 2) ^ 2 := by
      rw [div_le_iff₀ hpa]
      have := (div_le_iff₀ (by positivity)).1 hα2
      nlinarith
    nlinarith
  have hb := hH α hα s hs0 hslam
  unfold partIBound at hb
  -- the elementary bounds
  have h2s : 0 < 2 - s := by linarith
  have hlog := log_one_add_ge hs0.le
  have ht := tK_le hα hs0 hs1 hpas
  have ht0 := tK_nonneg hα.le hs0
  have hq := qK_le hs0
  have hρ : ρK α s ≤ R s := by
    unfold ρK
    simp only [hR]
    have hqt : qK s * tK α s ≤ 2 * s / (2 - s) := by
      calc qK s * tK α s ≤ 2 * s * tK α s := mul_le_mul_of_nonneg_right hq ht0
        _ ≤ 2 * s * (1 / (2 - s)) := mul_le_mul_of_nonneg_left ht (by linarith)
        _ = 2 * s / (2 - s) := by ring
    have := Real.sqrt_le_sqrt hqt
    have e2 : 2 / (2 - s) = 2 * (1 / (2 - s)) := by ring
    linarith
  have hρ0 := ρK_nonneg hα.le hs0
  have hR0 : 0 ≤ R s := by simp only [hR]; positivity
  have hx : 8 * α / (3 * π) * (s * (1 - s / 2)) ≤ 2 * xK α s := by
    unfold xK
    have : s * (1 - s / 2) ≤ log (1 + s) := by nlinarith
    rw [show 2 * (4 * α / (3 * π) * log (1 + s)) = 8 * α / (3 * π) * log (1 + s) by ring]
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hm : 0 ≤ s * (1 - s / 2) := by nlinarith
  have hH1 : 1 + 8 * α / (3 * π) * (s * (1 - s / 2)) / (1 + R s) ≤ H α := by
    have : 8 * α / (3 * π) * (s * (1 - s / 2)) / (1 + R s) ≤ 2 * xK α s / (1 + ρK α s) := by
      calc 8 * α / (3 * π) * (s * (1 - s / 2)) / (1 + R s)
          ≤ 8 * α / (3 * π) * (s * (1 - s / 2)) / (1 + ρK α s) :=
            div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
        _ ≤ 2 * xK α s / (1 + ρK α s) := div_le_div_of_nonneg_right hx (by linarith)
    linarith
  -- divide by `√α`
  have hsa : 0 < √α := Real.sqrt_pos.2 hα
  have hsas : √α * s = √(6 / π) := by
    rw [hs, hσf, ← Real.sqrt_mul hα.le]
    congr 1; field_simp
  have hφs : φ s = 8 * α / (3 * π) * (s * (1 - s / 2)) / (1 + R s) / √α := by
    simp only [hφ, hk]
    rw [← hsas]
    have hd : α / √α = √α := Real.div_sqrt
    rw [show 8 * α / (3 * π) * (s * (1 - s / 2)) / (1 + R s) / √α
        = 8 / (3 * π) * (α / √α) * s * (1 - s / 2) / (1 + R s) by ring, hd]
    ring
  have : φ s ≤ H α / √α := by
    rw [hφs]
    apply div_le_div_of_nonneg_right _ hsa.le
    linarith
  linarith

/-- Remark `rem:partI-values` (ii) in `liminf` form:
`liminf_{α→∞} h(α)/√α ≥ (4/3π) √(6/π) = 0.5865…`. -/
theorem partI_large_coupling_liminf {lam : ℝ} (hlam : 0 < lam) {H : ℝ → ℝ}
    (hH : ∀ α, 0 < α → ∀ σ, 0 < σ → σ ≤ lam / 2 → partIBound α σ ≤ H α) :
    ((4 / (3 * π) * √(6 / π) : ℝ) : EReal)
      ≤ liminf (fun α => ((H α / √α : ℝ) : EReal)) atTop :=
  le_liminf_ereal_of_forall (partI_large_coupling hlam hH)

end PauliFierzUV.PaperII
