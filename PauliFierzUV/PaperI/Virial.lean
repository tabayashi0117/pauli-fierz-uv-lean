import Mathlib

/-!
# Paper I, Corollary 8.4 (`cor:virial`, virial-type partition of the energy)

Paper I is arXiv:2610.34122. With `H_c := c𝒯 + H_f`, scaling gives
`inf σ(H_c) = c⁻¹ E₀(α, cΛ) = (1 + o(1)) c^(5/7) E₀(α, Λ)` for each fixed `c ∈ [½, 3/2]`, and for
almost minimising states `Ψ` (`⟨Ψ, HΨ⟩ ≤ (1+ε')E₀`, `ε' → 0`),
`inf σ(H_c) ≤ (1 + ε')E₀ + (c - 1)⟨𝒯⟩`. The corollary concludes `⟨𝒯⟩/E₀ → 5/7` and
`⟨H_f⟩/E₀ → 2/7`.

This file proves the limit argument (the "standard scaling argument" of the proof) for abstract
real sequences along an arbitrary filter: the inputs are exactly the three displayed facts,
taken as hypotheses. It also checks the exponent `c⁻¹ (cΛ)^(12/7) = c^(5/7) Λ^(12/7)` and
`ℓ(cΛ) = c^(1/7) ℓ(Λ)`.
-/

open Real Filter Topology

namespace PauliFierzUV.PaperI

/-- `c⁻¹ (cΛ)^(12/7) = c^(5/7) Λ^(12/7)`: the leading term of `c⁻¹ E₀(α, cΛ)`. -/
theorem virial_exponent {c Λ : ℝ} (hc : 0 < c) (hΛ : 0 < Λ) :
    c⁻¹ * (c * Λ) ^ (12 / 7 : ℝ) = c ^ (5 / 7 : ℝ) * Λ ^ (12 / 7 : ℝ) := by
  rw [Real.mul_rpow hc.le hΛ.le, ← mul_assoc, ← Real.rpow_neg_one, ← Real.rpow_add hc]
  norm_num

/-- `ℓ = (Λ/(πe²))^(1/7)` changes by the factor `c^(1/7)` under `Λ ↦ cΛ`. -/
theorem ell_scaling {c Λ e : ℝ} (hc : 0 < c) (hΛ : 0 < Λ) (he : 0 < e) :
    (c * Λ / (π * e ^ 2)) ^ (1 / 7 : ℝ) = c ^ (1 / 7 : ℝ) * (Λ / (π * e ^ 2)) ^ (1 / 7 : ℝ) := by
  rw [mul_div_assoc, Real.mul_rpow hc.le (by positivity)]

/-- **Corollary `cor:virial`, limit argument.** Let `E, T, ε' : ι → ℝ` and `Ec : ℝ → ι → ℝ`
(`Ec c = inf σ(H_c)`) along a filter `l`, with `E > 0`, `ε' → 0`,
`Ec c / E → c^(5/7)` for each `c ∈ [½, 3/2]`, and `Ec c ≤ (1+ε')E + (c-1)T`.
Then `T/E → 5/7`. -/
theorem virial_kinetic {ι : Type*} {l : Filter ι} {E T ε' : ι → ℝ} {Ec : ℝ → ι → ℝ}
    (hE : ∀ i, 0 < E i) (hε : Tendsto ε' l (𝓝 0))
    (hlim : ∀ c ∈ Set.Icc (1 / 2 : ℝ) (3 / 2),
      Tendsto (fun i => Ec c i / E i) l (𝓝 (c ^ (5 / 7 : ℝ))))
    (hvar : ∀ c ∈ Set.Icc (1 / 2 : ℝ) (3 / 2), ∀ i, Ec c i ≤ (1 + ε' i) * E i + (c - 1) * T i) :
    Tendsto (fun i => T i / E i) l (𝓝 (5 / 7)) := by
  -- the derivative of `c ↦ c^(5/7)` at `1`
  have hder : HasDerivAt (fun c : ℝ => c ^ (5 / 7 : ℝ)) (5 / 7) 1 := by
    have := Real.hasDerivAt_rpow_const (x := 1) (p := 5 / 7) (Or.inl one_ne_zero)
    simpa using this
  have hR := hder.tendsto_slope_zero_right
  have hL := hder.tendsto_slope_zero_left
  simp only [Real.one_rpow, smul_eq_mul] at hR hL
  rw [tendsto_order]
  constructor
  · -- lower bound, with `c = 1 + δ`
    intro a ha
    obtain ⟨δ, hδa, hδ1, hδ0⟩ :=
      ((hR.eventually (lt_mem_nhds ha)).and
        (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num))).exists
    have hδ0' : 0 < δ := hδ1
    have hc : 1 + δ ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) := ⟨by linarith, by linarith⟩
    -- `(Ec/E - 1 - ε')/δ → ((1+δ)^(5/7) - 1)/δ > a`
    have ht : Tendsto (fun i => (Ec (1 + δ) i / E i - 1 - ε' i) / δ) l
        (𝓝 (((1 + δ) ^ (5 / 7 : ℝ) - 1 - 0) / δ)) :=
      (((hlim _ hc).sub tendsto_const_nhds).sub hε).div_const δ
    have hgt : a < ((1 + δ) ^ (5 / 7 : ℝ) - 1 - 0) / δ := by
      rw [sub_zero, div_eq_inv_mul]; exact hδa
    filter_upwards [ht.eventually (lt_mem_nhds hgt)] with i hi
    have h1 := hvar _ hc i
    have hEi := hE i
    have : (Ec (1 + δ) i / E i - 1 - ε' i) / δ ≤ T i / E i := by
      rw [div_le_iff₀ hδ0', div_sub' hEi.ne', div_sub' hEi.ne', div_mul_eq_mul_div,
        div_le_div_iff_of_pos_right hEi]
      nlinarith
    linarith
  · -- upper bound, with `c = 1 - δ`
    intro b hb
    obtain ⟨t, htb, ht1, ht0⟩ :=
      ((hL.eventually (gt_mem_nhds hb)).and
        (Ioo_mem_nhdsLT (show (-1 / 2 : ℝ) < 0 by norm_num))).exists
    set δ := -t with hδ
    have hδ0 : 0 < δ := by linarith
    have hc : 1 - δ ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) := ⟨by linarith, by linarith⟩
    have ht' : Tendsto (fun i => (1 + ε' i - Ec (1 - δ) i / E i) / δ) l
        (𝓝 ((1 + 0 - (1 - δ) ^ (5 / 7 : ℝ)) / δ)) :=
      ((tendsto_const_nhds.add hε).sub (hlim _ hc)).div_const δ
    have hlt : (1 + 0 - (1 - δ) ^ (5 / 7 : ℝ)) / δ < b := by
      have e : (1 + 0 - (1 - δ) ^ (5 / 7 : ℝ)) / δ = t⁻¹ * ((1 + t) ^ (5 / 7 : ℝ) - 1) := by
        rw [hδ, show (1 : ℝ) - -t = 1 + t by ring]
        field_simp
        ring
      rw [e]; exact htb
    filter_upwards [ht'.eventually (gt_mem_nhds hlt)] with i hi
    have h1 := hvar _ hc i
    have hEi := hE i
    have : T i / E i ≤ (1 + ε' i - Ec (1 - δ) i / E i) / δ := by
      rw [le_div_iff₀ hδ0, sub_div' hEi.ne', div_mul_eq_mul_div,
        div_le_div_iff_of_pos_right hEi]
      nlinarith
    linarith

/-- **Corollary `cor:virial`, second part**: if moreover `E ≤ ⟨H⟩ ≤ (1+ε')E` and
`⟨H_f⟩ = ⟨H⟩ - ⟨𝒯⟩`, then `⟨H_f⟩/E → 2/7`. -/
theorem virial_field {ι : Type*} {l : Filter ι} {E T ε' Hexp : ι → ℝ}
    (hE : ∀ i, 0 < E i) (hε : Tendsto ε' l (𝓝 0))
    (hT : Tendsto (fun i => T i / E i) l (𝓝 (5 / 7)))
    (hH1 : ∀ i, E i ≤ Hexp i) (hH2 : ∀ i, Hexp i ≤ (1 + ε' i) * E i) :
    Tendsto (fun i => (Hexp i - T i) / E i) l (𝓝 (2 / 7)) := by
  have hHE : Tendsto (fun i => Hexp i / E i) l (𝓝 1) := by
    have hup : Tendsto (fun i => 1 + ε' i) l (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).add hε
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup ?_ ?_
    · intro i; rw [le_div_iff₀ (hE i)]; simpa using hH1 i
    · intro i; rw [div_le_iff₀ (hE i)]; exact hH2 i
  have := hHE.sub hT
  norm_num at this
  refine this.congr fun i => ?_
  rw [sub_div]

end PauliFierzUV.PaperI
