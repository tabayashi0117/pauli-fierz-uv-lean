import Mathlib

/-!
# Paper II, Remark 10.4 (`rem:budget`, exponent budget for the bad events)

Paper II is arXiv:2610.34125. Table `tab:budget` lists, for each bad event, a polynomial factor
`C ℓ^a` that multiplies its probability bound `ℓ^(-p)`, and the power `t` to which the product
must be small. With `D = 2`, the table chooses

* `κ_p* := D + 9 = 11` (the events in `prop:expect`),
* `p_bad := κ_p* + 8 = 19` (the events `S_M`, `B_θ` inside `prop:shell`),
* `p_bad + 2` for `Γ'_R ⊂ B_θ` (inside `prop:SMexpl`),
* `7 c_ev K ≥ p_bad + 9` for `B_θ` (`prop:events`, with `λ^(-c_ev K) ≍ ℓ^(-7 c_ev K)`).

This file checks the exponent arithmetic of the table: each row closes with one spare power of
`ℓ`, which absorbs the constant `C` once `ℓ ≥ C` (`absorb`). It checks only this arithmetic; the
polynomial factors and probability bounds themselves are the content of the cited propositions
and are not formalized.
-/

namespace PauliFierzUV.PaperII.Budget

/-- A row closes: if `a - p ≤ -t - 1`, then `C ℓ^a · ℓ^(-p) ≤ ℓ^(-t)` for `ℓ ≥ max 1 C`. -/
theorem absorb {C ℓ a p t : ℝ} (hC : 0 < C) (hℓ : max 1 C ≤ ℓ) (h : a - p ≤ -t - 1) :
    C * ℓ ^ a * ℓ ^ (-p) ≤ ℓ ^ (-t) := by
  have hℓ1 : 1 ≤ ℓ := (le_max_left _ _).trans hℓ
  have hℓC : C ≤ ℓ := (le_max_right _ _).trans hℓ
  have hℓ0 : 0 < ℓ := by linarith
  have e : C * ℓ ^ a * ℓ ^ (-p) = C * ℓ ^ (a - p) := by
    rw [mul_assoc, ← Real.rpow_add hℓ0]; ring_nf
  rw [e]
  calc C * ℓ ^ (a - p) ≤ C * ℓ ^ (-t - 1) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hℓ1 h) hC.le
    _ = C * ℓ ^ (-t) * ℓ⁻¹ := by
        rw [Real.rpow_sub hℓ0, Real.rpow_one]; ring
    _ ≤ ℓ * ℓ ^ (-t) * ℓ⁻¹ := by gcongr
    _ = ℓ ^ (-t) := by field_simp

/-- `D` of `prop:global` for the edge width `w = R_c`. -/
def D : ℝ := 2
/-- `κ_p* := D + 9`. -/
def kappaStar : ℝ := D + 9
/-- `p_bad := κ_p* + 8`. -/
def pBad : ℝ := kappaStar + 8

/-- **The rows of Table `tab:budget` close** (each with one spare power of `ℓ`):

1. `𝒢'ᶜ`, field part: `K_G ℓ^D · ℓ^(-κ_p*) ≲ ℓ^(-1)`;
2. `𝒢'ᶜ`, kinetic part: `c K_G ℓ^D · ℓ^(-κ_p*) ≲ ℓ^(-1)` with `c ≍ ℓ^7`;
3. `Γ'_ρ`: `C ℓ^7 · ℓ^(-p_bad) ≲ ℓ^(-κ_p*)`;
4. `S_M`: `C ℓ · ℓ^(-(p_bad+2)) ≲ ℓ^(-p_bad)`;
5. `B_θ`: `C ℓ^6 · ℓ^(-7 c_ev K) ≲ ℓ^(-(p_bad+2))` whenever `7 c_ev K ≥ p_bad + 9`. -/
theorem budget_rows (cK : ℝ) (hK : pBad + 9 ≤ 7 * cK) :
    D - kappaStar ≤ -1 - 1 ∧
    (7 + D) - kappaStar ≤ -1 - 1 ∧
    7 - pBad ≤ -kappaStar - 1 ∧
    1 - (pBad + 2) ≤ -pBad - 1 ∧
    6 - 7 * cK ≤ -(pBad + 2) - 1 := by
  unfold pBad kappaStar D at *
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by linarith⟩

/-- The kinetic part of `𝒢'ᶜ` is the binding row: `κ_p* = D + 9` is the least integer with
`(7 + D) - κ_p* ≤ -2`, i.e. `κ_p > D + 8` as required in the proof of `prop:expect`. -/
theorem kappaStar_minimal (k : ℤ) (hk : (7 + D) - k ≤ -1 - 1) : kappaStar ≤ k := by
  unfold kappaStar D at *
  linarith

/-- Consequence for the probability bounds, in the form used in `prop:expect`: for `ℓ` large,
`C ℓ^(7+D) · ℓ^(-κ_p*) ≤ ℓ^(-1)`. -/
theorem kinetic_bad_set_small {C ℓ : ℝ} (hC : 0 < C) (hℓ : max 1 C ≤ ℓ) :
    C * ℓ ^ (7 + D) * ℓ ^ (-kappaStar) ≤ ℓ ^ (-1 : ℝ) :=
  absorb hC hℓ (by unfold kappaStar D; norm_num)

end PauliFierzUV.PaperII.Budget
