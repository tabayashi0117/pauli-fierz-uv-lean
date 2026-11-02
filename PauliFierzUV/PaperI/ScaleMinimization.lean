import Mathlib

/-!
# Paper I, Appendix B (proof of Proposition B.1, `prop:F1`) and Section 6: two minimisations

Paper I is arXiv:2610.34122.

For the normalised dilate one has `F(u_t) = a t ^ 2 + b t ^ (-3/2)`, which is minimised at
`t_*`, `t_* ^ (7/2) = 3 b / (4 a)`, with value `(7/3) a ^ (3/7) ((3/4) b) ^ (4/7)`. Also the block arithmetic-geometric step
`h²/(8u) + γρ u ≥ h √(γρ/2)` used in Section 6 (block Born–Oppenheimer bound).
-/

open Real

namespace PauliFierzUV.PaperI

/-- Lower bound for the scale functional (weighted AM-GM). -/
theorem scale_lower {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht : 0 < t) :
    (7 / 3) * a ^ (3 / 7 : ℝ) * ((3 / 4) * b) ^ (4 / 7 : ℝ)
      ≤ a * t ^ (2 : ℝ) + b * t ^ (-(3 / 2) : ℝ) := by
  have hp1 : 0 < (7 / 3) * (a * t ^ (2 : ℝ)) := by positivity
  have hp2 : 0 < (7 / 4) * (b * t ^ (-(3 / 2) : ℝ)) := by positivity
  have key := Real.geom_mean_le_arith_mean2_weighted (w₁ := 3 / 7) (w₂ := 4 / 7)
    (by norm_num) (by norm_num) hp1.le hp2.le (by norm_num)
  have e1 : ((7 / 3) * (a * t ^ (2 : ℝ))) ^ (3 / 7 : ℝ)
      = (7 / 3 : ℝ) ^ (3 / 7 : ℝ) * a ^ (3 / 7 : ℝ) * t ^ (6 / 7 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) (by positivity), Real.mul_rpow ha.le (by positivity),
      ← Real.rpow_mul ht.le]
    norm_num
    ring
  have e2 : ((7 / 4) * (b * t ^ (-(3 / 2) : ℝ))) ^ (4 / 7 : ℝ)
      = (7 / 4 : ℝ) ^ (4 / 7 : ℝ) * b ^ (4 / 7 : ℝ) * t ^ (-(6 / 7) : ℝ) := by
    rw [Real.mul_rpow (by norm_num) (by positivity), Real.mul_rpow hb.le (by positivity),
      ← Real.rpow_mul ht.le]
    norm_num
    ring
  have e3 : t ^ (6 / 7 : ℝ) * t ^ (-(6 / 7) : ℝ) = 1 := by
    rw [← Real.rpow_add ht]; simp
  have e4 : (7 / 3 : ℝ) ^ (3 / 7 : ℝ) * (7 / 4 : ℝ) ^ (4 / 7 : ℝ)
      = (7 / 3) * (3 / 4 : ℝ) ^ (4 / 7 : ℝ) := by
    have h7 : (7 / 3 : ℝ) = (7 / 3 : ℝ) ^ (3 / 7 : ℝ) * (7 / 3 : ℝ) ^ (4 / 7 : ℝ) := by
      rw [← Real.rpow_add (by norm_num)]; norm_num
    have h4 : (7 / 4 : ℝ) = (7 / 3 : ℝ) * (3 / 4 : ℝ) := by norm_num
    calc (7 / 3 : ℝ) ^ (3 / 7 : ℝ) * (7 / 4 : ℝ) ^ (4 / 7 : ℝ)
        = (7 / 3 : ℝ) ^ (3 / 7 : ℝ) * ((7 / 3 : ℝ) ^ (4 / 7 : ℝ) * (3 / 4 : ℝ) ^ (4 / 7 : ℝ)) := by
          rw [h4, Real.mul_rpow (by norm_num) (by norm_num)]
      _ = ((7 / 3 : ℝ) ^ (3 / 7 : ℝ) * (7 / 3 : ℝ) ^ (4 / 7 : ℝ)) * (3 / 4 : ℝ) ^ (4 / 7 : ℝ) := by
          ring
      _ = (7 / 3) * (3 / 4 : ℝ) ^ (4 / 7 : ℝ) := by rw [← h7]
  have e5 : ((3 / 4) * b) ^ (4 / 7 : ℝ) = (3 / 4 : ℝ) ^ (4 / 7 : ℝ) * b ^ (4 / 7 : ℝ) :=
    Real.mul_rpow (by norm_num) hb.le
  have lhs : ((7 / 3) * (a * t ^ (2 : ℝ))) ^ (3 / 7 : ℝ)
        * ((7 / 4) * (b * t ^ (-(3 / 2) : ℝ))) ^ (4 / 7 : ℝ)
      = (7 / 3) * a ^ (3 / 7 : ℝ) * ((3 / 4) * b) ^ (4 / 7 : ℝ) := by
    rw [e1, e2, e5]
    calc _ = ((7 / 3 : ℝ) ^ (3 / 7 : ℝ) * (7 / 4 : ℝ) ^ (4 / 7 : ℝ))
            * a ^ (3 / 7 : ℝ) * b ^ (4 / 7 : ℝ) * (t ^ (6 / 7 : ℝ) * t ^ (-(6 / 7) : ℝ)) := by ring
      _ = _ := by rw [e3, e4]; ring
  rw [lhs] at key
  calc _ ≤ _ := key
    _ = a * t ^ (2 : ℝ) + b * t ^ (-(3 / 2) : ℝ) := by ring

/-- Equality at the minimiser `t_*`, `t_* ^ (7/2) = 3 b / (4 a)`. -/
theorem scale_attained {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht : 0 < t)
    (hstar : t ^ (7 / 2 : ℝ) = 3 * b / (4 * a)) :
    a * t ^ (2 : ℝ) + b * t ^ (-(3 / 2) : ℝ)
      = (7 / 3) * a ^ (3 / 7 : ℝ) * ((3 / 4) * b) ^ (4 / 7 : ℝ) := by
  -- express the two terms by `s := t ^ 2`
  have hb' : b = (4 / 3) * a * t ^ (7 / 2 : ℝ) := by rw [hstar]; field_simp
  have h1 : b * t ^ (-(3 / 2) : ℝ) = (4 / 3) * a * t ^ (2 : ℝ) := by
    rw [hb', mul_assoc, ← Real.rpow_add ht]; norm_num
  have h2 : ((3 / 4) * b) = a * t ^ (7 / 2 : ℝ) := by rw [hb']; ring
  have h3 : (a * t ^ (7 / 2 : ℝ)) ^ (4 / 7 : ℝ) = a ^ (4 / 7 : ℝ) * t ^ (2 : ℝ) := by
    rw [Real.mul_rpow ha.le (by positivity), ← Real.rpow_mul ht.le]; norm_num
  have h4 : a ^ (3 / 7 : ℝ) * a ^ (4 / 7 : ℝ) = a := by
    rw [← Real.rpow_add ha]; norm_num
  rw [h1, h2, h3]
  calc a * t ^ (2 : ℝ) + 4 / 3 * a * t ^ (2 : ℝ)
      = (7 / 3) * (a ^ (3 / 7 : ℝ) * a ^ (4 / 7 : ℝ)) * t ^ (2 : ℝ) := by rw [h4]; ring
    _ = _ := by ring

/-- The block arithmetic-geometric step `h²/(8u) + γρ u ≥ h √(γρ/2)` of Paper I, Sect. 6. -/
theorem block_amgm {h γρ u : ℝ} (hh : 0 ≤ h) (hγ : 0 ≤ γρ) (hu : 0 < u) :
    h * Real.sqrt (γρ / 2) ≤ h ^ 2 / (8 * u) + γρ * u := by
  set w := Real.sqrt (γρ / 2) with hw
  have hw2 : w ^ 2 = γρ / 2 := Real.sq_sqrt (by positivity)
  have : γρ = 2 * w ^ 2 := by linarith
  rw [this]
  have key : 0 ≤ (h - 4 * w * u) ^ 2 / (8 * u) := by positivity
  have e : (h - 4 * w * u) ^ 2 / (8 * u) = h ^ 2 / (8 * u) + 2 * w ^ 2 * u - h * w := by
    field_simp
    ring
  linarith

end PauliFierzUV.PaperI
