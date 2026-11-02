import PauliFierzUV.Common

/-!
# Paper II, Lemma 1.1 (`lem:LL-equivalence`) and Corollary C (= Corollary 2.6, `cor:LL`)

Paper II is arXiv:2610.34125. Fix `α`, let `h : (0, ∞) → [1, ∞)` (the effective mass ratio as a
function of `λ = Λ/m`) and put `F_Λ(m) := m h(Λ/m)`.

* (i) If `liminf_{λ→∞} h(λ)/λ > 0`, then `g_* := inf_{λ>0} h(λ)/λ > 0`, and for every pair
  `(Λ, m_phys)` with `m_phys/Λ < g_*` the equation `F_Λ(m) = m_phys` has no solution `m > 0`.
* (ii) If `h` is continuous and `liminf_{λ→∞} h(λ)/λ = 0`, the equation has a solution for all
  `(Λ, m_phys)`.
* In particular, for continuous `h`, the absence of solutions for large `Λ/m_phys` is equivalent
  to `liminf_{λ→∞} h(λ)/λ > 0`.

The lemma is about an abstract function, so this file formalizes it as stated, with one
modelling choice: `h` is real-valued (the paper allows the value `+∞`, which never produces a
solution of `F_Λ(m) = m_phys < ∞`). The `liminf` is taken in `EReal`.

We also record the elementary consequences used in Paper II: `ι_PF := inf h(λ)/λ > 0` as soon as
`h(λ)/λ → ∞` (end of the proof of `thm:main`), and the bound `Λ ≤ m_phys / ι_PF` for any
solution (Corollary C).
-/

open Filter Topology Set

namespace PauliFierzUV.PaperII

/-- The map `F_Λ(m) = m h(Λ/m)` of Lemma 1.1. -/
noncomputable def massMap (h : ℝ → ℝ) (Λ m : ℝ) : ℝ := m * h (Λ / m)

/-- `g_* = inf_{λ>0} h(λ)/λ`; for the effective mass ratio this is `ι_PF(α)`. -/
noncomputable def iota (h : ℝ → ℝ) : ℝ := sInf ((fun l => h l / l) '' Ioi 0)

/-- `liminf_{λ→∞} h(λ)/λ`, valued in the extended reals. -/
noncomputable def liminfRatio (h : ℝ → ℝ) : EReal :=
  liminf (fun l => ((h l / l : ℝ) : EReal)) atTop

variable {h : ℝ → ℝ}

/-- With `λ = Λ/m`, `F_Λ(m) = Λ h(λ)/λ`. -/
lemma massMap_eq {Λ m : ℝ} (hΛ : 0 < Λ) (hm : 0 < m) :
    massMap h Λ m = Λ * (h (Λ / m) / (Λ / m)) := by
  unfold massMap
  field_simp

lemma ratio_pos (hh : ∀ l, 0 < l → 1 ≤ h l) {l : ℝ} (hl : 0 < l) : 0 < h l / l :=
  div_pos (lt_of_lt_of_le one_pos (hh l hl)) hl

lemma bddBelow_ratio (hh : ∀ l, 0 < l → 1 ≤ h l) : BddBelow ((fun l => h l / l) '' Ioi 0) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨l, hl, rfl⟩
  exact (ratio_pos hh hl).le

lemma iota_le (hh : ∀ l, 0 < l → 1 ≤ h l) {l : ℝ} (hl : 0 < l) : iota h ≤ h l / l :=
  csInf_le (bddBelow_ratio hh) ⟨l, hl, rfl⟩

lemma le_iota {c : ℝ} (hc : ∀ l, 0 < l → c ≤ h l / l) : c ≤ iota h := by
  refine le_csInf ⟨h 1 / 1, 1, Set.mem_Ioi.2 one_pos, rfl⟩ ?_
  rintro _ ⟨l, hl, rfl⟩
  exact hc l hl

/-- `liminf h(λ)/λ > 0` iff `h(λ)/λ` is eventually bounded below by a positive constant. -/
lemma liminfRatio_pos_iff :
    0 < liminfRatio h ↔ ∃ c : ℝ, 0 < c ∧ ∀ᶠ l in atTop, c ≤ h l / l := by
  constructor
  · intro hpos
    obtain ⟨c, hc0, hc1⟩ := EReal.exists_between_coe_real hpos
    refine ⟨c, by exact_mod_cast hc0, ?_⟩
    have := eventually_lt_of_lt_liminf hc1 (by isBoundedDefault)
    exact this.mono fun l hl => by exact_mod_cast hl.le
  · rintro ⟨c, hc0, hev⟩
    have h1 : (c : EReal) ≤ liminfRatio h :=
      le_liminf_of_le (by isBoundedDefault) (hev.mono fun l hl => by exact_mod_cast hl)
    exact lt_of_lt_of_le (by exact_mod_cast hc0) h1

/-- Since `h ≥ 1`, `g_* > 0` iff `liminf h(λ)/λ > 0`. -/
theorem iota_pos_iff (hh : ∀ l, 0 < l → 1 ≤ h l) : 0 < iota h ↔ 0 < liminfRatio h := by
  rw [liminfRatio_pos_iff]
  constructor
  · intro hι
    refine ⟨iota h, hι, ?_⟩
    filter_upwards [eventually_gt_atTop 0] with l hl
    exact iota_le hh hl
  · rintro ⟨c, hc0, hev⟩
    obtain ⟨R, hR⟩ := eventually_atTop.1 hev
    set R' := max R 1 with hR'
    have hR'0 : 0 < R' := lt_of_lt_of_le one_pos (le_max_right _ _)
    have key : ∀ l, 0 < l → min c (1 / R') ≤ h l / l := by
      intro l hl
      by_cases hlR : R' ≤ l
      · exact (min_le_left _ _).trans (hR l ((le_max_left _ _).trans hlR))
      · replace hlR := not_le.1 hlR
        refine (min_le_right _ _).trans ?_
        have h1 : 1 / R' ≤ 1 / l := one_div_le_one_div_of_le hl hlR.le
        have h2 : 1 / l ≤ h l / l := div_le_div_of_nonneg_right (hh l hl) hl.le
        exact h1.trans h2
    exact lt_of_lt_of_le (lt_min hc0 (by positivity)) (le_iota key)

/-- **Lemma 1.1 (i)** of Paper II. -/
theorem lemma_1_1_i (hh : ∀ l, 0 < l → 1 ≤ h l) (hlim : 0 < liminfRatio h) :
    0 < iota h ∧
      ∀ Λ mphys : ℝ, 0 < Λ → mphys / Λ < iota h → ∀ m : ℝ, 0 < m → massMap h Λ m ≠ mphys := by
  refine ⟨(iota_pos_iff hh).2 hlim, ?_⟩
  intro Λ mphys hΛ hlt m hm heq
  have h1 : iota h ≤ h (Λ / m) / (Λ / m) := iota_le hh (div_pos hΛ hm)
  rw [massMap_eq hΛ hm] at heq
  rw [div_lt_iff₀ hΛ] at hlt
  nlinarith

/-- `liminf h(λ)/λ = 0` gives arbitrarily large `λ` with `h(λ)/λ < ε`. -/
lemma frequently_lt_of_liminfRatio_eq_zero (hlim : liminfRatio h = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ l in atTop, h l / l < ε := by
  have hle : liminfRatio h ≤ 0 := hlim.le
  unfold liminfRatio at hle
  rw [liminf_le_iff (by isBoundedDefault) (by isBoundedDefault)] at hle
  have := hle ε (by exact_mod_cast hε)
  exact this.mono fun l hl => by exact_mod_cast hl

/-- **Lemma 1.1 (ii)** of Paper II. -/
theorem lemma_1_1_ii (hh : ∀ l, 0 < l → 1 ≤ h l) (hc : ContinuousOn h (Ioi 0))
    (hlim : liminfRatio h = 0) :
    ∀ Λ mphys : ℝ, 0 < Λ → 0 < mphys → ∃ m : ℝ, 0 < m ∧ massMap h Λ m = mphys := by
  intro Λ mphys hΛ hmp
  set y := mphys / Λ with hy
  have hy0 : 0 < y := div_pos hmp hΛ
  -- a small `λ₁` with `h(λ₁)/λ₁ ≥ y`
  set l1 := 1 / (y + 1) with hl1
  have hl10 : 0 < l1 := by positivity
  have hg1 : y ≤ h l1 / l1 := by
    have : 1 / l1 = y + 1 := by rw [hl1]; field_simp
    have h2 : 1 / l1 ≤ h l1 / l1 := div_le_div_of_nonneg_right (hh l1 hl10) hl10.le
    linarith
  -- a large `λ₂ ≥ λ₁` with `h(λ₂)/λ₂ < y`
  obtain ⟨l2, hg2, hl2⟩ :=
    ((frequently_lt_of_liminfRatio_eq_zero hlim hy0).and_eventually
      (eventually_ge_atTop l1)).exists
  have hcont : ContinuousOn (fun l => h l / l) (Icc l1 l2) := by
    have hsub : Icc l1 l2 ⊆ Ioi 0 := fun l hl => lt_of_lt_of_le hl10 hl.1
    exact (hc.mono hsub).div continuousOn_id fun l hl => (hsub hl).ne'
  obtain ⟨c, hcI, hcy⟩ := intermediate_value_Icc' hl2 hcont ⟨hg2.le, hg1⟩
  have hc0 : 0 < c := lt_of_lt_of_le hl10 hcI.1
  refine ⟨Λ / c, div_pos hΛ hc0, ?_⟩
  rw [massMap_eq hΛ (div_pos hΛ hc0)]
  have : Λ / (Λ / c) = c := by field_simp
  have hcy' : h c / c = y := hcy
  rw [this, hcy', hy]
  field_simp

/-- **Lemma 1.1, final sentence**: for continuous `h ≥ 1`, the absence of solutions for all
large `Λ/m_phys` is equivalent to `liminf h(λ)/λ > 0`. -/
theorem lemma_1_1_equiv (hh : ∀ l, 0 < l → 1 ≤ h l) (hc : ContinuousOn h (Ioi 0)) :
    (∃ g : ℝ, 0 < g ∧ ∀ Λ mphys : ℝ, 0 < Λ → 0 < mphys → mphys / Λ < g →
        ∀ m : ℝ, 0 < m → massMap h Λ m ≠ mphys) ↔ 0 < liminfRatio h := by
  constructor
  · rintro ⟨g, hg, hno⟩
    by_contra hnot'
    have hnot : liminfRatio h ≤ 0 := not_lt.1 hnot'
    have hge : 0 ≤ liminfRatio h :=
      le_liminf_of_le (by isBoundedDefault)
        ((eventually_gt_atTop 0).mono fun l hl => by exact_mod_cast (ratio_pos hh hl).le)
    have heq : liminfRatio h = 0 := le_antisymm hnot hge
    obtain ⟨m, hm, hsol⟩ := lemma_1_1_ii hh hc heq (2 / g) 1 (by positivity) one_pos
    have : (1 : ℝ) / (2 / g) < g := by
      rw [one_div_div]; linarith
    exact hno (2 / g) 1 (by positivity) one_pos this m hm hsol
  · intro hlim
    obtain ⟨hι, hno⟩ := lemma_1_1_i hh hlim
    exact ⟨iota h, hι, fun Λ mphys hΛ _ hlt m hm => hno Λ mphys hΛ hlt m hm⟩

/-- `h(λ)/λ → ∞` implies `ι = inf h(λ)/λ > 0` (the last step of the proof of Theorem B). -/
theorem iota_pos_of_tendsto (hh : ∀ l, 0 < l → 1 ≤ h l)
    (htend : Tendsto (fun l => h l / l) atTop atTop) : 0 < iota h :=
  (iota_pos_iff hh).2 (liminfRatio_pos_iff.2 ⟨1, one_pos, htend.eventually_ge_atTop 1⟩)

/-- **Corollary C** of Paper II (arithmetic part): if `ι > 0` and `m h(Λ/m) = m_phys` for some
`m > 0`, then `Λ ≤ m_phys / ι`. -/
theorem corollary_C (hh : ∀ l, 0 < l → 1 ≤ h l) (hι : 0 < iota h) {Λ mphys m : ℝ}
    (hΛ : 0 < Λ) (hm : 0 < m) (hsol : massMap h Λ m = mphys) : Λ ≤ mphys / iota h := by
  have h1 : iota h ≤ h (Λ / m) / (Λ / m) := iota_le hh (div_pos hΛ hm)
  rw [massMap_eq hΛ hm] at hsol
  rw [le_div_iff₀ hι]
  nlinarith

end PauliFierzUV.PaperII
