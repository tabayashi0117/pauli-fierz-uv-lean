# pauli-fierz-uv-lean

Lean 4 / Mathlib formalization of the **computational core** of two papers on the Pauli–Fierz
model in the ultraviolet limit by S. Futakuchi:

- **Paper I**, arXiv:2610.34122. Main result: `E₀ = (1 + o(1)) c_α α^{2/7} Λ^{12/7}`.
- **Paper II**, arXiv:2610.34125. Theorem A (`h ≥ 1 + 0.3441α/(1 + 0.2985√α + 0.1252α)`),
  Theorem B (`h(λ) ≥ λ^{8/7-ε}` for large `λ`, so `ι_PF > 0`), and Lemma 1.1 (solvability of
  `m h(Λ/m) = m_phys`).

**Scope.** We formalized and machine-checked 23 self-contained computational lemmas from the
proofs of Papers I and II; the main theorems themselves are not formalized. The table below
lists them. Paper references use the numbering of arXiv v2 of each paper (the label in the TeX
source is given in brackets).

Each Lean statement either (a) is the paper's statement itself, when that statement is
elementary (for example Lemma 1.1 of Paper II, which is about an abstract function), or (b) is a
calculation or inequality used inside a proof, with all its inputs explicit, or (c) has the form
**"hypothesis ⇒ conclusion"**, where the hypothesis is the statement of an analytic result of the
paper that is *not* proved here. Rows of type (c) are marked **H⇒C**. They check that the
paper's conclusion follows from that result as claimed; they do not prove the conclusion.

## What is verified

All files are under `PauliFierzUV/`. Theorem names are given without the namespace prefix
(`PauliFierzUV.PaperI` or `PauliFierzUV.PaperII`).

### Paper I (arXiv:2610.34122)

| # | Lean theorem(s) | Paper reference | Statement | Type |
|---|---|---|---|---|
| 1 | `scale_lower`, `scale_attained` (`PaperI/ScaleMinimization`) | Prop. B.1 (b), proof [`prop:F1`] | `a t² + b t^{-3/2} ≥ (7/3) a^{3/7} (¾b)^{4/7}`, with equality at `t^{7/2} = 3b/(4a)` | (b) |
| 2 | `integral_u`, `integral_u_sq`, `integral_du_sq`, `a_value`, `exists_root` (`PaperI/MinimizerIntegrals`) | Prop. B.1 (b), proof | For `u(r) = 1 − sin r/(r cos x)` with `tan x = x`: `∫₀^x u r² = x³/3`, `∫₀^x u² r² = 5x³/6`, `∫₀^x u′² r² = x³/2`, `a = 3/10`; existence of the root `x ∈ (π, 3π/2)` | (b) |
| 3 | `a_eq`, `b_eq`, `tstar_eq`, `F1_first_expression`, `F1_scale_lower` (`PaperI/LeadingConstant`) | Prop. B.1 (b), proof | `a = 3/10`, `b = (4π/3)√(3/(10π)) x^{3/2}`, `t_*^{7/2} = 3b/(4a) = ‖u‖₂`, and the value `(7/3)(3/10)^{3/7}(3π/10)^{2/7} x^{6/7}` | (b) |
| 4 | `F1_two_expressions`, `nash_min_lower`, `nash_min_attained` | Prop. B.1 (b) and the paragraph after it | The two expressions for `F[1]` agree, with `C_N = 5^{5/3}/(2^{2/3}·3x²(4π/3)^{2/3})`; `min_{y>0}(y^{-4/3}/(2C_N) + y) = (7/4)(2/3)^{3/7} C_N^{-3/7}` | (b) |
| 5 | `coeff_physical`, `coeff_working`, `coeff_cF`, `working_functional_scaling` | Sect. 3, eq. [`eq:coeff`], [`eq:calpha`] | `F[1] β_*^{4/7} = c_α α^{2/7} Λ^{12/7} = (Λ/π) F_λ[β]`, `F_λ[β] = c_F e² ℓ⁵`, `λ F[β/λ] = λ^{3/7} β^{4/7} F[1]` | (b) |
| 6 | `params_identities`, `crossover_ratio`, `vacuum_energy` | Sect. 1 (after eq. [`eq:calpha`]), proof of Cor. 1.2, Rem. 3.6 [`rem:window`] | `Ξ = π^{-2/7}(e⁵Λ)^{2/7}`, `ℓ⁷ = Λ/(4π²α)`, `ℓ^{1/3} = (4π²)^{-1/21}(Λ/α)^{1/21}`; crossover ratio `(α^{5/2}Λ)^{2/7}/(2π c_α)` | (b) |
| 7 | `Finf_scaling`, `F_scaling_dim3`, `F_lambda_scaling_dim3` (`PaperI/FunctionalScaling`) | Sect. 3 ("The comparison functional") | `F[β] = β^{4/7} F[1]` and `F_λ[β] = λ^{3/7} β^{4/7} F[1]` by dilation (in dimension `d`: exponents `d/(d+4)`, `4/(d+4)`). See the caveat below on the function class | (b) |
| 8 | `hardy_field`, `pointwise` (`PaperI/HardyFieldSpace`) | Lemma 6.5 [`lem:hardy`] | `∫ g_S²/(4‖G_S‖(‖r q‖² + ε)) ψ² ≤ ∑ᵢ ∫ (∂ᵢψ)²` for real `ψ ∈ C¹_c`, `ε > 0` | (b), partial |
| 9 | `hardy_ratio_antitone`, `hardy_ratio_ge` | Cor. 6.7 (b) [`cor:hardy`] | `x ↦ (T − 2x)²/x` is decreasing on `(0, T/2]`, hence `g′²/‖G′‖ ≥ (T − 2)²` | (b) |
| 10 | `block_amgm` | Sect. 6 (after Thm. 6.2) and proof of Prop. 6.9 | `h²/(8u) + γρ u ≥ h √(γρ/2)` | (b) |
| 11 | `norm_add_sq_ge`, `weakfloor_combination`, `weakfloor_bracket`, `weakfloor_conclusion` (`PaperI/WeakFields`) | Lemma 7.5 [`lem:weakfloor`], proof | `|c+f|² ≥ (1−η)|c|² − (η⁻¹−1)|f|²`; the combination giving `(1−η) μ̂_b + (1 − 2√t − t/η + ηt)‖∇f‖²`; the bracket is `≥ 1 − 2/√8 − 1/8 > 0` for `t ≤ η/8` | (b); analytic inputs as hypotheses |
| 12 | `virial_kinetic`, `virial_field`, `virial_exponent`, `ell_scaling` (`PaperI/Virial`) | Cor. 8.4 [`cor:virial`], proof | From `inf σ(H_c)/E₀ → c^{5/7}` and `inf σ(H_c) ≤ (1+ε′)E₀ + (c−1)⟨𝒯⟩`: `⟨𝒯⟩/E₀ → 5/7` and `⟨H_f⟩/E₀ → 2/7` | **H⇒C** |
| 13 | `main_lower_from_relerr` (`PaperI/FinalAssembly`) | Thm. 1.1 (b) [`thm:main`], proof in Sect. 8, from Prop. 8.3 [`prop:relerr`] | Assuming the bound of Prop. 8.3, the parameter choices of Table [`tab:choices`] give `1 − E₀(H^{(λ)})/F_λ[β] ≤ ε` for `ℓ ≥ ℓ₀`, `Ξ ≥ Ξ₀`, `log(2+e²) ≤ κ₀ ℓ^{1/3}` | **H⇒C** |

### Paper II (arXiv:2610.34125)

| # | Lean theorem(s) | Paper reference | Statement | Type |
|---|---|---|---|---|
| 14 | `lemma_1_1_i`, `lemma_1_1_ii`, `lemma_1_1_equiv`, `iota_pos_iff` (`PaperII/MassRenormalization`) | Lemma 1.1 [`lem:LL-equivalence`] | (i) `liminf h(λ)/λ > 0` ⇒ `g_* > 0` and no solution of `m h(Λ/m) = m_phys` when `m_phys/Λ < g_*`; (ii) `h` continuous and `liminf h(λ)/λ = 0` ⇒ a solution for every `(Λ, m_phys)`; the equivalence for continuous `h` | (a) |
| 15 | `corollary_C`, `iota_pos_of_tendsto` | Cor. C = Cor. 2.6 [`cor:LL`]; end of proof of Thm. 2.5 | A solution exists only if `Λ ≤ m_phys/ι_PF`; `h(λ)/λ → ∞` and `h ≥ 1` ⇒ `ι_PF > 0` | (a) |
| 16 | `growth_of_curvatureBound`, `tendsto_ratio_of_curvatureBound`, `iota_pos_of_curvatureBound` (`PaperII/TheoremBAssembly`) | Thm. B = Thm. 2.5 [`thm:main`], proof (Sect. 10.3) | Assuming `c/h ≤ C_κ ℓ^{κ−1}(log λ)²` for every `κ ∈ (0,1)` (Lemma 6.2 + Prop. 10.2), with `c = λ/π`, `ℓ = (λ/(πā))^{1/7}`: `h(λ) ≥ λ^{8/7−ε}` for large `λ`, `h(λ)/λ → ∞`, `ι_PF > 0` | **H⇒C** |
| 17 | `budget_rows`, `kappaStar_minimal`, `absorb`, `kinetic_bad_set_small` (`PaperII/ExponentBudget`) | Rem. 10.4 [`rem:budget`], Table [`tab:budget`]; proof of Prop. 10.2 | With `D = 2`, `κ_p* = D+9`, `p_bad = κ_p*+8`, `7c_ev K ≥ p_bad+9`, every row closes with one spare power of `ℓ`; `κ_p* = D+9` is the least integer allowed by the kinetic row | (b), exponent arithmetic only |
| 18 | `integral_Lfun`, `integral_amplitude`, `integral_recoil`, `tK_from_amplitude`, `qK_from_recoil` (`PaperII/PartIConstants`) | Sect. 3.2 (definition of `L`), App. C [`app:integrals`] | `L(σ) = ∫₀^σ √(t/(1+t)) dt = √(σ(1+σ)) − arsinh √σ`; `∫₀^K m√(k/(2m+k)) dk = 2m² L(σ)`; `∫₀^K 4m²k/(2m+k)² dk = 4m²(log(1+σ) − σ/(1+σ))`; `𝖺_K²/(mS(0)) = t_K`, `𝖭_K/(mS(0)) = q_K` | (b) |
| 19 | `two_xK_half_ge`, `two_sqrt_qt_half_le`, `two_tK_half_le`, `log_three_halves_bounds`, `arsinh_sqrt_half_gt` | App. C.1, Table [`tab:partI-values`] | For `K = m`: `2x_m/α ≥ 0.3441`, `2√(q_m t_m/α) ≤ 0.2985`, `2t_m/α ≤ 0.1252`, proved in Lean from series bounds for `log` and `π` (no floating point, no `native_decide`) | (b) |
| 20 | `partI_explicit_arith`, `theoremA_explicit_of_partI` | Thm. A, first part = Cor. 3.2 [`cor:partI-explicit`] | `2x_m/(1+ρ_m) ≥ 0.3441α/(1 + 0.2985√α + 0.1252α)` for all `α ≥ 0`; hence Thm. 3.1 ⇒ Thm. A | (b) and **H⇒C** |
| 21 | `one_lt_partIBound` | Thm. 3.1 [`thm:partI`], last sentence | `1 + 2x_K/(1+ρ_K) > 1` for `α > 0` | (b) |
| 22 | `partI_first_order`, `partI_first_order_liminf` (`PaperII/PartIAsymptotics`) | Thm. A, second part = Cor. 3.3 [`cor:partI-first-order`] | Thm. 3.1 with `K = Λ` ⇒ `liminf_{α→0} (h−1)/α ≥ (8/3π) log(1 + λ/2)` | **H⇒C** |
| 23 | `partI_large_coupling`, `partI_large_coupling_liminf`, `log_one_add_ge`, `Lfun_le`, `qK_le`, `tK_le` | Rem. 3.4 (ii) [`rem:partI-values`] | `log(1+σ) ≥ σ − σ²/2`, `L(σ) ≤ (2/3)σ^{3/2}`, `q_K ≤ 2σ`, `t_K ≤ 1/(2−σ)` for `σ = √(6/(πα)) ≤ 1`; Thm. 3.1 for all `0 < σ ≤ λ/2` ⇒ `liminf_{α→∞} h/√α ≥ (4/3π)√(6/π)` | (b) and **H⇒C** |

`liminf` statements are formulated in `EReal` (`PauliFierzUV/Common.lean`): Mathlib's
`ℝ`-valued `liminf` takes a junk value for unbounded functions, which would make a statement such
as `liminf h(λ)/λ > 0` unfaithful when `h(λ)/λ → ∞`.

## What is NOT verified

- **The main theorems are not formalized.** Theorem 1.1 of Paper I and Theorems A and B (= Theorem 2.5)
  of Paper II are not stated as Lean theorems without hypotheses. Fock space, the Pauli–Fierz
  Hamiltonian, unbounded operators and their spectra do not appear in this project.
- **H⇒C rows prove only the implication.** Rows 12, 13, 16, 20, 22 and 23 take an analytic result
  of the paper (Prop. 8.3 and the scaling asymptotics of Paper I; Lemma 6.2 + Prop. 10.2 and
  Thm. 3.1 of Paper II) as a hypothesis. That the hypothesis holds is not checked in Lean, and
  that the Lean hypothesis matches the paper's statement was checked by reading, not by machine.
- **Modelling choices.**
  - Row 2–3: the norms of the minimiser are defined as `4π` times the radial integrals; the
    passage to polar coordinates in `ℝ³`, the sign `u ≥ 0`, and the minimality of `u` (which rests
    on the cited sharp Nash inequality of Carlen and Loss) are not formalized. Numerical
    enclosures of `x₁`, `F[1]` and `c_α` are not formalized.
  - Row 7: the infimum is over nonnegative `C¹` functions with compact support and `‖φ‖₂ = 1`.
    The paper's `F[β]` is the infimum over `H¹ ∩ L¹`; that the two infima coincide (density) is
    not formalized.
  - Row 8: the inequality is proved for real `ψ ∈ C¹_c` with the regularisation `ε > 0`. The
    extension to the form domain, the limit `ε ↓ 0` and complex `ψ` are not formalized.
  - Row 14–15: `h` is real-valued; the paper allows `h : (0,∞) → [1, ∞]`. The value `+∞` never
    gives a solution of `m h(Λ/m) = m_phys`, so the statements are unaffected.
  - Row 17 checks only the exponent arithmetic of Table `tab:budget`, not the polynomial factors or
    the probability bounds of the cited propositions.
- No numerical value from the ancillary scripts of the papers is used as an axiom or hypothesis.

## Building

Requirements: [elan](https://github.com/leanprover/elan). The toolchain and Mathlib versions are
pinned (`lean-toolchain`, `lake-manifest.json`).

```bash
lake exe cache get        # download prebuilt Mathlib (recommended)
lake build                # builds PauliFierzUV
./scripts/check_axioms.sh # build + forbidden-keyword scan + axiom check
```

`scripts/check_axioms.sh` fails if any source contains `sorry`, `admit`, `native_decide` or an
`axiom` declaration, or if any declaration depends on an axiom other than the three standard ones.
`PauliFierzUV/Axioms.lean` contains `#print axioms` for each of the 120 theorems and lemmas and
an `#eval` that checks *every* declaration under the namespace `PauliFierzUV` (279
declarations, including auxiliary ones) and raises an error otherwise. GitHub Actions runs the
same script (`.github/workflows/lean.yml`).

With Mathlib prebuilt, a clean build of this project's sources takes about 1 minute on a laptop
(14 modules, about 2,500 lines of Lean).

### Axiom check output

```
$ ./scripts/check_axioms.sh
...
Build completed successfully (9062 jobs).
 120 [propext, Classical.choice, Quot.sound]
OK: 279 declarations under PauliFierzUV depend only on [propext, Classical.choice, Quot.sound]
```

For example:

```
'PauliFierzUV.PaperII.lemma_1_1_ii' depends on axioms: [propext, Classical.choice, Quot.sound]
'PauliFierzUV.PaperII.theoremA_explicit_of_partI' depends on axioms: [propext, Classical.choice, Quot.sound]
'PauliFierzUV.PaperI.F_scaling_dim3' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Versions

| | |
|---|---|
| Lean | `leanprover/lean4:v4.35.0` |
| Mathlib | `v4.35.0` (commit `56a005855ea17e0b0958f73ec801ae140b0a1679`) |

## Layout

```
PauliFierzUV/
  Common.lean                    EReal liminf helper
  PaperI/  ScaleMinimization, MinimizerIntegrals, LeadingConstant, FunctionalScaling,
           HardyFieldSpace, WeakFields, Virial, FinalAssembly
  PaperII/ MassRenormalization, TheoremBAssembly, ExponentBudget, PartIConstants,
           PartIAsymptotics
  Axioms.lean                    #print axioms + programmatic check (not imported by the library)
scripts/check_axioms.sh
```

## License

Apache License 2.0 (see `LICENSE`).

---

## 日本語の概要

論文 I(arXiv:2610.34122)と論文 II(arXiv:2610.34125)の**証明の中の計算の核**を Lean 4 と
Mathlib で形式化したものです。**主定理そのもの(論文 I の Theorem 1.1、論文 II の
Theorem A・B)は形式化していません。** Fock 空間や作用素は扱っていません。

- 形式化して機械検証したのは、両論文の証明から取り出した 23 の自己完結した計算の補題です
  (上の表)。全ての定理は `sorry`・`axiom`・`native_decide` を使わず、依存する公理は標準の
  `propext`・`Classical.choice`・`Quot.sound` の 3 つだけです(`scripts/check_axioms.sh` で確認)。
- 表で **H⇒C** と書いた行は「仮定 ⇒ 結論」の形です。論文の解析的な結果(論文 I の
  Proposition 8.3、論文 II の Theorem 3.1 や Proposition 10.2 など)を仮定として置き、そこから
  論文の結論が述べたとおりに従うことだけを検証しています。仮定そのものは Lean では証明して
  いません。
- 論文 II の Lemma 1.1(質量くりこみの方程式 `m h(Λ/m) = m_phys` の可解性)は抽象的な関数に
  ついての補題なので、論文の主張そのままを証明しています。Theorem A の数値定数
  0.3441・0.2985・0.1252 は、`log` の級数評価と `π` の評価から Lean の中で証明しています。

正確に言える文: 「論文 I・II の証明から 23 個の自己完結した計算の補題を形式化し、機械検証
した。主定理そのものは形式化していない。」
