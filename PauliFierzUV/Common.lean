import Mathlib

/-!
# Common helpers

Statements of the form `liminf ≥ A` or `liminf > 0` are formulated with the `EReal`-valued
`Filter.liminf`. For real-valued functions Mathlib's `ℝ`-valued `liminf` takes a junk value
when the function is unbounded (for instance `liminf = 0` for a function tending to `+∞`),
so the extended reals are the faithful choice.
-/

open Filter Topology

namespace PauliFierzUV

/-- `A ≤ liminf u` in `EReal`, from "every real `c < A` is eventually below `u`". -/
theorem le_liminf_ereal_of_forall {ι : Type*} {f : Filter ι} {u : ι → ℝ} {A : ℝ}
    (h : ∀ c : ℝ, c < A → ∀ᶠ x in f, c ≤ u x) :
    (A : EReal) ≤ liminf (fun x => (u x : EReal)) f := by
  by_contra hlt'
  have hlt := not_le.1 hlt'
  obtain ⟨y, hy1, hy2⟩ := EReal.exists_between_coe_real hlt
  have hyA : y < A := by exact_mod_cast hy2
  have hev : ∀ᶠ x in f, (y : EReal) ≤ (u x : EReal) :=
    (h y hyA).mono fun x hx => by exact_mod_cast hx
  have := le_liminf_of_le (f := f) (u := fun x => (u x : EReal)) (by isBoundedDefault) hev
  exact absurd hy1 (not_lt.2 this)

end PauliFierzUV
