/-
Challenge module for the Palomar Registry submission of Erdős Problem #504
(Blumenthal's problem): the minimax angle of a planar point set.

Imports Mathlib alone.  The two theorems below are the statements of record;
the `sorry` holes are the deliberate Comparator convention (the proof lives in
Solution.lean).  A mathematician should audit these statements against:
  G. Szekeres, On an extremum problem in the plane, Amer. J. Math. 63 (1941), 208-210;
  P. Erdős and G. Szekeres, On some extremum problems in elementary geometry,
  Ann. Univ. Sci. Budapest. Eötvös Sect. Math. 3 (1960/61), 53-62.
-/
import Mathlib

namespace Erdos504Palomar

open Real EuclideanGeometry

/-- The angles guaranteed in every `N`-point planar set: `α ∈ [0, π]` such that
every set of `N` points contains three pairwise distinct points `x, z, y` with
`∠x z y ≥ α` (angle at the middle point `z`). -/
def admissibleAngles (N : ℕ) : Set ℝ :=
  {α : ℝ | α ∈ Set.Icc 0 π ∧
    ∀ S : Finset ℂ, S.card = N →
      ∃ x ∈ S, ∃ z ∈ S, ∃ y ∈ S, x ≠ z ∧ y ≠ z ∧ x ≠ y ∧
        α ≤ EuclideanGeometry.angle x z y}

/-- The minimax angle `α_N`: supremum of `admissibleAngles N`. -/
noncomputable def minimaxAngle (N : ℕ) : ℝ :=
  sSup {α : ℝ | α ∈ Set.Icc 0 π ∧
    ∀ S : Finset ℂ, S.card = N →
      ∃ x ∈ S, ∃ z ∈ S, ∃ y ∈ S, x ≠ z ∧ y ≠ z ∧ x ≠ y ∧
        α ≤ EuclideanGeometry.angle x z y}

/-- **Erdős–Szekeres (1960).** For `n ≥ 3`, the minimax angle of a `2 ^ n`-point
planar set is `π (1 - 1/n)`.  Statement of record; proof in Solution.lean. -/
theorem erdos_504 {n : ℕ} (hn : 3 ≤ n) :
    minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π := by
  sorry -- deliberate Comparator hole; proved in Solution.lean

/-- Endpoint form: for `n ≥ 3`, the minimax angle of a `(2 ^ n - 1)`-point planar
set is also `π (1 - 1/n)`.  Statement of record; proof in Solution.lean. -/
theorem erdos_504_endpoint {n : ℕ} (hn : 3 ≤ n) :
    minimaxAngle (2 ^ n - 1) = (1 - 1 / (n : ℝ)) * π := by
  sorry -- deliberate Comparator hole; proved in Solution.lean

end Erdos504Palomar