/-
Solution module for the Palomar Registry submission of Erdős Problem #504.
Self-contained: it repeats the Challenge definitions verbatim (same namespace,
same bodies) and proves the two statements of record from the sorry-free
development in Erdos504Formal/ (Szekeres 1941 + Erdős–Szekeres 1960 + the
supremum identification).  Per the Comparator convention this module is
compiled independently of Challenge; the comparator compares the two
environments, so the definitions and theorem statements here are syntactically
identical to Challenge.lean's.
-/
import Mathlib
import Erdos504Formal.Erdos504Minimax
import Erdos504Formal.Erdos504Endpoint

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
planar set is `π (1 - 1/n)`. -/
theorem erdos_504 {n : ℕ} (hn : 3 ≤ n) :
    minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π :=
  Erdos504.erdos_504 hn

/-- Endpoint form: for `n ≥ 3`, the minimax angle of a `(2 ^ n - 1)`-point planar
set is also `π (1 - 1/n)`. -/
theorem erdos_504_endpoint {n : ℕ} (hn : 3 ≤ n) :
    minimaxAngle (2 ^ n - 1) = (1 - 1 / (n : ℝ)) * π :=
  Erdos504.erdos_504_endpoint_of_card_le hn

end Erdos504Palomar