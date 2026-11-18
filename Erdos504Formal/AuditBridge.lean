/-
Statement-correspondence bridge — new work by the submitting author.

Purpose: connect the submitted theorem to the statement that Formal
Conjectures states for Erdős Problem #504
(`FormalConjectures/ErdosProblems/504.lean`, theorem `erdos_504`, currently
`sorry` there).  Two things are checked mechanically by type-checking this
file:

1. `minimaxAngle_eq_fc` — the submitted definition of the minimax angle is
   *definitionally* the Formal Conjectures definition (proof by `rfl`), so the
   submitted theorem really speaks about the same object.
2. `intended_main_fc` — the submitted theorem implies the Formal Conjectures
   statement, with the Formal Conjectures vocabulary `fcMinimaxAngle`.

This file contains no proof of the theorem itself; it only records the
correspondence between the submitted statement and the statement as published
in Formal Conjectures.  It is part of the submitted repository so that the
correspondence can be re-checked at the pinned commit without any further
material.

The `fcMinimaxAngle` definition below is copied verbatim from the Formal
Conjectures file (`FormalConjectures/ErdosProblems/504.lean`, lines 60–64);
Formal Conjectures is distributed under the MIT licence.  See `ATTRIBUTION.md`.
-/
import Erdos504Formal.Erdos504Minimax

namespace Erdos504

open Real EuclideanGeometry

/-- The Formal Conjectures definition of the minimax angle, copied verbatim. -/
noncomputable def fcMinimaxAngle (N : ℕ) : ℝ :=
  sSup {α : ℝ | α ∈ Set.Icc 0 π ∧
    ∀ S : Finset ℂ, S.card = N →
      ∃ x ∈ S, ∃ z ∈ S, ∃ y ∈ S, x ≠ z ∧ y ≠ z ∧ x ≠ y ∧
        α ≤ EuclideanGeometry.angle x z y}

/-- The submitted `minimaxAngle` is definitionally the Formal Conjectures one. -/
theorem minimaxAngle_eq_fc (N : ℕ) : minimaxAngle N = fcMinimaxAngle N := rfl

/-- The Formal Conjectures statement of Erdős Problem #504 (Theorem 1 of
Erdős–Szekeres 1960), obtained from the submitted theorem. -/
theorem intended_main_fc {n : ℕ} (hn : 3 ≤ n) :
    fcMinimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π := by
  rw [← minimaxAngle_eq_fc]
  exact erdos_504 hn

/-! ## Axiom audit

As in the other files of this library, the axiom dependencies of the bridge
theorems are printed by `lake build`.  Each line must report exactly the three
standard Lean foundations `propext`, `Classical.choice` and `Quot.sound`; in
particular no `sorryAx` and no `Lean.ofReduceBool` (i.e. no `native_decide`)
may appear. -/

#print axioms minimaxAngle_eq_fc
#print axioms intended_main_fc

end Erdos504
