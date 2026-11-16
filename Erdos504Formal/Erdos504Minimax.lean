/-
Lean formalisation of the minimax-angle statement of Erdős Problem #504
(Blumenthal's problem), contributed by the submitter.

The mathematical content is supplied by the following published results, which are
already formalised, sorry-free, in `Erdos504Formal/Erdos504.lean` (republished
unchanged from `ToshiDad/erdos-504`):

* Szekeres (1941), lower bound — `Erdos504.exists_angle_gt`
* Szekeres (1941), upper-bound construction — `Erdos504.exists_config_angle_lt`
* Erdős–Szekeres (1960), Theorem 1 — `Erdos504.erdos_szekeres_1960`

This file adds the missing step: it defines the minimax angle `α_N` as a supremum
and proves that the supremum is exactly the value determined by Erdős–Szekeres.

Reference: G. Szekeres, *On an extremum problem in the plane*, Amer. J. Math. 63
(1941), 208–210; P. Erdős and G. Szekeres, *On some extremum problems in elementary
geometry*, Ann. Univ. Sci. Budapest. Eötvös Sect. Math. 3 (1960/61), 53–62.
-/
import Erdos504Formal.Erdos504

namespace Erdos504

open Real EuclideanGeometry

/--
The set of angles that are guaranteed in every `N`-point set of the plane: the
angles `α ∈ [0, π]` such that every set of `N` points contains three pairwise
distinct points `x, z, y` with `∠x z y ≥ α` (the angle is taken at the middle
point `z`).
-/
def admissibleAngles (N : ℕ) : Set ℝ :=
  {α : ℝ | α ∈ Set.Icc 0 π ∧
    ∀ S : Finset ℂ, S.card = N →
      ∃ x ∈ S, ∃ z ∈ S, ∃ y ∈ S, x ≠ z ∧ y ≠ z ∧ x ≠ y ∧
        α ≤ EuclideanGeometry.angle x z y}

/--
The minimax angle `α_N`: the supremum of all `α ∈ [0, π]` such that every set of
`N` points of the plane contains three pairwise distinct points `x, z, y` with
`∠x z y ≥ α` (the angle is taken at the middle point `z`).
-/
noncomputable def minimaxAngle (N : ℕ) : ℝ :=
  sSup {α : ℝ | α ∈ Set.Icc 0 π ∧
    ∀ S : Finset ℂ, S.card = N →
      ∃ x ∈ S, ∃ z ∈ S, ∃ y ∈ S, x ≠ z ∧ y ≠ z ∧ x ≠ y ∧
        α ≤ EuclideanGeometry.angle x z y}

/-- The Erdős–Szekeres value `π (1 - 1/n)` is positive whenever `n ≥ 3`. -/
private lemma pi_mul_one_sub_inv_pos {n : ℕ} (hn : 3 ≤ n) :
    0 < (1 - 1 / (n : ℝ)) * π := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < n := by linarith
  have hinv : (1 : ℝ) / n < 1 := (div_lt_iff₀ hn_pos).2 (by linarith)
  have hcoef : 0 < 1 - 1 / (n : ℝ) := by linarith
  exact mul_pos hcoef Real.pi_pos

/-- The Erdős–Szekeres value `π (1 - 1/n)` is at most `π`. -/
private lemma pi_mul_one_sub_inv_le_pi {n : ℕ} (hn : 3 ≤ n) :
    (1 - 1 / (n : ℝ)) * π ≤ π := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < n := by linarith
  have hinv : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  have hcoef : 1 - 1 / (n : ℝ) ≤ 1 := by linarith
  have hmul := mul_le_mul_of_nonneg_right hcoef Real.pi_pos.le
  linarith

/--
**Three pairwise distinct points of a `2 ^ n`-point set determine an angle larger
than `(1 - 1/n)·π`.**

This is `erdos_szekeres_1960` (Erdős–Szekeres 1960, Theorem 1) with the degenerate
witness `p = r` excluded: if `p = r` then `∠p q p = 0`, contradicting
`(1 - 1/n)·π < ∠p q r`, since `n ≥ 3` gives `(1 - 1/n)·π > 0`.
-/
theorem exists_distinct_angle_gt {n : ℕ} (hn : 3 ≤ n) (S : Finset ℂ)
    (hcard : S.card = 2 ^ n) :
    ∃ x ∈ S, ∃ z ∈ S, ∃ y ∈ S, x ≠ z ∧ y ≠ z ∧ x ≠ y ∧
      (1 - 1 / (n : ℝ)) * π < EuclideanGeometry.angle x z y := by
  obtain ⟨p, hp, q, hq, r, hr, hpq, hrq, hangle⟩ := erdos_szekeres_1960 hn S hcard
  have hpr : p ≠ r := by
    by_contra h
    subst h
    have hz : EuclideanGeometry.angle p q p = 0 := EuclideanGeometry.angle_self_of_ne hpq
    have hc := pi_mul_one_sub_inv_pos hn
    linarith
  exact ⟨p, hp, q, hq, r, hr, hpq, hrq, hpr, hangle⟩

/--
**Erdős–Szekeres (1960).** For `n ≥ 3`, the minimax angle of a `2 ^ n`-point set of
the plane is `π (1 - 1/n)`.

Equivalently: the largest angle that every `2 ^ n`-point set of the plane must
determine is `π (1 - 1/n)`.
-/
theorem erdos_504 {n : ℕ} (hn : 3 ≤ n) :
    minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π := by
  classical
  have hc_pos := pi_mul_one_sub_inv_pos hn
  have hc_le_pi := pi_mul_one_sub_inv_le_pi hn
  -- `minimaxAngle` is the supremum of the admissible angles
  have hmin : minimaxAngle (2 ^ n) = sSup (admissibleAngles (2 ^ n)) := rfl
  rw [hmin]
  -- an angle `b` is admissible exactly when it lies in `[0, π]` and is guaranteed
  -- by every `2 ^ n`-point set
  have hmem (b : ℝ) (hb : b ∈ admissibleAngles (2 ^ n)) :
      b ∈ Set.Icc 0 π ∧
      (∀ S : Finset ℂ, S.card = 2 ^ n →
        ∃ x ∈ S, ∃ z ∈ S, ∃ y ∈ S, x ≠ z ∧ y ≠ z ∧ x ≠ y ∧
          b ≤ EuclideanGeometry.angle x z y) := by
    simpa only [admissibleAngles, Set.mem_ofPred_eq] using hb
  -- the Erdős–Szekeres value is itself an admissible angle
  have hmem_c : (1 - 1 / (n : ℝ)) * π ∈ admissibleAngles (2 ^ n) := by
    simp only [admissibleAngles, Set.mem_ofPred_eq]
    refine ⟨⟨by linarith, hc_le_pi⟩, ?_⟩
    intro S hScard
    obtain ⟨x, hx, z, hz, y, hy, hxz, hyz, hxy, hangle⟩ :=
      exists_distinct_angle_gt hn S hScard
    exact ⟨x, hx, z, hz, y, hy, hxz, hyz, hxy, hangle.le⟩
  apply le_antisymm
  · -- the supremum is at most the Erdős–Szekeres value
    have hne : (admissibleAngles (2 ^ n)).Nonempty :=
      ⟨(1 - 1 / (n : ℝ)) * π, hmem_c⟩
    have hle : ∀ b ∈ admissibleAngles (2 ^ n), b ≤ (1 - 1 / (n : ℝ)) * π := by
      intro b hb
      rcases hmem b hb with ⟨hbIcc, hbforall⟩
      by_contra hnot
      have hbc : (1 - 1 / (n : ℝ)) * π < b := lt_of_not_ge hnot
      have hε : 0 < b - (1 - 1 / (n : ℝ)) * π := by linarith
      obtain ⟨S, hScard, hang⟩ :=
        exists_config_angle_lt (t := n) (by omega)
          (ε := b - (1 - 1 / (n : ℝ)) * π) hε
      obtain ⟨x, hx, z, hz, y, hy, hxz, hyz, hxy, hbxy⟩ := hbforall S hScard
      have hlt := hang x hx z hz y hy hxz hyz
      linarith
    exact csSup_le hne hle
  · -- the Erdős–Szekeres value is at most the supremum
    have hbdd : BddAbove (admissibleAngles (2 ^ n)) := by
      refine ⟨π, ?_⟩
      intro b hb
      exact (hmem b hb).1.2
    exact le_csSup hbdd hmem_c

/-! ## Axiom audit

Running this file (or `lake build`) prints the transitive axiom dependencies of
every target theorem.  Each line must report exactly the three standard Lean
foundations `propext`, `Classical.choice` and `Quot.sound`; in particular no
`sorryAx` and no `Lean.ofReduceBool` (i.e. no `native_decide`) may appear. -/

#print axioms erdos_504
#print axioms exists_distinct_angle_gt
#print axioms exists_angle_gt
#print axioms exists_config_angle_lt
#print axioms erdos_szekeres_1960

end Erdos504
