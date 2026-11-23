/-
The generic `sSup` shell for a minimax-angle determination.

This file is **Phase-1a scaffolding** for the Sendov (1995) complete
determination of `α_N` (Erdős Problem #504).  It is the reusable template
that turns a pair of *atomic ingredients* into a minimax-angle identity:

* the **lower half** — every `N`-point set determines an angle `≥ V`;
  equivalently, a *counting bound*: if all angles of a set are `< V` then the
  set has at most `N - 1` points;
* the **upper half** — for every `ε > 0` there is an `N`-point set all of whose
  angles are `< V + ε`.

This is exactly the argument of `Erdos504.erdos_504`, but with the two halves
abstracted so that it can be instantiated at an arbitrary `N` and an arbitrary
value `V`.  No new mathematics about problem 504 is claimed here: the file
contains no statement about `α_N` for a specific `N`.

Every declaration is complete and `sorry`-free.
-/
import Erdos504Formal.Erdos504Minimax

namespace Erdos504

open Real EuclideanGeometry

/-- **The generic minimax-angle shell.**

Suppose `0 < V ≤ π`, every `N`-point set determines an angle `≥ V`, and for
every `ε > 0` there is an `N`-point set all of whose angles are `< V + ε`.
Then `α_N = V`. -/
theorem minimaxAngle_eq_of_bounds {N : ℕ} {V : ℝ}
    (hV0 : 0 < V) (hVpi : V ≤ π)
    (hLower : ∀ S : Finset ℂ, S.card = N →
      ∃ x ∈ S, ∃ z ∈ S, ∃ y ∈ S, x ≠ z ∧ y ≠ z ∧
        V ≤ EuclideanGeometry.angle x z y)
    (hUpper : ∀ ε : ℝ, 0 < ε →
      ∃ S : Finset ℂ, S.card = N ∧
        ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
          EuclideanGeometry.angle p q r < V + ε) :
    minimaxAngle N = V := by
  classical
  have hmin : minimaxAngle N = sSup (admissibleAngles N) := rfl
  rw [hmin]
  have hmem (b : ℝ) (hb : b ∈ admissibleAngles N) :
      b ∈ Set.Icc 0 π ∧
      (∀ S : Finset ℂ, S.card = N →
        ∃ x ∈ S, ∃ z ∈ S, ∃ y ∈ S, x ≠ z ∧ y ≠ z ∧ x ≠ y ∧
          b ≤ EuclideanGeometry.angle x z y) := by
    simpa only [admissibleAngles, Set.mem_ofPred_eq] using hb
  -- `V` is itself an admissible angle
  have hmem_c : V ∈ admissibleAngles N := by
    simp only [admissibleAngles, Set.mem_ofPred_eq]
    refine ⟨⟨hV0.le, hVpi⟩, ?_⟩
    intro S hScard
    obtain ⟨x, hx, z, hz, y, hy, hxz, hyz, hangle⟩ := hLower S hScard
    -- the three points are pairwise distinct: `x ≠ y` follows from `V > 0`
    have hxy : x ≠ y := by
      by_contra h
      subst h
      have hz0 : EuclideanGeometry.angle x z x = 0 :=
        EuclideanGeometry.angle_self_of_ne hxz
      linarith
    exact ⟨x, hx, z, hz, y, hy, hxz, hyz, hxy, hangle⟩
  apply le_antisymm
  · -- no admissible angle exceeds `V`
    have hne : (admissibleAngles N).Nonempty := ⟨V, hmem_c⟩
    have hle : ∀ b ∈ admissibleAngles N, b ≤ V := by
      intro b hb
      rcases hmem b hb with ⟨hbIcc, hbforall⟩
      by_contra hnot
      have hbc : V < b := lt_of_not_ge hnot
      have hε : 0 < b - V := by linarith
      obtain ⟨S, hScard, hang⟩ := hUpper (b - V) hε
      obtain ⟨x, hx, z, hz, y, hy, hxz, hyz, hxy, hbxy⟩ := hbforall S hScard
      have hlt := hang x hx z hz y hy hxz hyz
      linarith
    exact csSup_le hne hle
  · -- `V` does not exceed the supremum
    have hbdd : BddAbove (admissibleAngles N) := by
      refine ⟨π, ?_⟩
      intro b hb
      exact (hmem b hb).1.2
    exact le_csSup hbdd hmem_c

/-- **The generic minimax-angle shell, with the lower half given as a counting
bound.**

Suppose `0 < V ≤ π`, every set whose angles are all `< V` has fewer than `N`
points, and for every `ε > 0` there is an `N`-point set all of whose angles are
`< V + ε`.  Then `α_N = V`. -/
theorem minimaxAngle_eq_of_counting {N : ℕ} {V : ℝ}
    (hV0 : 0 < V) (hVpi : V ≤ π)
    (hcount : ∀ S : Finset ℂ,
      (∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
        EuclideanGeometry.angle p q r < V) → S.card < N)
    (hUpper : ∀ ε : ℝ, 0 < ε →
      ∃ S : Finset ℂ, S.card = N ∧
        ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
          EuclideanGeometry.angle p q r < V + ε) :
    minimaxAngle N = V := by
  refine minimaxAngle_eq_of_bounds hV0 hVpi ?_ hUpper
  intro S hScard
  by_contra hcon
  have hnot : ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
      EuclideanGeometry.angle p q r < V := by
    intro p hp q hq r hr hpq hrq
    by_contra hlt
    have hge : V ≤ EuclideanGeometry.angle p q r := le_of_not_gt hlt
    exact hcon ⟨p, hp, q, hq, r, hr, hpq, hrq, hge⟩
  have hlt := hcount S hnot
  omega

/-- The value `π (1 - 1/n)` satisfies `0 < π (1 - 1/n) ≤ π` whenever `n ≥ 3`. -/
theorem pi_mul_one_sub_inv_pos_le_pi {n : ℕ} (hn : 3 ≤ n) :
    0 < (1 - 1 / (n : ℝ)) * π ∧ (1 - 1 / (n : ℝ)) * π ≤ π := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < n := by linarith
  have hdiv_pos : (0 : ℝ) < 1 / n := by positivity
  have hinv : (1 : ℝ) / n < 1 := (div_lt_iff₀ hn_pos).2 (by linarith)
  have hcoef : (0 : ℝ) < 1 - 1 / (n : ℝ) := by linarith
  have hcoef1 : (1 : ℝ) - 1 / (n : ℝ) ≤ 1 := by linarith
  refine ⟨mul_pos hcoef Real.pi_pos, ?_⟩
  calc (1 - 1 / (n : ℝ)) * π ≤ 1 * π :=
        mul_le_mul_of_nonneg_right hcoef1 Real.pi_pos.le
       _ = π := one_mul π

/-- The value `π (1 - 2/(2n-1))` satisfies `0 < π (1 - 2/(2n-1)) ≤ π` whenever
`n ≥ 3`. -/
theorem pi_mul_two_sub_two_div_pos_le_pi {n : ℕ} (hn : 3 ≤ n) :
    0 < (1 - 2 / (2 * (n : ℝ) - 1)) * π ∧
      (1 - 2 / (2 * (n : ℝ) - 1)) * π ≤ π := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : (0 : ℝ) < 2 * (n : ℝ) - 1 := by linarith
  have hfrac_pos : (0 : ℝ) < 2 / (2 * (n : ℝ) - 1) := by positivity
  have hfrac : (2 : ℝ) / (2 * (n : ℝ) - 1) < 1 := (div_lt_iff₀ hden).2 (by linarith)
  have hcoef : (0 : ℝ) < 1 - 2 / (2 * (n : ℝ) - 1) := by linarith
  have hcoef1 : (1 : ℝ) - 2 / (2 * (n : ℝ) - 1) ≤ 1 := by linarith
  refine ⟨mul_pos hcoef Real.pi_pos, ?_⟩
  calc (1 - 2 / (2 * (n : ℝ) - 1)) * π ≤ 1 * π :=
        mul_le_mul_of_nonneg_right hcoef1 Real.pi_pos.le
       _ = π := one_mul π

/-! ## Axiom audit

Every declaration of this file is complete: running the file prints their
transitive axiom dependencies, and every line must report exactly the three
standard Lean foundations `propext`, `Classical.choice` and `Quot.sound`. -/

#print axioms minimaxAngle_eq_of_bounds
#print axioms minimaxAngle_eq_of_counting
#print axioms pi_mul_one_sub_inv_pos_le_pi
#print axioms pi_mul_two_sub_two_div_pos_le_pi

end Erdos504
