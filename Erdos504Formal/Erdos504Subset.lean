/-
Subsets, deletion of points, and the monotonicity of the minimax angle.

This file is **Phase-1a scaffolding** for the Sendov (1995) complete determination
of `α_N` (Erdős Problem #504).  It contains only *tooling* results; every
declaration here is complete and `sorry`-free, and none of them is a new
mathematical statement about problem 504 itself:

* `forall_angle_lt_of_subset` — deleting points cannot create an angle;
* `exists_config_angle_lt_card_le` — the Szekeres (1941) construction
  restricted to any smaller number of points.  This is the *upper-bound half*
  of the large-`N` branch of Sendov's formula, and it is essentially free:
  one deletes points from the `2^t`-point Szekeres configuration;
* `admissibleAngles_mono`, `minimaxAngle_mono` — `α_N` is nondecreasing in `N`.

The mathematical content of Sendov's formula itself is **not** proved here; see
`Erdos504Formal/Erdos504Sendov` (a skeleton whose three atomic ingredients are
still `sorry`) and `Erdos504Formal/Erdos504SendovShell` (the closed template).

Reference for the two published results used below:

* G. Szekeres, *On an extremum problem in the plane*, Amer. J. Math. 63 (1941),
  208–210 — `Erdos504.exists_config_angle_lt`;
* P. Erdős and G. Szekeres, *On some extremum problems in elementary geometry*,
  Ann. Univ. Sci. Budapest. Eötvös Sect. Math. 3–4 (1960/61), 53–62.
-/
import Erdos504Formal.Erdos504Minimax
import Erdos504Formal.Erdos504StrictCounting

namespace Erdos504

open Real EuclideanGeometry

/-- **Deleting points cannot create an angle.**  If every angle determined by
`T` is `< A`, then so is every angle determined by a subset `S ⊆ T`. -/
theorem forall_angle_lt_of_subset {T S : Finset ℂ} {A : ℝ} (hST : S ⊆ T)
    (hT : ∀ p ∈ T, ∀ q ∈ T, ∀ r ∈ T, p ≠ q → r ≠ q →
      EuclideanGeometry.angle p q r < A) :
    ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
      EuclideanGeometry.angle p q r < A := by
  intro p hp q hq r hr hpq hrq
  exact hT p (hST hp) q (hST hq) r (hST hr) hpq hrq

/-- **The Szekeres construction can be restricted to fewer points.**

For `t ≥ 1`, `ε > 0` and any `N ≤ 2 ^ t` there is a set of exactly `N` points
of the plane all of whose angles are smaller than `(1 - 1/t)·π + ε`.

This is `Erdos504.exists_config_angle_lt` (Szekeres 1941) with points deleted:
deleting points creates no new angle, and `2 ^ t` points remain available. -/
theorem exists_config_angle_lt_card_le {t N : ℕ} (ht : 0 < t) {ε : ℝ} (hε : 0 < ε)
    (hN : N ≤ 2 ^ t) :
    ∃ S : Finset ℂ, S.card = N ∧
      ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
        EuclideanGeometry.angle p q r < (1 - 1 / (t : ℝ)) * π + ε := by
  obtain ⟨T, hTcard, hang⟩ := exists_config_angle_lt (ht := ht) (ε := ε) hε
  obtain ⟨S, hST, hScard⟩ :=
    Finset.exists_subset_card_eq (s := T) (n := N) (by omega)
  refine ⟨S, hScard, ?_⟩
  intro p hp q hq r hr hpq hrq
  exact hang p (hST hp) q (hST hq) r (hST hr) hpq hrq

/-- **Admissible angles for `N` points are admissible for any larger `N`.**

If every `N`-point set determines an angle `≥ b`, then so does every
`N'`-point set with `N ≤ N'`: take an `N`-point subset of it. -/
theorem admissibleAngles_mono {N N' : ℕ} (h : N ≤ N') :
    admissibleAngles N ⊆ admissibleAngles N' := by
  intro b hb
  obtain ⟨hbIcc, hbforall⟩ := by
    simpa only [admissibleAngles, Set.mem_ofPred_eq] using hb
  simp only [admissibleAngles, Set.mem_ofPred_eq]
  refine ⟨hbIcc, ?_⟩
  intro S hScard
  obtain ⟨A, hSA, hAcard⟩ :=
    Finset.exists_subset_card_eq (s := S) (n := N) (by omega)
  obtain ⟨x, hx, z, hz, y, hy, hxz, hyz, hxy, hangle⟩ := hbforall A hAcard
  exact ⟨x, hSA hx, z, hSA hz, y, hSA hy, hxz, hyz, hxy, hangle⟩

/-- **The minimax angle is nondecreasing in the number of points.**

For `3 ≤ N ≤ N'` we have `α_N ≤ α_{N'}`. -/
theorem minimaxAngle_mono {N N' : ℕ} (hN : 3 ≤ N) (h : N ≤ N') :
    minimaxAngle N ≤ minimaxAngle N' := by
  have hmin : minimaxAngle N = sSup (admissibleAngles N) := rfl
  have hmin' : minimaxAngle N' = sSup (admissibleAngles N') := rfl
  rw [hmin, hmin']
  -- the angle `0` is admissible for `N`
  have hzero : (0 : ℝ) ∈ admissibleAngles N := by
    simp only [admissibleAngles, Set.mem_ofPred_eq]
    refine ⟨⟨by linarith, Real.pi_pos.le⟩, ?_⟩
    intro S hScard
    obtain ⟨x, hx, z, hz, y, hy, hxz, hzy, hxy⟩ :=
      exists_three_distinct_sc (S := S) (by omega)
    exact ⟨x, hx, z, hz, y, hy, hxz, hzy.symm, hxy,
      EuclideanGeometry.angle_nonneg x z y⟩
  have hne : (admissibleAngles N).Nonempty := ⟨0, hzero⟩
  have hbdd : BddAbove (admissibleAngles N') := by
    refine ⟨π, ?_⟩
    intro b hb
    obtain ⟨hbIcc, -⟩ := by
      simpa only [admissibleAngles, Set.mem_ofPred_eq] using hb
    exact hbIcc.2
  refine csSup_le hne ?_
  intro b hb
  exact le_csSup hbdd (admissibleAngles_mono h hb)

/-! ## Axiom audit

The declarations of this file are complete: running the file prints their
transitive axiom dependencies, and every line must report exactly the three
standard Lean foundations `propext`, `Classical.choice` and `Quot.sound`. -/

#print axioms forall_angle_lt_of_subset
#print axioms exists_config_angle_lt_card_le
#print axioms admissibleAngles_mono
#print axioms minimaxAngle_mono

end Erdos504
