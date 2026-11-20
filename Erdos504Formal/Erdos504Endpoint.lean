/-
Lean formalisation of the *endpoint* half of Erdős Problem #504
(Blumenthal's minimax angle problem), contributed by the submitter.

Background.  Erdős and Szekeres (1960) proved

    α_{2^n} = α_{2^n - 1} = π (1 - 1/n)      (n ≥ 3).

The `2^n` half is fully formalised in `Erdos504Formal/Erdos504Minimax.lean`
(using `Erdos504.erdos_szekeres_1960` and `Erdos504.exists_config_angle_lt`).
This file treats the endpoint `α_{2^n - 1}`.

## What is proved here

* `exists_config_angle_lt_card_sub_one` — Szekeres' construction with one point
  deleted: for every `ε > 0` there is a set of exactly `2^n - 1` points all of
  whose angles are below `π (1 - 1/n) + ε`.
* `minimaxAngle_card_sub_one_le` — the supremum half of the endpoint,
  `α_{2^n - 1} ≤ π (1 - 1/n)`.
* `erdos_504_endpoint_exists_of_card_le` — the guaranteed-angle half of the
  endpoint.
* `erdos_504_endpoint_of_card_le` — the endpoint itself, unconditional.

## The counting ingredient

The sharp sector-counting bound

    (all angles of `S` are < π (1 - 1/n))  ⟹  S.card ≤ 2^n - 2,

the sharp counterpart of `Erdos504.card_le_two_pow_of_angle_le` (which only
gives `S.card ≤ 2 ^ n` for the non-strict hypothesis `≤ π (1 - 1/n)`), is
proved in `Erdos504Formal/Erdos504StrictCounting.lean` as
`Erdos504.strictCountingBound`, following Erdős–Szekeres (1960), Theorem 3:
an interior point isolated in colour `0` after a rotation, a hull vertex
isolated in some colour, and the defect form of Lemma 4
(`emptyCount_sum_le`) with `k = 1`.

Everything else — the supremum bookkeeping, the `ε`-sharpness, the deletion
of a point from Szekeres' construction — is proved here.

Reference: P. Erdős and G. Szekeres, *On some extremum problems in elementary
geometry*, Ann. Univ. Sci. Budapest. Eötvös Sect. Math. 3-4 (1960/61), 53–62.
-/
import Erdos504Formal.Erdos504
import Erdos504Formal.Erdos504Minimax
import Erdos504Formal.Erdos504StrictCounting

namespace Erdos504

open Real EuclideanGeometry

/-! ## Auxiliary facts -/

/-- The Erdős–Szekeres value `π (1 - 1/n)` is positive whenever `n ≥ 3`. -/
private lemma pi_mul_one_sub_inv_pos' {n : ℕ} (hn : 3 ≤ n) :
    0 < (1 - 1 / (n : ℝ)) * π := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < n := by linarith
  have hinv : (1 : ℝ) / n < 1 := (div_lt_iff₀ hn_pos).2 (by linarith)
  have hcoef : 0 < 1 - 1 / (n : ℝ) := by linarith
  exact mul_pos hcoef Real.pi_pos

/-- The Erdős–Szekeres value `π (1 - 1/n)` is at most `π`. -/
private lemma pi_mul_one_sub_inv_le_pi' {n : ℕ} (hn : 3 ≤ n) :
    (1 - 1 / (n : ℝ)) * π ≤ π := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < n := by linarith
  have hinv : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  have hcoef : 1 - 1 / (n : ℝ) ≤ 1 := by linarith
  have hmul := mul_le_mul_of_nonneg_right hcoef Real.pi_pos.le
  linarith

/-- `2 ^ n ≥ 8` for `n ≥ 3`. -/
private lemma two_pow_ge_eight {n : ℕ} (hn : 3 ≤ n) : 8 ≤ 2 ^ n := by
  have h1 : (1 : ℕ) ≤ 2 ^ (n - 3) := Nat.one_le_pow (n - 3) 2 (by norm_num)
  have h2 : 8 * 1 ≤ 8 * 2 ^ (n - 3) := Nat.mul_le_mul_left 8 h1
  have h3 : 8 * 2 ^ (n - 3) = 2 ^ n := by
    calc 8 * 2 ^ (n - 3) = 2 ^ 3 * 2 ^ (n - 3) := by norm_num
      _ = 2 ^ (3 + (n - 3)) := (Nat.pow_add 2 3 (n - 3)).symm
      _ = 2 ^ n := by rw [show (3 : ℕ) + (n - 3) = n by omega]
  omega

/-- A `Finset` of cardinality at least `3` contains three pairwise distinct
points. -/
private lemma exists_three_distinct {S : Finset ℂ} (hS : 3 ≤ S.card) :
    ∃ x ∈ S, ∃ z ∈ S, ∃ y ∈ S, x ≠ z ∧ z ≠ y ∧ x ≠ y := by
  have hne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hEmpty
    have hcard0 : S.card = 0 := Finset.card_eq_zero.mpr hEmpty
    omega
  obtain ⟨x, hx⟩ := hne
  have hcard₁ : (S.erase x).card = S.card - 1 := Finset.card_erase_of_mem hx
  have hne₁ : (S.erase x).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hEmpty
    have hcard0 : (S.erase x).card = 0 := Finset.card_eq_zero.mpr hEmpty
    omega
  obtain ⟨z, hz⟩ := hne₁
  have hz' : z ≠ x ∧ z ∈ S := Finset.mem_erase.mp hz
  have hcard₂ : ((S.erase x).erase z).card = (S.erase x).card - 1 :=
    Finset.card_erase_of_mem hz
  have hne₂ : ((S.erase x).erase z).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hEmpty
    have hcard0 : ((S.erase x).erase z).card = 0 := Finset.card_eq_zero.mpr hEmpty
    omega
  obtain ⟨y, hy⟩ := hne₂
  have hy' : y ≠ z ∧ y ∈ S.erase x := Finset.mem_erase.mp hy
  have hy'' : y ≠ x ∧ y ∈ S := Finset.mem_erase.mp hy'.2
  exact ⟨x, hx, z, hz'.2, y, hy''.2, hz'.1.symm, hy'.1.symm, hy''.1.symm⟩

/-! ## The sharp side of the endpoint: Szekeres' construction minus one point -/

/--
**Szekeres (1941), upper bound for `2^n - 1` points.**  For every `ε > 0` there
is a set of exactly `2^n - 1` points of the plane all of whose angles are
smaller than `π (1 - 1/n) + ε`.

This is `Erdos504.exists_config_angle_lt` with one point deleted: deleting a
point cannot create an angle, and `2^n - 1` points remain.
-/
theorem exists_config_angle_lt_card_sub_one {n : ℕ} (hn : 3 ≤ n) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ S : Finset ℂ, S.card = 2 ^ n - 1 ∧
      ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
        EuclideanGeometry.angle p q r < (1 - 1 / (n : ℝ)) * π + ε := by
  obtain ⟨T, hTcard, hang⟩ :=
    exists_config_angle_lt (t := n) (by omega) (ε := ε) hε
  have h8 := two_pow_ge_eight hn
  have hTne : T.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hEmpty
    have hcard0 : T.card = 0 := Finset.card_eq_zero.mpr hEmpty
    omega
  obtain ⟨t, ht⟩ := hTne
  refine ⟨T.erase t, ?_, ?_⟩
  · rw [Finset.card_erase_of_mem ht, hTcard]
  · intro p hp q hq r hr hpq hrq
    exact hang p (Finset.mem_erase.mp hp).2 q (Finset.mem_erase.mp hq).2
      r (Finset.mem_erase.mp hr).2 hpq hrq

/--
**The supremum half of the endpoint.**  For `n ≥ 3`,

    α_{2^n - 1} ≤ π (1 - 1/n).

In words: no number larger than `π (1 - 1/n)` is guaranteed by *every*
`2^n - 1`-point set of the plane.
-/
theorem minimaxAngle_card_sub_one_le {n : ℕ} (hn : 3 ≤ n) :
    minimaxAngle (2 ^ n - 1) ≤ (1 - 1 / (n : ℝ)) * π := by
  classical
  have hmin : minimaxAngle (2 ^ n - 1) = sSup (admissibleAngles (2 ^ n - 1)) := rfl
  rw [hmin]
  -- the admissible set is nonempty: the angle `0` is always guaranteed
  have hne : (admissibleAngles (2 ^ n - 1)).Nonempty := by
    refine ⟨0, ?_⟩
    simp only [admissibleAngles, Set.mem_ofPred_eq]
    refine ⟨⟨by linarith, Real.pi_pos.le⟩, ?_⟩
    intro S hScard
    have h3 : 3 ≤ S.card := by
      have h8 := two_pow_ge_eight hn
      omega
    obtain ⟨x, hx, z, hz, y, hy, hxz, hzy, hxy⟩ := exists_three_distinct h3
    exact ⟨x, hx, z, hz, y, hy, hxz, hzy.symm, hxy,
      EuclideanGeometry.angle_nonneg x z y⟩
  refine csSup_le hne ?_
  intro b hb
  simp only [admissibleAngles, Set.mem_ofPred_eq] at hb
  rcases hb with ⟨_, hbforall⟩
  by_contra hnot
  have hbc : (1 - 1 / (n : ℝ)) * π < b := lt_of_not_ge hnot
  have hε : 0 < b - (1 - 1 / (n : ℝ)) * π := by linarith
  obtain ⟨S, hScard, hang⟩ := exists_config_angle_lt_card_sub_one hn hε
  obtain ⟨x, hx, z, hz, y, hy, hxz, hyz, hxy, hbxy⟩ := hbforall S hScard
  have hlt : EuclideanGeometry.angle x z y < (1 - 1 / (n : ℝ)) * π + (b - (1 - 1 / (n : ℝ)) * π) :=
    hang x hx z hz y hy hxz hyz
  linarith

/-! ## The endpoint -/

/--
**The guaranteed-angle half of the endpoint.**  Every set of `2^n - 1` points
of the plane contains three pairwise distinct points determining an angle of
at least `π (1 - 1/n)`.

Indeed, a `2^n - 1`-point set cannot have all of its angles *strictly* below
`π (1 - 1/n)`, since the strict counting bound `strictCountingBound`
(`Erdos504Formal/Erdos504StrictCounting.lean`) would force `S.card ≤ 2^n - 2`.
-/
theorem erdos_504_endpoint_exists_of_card_le {n : ℕ} (hn : 3 ≤ n)
    (S : Finset ℂ) (hcard : S.card = 2 ^ n - 1) :
    ∃ x ∈ S, ∃ z ∈ S, ∃ y ∈ S, x ≠ z ∧ y ≠ z ∧ x ≠ y ∧
      (1 - 1 / (n : ℝ)) * π ≤ EuclideanGeometry.angle x z y := by
  have hc_pos := pi_mul_one_sub_inv_pos' hn
  have h8 := two_pow_ge_eight hn
  have hex : ∃ x ∈ S, ∃ z ∈ S, ∃ y ∈ S, x ≠ z ∧ y ≠ z ∧
      (1 - 1 / (n : ℝ)) * π ≤ EuclideanGeometry.angle x z y := by
    by_contra hcon
    have hnot : ∀ x ∈ S, ∀ z ∈ S, ∀ y ∈ S, x ≠ z → y ≠ z →
        EuclideanGeometry.angle x z y < (1 - 1 / (n : ℝ)) * π := by
      intro x hx z hz y hy hxz hyz
      by_contra hlt
      have hge : (1 - 1 / (n : ℝ)) * π ≤ EuclideanGeometry.angle x z y :=
        le_of_not_gt hlt
      exact hcon ⟨x, hx, z, hz, y, hy, hxz, hyz, hge⟩
    exact absurd (strictCountingBound hn S hnot) (by omega)
  obtain ⟨x, hx, z, hz, y, hy, hxz, hyz, hge⟩ := hex
  have hxy : x ≠ y := by
    by_contra h
    subst h
    have hz : EuclideanGeometry.angle x z x = 0 :=
      EuclideanGeometry.angle_self_of_ne hxz
    linarith
  exact ⟨x, hx, z, hz, y, hy, hxz, hyz, hxy, hge⟩

/--
**The endpoint.**  For `n ≥ 3`,

    α_{2^n - 1} = π (1 - 1/n).

The proof uses only the two halves that are established elsewhere:

* the supremum half, from `minimaxAngle_card_sub_one_le`;
* the guaranteed-angle half, from `erdos_504_endpoint_exists_of_card_le`
  (which rests on `strictCountingBound`).
-/
theorem erdos_504_endpoint_of_card_le {n : ℕ} (hn : 3 ≤ n) :
    minimaxAngle (2 ^ n - 1) = (1 - 1 / (n : ℝ)) * π := by
  classical
  have hc_pos := pi_mul_one_sub_inv_pos' hn
  have hc_le_pi := pi_mul_one_sub_inv_le_pi' hn
  have hmin : minimaxAngle (2 ^ n - 1) = sSup (admissibleAngles (2 ^ n - 1)) := rfl
  rw [hmin]
  -- the Erdős–Szekeres value is admissible
  have hmem_c : (1 - 1 / (n : ℝ)) * π ∈ admissibleAngles (2 ^ n - 1) := by
    simp only [admissibleAngles, Set.mem_ofPred_eq]
    refine ⟨⟨hc_pos.le, hc_le_pi⟩, ?_⟩
    intro S hScard
    obtain ⟨x, hx, z, hz, y, hy, hxz, hyz, hxy, hge⟩ :=
      erdos_504_endpoint_exists_of_card_le hn S hScard
    exact ⟨x, hx, z, hz, y, hy, hxz, hyz, hxy, hge⟩
  apply le_antisymm
  · exact minimaxAngle_card_sub_one_le hn
  · have hbdd : BddAbove (admissibleAngles (2 ^ n - 1)) := by
      refine ⟨π, ?_⟩
      intro b hb
      simp only [admissibleAngles, Set.mem_ofPred_eq] at hb
      exact hb.1.2
    exact le_csSup hbdd hmem_c

/-! ## Axiom audit

Running this file (or `lake build`) prints the transitive axiom dependencies of
every target theorem.  Each line must report exactly the three standard Lean
foundations `propext`, `Classical.choice` and `Quot.sound`; in particular no
`sorryAx` and no `Lean.ofReduceBool` (i.e. no `native_decide`) may appear. -/

#print axioms exists_config_angle_lt_card_sub_one
#print axioms minimaxAngle_card_sub_one_le
#print axioms strictCountingBound
#print axioms erdos_504_endpoint_exists_of_card_le
#print axioms erdos_504_endpoint_of_card_le
#print axioms erdos_504
#print axioms erdos_szekeres_1960

end Erdos504
