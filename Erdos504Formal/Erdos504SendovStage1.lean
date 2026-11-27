/-
The gap in Sendov's Lemma 4.1 (the asserted s = 4 maxima) was first publicly
reported by NoahPuckett-IO in teorth/erdosproblems#494 (2026-10-26,
https://github.com/teorth/erdosproblems/issues/494), and this development
independently supplies exact-coordinate counterexamples, Lean machine checks,
and a refutation of the published proof along the Lemma 4.1 to Lemma 4.2 to
Theorem 4.1 chain.
-/

import Erdos504Formal.Erdos504StrictCounting

open scoped BigOperators

namespace Erdos504.SendovStage1

noncomputable def projectiveDir (z : ℂ) : ℝ :=
  let a := Complex.arg z / Real.pi
  a - (Int.floor a : ℝ)

structure CenterGapData (s : ℕ) where
  center : Fin s → ℂ
  injective : Function.Injective center
  other : (i : Fin s) → Fin (s - 1) ≃ {j : Fin s // j ≠ i}
  dir : Fin s → Fin (s - 1) → ℝ
  dir_spec : ∀ i j, dir i j =
    projectiveDir (center (other i j).val - center i)
  dir_strictMono : ∀ i, StrictMono (dir i)

noncomputable def cyclicGap {d : ℕ} (row : Fin d → ℝ) (j : Fin d) : ℝ :=
  if h : j.val + 1 < d then row ⟨j.val + 1, h⟩ - row j
  else 1 + row ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt⟩ - row j

noncomputable def gapExponent {s : ℕ} (D : CenterGapData s) (t : ℝ)
    (i : Fin s) : ℕ :=
  ∑ j : Fin (s - 1), (Int.floor (t * cyclicGap (D.dir i) j) - 1).toNat

noncomputable def centerWeight {s : ℕ} (D : CenterGapData s) (t : ℝ) : ℕ :=
  ∑ i : Fin s, 2 ^ gapExponent D t i

noncomputable def angleAt (t : ℝ) : ℝ := (1 - 1 / t) * Real.pi

def CenterAngleCap {s : ℕ} (D : CenterGapData s) (t : ℝ) : Prop :=
  ∀ i j k : Fin s, i ≠ j → k ≠ j →
    EuclideanGeometry.angle (D.center i) (D.center j) (D.center k) ≤ angleAt t

def RemovalDeltaGoal : Prop :=
  ∀ {s : ℕ} (D : CenterGapData (s + 1)) (D' : CenterGapData s)
    (i : Fin (s + 1)) (t : ℝ), 2 ≤ s → 0 ≤ t →
    (∀ j, D'.center j = D.center (i.succAbove j)) →
    ∀ j, gapExponent D t (i.succAbove j) ≤ gapExponent D' t j ∧
      gapExponent D' t j ≤ gapExponent D t (i.succAbove j) + 2

def CenterBoundUpperGoal : Prop :=
  ∀ {s m : ℕ} (D : CenterGapData s) (t : ℝ), 2 ≤ s → 2 ≤ m →
    (m : ℝ) + 1 / 2 ≤ t → t < (m : ℝ) + 1 → CenterAngleCap D t →
    centerWeight D t ≤ 2 ^ m + 2 ^ (m - 2)

def CenterBoundLowerGoal : Prop :=
  ∀ {s m : ℕ} (D : CenterGapData s) (t : ℝ), 2 ≤ s → 2 ≤ m →
    (m : ℝ) ≤ t → t < (m : ℝ) + 1 / 2 → CenterAngleCap D t →
    centerWeight D t ≤ 2 ^ m

structure PerfectGCCardinalityWitness {s : ℕ} (D : CenterGapData s) (t : ℝ)
    (total : ℕ) where
  angleCap : CenterAngleCap D t
  leaves : Fin s → ℕ
  internalAxes : Fin s → ℕ
  partitionCard : total = ∑ i : Fin s, leaves i
  leafPower : ∀ i, leaves i = 2 ^ internalAxes i
  axesLeCapacity : ∀ i, internalAxes i ≤ gapExponent D t i

lemma PerfectGCCardinalityWitness.total_le_weight {s : ℕ} {D : CenterGapData s}
    {t : ℝ} {total : ℕ} (W : PerfectGCCardinalityWitness D t total) :
    total ≤ centerWeight D t := by
  rw [W.partitionCard]
  unfold centerWeight
  apply Finset.sum_le_sum
  intro i _
  rw [W.leafPower i]
  exact Nat.pow_le_pow_right (by decide) (W.axesLeCapacity i)

def OrdinaryCenterBridgeGoal : Prop :=
  ∀ (S : Finset ℂ) (t : ℝ), 2 ≤ t → 2 ≤ S.card →
    (∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
      EuclideanGeometry.angle p q r ≤ angleAt t) →
    ∃ D : CenterGapData S.card,
      Set.range D.center = (S : Set ℂ) ∧ CenterAngleCap D t ∧ S.card ≤ centerWeight D t

def StrictToUpperBandGoal : Prop :=
  ∀ (n : ℕ) (S : Finset ℂ), 3 ≤ n →
    (∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
      EuclideanGeometry.angle p q r < angleAt (n : ℝ)) →
    ∃ t : ℝ, (n : ℝ) - 1 / 2 ≤ t ∧ t < (n : ℝ) ∧
      ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
        EuclideanGeometry.angle p q r ≤ angleAt t

end Erdos504.SendovStage1
