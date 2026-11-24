/-
Lean development for Phase-1b of the Sendov (1995) counting-bound spike, second
step: the `n = 3` instance.

    all angles of `S` are strictly below `2 * π / 3`  ⟹  `S.card ≤ 5`

This is the `n = 3` instance of Sendov's counting bound

    all angles of `S` are strictly below `π (1 - 1/n)`  ⟹  `S.card ≤ 2^(n-1) + 2^(n-3)`

because `2^(3-1) + 2^(3-3) = 4 + 1 = 5`.  It is *strictly stronger* than the
Erdős–Szekeres (1960) bound `strictCountingBound`, which only yields
`2^3 - 2 = 6` at `n = 3`; the regular pentagon shows that `5` is attained.

The proof has two ingredients.

* `exists_angle_ge_two_pi_div_three_of_interior` — a point of a set in general
  position that is *not* a vertex of the convex hull is seen under an angle
  `≥ 2 * π / 3` from some pair of other points of the set.  This is the
  classical "point inside a triangle" argument: by Carathéodory's theorem the
  point lies in the convex hull of at most three extreme points of the set; if
  it lies on a segment of two of them the angle there is `π`, and if it lies
  strictly inside the triangle of three of them, the three angles there add up
  to `2 * π` (`Erdos504.angle_sum_interior`).

* `sendov_counting_bound_n3` — a set of `6` points in the plane always
  determines an angle `≥ 2 * π / 3`.  Indeed a set of `6` points in general
  position has at most `2 * 3 - 1 = 5` vertices of its convex hull
  (`Erdos504.hull_card_le`), hence a point that is not a vertex of the hull,
  and the first ingredient applies.

References: I. Sendov, *Minimax of the angles in a plane configuration of
points*, Acta Math. Hungar. 69 (1995), 27–46 (the counting bound
`2^(n-1) + 2^(n-3)`); P. Erdős and G. Szekeres, *On some extremum problems in
elementary geometry*, Ann. Univ. Sci. Budapest Sect. Math. 3–4 (1960/61), 53–62
(Theorem 3, the bound `2^n - 2`).
-/
import Erdos504Formal.Erdos504StrictCounting
import Erdos504Formal.Erdos504SendovSpike

namespace Erdos504

open Real EuclideanGeometry

/-! ## Minkowski's theorem in equality form -/

/-- **Minkowski's theorem.**  The convex hull of a finite set of points of the
plane is the convex hull of the extreme points of its own convex hull. -/
theorem convexHull_eq_convexHull_extremePoints (S : Finset ℂ) :
    convexHull ℝ ((convexHull ℝ (↑S : Set ℂ)).extremePoints ℝ)
      = convexHull ℝ (↑S : Set ℂ) := by
  have hfin : (↑S : Set ℂ).Finite := S.finite_toSet
  have hKM := closure_convexHull_extremePoints (hfin.isCompact_convexHull ℝ)
    (convex_convexHull ℝ (↑S : Set ℂ))
  have hfin2 : ((convexHull ℝ (↑S : Set ℂ)).extremePoints ℝ).Finite :=
    hfin.subset (extremePoints_convexHull_subset' _)
  rw [(hfin2.isClosed_convexHull ℝ).closure_eq] at hKM
  exact hKM

/-! ## Two elementary angle lemmas -/

/-- **Straight angle.**  If `q` is a convex combination of two distinct points
`a`, `b` and is different from both, the angle at `q` between them is `π`. -/
theorem angle_eq_pi_of_combination {a b q : ℂ} {lam mu : ℝ}
    (_hab : a ≠ b) (hlam0 : 0 ≤ lam) (hmu0 : 0 ≤ mu) (hsum : lam + mu = 1)
    (hq : q = lam • a + mu • b) (hqa : q ≠ a) (hqb : q ≠ b) :
    EuclideanGeometry.angle a q b = π := by
  have hmem : q ∈ segment ℝ a b := by
    rw [segment, Set.mem_ofPred_eq]
    exact ⟨lam, mu, hlam0, hmu0, hsum, hq.symm⟩
  have hw : Wbtw ℝ a q b := (mem_segment_iff_wbtw).mp hmem
  exact Sbtw.angle₁₂₃_eq_pi ⟨hw, hqa, hqb⟩

/-- **Interior point of a triangle.**  If `x` lies strictly inside the triangle
`a b c` (witnessed by strictly positive barycentric coordinates summing to `1`),
then one of the three angles at `x` is at least `2 * π / 3`. -/
theorem exists_angle_ge_two_pi_div_three_of_interior_point {a b c x : ℂ} {α β γ : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hsum : α + β + γ = 1)
    (hx : x = α • a + β • b + γ • c)
    (hnc : ¬ Collinear ℝ ({a, b, c} : Set ℂ)) :
    2 * π / 3 ≤ EuclideanGeometry.angle a x b ∨
      2 * π / 3 ≤ EuclideanGeometry.angle b x c ∨
      2 * π / 3 ≤ EuclideanGeometry.angle c x a := by
  have h := angle_sum_interior hα hβ hγ hsum hx hnc
  rcases lt_or_ge (EuclideanGeometry.angle a x b) (2 * π / 3) with h1 | h1
  · rcases lt_or_ge (EuclideanGeometry.angle b x c) (2 * π / 3) with h2 | h2
    · rcases lt_or_ge (EuclideanGeometry.angle c x a) (2 * π / 3) with h3 | h3
      · linarith
      · exact Or.inr (Or.inr h3)
    · exact Or.inr (Or.inl h2)
  · exact Or.inl h1

/-! ## The interior-point lemma -/

/-- **A non-vertex sees a large angle.**  Let `S` be a finite set of points in
general position (no three collinear) and let `q ∈ S` be a point that is *not* a
vertex of the convex hull of `S`.  Then some two points of `S`, different from
`q`, are seen from `q` under an angle of at least `2 * π / 3`.

Proof.  By Minkowski's theorem `q` lies in the convex hull of the extreme
points of `S`; by Carathéodory's theorem it lies in the convex hull of at most
three of them.  If it lies on a segment of two of them the corresponding angle
is `π`.  Otherwise it lies strictly inside a triangle of three of them, and the
three angles there add up to `2 * π`. -/
theorem exists_angle_ge_two_pi_div_three_of_interior {S : Finset ℂ} {q : ℂ}
    (hgen : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c →
      ¬ Collinear ℝ ({a, b, c} : Set ℂ))
    (hq : q ∈ S)
    (hne : q ∉ extremeFinset S) :
    ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ a ≠ q ∧ b ≠ q ∧
      2 * π / 3 ≤ EuclideanGeometry.angle a q b := by
  classical
  set E : Set ℂ := (convexHull ℝ (↑S : Set ℂ)).extremePoints ℝ with hEdef
  have hqnE : q ∉ E := by
    intro h
    exact hne (mem_extremeFinset.mpr h)
  have hEsub : E ⊆ (↑S : Set ℂ) := extremePoints_convexHull_subset' _
  -- Minkowski: the convex hull of `S` is the convex hull of its extreme points
  have hconv : convexHull ℝ E = convexHull ℝ (↑S : Set ℂ) := by
    rw [hEdef]
    exact convexHull_eq_convexHull_extremePoints S
  have hqconv : q ∈ convexHull ℝ E := by
    rw [hconv]
    exact subset_convexHull ℝ _ hq
  -- Carathéodory: `q` lies in the convex hull of an affinely independent
  -- subset of `E`; in the plane such a subset has at most three elements
  obtain ⟨t, htE, htAI, htconv⟩ :
      ∃ t : Finset ℂ, (↑t : Set ℂ) ⊆ E ∧ AffineIndependent ℝ ((↑) : t → ℂ) ∧
        q ∈ convexHull ℝ (↑t : Set ℂ) := by
    rw [convexHull_eq_union] at hqconv
    simp only [exists_prop, Set.mem_iUnion] at hqconv
    obtain ⟨t, ht1, ht2, ht3⟩ := hqconv
    exact ⟨t, ht1, ht2, ht3⟩
  have htcard : t.card ≤ 3 := by
    have h1 : Fintype.card t
        ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : t → ℂ))) + 1 :=
      AffineIndependent.card_le_finrank_succ htAI
    have h2 : Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : t → ℂ)))
        ≤ Module.finrank ℝ ℂ := Submodule.finrank_le _
    have h3 : Fintype.card t = t.card := Fintype.card_coe _
    have h4 : Module.finrank ℝ ℂ = 2 := Complex.finrank_real_complex
    omega
  have htne0 : t.card ≠ 0 := by
    intro h0
    have ht0 : (↑t : Set ℂ) = (∅ : Set ℂ) := by
      have h5 : t = (∅ : Finset ℂ) := Finset.card_eq_zero.mp h0
      simpa using congrArg (fun s : Finset ℂ => (↑s : Set ℂ)) h5
    rw [ht0] at htconv
    rw [convexHull_empty] at htconv
    exact htconv
  have hcard : t.card = 1 ∨ t.card = 2 ∨ t.card = 3 := by omega
  rcases hcard with hcard | hcard | hcard
  · -- `t` is a singleton: `q` would be an extreme point of the hull
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hcard
    have haE : a ∈ E := htE (by simp)
    rw [Finset.convexHull_eq, Set.mem_ofPred_eq] at htconv
    obtain ⟨w, hw0, hw1, hq⟩ := htconv
    have hwa : w a = 1 := by simpa using hw1
    have hq' : q = ∑ y ∈ ({a} : Finset ℂ), w y • y := by
      rw [← hq]
      simp [Finset.centerMass, hw1]
    have hqa : q = a := by
      have h := hq'
      simp at h
      rw [h, hwa]
      simp
    exact False.elim (hqnE (by rw [hqa]; exact haE))
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
    have haE : a ∈ E := htE (by simp)
    have hbE : b ∈ E := htE (by simp)
    have hqa : q ≠ a := by rintro rfl; exact hqnE haE
    have hqb : q ≠ b := by rintro rfl; exact hqnE hbE
    have haS : a ∈ S := hEsub haE
    have hbS : b ∈ S := hEsub hbE
    rw [Finset.convexHull_eq, Set.mem_ofPred_eq] at htconv
    obtain ⟨w, hw0, hw1, hq⟩ := htconv
    have hsum : w a + w b = 1 := by simpa [hab] using hw1
    have hq' : q = ∑ y ∈ ({a, b} : Finset ℂ), w y • y := by
      rw [← hq]
      simp [Finset.centerMass, hw1]
    have hqab : q = w a • a + w b • b := by
      have h := hq'
      simp [hab] at h
      exact h
    have hpi : EuclideanGeometry.angle a q b = π :=
      angle_eq_pi_of_combination hab (hw0 a (by simp)) (hw0 b (by simp)) hsum hqab hqa hqb
    exact ⟨a, haS, b, hbS, hab, hqa.symm, hqb.symm, by linarith [Real.pi_pos]⟩
  · obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hcard
    have haE : a ∈ E := htE (by simp)
    have hbE : b ∈ E := htE (by simp)
    have hcE : c ∈ E := htE (by simp)
    have hqa : q ≠ a := by rintro rfl; exact hqnE haE
    have hqb : q ≠ b := by rintro rfl; exact hqnE hbE
    have hqc : q ≠ c := by rintro rfl; exact hqnE hcE
    have haS : a ∈ S := hEsub haE
    have hbS : b ∈ S := hEsub hbE
    have hcS : c ∈ S := hEsub hcE
    rw [Finset.convexHull_eq, Set.mem_ofPred_eq] at htconv
    obtain ⟨w, hw0, hw1, hq⟩ := htconv
    have hsum : w a + w b + w c = 1 := by
      have h := hw1
      simp [hab, hbc, hac] at h
      linarith
    have hq' : q = ∑ y ∈ ({a, b, c} : Finset ℂ), w y • y := by
      rw [← hq]
      simp [Finset.centerMass, hw1]
    have hqabc : q = w a • a + w b • b + w c • c := by
      have h := hq'
      simp [hab, hbc, hac] at h
      rw [h]
      simp only [Complex.real_smul]
      ring
    have hwa0 : 0 ≤ w a := hw0 a (by simp)
    have hwb0 : 0 ≤ w b := hw0 b (by simp)
    have hwc0 : 0 ≤ w c := hw0 c (by simp)
    by_cases hzc : w c = 0
    · -- `q` lies on the segment `a b`
      have hqab : q = w a • a + w b • b := by rw [hqabc, hzc, zero_smul, add_zero]
      have hsum2 : w a + w b = 1 := by linarith
      have hpi : EuclideanGeometry.angle a q b = π :=
        angle_eq_pi_of_combination hab hwa0 hwb0 hsum2 hqab hqa hqb
      exact ⟨a, haS, b, hbS, hab, hqa.symm, hqb.symm, by linarith [Real.pi_pos]⟩
    by_cases hzb : w b = 0
    · -- `q` lies on the segment `a c`
      have hqac : q = w a • a + w c • c := by rw [hqabc, hzb, zero_smul, add_zero]
      have hsum2 : w a + w c = 1 := by linarith
      have hpi : EuclideanGeometry.angle a q c = π :=
        angle_eq_pi_of_combination hac hwa0 hwc0 hsum2 hqac hqa hqc
      exact ⟨a, haS, c, hcS, hac, hqa.symm, hqc.symm, by linarith [Real.pi_pos]⟩
    by_cases hza : w a = 0
    · -- `q` lies on the segment `b c`
      have hqbc : q = w b • b + w c • c := by rw [hqabc, hza, zero_smul, zero_add]
      have hsum2 : w b + w c = 1 := by linarith
      have hpi : EuclideanGeometry.angle b q c = π :=
        angle_eq_pi_of_combination hbc hwb0 hwc0 hsum2 hqbc hqb hqc
      exact ⟨b, hbS, c, hcS, hbc, hqb.symm, hqc.symm, by linarith [Real.pi_pos]⟩
    -- `q` lies strictly inside the triangle `a b c`
    have hα : 0 < w a := lt_of_le_of_ne hwa0 (fun h => hza h.symm)
    have hβ : 0 < w b := lt_of_le_of_ne hwb0 (fun h => hzb h.symm)
    have hγ : 0 < w c := lt_of_le_of_ne hwc0 (fun h => hzc h.symm)
    have hnc : ¬ Collinear ℝ ({a, b, c} : Set ℂ) :=
      hgen a haS b hbS c hcS hab hbc hac
    rcases exists_angle_ge_two_pi_div_three_of_interior_point hα hβ hγ hsum hqabc hnc with
      h | h | h
    · exact ⟨a, haS, b, hbS, hab, hqa.symm, hqb.symm, h⟩
    · exact ⟨b, hbS, c, hcS, hbc, hqb.symm, hqc.symm, h⟩
    · exact ⟨c, hcS, a, haS, hac.symm, hqc.symm, hqa.symm, h⟩

/-! ## The `n = 3` counting bound -/

set_option maxHeartbeats 1000000

/-- **Sendov's counting bound at `n = 3`.**  If every angle determined by a
finite set of points of the plane is strictly smaller than `2 * π / 3`, then the
set has at most `5` points.

This is the `n = 3` instance of the bound `S.card ≤ 2^(n-1) + 2^(n-3)` of
Sendov (1995); it improves the Erdős–Szekeres (1960) bound `2^3 - 2 = 6`
proved in `Erdos504.strictCountingBound`. -/
theorem sendov_counting_bound_n3 : ∀ S : Finset ℂ,
    (∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
      EuclideanGeometry.angle p q r < 2 * π / 3) → S.card ≤ 5 := by
  intro S hangle
  by_contra hcon
  rw [Nat.not_le] at hcon
  have hS6 : 6 ≤ S.card := by omega
  have hS3 : 3 ≤ S.card := by omega
  have hthresh : (1 - 1 / (3 : ℝ)) * π = 2 * π / 3 := by
    have h1 : (1 - 1 / (3 : ℝ)) = 2 / 3 := by norm_num
    rw [h1]
    ring
  have hangle' : ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
      EuclideanGeometry.angle p q r < (1 - 1 / (3 : ℝ)) * π :=
    fun p hp q hq r hr hpq hrq => (hangle p hp q hq r hr hpq hrq).trans_eq hthresh.symm
  have hgen : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c →
      ¬ Collinear ℝ ({a, b, c} : Set ℂ) := hgen_of_hangle_lt (hn := by norm_num) hangle'
  -- the hull of `S` has at most `2 * 3 - 1 = 5` vertices
  classical
  obtain ⟨w, hmem, hsur, hmono⟩ := exists_argSorted_enum hS3 hgen
  have hm3 : 3 ≤ (extremeFinset S).card := three_le_card_extremeFinset hS3 hgen
  obtain ⟨θ, A, hA0, hAπ, hAΘ, hwin, hsucc, hpred⟩ :=
    exists_hull_windows (hn := by norm_num) hangle' hgen w hmem hsur hmono hm3
  have hcard2 : 2 < S.card := by omega
  have ht : ∀ i, ∃ r t : ℝ, 0 < r ∧ 0 < t ∧ t < A i ∧
      szCentroid S - w i = (r : ℂ) * Complex.exp (((θ i + t : ℝ) : ℂ) * Complex.I) :=
    fun i => centroid_dir_in_window_strict (mem_of_mem_extremeFinset (hmem i))
      hcard2 hgen (hA0 i) (hAπ i) (hwin i)
  have hap : ∑ i : Fin (extremeFinset S).card, A i
      = ((extremeFinset S).card : ℝ) * π - 2 * π :=
    sum_window_apertures w hS3 hgen hmem hsur hmono hm3 hAπ hsucc hpred ht
  have hmle : (extremeFinset S).card ≤ 2 * 3 - 1 := hull_card_le (hn := by norm_num) hAΘ hap hm3
  have hlt : (extremeFinset S).card < S.card := by omega
  -- hence there is a point of `S` which is not a vertex of the convex hull
  obtain ⟨q, hqS, hqne⟩ := exists_not_extreme_of_card_lt hlt
  obtain ⟨a, haS, b, hbS, hab, hqa, hqb, hang⟩ :=
    exists_angle_ge_two_pi_div_three_of_interior hgen hqS hqne
  -- contradiction: the angle at `q` is at least `2 * π / 3`
  have hlt' := hangle a haS q hqS b hbS hqa hqb
  linarith

/-! ## Axiom audit -/

#print axioms convexHull_eq_convexHull_extremePoints
#print axioms angle_eq_pi_of_combination
#print axioms exists_angle_ge_two_pi_div_three_of_interior_point
#print axioms exists_angle_ge_two_pi_div_three_of_interior
#print axioms sendov_counting_bound_n3

end Erdos504
