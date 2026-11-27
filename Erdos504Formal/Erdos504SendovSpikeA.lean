/-
The gap in Sendov's Lemma 4.1 (the asserted s = 4 maxima) was first publicly
reported by NoahPuckett-IO in teorth/erdosproblems#494 (2026-10-26,
https://github.com/teorth/erdosproblems/issues/494), and this development
independently supplies exact-coordinate counterexamples, Lean machine checks,
and a refutation of the published proof along the Lemma 4.1 to Lemma 4.2 to
Theorem 4.1 chain.
-/

import Erdos504Formal.Erdos504SendovStage1

open scoped BigOperators

namespace Erdos504.SendovStage1

noncomputable def gapCapacity (x : ℝ) : ℕ := (Int.floor x - 1).toNat

lemma gapCapacity_zero {x : ℝ} (hx : x < 2) : gapCapacity x = 0 := by
  have h : Int.floor x < 2 := (Int.floor_lt).2 (by exact_mod_cast hx)
  unfold gapCapacity
  omega

lemma capacity_add_one_le {x : ℝ} (hx : 0 < gapCapacity x) :
    (gapCapacity x : ℝ) + 1 ≤ x := by
  have h : (gapCapacity x : ℤ) + 1 = Int.floor x := by
    unfold gapCapacity at *
    omega
  calc
    (gapCapacity x : ℝ) + 1 = (Int.floor x : ℝ) := by exact_mod_cast h
    _ ≤ x := Int.floor_le _

lemma gapCapacity_merge (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    gapCapacity x + gapCapacity y ≤ gapCapacity (x + y) ∧
      gapCapacity (x + y) ≤ gapCapacity x + gapCapacity y + 2 := by
  have h₁ := Int.le_floor_add x y
  have h₂ := Int.le_floor_add_floor x y
  have h₃ : 0 ≤ Int.floor x := (Int.floor_nonneg).2 hx
  have h₄ : 0 ≤ Int.floor y := (Int.floor_nonneg).2 hy
  unfold gapCapacity
  omega

lemma rowCapacity_le_and_high {ι : Type*} [Fintype ι] (x : ι → ℝ) (m : ℕ)
    (hm : 2 ≤ m) (hx : ∀ i, 0 ≤ x i) (ht : (∑ i, x i) < (m : ℝ) + 1) :
    (∑ i, gapCapacity (x i)) ≤ m - 1 ∧
      ((∑ i, gapCapacity (x i)) = m - 1 → ∃ i, (m : ℝ) ≤ x i) := by
  classical
  let active := Finset.univ.filter (fun i : ι => 0 < gapCapacity (x i))
  have hs : (∑ i, gapCapacity (x i)) = ∑ i ∈ active, gapCapacity (x i) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ active)
    intro i _ hi
    have hn : ¬ 0 < gapCapacity (x i) := by simpa [active] using hi
    omega
  have hsum : (((∑ i, gapCapacity (x i)) : ℕ) : ℝ) + active.card ≤ ∑ i, x i := by
    rw [hs, Nat.cast_sum]
    calc
      (∑ i ∈ active, (gapCapacity (x i) : ℝ)) + (active.card : ℝ) =
          ∑ i ∈ active, ((gapCapacity (x i) : ℝ) + 1) := by
        rw [Finset.sum_add_distrib]
        simp
      _ ≤ ∑ i ∈ active, x i := by
        apply Finset.sum_le_sum
        intro i hi
        exact capacity_add_one_le ((Finset.mem_filter.mp hi).2)
      _ ≤ ∑ i, x i := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ active) (fun i _ _ => hx i)
  have hinteger : (∑ i, gapCapacity (x i)) + active.card ≤ m := by
    have hlt : (((∑ i, gapCapacity (x i)) + active.card : ℕ) : ℝ) <
        ((m + 1 : ℕ) : ℝ) := by rw [Nat.cast_add, Nat.cast_add, Nat.cast_one]; linarith
    exact Nat.le_of_lt_succ (by exact_mod_cast hlt)
  refine ⟨?_, ?_⟩
  · by_cases ha : active.Nonempty
    · have := Finset.card_pos.mpr ha
      omega
    · rw [Finset.not_nonempty_iff_eq_empty.mp ha, Finset.sum_empty] at hs
      omega
  · intro heq
    have ha : active.Nonempty := by
      by_contra hn
      rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.sum_empty] at hs
      omega
    have hcard : active.card = 1 := by
      have := Finset.card_pos.mpr ha
      omega
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
    have hk : gapCapacity (x i) = m - 1 := by simpa [hi] using hs.symm.trans heq
    have hpos : 0 < gapCapacity (x i) := by omega
    refine ⟨i, ?_⟩
    have hc := capacity_add_one_le hpos
    have hn : gapCapacity (x i) + 1 = m := by omega
    rw [← Nat.cast_one, ← Nat.cast_add, hn] at hc
    exact hc

private lemma sum_fin_differences (d : ℕ) (row : Fin (d + 1) → ℝ) :
    (∑ j : Fin d, (row j.succ - row j.castSucc)) = row (Fin.last d) - row 0 := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Fin.sum_univ_castSucc]
    have h := ih (fun i => row i.castSucc)
    change (∑ j : Fin d, (row j.succ.castSucc - row j.castSucc.castSucc)) =
      row (Fin.last d).castSucc - row (0 : Fin (d + 1)).castSucc at h
    have hc (j : Fin d) : j.castSucc.succ = j.succ.castSucc := Fin.ext rfl
    simp_rw [hc]
    rw [h]
    change row (Fin.last d).castSucc - row 0 +
      (row (Fin.last (d + 1)) - row (Fin.last d).castSucc) =
        row (Fin.last (d + 1)) - row 0
    ring

lemma sum_cyclicGap (d : ℕ) (row : Fin (d + 1) → ℝ) :
    ∑ j : Fin (d + 1), cyclicGap row j = 1 := by
  rw [Fin.sum_univ_castSucc]
  have h : (∑ j : Fin d, cyclicGap row j.castSucc) =
      ∑ j : Fin d, (row j.succ - row j.castSucc) := by
    apply Finset.sum_congr rfl
    intro j _
    have hj : j.castSucc.val + 1 < d + 1 := Nat.succ_lt_succ j.isLt
    rw [cyclicGap, dif_pos hj]
    rfl
  rw [h, sum_fin_differences, cyclicGap, dif_neg (by simp)]
  simp

lemma projectiveDir_mem (z : ℂ) : 0 ≤ projectiveDir z ∧ projectiveDir z < 1 := by
  exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

private lemma dir_mem {s : ℕ} (D : CenterGapData s) (i : Fin s) (j : Fin (s - 1)) :
    0 ≤ D.dir i j ∧ D.dir i j < 1 := D.dir_spec i j ▸ projectiveDir_mem _

private lemma cyclicGap_nonneg {d : ℕ} {row : Fin d → ℝ}
    (hmono : StrictMono row) (hrow : ∀ j, 0 ≤ row j ∧ row j < 1)
    (j : Fin d) : 0 ≤ cyclicGap row j := by
  unfold cyclicGap
  split
  · apply sub_nonneg.mpr
    apply hmono.monotone
    change j.val ≤ j.val + 1
    omega
  · have := (hrow j).2
    have := (hrow ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt⟩).1
    linarith

lemma gapExponent_le_and_high {s m : ℕ} (D : CenterGapData s) (i : Fin s) (t : ℝ)
    (hs : 2 ≤ s) (hm : 2 ≤ m) (ht : (m : ℝ) ≤ t) (ht' : t < (m : ℝ) + 1) :
    gapExponent D t i ≤ m - 1 ∧
      (gapExponent D t i = m - 1 →
        ∃ j, (m : ℝ) ≤ t * cyclicGap (D.dir i) j) := by
  have ht0 : 0 ≤ t := le_trans (Nat.cast_nonneg _) ht
  have hsum : ∑ j : Fin (s - 1), cyclicGap (D.dir i) j = 1 := by
    have he : s - 1 = (s - 2) + 1 := by omega
    generalize D.dir i = row
    revert row
    rw [he]
    exact sum_cyclicGap (s - 2)
  exact rowCapacity_le_and_high _ m hm
    (fun j => mul_nonneg ht0 (cyclicGap_nonneg (D.dir_strictMono i) (dir_mem D i) j))
    (by rw [← Finset.mul_sum, hsum, mul_one]; exact ht')

private lemma cos_angle_eq_cos_arg_sub {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0) :
    Real.cos (InnerProductGeometry.angle u v) =
      Real.cos (Complex.arg v - Complex.arg u) := by
  rw [Erdos504.angle_eq_abs_arg hu hv, Real.cos_abs]
  have hcu : (starRingEnd ℂ) u ≠ 0 := by simpa using hu
  have hangle : (Complex.arg ((starRingEnd ℂ) u * v) : Real.Angle) =
      ((Complex.arg v - Complex.arg u : ℝ) : Real.Angle) := by
    rw [Complex.arg_mul_coe_angle hcu hv, Complex.arg_conj_coe_angle, Real.Angle.coe_sub]
    abel
  simpa only [Real.Angle.cos_coe] using congrArg Real.Angle.cos hangle

lemma angle_eq_abs_arg_sub {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0)
    (h : |Complex.arg v - Complex.arg u| ≤ Real.pi) :
    InnerProductGeometry.angle u v = |Complex.arg v - Complex.arg u| := by
  apply Real.strictAntiOn_cos.injOn
    ⟨InnerProductGeometry.angle_nonneg _ _, InnerProductGeometry.angle_le_pi _ _⟩
    ⟨abs_nonneg _, h⟩
  rw [Real.cos_abs, cos_angle_eq_cos_arg_sub hu hv]

private lemma angle_one_eq_abs_arg {u : ℂ} (hu : u ≠ 0) :
    InnerProductGeometry.angle 1 u = |Complex.arg u| := by
  rw [Erdos504.angle_eq_abs_arg one_ne_zero hu]
  simp

lemma angle_eq_projective_or_supplement {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0) :
    InnerProductGeometry.angle u v = |projectiveDir v - projectiveDir u| * Real.pi ∨
      InnerProductGeometry.angle u v = (1 - |projectiveDir v - projectiveDir u|) * Real.pi := by
  let a := |projectiveDir v - projectiveDir u| * Real.pi
  let k := Int.floor (Complex.arg v / Real.pi) - Int.floor (Complex.arg u / Real.pi)
  have harg : Complex.arg v - Complex.arg u =
      (projectiveDir v - projectiveDir u) * Real.pi + (k : ℝ) * Real.pi := by
    unfold projectiveDir k
    push_cast
    field_simp [Real.pi_ne_zero]
    ring
  have habs : |Real.cos (InnerProductGeometry.angle u v)| = |Real.cos a| := by
    rw [cos_angle_eq_cos_arg_sub hu hv, harg, Real.cos_add_int_mul_pi, abs_mul, abs_zpow]
    simp only [abs_neg, abs_one, one_zpow, one_mul]
    have h := abs_mul (projectiveDir v - projectiveDir u) Real.pi
    rw [abs_of_pos Real.pi_pos] at h
    dsimp [a]
    rw [← h, Real.cos_abs]
  have hap : 0 ≤ a ∧ a ≤ Real.pi := by
    have hl := projectiveDir_mem u
    have hr := projectiveDir_mem v
    have hd : |projectiveDir v - projectiveDir u| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    exact ⟨mul_nonneg (abs_nonneg _) Real.pi_pos.le,
      by simpa using mul_le_mul_of_nonneg_right hd Real.pi_pos.le⟩
  have hθ : InnerProductGeometry.angle u v ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨InnerProductGeometry.angle_nonneg _ _, InnerProductGeometry.angle_le_pi _ _⟩
  rcases (abs_eq_abs.mp habs) with he | he
  · left
    exact Real.strictAntiOn_cos.injOn hθ hap he
  · right
    have hc : Real.cos (InnerProductGeometry.angle u v) = Real.cos (Real.pi - a) := by
      rwa [Real.cos_pi_sub]
    have hp : Real.pi - a ∈ Set.Icc (0 : ℝ) Real.pi := ⟨by linarith [hap.2], by linarith [hap.1]⟩
    calc
      InnerProductGeometry.angle u v = Real.pi - a := Real.strictAntiOn_cos.injOn hθ hp hc
      _ = _ := by dsimp [a]; ring

private lemma differences_outside_gap {d : ℕ} {row : Fin d → ℝ}
    (hm : StrictMono row) (hrow : ∀ j, 0 ≤ row j ∧ row j < 1) (g j k : Fin d) :
    |row k - row j| ≤ 1 - cyclicGap row g ∨
      cyclicGap row g ≤ |row k - row j| := by
  wlog hjk : j ≤ k generalizing j k
  · simpa only [abs_sub_comm (row k) (row j)] using this k j (le_of_not_ge hjk)
  rw [abs_of_nonneg (sub_nonneg.mpr (hm.monotone hjk))]
  unfold cyclicGap
  split
  · rename_i hg
    let g' : Fin d := ⟨g.val + 1, hg⟩
    change row k - row j ≤ 1 - (row g' - row g) ∨ row g' - row g ≤ row k - row j
    by_cases hk : k ≤ g
    · left
      have := hm.monotone hk
      linarith [(hrow j).1, (hrow g').2]
    by_cases hj : g' ≤ j
    · left
      have := hm.monotone hj
      linarith [(hrow k).2, (hrow g).1]
    · have hleft : j ≤ g := by
        change j.val ≤ g.val
        change ¬ g.val + 1 ≤ j.val at hj
        omega
      have hright : g' ≤ k := by
        change g.val + 1 ≤ k.val
        change ¬ k.val ≤ g.val at hk
        omega
      right
      linarith [hm.monotone hleft, hm.monotone hright]
  · rename_i hg
    have hk : k ≤ g := by
      change k.val ≤ g.val
      omega
    left
    have hmin : (⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) g.isLt⟩ : Fin d) ≤ j := by
      change 0 ≤ j.val
      exact Nat.zero_le _
    linarith [hm.monotone hk, hm.monotone hmin]

lemma high_center_angle_le {s m : ℕ} (D : CenterGapData s) (i : Fin s) (t : ℝ)
    (hs : 2 ≤ s) (hm : 2 ≤ m) (ht : (m : ℝ) ≤ t) (ht' : t < (m : ℝ) + 1)
    (hcap : CenterAngleCap D t) (hhigh : gapExponent D t i = m - 1)
    (j k : Fin s) (hj : j ≠ i) (hk : k ≠ i) :
    EuclideanGeometry.angle (D.center j) (D.center i) (D.center k) ≤
      (t - (m : ℝ)) * (Real.pi / t) := by
  let j' := (D.other i).symm ⟨j, hj⟩
  let k' := (D.other i).symm ⟨k, hk⟩
  have hdj : D.dir i j' = projectiveDir (D.center j - D.center i) := by simp [D.dir_spec, j']
  have hdk : D.dir i k' = projectiveDir (D.center k - D.center i) := by simp [D.dir_spec, k']
  have ht0 : 0 < t := lt_of_lt_of_le (by exact_mod_cast (show 0 < m by omega)) ht
  obtain ⟨g, hg⟩ := (gapExponent_le_and_high D i t hs hm ht ht').2 hhigh
  have harc := differences_outside_gap (D.dir_strictMono i) (dir_mem D i) g j' k'
  have hsmall : 1 - cyclicGap (D.dir i) g ≤ (t - (m : ℝ)) / t := by
    apply (le_div_iff₀ ht0).2
    linarith
  have hbig : (t - (m : ℝ)) / t < 1 / t := (div_lt_div_iff_of_pos_right ht0).2 (by linarith)
  have hlimit := hcap j i k hj hk
  unfold angleAt at hlimit
  have hang := angle_eq_projective_or_supplement
    (sub_ne_zero.mpr (D.injective.ne hj)) (sub_ne_zero.mpr (D.injective.ne hk))
  change (InnerProductGeometry.angle (D.center j - D.center i) (D.center k - D.center i)) ≤ _
  change (InnerProductGeometry.angle (D.center j - D.center i) (D.center k - D.center i)) ≤ _ at hlimit
  rw [← hdj, ← hdk] at hang
  have hfactor : (t - (m : ℝ)) * (Real.pi / t) =
      ((t - (m : ℝ)) / t) * Real.pi := by ring
  rw [hfactor]
  rcases harc with h | h <;> rcases hang with ha | ha <;> rw [ha] at hlimit ⊢
  · exact mul_le_mul_of_nonneg_right (h.trans hsmall) Real.pi_pos.le
  · have habs : |D.dir i k' - D.dir i j'| < 1 / t := (h.trans hsmall).trans_lt hbig
    exact False.elim ((not_lt_of_ge hlimit) (mul_lt_mul_of_pos_right (by linarith) Real.pi_pos))
  · have habs : 1 - 1 / t < |D.dir i k' - D.dir i j'| := by linarith
    exact False.elim ((not_lt_of_ge hlimit) (mul_lt_mul_of_pos_right habs Real.pi_pos))
  · exact mul_le_mul_of_nonneg_right (by linarith) Real.pi_pos.le

noncomputable def highCenters {s : ℕ} (D : CenterGapData s) (t : ℝ) (m : ℕ) :
    Finset (Fin s) := Finset.univ.filter (fun i => gapExponent D t i = m - 1)

private lemma mem_highCenters {s m : ℕ} {D : CenterGapData s} {t : ℝ} {i : Fin s} :
    i ∈ highCenters D t m ↔ gapExponent D t i = m - 1 := by
  simp [highCenters]

private lemma center_angles_sum {s : ℕ} (D : CenterGapData s) (a b c : Fin s) (hab : a ≠ b) :
    EuclideanGeometry.angle (D.center b) (D.center a) (D.center c) +
      EuclideanGeometry.angle (D.center a) (D.center b) (D.center c) +
      EuclideanGeometry.angle (D.center a) (D.center c) (D.center b) = Real.pi := by
  have h := EuclideanGeometry.angle_add_angle_add_angle_eq_pi (D.center c)
    (D.injective.ne hab.symm)
  rw [EuclideanGeometry.angle_comm (D.center b) (D.center c) (D.center a),
    EuclideanGeometry.angle_comm (D.center c) (D.center a) (D.center b)] at h
  linarith

lemma highCenters_card_le_one {s m : ℕ} (D : CenterGapData s) (t : ℝ)
    (hs : 3 ≤ s) (hm : 2 ≤ m) (ht : (m : ℝ) ≤ t) (ht' : t < (m : ℝ) + 1 / 2)
    (hcap : CenterAngleCap D t) : (highCenters D t m).card ≤ 1 := by
  classical
  by_contra! h
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h
  have ht0 : 0 < t := lt_of_lt_of_le (by exact_mod_cast (show 0 < m by omega)) ht
  have hlt : ({a,b} : Finset (Fin s)).card < (Finset.univ : Finset (Fin s)).card := by
    simp [hab]
    omega
  obtain ⟨c, _, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hca : c ≠ a := by intro he; exact hc (by simp [he])
  have hcb : c ≠ b := by intro he; exact hc (by simp [he])
  have hA := high_center_angle_le D a t (by omega) hm ht (by linarith) hcap
    (mem_highCenters.mp ha) b c hab.symm hca
  have hB := high_center_angle_le D b t (by omega) hm ht (by linarith) hcap
    (mem_highCenters.mp hb) a c hab hcb
  have hC := hcap a c b hca.symm hcb.symm
  have hsum := center_angles_sum D a b c hab
  unfold angleAt at hC
  have hscale : 0 < Real.pi / t := div_pos Real.pi_pos ht0
  have he : (1 - 1/t) * Real.pi = Real.pi - Real.pi / t := by ring
  rw [he] at hC
  have hsmall : (2 * (t - (m : ℝ))) * (Real.pi / t) < Real.pi / t := by
    simpa using mul_lt_mul_of_pos_right (show 2 * (t - (m : ℝ)) < 1 by linarith) hscale
  linarith

lemma highCenters_card_le_two {s m : ℕ} (D : CenterGapData s) (t : ℝ)
    (hs : 2 ≤ s) (hm : 2 ≤ m) (ht : (m : ℝ) ≤ t) (ht' : t < (m : ℝ) + 1)
    (hcap : CenterAngleCap D t) : (highCenters D t m).card ≤ 2 := by
  classical
  by_contra! h
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (highCenters D t m).card)
  have hlt : ({a,b} : Finset (Fin s)).card < (highCenters D t m).card := by
    simp [hab]
    omega
  obtain ⟨c, hc, hnc⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hca : c ≠ a := by intro he; exact hnc (by simp [he])
  have hcb : c ≠ b := by intro he; exact hnc (by simp [he])
  have hA := high_center_angle_le D a t hs hm ht ht' hcap
    (mem_highCenters.mp ha) b c hab.symm hca
  have hB := high_center_angle_le D b t hs hm ht ht' hcap
    (mem_highCenters.mp hb) a c hab hcb
  have hC := high_center_angle_le D c t hs hm ht ht' hcap
    (mem_highCenters.mp hc) a b hca.symm hcb.symm
  have hsum := center_angles_sum D a b c hab
  have ht0 : 0 < t := lt_of_lt_of_le (by exact_mod_cast (show 0 < m by omega)) ht
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hscale : 0 < Real.pi / t := div_pos Real.pi_pos ht0
  have hsmall : (3 * (t - (m : ℝ))) * (Real.pi / t) < Real.pi := calc
    _ < t * (Real.pi / t) := mul_lt_mul_of_pos_right (by linarith) hscale
    _ = Real.pi := by field_simp
  linarith

/-- Normalize the ordered anchors to \(0,1\) by an oriented similarity. -/
noncomputable def anchorCoord {s : ℕ} (D : CenterGapData s) (a b : Fin s) (i : Fin s) : ℂ :=
  (D.center b - D.center a)⁻¹ * (D.center i - D.center a)

@[simp] lemma anchorCoord_left {s : ℕ} (D : CenterGapData s) (a b : Fin s) :
    anchorCoord D a b a = 0 := by simp [anchorCoord]

@[simp] lemma anchorCoord_right {s : ℕ} (D : CenterGapData s) {a b : Fin s} (h : a ≠ b) :
    anchorCoord D a b b = 1 := by
  simp [anchorCoord, sub_ne_zero.mpr (D.injective.ne h.symm)]

lemma anchorCoord_injective {s : ℕ} (D : CenterGapData s) {a b : Fin s} (h : a ≠ b) :
    Function.Injective (anchorCoord D a b) := by
  intro i j hij
  apply D.injective
  have hscale : (D.center b - D.center a)⁻¹ ≠ 0 :=
    inv_ne_zero (sub_ne_zero.mpr (D.injective.ne h.symm))
  unfold anchorCoord at hij
  have he := mul_left_cancel₀ hscale hij
  simpa only [sub_add_cancel] using congrArg (fun z : ℂ => z + D.center a) he

lemma angle_anchorCoord {s : ℕ} (D : CenterGapData s) {a b : Fin s} (h : a ≠ b)
    (p q r : Fin s) :
    EuclideanGeometry.angle (anchorCoord D a b p) (anchorCoord D a b q) (anchorCoord D a b r) =
      EuclideanGeometry.angle (D.center p) (D.center q) (D.center r) := by
  let z : ℂ := (D.center b - D.center a)⁻¹
  have hz : z ≠ 0 := inv_ne_zero (sub_ne_zero.mpr (D.injective.ne h.symm))
  change EuclideanGeometry.angle (z * (D.center p - D.center a))
    (z * (D.center q - D.center a)) (z * (D.center r - D.center a)) = _
  rw [Erdos504.euclidean_angle_const_mul hz (D.center p - D.center a)
    (D.center q - D.center a) (D.center r - D.center a)]
  simpa only [sub_eq_add_neg] using
    Erdos504.euclidean_angle_add_const (-D.center a) (D.center p) (D.center q) (D.center r)

structure TwoHighFrame {s : ℕ} (D : CenterGapData s) (t : ℝ) (m : ℕ)
    (a b : Fin s) : Prop where
  size : 2 ≤ s
  distinct : a ≠ b
  floor_ge_two : 2 ≤ m
  floor_le : (m : ℝ) ≤ t
  lt_floor_add_one : t < (m : ℝ) + 1
  cap : CenterAngleCap D t
  leftHigh : gapExponent D t a = m - 1
  rightHigh : gapExponent D t b = m - 1

namespace TwoHighFrame

variable {s m : ℕ} {D : CenterGapData s} {t : ℝ} {a b : Fin s}
local notation "coord" => anchorCoord D a b
local notation "clearance" => Real.pi / t
local notation "fan" => (t - (m : ℝ)) * (Real.pi / t)

private lemma t_ge_two (F : TwoHighFrame D t m a b) : (2 : ℝ) ≤ t :=
  (by exact_mod_cast F.floor_ge_two : (2 : ℝ) ≤ (m : ℝ)).trans F.floor_le

private lemma clearance_pos (F : TwoHighFrame D t m a b) : 0 < clearance :=
  div_pos Real.pi_pos (by linarith [F.t_ge_two])

private lemma clearance_le_half_pi (F : TwoHighFrame D t m a b) : clearance ≤ Real.pi / 2 := by
  exact div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) F.t_ge_two

private lemma fan_lt_clearance (F : TwoHighFrame D t m a b) : fan < clearance := by
  have h : t - (m : ℝ) < 1 := by linarith [F.lt_floor_add_one]
  simpa only [one_mul] using mul_lt_mul_of_pos_right h F.clearance_pos

private lemma coord_ne_zero (F : TwoHighFrame D t m a b) {p : Fin s} (hp : p ≠ a) : coord p ≠ 0 := by
  simpa only [anchorCoord_left] using (anchorCoord_injective D F.distinct).ne hp

private lemma one_sub_coord_ne_zero (F : TwoHighFrame D t m a b) {p : Fin s} (hp : p ≠ b) :
    1 - coord p ≠ 0 := by
  have hne := (anchorCoord_injective D F.distinct).ne hp.symm
  rw [anchorCoord_right D F.distinct] at hne
  exact sub_ne_zero.mpr hne

private lemma angle_cap_coord (F : TwoHighFrame D t m a b) {p q r : Fin s}
    (hp : p ≠ q) (hr : r ≠ q) :
    InnerProductGeometry.angle (coord p - coord q) (coord r - coord q) ≤ Real.pi - clearance := by
  change EuclideanGeometry.angle (coord p) (coord q) (coord r) ≤ _
  rw [angle_anchorCoord D F.distinct]
  have h := F.cap p q r hp hr
  unfold angleAt at h
  convert h using 1
  ring

lemma abs_anchor_args_le (F : TwoHighFrame D t m a b) {p : Fin s}
    (ha : p ≠ a) (hb : p ≠ b) :
    |Complex.arg (coord p)| ≤ fan ∧ |Complex.arg (1 - coord p)| ≤ fan := by
  have hl := high_center_angle_le D a t F.size F.floor_ge_two F.floor_le F.lt_floor_add_one
    F.cap F.leftHigh b p F.distinct.symm ha
  have hr := high_center_angle_le D b t F.size F.floor_ge_two F.floor_le F.lt_floor_add_one
    F.cap F.rightHigh a p F.distinct hb
  rw [← angle_anchorCoord D F.distinct b a p] at hl
  rw [← angle_anchorCoord D F.distinct a b p] at hr
  change InnerProductGeometry.angle (coord b - coord a) (coord p - coord a) ≤ _ at hl
  change InnerProductGeometry.angle (coord a - coord b) (coord p - coord b) ≤ _ at hr
  simp only [anchorCoord_left, anchorCoord_right D F.distinct, sub_zero,
    angle_one_eq_abs_arg (F.coord_ne_zero ha)] at hl
  simp only [anchorCoord_left, anchorCoord_right D F.distinct, zero_sub] at hr
  rw [← neg_sub, InnerProductGeometry.angle_neg_neg,
    angle_one_eq_abs_arg (F.one_sub_coord_ne_zero hb)] at hr
  exact ⟨hl, hr⟩

private lemma abs_sub_le_pi_of_halves {x y : ℝ}
    (hx : |x| ≤ Real.pi / 2) (hy : |y| ≤ Real.pi / 2) :
    |x - y| ≤ Real.pi := by
  have hx' := abs_le.mp hx
  have hy' := abs_le.mp hy
  exact abs_le.mpr ⟨by linarith [hx'.1, hy'.2], by linarith [hx'.2, hy'.1]⟩

private lemma small_anchor_args (F : TwoHighFrame D t m a b) {p : Fin s}
    (ha : p ≠ a) (hb : p ≠ b) :
    |Complex.arg (coord p)| < Real.pi / 2 ∧ |Complex.arg (1 - coord p)| < Real.pi / 2 := by
  have h := F.fan_lt_clearance.trans_le F.clearance_le_half_pi
  exact ⟨(F.abs_anchor_args_le ha hb).1.trans_lt h, (F.abs_anchor_args_le ha hb).2.trans_lt h⟩

lemma anchor_separation (F : TwoHighFrame D t m a b) {p : Fin s} (ha : p ≠ a) (hb : p ≠ b) :
    clearance ≤ |Complex.arg (coord p) - Complex.arg (1 - coord p)| := by
  have h := F.angle_cap_coord (p := a) (q := p) (r := b) ha.symm hb.symm
  simp only [anchorCoord_left, anchorCoord_right D F.distinct, zero_sub] at h
  have hs := F.small_anchor_args ha hb
  rw [InnerProductGeometry.angle_neg_left,
    angle_eq_abs_arg_sub (F.coord_ne_zero ha) (F.one_sub_coord_ne_zero hb)
      (abs_sub_le_pi_of_halves hs.2.le hs.1.le), abs_sub_comm] at h
  linarith

lemma residual_im_ne_zero (F : TwoHighFrame D t m a b) {p : Fin s}
    (ha : p ≠ a) (hb : p ≠ b) : (coord p).im ≠ 0 := by
  intro hz
  have hs := F.small_anchor_args ha hb
  have hl := ((Complex.abs_arg_lt_pi_div_two_iff).mp hs.1).resolve_right (F.coord_ne_zero ha)
  have hr := ((Complex.abs_arg_lt_pi_div_two_iff).mp hs.2).resolve_right (F.one_sub_coord_ne_zero hb)
  have hzero := Complex.arg_eq_zero_iff.mpr ⟨hl.le, hz⟩
  have hzero' := Complex.arg_eq_zero_iff.mpr ⟨hr.le, by simp [hz]⟩
  have h := F.anchor_separation ha hb
  rw [hzero, hzero', sub_self, abs_zero] at h
  exact F.clearance_pos.not_ge h

private lemma arg_differences_le_fan (F : TwoHighFrame D t m a b) {p q : Fin s}
    (hpa : p ≠ a) (hpb : p ≠ b) (hqa : q ≠ a) (hqb : q ≠ b) :
    |Complex.arg (coord q) - Complex.arg (coord p)| ≤ fan ∧
      |Complex.arg (1 - coord q) - Complex.arg (1 - coord p)| ≤ fan := by
  have hA := high_center_angle_le D a t F.size F.floor_ge_two F.floor_le F.lt_floor_add_one
    F.cap F.leftHigh p q hpa hqa
  have hB := high_center_angle_le D b t F.size F.floor_ge_two F.floor_le F.lt_floor_add_one
    F.cap F.rightHigh p q hpb hqb
  rw [← angle_anchorCoord D F.distinct p a q] at hA
  rw [← angle_anchorCoord D F.distinct p b q] at hB
  change InnerProductGeometry.angle (coord p - coord a) (coord q - coord a) ≤ _ at hA
  change InnerProductGeometry.angle (coord p - coord b) (coord q - coord b) ≤ _ at hB
  have hs := F.small_anchor_args hpa hpb
  have hs' := F.small_anchor_args hqa hqb
  simp only [anchorCoord_left, sub_zero] at hA
  simp only [anchorCoord_right D F.distinct] at hB
  rw [angle_eq_abs_arg_sub (F.coord_ne_zero hpa) (F.coord_ne_zero hqa)
    (abs_sub_le_pi_of_halves hs'.1.le hs.1.le)] at hA
  rw [← neg_sub (1 : ℂ) (coord p), ← neg_sub (1 : ℂ) (coord q),
    InnerProductGeometry.angle_neg_neg,
    angle_eq_abs_arg_sub (F.one_sub_coord_ne_zero hpb) (F.one_sub_coord_ne_zero hqb)
      (abs_sub_le_pi_of_halves hs'.2.le hs.2.le)] at hB
  exact ⟨hA, hB⟩

private lemma not_opposite (F : TwoHighFrame D t m a b) {p q : Fin s}
    (hpa : p ≠ a) (hpb : p ≠ b) (hqa : q ≠ a) (hqb : q ≠ b)
    (hp : 0 < (coord p).im) (hq : (coord q).im < 0) : False := by
  have hap := Complex.arg_nonneg_iff.mpr hp.le
  have hbq : 0 ≤ Complex.arg (1 - coord q) :=
    Complex.arg_nonneg_iff.mpr (by simpa using hq.le)
  have haq := (Complex.arg_neg_iff.mpr hq).le
  have hbp : Complex.arg (1 - coord p) ≤ 0 :=
    (Complex.arg_neg_iff.mpr (by simpa using hp)).le
  obtain ⟨hA, hB⟩ := F.arg_differences_le_fan hpa hpb hqa hqb
  have hP := F.anchor_separation hpa hpb
  have hQ := F.anchor_separation hqa hqb
  rw [abs_of_nonpos (by linarith)] at hA
  rw [abs_of_nonneg (by linarith)] at hB
  rw [abs_of_nonneg (by linarith)] at hP
  rw [abs_of_nonpos (by linarith)] at hQ
  linarith [F.fan_lt_clearance]

/-- All residual centers are on one open side of the anchor line. -/
lemma residual_same_side (F : TwoHighFrame D t m a b) {p q : Fin s}
    (hpa : p ≠ a) (hpb : p ≠ b) (hqa : q ≠ a) (hqb : q ≠ b) :
    (0 < (coord p).im ∧ 0 < (coord q).im) ∨
      ((coord p).im < 0 ∧ (coord q).im < 0) := by
  rcases lt_or_gt_of_ne (F.residual_im_ne_zero hpa hpb) with hp | hp <;>
    rcases lt_or_gt_of_ne (F.residual_im_ne_zero hqa hqb) with hq | hq
  · exact Or.inr ⟨hp, hq⟩
  · exact (F.not_opposite hqa hqb hpa hpb hq hp).elim
  · exact (F.not_opposite hpa hpb hqa hqb hp hq).elim
  · exact Or.inl ⟨hp, hq⟩

/-- The signed form has \(b_D=-\arg(1-D)\) for centers above the anchor line. -/
lemma right_line_clearances (F : TwoHighFrame D t m a b) {p q : Fin s}
    (hpa : p ≠ a) (hpb : p ≠ b) (hqa : q ≠ a) (hqb : q ≠ b)
    (hpq : p ≠ q) (hre : (coord p).re ≤ (coord q).re) :
    let theta := Complex.arg (coord q - coord p)
    clearance ≤ |theta - Complex.arg (coord p)| ∧
      clearance ≤ |theta - Complex.arg (1 - coord q)| := by
  have hcapA := F.angle_cap_coord (p := a) (q := p) (r := q) hpa.symm hpq.symm
  have hcapB := F.angle_cap_coord (p := b) (q := q) (r := p) hqb.symm hpq
  have hne := sub_ne_zero.mpr ((anchorCoord_injective D F.distinct).ne hpq.symm)
  have hs : |Complex.arg (coord q - coord p)| ≤ Real.pi / 2 :=
    Complex.abs_arg_le_pi_div_two_iff.mpr (by simpa using sub_nonneg.mpr hre)
  have hl := (F.small_anchor_args hpa hpb).1
  have hr := (F.small_anchor_args hqa hqb).2
  simp only [anchorCoord_left, zero_sub] at hcapA
  simp only [anchorCoord_right D F.distinct] at hcapB
  rw [InnerProductGeometry.angle_neg_left,
    angle_eq_abs_arg_sub (F.coord_ne_zero hpa) hne (abs_sub_le_pi_of_halves hs hl.le)] at hcapA
  rw [← neg_sub (coord q) (coord p), InnerProductGeometry.angle_neg_right,
    angle_eq_abs_arg_sub (F.one_sub_coord_ne_zero hqb) hne
      (abs_sub_le_pi_of_halves hs hr.le)] at hcapB
  exact ⟨by linarith, by linarith⟩

private lemma sub_ge_of_clearance {theta x c : ℝ} (hθ : 0 ≤ theta)
    (hxc : x < c) (hc : c ≤ |theta - x|) : c ≤ theta - x := by
  by_cases h : 0 ≤ theta - x
  · rw [abs_of_nonneg h] at hc
    linarith
  · rw [abs_of_neg (lt_of_not_ge h)] at hc
    linarith

private lemma abs_le_of_two_clearances {theta x y c : ℝ}
    (hx : |x| < c) (hy : |y| < c) (h₁ : c ≤ |theta - x|) (h₂ : c ≤ |theta - y|)
    (hs : (0 ≤ x ∧ y ≤ 0) ∨ (x ≤ 0 ∧ 0 ≤ y)) : c ≤ |theta| := by
  have posCase {theta x y : ℝ} (hθ : 0 ≤ theta)
      (hx : |x| < c) (hy : |y| < c) (h₁ : c ≤ |theta - x|) (h₂ : c ≤ |theta - y|)
      (hs : (0 ≤ x ∧ y ≤ 0) ∨ (x ≤ 0 ∧ 0 ≤ y)) : c ≤ theta := by
    rcases hs with ⟨hx0, _⟩ | ⟨_, hy0⟩
    · linarith [sub_ge_of_clearance hθ ((le_abs_self _).trans_lt hx) h₁]
    · linarith [sub_ge_of_clearance hθ ((le_abs_self _).trans_lt hy) h₂]
  by_cases hθ : 0 ≤ theta
  · rw [abs_of_nonneg hθ]
    exact posCase hθ hx hy h₁ h₂ hs
  · rw [abs_of_neg (lt_of_not_ge hθ)]
    apply posCase (x := -x) (y := -y) (by linarith)
    · simpa only [abs_neg] using hx
    · simpa only [abs_neg] using hy
    · simpa only [neg_sub_neg, abs_sub_comm] using h₁
    · simpa only [neg_sub_neg, abs_sub_comm] using h₂
    · rcases hs with ⟨hx0, hy0⟩ | ⟨hx0, hy0⟩
      · exact Or.inr ⟨by linarith, by linarith⟩
      · exact Or.inl ⟨by linarith, by linarith⟩

private lemma right_line_abs_arg_band (F : TwoHighFrame D t m a b) {p q : Fin s}
    (hpa : p ≠ a) (hpb : p ≠ b) (hqa : q ≠ a) (hqb : q ≠ b)
    (hpq : p ≠ q) (hre : (coord p).re ≤ (coord q).re) :
    clearance ≤ |Complex.arg (coord q - coord p)| ∧
      |Complex.arg (coord q - coord p)| ≤ Real.pi / 2 := by
  have hxy := F.right_line_clearances hpa hpb hqa hqb hpq hre
  have hx := (F.abs_anchor_args_le hpa hpb).1.trans_lt F.fan_lt_clearance
  have hy := (F.abs_anchor_args_le hqa hqb).2.trans_lt F.fan_lt_clearance
  refine ⟨abs_le_of_two_clearances hx hy hxy.1 hxy.2 ?_,
    Complex.abs_arg_le_pi_div_two_iff.mpr (by simpa using sub_nonneg.mpr hre)⟩
  rcases F.residual_same_side hpa hpb hqa hqb with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · exact Or.inl ⟨Complex.arg_nonneg_iff.mpr hp.le, (Complex.arg_neg_iff.mpr (by simpa using hq)).le⟩
  · exact Or.inr ⟨(Complex.arg_neg_iff.mpr hp).le, Complex.arg_nonneg_iff.mpr (by simpa using hq.le)⟩

private lemma projective_band_of_angle_one {w : ℂ} (hw : w ≠ 0)
    (hlo : clearance ≤ InnerProductGeometry.angle 1 w)
    (hhi : InnerProductGeometry.angle 1 w ≤ Real.pi - clearance) :
    1 / t ≤ projectiveDir w ∧ projectiveDir w ≤ 1 - 1 / t := by
  have hone : projectiveDir 1 = 0 := by simp [projectiveDir]
  have he := angle_eq_projective_or_supplement one_ne_zero hw
  rw [hone, sub_zero, abs_of_nonneg (projectiveDir_mem w).1] at he
  have h₁ : (1 / t) * Real.pi = clearance := by ring
  have h₂ : (1 - 1 / t) * Real.pi = Real.pi - clearance := by ring
  rw [← h₁] at hlo
  rw [← h₂] at hhi
  rcases he with he | he <;> rw [he] at hlo hhi
  · exact ⟨(mul_le_mul_iff_left₀ Real.pi_pos).mp hlo, (mul_le_mul_iff_left₀ Real.pi_pos).mp hhi⟩
  · have ha := (mul_le_mul_iff_left₀ Real.pi_pos).mp hlo
    have hb := (mul_le_mul_iff_left₀ Real.pi_pos).mp hhi
    exact ⟨by linarith, by linarith⟩

/-- Every residual projective line is in the closed transverse direction band. -/
lemma residual_direction_band (F : TwoHighFrame D t m a b) {p q : Fin s}
    (hpa : p ≠ a) (hpb : p ≠ b) (hqa : q ≠ a) (hqb : q ≠ b) (hpq : p ≠ q) :
    1 / t ≤ projectiveDir (coord q - coord p) ∧
      projectiveDir (coord q - coord p) ≤ 1 - 1 / t := by
  have hne := sub_ne_zero.mpr ((anchorCoord_injective D F.distinct).ne hpq.symm)
  apply projective_band_of_angle_one hne
  · by_cases hre : (coord p).re ≤ (coord q).re
    · rw [angle_one_eq_abs_arg hne]
      exact (F.right_line_abs_arg_band hpa hpb hqa hqb hpq hre).1
    · have hne' := sub_ne_zero.mpr ((anchorCoord_injective D F.distinct).ne hpq)
      obtain ⟨_, h⟩ := F.right_line_abs_arg_band hqa hqb hpa hpb hpq.symm (le_of_not_ge hre)
      rw [← neg_sub (coord p) (coord q), InnerProductGeometry.angle_neg_right,
        angle_one_eq_abs_arg hne']
      linarith [F.clearance_le_half_pi]
  · by_cases hre : (coord p).re ≤ (coord q).re
    · rw [angle_one_eq_abs_arg hne]
      linarith [(F.right_line_abs_arg_band hpa hpb hqa hqb hpq hre).2, F.clearance_le_half_pi]
    · have hne' := sub_ne_zero.mpr ((anchorCoord_injective D F.distinct).ne hpq)
      obtain ⟨h, _⟩ := F.right_line_abs_arg_band hqa hqb hpa hpb hpq.symm (le_of_not_ge hre)
      rw [← neg_sub (coord p) (coord q), InnerProductGeometry.angle_neg_right,
        angle_one_eq_abs_arg hne']
      linarith

private lemma projectiveDir_neg_of_nonreal {w : ℂ} (hw : w.im ≠ 0) :
    projectiveDir (-w) = projectiveDir w := by
  change Int.fract (Complex.arg (-w) / Real.pi) = Int.fract (Complex.arg w / Real.pi)
  rcases lt_or_gt_of_ne hw with h | h
  · rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg h, add_div, div_self Real.pi_ne_zero]
    simpa only [Int.cast_one] using Int.fract_add_intCast (Complex.arg w / Real.pi) 1
  · rw [Complex.arg_neg_eq_arg_sub_pi_of_im_pos h, sub_div, div_self Real.pi_ne_zero]
    simpa only [Int.cast_one] using Int.fract_sub_intCast (Complex.arg w / Real.pi) 1

lemma projectiveDir_of_nonneg_arg {w : ℂ} (h₀ : 0 ≤ Complex.arg w)
    (h₁ : Complex.arg w < Real.pi) : projectiveDir w = Complex.arg w / Real.pi := by
  have h : Int.floor (Complex.arg w / Real.pi) = 0 := by
    have ha := Int.floor_nonneg.mpr (div_nonneg h₀ Real.pi_pos.le)
    have hb : Int.floor (Complex.arg w / Real.pi) < 1 := Int.floor_lt.mpr (by
      rw [Int.cast_one]
      exact (div_lt_one Real.pi_pos).mpr h₁)
    omega
  simp [projectiveDir, h]

private lemma projectiveDir_of_neg_arg {w : ℂ} (h : Complex.arg w < 0) :
    projectiveDir w = 1 + Complex.arg w / Real.pi := by
  have hf : Int.floor (Complex.arg w / Real.pi) = -1 := by
    have ha : -1 ≤ Int.floor (Complex.arg w / Real.pi) := Int.le_floor.mpr (by
      push_cast
      exact (le_div_iff₀ Real.pi_pos).mpr (by linarith [Complex.neg_pi_lt_arg w]))
    have hb : Int.floor (Complex.arg w / Real.pi) < 0 := Int.floor_lt.mpr (by
      simpa only [Int.cast_zero] using div_neg_of_neg_of_pos h Real.pi_pos)
    omega
  simp only [projectiveDir, hf, Int.cast_neg, Int.cast_one]
  ring

private lemma div_pi_lt_inv {x : ℝ} (h : x < clearance) : x / Real.pi < 1 / t := by
  calc
    _ < clearance / Real.pi := (div_lt_div_iff_of_pos_right Real.pi_pos).mpr h
    _ = _ := by
      by_cases ht : t = 0
      · simp [ht]
      · field_simp

private lemma dead_arc_capacity (F : TwoHighFrame D t m a b) {x y : ℝ}
    (hx : 0 ≤ x) (hy : y ≤ 0) (h : x - y ≤ 2 * fan) :
    let lo := x / Real.pi
    let hi := 1 + y / Real.pi
    0 ≤ 1 + lo - hi ∧ 1 + lo - hi ≤ 2 * (t - (m : ℝ)) / t ∧
      gapCapacity (t * (1 + lo - hi)) = 0 := by
  have ht : 0 < t := by linarith [F.t_ge_two]
  have he : 1 + x / Real.pi - (1 + y / Real.pi) = (x - y) / Real.pi := by ring
  have he' : (2 * fan) / Real.pi = 2 * (t - (m : ℝ)) / t := by field_simp
  change 0 ≤ 1 + x / Real.pi - (1 + y / Real.pi) ∧
    1 + x / Real.pi - (1 + y / Real.pi) ≤ 2 * (t - (m : ℝ)) / t ∧
    gapCapacity (t * (1 + x / Real.pi - (1 + y / Real.pi))) = 0
  rw [he]
  have hsmall : (x - y) / Real.pi ≤ 2 * (t - (m : ℝ)) / t := by
    rw [← he']
    exact div_le_div_of_nonneg_right h Real.pi_pos.le
  refine ⟨div_nonneg (by linarith) Real.pi_pos.le, hsmall, gapCapacity_zero ?_⟩
  calc
    _ ≤ t * (2 * (t - (m : ℝ)) / t) := mul_le_mul_of_nonneg_left hsmall ht.le
    _ = 2 * (t - (m : ℝ)) := by field_simp
    _ < 2 := by linarith [F.lt_floor_add_one]

/-- The arc through the reference direction has no residual line and zero capacity. -/
lemma anchor_dead_arc (F : TwoHighFrame D t m a b) {p : Fin s} (hpa : p ≠ a) (hpb : p ≠ b) :
    let u := projectiveDir (-coord p)
    let v := projectiveDir (1 - coord p)
    let lo := min u v
    let hi := max u v
    lo < 1 / t ∧ 1 - 1 / t < hi ∧
      0 ≤ 1 + lo - hi ∧ 1 + lo - hi ≤ 2 * (t - (m : ℝ)) / t ∧
      gapCapacity (t * (1 + lo - hi)) = 0 ∧
      ∀ q, q ≠ a → q ≠ b → q ≠ p →
        lo < projectiveDir (coord q - coord p) ∧ projectiveDir (coord q - coord p) < hi := by
  let x := Complex.arg (coord p)
  let y := Complex.arg (1 - coord p)
  have hx : |x| ≤ fan := (F.abs_anchor_args_le hpa hpb).1
  have hy : |y| ≤ fan := (F.abs_anchor_args_le hpa hpb).2
  have hxpi : x < Real.pi := by linarith [(abs_le.mp (F.small_anchor_args hpa hpb).1.le).2, Real.pi_pos]
  have hypi : y < Real.pi := by linarith [(abs_le.mp (F.small_anchor_args hpa hpb).2.le).2, Real.pi_pos]
  have hproj := projectiveDir_neg_of_nonreal (F.residual_im_ne_zero hpa hpb)
  have hhalf : 1 / t ≤ (1 : ℝ) / 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) F.t_ge_two
  have finish {lo hi : ℝ} (hlo : lo < 1 / t) (hhi : 1 - 1 / t < hi) :
      ∀ q, q ≠ a → q ≠ b → q ≠ p →
        lo < projectiveDir (coord q - coord p) ∧ projectiveDir (coord q - coord p) < hi := by
    intro q hqa hqb hqp
    have h := F.residual_direction_band hpa hpb hqa hqb hqp.symm
    exact ⟨hlo.trans_le h.1, h.2.trans_lt hhi⟩
  dsimp only
  rw [hproj]
  rcases lt_or_gt_of_ne (F.residual_im_ne_zero hpa hpb) with hp | hp
  · have hy₀ : 0 ≤ y := Complex.arg_nonneg_iff.mpr (by simpa using hp.le)
    have hx₀ : x < 0 := Complex.arg_neg_iff.mpr hp
    rw [projectiveDir_of_neg_arg hx₀, projectiveDir_of_nonneg_arg hy₀ hypi]
    have hlo : y / Real.pi < 1 / t := div_pi_lt_inv
      ((le_abs_self _).trans_lt (hy.trans_lt F.fan_lt_clearance))
    have hhi : 1 - 1 / t < 1 + x / Real.pi := by
      have h := div_pi_lt_inv ((neg_le_abs _).trans_lt (hx.trans_lt F.fan_lt_clearance))
      rw [neg_div] at h
      linarith
    have hle : y / Real.pi ≤ 1 + x / Real.pi := by linarith
    rw [min_eq_right hle, max_eq_left hle]
    have hc := F.dead_arc_capacity hy₀ hx₀.le (by linarith [(abs_le.mp hy).2, (abs_le.mp hx).1])
    exact ⟨hlo, hhi, hc.1, hc.2.1, hc.2.2, finish hlo hhi⟩
  · have hx₀ : 0 ≤ x := Complex.arg_nonneg_iff.mpr hp.le
    have hy₀ : y < 0 := Complex.arg_neg_iff.mpr (by simpa using hp)
    rw [projectiveDir_of_nonneg_arg hx₀ hxpi, projectiveDir_of_neg_arg hy₀]
    have hlo : x / Real.pi < 1 / t := div_pi_lt_inv
      ((le_abs_self _).trans_lt (hx.trans_lt F.fan_lt_clearance))
    have hhi : 1 - 1 / t < 1 + y / Real.pi := by
      have h := div_pi_lt_inv ((neg_le_abs _).trans_lt (hy.trans_lt F.fan_lt_clearance))
      rw [neg_div] at h
      linarith
    have hle : x / Real.pi ≤ 1 + y / Real.pi := by linarith
    rw [min_eq_left hle, max_eq_right hle]
    have hc := F.dead_arc_capacity hx₀ hy₀.le (by linarith [(abs_le.mp hx).2, (abs_le.mp hy).1])
    exact ⟨hlo, hhi, hc.1, hc.2.1, hc.2.2, finish hlo hhi⟩

/-- In any sorted row for the normalized centers, the dead arc is the wrapping gap. -/
lemma normalized_row_dead_gap (F : TwoHighFrame D t m a b) (N : CenterGapData s)
    (hN : ∀ i, N.center i = coord i) {p : Fin s} (hpa : p ≠ a) (hpb : p ≠ b) :
    ∃ j : Fin (s - 1), j.val + 1 = s - 1 ∧
      cyclicGap (N.dir p) j ≤ 2 * (t - (m : ℝ)) / t ∧
      gapCapacity (t * cyclicGap (N.dir p) j) = 0 := by
  let u := projectiveDir (-coord p)
  let v := projectiveDir (1 - coord p)
  let lo := min u v
  let hi := max u v
  obtain ⟨_, _, _, hlen, hzero, hinterior⟩ := F.anchor_dead_arc hpa hpb
  have hsize := F.size
  let first : Fin (s - 1) := ⟨0, by omega⟩
  let last : Fin (s - 1) := ⟨s - 2, by omega⟩
  have hlast : last.val + 1 = s - 1 := by dsimp only [last]; omega
  have hdir (j : Fin (s - 1)) :
      N.dir p j = projectiveDir (coord (N.other p j).val - coord p) := by
    rw [N.dir_spec, hN, hN]
  let ia := (N.other p).symm ⟨a, hpa.symm⟩
  let ib := (N.other p).symm ⟨b, hpb.symm⟩
  have ha : N.dir p ia = u := by rw [hdir]; simp [ia, u]
  have hb : N.dir p ib = v := by
    rw [hdir]
    simp only [ib, Equiv.apply_symm_apply, anchorCoord_right D F.distinct, v]
  have hbetween (j : Fin (s - 1)) : lo ≤ N.dir p j ∧ N.dir p j ≤ hi := by
    let q := (N.other p j).val
    by_cases hqa : q = a
    · have hj : N.dir p j = u := by
        rw [hdir]
        change projectiveDir (coord q - coord p) = u
        rw [hqa, anchorCoord_left, zero_sub]
      rw [hj]
      exact ⟨min_le_left _ _, le_max_left _ _⟩
    by_cases hqb : q = b
    · have hj : N.dir p j = v := by
        rw [hdir]
        change projectiveDir (coord q - coord p) = v
        rw [hqb, anchorCoord_right D F.distinct]
      rw [hj]
      exact ⟨min_le_right _ _, le_max_right _ _⟩
    · rw [hdir]
      have h := hinterior q hqa hqb (N.other p j).property
      exact ⟨h.1.le, h.2.le⟩
  have hfirst_lo : N.dir p first = lo := by
    apply le_antisymm _ (hbetween first).1
    have hz (j : Fin (s - 1)) : first ≤ j := by change 0 ≤ j.val; omega
    exact le_min
      (by simpa only [ha] using (N.dir_strictMono p).monotone (hz ia))
      (by simpa only [hb] using (N.dir_strictMono p).monotone (hz ib))
  have hlast_hi : N.dir p last = hi := by
    apply le_antisymm (hbetween last).2
    have hz (j : Fin (s - 1)) : j ≤ last := by
      have := j.isLt
      change j.val ≤ s - 2
      omega
    exact max_le
      (by simpa only [ha] using (N.dir_strictMono p).monotone (hz ia))
      (by simpa only [hb] using (N.dir_strictMono p).monotone (hz ib))
  have hg : cyclicGap (N.dir p) last = 1 + lo - hi := by
    rw [cyclicGap, dif_neg (by omega : ¬ last.val + 1 < s - 1)]
    change 1 + N.dir p first - N.dir p last = _
    rw [hfirst_lo, hlast_hi]
  exact ⟨last, hlast, hg.trans_le hlen, by rwa [hg]⟩

private lemma right_line_complementary_angles (F : TwoHighFrame D t m a b) {p q : Fin s}
    (hpa : p ≠ a) (hpb : p ≠ b) (hqa : q ≠ a) (hqb : q ≠ b)
    (hpq : p ≠ q) (hre : (coord p).re ≤ (coord q).re) :
    let theta := Complex.arg (coord q - coord p)
    |theta - Complex.arg (1 - coord p)| ≤ Real.pi - clearance ∧
      |theta - Complex.arg (coord q)| ≤ Real.pi - clearance := by
  have hL := F.angle_cap_coord (p := b) (q := p) (r := q) hpb.symm hpq.symm
  have hR := F.angle_cap_coord (p := a) (q := q) (r := p) hqa.symm hpq
  have hw := sub_ne_zero.mpr ((anchorCoord_injective D F.distinct).ne hpq.symm)
  have ht : |Complex.arg (coord q - coord p)| ≤ Real.pi / 2 :=
    Complex.abs_arg_le_pi_div_two_iff.mpr (by simpa using sub_nonneg.mpr hre)
  simp only [anchorCoord_right D F.distinct] at hL
  rw [angle_eq_abs_arg_sub (F.one_sub_coord_ne_zero hpb) hw
    (abs_sub_le_pi_of_halves ht (F.small_anchor_args hpa hpb).2.le)] at hL
  simp only [anchorCoord_left, zero_sub] at hR
  rw [← neg_sub (coord q) (coord p), InnerProductGeometry.angle_neg_neg,
    angle_eq_abs_arg_sub (F.coord_ne_zero hqa) hw
      (abs_sub_le_pi_of_halves ht (F.small_anchor_args hqa hqb).1.le)] at hR
  exact ⟨hL, hR⟩

private lemma clearance_le_third_pi_of_right_line (F : TwoHighFrame D t m a b) {p q : Fin s}
    (hpa : p ≠ a) (hpb : p ≠ b) (hqa : q ≠ a) (hqb : q ≠ b)
    (hpq : p ≠ q) (hre : (coord p).re ≤ (coord q).re) : 3 * clearance ≤ Real.pi := by
  let theta := Complex.arg (coord q - coord p)
  let ap := Complex.arg (coord p)
  let bp := Complex.arg (1 - coord p)
  let aq := Complex.arg (coord q)
  let bq := Complex.arg (1 - coord q)
  obtain ⟨hP, hQ⟩ := F.right_line_clearances hpa hpb hqa hqb hpq hre
  change clearance ≤ |theta - ap| at hP
  change clearance ≤ |theta - bq| at hQ
  obtain ⟨hL, hR⟩ := F.right_line_complementary_angles hpa hpb hqa hqb hpq hre
  change |theta - bp| ≤ Real.pi - clearance at hL
  change |theta - aq| ≤ Real.pi - clearance at hR
  have hp := F.anchor_separation hpa hpb
  have hq := F.anchor_separation hqa hqb
  change clearance ≤ |ap - bp| at hp
  change clearance ≤ |aq - bq| at hq
  have hboundA : |ap| < clearance := (F.abs_anchor_args_le hpa hpb).1.trans_lt F.fan_lt_clearance
  have hboundB : |bq| < clearance := (F.abs_anchor_args_le hqa hqb).2.trans_lt F.fan_lt_clearance
  rcases F.residual_same_side hpa hpb hqa hqb with ⟨hpim, hqim⟩ | ⟨hpim, hqim⟩
  · have ha : 0 ≤ ap := Complex.arg_nonneg_iff.mpr hpim.le
    have hb : bp ≤ 0 := (Complex.arg_neg_iff.mpr (by simpa using hpim)).le
    have ha' : 0 ≤ aq := Complex.arg_nonneg_iff.mpr hqim.le
    have hb' : bq ≤ 0 := (Complex.arg_neg_iff.mpr (by simpa using hqim)).le
    by_cases hθ : 0 ≤ theta
    · have h := sub_ge_of_clearance hθ ((le_abs_self _).trans_lt hboundA) hP
      rw [abs_of_nonneg (by linarith)] at hp
      linarith [(abs_le.mp hL).2]
    · have h := sub_ge_of_clearance (theta := -theta) (x := -bq)
        (by linarith) ((neg_le_abs _).trans_lt hboundB)
        (by simpa only [neg_sub_neg, abs_sub_comm] using hQ)
      rw [abs_of_nonneg (by linarith)] at hq
      linarith [(abs_le.mp hR).1]
  · have ha : ap ≤ 0 := (Complex.arg_neg_iff.mpr hpim).le
    have hb : 0 ≤ bp := Complex.arg_nonneg_iff.mpr (by simpa using hpim.le)
    have ha' : aq ≤ 0 := (Complex.arg_neg_iff.mpr hqim).le
    have hb' : 0 ≤ bq := Complex.arg_nonneg_iff.mpr (by simpa using hqim.le)
    by_cases hθ : 0 ≤ theta
    · have h := sub_ge_of_clearance hθ ((le_abs_self _).trans_lt hboundB) hQ
      rw [abs_of_nonpos (by linarith)] at hq
      linarith [(abs_le.mp hR).2]
    · have h := sub_ge_of_clearance (theta := -theta) (x := -ap)
        (by linarith) ((neg_le_abs _).trans_lt hboundA)
        (by simpa only [neg_sub_neg, abs_sub_comm] using hP)
      rw [abs_of_nonpos (by linarith)] at hp
      linarith [(abs_le.mp hL).1]

/-- A second residual center forces \(t \ge 3\), so the dead arc is then strictly shorter. -/
lemma t_ge_three_of_residual_pair (F : TwoHighFrame D t m a b) {p q : Fin s}
    (hpa : p ≠ a) (hpb : p ≠ b) (hqa : q ≠ a) (hqb : q ≠ b) (hpq : p ≠ q) :
    (3 : ℝ) ≤ t := by
  have h : 3 * clearance ≤ Real.pi := by
    by_cases hre : (coord p).re ≤ (coord q).re
    · exact F.clearance_le_third_pi_of_right_line hpa hpb hqa hqb hpq hre
    · exact F.clearance_le_third_pi_of_right_line hqa hqb hpa hpb hpq.symm (le_of_not_ge hre)
  have ht : 0 < t := by linarith [F.t_ge_two]
  have h' := mul_le_mul_of_nonneg_right h ht.le
  have he : 3 * clearance * t = 3 * Real.pi := by field_simp
  rw [he] at h'
  exact (mul_le_mul_iff_left₀ Real.pi_pos).mp (by simpa only [mul_comm Real.pi t] using h')

lemma dead_arc_lt_half_of_residual_pair (F : TwoHighFrame D t m a b) {p q : Fin s}
    (hpa : p ≠ a) (hpb : p ≠ b) (hqa : q ≠ a) (hqb : q ≠ b) (hpq : p ≠ q) :
    let u := projectiveDir (-coord p)
    let v := projectiveDir (1 - coord p)
    1 + min u v - max u v < 1 / 2 := by
  obtain ⟨_, _, _, hlen, _, _⟩ := F.anchor_dead_arc hpa hpb
  have ht := F.t_ge_three_of_residual_pair hpa hpb hqa hqb hpq
  have hm : (3 : ℝ) ≤ m := by
    have hn : 3 ≤ m := by
      by_contra! hlt
      have hm₂ := F.floor_ge_two
      have : m = 2 := by omega
      have h := F.lt_floor_add_one
      rw [this] at h
      norm_num at h
      linarith
    exact_mod_cast hn
  apply hlen.trans_lt
  apply (div_lt_iff₀ (by linarith : 0 < t)).2
  linarith [F.lt_floor_add_one]

lemma projectiveDir_neg (w : ℂ) : projectiveDir (-w) = projectiveDir w := by
  have realDir {z : ℂ} (hz : z.im = 0) : projectiveDir z = 0 := by
    change Int.fract (Complex.arg z / Real.pi) = 0
    by_cases h : 0 ≤ z.re
    · rw [Complex.arg_eq_zero_iff.mpr ⟨h, hz⟩, zero_div]
      simp [Int.fract]
    · rw [Complex.arg_eq_pi_iff.mpr ⟨lt_of_not_ge h, hz⟩, div_self Real.pi_ne_zero]
      exact Int.fract_one
  by_cases hw : w.im = 0
  · rw [realDir (by simpa only [Complex.neg_im, neg_zero] using congrArg Neg.neg hw), realDir hw]
  · exact projectiveDir_neg_of_nonreal hw

lemma anchorCoord_swap (F : TwoHighFrame D t m a b) (i : Fin s) :
    anchorCoord D b a i = 1 - coord i := by
  have h := sub_ne_zero.mpr (D.injective.ne F.distinct.symm)
  unfold anchorCoord
  rw [show D.center a - D.center b = -(D.center b - D.center a) by ring, inv_neg]
  field_simp
  ring

lemma swap (F : TwoHighFrame D t m a b) : TwoHighFrame D t m b a :=
  ⟨F.size, F.distinct.symm, F.floor_ge_two, F.floor_le, F.lt_floor_add_one,
    F.cap, F.rightHigh, F.leftHigh⟩

/-- Use the smallest anchor clearance in the subset at each endpoint of the band. -/
noncomputable def refinedResidualBand (D : CenterGapData s) (a b : Fin s) (t : ℝ)
    (S : Finset (Fin s)) (hS : S.Nonempty) : Set ℝ :=
  Set.Icc
    ((Real.pi / t + S.inf' hS (fun i => Complex.arg (anchorCoord D a b i))) / Real.pi)
    (1 - (Real.pi / t + S.inf' hS (fun i => -Complex.arg (1 - anchorCoord D a b i))) / Real.pi)

lemma refinedResidualBand_subset {S T : Finset (Fin s)} {hS : S.Nonempty} {hT : T.Nonempty}
    (h : S ⊆ T) :
    refinedResidualBand D a b t S hS ⊆ refinedResidualBand D a b t T hT := by
  have hmin (f : Fin s → ℝ) : T.inf' hT f ≤ S.inf' hS f :=
    Finset.le_inf' _ _ (fun i hi => Finset.inf'_le f (h hi))
  intro x hx
  obtain ⟨hl, hr⟩ := hx
  dsimp only [refinedResidualBand] at hl hr ⊢
  have hclear : clearance ≤ clearance := le_rfl
  have h₁ := div_le_div_of_nonneg_right
    (add_le_add hclear (hmin (fun i => Complex.arg (coord i)))) Real.pi_pos.le
  have h₂ := div_le_div_of_nonneg_right
    (add_le_add hclear (hmin (fun i => -Complex.arg (1 - coord i)))) Real.pi_pos.le
  exact ⟨h₁.trans hl, by linarith⟩

private lemma fan_add_clearance_le_half (F : TwoHighFrame D t m a b) {p q : Fin s}
    (hpa : p ≠ a) (hpb : p ≠ b) (hqa : q ≠ a) (hqb : q ≠ b) (hpq : p ≠ q) :
    fan + clearance ≤ Real.pi / 2 := by
  have ht3 := F.t_ge_three_of_residual_pair hpa hpb hqa hqb hpq
  have hm3 : (3 : ℝ) ≤ m := by
    have hn : 3 ≤ m := by
      by_contra! hlt
      have hm₂ := F.floor_ge_two
      have he : m = 2 := by omega
      have ht := F.lt_floor_add_one
      rw [he] at ht
      norm_num at ht
      linarith
    exact_mod_cast hn
  have hf : (1 + (t - (m : ℝ))) / t ≤ 1 / 2 := by
    apply (div_le_iff₀ (by linarith : 0 < t)).mpr
    linarith [F.lt_floor_add_one]
  calc
    _ = ((1 + (t - (m : ℝ))) / t) * Real.pi := by ring
    _ ≤ (1 / 2) * Real.pi := mul_le_mul_of_nonneg_right hf Real.pi_pos.le
    _ = _ := by ring

private lemma right_line_mem_refinedResidualBand (F : TwoHighFrame D t m a b)
    {S : Finset (Fin s)} (hS : S.Nonempty) {p q : Fin s} (hp : p ∈ S) (hq : q ∈ S)
    (hpa : p ≠ a) (hpb : p ≠ b) (hqa : q ≠ a) (hqb : q ≠ b)
    (hpq : p ≠ q)
    (hre : (coord p).re ≤ (coord q).re) :
    projectiveDir (coord q - coord p) ∈ refinedResidualBand D a b t S hS := by
  let w := coord q - coord p
  let x := S.inf' hS (fun i => Complex.arg (coord i))
  let y := S.inf' hS (fun i => -Complex.arg (1 - coord i))
  have hx : x ≤ Complex.arg (coord p) := Finset.inf'_le _ hp
  have hy : y ≤ -Complex.arg (1 - coord q) := Finset.inf'_le _ hq
  have hhalf := F.fan_add_clearance_le_half hpa hpb hqa hqb hpq
  have hxhalf : (clearance + x) / Real.pi ≤ 1 / 2 := (div_le_iff₀ Real.pi_pos).mpr (by
    linarith [(le_abs_self (Complex.arg (coord p))).trans (F.abs_anchor_args_le hpa hpb).1])
  have hyhalf : (clearance + y) / Real.pi ≤ 1 / 2 := (div_le_iff₀ Real.pi_pos).mpr (by
    linarith [(neg_le_abs (Complex.arg (1 - coord q))).trans (F.abs_anchor_args_le hqa hqb).2])
  have hw : |Complex.arg w| ≤ Real.pi / 2 :=
    Complex.abs_arg_le_pi_div_two_iff.mpr (by simpa [w] using sub_nonneg.mpr hre)
  obtain ⟨hleft, hright⟩ := F.right_line_clearances hpa hpb hqa hqb hpq hre
  change clearance ≤ |Complex.arg w - Complex.arg (coord p)| at hleft
  change clearance ≤ |Complex.arg w - Complex.arg (1 - coord q)| at hright
  change (clearance + x) / Real.pi ≤ projectiveDir w ∧
      projectiveDir w ≤ 1 - (clearance + y) / Real.pi
  by_cases harg : 0 ≤ Complex.arg w
  · rw [projectiveDir_of_nonneg_arg harg (by linarith [(abs_le.mp hw).2, Real.pi_pos])]
    have h := sub_ge_of_clearance harg
      ((le_abs_self _).trans_lt ((F.abs_anchor_args_le hpa hpb).1.trans_lt F.fan_lt_clearance)) hleft
    have hhalf' : Complex.arg w / Real.pi ≤ 1 / 2 := (div_le_iff₀ Real.pi_pos).mpr (by
      linarith [(abs_le.mp hw).2])
    exact ⟨div_le_div_of_nonneg_right (by linarith) Real.pi_pos.le, by linarith⟩
  · rw [projectiveDir_of_neg_arg (lt_of_not_ge harg)]
    have h := sub_ge_of_clearance (theta := -Complex.arg w) (x := -Complex.arg (1 - coord q))
      (by linarith) ((neg_le_abs _).trans_lt
        ((F.abs_anchor_args_le hqa hqb).2.trans_lt F.fan_lt_clearance))
      (by simpa only [neg_sub_neg, abs_sub_comm] using hright)
    have hhalf' : -(1 / 2) ≤ Complex.arg w / Real.pi := (le_div_iff₀ Real.pi_pos).mpr (by
      linarith [(abs_le.mp hw).1])
    have h' := div_le_div_of_nonneg_right (show clearance + y ≤ -Complex.arg w by linarith)
      Real.pi_pos.le
    rw [neg_div] at h'
    exact ⟨by linarith, by linarith⟩

lemma residual_line_mem_refinedResidualBand (F : TwoHighFrame D t m a b)
    {S : Finset (Fin s)} (hS : S.Nonempty) {p q : Fin s} (hp : p ∈ S) (hq : q ∈ S)
    (hpa : p ≠ a) (hpb : p ≠ b) (hqa : q ≠ a) (hqb : q ≠ b)
    (hpq : p ≠ q) :
    projectiveDir (coord q - coord p) ∈ refinedResidualBand D a b t S hS := by
  by_cases hre : (coord p).re ≤ (coord q).re
  · exact F.right_line_mem_refinedResidualBand hS hp hq hpa hpb hqa hqb hpq hre
  · rw [← neg_sub (coord p) (coord q), projectiveDir_neg]
    exact F.right_line_mem_refinedResidualBand hS hq hp hqa hqb hpa hpb hpq.symm
      (le_of_not_ge hre)

/-- An internal axis with one unit of clearance from both anchor lines is in the same band. -/
lemma internal_axis_mem_refinedResidualBand {S : Finset (Fin s)} (hS : S.Nonempty)
    {p : Fin s} (hp : p ∈ S) {x : ℝ}
    (hl : (clearance + Complex.arg (coord p)) / Real.pi ≤ x)
    (hr : x ≤ 1 - (clearance - Complex.arg (1 - coord p)) / Real.pi) :
    x ∈ refinedResidualBand D a b t S hS := by
  have h₁ : S.inf' hS (fun i => Complex.arg (coord i)) ≤ Complex.arg (coord p) :=
    Finset.inf'_le _ hp
  have h₂ : S.inf' hS (fun i => -Complex.arg (1 - coord i)) ≤ -Complex.arg (1 - coord p) :=
    Finset.inf'_le _ hp
  have hclear : clearance ≤ clearance := le_rfl
  have hleft := div_le_div_of_nonneg_right (add_le_add hclear h₁) Real.pi_pos.le
  have hright := div_le_div_of_nonneg_right (add_le_add hclear h₂) Real.pi_pos.le
  have hright' :
      (clearance + S.inf' hS (fun i => -Complex.arg (1 - coord i))) / Real.pi ≤
        (clearance - Complex.arg (1 - coord p)) / Real.pi := by
    simpa only [sub_eq_add_neg] using hright
  dsimp only [refinedResidualBand]
  exact ⟨hleft.trans hl, by linarith only [hr, hright']⟩

private lemma real_pos_of_small_args {w : ℂ} (hw : w ≠ 0)
    (h : |Complex.arg w| < Real.pi / 2) : 0 < w.re :=
  (Complex.abs_arg_lt_pi_div_two_iff.mp h).resolve_right hw

/-- Above the anchor line, distinct residual centers cannot reverse the order
of their two anchor angles. -/
lemma eq_of_mixed_anchor_orders (F : TwoHighFrame D t m a b) {p q : Fin s}
    (hpa : p ≠ a) (hpb : p ≠ b) (hqa : q ≠ a) (hqb : q ≠ b)
    (hup : 0 < (coord p).im)
    (ha : Complex.arg (coord p) ≤ Complex.arg (coord q))
    (hb : -Complex.arg (1 - coord q) ≤ -Complex.arg (1 - coord p)) :
    p = q := by
  by_contra hpq
  let P := coord p
  let Q := coord q
  have hP := F.small_anchor_args hpa hpb
  have hQ := F.small_anchor_args hqa hqb
  have px : 0 < P.re := real_pos_of_small_args (F.coord_ne_zero hpa) hP.1
  have qx : 0 < Q.re := real_pos_of_small_args (F.coord_ne_zero hqa) hQ.1
  have px' : 0 < 1 - P.re := by
    simpa only [Complex.sub_re, Complex.one_re] using
      real_pos_of_small_args (F.one_sub_coord_ne_zero hpb) hP.2
  have qx' : 0 < 1 - Q.re := by
    simpa only [Complex.sub_re, Complex.one_re] using
      real_pos_of_small_args (F.one_sub_coord_ne_zero hqb) hQ.2
  let u := P.im / P.re
  let v := P.im / (1 - P.re)
  have uu : 0 < u := div_pos hup px
  have vv : 0 < v := div_pos hup px'
  have pu : u * P.re = P.im := div_mul_cancel₀ _ px.ne'
  have pv : v * (1 - P.re) = P.im := div_mul_cancel₀ _ px'.ne'
  have ta : Real.tan (Complex.arg P) = u := Complex.tan_arg P
  have tb (w : ℂ) : Real.tan (-Complex.arg (1 - w)) = w.im / (1 - w.re) := by
    rw [Real.tan_neg, Complex.tan_arg, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im, zero_sub, neg_div, neg_neg]
  have htanLeft := Real.strictMonoOn_tan.monotoneOn (abs_lt.mp hP.1) (abs_lt.mp hQ.1) ha
  rw [ta, Complex.tan_arg] at htanLeft
  have htanRight := Real.strictMonoOn_tan.monotoneOn
    (abs_lt.mp (by simpa only [abs_neg] using hQ.2 : |(-Complex.arg (1 - Q))| < Real.pi / 2))
    (abs_lt.mp (by simpa only [abs_neg] using hP.2 : |(-Complex.arg (1 - P))| < Real.pi / 2)) hb
  rw [tb, tb] at htanRight
  have hq1 : u * Q.re ≤ Q.im := (le_div_iff₀ qx).mp htanLeft
  have hq2 : Q.im ≤ v * (1 - Q.re) := (div_le_iff₀ qx').mp htanRight
  have hLower : u * (Q.re - P.re) ≤ Q.im - P.im := by rw [mul_sub, pu]; linarith
  have hUpper : Q.im - P.im ≤ -v * (Q.re - P.re) := by nlinarith
  have hQP : Q.re < P.re := by
    by_contra! hge
    have he : Q.re = P.re := by
      by_contra hne
      have hn : P.re ≠ Q.re := fun h => hne h.symm
      have hd : 0 < Q.re - P.re := sub_pos.mpr (lt_of_le_of_ne hge hn)
      linarith [mul_pos uu hd, mul_pos vv hd]
    have he' : Q.im = P.im := by rw [he, sub_self, mul_zero] at hLower hUpper; linarith
    exact hpq ((anchorCoord_injective D F.distinct) (Complex.ext he.symm he'.symm))
  let w := P - Q
  have hwre : 0 < w.re := by simpa only [w, Complex.sub_re] using sub_pos.mpr hQP
  have hw : |Complex.arg w| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hwre)
  have hwtan₁ : -v ≤ Real.tan (Complex.arg w) := by
    rw [Complex.tan_arg]
    apply (le_div_iff₀ hwre).mpr
    dsimp only [w, Complex.sub_re, Complex.sub_im]
    nlinarith
  have hwtan₂ : Real.tan (Complex.arg w) ≤ u := by
    rw [Complex.tan_arg]
    apply (div_le_iff₀ hwre).mpr
    dsimp only [w, Complex.sub_re, Complex.sub_im]
    nlinarith
  have hl : Complex.arg (1 - P) ≤ Complex.arg w := by
    apply (Real.strictMonoOn_tan.le_iff_le (abs_lt.mp hP.2) (abs_lt.mp hw)).mp
    have he := tb P
    rw [Real.tan_neg] at he
    have hv : Real.tan (Complex.arg (1 - P)) = -v := by linarith
    rwa [hv]
  have hh : Complex.arg w ≤ Complex.arg P := by
    apply (Real.strictMonoOn_tan.le_iff_le (abs_lt.mp hw) (abs_lt.mp hP.1)).mp
    rwa [ta]
  have hsmall : |Complex.arg w| < clearance := by
    have hfan := F.abs_anchor_args_le hpa hpb
    exact abs_lt.mpr ⟨by linarith [(abs_le.mp hfan.2).1, F.fan_lt_clearance],
      by linarith [(abs_le.mp hfan.1).2, F.fan_lt_clearance]⟩
  exact hsmall.not_ge
    (F.right_line_abs_arg_band hqa hqb hpa hpb (fun h => hpq h.symm) hQP.le).1

lemma shared_anchor_minima (F : TwoHighFrame D t m a b) {S : Finset (Fin s)}
    (hS : S.Nonempty) (hres : ∀ i ∈ S, i ≠ a ∧ i ≠ b)
    (hup : ∀ i ∈ S, 0 < (coord i).im) :
    ∃ p ∈ S,
      S.inf' hS (fun i => Complex.arg (coord i)) = Complex.arg (coord p) ∧
      S.inf' hS (fun i => -Complex.arg (1 - coord i)) = -Complex.arg (1 - coord p) := by
  obtain ⟨p, hp, hmin⟩ := Finset.exists_mem_eq_inf' hS (fun i => Complex.arg (coord i))
  refine ⟨p, hp, hmin, le_antisymm (Finset.inf'_le _ hp) ?_⟩
  apply Finset.le_inf'
  intro q hq
  by_contra! hlt
  have ha : Complex.arg (coord p) ≤ Complex.arg (coord q) := hmin ▸ Finset.inf'_le _ hq
  have he := F.eq_of_mixed_anchor_orders (hres p hp).1 (hres p hp).2
    (hres q hq).1 (hres q hq).2 (hup p hp) ha hlt.le
  exact hlt.ne (by rw [he])

/-- On a nonempty upper-side subset, the two envelope endpoints can be
charged to the same residual center. The band length is at most \(1-3/t\). -/
lemma refinedResidualBand_width_le (F : TwoHighFrame D t m a b) {S : Finset (Fin s)}
    (hS : S.Nonempty) (hres : ∀ i ∈ S, i ≠ a ∧ i ≠ b)
    (hup : ∀ i ∈ S, 0 < (coord i).im) :
    1 - (clearance + S.inf' hS (fun i => -Complex.arg (1 - coord i))) / Real.pi -
      (clearance + S.inf' hS (fun i => Complex.arg (coord i))) / Real.pi ≤ 1 - 3 / t := by
  obtain ⟨p, hp, hA, hB⟩ := F.shared_anchor_minima hS hres hup
  rw [hA, hB]
  have ha := Complex.arg_nonneg_iff.mpr (hup p hp).le
  have hb : Complex.arg (1 - coord p) < 0 := Complex.arg_neg_iff.mpr (by simpa using hup p hp)
  have h := F.anchor_separation (hres p hp).1 (hres p hp).2
  rw [abs_of_nonneg (sub_nonneg.mpr (hb.le.trans ha))] at h
  have hd := div_le_div_of_nonneg_right h Real.pi_pos.le
  have ht : 0 < t := by linarith [F.t_ge_two]
  have hr : clearance / Real.pi = 1 / t := by field_simp
  rw [hr, sub_div] at hd
  rw [add_div, add_div, hr, neg_div]
  rw [show (3 : ℝ) / t = 3 * (1 / t) by ring]
  linarith

/-- After division by π, the band has width strictly below `(m - 2) / t`. -/
lemma refinedResidualBand_width_lt (F : TwoHighFrame D t m a b) {S : Finset (Fin s)}
    (hS : S.Nonempty) (hres : ∀ i ∈ S, i ≠ a ∧ i ≠ b)
    (hup : ∀ i ∈ S, 0 < (coord i).im) :
    1 - (clearance + S.inf' hS (fun i => -Complex.arg (1 - coord i))) / Real.pi -
      (clearance + S.inf' hS (fun i => Complex.arg (coord i))) / Real.pi <
        ((m - 2 : ℕ) : ℝ) / t := by
  apply (F.refinedResidualBand_width_le hS hres hup).trans_lt
  have ht : 0 < t := by linarith [F.t_ge_two]
  have he : (1 - 3 / t) * t = t - 3 := by field_simp [ht.ne']
  rw [lt_div_iff₀ ht, he, Nat.cast_sub F.floor_ge_two]
  norm_num
  linarith [F.lt_floor_add_one]

lemma refinedResidualBand_span_lt (F : TwoHighFrame D t m a b) {S : Finset (Fin s)}
    (hS : S.Nonempty) (hres : ∀ i ∈ S, i ≠ a ∧ i ≠ b)
    (hup : ∀ i ∈ S, 0 < (coord i).im) {x y : ℝ}
    (hx : x ∈ refinedResidualBand D a b t S hS)
    (hy : y ∈ refinedResidualBand D a b t S hS) :
    |y - x| < ((m - 2 : ℕ) : ℝ) / t := by
  change _ ≤ x ∧ x ≤ _ at hx
  change _ ≤ y ∧ y ≤ _ at hy
  exact abs_lt.mpr ⟨by linarith [F.refinedResidualBand_width_lt hS hres hup, hx.2, hy.1],
    by linarith [F.refinedResidualBand_width_lt hS hres hup, hx.1, hy.2]⟩

end TwoHighFrame

/-- Distinct axis labels occupy points at least `spacing` apart. -/
def AxisSeparated {ι : Type*} (spacing : ℝ) (axis : ι → ℝ) : Prop :=
  ∀ i j, i ≠ j → spacing ≤ |axis i - axis j|

/-- The axes are separated even if they come from different rows. -/
def CrossRowAxisSeparated {ι : Type*} {k : ι → ℕ} (spacing : ℝ)
    (axis : (i : ι) → Fin (k i) → ℝ) : Prop :=
  ∀ ⦃i j⦄, i ≠ j → ∀ p q, spacing ≤ |axis i p - axis j q|

lemma taggedAxes_separated {ι : Type*} {k : ι → ℕ} {spacing : ℝ}
    {axis : (i : ι) → Fin (k i) → ℝ}
    (within : ∀ i, AxisSeparated spacing (axis i))
    (cross : CrossRowAxisSeparated spacing axis) :
    AxisSeparated spacing (fun p : Σ i, Fin (k i) => axis p.1 p.2) := by
  rintro ⟨i, p⟩ ⟨j, q⟩ h
  by_cases hij : i = j
  · subst j
    exact within i p q (fun hpq => h (by cases hpq; rfl))
  · exact cross hij p q

/-- A line interval holding `n` separated points has length at least `(n-1) * spacing`. -/
lemma separatedAxis_card_sub_one_mul_le_span {ι : Type*} [Fintype ι]
    {axis : ι → ℝ} {spacing lo hi : ℝ} (hspacing : 0 < spacing)
    (hn : Nonempty ι) (sep : AxisSeparated spacing axis)
    (mem : ∀ i, axis i ∈ Set.Icc lo hi) :
    ((Fintype.card ι - 1 : ℕ) : ℝ) * spacing ≤ hi - lo := by
  classical
  have hinj : Function.Injective axis := by
    intro i j hij
    by_contra hne
    have h := sep i j hne
    rw [hij, sub_self, abs_zero] at h
    exact hspacing.not_ge h
  let T := Finset.univ.image axis
  have hc : T.card = Fintype.card ι := by
    dsimp only [T]
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
  let d := Fintype.card ι - 1
  have hT : T.card = d + 1 := by
    have hp := Fintype.card_pos_iff.mpr hn
    dsimp [d]
    omega
  let row : Fin (d + 1) → ℝ := T.orderEmbOfFin hT
  have preimage (j : Fin (d + 1)) : ∃ i, axis i = row j := by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (T.orderEmbOfFin_mem hT j)
    exact ⟨i, hi⟩
  have step (j : Fin d) : spacing ≤ row j.succ - row j.castSucc := by
    have hlt : row j.castSucc < row j.succ :=
      (T.orderEmbOfFin hT).strictMono j.castSucc_lt_succ
    obtain ⟨i, hi⟩ := preimage j.succ
    obtain ⟨i', hi'⟩ := preimage j.castSucc
    have hne : i ≠ i' := by
      intro he
      subst i'
      exact hlt.ne (hi'.symm.trans hi)
    simpa only [hi, hi', abs_of_pos (sub_pos.mpr hlt)] using sep i i' hne
  have endpoints (j : Fin (d + 1)) : row j ∈ Set.Icc lo hi := by
    obtain ⟨i, hi⟩ := preimage j
    simpa only [hi] using mem i
  calc
    (d : ℝ) * spacing = ∑ _ : Fin d, spacing := by simp
    _ ≤ ∑ j : Fin d, (row j.succ - row j.castSucc) :=
      Finset.sum_le_sum (fun j _ => step j)
    _ = row (Fin.last d) - row 0 := sum_fin_differences d row
    _ ≤ hi - lo := sub_le_sub (endpoints (Fin.last d)).2 (endpoints 0).1

lemma separatedAxis_card_le_of_strict_span {ι : Type*} [Fintype ι]
    {axis : ι → ℝ} {spacing lo hi : ℝ} {K : ℕ} (hspacing : 0 < spacing)
    (sep : AxisSeparated spacing axis) (mem : ∀ i, axis i ∈ Set.Icc lo hi)
    (span : hi - lo < (K : ℝ) * spacing) : Fintype.card ι ≤ K := by
  by_contra! h
  have hn : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  have hK : (K : ℝ) ≤ ((Fintype.card ι - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show K ≤ Fintype.card ι - 1 by omega)
  exact (mul_le_mul_of_nonneg_right hK hspacing.le).not_gt
    ((separatedAxis_card_sub_one_mul_le_span hspacing hn sep mem).trans_lt span)

lemma separatedAxis_card_le_of_closed_span {ι : Type*} [Fintype ι]
    {axis : ι → ℝ} {spacing lo hi : ℝ} {K : ℕ} (hspacing : 0 < spacing)
    (sep : AxisSeparated spacing axis) (mem : ∀ i, axis i ∈ Set.Icc lo hi)
    (span : hi - lo ≤ (K : ℝ) * spacing) : Fintype.card ι ≤ K + 1 := by
  by_contra! h
  have hn : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  have hK : (K : ℝ) < ((Fintype.card ι - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show K < Fintype.card ι - 1 by omega)
  exact (mul_lt_mul_of_pos_right hK hspacing).not_ge
    ((separatedAxis_card_sub_one_mul_le_span hspacing hn sep mem).trans span)

private lemma sum_pow_le_pow_sum_of_positive {ι : Type*} (S : Finset ι) (k : ι → ℕ)
    (positive : ∀ i ∈ S, 1 ≤ k i) :
    (∑ i ∈ S, (2 : ℕ) ^ k i) ≤ 2 ^ (∑ i ∈ S, k i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hki := positive i (Finset.mem_insert_self i S)
    have hpos j (hj : j ∈ S) := positive j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    by_cases hS : S.Nonempty
    · obtain ⟨j, hj⟩ := hS
      have hsum : 1 ≤ ∑ j ∈ S, k j :=
        (hpos j hj).trans (Finset.single_le_sum (fun j _ => Nat.zero_le (k j)) hj)
      have hx : 2 ≤ (2 : ℕ) ^ k i := by
        simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hki
      have hy : 2 ≤ (2 : ℕ) ^ (∑ j ∈ S, k j) := by
        simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hsum
      refine (add_le_add (le_refl ((2 : ℕ) ^ k i)) (ih hpos)).trans ?_
      rw [pow_add]
      have h₁ := Nat.mul_le_mul_left ((2 : ℕ) ^ k i) hy
      have h₂ := Nat.mul_le_mul_right ((2 : ℕ) ^ (∑ j ∈ S, k j)) hx
      omega
    · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
      simp

/-- Each positive row uses its own number of slots. Each zero row needs one slot. -/
lemma dyadicWeight_le_of_slot_budget {ι : Type*} [Fintype ι] {k : ι → ℕ} {K : ℕ}
    (slots : (∑ i, max 1 (k i)) ≤ K) :
    (∑ i, (2 : ℕ) ^ k i) ≤ 2 ^ K := by
  calc
    _ ≤ ∑ i, (2 : ℕ) ^ max 1 (k i) := Finset.sum_le_sum fun i _ =>
      Nat.pow_le_pow_right (by decide) (le_max_right 1 (k i))
    _ ≤ 2 ^ (∑ i, max 1 (k i)) :=
      sum_pow_le_pow_sum_of_positive Finset.univ _ (fun i _ => le_max_left 1 (k i))
    _ ≤ 2 ^ K := Nat.pow_le_pow_right (by decide) slots

namespace TwoHighFrame

/-- Axes are measured in units of π. Cross-row separation is a hypothesis. -/
lemma internalAxes_count_of_cross_separation {s : ℕ} {D : CenterGapData s} {a b : Fin s}
    {t : ℝ} {m : ℕ} (F : TwoHighFrame D t m a b) {S : Finset (Fin s)}
    (hS : S.Nonempty) (hres : ∀ i ∈ S, i ≠ a ∧ i ≠ b)
    (hup : ∀ i ∈ S, 0 < (anchorCoord D a b i).im)
    {k : S → ℕ} {axis : (i : S) → Fin (k i) → ℝ}
    (mem : ∀ i p, axis i p ∈ refinedResidualBand D a b t S hS)
    (within : ∀ i, AxisSeparated (1 / t) (axis i))
    (cross : CrossRowAxisSeparated (1 / t) axis) :
    (∑ i, k i) ≤ m - 2 := by
  have hspacing : 0 < 1 / t := one_div_pos.mpr (by linarith [F.t_ge_two])
  have span := F.refinedResidualBand_width_lt hS hres hup
  rw [div_eq_mul_one_div (((m - 2 : ℕ) : ℝ)) t] at span
  have h := separatedAxis_card_le_of_strict_span hspacing
    (taggedAxes_separated within cross) (fun p => mem p.1 p.2) span
  simpa using h

lemma kraft_of_internalAxis_separation {s : ℕ} {D : CenterGapData s} {a b : Fin s}
    {t : ℝ} {m : ℕ} (F : TwoHighFrame D t m a b) {S : Finset (Fin s)}
    (hS : S.Nonempty) (hres : ∀ i ∈ S, i ≠ a ∧ i ≠ b)
    (hup : ∀ i ∈ S, 0 < (anchorCoord D a b i).im)
    {k : S → ℕ} {axis : (i : S) → Fin (k i) → ℝ}
    (mem : ∀ i p, axis i p ∈ refinedResidualBand D a b t S hS)
    (within : ∀ i, AxisSeparated (1 / t) (axis i))
    (cross : CrossRowAxisSeparated (1 / t) axis) (positive : ∀ i, 1 ≤ k i) :
    (∑ i, (2 : ℕ) ^ k i) ≤ 2 ^ (m - 2) := by
  apply dyadicWeight_le_of_slot_budget
  have hk (i : S) : max 1 (k i) = k i := max_eq_right (positive i)
  simpa only [hk] using
    F.internalAxes_count_of_cross_separation hS hres hup mem within cross

end TwoHighFrame

/-- The residual exponent profile of the nine-center witness cannot be packed
even in a closed interval of length nine times the separation. -/
lemma nineCenterAxes_not_cross_separated {spacing lo hi : ℝ}
    (hspacing : 0 < spacing) (span : hi - lo ≤ 9 * spacing)
    {axis : (i : Fin 7) → Fin (if i = 0 then 7 else 6) → ℝ}
    (mem : ∀ i p, axis i p ∈ Set.Icc lo hi)
    (within : ∀ i, AxisSeparated spacing (axis i)) :
    ¬ CrossRowAxisSeparated spacing axis := by
  intro cross
  have h := separatedAxis_card_le_of_closed_span (K := 9) hspacing
    (taggedAxes_separated within cross) (fun p => mem p.1 p.2) (by simpa using span)
  have hcount : Fintype.card (Σ i : Fin 7, Fin (if i = 0 then 7 else 6)) = 43 := by
    simp [Fin.sum_univ_succ]
  rw [hcount] at h
  omega

/-- A split may use any separately justified geometric rule. Its two subtrees
each receive one fewer bit of budget, and all leaves keep their original weight. -/
inductive TreeCharging {ι : Type*} [DecidableEq ι] (exponent : ι → ℕ)
    (compatible : Finset ι → Finset ι → Prop) : Finset ι → ℕ → Prop
  | leaf (i : ι) {budget : ℕ} (fits : exponent i ≤ budget) :
      TreeCharging exponent compatible {i} budget
  | branch {S T : Finset ι} {budget : ℕ}
      (disjoint : Disjoint S T) (split : compatible S T)
      (left : TreeCharging exponent compatible S budget)
      (right : TreeCharging exponent compatible T budget) :
      TreeCharging exponent compatible (S ∪ T) (budget + 1)

/-- A single sector of the given width contains all directions across a split. -/
def CrossDirectionSector {ι : Type*} (direction : ι → ι → ℝ) (width : ℝ)
    (S T : Finset ι) : Prop :=
  ∃ lo : ℝ, ∀ i ∈ S, ∀ j ∈ T, direction i j ∈ Set.Ico lo (lo + width)

lemma TreeCharging.weight_le {ι : Type*} [DecidableEq ι] {exponent : ι → ℕ}
    {compatible : Finset ι → Finset ι → Prop} {S : Finset ι} {budget : ℕ}
    (tree : TreeCharging exponent compatible S budget) :
    (∑ i ∈ S, (2 : ℕ) ^ exponent i) ≤ 2 ^ budget := by
  induction tree with
  | leaf i fits =>
      simpa only [Finset.sum_singleton] using Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) fits
  | branch h _ _ _ hl hr =>
      rw [Finset.sum_union h, pow_succ]
      omega

lemma TreeCharging.children_saturate {ι : Type*} [DecidableEq ι] {exponent : ι → ℕ}
    {compatible : Finset ι → Finset ι → Prop} {S T : Finset ι} {budget : ℕ}
    (hs : TreeCharging exponent compatible S budget)
    (ht : TreeCharging exponent compatible T budget) (h : Disjoint S T)
    (heq : (∑ i ∈ S ∪ T, (2 : ℕ) ^ exponent i) = 2 ^ (budget + 1)) :
    (∑ i ∈ S, (2 : ℕ) ^ exponent i) = 2 ^ budget ∧
      (∑ i ∈ T, (2 : ℕ) ^ exponent i) = 2 ^ budget := by
  have hl := hs.weight_le
  have hr := ht.weight_le
  rw [Finset.sum_union h, pow_succ] at heq
  omega

/-- Integer subtraction preserves the signed change, including a loss of weight. -/
lemma deletion_weight_identity {s : ℕ} (before : Fin (s + 1) → ℕ)
    (after delta : Fin s → ℕ) (i : Fin (s + 1))
    (hdelta : ∀ j, after j = before (i.succAbove j) + delta j) :
    (∑ j, (2 : ℤ) ^ after j) - (∑ j, (2 : ℤ) ^ before j) =
      -(2 : ℤ) ^ before i +
        ∑ j, (2 : ℤ) ^ before (i.succAbove j) * ((2 : ℤ) ^ delta j - 1) := by
  rw [Fin.sum_univ_succAbove _ i]
  simp_rw [hdelta, pow_add, mul_sub, mul_one, Finset.sum_sub_distrib]
  ring

lemma gapCapacity_add_delta (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ∃ d : ℕ, d ≤ 2 ∧ gapCapacity (x + y) = gapCapacity x + gapCapacity y + d := by
  have h := gapCapacity_merge x y hx hy
  exact ⟨gapCapacity (x + y) - (gapCapacity x + gapCapacity y), by omega, by omega⟩

private def skipIndex (removed j : ℕ) : ℕ :=
  if j < removed then j else j + 1

private def replacementSlot (d removed : ℕ) : ℕ :=
  if removed = 0 then d - 1 else removed - 1

private def cycleStep (row : ℕ → ℝ) (d j : ℕ) : ℝ :=
  if j + 1 < d then row (j + 1) - row j else 1 + row 0 - row j

private lemma step_after_erase (row : ℕ → ℝ) (d r j : ℕ)
    (hr : r ≤ d) (hj : j < d) :
    cycleStep (row ∘ skipIndex r) d j =
      cycleStep row (d + 1) (skipIndex r j) +
        if j = replacementSlot d r then cycleStep row (d + 1) r else 0 := by
  by_cases hr0 : r = 0
  · subst r
    by_cases hlast : j + 1 < d
    · have hbefore : j + 1 + 1 < d + 1 := by omega
      have hp : j ≠ d - 1 := by omega
      simp [cycleStep, skipIndex, replacementSlot, hlast, hbefore, hp]
    · have he : j = d - 1 := by omega
      have hafter : ¬ j + 1 + 1 < d + 1 := by omega
      have hd : 1 < d + 1 := by omega
      simp only [cycleStep, skipIndex, replacementSlot, Function.comp_apply, Nat.not_lt_zero,
        if_false, if_true, if_neg hlast, if_neg hafter,
        if_pos he, Nat.zero_add, if_pos hd]
      ring
  · have hrpos : 0 < r := by omega
    by_cases hbefore : j + 1 < r
    · have hjr : j < r := by omega
      have hjd : j + 1 < d := by omega
      have hjd' : j + 1 < d + 1 := by omega
      have hp : j ≠ r - 1 := by omega
      simp [cycleStep, skipIndex, replacementSlot, hr0, hbefore, hjr, hjd, hjd', hp]
    by_cases hprev : j + 1 = r
    · have hjr : j < r := by omega
      have hrd₀ : r < d + 1 := by omega
      have hp : j = r - 1 := by omega
      by_cases hrd : r < d
      · have hrd' : r + 1 < d + 1 := by omega
        simp only [cycleStep, skipIndex, replacementSlot, Function.comp_apply,
          if_neg hr0, if_pos hjr, if_pos hp, hprev, if_pos hrd, if_pos hrd₀,
          lt_irrefl, if_false, if_pos hrd']
        ring
      · have hrd' : ¬ r + 1 < d + 1 := by omega
        simp only [cycleStep, skipIndex, replacementSlot, Function.comp_apply,
          if_neg hr0, if_pos hrpos, if_pos hjr, if_neg hrd, if_pos hrd₀, if_pos hp,
          if_neg hrd', hprev]
        ring
    · have hskip : ¬ j < r := by omega
      have hskip' : ¬ j + 1 < r := by omega
      have hp : j ≠ r - 1 := by omega
      by_cases hjd : j + 1 < d
      · have hjd' : j + 1 + 1 < d + 1 := by omega
        simp [cycleStep, skipIndex, replacementSlot, hr0, hskip, hskip', hp, hjd, hjd']
      · have hjd' : ¬ j + 1 + 1 < d + 1 := by omega
        simp [cycleStep, skipIndex, replacementSlot, hr0, hrpos, hskip, hp, hjd, hjd']

private lemma cyclicGap_as_step {d : ℕ} (row : ℕ → ℝ) (j : Fin d) :
    cyclicGap (fun i : Fin d => row i.val) j = cycleStep row d j.val := by
  unfold cyclicGap cycleStep
  by_cases h : j.val + 1 < d <;> simp [h]

private lemma succAbove_val_as_skip {d : ℕ} (r : Fin (d + 1)) (j : Fin d) :
    (r.succAbove j).val = skipIndex r.val j.val := by
  unfold Fin.succAbove skipIndex
  by_cases h : j.val < r.val
  · have h' : j.castSucc < r := h
    rw [if_pos h', if_pos h]
    rfl
  · have h' : ¬ j.castSucc < r := h
    rw [if_neg h', if_neg h]
    rfl

private lemma cyclicGap_after_erase {d : ℕ} (row : Fin (d + 1) → ℝ)
    (r : Fin (d + 1)) (j : Fin d) :
    cyclicGap (row ∘ r.succAbove) j = cyclicGap row (r.succAbove j) +
      if j.val = replacementSlot d r.val then cyclicGap row r else 0 := by
  let a (k : ℕ) := if h : k < d + 1 then row ⟨k, h⟩ else 0
  have ha (i : Fin (d + 1)) : row i = a i.val := by
    unfold a
    rw [dif_pos i.isLt]
  have oldRow : row = fun i => a i.val := funext ha
  have newRow : row ∘ r.succAbove = fun i => (a ∘ skipIndex r.val) i.val := by
    funext i
    exact (ha _).trans (congrArg a (succAbove_val_as_skip r i))
  rw [newRow, cyclicGap_as_step, step_after_erase _ _ _ _ (by have := r.isLt; omega) j.isLt]
  conv_rhs =>
    rw [oldRow, cyclicGap_as_step, cyclicGap_as_step, succAbove_val_as_skip]

lemma cyclic_capacity_after_erase {d : ℕ} (row : Fin (d + 1) → ℝ)
    (r : Fin (d + 1)) (t : ℝ) (hd : 0 < d) (ht : 0 ≤ t)
    (hg : ∀ j, 0 ≤ cyclicGap row j) :
    ∃ delta : ℕ, delta ≤ 2 ∧
      (∑ j : Fin d, gapCapacity (t * cyclicGap (row ∘ r.succAbove) j)) =
        (∑ j : Fin (d + 1), gapCapacity (t * cyclicGap row j)) + delta := by
  let p : Fin d := ⟨replacementSlot d r.val, by
    have hr := r.isLt
    unfold replacementSlot
    split <;> omega⟩
  let old (j : Fin (d + 1)) := gapCapacity (t * cyclicGap row j)
  let new (j : Fin d) := gapCapacity (t * cyclicGap (row ∘ r.succAbove) j)
  have hsame (j : Fin d) (hj : j ≠ p) : new j = old (r.succAbove j) := by
    have he : j.val ≠ replacementSlot d r.val := fun h => hj (Fin.ext h)
    simp [new, old, cyclicGap_after_erase, he]
  have hmerge : new p =
      gapCapacity (t * cyclicGap row (r.succAbove p) + t * cyclicGap row r) := by
    unfold new
    rw [cyclicGap_after_erase, if_pos (show p.val = replacementSlot d r.val from rfl), mul_add]
  obtain ⟨delta, hdelta, hm⟩ := gapCapacity_add_delta
    (t * cyclicGap row (r.succAbove p)) (t * cyclicGap row r)
    (mul_nonneg ht (hg _)) (mul_nonneg ht (hg _))
  refine ⟨delta, hdelta, ?_⟩
  change (∑ j, new j) = (∑ j, old j) + delta
  rw [Fin.sum_univ_succAbove old r,
    ← Finset.sum_erase_add _ new (Finset.mem_univ p),
    ← Finset.sum_erase_add _ (fun j => old (r.succAbove j)) (Finset.mem_univ p)]
  have hsum : (∑ j ∈ Finset.univ.erase p, new j) =
      ∑ j ∈ Finset.univ.erase p, old (r.succAbove j) :=
    Finset.sum_congr rfl (fun j hj => hsame j (Finset.ne_of_mem_erase hj))
  rw [hsum, hmerge, hm]
  change _ + (old (r.succAbove p) + old r + delta) = _
  omega

private lemma row_after_center_erase {d : ℕ} (D : CenterGapData (d + 2 + 1))
    (D' : CenterGapData (d + 2)) (r : Fin (d + 2 + 1)) (i : Fin (d + 2))
    (hcenter : ∀ j, D'.center j = D.center (r.succAbove j)) :
    ∃ e : Fin (d + 2), D'.dir i = D.dir (r.succAbove i) ∘ e.succAbove := by
  let ii := r.succAbove i
  let e : Fin (d + 2) := (D.other ii).symm ⟨r, Fin.ne_succAbove r i⟩
  have he : ((D.other ii) e).val = r := by simp [e]
  refine ⟨e, ((D'.dir_strictMono i).range_inj
    ((D.dir_strictMono ii).comp (Fin.strictMono_succAbove e))).mp ?_⟩
  ext z
  constructor
  · rintro ⟨j, rfl⟩
    let v := (D'.other i j).val
    have hv : v ≠ i := (D'.other i j).property
    let q : Fin (d + 2) := (D.other ii).symm
      ⟨r.succAbove v, fun h => hv (Fin.succAbove_right_injective h)⟩
    have hq : ((D.other ii) q).val = r.succAbove v := by simp [q]
    have hqe : q ≠ e := by
      intro h
      exact Fin.succAbove_ne r v (hq.symm.trans (by rw [h, he]))
    obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq hqe
    refine ⟨j', ?_⟩
    change D.dir ii (e.succAbove j') = D'.dir i j
    rw [hj', D.dir_spec, D'.dir_spec, hq, hcenter v, hcenter i]
  · rintro ⟨j, rfl⟩
    let v := (D.other ii (e.succAbove j)).val
    have hv : v ≠ ii := (D.other ii (e.succAbove j)).property
    have hvr : v ≠ r := by
      intro h
      apply Fin.succAbove_ne e j
      apply (D.other ii).injective
      exact Subtype.ext (h.trans he.symm)
    obtain ⟨v', hv'⟩ := Fin.exists_succAbove_eq hvr
    have hv'i : v' ≠ i := by
      intro h
      apply hv
      rw [← hv', h]
    let j' := (D'.other i).symm ⟨v', hv'i⟩
    have hj' : (D'.other i j').val = v' := by simp [j']
    refine ⟨j', ?_⟩
    change D'.dir i j' = D.dir ii (e.succAbove j)
    rw [D'.dir_spec, D.dir_spec, hj', hcenter v', hv', hcenter i]

lemma removalDelta : RemovalDeltaGoal := by
  intro s D D' r t hs ht hcenter i
  obtain ⟨d, hd⟩ : ∃ d, s = d + 2 := ⟨s - 2, by omega⟩
  subst s
  obtain ⟨e, he⟩ := row_after_center_erase D D' r i hcenter
  have hnonneg j := cyclicGap_nonneg (D.dir_strictMono (r.succAbove i))
    (dir_mem D (r.succAbove i)) j
  obtain ⟨delta, hdelta, hEq⟩ := cyclic_capacity_after_erase
    (D.dir (r.succAbove i)) e t (by omega) ht hnonneg
  have hf : gapExponent D' t i = gapExponent D t (r.succAbove i) + delta := by
    unfold gapExponent
    rw [he]
    exact hEq
  omega

lemma centerWeight_deletion {s : ℕ} (D : CenterGapData (s + 1)) (D' : CenterGapData s)
    (r : Fin (s + 1)) (t : ℝ) (hs : 2 ≤ s) (ht : 0 ≤ t)
    (hcenter : ∀ j, D'.center j = D.center (r.succAbove j)) :
    ∃ delta : Fin s → ℕ, (∀ j, delta j ≤ 2) ∧
      ((centerWeight D' t : ℤ) - (centerWeight D t : ℤ)) =
        -(2 : ℤ) ^ gapExponent D t r +
          ∑ j, (2 : ℤ) ^ gapExponent D t (r.succAbove j) * ((2 : ℤ) ^ delta j - 1) := by
  let delta j := gapExponent D' t j - gapExponent D t (r.succAbove j)
  have h j := removalDelta D D' r t hs ht hcenter j
  have hsum j : gapExponent D' t j = gapExponent D t (r.succAbove j) + delta j := by
    have := h j
    dsimp [delta]
    omega
  refine ⟨delta, fun j => ?_, ?_⟩
  · have := h j
    dsimp [delta]
    omega
  · simpa only [centerWeight, Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat] using
      deletion_weight_identity (gapExponent D t) (gapExponent D' t) delta r hsum

private lemma gapCapacity_of_band {x : ℝ} {m : ℕ}
    (h : (m : ℝ) ≤ x) (h' : x < (m : ℝ) + 1) : gapCapacity x = m - 1 := by
  have hl : (m : ℤ) ≤ Int.floor x := Int.le_floor.mpr (by exact_mod_cast h)
  have hr : Int.floor x < (m : ℤ) + 1 := Int.floor_lt.mpr (by exact_mod_cast h')
  unfold gapCapacity
  omega

lemma centerWeight_two {m : ℕ} (D : CenterGapData 2) (t : ℝ)
    (hm : 2 ≤ m) (ht : (m : ℝ) ≤ t) (ht' : t < (m : ℝ) + 1) :
    centerWeight D t = 2 ^ m := by
  have hk (i : Fin 2) : gapExponent D t i = m - 1 := by
    unfold gapExponent
    rw [Fin.sum_univ_one]
    change gapCapacity (t * cyclicGap (D.dir i) 0) = _
    have hgap : cyclicGap (D.dir i) 0 = 1 := by unfold cyclicGap; simp
    rw [hgap, mul_one]
    exact gapCapacity_of_band ht ht'
  have he : m = (m - 1) + 1 := by omega
  rw [centerWeight, Fin.sum_univ_two, hk, hk]
  conv_rhs => rw [he, pow_succ]
  omega

private lemma three_weight_le_of_card_high_le_one {m : ℕ}
    (D : CenterGapData 3) (t : ℝ) (hm : 2 ≤ m)
    (hle : ∀ i, gapExponent D t i ≤ m - 1) (hcard : (highCenters D t m).card ≤ 1) :
    centerWeight D t ≤ 2 ^ m := by
  classical
  let H := highCenters D t m
  let w := (2 : ℕ) ^ (m - 2)
  have hm1 : m - 1 = (m - 2) + 1 := by omega
  have hm2 : m = (m - 2) + 2 := by omega
  have h2 : (2 : ℕ) ^ (m - 1) = 2 * w := by rw [hm1, pow_succ]; dsimp [w]; ring
  have h4 : (2 : ℕ) ^ m = 4 * w := by
    conv_lhs => rw [hm2, pow_add]
    change w * 4 = 4 * w
    omega
  have hpoint (i : Fin 3) : (2 : ℕ) ^ gapExponent D t i ≤ w + (if i ∈ H then w else 0) := by
    by_cases hi : i ∈ H
    · rw [if_pos hi, mem_highCenters.mp hi, h2]
      omega
    · rw [if_neg hi, add_zero]
      apply Nat.pow_le_pow_right (by decide)
      have hne : gapExponent D t i ≠ m - 1 := fun he => hi (mem_highCenters.mpr he)
      have := hle i
      omega
  have hbonus : (∑ i : Fin 3, (if i ∈ H then w else 0)) = H.card * w := by
    rw [← Finset.sum_filter]
    simp
  unfold centerWeight
  calc
    _ ≤ ∑ i : Fin 3, (w + if i ∈ H then w else 0) := Finset.sum_le_sum (fun i _ => hpoint i)
    _ = 3 * w + H.card * w := by rw [Finset.sum_add_distrib, hbonus]; simp
    _ ≤ 2 ^ m := by
      rw [h4]
      have hc : H.card * w ≤ 1 * w := Nat.mul_le_mul_right w hcard
      omega

private lemma gapExponent_three_of_angle (D : CenterGapData 3) (i j k : Fin 3) (t : ℝ)
    (hj : j ≠ i) (hk : k ≠ i) (hjk : j ≠ k) :
    let a := EuclideanGeometry.angle (D.center j) (D.center i) (D.center k) / Real.pi
    gapExponent D t i = gapCapacity (t * a) + gapCapacity (t * (1 - a)) := by
  let j' := (D.other i).symm ⟨j, hj⟩
  let k' := (D.other i).symm ⟨k, hk⟩
  have hdj : D.dir i j' = projectiveDir (D.center j - D.center i) := by simp [D.dir_spec, j']
  have hdk : D.dir i k' = projectiveDir (D.center k - D.center i) := by simp [D.dir_spec, k']
  have hne : j' ≠ k' := by
    intro h
    exact hjk (congrArg Subtype.val ((D.other i).symm.injective h))
  have hord : D.dir i 0 ≤ D.dir i 1 := (D.dir_strictMono i).monotone (by decide)
  have hdiff : |D.dir i k' - D.dir i j'| = D.dir i 1 - D.dir i 0 := by
    have h01 (z : Fin 2) : z = 0 ∨ z = 1 := by
      have hz := z.isLt
      by_cases h : z.val = 0
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext (by change z.val = 1; omega))
    rcases h01 j' with h₀ | h₀ <;> rcases h01 k' with h₁ | h₁
    · exact (hne (h₀.trans h₁.symm)).elim
    · rw [h₀, h₁, abs_of_nonneg (sub_nonneg.mpr hord)]
    · rw [h₀, h₁, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hord)]
    · exact (hne (h₀.trans h₁.symm)).elim
  have hang := angle_eq_projective_or_supplement
    (sub_ne_zero.mpr (D.injective.ne hj)) (sub_ne_zero.mpr (D.injective.ne hk))
  rw [← hdj, ← hdk, hdiff] at hang
  change EuclideanGeometry.angle (D.center j) (D.center i) (D.center k) = _ ∨
    EuclideanGeometry.angle (D.center j) (D.center i) (D.center k) = _ at hang
  simp only
  unfold gapExponent
  rw [Fin.sum_univ_two]
  have h₀ : cyclicGap (D.dir i) 0 = D.dir i 1 - D.dir i 0 := by unfold cyclicGap; rfl
  have h₁ : cyclicGap (D.dir i) 1 = 1 + D.dir i 0 - D.dir i 1 := by unfold cyclicGap; rfl
  change gapCapacity (t * cyclicGap (D.dir i) 0) + gapCapacity (t * cyclicGap (D.dir i) 1) = _
  rw [h₀, h₁]
  rcases hang with ha | ha <;> rw [ha, mul_div_cancel_right₀ _ Real.pi_ne_zero]
  · congr 2
    ring
  · rw [add_comm]
    congr 2 <;> ring

lemma centerWeight_three_lower {m : ℕ} (D : CenterGapData 3) (t : ℝ)
    (hm : 2 ≤ m) (ht : (m : ℝ) ≤ t) (ht' : t < (m : ℝ) + 1 / 2)
    (hcap : CenterAngleCap D t) : centerWeight D t ≤ 2 ^ m :=
  three_weight_le_of_card_high_le_one D t hm
    (fun i => (gapExponent_le_and_high D i t (by decide) hm ht (by linarith)).1)
    (highCenters_card_le_one D t (by decide) hm ht ht' hcap)

lemma centerWeight_three_upper {m : ℕ} (D : CenterGapData 3) (t : ℝ)
    (hm : 2 ≤ m) (ht : (m : ℝ) ≤ t) (ht' : t < (m : ℝ) + 1)
    (hcap : CenterAngleCap D t) : centerWeight D t ≤ 2 ^ m + 2 ^ (m - 2) := by
  classical
  have hle i := (gapExponent_le_and_high D i t (by decide) hm ht ht').1
  by_cases hcard : (highCenters D t m).card ≤ 1
  · exact (three_weight_le_of_card_high_le_one D t hm hle hcard).trans (Nat.le_add_right _ _)
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (highCenters D t m).card)
  have hlt : ({a,b} : Finset (Fin 3)).card < (Finset.univ : Finset (Fin 3)).card := by simp [hab]
  obtain ⟨c, _, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hca : c ≠ a := by intro he; exact hc (by simp [he])
  have hcb : c ≠ b := by intro he; exact hc (by simp [he])
  have hsum := center_angles_sum D a b c hab
  have hA := high_center_angle_le D a t (by decide) hm ht ht' hcap
    (mem_highCenters.mp ha) b c hab.symm hca
  have hB := high_center_angle_le D b t (by decide) hm ht ht' hcap
    (mem_highCenters.mp hb) a c hab hcb
  have hC := hcap a c b hca.symm hcb.symm
  let x := EuclideanGeometry.angle (D.center a) (D.center c) (D.center b)
  change x ≤ angleAt t at hC
  have ht0 : 0 < t := lt_of_lt_of_le (by exact_mod_cast (show 0 < m by omega)) ht
  have hxupper : t * (x / Real.pi) ≤ t - 1 := by
    have h := (div_le_div_iff_of_pos_right Real.pi_pos).2 hC
    unfold angleAt at h
    rw [mul_div_cancel_right₀ _ Real.pi_ne_zero] at h
    have hh := mul_le_mul_of_nonneg_left h ht0.le
    have he : t * (1 - 1 / t) = t - 1 := by field_simp
    simpa only [he] using hh
  have hmul : t * (Real.pi / t) = Real.pi := by field_simp
  have hxlower : t - 2 * (t - (m : ℝ)) ≤ t * (x / Real.pi) := by
    have h := (mul_le_mul_of_nonneg_left (add_le_add hA hB) ht0.le)
    have he : t * ((t - (m : ℝ)) * (Real.pi / t) +
        (t - (m : ℝ)) * (Real.pi / t)) = 2 * (t - (m : ℝ)) * Real.pi := by
      calc
        _ = 2 * (t - (m : ℝ)) * (t * (Real.pi / t)) := by ring
        _ = _ := by rw [hmul]
    change _ + _ + x = Real.pi at hsum
    rw [he] at h
    have heq : Real.pi * (t * (x / Real.pi)) = t * x := by field_simp
    apply (mul_le_mul_iff_right₀ Real.pi_pos).mp
    rw [heq]
    nlinarith [congrArg (t * ·) hsum]
  have hbig : gapCapacity (t * (x / Real.pi)) = m - 2 := by
    have hm1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub (show 1 ≤ m by omega), Nat.cast_one]
    have hv := gapCapacity_of_band (m := m - 1) (x := t * (x / Real.pi))
      (by rw [hm1]; linarith) (by rw [hm1]; linarith)
    omega
  have hzero : gapCapacity (t * (1 - x / Real.pi)) = 0 := gapCapacity_zero (by
    rw [mul_sub, mul_one]
    linarith)
  have hkc : gapExponent D t c = m - 2 := by
    rw [gapExponent_three_of_angle D c a b t hca.symm hcb.symm hab]
    change gapCapacity (t * (x / Real.pi)) + gapCapacity (t * (1 - x / Real.pi)) = _
    simp [hbig, hzero]
  have hfin : (Finset.univ : Finset (Fin 3)) = {a,b,c} := by
    symm
    refine Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_
    simp [hab, hca.symm, hcb.symm]
  have hpow : (2 : ℕ) ^ m = 2 ^ (m - 1) * 2 := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ]
  unfold centerWeight
  rw [hfin]
  simp [hab, hca.symm, hcb.symm, mem_highCenters.mp ha, mem_highCenters.mp hb, hkc]
  rw [hpow]
  omega

end Erdos504.SendovStage1
