import Erdos504Formal.Erdos504SendovSpikeA
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

open scoped BigOperators

/-!
# Sendov (1995), fixed-s counterexamples

The witnesses concern the range-1 centers and their cyclic-gap capacities.
The angle certificates use rational enclosures of the original coordinates,
with analytic bounds on the trigonometric terms. The dependency model at the
end records the steps in the published counting argument.

The gap in Sendov's Lemma 4.1 (the asserted s = 4 maxima) was first publicly
reported by NoahPuckett-IO in teorth/erdosproblems#494 (2026-10-26,
https://github.com/teorth/erdosproblems/issues/494), and this development
independently supplies exact-coordinate counterexamples, Lean machine checks,
and a refutation of the published proof along the Lemma 4.1 to Lemma 4.2 to
Theorem 4.1 chain.
-/

namespace Erdos504.SendovStage1.Se95Correction

private noncomputable def deg (d : ℝ) : ℝ := d * Real.pi / 180

private noncomputable def sinPolynomial (x : ℝ) : ℝ :=
  x - x^3/6 + x^5/120 - x^7/5040 + x^9/362880 - x^11/39916800 +
    x^13/6227020800 - x^15/1307674368000

private noncomputable def cosPolynomial (x : ℝ) : ℝ :=
  1 - x^2/2 + x^4/24 - x^6/720 + x^8/40320 - x^10/3628800 +
    x^12/479001600 - x^14/87178291200

private lemma trigTaylor {x : ℝ} (hx : |x| ≤ 2) :
    |Real.sin x - sinPolynomial x| ≤ 1 / 100000000 ∧
    |Real.cos x - cosPolynomial x| ≤ 1 / 100000000 := by
  let z := (x : ℂ) * Complex.I
  have hz : ‖z‖ = |x| := by simp [z, Complex.norm_real, Real.norm_eq_abs]
  have hcond : ‖z‖ / ((16 : ℕ).succ : ℝ) ≤ 1 / 2 := by rw [hz]; linarith
  have h := Complex.exp_bound' hcond
  have hsum : (∑ j ∈ Finset.range 16, z ^ j / j.factorial) =
      ⟨cosPolynomial x, sinPolynomial x⟩ := by
    apply Complex.ext <;>
      norm_num [Finset.sum_range_succ, z, mul_pow, ← Complex.ofReal_pow,
        Complex.div_natCast, Nat.factorial, cosPolynomial, sinPolynomial] <;>
      simp [Complex.I_pow_eq_pow_mod'] <;> ring
  rw [hsum, hz] at h
  have herror : |x| ^ 16 / (Nat.factorial 16 : ℝ) * 2 ≤ 1 / 100000000 :=
    calc
      _ ≤ 2 ^ 16 / (Nat.factorial 16 : ℝ) * 2 := by gcongr
      _ ≤ _ := by norm_num [Nat.factorial]
  have hsin := Complex.abs_im_le_norm (Complex.exp z - ⟨cosPolynomial x, sinPolynomial x⟩)
  have hcos := Complex.abs_re_le_norm (Complex.exp z - ⟨cosPolynomial x, sinPolynomial x⟩)
  exact ⟨by simpa [z] using hsin.trans (h.trans herror),
    by simpa [z] using hcos.trans (h.trans herror)⟩

private lemma deg_mem_tan {d : ℝ} (hd : |d| < 90) :
    deg d ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
  have hd' := abs_lt.mp hd
  constructor <;> unfold deg <;> nlinarith only [hd'.1, hd'.2, Real.pi_pos,
    mul_pos (show 0 < d + 90 by linarith) Real.pi_pos,
    mul_pos (show 0 < 90 - d by linarith) Real.pi_pos]

/-- Rational tangent enclosure. The two polynomial tests use a margin larger
than the Taylor and argument approximation errors. -/
private lemma tan_box (d q lo hi : ℝ) (hd : |d| < 90) (hq : |q| ≤ 2)
    (hclose : |deg d - q| ≤ 1 / 100000000)
    (hlo : |lo| ≤ 4) (hhi : |hi| ≤ 4)
    (lower : lo * cosPolynomial q + 1 / 1000000 ≤ sinPolynomial q)
    (upper : sinPolynomial q + 1 / 1000000 ≤ hi * cosPolynomial q) :
    lo ≤ Real.tan (deg d) ∧ Real.tan (deg d) ≤ hi := by
  obtain ⟨hs, hc⟩ := trigTaylor hq
  have es : |Real.sin (deg d) - sinPolynomial q| ≤ 1 / 50000000 := by
    refine (abs_sub_le _ (Real.sin q) _).trans ?_
    linarith [(Real.abs_sin_sub_sin_le (deg d) q).trans hclose]
  have ec : |Real.cos (deg d) - cosPolynomial q| ≤ 1 / 50000000 := by
    refine (abs_sub_le _ (Real.cos q) _).trans ?_
    linarith [(Real.abs_cos_sub_cos_le (deg d) q).trans hclose]
  have productError (r : ℝ) (hr : |r| ≤ 4) :
      |r * Real.cos (deg d) - r * cosPolynomial q| ≤ 4 / 50000000 := by
    rw [← mul_sub, abs_mul]
    calc
      _ ≤ 4 * (1 / 50000000) :=
        mul_le_mul hr ec (abs_nonneg _) (by norm_num)
      _ = _ := by ring
  have hp := Real.cos_pos_of_mem_Ioo (deg_mem_tan hd)
  rw [Real.tan_eq_sin_div_cos]
  exact ⟨(le_div_iff₀ hp).mpr (by linarith [(abs_le.mp es).1,
      (abs_le.mp (productError lo hlo)).2]),
    (div_le_iff₀ hp).mpr (by linarith [(abs_le.mp es).2,
      (abs_le.mp (productError hi hhi)).1])⟩

private lemma normalizedArg_box {z : ℂ} (hy : 0 < z.im) {l u : ℝ}
    (hl : 0 < l) (hu : u < 1) (hlu : l ≤ u)
    (lower : Real.tan (deg (90 - 180 * u)) ≤ z.re / z.im)
    (upper : z.re / z.im ≤ Real.tan (deg (90 - 180 * l))) :
    l ≤ Complex.arg z / Real.pi ∧ Complex.arg z / Real.pi ≤ u := by
  have harg0 : 0 < Complex.arg z :=
    (Complex.arg_nonneg_iff.mpr hy.le).lt_of_ne
      (fun h => hy.ne' (Complex.arg_eq_zero_iff.mp h.symm).2)
  have hargπ : Complex.arg z < Real.pi :=
    (Complex.arg_le_pi z).lt_of_ne (fun h => hy.ne' (Complex.arg_eq_pi_iff.mp h).2)
  have hθ : Real.pi / 2 - Complex.arg z ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith, by linarith⟩
  have ht : Real.tan (Real.pi / 2 - Complex.arg z) = z.re / z.im := by
    rw [Real.tan_pi_div_two_sub, Complex.tan_arg, inv_div]
  rw [← ht] at lower upper
  have hlow := (Real.strictMonoOn_tan.le_iff_le
    (deg_mem_tan (d := 90 - 180 * u) (by rw [abs_lt]; constructor <;> linarith)) hθ).mp lower
  have hhigh := (Real.strictMonoOn_tan.le_iff_le hθ
    (deg_mem_tan (d := 90 - 180 * l) (by rw [abs_lt]; constructor <;> linarith))).mp upper
  unfold deg at hlow hhigh
  exact ⟨(le_div_iff₀ Real.pi_pos).mpr (by linarith),
    (div_le_iff₀ Real.pi_pos).mpr (by linarith)⟩

private abbrev Bounds := ℚ × ℚ

private noncomputable def upwardRay {s : ℕ} (p : Fin s → ℂ) (i j : Fin s) : ℂ :=
  if i < j then p j - p i else p i - p j

private noncomputable def bearing {s : ℕ} (p : Fin s → ℂ) (i j : Fin s) : ℝ :=
  Complex.arg (upwardRay p i j) / Real.pi

private def Encloses (b : Bounds) (x : ℝ) : Prop := (b.1 : ℝ) ≤ x ∧ x ≤ (b.2 : ℝ)

private lemma upwardRay_symm {s : ℕ} (p : Fin s → ℂ) (i j : Fin s) :
    upwardRay p i j = upwardRay p j i := by
  rcases lt_trichotomy i j with h | rfl | h
  · simp [upwardRay, h, h.not_gt]
  · rfl
  · simp [upwardRay, h, h.not_gt]

private structure Certificate (n : ℕ) where
  points : Fin (n + 1) → ℂ
  distinct : Function.Injective points
  bounds : Fin (n + 1) → Fin (n + 1) → Bounds
  unit : ∀ i j, 0 ≤ (bounds i j).1 ∧ (bounds i j).2 < 1
  bearing_mem : ∀ i j, i ≠ j → Encloses (bounds i j) (bearing points i j)
  order : Fin (n + 1) → Fin n → Fin n
  order_bijective : ∀ i, Function.Bijective (order i)
  sorted : ∀ i j k, j < k →
    (bounds i (i.succAbove (order i j))).2 < (bounds i (i.succAbove (order i k))).1

private def Certificate.row {n : ℕ} (C : Certificate n) (i : Fin (n + 1)) (j : Fin n) :
    Bounds := C.bounds i (i.succAbove (C.order i j))

private lemma Certificate.bearing_range {n : ℕ} (C : Certificate n) {i j : Fin (n + 1)}
    (hne : i ≠ j) : 0 ≤ bearing C.points i j ∧ bearing C.points i j < 1 := by
  have h := C.bearing_mem i j hne
  have hu := C.unit i j
  exact ⟨(by exact_mod_cast hu.1 : (0 : ℝ) ≤ (C.bounds i j).1).trans h.1,
    h.2.trans_lt (by exact_mod_cast hu.2)⟩

private noncomputable def Certificate.toData {n : ℕ} (C : Certificate n) :
    CenterGapData (n + 1) where
  center := C.points
  injective := C.distinct
  other i := (Equiv.ofBijective (C.order i) (C.order_bijective i)).trans (finSuccAboveEquiv i)
  dir i j := bearing C.points i (i.succAbove (C.order i j))
  dir_spec i j := by
    let k := i.succAbove (C.order i j)
    change bearing C.points i k = projectiveDir (C.points k - C.points i)
    have hr := C.bearing_range (Fin.succAbove_ne i (C.order i j)).symm
    have hh : Complex.arg (upwardRay C.points i k) / Real.pi =
        projectiveDir (upwardRay C.points i k) :=
      (TwoHighFrame.projectiveDir_of_nonneg_arg
        (by simpa only [zero_mul] using (le_div_iff₀ Real.pi_pos).mp hr.1)
        ((div_lt_one Real.pi_pos).mp hr.2)).symm
    rw [bearing, hh]
    by_cases h : i < k
    · simp [upwardRay, h]
    · simp only [upwardRay, if_neg h, ← neg_sub (C.points k) (C.points i),
        TwoHighFrame.projectiveDir_neg]
  dir_strictMono i := by
    intro j k hjk
    have hj := C.bearing_mem i _ (Fin.succAbove_ne i (C.order i j)).symm
    have hk := C.bearing_mem i _ (Fin.succAbove_ne i (C.order i k)).symm
    exact hj.2.trans_lt ((by exact_mod_cast C.sorted i j k hjk :
      ((C.row i j).2 : ℝ) < (C.row i k).1).trans_le hk.1)

private def angleUpper (a b : Bounds) (sameSide : Bool) : ℚ :=
  if sameSide then max (b.2 - a.1) (a.2 - b.1)
  else 1 - max (b.1 - a.2) (a.1 - b.2)

private lemma angle_upper_of_certificate {n : ℕ} (C : Certificate n)
    {i j k : Fin (n + 1)} (hi : i ≠ j) (hk : k ≠ j) :
    EuclideanGeometry.angle (C.points i) (C.points j) (C.points k) ≤
      (angleUpper (C.bounds j i) (C.bounds j k) (decide (j < i ↔ j < k)) : ℝ) * Real.pi := by
  let u := upwardRay C.points j i
  let v := upwardRay C.points j k
  have hu : u ≠ 0 := by
    unfold u upwardRay
    split
    · exact sub_ne_zero.mpr (fun he => hi (C.distinct he))
    · exact sub_ne_zero.mpr (fun he => hi (C.distinct he).symm)
  have hv : v ≠ 0 := by
    unfold v upwardRay
    split
    · exact sub_ne_zero.mpr (fun he => hk (C.distinct he))
    · exact sub_ne_zero.mpr (fun he => hk (C.distinct he).symm)
  have ru := C.bearing_range hi.symm
  have rv := C.bearing_range hk.symm
  let a := bearing C.points j i
  let b := bearing C.points j k
  have hd : |b - a| ≤ 1 := abs_le.mpr ⟨by linarith [ru.1, rv.1, ru.2, rv.2],
    by linarith [ru.1, rv.1, ru.2, rv.2]⟩
  have he : |Complex.arg v - Complex.arg u| = |b - a| * Real.pi := by
    simp only [a, b, bearing, ← sub_div, abs_div, abs_of_pos Real.pi_pos, u, v]
    field_simp
  have hang : InnerProductGeometry.angle u v = |b - a| * Real.pi := by
    rw [angle_eq_abs_arg_sub hu hv, he]
    rw [he]
    simpa using mul_le_mul_of_nonneg_right hd Real.pi_pos.le
  have h₁ : C.points i - C.points j = if j < i then u else -u := by
    by_cases h : j < i <;> simp [h, u, upwardRay]
  have h₂ : C.points k - C.points j = if j < k then v else -v := by
    by_cases h : j < k <;> simp [h, v, upwardRay]
  have ba : Encloses (C.bounds j i) a := C.bearing_mem j i hi.symm
  have bb : Encloses (C.bounds j k) b := C.bearing_mem j k hk.symm
  have hupper : |b - a| ≤ (angleUpper (C.bounds j i) (C.bounds j k) true : ℝ) := by
    rw [angleUpper, if_pos rfl, Rat.cast_max, Rat.cast_sub, Rat.cast_sub]
    apply abs_le.mpr
    constructor
    · have hmax := le_max_right
        ((C.bounds j k).2 - (C.bounds j i).1 : ℝ) ((C.bounds j i).2 - (C.bounds j k).1 : ℝ)
      linarith only [ba.2, bb.1, hmax]
    · have hmax := le_max_left
        ((C.bounds j k).2 - (C.bounds j i).1 : ℝ) ((C.bounds j i).2 - (C.bounds j k).1 : ℝ)
      linarith only [ba.1, bb.2, hmax]
  have hlower : 1 - |b - a| ≤ (angleUpper (C.bounds j i) (C.bounds j k) false : ℝ) := by
    rw [angleUpper, if_neg Bool.false_ne_true, Rat.cast_sub, Rat.cast_one, Rat.cast_max,
      Rat.cast_sub, Rat.cast_sub, sub_le_sub_iff_left]
    exact max_le (by linarith [bb.1, ba.2, le_abs_self (b - a)])
      (by linarith [ba.1, bb.2, neg_le_abs (b - a)])
  change InnerProductGeometry.angle (C.points i - C.points j) (C.points k - C.points j) ≤ _
  rw [h₁, h₂]
  by_cases hji : j < i <;> by_cases hjk : j < k <;>
    simp [hji, hjk,
      InnerProductGeometry.angle_neg_left,
      InnerProductGeometry.angle_neg_right, hang] <;>
    first
    | exact mul_le_mul_of_nonneg_right hupper Real.pi_pos.le
    | nlinarith only [mul_le_mul_of_nonneg_right hlower Real.pi_pos.le]

private lemma Certificate.strictCap {n : ℕ} (C : Certificate n) (t : ℚ)
    (check : ∀ i j k, i ≠ j → k ≠ j →
      angleUpper (C.bounds j i) (C.bounds j k) (decide (j < i ↔ j < k)) < 1 - 1 / t) :
    ∀ i j k : Fin (n + 1), i ≠ j → k ≠ j →
      EuclideanGeometry.angle (C.toData.center i) (C.toData.center j) (C.toData.center k) <
        angleAt (t : ℝ) := by
  intro i j k hi hk
  apply (angle_upper_of_certificate C hi hk).trans_lt
  unfold angleAt
  apply mul_lt_mul_of_pos_right _ Real.pi_pos
  exact_mod_cast check i j k hi hk

private def gapBounds {n : ℕ} (row : Fin n → Bounds) (j : Fin n) : Bounds :=
  if hj : j.val + 1 < n then
    ((row ⟨j.val + 1, hj⟩).1 - (row j).2, (row ⟨j.val + 1, hj⟩).2 - (row j).1)
  else
    let first := row ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt⟩
    (1 + first.1 - (row j).2, 1 + first.2 - (row j).1)

private lemma Certificate.gap_mem {n : ℕ} (C : Certificate n) (i : Fin (n + 1)) (j : Fin n) :
    Encloses (gapBounds (C.row i) j) (cyclicGap (C.toData.dir i) j) := by
  change Encloses (gapBounds (C.row i) j) (@cyclicGap n (C.toData.dir i) j)
  have hb (k : Fin n) : Encloses (C.row i k) (C.toData.dir i k) :=
    C.bearing_mem i _ (Fin.succAbove_ne i (C.order i k)).symm
  unfold Encloses at *
  by_cases h : j.val + 1 < n
  · simp only [gapBounds, cyclicGap, dif_pos h]
    push_cast
    exact ⟨sub_le_sub (hb ⟨_, h⟩).1 (hb j).2, sub_le_sub (hb ⟨_, h⟩).2 (hb j).1⟩
  · simp only [gapBounds, cyclicGap, dif_neg h]
    push_cast
    exact ⟨sub_le_sub (add_le_add le_rfl (hb ⟨0, _⟩).1) (hb j).2,
      sub_le_sub (add_le_add le_rfl (hb ⟨0, _⟩).2) (hb j).1⟩

private lemma Certificate.exponents {n : ℕ} (C : Certificate n) (t : ℚ) (ht : 0 ≤ t)
    (f : Fin (n + 1) → Fin n → ℤ)
    (check : ∀ i j, (f i j : ℚ) ≤ t * (gapBounds (C.row i) j).1 ∧
      t * (gapBounds (C.row i) j).2 < (f i j : ℚ) + 1) :
    ∀ i, gapExponent C.toData t i = ∑ j, (f i j - 1).toNat := by
  intro i
  unfold gapExponent
  apply Finset.sum_congr rfl
  intro j _
  have h := C.gap_mem i j
  have ht' : 0 ≤ (t : ℝ) := by exact_mod_cast ht
  have hlow : (f i j : ℝ) ≤ (t : ℝ) * (gapBounds (C.row i) j).1 := by
    exact_mod_cast (check i j).1
  have hhigh : (t : ℝ) * (gapBounds (C.row i) j).2 < (f i j : ℝ) + 1 := by
    exact_mod_cast (check i j).2
  rw [Int.floor_eq_iff.mpr ⟨hlow.trans (mul_le_mul_of_nonneg_left h.1 ht'),
    (mul_le_mul_of_nonneg_left h.2 ht').trans_lt hhigh⟩]

private def millidegrees (lo hi : ℤ) : Bounds := ((lo : ℚ) / 180000, (hi : ℚ) / 180000)

private lemma millidegrees_mem {z : ℂ} (hy : 0 < z.im) (lo hi : ℤ)
    (hl : 0 < lo) (hu : hi < 180000) (hlu : lo ≤ hi)
    (lower : Real.tan (deg (90 - (hi : ℝ) / 1000)) ≤ z.re / z.im)
    (upper : z.re / z.im ≤ Real.tan (deg (90 - (lo : ℝ) / 1000))) :
    Encloses (millidegrees lo hi) (Complex.arg z / Real.pi) := by
  have hlo : (0 : ℝ) < lo := by exact_mod_cast hl
  have hhi : (hi : ℝ) < 180000 := by exact_mod_cast hu
  have hle : (lo : ℝ) ≤ hi := by exact_mod_cast hlu
  unfold Encloses millidegrees
  push_cast
  refine normalizedArg_box hy (by linarith) (by linarith) (by linarith) ?_ ?_
  · rw [show 90 - 180 * ((hi : ℝ) / 180000) = 90 - (hi : ℝ) / 1000 by ring]
    exact lower
  · rw [show 90 - 180 * ((lo : ℝ) / 180000) = 90 - (lo : ℝ) / 1000 by ring]
    exact upper

private lemma checkUnordered {s : ℕ} {p : Fin s → ℂ} {b : Fin s → Fin s → Bounds}
    (symm : ∀ i j, b i j = b j i)
    (ordered : ∀ i j, i < j → Encloses (b i j) (bearing p i j)) :
    ∀ i j, i ≠ j → Encloses (b i j) (bearing p i j) := by
  intro i j hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact ordered i j h
  · rw [symm i j, bearing, upwardRay_symm p i j]
    exact ordered j i h

local macro "check_tan " q:term : tactic =>
  `(tactic| refine tan_box _ $q _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    first
    | (norm_num [sinPolynomial, cosPolynomial]; done)
    | (rw [abs_le]; constructor <;> unfold deg <;>
        linarith only [Real.pi_gt_d20, Real.pi_lt_d20]))

/-- Coordinates of §2.1, with the two anchors first. -/
noncomputable def fourCenters : Fin 4 → ℂ :=
  fun i => match i.val with
  | 0 => ⟨-1, 0⟩
  | 1 => ⟨1, 0⟩
  | 2 => ⟨0, Real.tan (deg 30)⟩
  | _ => ⟨0, Real.tan (deg 35)⟩

private lemma cot68 : Real.cot (deg 68) = Real.tan (deg 22) := by
  rw [← Real.tan_inv_eq_cot, ← Real.tan_pi_div_two_sub]
  congr 1
  unfold deg
  ring

/-- Coordinates of §2.2 at ε = 1/100. -/
noncomputable def fiveCenters : Fin 5 → ℂ :=
  let h := Real.tan (deg 25)
  fun i => match i.val with
  | 0 => ⟨-1, 0⟩
  | 1 => ⟨1, 0⟩
  | 2 => ⟨0, h⟩
  | 3 => ⟨Real.cot (deg 68) / 100, h + 1 / 100⟩
  | _ => ⟨0, h + 1 / 50⟩

/-- The six-center cluster at ε = 1/100. Its offsets are ordered as 0, b, a, a+b,
with a = (1/2, √3/2) and b = (3/25) • (-1/2, √3/2), before scaling. -/
noncomputable def sixCenters : Fin 6 → ℂ :=
  let h := Real.tan (deg 20)
  let r := Real.sqrt 3
  fun i => match i.val with
  | 0 => ⟨-1, 0⟩
  | 1 => ⟨1, 0⟩
  | 2 => ⟨0, h⟩
  | 3 => ⟨-3 / 5000, h + 3 * r / 5000⟩
  | 4 => ⟨1 / 200, h + r / 200⟩
  | _ => ⟨11 / 2500, h + 7 * r / 1250⟩

private lemma sqrt3_mem : (1.732050807 : ℝ) ≤ Real.sqrt 3 ∧
    Real.sqrt 3 ≤ 1.732050808 := by
  have hn : 0 ≤ (3 : ℝ) := by norm_num
  refine ⟨(sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp ?_,
    (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp ?_⟩ <;>
    rw [Real.sq_sqrt hn] <;> norm_num

private lemma distinctOfOrderedRays {s : ℕ} (p : Fin s → ℂ)
    (valid : ∀ i j, i < j → p j - p i ≠ 0) : Function.Injective p := by
  intro i j he
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact valid i j h (sub_eq_zero.mpr he.symm)
  · exact valid j i h (sub_eq_zero.mpr he)

private def fourBounds : Fin 4 → Fin 4 → Bounds :=
  ![![(0, 0), (0, 0), millidegrees 29990 30010, millidegrees 34990 35010],
    ![(0, 0), (0, 0), millidegrees 149990 150010, millidegrees 144990 145010],
    ![millidegrees 29990 30010, millidegrees 149990 150010, (0, 0), millidegrees 89990 90010],
    ![millidegrees 34990 35010, millidegrees 144990 145010, millidegrees 89990 90010, (0, 0)]]

private def fourOrder : Fin 4 → Fin 3 → Fin 3 :=
  ![![0, 1, 2], ![0, 2, 1], ![0, 2, 1], ![0, 2, 1]]

private def fourFloors : Fin 4 → Fin 3 → ℤ :=
  ![![0, 0, 3], ![3, 0, 0], ![1, 1, 1], ![1, 1, 1]]

set_option maxHeartbeats 1600000 in
private lemma fourOrdered (i j : Fin 4) (h : i < j) :
    fourCenters j - fourCenters i ≠ 0 ∧ Encloses (fourBounds i j) (bearing fourCenters i j) := by
  have tan30 : 0.5773463 ≤ Real.tan (deg 30) ∧ Real.tan (deg 30) ≤ 0.5773543 := by
    check_tan 0.523598776
  have tan35 : 0.7002035 ≤ Real.tan (deg 35) ∧ Real.tan (deg 35) ≤ 0.7002115 := by
    check_tan 0.610865238
  fin_cases i <;> fin_cases j <;> try (exact False.elim ((of_decide_eq_false (by rfl)) h))
  · have hv : fourCenters 1 - fourCenters 0 = (2 : ℂ) := by
      apply Complex.ext <;> norm_num [fourCenters]
    refine ⟨fun hz => (show (2 : ℂ) ≠ 0 by norm_num) (hv.symm.trans hz), ?_⟩
    rw [bearing, upwardRay, if_pos h]
    change Encloses (fourBounds 0 1) (Complex.arg (fourCenters 1 - fourCenters 0) / Real.pi)
    rw [hv]
    norm_num [fourBounds, Encloses]
  · have hy : 0 < (fourCenters 2 - fourCenters 0).im := by norm_num [fourCenters]; all_goals linarith only [tan30.1, tan30.2, tan35.1, tan35.2]
    have lower : 1.7313449 ≤ Real.tan (deg (90 - (30010 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (30010 : ℝ) / 1000)) ≤ 1.7313609 := by check_tan 1.047023018
    have upper : 1.7327412 ≤ Real.tan (deg (90 - (29990 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (29990 : ℝ) / 1000)) ≤ 1.7327572 := by check_tan 1.047372084
    refine ⟨fun hz => hy.ne' (congrArg Complex.im hz), ?_⟩
    rw [bearing, upwardRay, if_pos h]
    exact millidegrees_mem hy 29990 30010 (by decide) (by decide) (by decide)
      (lower.2.trans ((le_div_iff₀ hy).mpr (by norm_num [fourCenters]; all_goals linarith only [tan30.1, tan30.2, tan35.1, tan35.2])))
      (((div_le_iff₀ hy).mpr (by norm_num [fourCenters]; all_goals linarith only [tan30.1, tan30.2, tan35.1, tan35.2])).trans upper.1)
  · have hy : 0 < (fourCenters 3 - fourCenters 0).im := by norm_num [fourCenters]; all_goals linarith only [tan30.1, tan30.2, tan35.1, tan35.2]
    have lower : 1.4276096 ≤ Real.tan (deg (90 - (35010 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (35010 : ℝ) / 1000)) ≤ 1.4276256 := by check_tan 0.959756556
    have upper : 1.4286707 ≤ Real.tan (deg (90 - (34990 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (34990 : ℝ) / 1000)) ≤ 1.4286867 := by check_tan 0.960105622
    refine ⟨fun hz => hy.ne' (congrArg Complex.im hz), ?_⟩
    rw [bearing, upwardRay, if_pos h]
    exact millidegrees_mem hy 34990 35010 (by decide) (by decide) (by decide)
      (lower.2.trans ((le_div_iff₀ hy).mpr (by norm_num [fourCenters]; all_goals linarith only [tan30.1, tan30.2, tan35.1, tan35.2])))
      (((div_le_iff₀ hy).mpr (by norm_num [fourCenters]; all_goals linarith only [tan30.1, tan30.2, tan35.1, tan35.2])).trans upper.1)
  · have hy : 0 < (fourCenters 2 - fourCenters 1).im := by norm_num [fourCenters]; all_goals linarith only [tan30.1, tan30.2, tan35.1, tan35.2]
    have lower : (-1.7327572) ≤ Real.tan (deg (90 - (150010 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (150010 : ℝ) / 1000)) ≤ (-1.7327412) := by check_tan (-1.047372084)
    have upper : (-1.7313609) ≤ Real.tan (deg (90 - (149990 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (149990 : ℝ) / 1000)) ≤ (-1.7313449) := by check_tan (-1.047023018)
    refine ⟨fun hz => hy.ne' (congrArg Complex.im hz), ?_⟩
    rw [bearing, upwardRay, if_pos h]
    exact millidegrees_mem hy 149990 150010 (by decide) (by decide) (by decide)
      (lower.2.trans ((le_div_iff₀ hy).mpr (by norm_num [fourCenters]; all_goals linarith only [tan30.1, tan30.2, tan35.1, tan35.2])))
      (((div_le_iff₀ hy).mpr (by norm_num [fourCenters]; all_goals linarith only [tan30.1, tan30.2, tan35.1, tan35.2])).trans upper.1)
  · have hy : 0 < (fourCenters 3 - fourCenters 1).im := by norm_num [fourCenters]; all_goals linarith only [tan30.1, tan30.2, tan35.1, tan35.2]
    have lower : (-1.4286867) ≤ Real.tan (deg (90 - (145010 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (145010 : ℝ) / 1000)) ≤ (-1.4286707) := by check_tan (-0.960105622)
    have upper : (-1.4276256) ≤ Real.tan (deg (90 - (144990 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (144990 : ℝ) / 1000)) ≤ (-1.4276096) := by check_tan (-0.959756556)
    refine ⟨fun hz => hy.ne' (congrArg Complex.im hz), ?_⟩
    rw [bearing, upwardRay, if_pos h]
    exact millidegrees_mem hy 144990 145010 (by decide) (by decide) (by decide)
      (lower.2.trans ((le_div_iff₀ hy).mpr (by norm_num [fourCenters]; all_goals linarith only [tan30.1, tan30.2, tan35.1, tan35.2])))
      (((div_le_iff₀ hy).mpr (by norm_num [fourCenters]; all_goals linarith only [tan30.1, tan30.2, tan35.1, tan35.2])).trans upper.1)
  · have hy : 0 < (fourCenters 3 - fourCenters 2).im := by norm_num [fourCenters]; all_goals linarith only [tan30.1, tan30.2, tan35.1, tan35.2]
    have lower : (-0.0001825) ≤ Real.tan (deg (90 - (90010 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (90010 : ℝ) / 1000)) ≤ (-0.0001665) := by check_tan (-0.000174533)
    have upper : 0.0001665 ≤ Real.tan (deg (90 - (89990 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (89990 : ℝ) / 1000)) ≤ 0.0001825 := by check_tan 0.000174533
    refine ⟨fun hz => hy.ne' (congrArg Complex.im hz), ?_⟩
    rw [bearing, upwardRay, if_pos h]
    exact millidegrees_mem hy 89990 90010 (by decide) (by decide) (by decide)
      (lower.2.trans ((le_div_iff₀ hy).mpr (by norm_num [fourCenters]; all_goals linarith only [tan30.1, tan30.2, tan35.1, tan35.2])))
      (((div_le_iff₀ hy).mpr (by norm_num [fourCenters]; all_goals linarith only [tan30.1, tan30.2, tan35.1, tan35.2])).trans upper.1)

private noncomputable def fourCertificate : Certificate 3 where
  points := fourCenters
  distinct := distinctOfOrderedRays fourCenters (fun i j h => (fourOrdered i j h).1)
  bounds := fourBounds
  unit := by decide +kernel
  bearing_mem := checkUnordered (by decide +kernel) (fun i j h => (fourOrdered i j h).2)
  order := fourOrder
  order_bijective := by decide
  sorted := by decide +kernel


private def fiveBounds : Fin 5 → Fin 5 → Bounds :=
  ![![(0, 0), (0, 0), millidegrees 24990 25010, millidegrees 25370 25390, millidegrees 25920 25940],
    ![(0, 0), (0, 0), millidegrees 154990 155010, millidegrees 154430 154450, millidegrees 154060 154080],
    ![millidegrees 24990 25010, millidegrees 154990 155010, (0, 0), millidegrees 67990 68010, millidegrees 89990 90010],
    ![millidegrees 25370 25390, millidegrees 154430 154450, millidegrees 67990 68010, (0, 0), millidegrees 111990 112010],
    ![millidegrees 25920 25940, millidegrees 154060 154080, millidegrees 89990 90010, millidegrees 111990 112010, (0, 0)]]

private def fiveOrder : Fin 5 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![0, 3, 2, 1], ![0, 2, 3, 1], ![0, 2, 3, 1], ![0, 2, 3, 1]]

private def fiveFloors : Fin 5 → Fin 4 → ℤ :=
  ![![0, 0, 0, 4], ![4, 0, 0, 0], ![1, 0, 1, 1], ![1, 1, 1, 1], ![1, 0, 1, 1]]

set_option maxHeartbeats 1600000 in
private lemma fiveOrdered (i j : Fin 5) (h : i < j) :
    fiveCenters j - fiveCenters i ≠ 0 ∧ Encloses (fiveBounds i j) (bearing fiveCenters i j) := by
  have tan22 : 0.4040222 ≤ Real.tan (deg 22) ∧ Real.tan (deg 22) ≤ 0.4040302 := by
    check_tan 0.383972435
  have tan25 : 0.4663037 ≤ Real.tan (deg 25) ∧ Real.tan (deg 25) ≤ 0.4663117 := by
    check_tan 0.436332313
  fin_cases i <;> fin_cases j <;> try (exact False.elim ((of_decide_eq_false (by rfl)) h))
  · have hv : fiveCenters 1 - fiveCenters 0 = (2 : ℂ) := by
      apply Complex.ext <;> norm_num [fiveCenters]
    refine ⟨fun hz => (show (2 : ℂ) ≠ 0 by norm_num) (hv.symm.trans hz), ?_⟩
    rw [bearing, upwardRay, if_pos h]
    change Encloses (fiveBounds 0 1) (Complex.arg (fiveCenters 1 - fiveCenters 0) / Real.pi)
    rw [hv]
    norm_num [fiveBounds, Encloses]
  · have hy : 0 < (fiveCenters 2 - fiveCenters 0).im := by norm_num [fiveCenters, cot68]; all_goals linarith only [tan22.1, tan22.2, tan25.1, tan25.2]
    have lower : 2.1435221 ≤ Real.tan (deg (90 - (25010 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (25010 : ℝ) / 1000)) ≤ 2.1435381 := by check_tan 1.134289481
    have upper : 2.1454765 ≤ Real.tan (deg (90 - (24990 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (24990 : ℝ) / 1000)) ≤ 2.1454925 := by check_tan 1.134638547
    refine ⟨fun hz => hy.ne' (congrArg Complex.im hz), ?_⟩
    rw [bearing, upwardRay, if_pos h]
    exact millidegrees_mem hy 24990 25010 (by decide) (by decide) (by decide)
      (lower.2.trans ((le_div_iff₀ hy).mpr (by norm_num [fiveCenters, cot68]; all_goals linarith only [tan22.1, tan22.2, tan25.1, tan25.2])))
      (((div_le_iff₀ hy).mpr (by norm_num [fiveCenters, cot68]; all_goals linarith only [tan22.1, tan22.2, tan25.1, tan25.2])).trans upper.1)
  · have hy : 0 < (fiveCenters 3 - fiveCenters 0).im := by norm_num [fiveCenters, cot68]; all_goals linarith only [tan22.1, tan22.2, tan25.1, tan25.2]
    have lower : 2.1069361 ≤ Real.tan (deg (90 - (25390 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (25390 : ℝ) / 1000)) ≤ 2.1069521 := by check_tan 1.127657230
    have upper : 2.1088361 ≤ Real.tan (deg (90 - (25370 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (25370 : ℝ) / 1000)) ≤ 2.1088521 := by check_tan 1.128006296
    refine ⟨fun hz => hy.ne' (congrArg Complex.im hz), ?_⟩
    rw [bearing, upwardRay, if_pos h]
    exact millidegrees_mem hy 25370 25390 (by decide) (by decide) (by decide)
      (lower.2.trans ((le_div_iff₀ hy).mpr (by norm_num [fiveCenters, cot68]; all_goals linarith only [tan22.1, tan22.2, tan25.1, tan25.2])))
      (((div_le_iff₀ hy).mpr (by norm_num [fiveCenters, cot68]; all_goals linarith only [tan22.1, tan22.2, tan25.1, tan25.2])).trans upper.1)
  · have hy : 0 < (fiveCenters 4 - fiveCenters 0).im := by norm_num [fiveCenters, cot68]; all_goals linarith only [tan22.1, tan22.2, tan25.1, tan25.2]
    have lower : 2.0557569 ≤ Real.tan (deg (90 - (25940 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (25940 : ℝ) / 1000)) ≤ 2.0557729 := by check_tan 1.118057919
    have upper : 2.0575825 ≤ Real.tan (deg (90 - (25920 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (25920 : ℝ) / 1000)) ≤ 2.0575985 := by check_tan 1.118406985
    refine ⟨fun hz => hy.ne' (congrArg Complex.im hz), ?_⟩
    rw [bearing, upwardRay, if_pos h]
    exact millidegrees_mem hy 25920 25940 (by decide) (by decide) (by decide)
      (lower.2.trans ((le_div_iff₀ hy).mpr (by norm_num [fiveCenters, cot68]; all_goals linarith only [tan22.1, tan22.2, tan25.1, tan25.2])))
      (((div_le_iff₀ hy).mpr (by norm_num [fiveCenters, cot68]; all_goals linarith only [tan22.1, tan22.2, tan25.1, tan25.2])).trans upper.1)
  · have hy : 0 < (fiveCenters 2 - fiveCenters 1).im := by norm_num [fiveCenters, cot68]; all_goals linarith only [tan22.1, tan22.2, tan25.1, tan25.2]
    have lower : (-2.1454925) ≤ Real.tan (deg (90 - (155010 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (155010 : ℝ) / 1000)) ≤ (-2.1454765) := by check_tan (-1.134638547)
    have upper : (-2.1435381) ≤ Real.tan (deg (90 - (154990 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (154990 : ℝ) / 1000)) ≤ (-2.1435221) := by check_tan (-1.134289481)
    refine ⟨fun hz => hy.ne' (congrArg Complex.im hz), ?_⟩
    rw [bearing, upwardRay, if_pos h]
    exact millidegrees_mem hy 154990 155010 (by decide) (by decide) (by decide)
      (lower.2.trans ((le_div_iff₀ hy).mpr (by norm_num [fiveCenters, cot68]; all_goals linarith only [tan22.1, tan22.2, tan25.1, tan25.2])))
      (((div_le_iff₀ hy).mpr (by norm_num [fiveCenters, cot68]; all_goals linarith only [tan22.1, tan22.2, tan25.1, tan25.2])).trans upper.1)
  · have hy : 0 < (fiveCenters 3 - fiveCenters 1).im := by norm_num [fiveCenters, cot68]; all_goals linarith only [tan22.1, tan22.2, tan25.1, tan25.2]
    have lower : (-2.0918517) ≤ Real.tan (deg (90 - (154450 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (154450 : ℝ) / 1000)) ≤ (-2.0918357) := by check_tan (-1.124864703)
    have upper : (-2.0899766) ≤ Real.tan (deg (90 - (154430 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (154430 : ℝ) / 1000)) ≤ (-2.0899606) := by check_tan (-1.124515637)
    refine ⟨fun hz => hy.ne' (congrArg Complex.im hz), ?_⟩
    rw [bearing, upwardRay, if_pos h]
    exact millidegrees_mem hy 154430 154450 (by decide) (by decide) (by decide)
      (lower.2.trans ((le_div_iff₀ hy).mpr (by norm_num [fiveCenters, cot68]; all_goals linarith only [tan22.1, tan22.2, tan25.1, tan25.2])))
      (((div_le_iff₀ hy).mpr (by norm_num [fiveCenters, cot68]; all_goals linarith only [tan22.1, tan22.2, tan25.1, tan25.2])).trans upper.1)
  · have hy : 0 < (fiveCenters 4 - fiveCenters 1).im := by norm_num [fiveCenters, cot68]; all_goals linarith only [tan22.1, tan22.2, tan25.1, tan25.2]
    have lower : (-2.0575985) ≤ Real.tan (deg (90 - (154080 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (154080 : ℝ) / 1000)) ≤ (-2.0575825) := by check_tan (-1.118406985)
    have upper : (-2.0557729) ≤ Real.tan (deg (90 - (154060 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (154060 : ℝ) / 1000)) ≤ (-2.0557569) := by check_tan (-1.118057919)
    refine ⟨fun hz => hy.ne' (congrArg Complex.im hz), ?_⟩
    rw [bearing, upwardRay, if_pos h]
    exact millidegrees_mem hy 154060 154080 (by decide) (by decide) (by decide)
      (lower.2.trans ((le_div_iff₀ hy).mpr (by norm_num [fiveCenters, cot68]; all_goals linarith only [tan22.1, tan22.2, tan25.1, tan25.2])))
      (((div_le_iff₀ hy).mpr (by norm_num [fiveCenters, cot68]; all_goals linarith only [tan22.1, tan22.2, tan25.1, tan25.2])).trans upper.1)
  · have hy : 0 < (fiveCenters 3 - fiveCenters 2).im := by norm_num [fiveCenters]
    have lower : 0.4038152 ≤ Real.tan (deg (90 - (68010 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (68010 : ℝ) / 1000)) ≤ 0.4038312 := by check_tan 0.383797903
    have upper : 0.4042213 ≤ Real.tan (deg (90 - (67990 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (67990 : ℝ) / 1000)) ≤ 0.4042373 := by check_tan 0.384146968
    refine ⟨fun hz => hy.ne' (congrArg Complex.im hz), ?_⟩
    rw [bearing, upwardRay, if_pos h]
    exact millidegrees_mem hy 67990 68010 (by decide) (by decide) (by decide)
      (lower.2.trans ((le_div_iff₀ hy).mpr (by norm_num [fiveCenters, cot68]; all_goals linarith only [tan22.1, tan22.2, tan25.1, tan25.2])))
      (((div_le_iff₀ hy).mpr (by norm_num [fiveCenters, cot68]; all_goals linarith only [tan22.1, tan22.2, tan25.1, tan25.2])).trans upper.1)
  · have hy : 0 < (fiveCenters 4 - fiveCenters 2).im := by norm_num [fiveCenters]
    have lower : (-0.0001825) ≤ Real.tan (deg (90 - (90010 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (90010 : ℝ) / 1000)) ≤ (-0.0001665) := by check_tan (-0.000174533)
    have upper : 0.0001665 ≤ Real.tan (deg (90 - (89990 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (89990 : ℝ) / 1000)) ≤ 0.0001825 := by check_tan 0.000174533
    refine ⟨fun hz => hy.ne' (congrArg Complex.im hz), ?_⟩
    rw [bearing, upwardRay, if_pos h]
    exact millidegrees_mem hy 89990 90010 (by decide) (by decide) (by decide)
      (lower.2.trans ((le_div_iff₀ hy).mpr (by norm_num [fiveCenters])))
      (((div_le_iff₀ hy).mpr (by norm_num [fiveCenters])).trans upper.1)
  · have hy : 0 < (fiveCenters 4 - fiveCenters 3).im := by norm_num [fiveCenters]
    have lower : (-0.4042373) ≤ Real.tan (deg (90 - (112010 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (112010 : ℝ) / 1000)) ≤ (-0.4042213) := by check_tan (-0.384146968)
    have upper : (-0.4038312) ≤ Real.tan (deg (90 - (111990 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (111990 : ℝ) / 1000)) ≤ (-0.4038152) := by check_tan (-0.383797903)
    refine ⟨fun hz => hy.ne' (congrArg Complex.im hz), ?_⟩
    rw [bearing, upwardRay, if_pos h]
    exact millidegrees_mem hy 111990 112010 (by decide) (by decide) (by decide)
      (lower.2.trans ((le_div_iff₀ hy).mpr (by norm_num [fiveCenters, cot68]; all_goals linarith only [tan22.1, tan22.2, tan25.1, tan25.2])))
      (((div_le_iff₀ hy).mpr (by norm_num [fiveCenters, cot68]; all_goals linarith only [tan22.1, tan22.2, tan25.1, tan25.2])).trans upper.1)

private noncomputable def fiveCertificate : Certificate 4 where
  points := fiveCenters
  distinct := distinctOfOrderedRays fiveCenters (fun i j h => (fiveOrdered i j h).1)
  bounds := fiveBounds
  unit := by decide +kernel
  bearing_mem := checkUnordered (by decide +kernel) (fun i j h => (fiveOrdered i j h).2)
  order := fiveOrder
  order_bijective := by decide
  sorted := by decide +kernel


private def sixBounds : Fin 6 → Fin 6 → Bounds :=
  ![![(0, 0), (0, 0), millidegrees 19990 20010, millidegrees 20050 20070, millidegrees 20330 20350, millidegrees 20400 20420],
    ![(0, 0), (0, 0), millidegrees 159990 160010, millidegrees 159950 159970, millidegrees 159460 159480, millidegrees 159420 159440],
    ![millidegrees 19990 20010, millidegrees 159990 160010, (0, 0), millidegrees 119990 120010, millidegrees 59990 60010, millidegrees 65590 65610],
    ![millidegrees 20050 20070, millidegrees 159950 159970, millidegrees 119990 120010, (0, 0), millidegrees 53680 53700, millidegrees 59990 60010],
    ![millidegrees 20330 20350, millidegrees 159460 159480, millidegrees 59990 60010, millidegrees 53680 53700, (0, 0), millidegrees 119990 120010],
    ![millidegrees 20400 20420, millidegrees 159420 159440, millidegrees 65590 65610, millidegrees 59990 60010, millidegrees 119990 120010, (0, 0)]]

private def sixOrder : Fin 6 → Fin 5 → Fin 5 :=
  ![![0, 1, 2, 3, 4], ![0, 4, 3, 2, 1], ![0, 3, 4, 2, 1], ![0, 3, 4, 2, 1], ![0, 3, 2, 4, 1], ![0, 3, 2, 4, 1]]

private def sixFloors : Fin 6 → Fin 5 → ℤ :=
  ![![0, 0, 0, 0, 5], ![5, 0, 0, 0, 0], ![1, 0, 1, 1, 1], ![1, 0, 1, 1, 1], ![1, 0, 1, 1, 1], ![1, 0, 1, 1, 1]]

set_option maxHeartbeats 1600000 in
private lemma sixOrdered (i j : Fin 6) (h : i < j) :
    sixCenters j - sixCenters i ≠ 0 ∧ Encloses (sixBounds i j) (bearing sixCenters i j) := by
  have tan20 : 0.3639662 ≤ Real.tan (deg 20) ∧ Real.tan (deg 20) ≤ 0.3639742 := by
    check_tan 0.349065850
  fin_cases i <;> fin_cases j <;> try (exact False.elim ((of_decide_eq_false (by rfl)) h))
  · have hv : sixCenters 1 - sixCenters 0 = (2 : ℂ) := by
      apply Complex.ext <;> norm_num [sixCenters]
    refine ⟨fun hz => (show (2 : ℂ) ≠ 0 by norm_num) (hv.symm.trans hz), ?_⟩
    rw [bearing, upwardRay, if_pos h]
    change Encloses (sixBounds 0 1) (Complex.arg (sixCenters 1 - sixCenters 0) / Real.pi)
    rw [hv]
    norm_num [sixBounds, Encloses]
  · have hy : 0 < (sixCenters 2 - sixCenters 0).im := by norm_num [sixCenters]; all_goals linarith only [tan20.1, tan20.2, sqrt3_mem.1, sqrt3_mem.2]
    have lower : 2.7459781 ≤ Real.tan (deg (90 - (20010 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (20010 : ℝ) / 1000)) ≤ 2.7459941 := by check_tan 1.221555943
    have upper : 2.7489622 ≤ Real.tan (deg (90 - (19990 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (19990 : ℝ) / 1000)) ≤ 2.7489782 := by check_tan 1.221905009
    refine ⟨fun hz => hy.ne' (congrArg Complex.im hz), ?_⟩
    rw [bearing, upwardRay, if_pos h]
    exact millidegrees_mem hy 19990 20010 (by decide) (by decide) (by decide)
      (lower.2.trans ((le_div_iff₀ hy).mpr (by norm_num [sixCenters]; all_goals linarith only [tan20.1, tan20.2, sqrt3_mem.1, sqrt3_mem.2])))
      (((div_le_iff₀ hy).mpr (by norm_num [sixCenters]; all_goals linarith only [tan20.1, tan20.2, sqrt3_mem.1, sqrt3_mem.2])).trans upper.1)
  · have hy : 0 < (sixCenters 3 - sixCenters 0).im := by norm_num [sixCenters]; all_goals linarith only [tan20.1, tan20.2, sqrt3_mem.1, sqrt3_mem.2]
    have lower : 2.7370602 ≤ Real.tan (deg (90 - (20070 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (20070 : ℝ) / 1000)) ≤ 2.7370762 := by check_tan 1.220508746
    have upper : 2.7400272 ≤ Real.tan (deg (90 - (20050 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (20050 : ℝ) / 1000)) ≤ 2.7400432 := by check_tan 1.220857812
    refine ⟨fun hz => hy.ne' (congrArg Complex.im hz), ?_⟩
    rw [bearing, upwardRay, if_pos h]
    exact millidegrees_mem hy 20050 20070 (by decide) (by decide) (by decide)
      (lower.2.trans ((le_div_iff₀ hy).mpr (by norm_num [sixCenters]; all_goals linarith only [tan20.1, tan20.2, sqrt3_mem.1, sqrt3_mem.2])))
      (((div_le_iff₀ hy).mpr (by norm_num [sixCenters]; all_goals linarith only [tan20.1, tan20.2, sqrt3_mem.1, sqrt3_mem.2])).trans upper.1)
  · have hy : 0 < (sixCenters 4 - sixCenters 0).im := by norm_num [sixCenters]; all_goals linarith only [tan20.1, tan20.2, sqrt3_mem.1, sqrt3_mem.2]
    have lower : 2.6961101 ≤ Real.tan (deg (90 - (20350 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (20350 : ℝ) / 1000)) ≤ 2.6961261 := by check_tan 1.215621824
    have upper : 2.6989993 ≤ Real.tan (deg (90 - (20330 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (20330 : ℝ) / 1000)) ≤ 2.6990153 := by check_tan 1.215970890
    refine ⟨fun hz => hy.ne' (congrArg Complex.im hz), ?_⟩
    rw [bearing, upwardRay, if_pos h]
    exact millidegrees_mem hy 20330 20350 (by decide) (by decide) (by decide)
      (lower.2.trans ((le_div_iff₀ hy).mpr (by norm_num [sixCenters]; all_goals linarith only [tan20.1, tan20.2, sqrt3_mem.1, sqrt3_mem.2])))
      (((div_le_iff₀ hy).mpr (by norm_num [sixCenters]; all_goals linarith only [tan20.1, tan20.2, sqrt3_mem.1, sqrt3_mem.2])).trans upper.1)
  · have hy : 0 < (sixCenters 5 - sixCenters 0).im := by norm_num [sixCenters]; all_goals linarith only [tan20.1, tan20.2, sqrt3_mem.1, sqrt3_mem.2]
    have lower : 2.6860407 ≤ Real.tan (deg (90 - (20420 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (20420 : ℝ) / 1000)) ≤ 2.6860567 := by check_tan 1.214400094
    have upper : 2.6889110 ≤ Real.tan (deg (90 - (20400 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (20400 : ℝ) / 1000)) ≤ 2.6889270 := by check_tan 1.214749159
    refine ⟨fun hz => hy.ne' (congrArg Complex.im hz), ?_⟩
    rw [bearing, upwardRay, if_pos h]
    exact millidegrees_mem hy 20400 20420 (by decide) (by decide) (by decide)
      (lower.2.trans ((le_div_iff₀ hy).mpr (by norm_num [sixCenters]; all_goals linarith only [tan20.1, tan20.2, sqrt3_mem.1, sqrt3_mem.2])))
      (((div_le_iff₀ hy).mpr (by norm_num [sixCenters]; all_goals linarith only [tan20.1, tan20.2, sqrt3_mem.1, sqrt3_mem.2])).trans upper.1)
  · have hy : 0 < (sixCenters 2 - sixCenters 1).im := by norm_num [sixCenters]; all_goals linarith only [tan20.1, tan20.2, sqrt3_mem.1, sqrt3_mem.2]
    have lower : (-2.7489782) ≤ Real.tan (deg (90 - (160010 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (160010 : ℝ) / 1000)) ≤ (-2.7489622) := by check_tan (-1.221905009)
    have upper : (-2.7459941) ≤ Real.tan (deg (90 - (159990 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (159990 : ℝ) / 1000)) ≤ (-2.7459781) := by check_tan (-1.221555943)
    refine ⟨fun hz => hy.ne' (congrArg Complex.im hz), ?_⟩
    rw [bearing, upwardRay, if_pos h]
    exact millidegrees_mem hy 159990 160010 (by decide) (by decide) (by decide)
      (lower.2.trans ((le_div_iff₀ hy).mpr (by norm_num [sixCenters]; all_goals linarith only [tan20.1, tan20.2, sqrt3_mem.1, sqrt3_mem.2])))
      (((div_le_iff₀ hy).mpr (by norm_num [sixCenters]; all_goals linarith only [tan20.1, tan20.2, sqrt3_mem.1, sqrt3_mem.2])).trans upper.1)
  · have hy : 0 < (sixCenters 3 - sixCenters 1).im := by norm_num [sixCenters]; all_goals linarith only [tan20.1, tan20.2, sqrt3_mem.1, sqrt3_mem.2]
    have lower : (-2.7430158) ≤ Real.tan (deg (90 - (159970 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (159970 : ℝ) / 1000)) ≤ (-2.7429998) := by check_tan (-1.221206878)
    have upper : (-2.7400432) ≤ Real.tan (deg (90 - (159950 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (159950 : ℝ) / 1000)) ≤ (-2.7400272) := by check_tan (-1.220857812)
    refine ⟨fun hz => hy.ne' (congrArg Complex.im hz), ?_⟩
    rw [bearing, upwardRay, if_pos h]
    exact millidegrees_mem hy 159950 159970 (by decide) (by decide) (by decide)
      (lower.2.trans ((le_div_iff₀ hy).mpr (by norm_num [sixCenters]; all_goals linarith only [tan20.1, tan20.2, sqrt3_mem.1, sqrt3_mem.2])))
      (((div_le_iff₀ hy).mpr (by norm_num [sixCenters]; all_goals linarith only [tan20.1, tan20.2, sqrt3_mem.1, sqrt3_mem.2])).trans upper.1)
  · have hy : 0 < (sixCenters 4 - sixCenters 1).im := by norm_num [sixCenters]; all_goals linarith only [tan20.1, tan20.2, sqrt3_mem.1, sqrt3_mem.2]
    have lower : (-2.6717860) ≤ Real.tan (deg (90 - (159480 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (159480 : ℝ) / 1000)) ≤ (-2.6717700) := by check_tan (-1.212654764)
    have upper : (-2.6689478) ≤ Real.tan (deg (90 - (159460 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (159460 : ℝ) / 1000)) ≤ (-2.6689318) := by check_tan (-1.212305698)
    refine ⟨fun hz => hy.ne' (congrArg Complex.im hz), ?_⟩
    rw [bearing, upwardRay, if_pos h]
    exact millidegrees_mem hy 159460 159480 (by decide) (by decide) (by decide)
      (lower.2.trans ((le_div_iff₀ hy).mpr (by norm_num [sixCenters]; all_goals linarith only [tan20.1, tan20.2, sqrt3_mem.1, sqrt3_mem.2])))
      (((div_le_iff₀ hy).mpr (by norm_num [sixCenters]; all_goals linarith only [tan20.1, tan20.2, sqrt3_mem.1, sqrt3_mem.2])).trans upper.1)
  · have hy : 0 < (sixCenters 5 - sixCenters 1).im := by norm_num [sixCenters]; all_goals linarith only [tan20.1, tan20.2, sqrt3_mem.1, sqrt3_mem.2]
    have lower : (-2.6661149) ≤ Real.tan (deg (90 - (159440 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (159440 : ℝ) / 1000)) ≤ (-2.6660989) := by check_tan (-1.211956633)
    have upper : (-2.6632873) ≤ Real.tan (deg (90 - (159420 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (159420 : ℝ) / 1000)) ≤ (-2.6632713) := by check_tan (-1.211607567)
    refine ⟨fun hz => hy.ne' (congrArg Complex.im hz), ?_⟩
    rw [bearing, upwardRay, if_pos h]
    exact millidegrees_mem hy 159420 159440 (by decide) (by decide) (by decide)
      (lower.2.trans ((le_div_iff₀ hy).mpr (by norm_num [sixCenters]; all_goals linarith only [tan20.1, tan20.2, sqrt3_mem.1, sqrt3_mem.2])))
      (((div_le_iff₀ hy).mpr (by norm_num [sixCenters]; all_goals linarith only [tan20.1, tan20.2, sqrt3_mem.1, sqrt3_mem.2])).trans upper.1)
  · have hy : 0 < (sixCenters 3 - sixCenters 2).im := by norm_num [sixCenters]
    have lower : (-0.5775910) ≤ Real.tan (deg (90 - (120010 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (120010 : ℝ) / 1000)) ≤ (-0.5775750) := by check_tan (-0.523773309)
    have upper : (-0.5771256) ≤ Real.tan (deg (90 - (119990 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (119990 : ℝ) / 1000)) ≤ (-0.5771096) := by check_tan (-0.523424243)
    refine ⟨fun hz => hy.ne' (congrArg Complex.im hz), ?_⟩
    rw [bearing, upwardRay, if_pos h]
    exact millidegrees_mem hy 119990 120010 (by decide) (by decide) (by decide)
      (lower.2.trans ((le_div_iff₀ hy).mpr (by norm_num [sixCenters]; all_goals linarith only [tan20.1, tan20.2, sqrt3_mem.1, sqrt3_mem.2])))
      (((div_le_iff₀ hy).mpr (by norm_num [sixCenters]; all_goals linarith only [tan20.1, tan20.2, sqrt3_mem.1, sqrt3_mem.2])).trans upper.1)
  · have hy : 0 < (sixCenters 4 - sixCenters 2).im := by norm_num [sixCenters]
    have lower : 0.5771096 ≤ Real.tan (deg (90 - (60010 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (60010 : ℝ) / 1000)) ≤ 0.5771256 := by check_tan 0.523424243
    have upper : 0.5775750 ≤ Real.tan (deg (90 - (59990 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (59990 : ℝ) / 1000)) ≤ 0.5775910 := by check_tan 0.523773309
    refine ⟨fun hz => hy.ne' (congrArg Complex.im hz), ?_⟩
    rw [bearing, upwardRay, if_pos h]
    exact millidegrees_mem hy 59990 60010 (by decide) (by decide) (by decide)
      (lower.2.trans ((le_div_iff₀ hy).mpr (by norm_num [sixCenters]; all_goals linarith only [tan20.1, tan20.2, sqrt3_mem.1, sqrt3_mem.2])))
      (((div_le_iff₀ hy).mpr (by norm_num [sixCenters]; all_goals linarith only [tan20.1, tan20.2, sqrt3_mem.1, sqrt3_mem.2])).trans upper.1)
  · have hy : 0 < (sixCenters 5 - sixCenters 2).im := by norm_num [sixCenters]
    have lower : 0.4534017 ≤ Real.tan (deg (90 - (65610 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (65610 : ℝ) / 1000)) ≤ 0.4534177 := by check_tan 0.425685805
    have upper : 0.4538226 ≤ Real.tan (deg (90 - (65590 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (65590 : ℝ) / 1000)) ≤ 0.4538386 := by check_tan 0.426034870
    refine ⟨fun hz => hy.ne' (congrArg Complex.im hz), ?_⟩
    rw [bearing, upwardRay, if_pos h]
    exact millidegrees_mem hy 65590 65610 (by decide) (by decide) (by decide)
      (lower.2.trans ((le_div_iff₀ hy).mpr (by norm_num [sixCenters]; all_goals linarith only [tan20.1, tan20.2, sqrt3_mem.1, sqrt3_mem.2])))
      (((div_le_iff₀ hy).mpr (by norm_num [sixCenters]; all_goals linarith only [tan20.1, tan20.2, sqrt3_mem.1, sqrt3_mem.2])).trans upper.1)
  · have hy : 0 < (sixCenters 4 - sixCenters 3).im := by norm_num [sixCenters]; all_goals linarith only [tan20.1, tan20.2, sqrt3_mem.1, sqrt3_mem.2]
    have lower : 0.7345650 ≤ Real.tan (deg (90 - (53700 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (53700 : ℝ) / 1000)) ≤ 0.7345810 := by check_tan 0.633554518
    have upper : 0.7351026 ≤ Real.tan (deg (90 - (53680 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (53680 : ℝ) / 1000)) ≤ 0.7351186 := by check_tan 0.633903584
    refine ⟨fun hz => hy.ne' (congrArg Complex.im hz), ?_⟩
    rw [bearing, upwardRay, if_pos h]
    exact millidegrees_mem hy 53680 53700 (by decide) (by decide) (by decide)
      (lower.2.trans ((le_div_iff₀ hy).mpr (by norm_num [sixCenters]; all_goals linarith only [tan20.1, tan20.2, sqrt3_mem.1, sqrt3_mem.2])))
      (((div_le_iff₀ hy).mpr (by norm_num [sixCenters]; all_goals linarith only [tan20.1, tan20.2, sqrt3_mem.1, sqrt3_mem.2])).trans upper.1)
  · have hy : 0 < (sixCenters 5 - sixCenters 3).im := by norm_num [sixCenters]; all_goals linarith only [tan20.1, tan20.2, sqrt3_mem.1, sqrt3_mem.2]
    have lower : 0.5771096 ≤ Real.tan (deg (90 - (60010 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (60010 : ℝ) / 1000)) ≤ 0.5771256 := by check_tan 0.523424243
    have upper : 0.5775750 ≤ Real.tan (deg (90 - (59990 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (59990 : ℝ) / 1000)) ≤ 0.5775910 := by check_tan 0.523773309
    refine ⟨fun hz => hy.ne' (congrArg Complex.im hz), ?_⟩
    rw [bearing, upwardRay, if_pos h]
    exact millidegrees_mem hy 59990 60010 (by decide) (by decide) (by decide)
      (lower.2.trans ((le_div_iff₀ hy).mpr (by norm_num [sixCenters]; all_goals linarith only [tan20.1, tan20.2, sqrt3_mem.1, sqrt3_mem.2])))
      (((div_le_iff₀ hy).mpr (by norm_num [sixCenters]; all_goals linarith only [tan20.1, tan20.2, sqrt3_mem.1, sqrt3_mem.2])).trans upper.1)
  · have hy : 0 < (sixCenters 5 - sixCenters 4).im := by norm_num [sixCenters]; all_goals linarith only [tan20.1, tan20.2, sqrt3_mem.1, sqrt3_mem.2]
    have lower : (-0.5775910) ≤ Real.tan (deg (90 - (120010 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (120010 : ℝ) / 1000)) ≤ (-0.5775750) := by check_tan (-0.523773309)
    have upper : (-0.5771256) ≤ Real.tan (deg (90 - (119990 : ℝ) / 1000)) ∧
        Real.tan (deg (90 - (119990 : ℝ) / 1000)) ≤ (-0.5771096) := by check_tan (-0.523424243)
    refine ⟨fun hz => hy.ne' (congrArg Complex.im hz), ?_⟩
    rw [bearing, upwardRay, if_pos h]
    exact millidegrees_mem hy 119990 120010 (by decide) (by decide) (by decide)
      (lower.2.trans ((le_div_iff₀ hy).mpr (by norm_num [sixCenters]; all_goals linarith only [tan20.1, tan20.2, sqrt3_mem.1, sqrt3_mem.2])))
      (((div_le_iff₀ hy).mpr (by norm_num [sixCenters]; all_goals linarith only [tan20.1, tan20.2, sqrt3_mem.1, sqrt3_mem.2])).trans upper.1)

private noncomputable def sixCertificate : Certificate 5 where
  points := sixCenters
  distinct := distinctOfOrderedRays sixCenters (fun i j h => (sixOrdered i j h).1)
  bounds := sixBounds
  unit := by decide +kernel
  bearing_mem := checkUnordered (by decide +kernel) (fun i j h => (sixOrdered i j h).2)
  order := sixOrder
  order_bijective := by decide
  sorted := by decide +kernel


/-- The existing ordinary-angle cap, checked with strict slack at every vertex. -/
def StrictCenterAngleCap {s : ℕ} (D : CenterGapData s) (t : ℝ) : Prop :=
  ∀ i j k : Fin s, i ≠ j → k ≠ j →
    EuclideanGeometry.angle (D.center i) (D.center j) (D.center k) < angleAt t

lemma StrictCenterAngleCap.angleCap {s : ℕ} {D : CenterGapData s} {t : ℝ}
    (h : StrictCenterAngleCap D t) : CenterAngleCap D t :=
  fun i j k hi hk => (h i j k hi hk).le

lemma StrictCenterAngleCap.not_collinear {s : ℕ} {D : CenterGapData s} {t : ℝ}
    (h : StrictCenterAngleCap D t) (ht : 0 < t) {i j k : Fin s}
    (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i) :
    ¬ Collinear ℝ ({D.center i, D.center j, D.center k} : Set ℂ) := by
  have hπ : angleAt t < Real.pi := by
    unfold angleAt
    calc
      _ < 1 * Real.pi := mul_lt_mul_of_pos_right
        (sub_lt_self _ (one_div_pos.mpr ht)) Real.pi_pos
      _ = _ := one_mul _
  intro hcol
  rcases hcol.wbtw_or_wbtw_or_wbtw with hb | hb | hb
  · exact ((h i j k hij hjk.symm).trans hπ).ne
      (Sbtw.angle₁₂₃_eq_pi ⟨hb, D.injective.ne hij.symm, D.injective.ne hjk⟩)
  · exact ((h j k i hjk hki.symm).trans hπ).ne
      (Sbtw.angle₁₂₃_eq_pi ⟨hb, D.injective.ne hjk.symm, D.injective.ne hki⟩)
  · exact ((h k i j hki hij.symm).trans hπ).ne
      (Sbtw.angle₁₂₃_eq_pi ⟨hb, D.injective.ne hki.symm, D.injective.ne hij⟩)

private lemma Certificate.weight {n : ℕ} (C : Certificate n) (t : ℚ) (ht : 0 ≤ t)
    (f : Fin (n + 1) → Fin n → ℤ)
    (check : ∀ i j, (f i j : ℚ) ≤ t * (gapBounds (C.row i) j).1 ∧
      t * (gapBounds (C.row i) j).2 < (f i j : ℚ) + 1) :
    centerWeight C.toData t = ∑ i, (2 : ℕ) ^ (∑ j, (f i j - 1).toNat) := by
  simp only [centerWeight, C.exponents t ht f check]

/-- The four-center instance of Lemma 4.1 c.2, at t = 15/4. -/
theorem four_counterexample :
    ∃ D : CenterGapData 4, D.center = fourCenters ∧ StrictCenterAngleCap D (15 / 4) ∧
      centerWeight D (15 / 4) = 10 ∧ 9 < centerWeight D (15 / 4) := by
  have hc := fourCertificate.strictCap (15 / 4) (by decide +kernel)
  have hw := fourCertificate.weight (15 / 4) (by norm_num) fourFloors (by decide +kernel)
  push_cast at hc hw
  have he : centerWeight fourCertificate.toData (15 / 4) = 10 := hw.trans (by decide)
  exact ⟨fourCertificate.toData, rfl, hc, he, he.symm ▸ (by decide : 9 < 10)⟩

/-- The five-center instance of Lemma 4.1 s.2, at t = 19/4. -/
theorem five_counterexample :
    ∃ D : CenterGapData 5, D.center = fiveCenters ∧ StrictCenterAngleCap D (19 / 4) ∧
      centerWeight D (19 / 4) = 19 ∧ 17 < centerWeight D (19 / 4) := by
  have hc := fiveCertificate.strictCap (19 / 4) (by decide +kernel)
  have hw := fiveCertificate.weight (19 / 4) (by norm_num) fiveFloors (by decide +kernel)
  push_cast at hc hw
  have he : centerWeight fiveCertificate.toData (19 / 4) = 19 := hw.trans (by decide)
  exact ⟨fiveCertificate.toData, rfl, hc, he, he.symm ▸ (by decide : 17 < 19)⟩

/-- The six-center instance of Lemma 4.1 s.2, at t = 23/4. -/
theorem six_counterexample :
    ∃ D : CenterGapData 6, D.center = sixCenters ∧ StrictCenterAngleCap D (23 / 4) ∧
      centerWeight D (23 / 4) = 36 ∧ 33 < centerWeight D (23 / 4) := by
  have hc := sixCertificate.strictCap (23 / 4) (by decide +kernel)
  have hw := sixCertificate.weight (23 / 4) (by norm_num) sixFloors (by decide +kernel)
  push_cast at hc hw
  have he : centerWeight sixCertificate.toData (23 / 4) = 36 := hw.trans (by decide)
  exact ⟨sixCertificate.toData, rfl, hc, he, he.symm ▸ (by decide : 33 < 36)⟩

def FixedWeightClaim (s : ℕ) (t : ℝ) (bound : ℕ) : Prop :=
  ∀ D : CenterGapData s, CenterAngleCap D t → centerWeight D t ≤ bound

private lemma fixedWeightClaim_false {s bound : ℕ} {t : ℝ}
    {D : CenterGapData s} (hcap : StrictCenterAngleCap D t) (hweight : bound < centerWeight D t) :
    ¬ FixedWeightClaim s t bound :=
  fun claim => hweight.not_ge (claim D hcap.angleCap)

/-- The three fixed-s weight bounds asserted by the published exponent sequences. -/
theorem not_fixed_weight_claims :
    (¬ FixedWeightClaim 4 (15 / 4) 9) ∧ (¬ FixedWeightClaim 5 (19 / 4) 17) ∧
      (¬ FixedWeightClaim 6 (23 / 4) 33) := by
  obtain ⟨_, _, h4, _, w4⟩ := four_counterexample
  obtain ⟨_, _, h5, _, w5⟩ := five_counterexample
  obtain ⟨_, _, h6, _, w6⟩ := six_counterexample
  exact ⟨fixedWeightClaim_false h4 w4, fixedWeightClaim_false h5 w5, fixedWeightClaim_false h6 w6⟩

/-- The fixed-s upper envelope in Lemma 4.1, s.2, restricted to the range
where all the exponents in the published sequence are nonnegative. -/
def Lemma41FixedS2 : Prop :=
  ∀ (s m : ℕ) (D : CenterGapData s) (t : ℝ), 5 ≤ s → s ≤ m + 1 →
    (m : ℝ) + 1 / 2 ≤ t → t < (m : ℝ) + 1 → CenterAngleCap D t →
    centerWeight D t ≤ 2 ^ m + 2 ^ (m + 1 - s)

theorem not_lemma41_fixedS2 : ¬ Lemma41FixedS2 := by
  intro h
  obtain ⟨D, _, hcap, _, hweight⟩ := five_counterexample
  have hb := h 5 4 D (19 / 4) (by decide) (by decide) (by norm_num) (by norm_num) hcap.angleCap
  exact hweight.not_ge hb

/-- The published dependency chain (print pp. 37–42).
Lemma 4.2 says “From Lemma 4.1 there follows”. The upper direction of
Theorem 4.1 uses that counting step together with Lemma 4.3 and the identity
α(N(α)) = α. The propositions for those steps are parameters here. A
derivation along this route needs the fixed-s step as a proved premise. -/
structure PublishedUpperDerivation (lemma42 lemma43 alphaIdentity theorem41Upper : Prop) : Prop where
  fixedS2 : Lemma41FixedS2
  transfer : Lemma41FixedS2 → lemma42
  lower : lemma43
  identity : alphaIdentity
  finish : lemma42 → lemma43 → alphaIdentity → theorem41Upper

/-- This refutes the displayed derivation. A separate proof of the upper
bound would require its own counting argument. -/
theorem no_published_upper_derivation (lemma42 lemma43 alphaIdentity theorem41Upper : Prop) :
    ¬ PublishedUpperDerivation lemma42 lemma43 alphaIdentity theorem41Upper :=
  fun route => not_lemma41_fixedS2 route.fixedS2

end Erdos504.SendovStage1.Se95Correction
