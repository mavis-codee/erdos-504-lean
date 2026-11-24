/-
Lean development for the Phase-1b **G2 spike** on Erdős Problem #504: the
Sendov (1995) counting bound

    all angles of `S` strictly below `π (1 - 1/n)`  ⟹  `S.card ≤ 2^(n-1) + 2^(n-3)`

## Coverage of this file (read this before using any theorem below)

> **Correction (2026-11-24).**  The spike session was lost before this file was
> finished.  An earlier version of this header claimed three theorems; only
> **`angle_sum_interior`** was actually written and machine-checked.  The two
> remaining items below are **not present in this file** — they are listed as
> the exact next steps, not as results.  See `SENDOV-PHASE1B-REPORT.md`.

**Proved here (no `sorry`, no `admit`, no unproved hypotheses):**

* `angle_sum_interior` — the three angles subtended at a point strictly inside a
  triangle add up to `2 * π`.

**NOT present in this file (written or proved: nothing):**

* `exists_angle_ge_two_pi_div_three_of_interior` — would follow from
  `angle_sum_interior` plus a containing triangle: a point of a set in general
  position that is *not* a vertex of the convex hull is seen under an angle
  `≥ 2 * π / 3` from some pair of other points of the set.  **Not written.**
* `sendov_counting_bound_n3` — would be the `n = 3` instance of Sendov's
  counting bound: if every angle determined by `S` is strictly below `2 * π / 3`
  then `S.card ≤ 5 = 2 ^ (3 - 1) + 2 ^ (3 - 3)` (strictly stronger than the
  previously proved `strictCountingBound`, which gives `2 ^ 3 - 2 = 6` at
  `n = 3`).  It would follow from the previous item together with the already
  proved `hull_card_le` (a set in convex position has at most `2 * 3 - 1 = 5`
  vertices).  **Not written.**

**NOT covered here (explicitly unproved):**

* the general instance `S.card ≤ 2 ^ (n - 1) + 2 ^ (n - 3)` for `n ≥ 4`;
  the target statement `sendov_counting_bound_large` is therefore **not**
  proved by this file.  See `SENDOV-G2-SPIKE.md` §3 (route evaluation) and §5
  (STOP report) for the exact missing mathematical input.

* the other two Sendov ingredients (the `1 - 2/(2n-1)` counting bound and the
  extremal configuration) are out of scope for this spike and are **not**
  started here.

Reference for the geometry: the classical fact that a point inside a triangle
sees its three sides under angles summing to `2π`; together with Erdős–Szekeres
(1960), *On some extremum problems in elementary geometry*, Ann. Univ. Sci.
Budapest Sect. Math. 3–4 (1960/61), 53–62 (Lemma 6, Theorem 3), and Sendov
(1995), *Minimax of the angles in a plane configuration of points*, Acta Math.
Hungar. 69 (1995), 27–46.
-/
import Erdos504Formal.Erdos504StrictCounting

namespace Erdos504

open Real EuclideanGeometry

/-! ## Angles around a point strictly inside a triangle -/

/--
**Angles around an interior point.**  If `x` lies strictly inside the triangle
`a b c` (witnessed by strictly positive barycentric coordinates), then the three
angles subtended at `x` by the sides of the triangle add up to `2 * π`:

    `angle a x b + angle b x c + angle c x a = 2 * π`.

The proof follows the pattern of `Erdos504.angle_lt_angle_of_interior`: the ray
`b → x` meets the side `a c` in a point `d`, the angle at `x` is split by the
ray `x → d`, and the two angles at `x` that are supplementary to `angle a x b`
and `angle b x c` are used.
-/
theorem angle_sum_interior {a b c x : ℂ} {α β γ : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hsum : α + β + γ = 1)
    (hx : x = α • a + β • b + γ • c)
    (hnc : ¬ Collinear ℝ ({a, b, c} : Set ℂ)) :
    EuclideanGeometry.angle a x b + EuclideanGeometry.angle b x c
        + EuclideanGeometry.angle c x a = 2 * π := by
  have hβeq : β = 1 - α - γ := by linarith
  subst hβeq
  have hαγ : (0 : ℝ) < α + γ := by linarith
  have hαγne : α + γ ≠ 0 := ne_of_gt hαγ
  have hacne : a ≠ c := ne₁₃_of_not_collinear hnc
  have hαC : ((α : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hα)
  have hβC : (((1 - α - γ : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hβ)
  have hγC : ((γ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hγ)
  have hαγC : ((α : ℝ) : ℂ) + ((γ : ℝ) : ℂ) ≠ 0 := by
    have h := Complex.ofReal_ne_zero.mpr hαγne
    push_cast at h
    exact h
  -- `d` is the point where the ray `b → x` meets the side `a c`
  obtain ⟨d, hd_def⟩ : ∃ d : ℂ, d = (α / (α + γ) : ℝ) • a + (γ / (α + γ) : ℝ) • c :=
    ⟨_, rfl⟩
  have hwad : Wbtw ℝ a d c := by
    rw [← mem_segment_iff_wbtw]
    exact ⟨α / (α + γ), γ / (α + γ), by positivity, by positivity, by field_simp,
      hd_def.symm⟩
  have hbd : b ≠ d := by
    intro h
    exact hnc (by rw [h]; exact hwad.collinear)
  have hwbxd : Wbtw ℝ b x d := by
    rw [← mem_segment_iff_wbtw]
    refine ⟨1 - α - γ, α + γ, by linarith, by linarith, by ring, ?_⟩
    rw [hx, hd_def]; simp only [Complex.real_smul]; push_cast; field_simp; ring
  -- the four elementary difference identities
  have hdiff_da : d - a
      = ((γ : ℝ) : ℂ) * (c - a) / (((α : ℝ) : ℂ) + ((γ : ℝ) : ℂ)) := by
    rw [hd_def]; simp only [Complex.real_smul]; push_cast; field_simp; ring
  have hdiff_dc : d - c
      = ((α : ℝ) : ℂ) * (a - c) / (((α : ℝ) : ℂ) + ((γ : ℝ) : ℂ)) := by
    rw [hd_def]; simp only [Complex.real_smul]; push_cast; field_simp; ring
  have hdiff_xb : x - b = (((α : ℝ) : ℂ) + ((γ : ℝ) : ℂ)) * (d - b) := by
    rw [hx, hd_def]; simp only [Complex.real_smul]; push_cast; field_simp; ring
  have hdiff_xd : x - d = (((1 - α - γ : ℝ)) : ℂ) * (b - d) := by
    rw [hx, hd_def]; simp only [Complex.real_smul]; push_cast; field_simp; ring
  have hdane : d ≠ a := by
    rw [← sub_ne_zero, hdiff_da]
    exact div_ne_zero (mul_ne_zero hγC (sub_ne_zero.mpr hacne.symm)) hαγC
  have hdcne : d ≠ c := by
    rw [← sub_ne_zero, hdiff_dc]
    exact div_ne_zero (mul_ne_zero hαC (sub_ne_zero.mpr hacne)) hαγC
  have hxbne : x ≠ b := by
    rw [← sub_ne_zero, hdiff_xb]
    exact mul_ne_zero hαγC (sub_ne_zero.mpr (Ne.symm hbd))
  have hxdne : x ≠ d := by
    rw [← sub_ne_zero, hdiff_xd]
    exact mul_ne_zero hβC (sub_ne_zero.mpr hbd)
  have hsad : Sbtw ℝ a d c := ⟨hwad, hdane, hdcne⟩
  have hsbxd : Sbtw ℝ b x d := ⟨hwbxd, hxbne, hxdne⟩
  -- `b`, `x`, `d` are collinear with `x` in between: the angle `b x d` is straight
  have hpi : EuclideanGeometry.angle b x d = π := Sbtw.angle₁₂₃_eq_pi hsbxd
  -- the two angles at `x` that are supplementary to `angle a x b` and `angle b x c`
  have hsupp₁ : EuclideanGeometry.angle a x b + EuclideanGeometry.angle a x d = π :=
    EuclideanGeometry.angle_add_angle_eq_pi_of_angle_eq_pi a hpi
  have hsupp₂ : EuclideanGeometry.angle c x b + EuclideanGeometry.angle c x d = π :=
    EuclideanGeometry.angle_add_angle_eq_pi_of_angle_eq_pi c hpi
  -- the ray `x → d` splits the angle `a x c`
  have hsplit : EuclideanGeometry.angle a x d + EuclideanGeometry.angle d x c
      = EuclideanGeometry.angle a x c :=
    EuclideanGeometry.angle_add_angle_eq_of_sbtw hsad
  have hA : EuclideanGeometry.angle a x d = π - EuclideanGeometry.angle a x b := by
    linarith
  have hB : EuclideanGeometry.angle d x c = π - EuclideanGeometry.angle b x c := by
    have h2 : EuclideanGeometry.angle b x c + EuclideanGeometry.angle d x c = π := by
      have h3 := hsupp₂
      rw [EuclideanGeometry.angle_comm (c) (x) (b),
        EuclideanGeometry.angle_comm (c) (x) (d)] at h3
      exact h3
    linarith
  rw [hA, hB] at hsplit
  rw [EuclideanGeometry.angle_comm (c) (x) (a)]
  linarith

/-! ## Axiom audit

The only declaration of this file is complete.  Running the file prints its
transitive axiom dependencies; the line must report exactly the three standard
Lean foundations `propext`, `Classical.choice` and `Quot.sound` — in particular
no `sorryAx` and no `Lean.ofReduceBool` (i.e. no `native_decide`). -/

#print axioms angle_sum_interior

end Erdos504
