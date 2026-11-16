# Erdős Problem #504 — Lean 4 formalisation of the minimax angle

A complete, sorry-free Lean 4 formalisation of

> **Erdős Problem #504 (Blumenthal's problem).** What is the largest angle that
> every planar set of a prescribed number of points must determine?

in the form used by the Formal Conjectures statement of the problem:

```lean
theorem erdos_504 {n : ℕ} (hn : 3 ≤ n) :
    minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π
```

where

```lean
noncomputable def minimaxAngle (N : ℕ) : ℝ :=
  sSup {α : ℝ | α ∈ Set.Icc 0 π ∧
    ∀ S : Finset ℂ, S.card = N →
      ∃ x ∈ S, ∃ z ∈ S, ∃ y ∈ S, x ≠ z ∧ y ≠ z ∧ x ≠ y ∧
        α ≤ EuclideanGeometry.angle x z y}
```

i.e. `α_N` is the supremum of all angles that are guaranteed in every `N`-point
set of the plane. The value for `N = 2^n` is the Erdős–Szekeres (1960) value
`π (1 − 1/n)`.

## Contents

| File | Content |
| --- | --- |
| `Erdos504Formal/Erdos504.lean` | Republished unchanged from [`ToshiDad/erdos-504`](https://github.com/ToshiDad/erdos-504) @ `fd344a9b65ecaebca66b77497fea197cb895960e`: the Szekeres (1941) bounds and the Erdős–Szekeres (1960) theorem, sorry-free. See [ATTRIBUTION.md](./ATTRIBUTION.md). |
| `Erdos504Formal/Erdos504Minimax.lean` | New work: the `sSup` definition of the minimax angle, the auxiliary lemma `exists_distinct_angle_gt`, and the main theorem `erdos_504`. |

## Toolchain

* Lean `leanprover/lean4:v4.33.0` (pinned in `lean-toolchain`)
* Mathlib `v4.33.0`, commit `db584cd6d46c92f209a44c0f1c829460d327499d`
  (pinned in `lake-manifest.json`)

## Reproduce

```bash
# 1. install the pinned toolchain (elan)
elan toolchain install leanprover/lean4:v4.33.0

# 2. fetch the pinned dependencies and the Mathlib build cache
lake exe cache get

# 3. build the library (the two Lean files)
lake build

# 4. type-check the target theorem directly
lake env lean Erdos504Formal/Erdos504Minimax.lean
```

## Axiom audit

The library uses only the three standard Lean foundations. To check:

```bash
lake env lean Erdos504Formal/Erdos504Minimax.lean
```

with the following appended to the file (or in a scratch copy):

```lean
#print axioms Erdos504.erdos_504
#print axioms Erdos504.exists_distinct_angle_gt
#print axioms Erdos504.exists_angle_gt
#print axioms Erdos504.exists_config_angle_lt
#print axioms Erdos504.erdos_szekeres_1960
```

Expected output for every line:

```
'Erdos504.erdos_504' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`, no `admit`, no `native_decide`.

## Mathematical references

* G. Szekeres, *On an extremum problem in the plane*, Amer. J. Math. **63**
  (1941), 208–210.
* P. Erdős and G. Szekeres, *On some extremum problems in elementary geometry*,
  Ann. Univ. Sci. Budapest. Eötvös Sect. Math. **3** (1960/61), 53–62.
* B. Sendov, *Minimax of the angles in a plane configuration of points*, Acta
  Math. Hungar. **69** (1995), 27–46.
