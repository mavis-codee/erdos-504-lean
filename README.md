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
| `Erdos504Formal/Erdos504Endpoint.lean` | New work: the endpoint `α_{2^n − 1}`. The sharp (`ε`-relaxed) side and the reduction of the endpoint to one counting lemma are proved; the endpoint itself is proved **conditional** on `StrictCountingBound`. | |
| `Erdos504Formal/AuditBridge.lean` | New work: the statement-correspondence bridge to the Formal Conjectures statement of the problem — `minimaxAngle_eq_fc` (the submitted definition is definitionally the Formal Conjectures one, by `rfl`) and `intended_main_fc` (the submitted theorem implies the Formal Conjectures statement). Contains no part of the proof itself. | |

## The endpoint `α_{2^n − 1}`

Erdős and Szekeres (1960) proved

```
α_{2^n} = α_{2^n − 1} = π (1 − 1/n)      (n ≥ 3).
```

`Erdos504Formal/Erdos504Endpoint.lean` works on the endpoint. What is **proved**
there:

* `exists_config_angle_lt_card_sub_one` — for every `ε > 0` there is a set of
  exactly `2^n − 1` points all of whose angles are below `π (1 − 1/n) + ε`
  (Szekeres' construction with one point deleted);
* `minimaxAngle_card_sub_one_le` — the supremum half,
  `α_{2^n − 1} ≤ π (1 − 1/n)`;
* `erdos_504_endpoint_exists_of_card_le` and `erdos_504_endpoint_of_card_le` —
  the endpoint itself, **conditional** on the single lemma

  ```lean
  def StrictCountingBound (n : ℕ) : Prop :=
    ∀ S : Finset ℂ,
      (∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
        EuclideanGeometry.angle p q r < (1 - 1 / (n : ℝ)) * π) →
      S.card ≤ 2 ^ n - 2
  ```

  i.e. *if every angle of `S` is strictly below `π (1 − 1/n)`, then `S` has at
  most `2^n − 2` points*.

### The remaining gap, precisely

The upstream file proves only the non-strict counting bound
`Erdos504.card_le_two_pow_of_angle_le`:

```lean
theorem card_le_two_pow_of_angle_le {n : ℕ} (hn : 0 < n) (S : Finset ℂ)
    (hangle : … angle p q r ≤ (1 - 1 / (n : ℝ)) * π) : S.card ≤ 2 ^ n
```

`2^n` points already force an angle *strictly* larger than `π (1 − 1/n)`
(Erdős–Szekeres 1960, Theorem 1, `Erdos504.erdos_szekeres_1960`), so the
endpoint needs the counting argument to lose one further point once the
hypothesis is strict. The upstream `2^n`-argument (rigidity ⇒ regular `n`-gon
⇒ an interior point sees a wide angle) is built around `hcard : S.card = 2 ^ n`
and does not carry over to `2^n − 1` points; the upstream README lists the
endpoint as future work.

`StrictCountingBound` is the exact statement that is still missing: everything
else in the endpoint — the supremum bookkeeping, the `ε`-sharpness, the
deletion of a point from Szekeres' construction — is proved and machine-checked
in this repository.
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

# 3. build the library (the four Lean files)
lake build

# 4. type-check the target theorems directly
lake env lean Erdos504Formal/Erdos504Minimax.lean
lake env lean Erdos504Formal/Erdos504Endpoint.lean
lake env lean Erdos504Formal/AuditBridge.lean
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
#print axioms Erdos504.exists_config_angle_lt_card_sub_one
#print axioms Erdos504.minimaxAngle_card_sub_one_le
#print axioms Erdos504.erdos_504_endpoint_exists_of_card_le
#print axioms Erdos504.erdos_504_endpoint_of_card_le
#print axioms Erdos504.minimaxAngle_eq_fc
#print axioms Erdos504.intended_main_fc
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
