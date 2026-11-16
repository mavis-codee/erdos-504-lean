# Attribution

This repository contains a complete, sorry-free Lean 4 formalisation of the
minimax-angle statement of **Erdős Problem #504 (Blumenthal's problem)**,
which is the target of `JSP-000404` in the Justin Sun Prize problem bank.

## Split of the work

| File | Origin | Status |
| --- | --- | --- |
| `Erdos504Formal/Erdos504.lean` | **Republished unchanged** from [`ToshiDad/erdos-504`](https://github.com/ToshiDad/erdos-504) at commit [`fd344a9b65ecaebca66b77497fea197cb895960e`](https://github.com/ToshiDad/erdos-504/tree/fd344a9b65ecaebca66b77497fea197cb895960e) | Byte-identical to the upstream file (319,212 bytes). Original authorship and original commit dates are retained; the upstream author is the author of every declaration in this file. |
| `Erdos504Formal/Erdos504Minimax.lean` | **New work by the submitting author.** | Defines the minimax angle `α_N` as a supremum, proves the auxiliary lemma `exists_distinct_angle_gt`, and proves the main theorem `Erdos504.erdos_504`. |
| `Erdos504Formal/Erdos504Endpoint.lean` | **New work by the submitting author.** | Works on the endpoint `α_{2^n − 1}`: proves the sharp (`ε`-relaxed) side, the supremum half `α_{2^n − 1} ≤ π (1 − 1/n)`, and the endpoint itself **conditional** on the counting lemma `StrictCountingBound`, which is stated precisely but not proved. |

The upstream file contains **no** `sorry`, no `admit` and no `native_decide`;
the new files contain **no** `sorry` either. The whole library is therefore
`sorry`-free.

The endpoint file is honest about its own limit: `StrictCountingBound` is a
*hypothesis* of `erdos_504_endpoint_of_card_le`, not a theorem. No claim of a
complete formalisation of the endpoint is made.

## What the upstream file already contained

`ToshiDad/erdos-504` formalises the three published ingredients of the problem,
all sorry-free:

* `Erdos504.exists_angle_gt` — **Szekeres (1941), lower bound.** More than `2^n`
  points of the plane determine an angle greater than `(1 - 1/n)·π`.
* `Erdos504.exists_config_angle_lt` — **Szekeres (1941), upper-bound
  construction.** For every `ε > 0` there is a set of exactly `2^t` points all of
  whose angles are below `(1 - 1/t)·π + ε`.
* `Erdos504.erdos_szekeres_1960` — **Erdős–Szekeres (1960), Theorem 1.** Among
  `2^n` points of the plane some three determine an angle exceeding
  `(1 - 1/n)·π`.

The upstream README states explicitly that the supremum-based quantity `α` is
*not* defined in Lean there, and lists the endpoint `α(2^n − 1)` and Sendov's
complete determination of `α(N)` as future work. `Erdos504Minimax.lean` supplies
the missing `sSup` layer.

## Why this split

* The awarding rules treat a *mirror* of somebody else's proof as an unacceptable
  original source, but they explicitly accept a proof that was **first published
  in a coauthor's repository and is republished unchanged, with its original
  authorship and dates**, in the submitting author's repository (see the
  `Attribution basis` row of `JSP-000110` in the problem bank).
* The new theorem `Erdos504.erdos_504` — the statement of the problem in its
  `sSup` form — is new work and is claimed by the submitting author only.

## Author identity

Every commit in this repository was made by the owner of the GitHub account
[`mavis-codee`](https://github.com/mavis-codee), whose display name is
**Koji Tamaki**. The author address of each commit is a verified address of that
account, so GitHub attributes every commit here to `mavis-codee`:

```
GET /repos/mavis-codee/erdos-504-lean/commits/a3e262e8fadde9a5b208495d94f4d71f0092d6db
  .commit.author  = { name: "Mavis", email: "1183959472@qq.com", date: "2026-11-16T10:02:36Z" }
  .commit.committer = { name: "Mavis", email: "1183959472@qq.com", date: "2026-11-16T10:02:36Z" }
  .author.login   = "mavis-codee"
  .committer.login = "mavis-codee"
```

Two author strings occur in the history because the author's display name and
commit address were updated after the proof history was first pushed:

| Commits | Author string | Address |
| --- | --- | --- |
| `a3e262e` … `f2e33a2` — the submitted proof history | `Mavis` | `1183959472@qq.com` |
| later commits (documentation only) | `Koji Tamaki` | `kojitamaki223@gmail.com` |

Both addresses are verified addresses of the same account, and **no commit
identity was ever rewritten**: the priority anchor
`a3e262e8fadde9a5b208495d94f4d71f0092d6db` and every commit of the submitted
history keep their original object id, author string, author date and committer
date. The author's public correspondence address, used for the award process, is
`kojitamaki223@gmail.com`.

## References

* G. Szekeres, *On an extremum problem in the plane*, Amer. J. Math. **63**
  (1941), 208–210. <https://doi.org/10.2307/2371290>
* P. Erdős and G. Szekeres, *On some extremum problems in elementary geometry*,
  Ann. Univ. Sci. Budapest. Eötvös Sect. Math. **3** (1960/61), 53–62.
* B. Sendov, *Minimax of the angles in a plane configuration of points*, Acta
  Math. Hungar. **69** (1995), 27–46.
* T. F. Bloom, *Erdős Problem #504*, <https://www.erdosproblems.com/504>
