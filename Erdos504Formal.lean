/-
Umbrella module for the `Erdos504Formal` library.

- `Erdos504Formal.Erdos504` — the Szekeres (1941) bounds and the Erdős–Szekeres
  (1960) theorem, republished unchanged from `ToshiDad/erdos-504`.
- `Erdos504Formal.Erdos504Minimax` — the minimax-angle (`sSup`) formulation and
  the main theorem `Erdos504.erdos_504`.
- `Erdos504Formal.Erdos504StrictCounting` — the strict sector-counting bound
  `strictCountingBound` (Erdős–Szekeres 1960, Theorem 3).
- `Erdos504Formal.Erdos504Endpoint` — the endpoint `α_{2^n - 1}`: the sharp
  (`ε`-relaxed) side and the endpoint itself are proved, using
  `strictCountingBound`.
- `Erdos504Formal.AuditBridge` — the statement-correspondence bridge to the
  Formal Conjectures statement of the problem.
- `Erdos504Formal.Erdos504Subset` — subsets, deletion of points, and the
  monotonicity of the minimax angle (Phase-1a scaffolding).
- `Erdos504Formal.Erdos504SendovShell` — the generic `sSup` template that
  turns a pair of atomic ingredients into a minimax-angle identity
  (Phase-1a scaffolding).

The module `Erdos504Formal.Erdos504Sendov` is **not** imported here on purpose:
it is an incomplete skeleton for Sendov's complete determination of `α_N` and
contains `sorry` placeholders.  Importing this umbrella therefore keeps the
library free of `sorry`.
-/
import Erdos504Formal.Erdos504
import Erdos504Formal.Erdos504Minimax
import Erdos504Formal.Erdos504StrictCounting
import Erdos504Formal.Erdos504Endpoint
import Erdos504Formal.AuditBridge
import Erdos504Formal.Erdos504Subset
import Erdos504Formal.Erdos504SendovShell
