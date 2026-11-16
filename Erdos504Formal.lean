/-
Umbrella module for the `Erdos504Formal` library.

- `Erdos504Formal.Erdos504` — the Szekeres (1941) bounds and the Erdős–Szekeres
  (1960) theorem, republished unchanged from `ToshiDad/erdos-504`.
- `Erdos504Formal.Erdos504Minimax` — the minimax-angle (`sSup`) formulation and
  the main theorem `Erdos504.erdos_504`.
- `Erdos504Formal.Erdos504Endpoint` — the endpoint `α_{2^n - 1}`: the sharp
  (`ε`-relaxed) side is proved, the endpoint itself is proved conditional on the
  strict counting bound `StrictCountingBound`.
-/
import Erdos504Formal.Erdos504
import Erdos504Formal.Erdos504Minimax
import Erdos504Formal.Erdos504Endpoint
