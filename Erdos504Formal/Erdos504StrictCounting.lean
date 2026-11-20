/-
Lean formalisation of the *strict* sector-counting bound for Erdős Problem #504
(Blumenthal's minimax angle problem).

The endpoint `α_{2^n - 1} = π (1 - 1/n)` of Erdős–Szekeres (1960) splits into a
supremum half (Szekeres' construction with one point deleted) and a
guaranteed-angle half.  The guaranteed-angle half is equivalent to the counting
statement

    all angles of `S` are strictly below `π (1 - 1/n)`  ⟹  `S.card ≤ 2 ^ n - 2`,

which is `StrictCountingBound`.  This file proves the abstract counting lemma
(Lemma 4 of Erdős–Szekeres 1960).  The geometric assembly is in progress.

Reference: P. Erdős and G. Szekeres, *On some extremum problems in elementary
geometry*, Ann. Univ. Sci. Budapest. Eötvös Sect. Math. 3-4 (1960/61), 53–62.
-/
import Erdos504Formal.Erdos504

namespace Erdos504

open Real EuclideanGeometry

-- Unify decidability instances so that `emptyCountIn` and restated filters
-- are syntactically equal.
attribute [local instance] Classical.propDecidable

/-! ## The statement -/

/--
**The strict sector-counting bound.**  If every angle determined by `S` is
*strictly* smaller than `π (1 - 1/n)`, then `S` has at most `2^n - 2` points.

This is the sharp counterpart of `Erdos504.card_le_two_pow_of_angle_le`
(which yields only `S.card ≤ 2 ^ n` for the non-strict hypothesis
`≤ π (1 - 1/n)`).  It is the mathematical content of the endpoint
`α_{2^n - 1} = π (1 - 1/n)` of Erdős–Szekeres (1960).
-/
def StrictCountingBound (n : ℕ) : Prop :=
  ∀ S : Finset ℂ,
    (∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
      EuclideanGeometry.angle p q r < (1 - 1 / (n : ℝ)) * π) →
    S.card ≤ 2 ^ n - 2

/-! ## Arithmetic helpers -/

/-- `2 ^ n ≥ 8` for `n ≥ 3`. -/
lemma two_pow_ge_eight' {n : ℕ} (hn : 3 ≤ n) : 8 ≤ 2 ^ n := by
  have h1 : (1 : ℕ) ≤ 2 ^ (n - 3) := Nat.one_le_pow (n - 3) 2 (by norm_num)
  have h2 : 8 * 1 ≤ 8 * 2 ^ (n - 3) := Nat.mul_le_mul_left 8 h1
  have h3 : 8 * 2 ^ (n - 3) = 2 ^ n := by
    calc 8 * 2 ^ (n - 3) = 2 ^ 3 * 2 ^ (n - 3) := by norm_num
      _ = 2 ^ (3 + (n - 3)) := (Nat.pow_add 2 3 (n - 3)).symm
      _ = 2 ^ n := by rw [show (3 : ℕ) + (n - 3) = n by omega]
  omega

/-- The Erdős–Szekeres value `π (1 - 1/n)` is positive whenever `n ≥ 3`. -/
lemma pi_mul_one_sub_inv_pos_sc {n : ℕ} (hn : 3 ≤ n) :
    0 < (1 - 1 / (n : ℝ)) * π := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < n := by linarith
  have hinv : (1 : ℝ) / n < 1 := (div_lt_iff₀ hn_pos).2 (by linarith)
  have hcoef : 0 < 1 - 1 / (n : ℝ) := by linarith
  exact mul_pos hcoef Real.pi_pos

/-- `2 ^ k ≥ 1`. -/
lemma one_le_two_pow' (k : ℕ) : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)

/-- `2 ^ (k+1) - 1 = 2 * (2 ^ k - 1) + 1`. -/
lemma two_pow_succ_sub_one (k : ℕ) :
    2 ^ (k + 1) - 1 = 2 * (2 ^ k - 1) + 1 := by
  have h := one_le_two_pow' k
  omega

/-- Monotone in the exponent: `a ≤ b` implies `2 ^ a ≤ 2 ^ b`. -/
lemma pow_two_le_pow_two {a b : ℕ} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b := by
  have h1 : (1 : ℕ) ≤ 2 ^ (b - a) := one_le_two_pow' (b - a)
  have h2 : 2 ^ a * 1 ≤ 2 ^ a * 2 ^ (b - a) := Nat.mul_le_mul_left _ h1
  have h3 : 2 ^ a * 2 ^ (b - a) = 2 ^ (a + (b - a)) := (Nat.pow_add 2 a (b - a)).symm
  have h4 : a + (b - a) = b := by omega
  rw [h4] at h3
  calc 2 ^ a = 2 ^ a * 1 := (Nat.mul_one _).symm
    _ ≤ 2 ^ a * 2 ^ (b - a) := h2
    _ = 2 ^ b := h3

/-- Monotone: `a ≤ b` implies `2 ^ a - 1 ≤ 2 ^ b - 1`. -/
lemma two_pow_sub_one_le {a b : ℕ} (h : a ≤ b) : 2 ^ a - 1 ≤ 2 ^ b - 1 := by
  have h1 := one_le_two_pow' a
  have h2 : 2 ^ a ≤ 2 ^ b := pow_two_le_pow_two h
  omega

/-- Linear arithmetic on the *atoms* `x, y, z`: from `x ≤ 2y+1` and `x ≤ 2z+1`
conclude `x ≤ y+z+1`.  Used to keep `omega` away from variable exponents. -/
lemma two_pow_iso_le {x y z : ℕ} (h1 : x ≤ 2 * y + 1) (h2 : x ≤ 2 * z + 1) :
    x ≤ y + z + 1 := by
  omega

/-! ## Shifting colours -/

/-- Embed `Fin n` into `Fin n+1` as the nonzero colours. -/
def shiftSucc {n : ℕ} (i : Fin n) : Fin (n + 1) :=
  ⟨i.val + 1, by have := i.isLt; omega⟩

/-- Remove the zero colour, given a proof that the colour is nonzero. -/
def shiftPred {n : ℕ} (i : Fin (n + 1)) (h : i ≠ 0) : Fin n :=
  ⟨i.val - 1, by
    have hi := i.isLt
    have hne : i.val ≠ 0 := fun he => h (Fin.ext he)
    omega⟩

lemma shiftSucc_ne_zero {n : ℕ} (i : Fin n) : shiftSucc i ≠ 0 := by
  intro h
  have hv : (shiftSucc i).val = 0 := by rw [h]; rfl
  simp only [shiftSucc] at hv
  omega

lemma shiftPred_shiftSucc {n : ℕ} (i : Fin n) :
    shiftPred (shiftSucc i) (shiftSucc_ne_zero i) = i := by
  apply Fin.ext
  show (shiftSucc i).val - 1 = i.val
  simp only [shiftSucc]
  omega

lemma shiftSucc_pred {n : ℕ} (i : Fin (n+1)) (h : i ≠ 0) :
    shiftSucc (shiftPred i h) = i := by
  apply Fin.ext
  show (shiftPred i h).val + 1 = i.val
  have hi := i.isLt
  have hne : i.val ≠ 0 := fun he => h (Fin.ext he)
  simp only [shiftPred]
  omega

lemma shiftSucc_inj {n : ℕ} : Function.Injective (@shiftSucc n) := by
  intro i j hij
  apply Fin.ext
  have h1 : (shiftSucc i).val = (shiftSucc j).val := by rw [hij]
  simp only [shiftSucc] at h1
  omega

/-! ## Empty colours -/

/-- The set of colours in which `p` is isolated *inside the vertex set `W`*.
Defined opaquely so that occurrences in later statements are syntactically equal. -/
noncomputable def emptyFilter {V : Type*} [DecidableEq V] {n : ℕ}
    (color : V → V → Fin n) (W : Finset V) (p : V) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => ∀ q ∈ W, q ≠ p → color p q ≠ i)

/-- The successor-colour filter, opaquely (same reason as `emptyFilter`). -/
noncomputable def succFilter {V : Type*} [DecidableEq V] {n : ℕ}
    (color : V → V → Fin (n+1)) (W : Finset V) (p : V) : Finset (Fin n) :=
  Finset.univ.filter (fun j : Fin n => ∀ q ∈ W, q ≠ p → color p q ≠ shiftSucc j)

/-- The number of colours in which `p` is isolated *inside the vertex set `W`*. -/
noncomputable def emptyCountIn {V : Type*} [DecidableEq V] {n : ℕ}
    (color : V → V → Fin n) (W : Finset V) (p : V) : ℕ :=
  (emptyFilter color W p).card

/-- Cardinality of the successor-colour filter, opaquely. -/
noncomputable def succEmpty {V : Type*} [DecidableEq V] {n : ℕ}
    (color : V → V → Fin (n+1)) (W : Finset V) (p : V) : ℕ :=
  (succFilter color W p).card

/-- Membership in `emptyFilter`, stated on the opaque atom so that later rewrites
never re-synthesize the `DecidablePred` instance of the raw filter. -/
lemma mem_emptyFilter {V : Type*} [DecidableEq V] {n : ℕ}
    (color : V → V → Fin n) (W : Finset V) (p : V) (i : Fin n) :
    i ∈ emptyFilter color W p ↔ ∀ q ∈ W, q ≠ p → color p q ≠ i := by
  unfold emptyFilter
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ i, h⟩⟩

/-- Membership in `succFilter`, stated on the opaque atom. -/
lemma mem_succFilter {V : Type*} [DecidableEq V] {n : ℕ}
    (color : V → V → Fin (n+1)) (W : Finset V) (p : V) (j : Fin n) :
    j ∈ succFilter color W p ↔ ∀ q ∈ W, q ≠ p → color p q ≠ shiftSucc j := by
  unfold succFilter
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ j, h⟩⟩

lemma emptyCountIn_mem {V : Type*} [DecidableEq V] {n : ℕ}
    {color : V → V → Fin n} {W : Finset V} {p : V} {i : Fin n} :
    (∀ q ∈ W, q ≠ p → color p q ≠ i) ↔ i ∈ emptyFilter color W p := by
  rw [mem_emptyFilter]

/-- Smaller vertex sets have more empty colours. -/
lemma emptyCountIn_mono_W {V : Type*} [DecidableEq V] {n : ℕ}
    {color : V → V → Fin n} {W₁ W₂ : Finset V} (h : W₂ ⊆ W₁) {p : V} :
    emptyCountIn color W₁ p ≤ emptyCountIn color W₂ p := by
  unfold emptyCountIn
  apply Finset.card_le_card
  intro j hj
  rw [mem_emptyFilter] at hj ⊢
  exact fun q hq hqp => hj q (h hq) hqp

/-- Smaller vertex sets have a larger successor-colour count. -/
lemma succEmpty_mono {V : Type*} [DecidableEq V] {n : ℕ}
    {color : V → V → Fin (n+1)} {W₁ W₂ : Finset V} (h : W₂ ⊆ W₁) {p : V} :
    succEmpty color W₁ p ≤ succEmpty color W₂ p := by
  unfold succEmpty
  apply Finset.card_le_card
  intro j hj
  rw [mem_succFilter] at hj ⊢
  exact fun q hq hqp => hj q (h hq) hqp

/-- Dropping the zero colour: the successor-colour part of `emptyCountIn`. -/
lemma emptyCountIn_succ_split {V : Type*} [DecidableEq V] {n : ℕ}
    (color : V → V → Fin (n+1)) (W : Finset V) (p : V) :
    emptyCountIn color W p
      ≤ (if ∀ q ∈ W, q ≠ p → color p q ≠ 0 then 1 else 0) + succEmpty color W p := by
  by_cases hP : ∀ q ∈ W, q ≠ p → color p q ≠ 0
  · rw [if_pos hP]
    show (emptyFilter color W p).card ≤ 1 + (succFilter color W p).card
    have key : emptyFilter color W p
        = insert 0 ((succFilter color W p).image shiftSucc) := by
      apply Finset.ext
      intro i
      rw [mem_emptyFilter, Finset.mem_insert, Finset.mem_image]
      constructor
      · intro hi
        by_cases h0 : i = 0
        · exact Or.inl h0
        · refine Or.inr ⟨shiftPred i h0,
            (mem_succFilter color W p (shiftPred i h0)).mpr ?_, shiftSucc_pred i h0⟩
          rw [← shiftSucc_pred i h0] at hi
          exact hi
      · rintro (rfl | ⟨j, hj, hji⟩)
        · exact hP
        · rw [← hji]
          exact (mem_succFilter color W p j).mp hj
    rw [key]
    have h0not : (0 : Fin (n+1)) ∉ (succFilter color W p).image shiftSucc := by
      intro h
      obtain ⟨j, -, hj⟩ := Finset.mem_image.mp h
      exact shiftSucc_ne_zero j hj
    rw [Finset.card_insert_of_notMem h0not]
    rw [Finset.card_image_of_injOn (fun j _ k _ h => shiftSucc_inj h)]
    omega
  · rw [if_neg hP]
    show (emptyFilter color W p).card ≤ 0 + (succFilter color W p).card
    have key : emptyFilter color W p = (succFilter color W p).image shiftSucc := by
      apply Finset.ext
      intro i
      rw [mem_emptyFilter, Finset.mem_image]
      constructor
      · intro hi
        by_cases h0 : i = 0
        · refine absurd ?_ hP
          rw [← h0]
          exact hi
        · refine ⟨shiftPred i h0, (mem_succFilter color W p (shiftPred i h0)).mpr ?_,
            shiftSucc_pred i h0⟩
          rw [← shiftSucc_pred i h0] at hi
          exact hi
      · rintro ⟨j, hj, hji⟩
        rw [← hji]
        exact (mem_succFilter color W p j).mp hj
    rw [key]
    rw [Finset.card_image_of_injOn (fun j _ k _ h => shiftSucc_inj h)]
    omega

/-! ## The one-colour case -/

private theorem emptyCount_sum_le_one (V : Type) [Fintype V] [DecidableEq V]
    (k : ℕ) (W : Finset V) (color : V → V → Fin 1) (side : Fin 1 → V → Bool)
    (hside : ∀ u ∈ W, ∀ v ∈ W, u ≠ v → side (color u v) u ≠ side (color u v) v)
    (hW : W.card + k = 2) :
    ∑ p ∈ W, (2 ^ emptyCountIn color W p - 1) ≤ k := by
  have hcol : ∀ p q : V, color p q = 0 := fun p q => Subsingleton.elim _ _
  have hinj : ∀ u ∈ W, ∀ v ∈ W, side 0 u = side 0 v → u = v := by
    intro u hu v hv h
    by_contra huv
    exact hside u hu v hv huv (by rw [hcol]; exact h)
  have hcard2 : W.card ≤ 2 := by
    have hinj' : Function.Injective (fun p : ↥W => side 0 (p : V)) := by
      intro u v h
      have := hinj (↑u) u.property (↑v) v.property h
      exact Subtype.ext this
    have hle := Fintype.card_le_of_injective (fun p : ↥W => side 0 (p : V)) hinj'
    have h2 : Fintype.card ↥W = W.card := Fintype.card_coe W
    have h3 : Fintype.card Bool = 2 := by simp
    omega
  have hempty : ∀ p ∈ W, emptyCountIn color W p = if 2 ≤ W.card then 0 else 1 := by
    intro p hp
    rcases Nat.lt_or_ge W.card 2 with hlt | hge
    · have hall : ∀ q ∈ W, q = p := by
        intro q hq
        by_contra hqp
        have hpair : ({p, q} : Finset V) ⊆ W := by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx'
          · exact hp
          · have hxq : x = q := Finset.mem_singleton.mp hx'
            rw [hxq]
            exact hq
        have hcardpair : ({p, q} : Finset V).card = 2 :=
          Finset.card_pair (show p ≠ q from fun hc => hqp hc.symm)
        have := Finset.card_le_card hpair
        omega
      have he1 : emptyCountIn color W p = 1 := by
        have hfil : emptyFilter color W p = (Finset.univ : Finset (Fin 1)) := by
          apply Finset.eq_univ_of_forall
          intro i
          rw [mem_emptyFilter]
          exact fun q hq hqp => absurd (hall q hq) hqp
        unfold emptyCountIn
        rw [hfil]
        simp
      rw [he1, if_neg (show ¬ (2 : ℕ) ≤ W.card from by omega)]
    · have hex : ∃ q ∈ W, q ≠ p := by
        by_contra hall
        have hsub : W ⊆ ({p} : Finset V) := fun x hx => by
          by_contra hx'
          exact hall ⟨x, hx, fun hc => hx' (by rw [hc]; exact Finset.mem_singleton_self p)⟩
        have hle := Finset.card_le_card hsub
        have hp1 : ({p} : Finset V).card = 1 := Finset.card_singleton p
        omega
      obtain ⟨q, hq, hqp⟩ := hex
      have he0 : emptyCountIn color W p = 0 := by
        have hfil : emptyFilter color W p = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro i hi
          rw [mem_emptyFilter] at hi
          exact hi q hq hqp ((hcol p q).trans (Subsingleton.elim i 0).symm)
        unfold emptyCountIn
        rw [hfil]
        rfl
      rw [he0, if_pos (show (2 : ℕ) ≤ W.card from by omega)]
  rcases Nat.lt_or_ge W.card 2 with hlt | hge
  · have h1 : W.card ≤ 1 := by omega
    have hstep : ∑ p ∈ W, (2 ^ emptyCountIn color W p - 1)
        = ∑ p ∈ W, (1 : ℕ) :=
      Finset.sum_congr rfl (fun p hp => by
        rw [hempty p hp, if_neg (show ¬ (2 : ℕ) ≤ W.card from by omega)]
        simp)
    rw [hstep]
    simp
    omega
  · have hstep : ∑ p ∈ W, (2 ^ emptyCountIn color W p - 1)
        = ∑ p ∈ W, (0 : ℕ) :=
      Finset.sum_congr rfl (fun p hp => by
        rw [hempty p hp, if_pos hge]
        simp)
    rw [hstep]
    simp

/-! ## Lemma 4 of Erdős–Szekeres 1960 -/

/--
**Lemma 4 (Erdős–Szekeres 1960).**  Let the edges of the complete graph on a
`Fintype` `V` be coloured with `n` colours, symmetrically, in such a way that
each colour class is bipartite in the strong sense that there is a `side`
function with the two endpoints of every edge of colour `i` on opposite sides.
If the vertex set `W` has `2 ^ n - k` points then

    ∑_{p ∈ W} (2 ^ v(p) - 1) ≤ k,

where `v(p)` is the number of colours in which `p` is isolated inside `W`.
-/
theorem emptyCount_sum_le :
    ∀ n : ℕ, ∀ V : Type, [Fintype V] → [DecidableEq V] → ∀ k : ℕ,
      ∀ (W : Finset V) (color : V → V → Fin n) (side : Fin n → V → Bool),
        (∀ u ∈ W, ∀ v ∈ W, u ≠ v → side (color u v) u ≠ side (color u v) v) →
        (∀ u v : V, color u v = color v u) →
        W.card + k = 2 ^ n →
        ∑ p ∈ W, (2 ^ emptyCountIn color W p - 1) ≤ k := by
  intro n
  induction n with
  | zero =>
    intro V _ _ k W color _ _ hW
    have hW0 : W = ∅ := Finset.eq_empty_iff_forall_notMem.mpr
      (fun p _ => Fin.elim0 (color p p))
    subst hW0
    simp
  | succ n ih =>
    intro V _ _ k W color side hside hsymm hN
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have h2 : (2 : ℕ) ^ (0 + 1) = 2 := by norm_num
      rw [h2] at hN
      exact emptyCount_sum_le_one V k W color side hside (by omega)
    · -- Partitions of `W` by colour-`0` isolation and side.
      set Q : Finset V :=
        W.filter (fun p : V => ∀ q ∈ W, q ≠ p → color p q ≠ 0) with hQdef
      have hQsub : Q ⊆ W := Finset.filter_subset _ _
      have hQmem : ∀ p : V, p ∈ Q ↔ (p ∈ W ∧ ∀ q ∈ W, q ≠ p → color p q ≠ 0) := by
        intro p
        rw [hQdef]
        exact Finset.mem_filter
      set A : Finset V := W.filter (fun p : V => p ∉ Q ∧ side 0 p = true) with hAdef
      have hAsub : A ⊆ W := Finset.filter_subset _ _
      have hAmem : ∀ p : V, p ∈ A ↔ (p ∈ W ∧ p ∉ Q ∧ side 0 p = true) := by
        intro p
        rw [hAdef]
        exact Finset.mem_filter
      set B : Finset V := W.filter (fun p : V => p ∉ Q ∧ side 0 p = false) with hBdef
      have hBsub : B ⊆ W := Finset.filter_subset _ _
      have hBmem : ∀ p : V, p ∈ B ↔ (p ∈ W ∧ p ∉ Q ∧ side 0 p = false) := by
        intro p
        rw [hBdef]
        exact Finset.mem_filter
      have hAQ : Disjoint A Q := by
        rw [Finset.disjoint_iff_inter_eq_empty]
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro p hp
        rw [Finset.mem_inter] at hp
        exact (hAmem p).mp hp.1 |>.2.1 hp.2
      have hBQ : Disjoint B Q := by
        rw [Finset.disjoint_iff_inter_eq_empty]
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro p hp
        rw [Finset.mem_inter] at hp
        exact (hBmem p).mp hp.1 |>.2.1 hp.2
      have hAB : Disjoint A B := by
        rw [Finset.disjoint_iff_inter_eq_empty]
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro p hp
        rw [Finset.mem_inter] at hp
        have h1 := (hAmem p).mp hp.1
        have h2 := (hBmem p).mp hp.2
        rw [h1.2.2] at h2
        exact Bool.noConfusion h2.2.2
      have hcover : A ∪ B ∪ Q = W := by
        ext p
        refine ⟨fun h => ?_, fun hpW => ?_⟩
        · rcases Finset.mem_union.mp h with hAB' | hQ'
          · rcases Finset.mem_union.mp hAB' with hA' | hB'
            · exact ((hAmem p).mp hA').1
            · exact ((hBmem p).mp hB').1
          · exact ((hQmem p).mp hQ').1
        · by_cases hpQ : p ∈ Q
          · exact Finset.mem_union_right _ hpQ
          · have hbool : side 0 p = true ∨ side 0 p = false := by
              cases hb : side 0 p
              · exact Or.inr rfl
              · exact Or.inl rfl
            rcases hbool with hp0 | hp0
            · exact Finset.mem_union_left _
                (Finset.mem_union_left _ ((hAmem p).mpr ⟨hpW, hpQ, hp0⟩))
            · exact Finset.mem_union_left _
                (Finset.mem_union_right _ ((hBmem p).mpr ⟨hpW, hpQ, hp0⟩))
      -- No colour-`0` edge inside `A ∪ Q` or `B ∪ Q`.
      have hno0 : ∀ p q : V, p ∈ A ∪ Q → q ∈ A ∪ Q → p ≠ q → color p q ≠ 0 := by
        intro p q hp hq hpq
        rcases Finset.mem_union.mp hp with hpA | hpQ
        · rcases Finset.mem_union.mp hq with hqA | hqQ
          · have h1 := (hAmem p).mp hpA
            have h2 := (hAmem q).mp hqA
            intro hc
            have hs := hside p h1.1 q h2.1 hpq
            rw [hc, h1.2.2, h2.2.2] at hs
            exact hs rfl
          · intro hc
            have hqiso := ((hQmem q).mp hqQ).2
            have hpW : p ∈ W := ((hAmem p).mp hpA).1
            have hqp' : color q p ≠ 0 := hqiso p hpW hpq
            exact hqp' (by rw [hsymm]; exact hc)
        · intro hc
          have hpiso := ((hQmem p).mp hpQ).2
          have hqW : q ∈ W := by
            rcases Finset.mem_union.mp hq with h | h
            · exact hAsub h
            · exact hQsub h
          exact hpiso q hqW (Ne.symm hpq) hc
      have hno0' : ∀ p q : V, p ∈ B ∪ Q → q ∈ B ∪ Q → p ≠ q → color p q ≠ 0 := by
        intro p q hp hq hpq
        rcases Finset.mem_union.mp hp with hpB | hpQ
        · rcases Finset.mem_union.mp hq with hqB | hqQ
          · have h1 := (hBmem p).mp hpB
            have h2 := (hBmem q).mp hqB
            intro hc
            have hs := hside p h1.1 q h2.1 hpq
            rw [hc, h1.2.2, h2.2.2] at hs
            exact hs rfl
          · intro hc
            have hqiso := ((hQmem q).mp hqQ).2
            have hpW : p ∈ W := ((hBmem p).mp hpB).1
            have hqp' : color q p ≠ 0 := hqiso p hpW hpq
            exact hqp' (by rw [hsymm]; exact hc)
        · intro hc
          have hpiso := ((hQmem p).mp hpQ).2
          have hqW : q ∈ W := by
            rcases Finset.mem_union.mp hq with h | h
            · exact hBsub h
            · exact hQsub h
          exact hpiso q hqW (Ne.symm hpq) hc
      -- The two halves.
      set WA : Finset V := A ∪ Q with hWAeq
      set WB : Finset V := B ∪ Q with hWBeq
      have hWAsub : WA ⊆ W := fun p hp => by
        rcases Finset.mem_union.mp hp with h | h
        · exact hAsub h
        · exact hQsub h
      have hWBsub : WB ⊆ W := fun p hp => by
        rcases Finset.mem_union.mp hp with h | h
        · exact hBsub h
        · exact hQsub h
      have hAtoWA : ∀ p ∈ A, p ∈ WA := fun p hp => Finset.mem_union_left _ hp
      have hBtoWB : ∀ p ∈ B, p ∈ WB := fun p hp => Finset.mem_union_left _ hp
      have hQtoWA : ∀ p ∈ Q, p ∈ WA := fun p hp => Finset.mem_union_right _ hp
      have hQtoWB : ∀ p ∈ Q, p ∈ WB := fun p hp => Finset.mem_union_right _ hp
      -- The shifted colouring.
      set colorN : V → V → Fin n := fun u v => ⟨(color u v).val - 1, by
        have hisLt := (color u v).isLt
        by_cases hh : color u v = 0
        · have hv0 : (color u v).val = 0 := by rw [hh]; rfl
          omega
        · have hne : (color u v).val ≠ 0 := fun he => hh (Fin.ext he)
          omega⟩ with hcolorN
      set sideN : Fin n → V → Bool := fun i p => side (shiftSucc i) p with hsideNdef
      have hvalN : ∀ u v : V, (colorN u v).val = (color u v).val - 1 := fun u v => rfl
      have hsymmN : ∀ u v : V, colorN u v = colorN v u := by
        intro u v
        apply Fin.ext
        rw [hvalN, hvalN, hsymm]
      have hshift : ∀ u v : V, color u v ≠ 0 → shiftSucc (colorN u v) = color u v := by
        intro u v h
        apply Fin.ext
        have hval : (color u v).val ≠ 0 := fun he => h (Fin.ext he)
        show (colorN u v).val + 1 = (color u v).val
        rw [hvalN]
        have := (color u v).isLt
        omega
      have hsideWA : ∀ u ∈ WA, ∀ v ∈ WA, u ≠ v →
          sideN (colorN u v) u ≠ sideN (colorN u v) v := by
        intro u hu v hv huv
        have hc : color u v ≠ 0 := hno0 u v hu hv huv
        have hsh : shiftSucc (colorN u v) = color u v := hshift u v hc
        show side (shiftSucc (colorN u v)) u ≠ side (shiftSucc (colorN u v)) v
        rw [hsh]
        exact hside u (hWAsub hu) v (hWAsub hv) huv
      have hsideWB : ∀ u ∈ WB, ∀ v ∈ WB, u ≠ v →
          sideN (colorN u v) u ≠ sideN (colorN u v) v := by
        intro u hu v hv huv
        have hc : color u v ≠ 0 := hno0' u v hu hv huv
        have hsh : shiftSucc (colorN u v) = color u v := hshift u v hc
        show side (shiftSucc (colorN u v)) u ≠ side (shiftSucc (colorN u v)) v
        rw [hsh]
        exact hside u (hWBsub hu) v (hWBsub hv) huv
      -- Cardinality bounds for the halves, via the existing colouring bound.
      have hWAle : WA.card ≤ 2 ^ n := by
        have h := card_le_two_pow_of_side
          (color := fun u v : ↥WA => colorN (↑u) (↑v))
          (side := fun i : Fin n => fun p : ↥WA => sideN i (↑p))
          (fun u v huv => hsideWA (↑u) u.property (↑v) v.property
            (fun h => huv (Subtype.ext h)))
        have hcoe : Fintype.card ↥WA = WA.card := Fintype.card_coe WA
        omega
      have hWBle : WB.card ≤ 2 ^ n := by
        have h := card_le_two_pow_of_side
          (color := fun u v : ↥WB => colorN (↑u) (↑v))
          (side := fun i : Fin n => fun p : ↥WB => sideN i (↑p))
          (fun u v huv => hsideWB (↑u) u.property (↑v) v.property
            (fun h => huv (Subtype.ext h)))
        have hcoe : Fintype.card ↥WB = WB.card := Fintype.card_coe WB
        omega
      have hcardWA : WA.card = A.card + Q.card := by
        rw [hWAeq]
        exact Finset.card_union_eq_card_add_card.mpr hAQ
      have hcardWB : WB.card = B.card + Q.card := by
        rw [hWBeq]
        exact Finset.card_union_eq_card_add_card.mpr hBQ
      have hdisABQ : Disjoint (A ∪ B) Q := by
        rw [Finset.disjoint_union_left]
        exact ⟨hAQ, hBQ⟩
      have hcardW : A.card + B.card + Q.card = W.card := by
        have h1 : (A ∪ B ∪ Q).card = W.card := by rw [hcover]
        rw [Finset.card_union_eq_card_add_card.mpr hdisABQ] at h1
        rw [Finset.card_union_eq_card_add_card.mpr hAB] at h1
        omega
      -- Relating `emptyCountIn colorN WA p` to the successor-colour filter.
      have heqN : ∀ p ∈ WA, emptyCountIn colorN WA p
          = succEmpty color WA p := by
        intro p hp
        unfold emptyCountIn succEmpty
        apply congrArg Finset.card
        apply Finset.ext
        intro j
        rw [mem_emptyFilter, mem_succFilter]
        apply forall_congr'
        intro q
        by_cases hqp : q = p
        · exact iff_of_true
            (fun _ hne => absurd hqp hne)
            (fun _ hne => absurd hqp hne)
        · by_cases hqW : q ∈ WA
          · have hc : color p q ≠ 0 := hno0 p q hp hqW (Ne.symm hqp)
            have hsh : shiftSucc (colorN p q) = color p q := hshift p q hc
            constructor
            · intro h h1 h2 heq2
              exact h h1 h2 (shiftSucc_inj (hsh.trans heq2))
            · intro h h1 h2 heq2
              exact h h1 h2 (by rw [← hsh, heq2])
          · exact iff_of_true
              (fun h1 _ _ => absurd h1 hqW)
              (fun h1 _ _ => absurd h1 hqW)
      have heqN' : ∀ p ∈ WB, emptyCountIn colorN WB p
          = succEmpty color WB p := by
        intro p hp
        unfold emptyCountIn succEmpty
        apply congrArg Finset.card
        apply Finset.ext
        intro j
        rw [mem_emptyFilter, mem_succFilter]
        apply forall_congr'
        intro q
        by_cases hqp : q = p
        · exact iff_of_true
            (fun _ hne => absurd hqp hne)
            (fun _ hne => absurd hqp hne)
        · by_cases hqW : q ∈ WB
          · have hc : color p q ≠ 0 := hno0' p q hp hqW (Ne.symm hqp)
            have hsh : shiftSucc (colorN p q) = color p q := hshift p q hc
            constructor
            · intro h h1 h2 heq2
              exact h h1 h2 (shiftSucc_inj (hsh.trans heq2))
            · intro h h1 h2 heq2
              exact h h1 h2 (by rw [← hsh, heq2])
          · exact iff_of_true
              (fun h1 _ _ => absurd h1 hqW)
              (fun h1 _ _ => absurd h1 hqW)
      -- Pointwise defect bounds.
      have hbA : ∀ p ∈ A, 2 ^ emptyCountIn color W p - 1
          ≤ 2 ^ emptyCountIn colorN WA p - 1 := by
        intro p hp
        have hpW : p ∈ W := ((hAmem p).mp hp).1
        have hnotQ : p ∉ Q := ((hAmem p).mp hp).2.1
        have hnotIso : ¬ ∀ q ∈ W, q ≠ p → color p q ≠ 0 := fun h =>
          hnotQ ((hQmem p).mpr ⟨hpW, h⟩)
        have hsplit := emptyCountIn_succ_split color W p
        rw [if_neg hnotIso] at hsplit
        have hmono : succEmpty color W p ≤ succEmpty color WA p :=
          succEmpty_mono (p := p) hWAsub
        have hEq : succEmpty color WA p = emptyCountIn colorN WA p :=
          (heqN p (hAtoWA p hp)).symm
        have h1 : emptyCountIn color W p ≤ succEmpty color W p := by omega
        exact two_pow_sub_one_le ((h1.trans hmono).trans (le_of_eq hEq))
      have hbB : ∀ p ∈ B, 2 ^ emptyCountIn color W p - 1
          ≤ 2 ^ emptyCountIn colorN WB p - 1 := by
        intro p hp
        have hpW : p ∈ W := ((hBmem p).mp hp).1
        have hnotQ : p ∉ Q := ((hBmem p).mp hp).2.1
        have hnotIso : ¬ ∀ q ∈ W, q ≠ p → color p q ≠ 0 := fun h =>
          hnotQ ((hQmem p).mpr ⟨hpW, h⟩)
        have hsplit := emptyCountIn_succ_split color W p
        rw [if_neg hnotIso] at hsplit
        have hmono : succEmpty color W p ≤ succEmpty color WB p :=
          succEmpty_mono (p := p) hWBsub
        have hEq : succEmpty color WB p = emptyCountIn colorN WB p :=
          (heqN' p (hBtoWB p hp)).symm
        have h1 : emptyCountIn color W p ≤ succEmpty color W p := by omega
        exact two_pow_sub_one_le ((h1.trans hmono).trans (le_of_eq hEq))
      have hbQ : ∀ p ∈ Q, 2 ^ emptyCountIn color W p - 1
          ≤ (2 ^ emptyCountIn colorN WA p - 1) + (2 ^ emptyCountIn colorN WB p - 1) + 1 := by
        intro p hp
        have hIso : ∀ q ∈ W, q ≠ p → color p q ≠ 0 := ((hQmem p).mp hp).2
        have hsplit := emptyCountIn_succ_split color W p
        rw [if_pos hIso] at hsplit
        have hmonoA : succEmpty color W p ≤ succEmpty color WA p :=
          succEmpty_mono (p := p) hWAsub
        have hmonoB : succEmpty color W p ≤ succEmpty color WB p :=
          succEmpty_mono (p := p) hWBsub
        have hEqA : succEmpty color WA p = emptyCountIn colorN WA p :=
          (heqN p (hQtoWA p hp)).symm
        have hEqB : succEmpty color WB p = emptyCountIn colorN WB p :=
          (heqN' p (hQtoWB p hp)).symm
        have heA : emptyCountIn color W p ≤ emptyCountIn colorN WA p + 1 := by
          calc emptyCountIn color W p
              ≤ 1 + succEmpty color W p := hsplit
            _ ≤ 1 + succEmpty color WA p := Nat.add_le_add_left hmonoA 1
            _ = emptyCountIn colorN WA p + 1 := by rw [hEqA]; ring
        have heB : emptyCountIn color W p ≤ emptyCountIn colorN WB p + 1 := by
          calc emptyCountIn color W p
              ≤ 1 + succEmpty color W p := hsplit
            _ ≤ 1 + succEmpty color WB p := Nat.add_le_add_left hmonoB 1
            _ = emptyCountIn colorN WB p + 1 := by rw [hEqB]; ring
        have t1 : 2 ^ emptyCountIn color W p - 1
            ≤ 2 ^ (emptyCountIn colorN WA p + 1) - 1 := two_pow_sub_one_le heA
        have t2 : 2 ^ emptyCountIn color W p - 1
            ≤ 2 ^ (emptyCountIn colorN WB p + 1) - 1 := two_pow_sub_one_le heB
        rw [two_pow_succ_sub_one] at t1 t2
        exact two_pow_iso_le t1 t2
      -- Apply the induction hypothesis to the two halves.
      have hkA : WA.card + (2 ^ n - WA.card) = 2 ^ n := by omega
      have hkB : WB.card + (2 ^ n - WB.card) = 2 ^ n := by omega
      have hihA := ih (V := V) (2 ^ n - WA.card) WA colorN sideN hsideWA hsymmN hkA
      have hihB := ih (V := V) (2 ^ n - WB.card) WB colorN sideN hsideWB hsymmN hkB
      -- Bookkeeping.
      have hsplit : ∑ p ∈ W, (2 ^ emptyCountIn color W p - 1)
          = ∑ p ∈ A, (2 ^ emptyCountIn color W p - 1)
            + ∑ p ∈ B, (2 ^ emptyCountIn color W p - 1)
            + ∑ p ∈ Q, (2 ^ emptyCountIn color W p - 1) := by
        rw [← hcover]
        rw [Finset.sum_union hdisABQ]
        rw [Finset.sum_union hAB]
      have hstep2 : ∑ p ∈ A, (2 ^ emptyCountIn color W p - 1)
            + ∑ p ∈ B, (2 ^ emptyCountIn color W p - 1)
            + ∑ p ∈ Q, (2 ^ emptyCountIn color W p - 1)
          ≤ ∑ p ∈ A, (2 ^ emptyCountIn colorN WA p - 1)
            + ∑ p ∈ B, (2 ^ emptyCountIn colorN WB p - 1)
            + ∑ p ∈ Q, ((2 ^ emptyCountIn colorN WA p - 1)
              + (2 ^ emptyCountIn colorN WB p - 1) + 1) := by
        refine add_le_add
          (add_le_add (Finset.sum_le_sum hbA) (Finset.sum_le_sum hbB))
          (Finset.sum_le_sum hbQ)
      have hQsum1 : ∑ p ∈ Q, ((2 ^ emptyCountIn colorN WA p - 1)
            + (2 ^ emptyCountIn colorN WB p - 1) + 1)
          = ∑ p ∈ Q, (2 ^ emptyCountIn colorN WA p - 1)
            + ∑ p ∈ Q, (2 ^ emptyCountIn colorN WB p - 1) + Q.card := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        rw [Finset.sum_const]
        simp
      have hstep3 : ∑ p ∈ A, (2 ^ emptyCountIn colorN WA p - 1)
            + ∑ p ∈ B, (2 ^ emptyCountIn colorN WB p - 1)
            + ∑ p ∈ Q, ((2 ^ emptyCountIn colorN WA p - 1)
              + (2 ^ emptyCountIn colorN WB p - 1) + 1)
          = ∑ p ∈ WA, (2 ^ emptyCountIn colorN WA p - 1)
            + ∑ p ∈ WB, (2 ^ emptyCountIn colorN WB p - 1) + Q.card := by
        have h1 : ∑ p ∈ A, (2 ^ emptyCountIn colorN WA p - 1)
            + ∑ p ∈ Q, (2 ^ emptyCountIn colorN WA p - 1)
          = ∑ p ∈ WA, (2 ^ emptyCountIn colorN WA p - 1) := by
          calc ∑ p ∈ A, (2 ^ emptyCountIn colorN WA p - 1)
              + ∑ p ∈ Q, (2 ^ emptyCountIn colorN WA p - 1)
              = ∑ p ∈ A ∪ Q, (2 ^ emptyCountIn colorN WA p - 1) :=
                (Finset.sum_union hAQ).symm
            _ = ∑ p ∈ WA, (2 ^ emptyCountIn colorN WA p - 1) := by rw [hWAeq]
        have h2 : ∑ p ∈ B, (2 ^ emptyCountIn colorN WB p - 1)
            + ∑ p ∈ Q, (2 ^ emptyCountIn colorN WB p - 1)
          = ∑ p ∈ WB, (2 ^ emptyCountIn colorN WB p - 1) := by
          calc ∑ p ∈ B, (2 ^ emptyCountIn colorN WB p - 1)
              + ∑ p ∈ Q, (2 ^ emptyCountIn colorN WB p - 1)
              = ∑ p ∈ B ∪ Q, (2 ^ emptyCountIn colorN WB p - 1) :=
                (Finset.sum_union hBQ).symm
            _ = ∑ p ∈ WB, (2 ^ emptyCountIn colorN WB p - 1) := by rw [hWBeq]
        rw [hQsum1]
        omega
      have hstep4 : ∑ p ∈ WA, (2 ^ emptyCountIn colorN WA p - 1)
            + ∑ p ∈ WB, (2 ^ emptyCountIn colorN WB p - 1) + Q.card
          ≤ (2 ^ n - WA.card) + (2 ^ n - WB.card) + Q.card := by
        refine add_le_add (add_le_add hihA hihB) le_rfl
      have hlast : (2 ^ n - WA.card) + (2 ^ n - WB.card) + Q.card = k := by
        have h4 : W.card + k = 2 ^ (n + 1) := hN
        have h5 : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by
          rw [pow_succ]
          ring
        omega
      calc ∑ p ∈ W, (2 ^ emptyCountIn color W p - 1)
          = ∑ p ∈ A, (2 ^ emptyCountIn color W p - 1)
            + ∑ p ∈ B, (2 ^ emptyCountIn color W p - 1)
            + ∑ p ∈ Q, (2 ^ emptyCountIn color W p - 1) := hsplit
        _ ≤ ∑ p ∈ A, (2 ^ emptyCountIn colorN WA p - 1)
            + ∑ p ∈ B, (2 ^ emptyCountIn colorN WB p - 1)
            + ∑ p ∈ Q, ((2 ^ emptyCountIn colorN WA p - 1)
              + (2 ^ emptyCountIn colorN WB p - 1) + 1) := hstep2
        _ = ∑ p ∈ WA, (2 ^ emptyCountIn colorN WA p - 1)
            + ∑ p ∈ WB, (2 ^ emptyCountIn colorN WB p - 1) + Q.card := hstep3
        _ ≤ (2 ^ n - WA.card) + (2 ^ n - WB.card) + Q.card := hstep4
        _ = k := hlast

/-! ## Geometric foundations -/

/-- `2 * n < 2 ^ n` for `n ≥ 3`. -/
lemma two_pow_gt_two_mul {n : ℕ} (hn : 3 ≤ n) : 2 * n < 2 ^ n := by
  have h : ∀ m : ℕ, 3 ≤ m → 2 * m + 2 ≤ 2 ^ m := by
    intro m hm
    induction m with
    | zero => omega
    | succ k ih =>
      rcases Nat.lt_or_ge k 3 with hk | hk
      · have hk2 : k = 2 := by omega
        subst hk2
        norm_num
      · have h1 := ih hk
        have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
        omega
  have h2 := h n hn
  omega

/-- The Erdős–Szekeres value is below `π`. -/
lemma theta_lt_pi {n : ℕ} (hn : 3 ≤ n) :
    (1 - 1 / (n : ℝ)) * π < π := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  have h2 : (1 - 1 / (n : ℝ)) * π < 1 * π := mul_lt_mul_of_pos_right (by linarith) Real.pi_pos
  linarith

/-- A `Finset` of cardinality at least `3` contains three pairwise distinct
points. -/
lemma exists_three_distinct_sc {S : Finset ℂ} (hS : 3 ≤ S.card) :
    ∃ x ∈ S, ∃ z ∈ S, ∃ y ∈ S, x ≠ z ∧ z ≠ y ∧ x ≠ y := by
  have hne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hEmpty
    have hcard0 : S.card = 0 := Finset.card_eq_zero.mpr hEmpty
    omega
  obtain ⟨x, hx⟩ := hne
  have hcard₁ : (S.erase x).card = S.card - 1 := Finset.card_erase_of_mem hx
  have hne₁ : (S.erase x).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hEmpty
    have hcard0 : (S.erase x).card = 0 := Finset.card_eq_zero.mpr hEmpty
    omega
  obtain ⟨z, hz⟩ := hne₁
  have hz' : z ≠ x ∧ z ∈ S := Finset.mem_erase.mp hz
  have hcard₂ : ((S.erase x).erase z).card = (S.erase x).card - 1 :=
    Finset.card_erase_of_mem hz
  have hne₂ : ((S.erase x).erase z).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hEmpty
    have hcard0 : ((S.erase x).erase z).card = 0 := Finset.card_eq_zero.mpr hEmpty
    omega
  obtain ⟨y, hy⟩ := hne₂
  have hy' : y ≠ z ∧ y ∈ S.erase x := Finset.mem_erase.mp hy
  have hy'' : y ≠ x ∧ y ∈ S := Finset.mem_erase.mp hy'.2
  exact ⟨x, hx, z, hz'.2, y, hy''.2, hz'.1.symm, hy'.1.symm, hy''.1.symm⟩

/-- The strict angle bound forces general position. -/
lemma hgen_of_hangle_lt {n : ℕ} (hn : 3 ≤ n) {S : Finset ℂ}
    (hangle : ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
      EuclideanGeometry.angle p q r < (1 - 1 / (n : ℝ)) * π) :
    ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c →
      ¬ Collinear ℝ ({a, b, c} : Set ℂ) := by
  have hle : ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
      EuclideanGeometry.angle p q r ≤ (1 - 1 / (n : ℝ)) * π := fun p hp q hq r hr hpq hrq =>
    le_of_lt (hangle p hp q hq r hr hpq hrq)
  exact hgen_of_hangle hn hle

/-- Three distinct collinear points of a set determine a straight angle. -/
lemma exists_angle_eq_pi_of_collinear_finset {S : Finset ℂ} (hS : 3 ≤ S.card)
    (hcol : Collinear ℝ (↑S : Set ℂ)) :
    ∃ x ∈ S, ∃ z ∈ S, ∃ y ∈ S, x ≠ z ∧ y ≠ z ∧ x ≠ y ∧
      EuclideanGeometry.angle x z y = π := by
  obtain ⟨x, hx, z, hz, y, hy, hxz, hzy, hxy⟩ := exists_three_distinct_sc hS
  have hsub : ({x, z, y} : Set ℂ) ⊆ ↑S := by
    intro t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl | rfl
    · exact hx
    · exact hz
    · exact hy
  rcases exists_angle_eq_pi_of_collinear hxz hzy hxy (hcol.subset hsub) with h | h | h
  · exact ⟨x, hx, z, hz, y, hy, hxz, Ne.symm hzy, hxy, h⟩
  · exact ⟨z, hz, x, hx, y, hy, Ne.symm hxz, hxy.symm, hzy, h⟩
  · exact ⟨x, hx, y, hy, z, hz, hxy, hzy, hxz, h⟩

/-- It suffices to refute the extremal cardinality `2 ^ n - 1`. -/
lemma scb_of_no_extremal {n : ℕ} (hn : 3 ≤ n)
    (H : ∀ T : Finset ℂ, T.card = 2 ^ n - 1 →
      (∀ p ∈ T, ∀ q ∈ T, ∀ r ∈ T, p ≠ q → r ≠ q →
        EuclideanGeometry.angle p q r < (1 - 1 / (n : ℝ)) * π) → False) :
    StrictCountingBound n := by
  have h8 := two_pow_ge_eight' hn
  intro S hangle
  by_contra hcon
  rw [Nat.not_le] at hcon
  have hle : 2 ^ n - 1 ≤ S.card := by omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hle
  refine H T hTcard fun p hp q hq r hr hpq hrq => ?_
  exact hangle p (hTsub hp) q (hTsub hq) r (hTsub hr) hpq hrq


/-! ## Hull windows -/

/-- The cyclic successor is never the cyclic predecessor. -/
lemma finRotate_ne_symm {k : ℕ} (hk3 : 3 ≤ k) (i : Fin k) :
    finRotate k i ≠ (finRotate k).symm i := by
  intro h
  have h2 : finRotate k ((finRotate k).symm i) = i :=
    Equiv.apply_symm_apply (finRotate k) i
  rw [← h] at h2
  have h5 : ((finRotate k (finRotate k i) : Fin k) : ℕ) = (i : ℕ) :=
    congrArg (fun j : Fin k => (j : ℕ)) h2
  rw [finRotate_val, finRotate_val] at h5
  rw [Nat.mod_add_mod] at h5
  have h4 : ((i : ℕ) + 2) % k = (i : ℕ) := h5
  rcases Nat.lt_or_ge ((i : ℕ) + 2) k with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at h4
    omega
  · have hdiv : k * (((i : ℕ) + 2) / k) = 2 := by
      have h6 := Nat.mod_add_div ((i : ℕ) + 2) k
      rw [h4] at h6
      omega
    have hk2 : k ≤ 2 := by
      rcases Nat.eq_zero_or_pos (((i : ℕ) + 2) / k) with h0 | hp
      · rw [h0] at hdiv
        simp at hdiv
      · have hle : k ≤ k * (((i : ℕ) + 2) / k) := Nat.le_mul_of_pos_right _ hp
        omega
    omega

/-- The angle at `c` between two points given in polar form around `c`, with
the second direction obtained by adding `A ∈ [0, π)`. -/
lemma angle_polar_eq {a b c : ℂ} {r s θ A : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hA : 0 ≤ A) (hAπ : A < π)
    (ha : a - c = (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
    (hb : b - c = (s : ℂ) * Complex.exp (((θ + A : ℝ) : ℂ) * Complex.I)) :
    EuclideanGeometry.angle a c b = A := by
  have hbridge : EuclideanGeometry.angle a c b
      = InnerProductGeometry.angle (a - c) (b - c) := by
    simp [EuclideanGeometry.angle, vsub_eq_sub]
  rw [hbridge, ha, hb]
  rw [angle_eq_abs_arg (mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hr))
      (Complex.exp_ne_zero _))
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hs)) (Complex.exp_ne_zero _))]
  have hexp : (starRingEnd ℂ) ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
      * ((s : ℂ) * Complex.exp (((θ + A : ℝ) : ℂ) * Complex.I))
      = ((r * s : ℝ) : ℂ) * Complex.exp ((A : ℂ) * Complex.I) := by
    rw [map_mul, Complex.conj_ofReal]
    calc ((r : ℂ) * (starRingEnd ℂ) (Complex.exp ((θ : ℂ) * Complex.I)))
        * ((s : ℂ) * Complex.exp (((θ + A : ℝ) : ℂ) * Complex.I))
        = ((r * s : ℝ) : ℂ)
          * ((starRingEnd ℂ) (Complex.exp ((θ : ℂ) * Complex.I))
            * Complex.exp (((θ + A : ℝ) : ℂ) * Complex.I)) := by
          push_cast
          ring
      _ = ((r * s : ℝ) : ℂ) * Complex.exp ((A : ℂ) * Complex.I) := by
          rw [conj_exp_mul_exp]
  rw [hexp, arg_of_polar (mul_pos hr hs) (by linarith) (by linarith), abs_of_nonneg hA]

/-- **The hull window package.**  Along the cyclic enumeration of the extreme
points, every vertex carries a window of aperture `< π (1 - 1/n)` starting at
the direction to its cyclic successor and ending at the direction to its
cyclic predecessor. -/
lemma exists_hull_windows {n : ℕ} (hn : 3 ≤ n) {S : Finset ℂ}
    (hangle : ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
      EuclideanGeometry.angle p q r < (1 - 1 / (n : ℝ)) * π)
    (hgen : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c →
      ¬ Collinear ℝ ({a, b, c} : Set ℂ))
    {m : ℕ} (w : Fin m → ℂ)
    (hmem : ∀ i, w i ∈ extremeFinset S)
    (hsur : ∀ v ∈ extremeFinset S, ∃ i, w i = v)
    (hmono : StrictMono (fun i => Complex.arg (w i - szCentroid S)))
    (hm3 : 3 ≤ m) :
    ∃ θ A : Fin m → ℝ, (∀ i, 0 ≤ A i) ∧ (∀ i, A i < π) ∧
      (∀ i, A i < (1 - 1 / (n : ℝ)) * π) ∧
      (∀ i, ∀ q ∈ S, q ≠ w i → ∃ r t : ℝ, 0 < r ∧ 0 ≤ t ∧ t ≤ A i ∧
        q - w i = (r : ℂ) * Complex.exp (((θ i + t : ℝ) : ℂ) * Complex.I)) ∧
      (∀ i, w (finRotate m i) - w i
        = ((‖w (finRotate m i) - w i‖ : ℝ) : ℂ)
          * Complex.exp ((θ i : ℂ) * Complex.I)) ∧
      (∀ i, w ((finRotate m).symm i) - w i
        = ((‖w ((finRotate m).symm i) - w i‖ : ℝ) : ℂ)
          * Complex.exp (((θ i + A i : ℝ) : ℂ) * Complex.I)) := by
  classical
  have hk : 0 < m := by omega
  have hinj : Function.Injective w := fun x y hxy =>
    hmono.injective (show (fun j => Complex.arg (w j - szCentroid S)) x
      = (fun j => Complex.arg (w j - szCentroid S)) y from by simp only [hxy])
  have himg : Finset.univ.image w = extremeFinset S := by
    apply Finset.ext
    intro x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, -, rfl⟩
      exact hmem i
    · intro hx
      obtain ⟨i, hi⟩ := hsur x hx
      exact ⟨i, hi⟩
  have hcardm : (extremeFinset S).card = m := by
    rw [← himg, Finset.card_image_of_injective _ hinj, Finset.card_univ,
      Fintype.card_fin]
  have hEsub : extremeFinset S ⊆ S := fun p hp => mem_of_mem_extremeFinset hp
  have hS3 : 3 ≤ S.card := by
    have hle := Finset.card_le_card hEsub
    calc 3 ≤ m := hm3
      _ = (extremeFinset S).card := hcardm.symm
      _ ≤ S.card := hle
  have hhex : ∀ i, ∃ q ∈ S, q ≠ w i := by
    intro i
    obtain ⟨a, ha, b, hb, c, hc, hab, hbc, hac⟩ := exists_three_distinct_sc hS3
    by_cases hac' : a = w i
    · exact ⟨c, hc, by rw [← hac']; exact Ne.symm hac⟩
    · exact ⟨a, ha, hac'⟩
  have hwin_ex : ∀ i : Fin m, ∃ θ A : ℝ, 0 ≤ A ∧ A < π ∧
      (∀ q ∈ S, q ≠ w i → ∃ r t : ℝ, 0 < r ∧ 0 ≤ t ∧ t ≤ A ∧
        q - w i = (r : ℂ) * Complex.exp (((θ + t : ℝ) : ℂ) * Complex.I)) ∧
      (∃ a ∈ S, a ≠ w i ∧ a - w i = ((‖a - w i‖ : ℝ) : ℂ)
          * Complex.exp ((θ : ℂ) * Complex.I)) ∧
      (∃ b ∈ S, b ≠ w i ∧ b - w i = ((‖b - w i‖ : ℝ) : ℂ)
          * Complex.exp (((θ + A : ℝ) : ℂ) * Complex.I)) := fun i =>
    exists_window_at_extreme (mem_of_mem_extremeFinset (hmem i)) (hhex i)
      (mem_extremeFinset.mp (hmem i))
  choose θ A hA0 hAπ hwin haform hbform using hwin_ex
  refine ⟨θ, A, hA0, hAπ, ?_, hwin, ?_, ?_⟩
  · intro i
    obtain ⟨a, haS, hav, haform'⟩ := haform i
    obtain ⟨b, hbS, hbv, hbform'⟩ := hbform i
    have hang : EuclideanGeometry.angle a (w i) b = A i :=
      angle_polar_eq (r := ‖a - w i‖) (s := ‖b - w i‖) (θ := θ i) (A := A i)
        (norm_pos_iff.mpr (sub_ne_zero.mpr hav))
        (norm_pos_iff.mpr (sub_ne_zero.mpr hbv))
        (hA0 i) (hAπ i) haform' hbform'
    have hlt := hangle a haS (w i) (mem_of_mem_extremeFinset (hmem i)) b hbS
      hav hbv
    rwa [hang] at hlt
  · intro i
    obtain ⟨a, haS, hav, haform'⟩ := haform i
    have hsu : w (finRotate m i) = a :=
      succ_eq_window_start hS3 hgen w hmem hsur hmono hk hm3 i haS hav (hAπ i)
        (hwin i) haform'
    rw [hsu]
    exact haform'
  · intro i
    obtain ⟨b, hbS, hbv, hbform'⟩ := hbform i
    have hpr : w ((finRotate m).symm i) = b :=
      pred_eq_window_end hS3 hgen w hmem hsur hmono hk hm3 i hbS hbv (hAπ i)
        (hwin i) hbform'
    rw [hpr]
    exact hbform'

/-! ## Hull size -/

/-- The real part of `conj (e^{iθ}) * (q - v)`, in polar terms. -/
lemma re_conj_exp_mul_polar {v q : ℂ} {θ t r : ℝ}
    (h : q - v = (r : ℂ) * Complex.exp (((θ + t : ℝ) : ℂ) * Complex.I)) :
    ((starRingEnd ℂ) (Complex.exp ((θ : ℂ) * Complex.I)) * (q - v)).re
      = r * Real.cos t := by
  have hkey : (starRingEnd ℂ) (Complex.exp ((θ : ℂ) * Complex.I)) * (q - v)
      = ((r : ℝ) : ℂ) * Complex.exp ((t : ℂ) * Complex.I) := by
    rw [h, ← conj_exp_mul_exp θ t]
    ring
  rw [hkey, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-- The colour of a direction given in polar form is the integer sector
index modulo `n`. -/
lemma dirIndex_polar_eq {n : ℕ} (hn : 0 < n) {r s : ℝ} (hr : 0 < r)
    {z : ℂ} (hform : z = (r : ℂ) * Complex.exp ((s : ℂ) * Complex.I)) :
    dirIndex n z = ((⌊(n : ℝ) * s / π⌋ : ℤ) % ((n : ℤ))).toNat := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  obtain ⟨m, hα⟩ : ∃ m : ℤ, s - 2 * π * m ∈ Set.Ioc (-π) π := by
    have hfr : s - 2 * π * (⌊s / (2 * π)⌋ : ℝ) = 2 * π * Int.fract (s / (2 * π)) := by
      have h1 := Int.floor_add_fract (s / (2 * π))
      have hπpos : (0 : ℝ) < π := Real.pi_pos
      have h2 : (2 * π) * ((⌊s / (2 * π)⌋ : ℝ) + Int.fract (s / (2 * π))) = s := by
        rw [h1]
        field_simp
      have h3 : (2 * π) * (⌊s / (2 * π)⌋ : ℝ) + (2 * π) * Int.fract (s / (2 * π)) = s := by
        rw [← mul_add]
        exact h2
      linarith
    have h0 : 0 ≤ s - 2 * π * (⌊s / (2 * π)⌋ : ℝ) := by
      rw [hfr]
      have hf := Int.fract_nonneg (s / (2 * π))
      nlinarith [hf, Real.pi_pos]
    have hlt : s - 2 * π * (⌊s / (2 * π)⌋ : ℝ) < 2 * π := by
      rw [hfr]
      have hf := Int.fract_lt_one (s / (2 * π))
      nlinarith [hf, Real.pi_pos]
    by_cases hle : s - 2 * π * (⌊s / (2 * π)⌋ : ℝ) ≤ π
    · exact ⟨⌊s / (2 * π)⌋, ⟨by linarith [h0, Real.pi_pos], hle⟩⟩
    · have hgt : π < s - 2 * π * (⌊s / (2 * π)⌋ : ℝ) := lt_of_not_ge hle
      refine ⟨⌊s / (2 * π)⌋ + 1, ⟨?_, ?_⟩⟩
      · have heq : s - 2 * π * ((⌊s / (2 * π)⌋ : ℤ) + 1)
          = (s - 2 * π * (⌊s / (2 * π)⌋ : ℝ)) - 2 * π := by
          push_cast
          ring
        push_cast
        rw [heq]
        linarith [hgt, Real.pi_pos]
      · have heq : s - 2 * π * ((⌊s / (2 * π)⌋ : ℤ) + 1)
          = (s - 2 * π * (⌊s / (2 * π)⌋ : ℝ)) - 2 * π := by
          push_cast
          ring
        push_cast
        rw [heq]
        linarith [hlt]
  have hexp : Complex.exp ((s : ℂ) * Complex.I)
      = Complex.exp (((s - 2 * π * m : ℝ) : ℂ) * Complex.I) := by
    have h4 : ((s : ℝ) : ℂ) = ((s - 2 * π * m + 2 * π * m : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h4]
    exact exp_add_int_two_pi (s - 2 * π * m) m
  have hz : z = (r : ℂ) * Complex.exp (((s - 2 * π * m : ℝ) : ℂ) * Complex.I) := by
    rw [hform, hexp]
  have harg : Complex.arg z = s - 2 * π * m := by
    rw [hz]
    exact arg_of_polar hr hα.1 hα.2
  unfold dirIndex
  rw [harg]
  have hfract : Int.fract ((s - 2 * π * m : ℝ) / π) = Int.fract (s / π) := by
    rw [Int.fract_eq_fract]
    refine ⟨-2 * m, ?_⟩
    have hπ0 : (0 : ℝ) ≠ π := by
      have := Real.pi_pos
      linarith
    field_simp
    push_cast
    ring
  rw [hfract]
  have hsplit : ⌊(n : ℝ) * s / π⌋ = (n : ℤ) * ⌊s / π⌋ + ⌊(n : ℝ) * Int.fract (s / π)⌋ := by
    have h1 : (n : ℝ) * s / π = (n : ℝ) * (s / π) := by ring
    have h2 : (n : ℝ) * (s / π) = (n : ℝ) * (⌊s / π⌋ + Int.fract (s / π)) := by
      congr 1
      exact (Int.floor_add_fract (s / π)).symm
    have h3 : (n : ℝ) * (⌊s / π⌋ + Int.fract (s / π))
        = (n : ℝ) * Int.fract (s / π) + ((n : ℤ) * ⌊s / π⌋ : ℤ) := by
      push_cast
      ring
    rw [h1, h2, h3, Int.floor_add_intCast]
    push_cast
    ring
  have hbn : 0 ≤ ⌊(n : ℝ) * Int.fract (s / π)⌋ ∧ ⌊(n : ℝ) * Int.fract (s / π)⌋ < (n : ℤ) := by
    have hf0 := Int.fract_nonneg (s / π)
    have hf1 := Int.fract_lt_one (s / π)
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    refine ⟨Int.floor_nonneg.mpr ?_, Int.floor_lt.mpr ?_⟩
    · nlinarith [hf0, hn']
    · simpa using mul_lt_mul_of_pos_left hf1 hn'
  rw [hsplit]
  have hmod : (((n : ℤ) * ⌊s / π⌋ + ⌊(n : ℝ) * Int.fract (s / π)⌋ : ℤ) % (n : ℤ))
      = ⌊(n : ℝ) * Int.fract (s / π)⌋ := by
    rw [Int.add_comm, Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt hbn.1 hbn.2
  rw [hmod]

/-- Expanding `conj (e^{iA}) * Z` using the polar form of `Z`. -/
lemma conj_exp_z_polar {Z : ℂ} {A : ℝ} :
    (starRingEnd ℂ) (Complex.exp (((A : ℝ) : ℂ) * Complex.I)) * Z
      = ((‖Z‖ : ℝ) : ℂ) * Complex.exp ((((Complex.arg Z - A : ℝ) : ℂ) * Complex.I)) := by
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I Z]
  have hreorder : (starRingEnd ℂ) (Complex.exp (((A : ℝ) : ℂ) * Complex.I))
      * (((‖Z‖ : ℝ) : ℂ) * Complex.exp (((Complex.arg Z : ℝ) : ℂ) * Complex.I))
    = ((‖Z‖ : ℝ) : ℂ) * ((starRingEnd ℂ) (Complex.exp (((A : ℝ) : ℂ) * Complex.I))
      * Complex.exp (((Complex.arg Z : ℝ) : ℂ) * Complex.I)) := by
    ring
  have hconj : (starRingEnd ℂ) (Complex.exp (((A : ℝ) : ℂ) * Complex.I))
      = Complex.exp (((-A : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have hex : Complex.exp (((-A : ℝ) : ℂ) * Complex.I)
      * Complex.exp (((Complex.arg Z : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((((Complex.arg Z - A : ℝ) : ℂ) * Complex.I)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hreorder, hconj, hex]

/-- If `sin (φ - A) ≤ 0` and `cos (φ - A / 2) > 0` with `φ ≤ π` and `0 ≤ A`,
then `φ ≤ A`. -/
lemma le_of_sin_nonpos {φ A : ℝ} (hφπ : φ ≤ π) (hA0 : 0 ≤ A)
    (hcos : 0 < Real.cos (φ - A / 2))
    (hsin : Real.sin (φ - A) ≤ 0) : φ ≤ A := by
  by_contra h
  have hgt : A < φ := lt_of_not_ge h
  have h1 : 0 < φ - A := by linarith
  have h2 : φ - A ≤ π := by linarith
  by_cases heq : φ - A = π
  · have hφπ' : φ = π := by linarith [heq, hφπ, hA0]
    have hA0' : A = 0 := by linarith [heq, hφπ', hA0]
    have hsplit : φ - A / 2 = π := by rw [hφπ', hA0']; ring
    rw [hsplit, Real.cos_pi] at hcos
    linarith
  · have hlt : φ - A < π := lt_of_le_of_ne h2 heq
    have hsinpos : 0 < Real.sin (φ - A) := Real.sin_pos_of_pos_of_lt_pi h1 hlt
    linarith [hsin]

/-- The direction from a point `v ∈ S` to the centroid lies in the window at
`v`, as a polar direction with parameter `t ∈ [0, A]`. -/
lemma centroid_dir_in_window {S : Finset ℂ} {v : ℂ} (hv : v ∈ S)
    (hcard : 1 < S.card)
    {θ A : ℝ} (hA0 : 0 ≤ A) (hAπ : A < π)
    (hwin : ∀ q ∈ S, q ≠ v → ∃ r t : ℝ, 0 < r ∧ 0 ≤ t ∧ t ≤ A ∧
      q - v = (r : ℂ) * Complex.exp (((θ + t : ℝ) : ℂ) * Complex.I)) :
    ∃ r t : ℝ, 0 < r ∧ 0 ≤ t ∧ t ≤ A ∧
      szCentroid S - v = (r : ℂ) * Complex.exp (((θ + t : ℝ) : ℂ) * Complex.I) := by
  classical
  have hneW : (S.erase v).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro h0
    have h1 : (S.erase v).card = 0 := Finset.card_eq_zero.mpr h0
    have h2 := Finset.card_erase_of_mem hv
    omega
  have hchoice : ∀ p ∈ S.erase v, ∃ r t : ℝ, 0 < r ∧ 0 ≤ t ∧ t ≤ A ∧
      p - v = (r : ℂ) * Complex.exp (((θ + t : ℝ) : ℂ) * Complex.I) := by
    intro p hp
    have h1 := Finset.mem_erase.mp hp
    exact hwin p h1.2 h1.1
  choose! r t hr ht0 htA hform using hchoice
  have hcval : szCentroid S - v
      = ∑ p ∈ S.erase v, ((1 / (S.card : ℝ) : ℝ) : ℂ) • (p - v) := by
    have hc : (S.card : ℂ) ≠ 0 := by
      have : S.card ≠ 0 := by omega
      exact_mod_cast this
    have hrhs : ∑ p ∈ S.erase v, ((1 / (S.card : ℝ) : ℝ) : ℂ) • (p - v)
        = ((1 / (S.card : ℝ) : ℝ) : ℂ) • ∑ p ∈ S.erase v, (p - v) :=
          (Finset.smul_sum).symm
    have hsplit : ∑ p ∈ S.erase v, (p - v) = ∑ p ∈ S, (p - v) := by
      refine Finset.sum_subset (Finset.erase_subset v S) ?_
      intro x hx hnot
      have hxe : x = v := by
        by_contra hxc
        exact hnot (Finset.mem_erase.mpr ⟨hxc, hx⟩)
      rw [hxe, sub_self]
    rw [szCentroid, hrhs, hsplit, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    push_cast
    simp only [smul_eq_mul]
    field_simp
  set Z : ℂ := (starRingEnd ℂ) (Complex.exp ((θ : ℂ) * Complex.I))
      * (szCentroid S - v) with hZ
  have hZsum : Z = ∑ p ∈ S.erase v,
      ((1 / (S.card : ℝ) : ℝ) : ℂ) * ((r p : ℂ) * Complex.exp ((t p : ℂ) * Complex.I)) := by
    rw [hZ, hcval, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hstep : (starRingEnd ℂ) (Complex.exp ((θ : ℂ) * Complex.I))
        * (((1 / (S.card : ℝ) : ℝ) : ℂ) * ((r p : ℂ)
          * Complex.exp (((θ + t p : ℝ) : ℂ) * Complex.I)))
      = ((1 / (S.card : ℝ) : ℝ) : ℂ)
        * ((starRingEnd ℂ) (Complex.exp ((θ : ℂ) * Complex.I))
          * ((r p : ℂ) * Complex.exp (((θ + t p : ℝ) : ℂ) * Complex.I))) := by ring
    have hkey : (starRingEnd ℂ) (Complex.exp ((θ : ℂ) * Complex.I))
        * ((r p : ℂ) * Complex.exp (((θ + t p : ℝ) : ℂ) * Complex.I))
        = (r p : ℂ) * Complex.exp ((t p : ℂ) * Complex.I) := by
      rw [← conj_exp_mul_exp θ (t p)]
      ring
    rw [smul_eq_mul, hform p hp, hstep, hkey]
  have hwc : 0 < 1 / (S.card : ℝ) := by
    have h2 : (0:ℝ) < S.card := by
      have : 0 < S.card := by omega
      exact_mod_cast this
    exact div_pos one_pos h2
  have hpos : ∀ p ∈ S.erase v, 0 < (1 / (S.card : ℝ)) * r p * Real.cos (t p - A / 2) := by
    intro p hp
    have htp : t p ≤ A := htA p hp
    have ht0p : 0 ≤ t p := ht0 p hp
    have hπ : (0:ℝ) < π := Real.pi_pos
    have hcospos : 0 < Real.cos (A / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
    have hab : |t p - A / 2| ≤ A / 2 := by rw [abs_le]; exact ⟨by linarith, by linarith⟩
    have hmono : Real.cos (A / 2) ≤ Real.cos (t p - A / 2) := by
      have h1 : Real.cos (A / 2) ≤ Real.cos |t p - A / 2| :=
        Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [hAπ, hπ]) hab
      rwa [Real.cos_abs] at h1
    have hrp : 0 < r p := hr p hp
    have h1 : 0 < (1 / (S.card : ℝ)) * r p := by nlinarith
    have h2 : 0 < (1 / (S.card : ℝ)) * r p * Real.cos (A / 2) := by nlinarith [h1, hcospos]
    nlinarith [h2, hmono]
  have hhalf : 0 < ((starRingEnd ℂ)
      (Complex.exp (((A / 2 : ℝ) : ℂ) * Complex.I)) * Z).re := by
    have hmove : (starRingEnd ℂ) (Complex.exp (((A / 2 : ℝ) : ℂ) * Complex.I)) * Z
        = ∑ p ∈ S.erase v, ((1 / (S.card : ℝ) : ℝ) : ℂ)
            * ((starRingEnd ℂ) (Complex.exp (((A / 2 : ℝ) : ℂ) * Complex.I))
              * ((r p : ℂ) * Complex.exp ((t p : ℂ) * Complex.I))) := by
      rw [hZsum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun p hp => by ring
    have hterm : ∀ p ∈ S.erase v,
        0 < (((1 / (S.card : ℝ) : ℝ) : ℂ)
          * ((starRingEnd ℂ) (Complex.exp (((A / 2 : ℝ) : ℂ) * Complex.I))
            * ((r p : ℂ) * Complex.exp ((t p : ℂ) * Complex.I)))).re := by
      intro p hp
      have hex : ((A / 2 + (t p - A / 2 : ℝ) : ℝ) : ℂ) * Complex.I
          = (t p : ℂ) * Complex.I := by
        push_cast; ring
      have hbr' : (r p : ℂ) * Complex.exp ((t p : ℂ) * Complex.I) - 0
          = (r p : ℂ) * Complex.exp (((A / 2 + (t p - A / 2 : ℝ) : ℝ) * Complex.I)) := by
        rw [sub_zero, hex]
      have h2 := re_conj_exp_mul_polar (θ := A / 2) (t := t p - A / 2) (r := r p) hbr'
      rw [sub_zero] at h2
      rw [Complex.re_ofReal_mul, h2, ← mul_assoc]
      exact hpos p hp
    obtain ⟨p0, hp0⟩ := hneW
    rw [hmove, Complex.re_sum]
    exact Finset.sum_pos' (fun p hp => le_of_lt (hterm p hp)) ⟨p0, hp0, hterm p0 hp0⟩
  have hZ0 : Z ≠ 0 := by
    intro h0
    rw [h0, mul_zero, Complex.zero_re] at hhalf
    linarith
  have hRpos : (0:ℝ) < ‖Z‖ := norm_pos_iff.mpr hZ0
  have hWpolar : Z = ((‖Z‖ : ℝ) : ℂ) * Complex.exp (((Complex.arg Z : ℝ) : ℂ) * Complex.I) :=
    (Complex.norm_mul_exp_arg_mul_I Z).symm
  have him0 : 0 ≤ Z.im := by
    rw [hZsum, Complex.im_sum]
    refine Finset.sum_nonneg fun p hp => ?_
    have h3 : ((r p : ℂ) * Complex.exp ((t p : ℂ) * Complex.I)).im = r p * Real.sin (t p) := by
      rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
    rw [Complex.im_ofReal_mul, h3]
    refine mul_nonneg (le_of_lt hwc) (mul_nonneg (hr p hp).le ?_)
    exact Real.sin_nonneg_of_nonneg_of_le_pi (ht0 p hp) (by linarith [htA p hp, hAπ])
  have himA : ((starRingEnd ℂ) (Complex.exp (((A : ℝ) : ℂ) * Complex.I)) * Z).im ≤ 0 := by
    rw [hZsum, Finset.mul_sum, Complex.im_sum]
    refine Finset.sum_nonpos fun p hp => ?_
    have hex : ((A + (t p - A : ℝ) : ℝ) : ℂ) * Complex.I
        = (t p : ℂ) * Complex.I := by
      push_cast; ring
    have hbr' : (r p : ℂ) * Complex.exp ((t p : ℂ) * Complex.I) - 0
        = (r p : ℂ) * Complex.exp (((A + (t p - A : ℝ) : ℝ) * Complex.I)) := by
      rw [sub_zero, hex]
    have h2 := im_conj_exp_mul_polar (θ := A) (t := t p - A) (r := r p) hbr'
    rw [sub_zero] at h2
    have hmove : (starRingEnd ℂ) (Complex.exp (((A : ℝ) : ℂ) * Complex.I))
        * (((1 / (S.card : ℝ) : ℝ) : ℂ) * ((r p : ℂ) * Complex.exp ((t p : ℂ) * Complex.I)))
      = ((1 / (S.card : ℝ) : ℝ) : ℂ)
        * ((starRingEnd ℂ) (Complex.exp (((A : ℝ) : ℂ) * Complex.I))
          * ((r p : ℂ) * Complex.exp ((t p : ℂ) * Complex.I))) := by ring
    rw [hmove, Complex.im_ofReal_mul, h2]
    have hs : Real.sin (t p - A) ≤ 0 := by
      have h1 : 0 ≤ A - t p := by linarith [ht0 p hp, htA p hp]
      have h2' : A - t p ≤ π := by linarith [ht0 p hp, htA p hp, hAπ]
      have h3 : 0 ≤ Real.sin (A - t p) := Real.sin_nonneg_of_nonneg_of_le_pi h1 h2'
      have h4 := Real.sin_neg (A - t p)
      rw [neg_sub] at h4
      linarith
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hwc)
      (mul_nonpos_of_nonneg_of_nonpos (hr p hp).le hs)
  have hsinle : ‖Z‖ * Real.sin (Complex.arg Z - A) ≤ 0 := by
    have hgoal : ((starRingEnd ℂ) (Complex.exp (((A : ℝ) : ℂ) * Complex.I)) * Z).im
        = ‖Z‖ * Real.sin (Complex.arg Z - A) := by
      rw [conj_exp_z_polar, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
    rw [← hgoal]
    exact himA
  have harg0 : 0 ≤ Complex.arg Z := Complex.arg_nonneg_iff.mpr him0
  have hargπ : Complex.arg Z ≤ π := Complex.arg_le_pi Z
  have hcospos : 0 < Real.cos (Complex.arg Z - A / 2) := by
    have hre : ((starRingEnd ℂ) (Complex.exp (((A / 2 : ℝ) : ℂ) * Complex.I)) * Z).re
        = ‖Z‖ * Real.cos (Complex.arg Z - A / 2) := by
      rw [conj_exp_z_polar, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
    nlinarith [hre, hhalf, hRpos]
  have hsin0 : Real.sin (Complex.arg Z - A) ≤ 0 := by
    have h2 : ‖Z‖ * Real.sin (Complex.arg Z - A) ≤ ‖Z‖ * 0 := by
      rw [mul_zero]; exact hsinle
    exact le_of_mul_le_mul_left h2 hRpos
  have hargA : Complex.arg Z ≤ A :=
    le_of_sin_nonpos hargπ hA0 hcospos hsin0
  refine ⟨‖Z‖, Complex.arg Z, hRpos, harg0, hargA, ?_⟩
  have hcval' : szCentroid S - v = Complex.exp (((θ : ℂ) * Complex.I)) * Z := by
    rw [hZ]
    have hunit : Complex.exp (((θ : ℂ) * Complex.I))
        * (starRingEnd ℂ) (Complex.exp ((θ : ℂ) * Complex.I)) = 1 := by
      have h1 : (starRingEnd ℂ) (Complex.exp ((θ : ℂ) * Complex.I))
          = Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) := by
        rw [← Complex.exp_conj]
        congr 1
        rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
        push_cast
        ring
      rw [h1, ← Complex.exp_add]
      have h2 : ((θ : ℂ) * Complex.I + ((-θ : ℝ) : ℂ) * Complex.I) = 0 := by push_cast; ring
      rw [h2, Complex.exp_zero]
    rw [← mul_assoc, hunit, one_mul]
  have hre : Complex.exp (((θ : ℂ) * Complex.I))
      * (((‖Z‖ : ℝ) : ℂ) * Complex.exp (((Complex.arg Z : ℝ) : ℂ) * Complex.I))
    = ((‖Z‖ : ℝ) : ℂ) * (Complex.exp (((θ : ℂ) * Complex.I))
      * Complex.exp (((Complex.arg Z : ℝ) : ℂ) * Complex.I)) := by ring
  have hexpadd : Complex.exp (((θ : ℂ) * Complex.I))
      * Complex.exp (((Complex.arg Z : ℝ) : ℂ) * Complex.I)
    = Complex.exp ((((θ + Complex.arg Z : ℝ) : ℂ) * Complex.I)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hcval']
  conv_lhs => rw [hWpolar]
  rw [hre, hexpadd]

/-! ## Hull isolation via sector-span pigeonhole -/

/-- The centroid difference as a weighted sum over the other points. -/
lemma szCentroid_sub {S : Finset ℂ} {v : ℂ} (hv : v ∈ S) (hne : S.card ≠ 0) :
    szCentroid S - v = ∑ p ∈ S.erase v, ((1 / (S.card : ℝ) : ℝ) : ℂ) • (p - v) := by
  have hc : (S.card : ℂ) ≠ 0 := by exact_mod_cast hne
  have hrhs : ∑ p ∈ S.erase v, ((1 / (S.card : ℝ) : ℝ) : ℂ) • (p - v)
      = ((1 / (S.card : ℝ) : ℝ) : ℂ) • ∑ p ∈ S.erase v, (p - v) :=
        (Finset.smul_sum).symm
  have hsplit : ∑ p ∈ S.erase v, (p - v) = ∑ p ∈ S, (p - v) := by
    refine Finset.sum_subset (Finset.erase_subset v S) ?_
    intro x hx hnot
    have hxe : x = v := by
      by_contra hxc
      exact hnot (Finset.mem_erase.mpr ⟨hxc, hx⟩)
    rw [hxe, sub_self]
  rw [szCentroid, hrhs, hsplit, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  push_cast
  simp only [smul_eq_mul]
  field_simp

/-- Imaginary part of a rotated centroid difference, as a weighted sum. -/
lemma im_conj_smul_sum {S : Finset ℂ} {v : ℂ} (hv : v ∈ S) (hne : S.card ≠ 0)
    (z : ℂ) :
    (z * (szCentroid S - v)).im
      = (1 / (S.card : ℝ)) * ∑ p ∈ S.erase v, (z * (p - v)).im := by
  have hsub := szCentroid_sub hv hne
  have hrotsum : z * (szCentroid S - v)
      = ∑ p ∈ S.erase v, ((1 / (S.card : ℝ) : ℝ) : ℂ) * (z * (p - v)) := by
    rw [hsub]
    simp only [smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p hp => by ring
  rw [hrotsum, Complex.im_sum]
  have h2 : ∀ p ∈ S.erase v, (((1 / (S.card : ℝ) : ℝ) : ℂ) * (z * (p - v))).im
      = (1 / (S.card : ℝ)) * (z * (p - v)).im := by
    intro p hp
    have h3 := Complex.mul_im ((1 / (S.card : ℝ) : ℝ) : ℂ) (z * (p - v))
    rw [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at h3
    exact h3
  rw [Finset.sum_congr rfl h2, ← Finset.mul_sum]

/-- Two distinct points of `S \ {v}` whose directions from `v` have the same
polar parameter are collinear with `v`. -/
lemma collinear_of_same_ray {v q₁ q₂ : ℂ} {θ : ℝ} {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (h₁ : q₁ - v = (r₁ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
    (h₂ : q₂ - v = (r₂ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) :
    Collinear ℝ ({q₁, v, q₂} : Set ℂ) := by
  have h₂' : q₂ - v = (r₂ : ℂ) * Complex.exp (((θ + 0 : ℝ) : ℂ) * Complex.I) := by
    rw [h₂, add_zero]
  have hang : EuclideanGeometry.angle q₁ v q₂ = 0 :=
    angle_polar_eq hr₁ hr₂ (by norm_num) (by linarith [Real.pi_pos]) h₁ h₂'
  exact EuclideanGeometry.collinear_of_angle_eq_zero hang

/-- If every other point of `S` lies on one ray from `v`, three points of `S`
are collinear — contradicting general position. -/
lemma not_all_same_ray {S : Finset ℂ} {v : ℂ} (hv : v ∈ S) (hcard : 2 < S.card)
    (hgen : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c →
      ¬ Collinear ℝ ({a, b, c} : Set ℂ))
    {θ : ℝ}
    (hform : ∀ p ∈ S, p ≠ v → ∃ r : ℝ, 0 < r ∧
      p - v = (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) :
    False := by
  have htwo : 1 < (S.erase v).card := by
    have h1 := Finset.card_erase_of_mem hv
    omega
  obtain ⟨q₁, hq₁, q₂, hq₂, hneq⟩ := Finset.one_lt_card.mp htwo
  obtain ⟨r₁, hr₁, h₁⟩ := hform q₁ (Finset.mem_erase.mp hq₁).2 (Finset.mem_erase.mp hq₁).1
  obtain ⟨r₂, hr₂, h₂⟩ := hform q₂ (Finset.mem_erase.mp hq₂).2 (Finset.mem_erase.mp hq₂).1
  exact hgen q₁ (Finset.mem_erase.mp hq₁).2 v hv q₂ (Finset.mem_erase.mp hq₂).2
    (Finset.mem_erase.mp hq₁).1 (Ne.symm (Finset.mem_erase.mp hq₂).1) hneq
    (collinear_of_same_ray hr₁ hr₂ h₁ h₂)

/-- A sine that vanishes at a point of `[0, π)` forces the point to be `0`. -/
lemma eq_zero_of_sin_eq_zero {x : ℝ} (h0 : 0 ≤ x) (hπ : x < π)
    (hs : Real.sin x = 0) : x = 0 := by
  have hπpos := Real.pi_pos
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hs
  have h0n : (0:ℤ) ≤ n := by
    have h2 : (0:ℝ) * π ≤ n * π := by linarith
    exact_mod_cast le_of_mul_le_mul_right h2 hπpos
  have h1n : n < 1 := by
    have h2 : n * π < (1:ℝ) * π := by linarith
    exact_mod_cast lt_of_mul_lt_mul_right h2 (le_of_lt hπpos)
  have hzero : n = 0 := by omega
  rw [← hn, hzero, Int.cast_zero, zero_mul]

/-- The direction from `v` to the centroid is *strictly* inside the window:
`0 < t < A`. -/
lemma centroid_dir_in_window_strict {S : Finset ℂ} {v : ℂ} (hv : v ∈ S)
    (hcard : 2 < S.card)
    (hgen : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c →
      ¬ Collinear ℝ ({a, b, c} : Set ℂ))
    {θ A : ℝ} (hA0 : 0 ≤ A) (hAπ : A < π)
    (hwin : ∀ q ∈ S, q ≠ v → ∃ r t : ℝ, 0 < r ∧ 0 ≤ t ∧ t ≤ A ∧
      q - v = (r : ℂ) * Complex.exp (((θ + t : ℝ) : ℂ) * Complex.I)) :
    ∃ r t : ℝ, 0 < r ∧ 0 < t ∧ t < A ∧
      szCentroid S - v = (r : ℂ) * Complex.exp (((θ + t : ℝ) : ℂ) * Complex.I) := by
  classical
  obtain ⟨ρ, τ, hρ, hτ0, hτA, hform⟩ :=
    centroid_dir_in_window hv (by omega) hA0 hAπ hwin
  refine ⟨ρ, τ, hρ, ?_, ?_, hform⟩
  · rcases lt_or_eq_of_le hτ0 with h | h
    · exact h
    · -- `τ = 0`: the rotated imaginary parts sum to zero, so every `t p = 0`.
      exfalso
      have hchoice : ∀ p ∈ S.erase v, ∃ r t : ℝ, 0 < r ∧ 0 ≤ t ∧ t ≤ A ∧
          p - v = (r : ℂ) * Complex.exp (((θ + t : ℝ) : ℂ) * Complex.I) := by
        intro p hp
        have h1 := Finset.mem_erase.mp hp
        exact hwin p h1.2 h1.1
      choose! r t hr ht0 htA hformp using hchoice
      set z : ℂ := (starRingEnd ℂ) (Complex.exp ((θ : ℂ) * Complex.I)) with hz
      have hterm : ∀ p ∈ S.erase v, (z * (p - v)).im = r p * Real.sin (t p) :=
        fun p hp => im_conj_exp_mul_polar (hformp p hp)
      have hnonneg : ∀ p ∈ S.erase v, 0 ≤ (z * (p - v)).im := by
        intro p hp
        rw [hterm p hp]
        exact mul_nonneg (le_of_lt (hr p hp))
          (Real.sin_nonneg_of_nonneg_of_le_pi (ht0 p hp) (by linarith [htA p hp, hAπ]))
      have himC := im_conj_smul_sum hv (by omega) z
      have himC0 : (z * (szCentroid S - v)).im = 0 := by
        rw [im_conj_exp_mul_polar hform, h.symm, Real.sin_zero, mul_zero]
      have hsum0 : ∑ p ∈ S.erase v, (z * (p - v)).im = 0 := by
        have h1 : (1 / (S.card : ℝ)) * ∑ p ∈ S.erase v, (z * (p - v)).im = 0 := by
          rw [← himC, himC0]
        have hpos : (1 / (S.card : ℝ)) ≠ 0 := by
          have h3 : (0:ℝ) < S.card := by
            exact_mod_cast (show 0 < S.card by omega)
          exact ne_of_gt (div_pos one_pos h3)
        exact mul_left_cancel₀ hpos (h1.trans (mul_zero _).symm)
      have htzero : ∀ p ∈ S.erase v, t p = 0 := by
        intro p hp
        have h3 : Real.sin (t p) = 0 := by
          have h4 := hterm p hp
          have h6 : (z * (p - v)).im = 0 := by
            have h7 := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum0
            exact h7 p hp
          rw [h4] at h6
          have hρ0 : r p ≠ 0 := ne_of_gt (hr p hp)
          exact (mul_eq_zero.mp h6).resolve_left hρ0
        exact eq_zero_of_sin_eq_zero (ht0 p hp) (by linarith [htA p hp, hAπ]) h3
      apply not_all_same_ray hv hcard hgen (θ := θ)
      intro p hp hvp
      have hpe : p ∈ S.erase v := Finset.mem_erase.mpr ⟨hvp, hp⟩
      refine ⟨r p, hr p hpe, ?_⟩
      have h2 := hformp p hpe
      rw [htzero p hpe, add_zero] at h2
      exact h2
  · rcases lt_or_eq_of_le hτA with h | h
    · exact h
    · -- `τ = A`: rotate by `θ + A`; every `t p = A`.
      exfalso
      have hchoice : ∀ p ∈ S.erase v, ∃ r t : ℝ, 0 < r ∧ 0 ≤ t ∧ t ≤ A ∧
          p - v = (r : ℂ) * Complex.exp (((θ + t : ℝ) : ℂ) * Complex.I) := by
        intro p hp
        have h1 := Finset.mem_erase.mp hp
        exact hwin p h1.2 h1.1
      choose! r t hr ht0 htA hformp using hchoice
      set z : ℂ := (starRingEnd ℂ) (Complex.exp (((θ + A : ℝ) : ℂ) * Complex.I)) with hz
      have hterm : ∀ p ∈ S.erase v, (z * (p - v)).im = r p * Real.sin (t p - A) := by
        intro p hp
        have h' : p - v
            = (r p : ℂ) * Complex.exp ((((θ + A) + (t p - A) : ℝ) : ℂ) * Complex.I) := by
          rw [hformp p hp]
          push_cast
          ring
        exact im_conj_exp_mul_polar h'
      have hnonpos : ∀ p ∈ S.erase v, (z * (p - v)).im ≤ 0 := by
        intro p hp
        rw [hterm p hp]
        have h1 : 0 ≤ A - t p := by linarith [ht0 p hp, htA p hp]
        have h2 : A - t p ≤ π := by linarith [ht0 p hp, htA p hp, hAπ]
        have h3 : 0 ≤ Real.sin (A - t p) :=
          Real.sin_nonneg_of_nonneg_of_le_pi h1 h2
        have h4 := Real.sin_neg (A - t p)
        rw [neg_sub] at h4
        exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (hr p hp)) (by linarith)
      have himC := im_conj_smul_sum hv (by omega) z
      have himC0 : (z * (szCentroid S - v)).im = 0 := by
        have h' : szCentroid S - v
            = (ρ : ℂ) * Complex.exp ((((θ + A) + (τ - A) : ℝ) : ℂ) * Complex.I) := by
          rw [hform]
          push_cast
          ring
        rw [im_conj_exp_mul_polar h', h, sub_self, Real.sin_zero, mul_zero]
      have hsum0 : ∑ p ∈ S.erase v, (z * (p - v)).im = 0 := by
        have h1 : (1 / (S.card : ℝ)) * ∑ p ∈ S.erase v, (z * (p - v)).im = 0 := by
          rw [← himC, himC0]
        have hpos : (1 / (S.card : ℝ)) ≠ 0 := by
          have h3 : (0:ℝ) < S.card := by
            exact_mod_cast (show 0 < S.card by omega)
          exact ne_of_gt (div_pos one_pos h3)
        exact mul_left_cancel₀ hpos (h1.trans (mul_zero _).symm)
      have hall0 : ∀ p ∈ S.erase v, (z * (p - v)).im = 0 := by
        intro p hp
        have hle := hnonpos p hp
        by_contra hne0
        have hlt : (z * (p - v)).im < 0 := by
          rcases lt_or_eq_of_le hle with hlt | hlt
          · exact hlt
          · exact absurd hlt hne0
        have hsumlt : ∑ q ∈ S.erase v, (z * (q - v)).im < 0 := by
          have h := Finset.sum_lt_sum (fun q hq => hnonpos q hq) ⟨p, hp, hlt⟩
          rwa [Finset.sum_const_zero] at h
        linarith [hsum0]
      have htAeq : ∀ p ∈ S.erase v, t p = A := by
        intro p hp
        have h3 : Real.sin (t p - A) = 0 := by
          have h4 := hterm p hp
          have h6 := hall0 p hp
          rw [h4] at h6
          have hρ0 : r p ≠ 0 := ne_of_gt (hr p hp)
          exact (mul_eq_zero.mp h6).resolve_left hρ0
        have hlo : -π < t p - A := by linarith [ht0 p hp, htA p hp, hAπ]
        have hhi : t p - A ≤ 0 := by linarith [htA p hp]
        obtain ⟨n, hx⟩ := Real.sin_eq_zero_iff.mp h3
        have hπ := Real.pi_pos
        have hn0 : n = 0 := by
          have hlt2 : (-1:ℤ) < n := by
            have h1 : -(1:ℝ) * π < n * π := by linarith
            exact_mod_cast lt_of_mul_lt_mul_right h1 (le_of_lt hπ)
          have hle : n ≤ 0 := by
            have h1 : n * π ≤ (0:ℝ) * π := by linarith
            exact_mod_cast le_of_mul_le_mul_right h1 hπ
          omega
        have hzero : t p - A = 0 := by rw [← hx, hn0, Int.cast_zero, zero_mul]
        linarith
      apply not_all_same_ray hv hcard hgen (θ := θ + A)
      intro p hp hvp
      have hpe : p ∈ S.erase v := Finset.mem_erase.mpr ⟨hvp, hp⟩
      refine ⟨r p, hr p hpe, ?_⟩
      have h2 := hformp p hpe
      rw [htAeq p hpe] at h2
      exact h2

/-- The window apertures of a convex hull sum to `mπ - 2π`. -/
lemma sum_window_apertures {S : Finset ℂ} {m : ℕ} (w : Fin m → ℂ)
    (hS3 : 3 ≤ S.card)
    (hgen : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c →
      ¬ Collinear ℝ ({a, b, c} : Set ℂ))
    (hmem : ∀ i, w i ∈ extremeFinset S)
    (hsur : ∀ v ∈ extremeFinset S, ∃ i, w i = v)
    (hmono : StrictMono (fun i => Complex.arg (w i - szCentroid S)))
    (hm3 : 3 ≤ m)
    {θ A : Fin m → ℝ}
    (hAπ : ∀ i, A i < π)
    (hsucc : ∀ i, w (finRotate m i) - w i
      = ((‖w (finRotate m i) - w i‖ : ℝ) : ℂ) * Complex.exp ((θ i : ℂ) * Complex.I))
    (hpred : ∀ i, w ((finRotate m).symm i) - w i
      = ((‖w ((finRotate m).symm i) - w i‖ : ℝ) : ℂ)
        * Complex.exp (((θ i + A i : ℝ) : ℂ) * Complex.I))
    (ht : ∀ i, ∃ r t : ℝ, 0 < r ∧ 0 < t ∧ t < A i ∧
      szCentroid S - w i = (r : ℂ) * Complex.exp (((θ i + t : ℝ) : ℂ) * Complex.I)) :
    ∑ i : Fin m, A i = (m : ℝ) * π - 2 * π := by
  classical
  have hk : 0 < m := by omega
  have hinj : Function.Injective w := fun x y hxy =>
    hmono.injective (show (fun j => Complex.arg (w j - szCentroid S)) x
      = (fun j => Complex.arg (w j - szCentroid S)) y from by simp only [hxy])
  have hne : ∀ i, w i ≠ w (finRotate m i) := by
    intro i h
    exact finRotate_ne_self hm3 i (hinj h).symm
  choose! ρ t hρ ht0 htA hform using ht
  have hrot : ∀ i : Fin m, ∃ μ : ℤ,
      θ (finRotate m i) + A (finRotate m i) = θ i + π + 2 * π * μ := by
    intro i
    have h1 := hpred (finRotate m i)
    rw [Equiv.symm_apply_apply] at h1
    exact edge_rotation_rule (v := w i) (v' := w (finRotate m i))
      (θ := θ i) (θ' := θ (finRotate m i)) (A' := A (finRotate m i))
      (ℓ := ‖w (finRotate m i) - w i‖) (ℓ' := ‖w i - w (finRotate m i)‖)
      (norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm (hne i))))
      (norm_pos_iff.mpr (sub_ne_zero.mpr (hne i))) (hsucc i) h1
  choose! μ hμ using hrot
  have hcyc : ∀ i : Fin m, cycAdv w (szCentroid S) i (finRotate m i)
      = π - A (finRotate m i) + t (finRotate m i) - t i := by
    intro i
    obtain ⟨h1, -⟩ := arg_conj_succ hS3 hgen w hmem hsur hmono hm3 i
    have harg := arg_conj_centroid_succ (v := w i) (v' := w (finRotate m i))
      (c := szCentroid S) (θ := θ i) (A := A i) (t := t i)
      (θ' := θ (finRotate m i)) (A' := A (finRotate m i)) (t' := t (finRotate m i))
      (ρ := ρ i) (ρ' := ρ (finRotate m i)) (m := μ i)
      (hAπ i) (hAπ (finRotate m i)) (ht0 i) (htA i) (ht0 (finRotate m i))
      (htA (finRotate m i)) (hform i) (hform (finRotate m i)) (hρ i) (hρ (finRotate m i))
      (hμ i)
    rw [← h1]
    exact harg
  have hsum := sum_cycAdv_succ hm3 w (szCentroid S)
  rw [Finset.sum_congr rfl (fun i _ => hcyc i)] at hsum
  have hexp : ∑ i : Fin m, (π - A (finRotate m i) + t (finRotate m i) - t i)
      = (m:ℝ) * π - ∑ i : Fin m, A i := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have hπsum : ∑ i : Fin m, π = (m:ℝ) * π := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
    have hArot : ∑ i : Fin m, A (finRotate m i) = ∑ i : Fin m, A i :=
      Equiv.sum_comp (finRotate m) (fun j => A j)
    have htrot : ∑ i : Fin m, t (finRotate m i) = ∑ i : Fin m, t i :=
      Equiv.sum_comp (finRotate m) (fun j => t j)
    rw [hπsum, hArot, htrot]
    ring
  rw [hexp] at hsum
  linarith

/-- A hull whose windows all have aperture `< π (1 - 1/n)` has at most
`2n - 1` vertices. -/
theorem hull_card_le {n : ℕ} (hn : 3 ≤ n) {m : ℕ} {A : Fin m → ℝ}
    (hA : ∀ i, A i < (1 - 1 / (n : ℝ)) * π)
    (hsum : ∑ i : Fin m, A i = (m : ℝ) * π - 2 * π)
    (hm3 : 3 ≤ m) :
    m ≤ 2 * n - 1 := by
  have hπ : (0:ℝ) < π := Real.pi_pos
  have hn0 : 0 < n := by omega
  have hnR : (0:ℝ) < n := by exact_mod_cast hn0
  have hm0 : 0 < m := by omega
  have hlt : ∑ i : Fin m, A i < (m:ℝ) * ((1 - 1 / (n : ℝ)) * π) := by
    have h1 : ∑ i : Fin m, A i < ∑ i : Fin m, ((1 - 1 / (n : ℝ)) * π) := by
      refine Finset.sum_lt_sum (fun i _ => le_of_lt (hA i))
        ⟨⟨0, hm0⟩, Finset.mem_univ _, hA ⟨0, hm0⟩⟩
    have h2 : ∑ i : Fin m, ((1 - 1 / (n : ℝ)) * π)
        = (m:ℝ) * ((1 - 1 / (n : ℝ)) * π) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
    rw [h2] at h1
    exact h1
  rw [hsum] at hlt
  have hexp : (m:ℝ) * ((1 - 1 / (n : ℝ)) * π) = (m:ℝ) * π - (m:ℝ) * π / n := by
    field_simp
  rw [hexp] at hlt
  have h2 : (m:ℝ) * π / n < 2 * π := by linarith
  have h3 : (m:ℝ) * π < 2 * π * n := by
    rw [div_lt_iff₀ hnR] at h2
    linarith
  have h4 : (m:ℝ) < 2 * n := by
    have h5 : (m:ℝ) * π < (2 * n : ℝ) * π := by linarith
    exact lt_of_mul_lt_mul_right h5 (le_of_lt hπ)
  have hnat : m < 2 * n := by exact_mod_cast h4
  omega

/-- If the integer span `Q - P` is at most `n - 2`, then no integer in `[P, Q]`
is congruent to `Q + 1` mod `n`. -/
lemma emod_ne_of_span_le {n : ℕ} (hn : 3 ≤ n) {P Q j : ℤ}
    (hPQ : Q - P ≤ (n:ℤ) - 2) (hjP : P ≤ j) (hjQ : j ≤ Q) :
    j % (n:ℤ) ≠ (Q + 1) % (n:ℤ) := by
  have hn0 : (0:ℤ) < n := by exact_mod_cast (show 0 < n by omega)
  intro hjmod
  have h1 := Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hjmod
  obtain ⟨t, ht⟩ := Int.dvd_iff_emod_eq_zero.mpr h1
  have hlo : -(n:ℤ) < j - (Q + 1) := by omega
  have hhi : j - (Q + 1) < 0 := by omega
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, mul_zero] at ht
    omega
  rcases le_or_gt (0:ℤ) t with ht' | ht'
  · have h1 : 1 ≤ t := by omega
    have h2 : (n:ℤ) * 1 ≤ (n:ℤ) * t :=
      mul_le_mul_of_nonneg_left h1 hn0.le
    rw [mul_one] at h2
    linarith [h2, hhi]
  · have h1 : t ≤ -1 := by omega
    have h2 : (n:ℤ) * t ≤ (n:ℤ) * (-1) :=
      mul_le_mul_of_nonneg_left h1 hn0.le
    rw [mul_neg_one] at h2
    linarith [h2, hlo]

/-- If the sector spans sum to `mn - 2n` and the hull has at most `2n - 1`
vertices, some span is at most `n - 2`. -/
lemma exists_small_span {n m : ℕ} (hn : 3 ≤ n) {a : Fin m → ℤ}
    (hsum : ∑ i : Fin m, a i = (m:ℤ) * n - 2 * n)
    (hcard : m ≤ 2 * n - 1) :
    ∃ i : Fin m, a i ≤ (n:ℤ) - 2 := by
  by_contra hall
  have hge : ∀ i, (n:ℤ) - 1 ≤ a i := by
    intro i
    by_contra hi
    exact hall ⟨i, by linarith⟩
  have hsumge : (m:ℤ) * ((n:ℤ) - 1) ≤ ∑ i : Fin m, a i := by
    have h : ∑ i : Fin m, ((n:ℤ) - 1) ≤ ∑ i : Fin m, a i :=
      Finset.sum_le_sum (fun i _ => hge i)
    have hconstn : ∑ _i : Fin m, ((n:ℤ) - 1) = (m:ℤ) * ((n:ℤ) - 1) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
    rwa [hconstn] at h
  rw [hsum] at hsumge
  have hex : (m:ℤ) * ((n:ℤ) - 1) = (m:ℤ) * (n:ℤ) - (m:ℤ) := by ring
  rw [hex] at hsumge
  have hlt : (m:ℤ) < 2 * (n:ℤ) := by
    have h1 : (m:ℕ) < 2 * n := by omega
    exact_mod_cast h1
  linarith

/-- The sector spans `⌊n(θ i + A i)/π⌋ - ⌊n θ i /π⌋` sum to `mn - 2n`. -/
lemma sum_sector_spans {n m : ℕ} (w : Fin m → ℂ)
    {θ A : Fin m → ℝ}
    (hA : ∑ i : Fin m, A i = (m:ℝ) * π - 2 * π)
    (hm3 : 3 ≤ m)
    (hne : ∀ i, w i ≠ w (finRotate m i))
    (hsucc : ∀ i, w (finRotate m i) - w i
      = ((‖w (finRotate m i) - w i‖ : ℝ) : ℂ) * Complex.exp ((θ i : ℂ) * Complex.I))
    (hpred : ∀ i, w ((finRotate m).symm i) - w i
      = ((‖w ((finRotate m).symm i) - w i‖ : ℝ) : ℂ)
        * Complex.exp (((θ i + A i : ℝ) : ℂ) * Complex.I)) :
    ∑ i : Fin m, (⌊(n:ℝ) * (θ i + A i) / π⌋ - ⌊(n:ℝ) * θ i / π⌋)
      = (m:ℤ) * n - 2 * n := by
  classical
  have hπne : (π:ℝ) ≠ 0 := Real.pi_ne_zero
  have hrot : ∀ i : Fin m, ∃ μ : ℤ,
      θ (finRotate m i) + A (finRotate m i) = θ i + π + 2 * π * μ := by
    intro i
    have h1 := hpred (finRotate m i)
    rw [Equiv.symm_apply_apply] at h1
    exact edge_rotation_rule (v := w i) (v' := w (finRotate m i))
      (θ := θ i) (θ' := θ (finRotate m i)) (A' := A (finRotate m i))
      (ℓ := ‖w (finRotate m i) - w i‖) (ℓ' := ‖w i - w (finRotate m i)‖)
      (norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm (hne i))))
      (norm_pos_iff.mpr (sub_ne_zero.mpr (hne i))) (hsucc i) h1
  choose! μ hμ using hrot
  have hQnext : ∀ i : Fin m,
      ⌊(n:ℝ) * (θ (finRotate m i) + A (finRotate m i)) / π⌋
        = ⌊(n:ℝ) * θ i / π⌋ + ((n:ℤ) + 2 * (n:ℤ) * μ i) := by
    intro i
    have hne : (π:ℝ) ≠ 0 := Real.pi_ne_zero
    have h1 : (n:ℝ) * (θ i + π + 2 * π * (μ i : ℝ)) / π
        = (n:ℝ) * θ i / π + ((n:ℝ) + 2 * (n:ℝ) * (μ i : ℝ)) := by
      have hd : (n:ℝ) * (θ i + π + 2 * π * (μ i : ℝ))
          = (n:ℝ) * θ i + (n:ℝ) * π + (n:ℝ) * (2 * π * (μ i : ℝ)) := by ring
      have hcancel : ∀ x : ℝ, x * π / π = x := fun x => by
        have hp : (π:ℝ) ≠ 0 := Real.pi_ne_zero
        field_simp
      rw [hd, add_div, add_div, hcancel]
      have hz : (n:ℝ) * (2 * π * (μ i : ℝ)) / π = 2 * (n:ℝ) * (μ i : ℝ) := by
        have he : (n:ℝ) * (2 * π * (μ i : ℝ)) = (2 * (n:ℝ) * (μ i : ℝ)) * π := by ring
        rw [he, hcancel]
      rw [hz]
      ring
    have h2 : (n:ℝ) * θ i / π + ((n:ℝ) + 2 * (n:ℝ) * (μ i : ℝ))
        = (n:ℝ) * θ i / π + ↑((n:ℤ) + 2 * (n:ℤ) * μ i) := by
      push_cast
      ring
    rw [hμ i, h1, h2, Int.floor_add_intCast]
  have hmu1 : ∑ i : Fin m, μ i = -1 := by
    have hkey : ∀ i : Fin m, (θ (finRotate m i) : ℝ)
        = θ i + π - A (finRotate m i) + 2 * π * (μ i : ℝ) := fun i => by
      linarith [hμ i]
    have hsumθ : ∑ i : Fin m, (θ (finRotate m i) : ℝ) = ∑ i : Fin m, θ i :=
      Equiv.sum_comp (finRotate m) θ
    have h0 : ∑ i : Fin m, θ i
        = ∑ i : Fin m, (θ i + π - A (finRotate m i) + 2 * π * (μ i : ℝ)) := by
      rw [← hsumθ]
      exact Finset.sum_congr rfl (fun i _ => hkey i)
    have hexp : ∑ i : Fin m, (θ i + π - A (finRotate m i) + 2 * π * (μ i : ℝ))
        = ∑ i : Fin m, θ i + ((m:ℝ) * π - ∑ i : Fin m, A i)
          + 2 * π * (∑ i : Fin m, μ i) := by
      have e1 : ∀ i : Fin m, (θ i + π - A (finRotate m i) + 2 * π * (μ i : ℝ))
          = (θ i + π - A (finRotate m i)) + 2 * π * (μ i : ℝ) := fun i => by ring
      rw [Finset.sum_congr rfl (fun i _ => e1 i), Finset.sum_add_distrib,
        Finset.sum_sub_distrib, Finset.sum_add_distrib]
      have hπsum : ∑ _i : Fin m, (π:ℝ) = (m:ℝ) * π := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
      rw [hπsum, Equiv.sum_comp (finRotate m) (fun j => A j), ← Finset.mul_sum]
      push_cast
      ring
    rw [hexp] at h0
    have hcancel : 0 = (m:ℝ) * π - ∑ i : Fin m, A i
        + 2 * π * (∑ i : Fin m, μ i) := by
      linarith [h0]
    have hA' : (m:ℝ) * π - ∑ i : Fin m, A i = 2 * π := by
      rw [hA]; ring
    rw [hA'] at hcancel
    have hfac : (2:ℝ) * π ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
    have hstep : (2:ℝ) * π * (Int.cast (∑ i : Fin m, μ i))
        = (2:ℝ) * π * (-1) := by
      linarith [hcancel]
    have hval : ((∑ i : Fin m, μ i : ℤ) : ℝ) = -1 :=
      mul_left_cancel₀ hfac hstep
    exact_mod_cast hval
  have hsumQP : ∑ i : Fin m, (⌊(n:ℝ) * (θ i + A i) / π⌋ - ⌊(n:ℝ) * θ i / π⌋)
      = ∑ i : Fin m, ⌊(n:ℝ) * (θ i + A i) / π⌋ - ∑ i : Fin m, ⌊(n:ℝ) * θ i / π⌋ := by
    rw [Finset.sum_sub_distrib]
  have hQrot : ∑ i : Fin m, ⌊(n:ℝ) * (θ i + A i) / π⌋
      = ∑ i : Fin m, ⌊(n:ℝ) * (θ (finRotate m i) + A (finRotate m i)) / π⌋ :=
    (Equiv.sum_comp (finRotate m) (fun j => ⌊(n:ℝ) * (θ j + A j) / π⌋)).symm
  have hQexpand : ∑ i : Fin m, ⌊(n:ℝ) * (θ (finRotate m i) + A (finRotate m i)) / π⌋
      = ∑ i : Fin m, ⌊(n:ℝ) * θ i / π⌋ + (m:ℤ) * n + 2 * (n:ℤ) * (∑ i : Fin m, μ i) := by
    rw [Finset.sum_congr rfl (fun i _ => hQnext i), Finset.sum_add_distrib,
      Finset.sum_add_distrib]
    have hconstn : ∑ _i : Fin m, ((n:ℤ)) = (m:ℤ) * n := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
    have hconstmu : ∑ i : Fin m, (2 * (n:ℤ) * μ i)
        = 2 * (n:ℤ) * (∑ i : Fin m, μ i) := by
      rw [← Finset.mul_sum]
    rw [hconstn, hconstmu, hmu1]
    ring
  rw [hsumQP, hQrot, hQexpand, hmu1]
  ring

/-- **Hull isolation.**  Under the strict angle bound there is a hull vertex
`w i` and a colour `k` such that no other point of `S` has colour `k` from
`w i`. -/
theorem exists_isolated_hull_vertex {n : ℕ} (hn : 3 ≤ n)
    {S : Finset ℂ} (hS3 : 3 ≤ S.card)
    (hangle : ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
      EuclideanGeometry.angle p q r < (1 - 1 / (n : ℝ)) * π)
    (hgen : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c →
      ¬ Collinear ℝ ({a, b, c} : Set ℂ))
    {m : ℕ} (w : Fin m → ℂ)
    (hmem : ∀ i, w i ∈ extremeFinset S)
    (hsur : ∀ v ∈ extremeFinset S, ∃ i, w i = v)
    (hmono : StrictMono (fun i => Complex.arg (w i - szCentroid S)))
    (hm3 : 3 ≤ m) :
    ∃ i : Fin m, ∃ k : Fin n, ∀ q ∈ S, q ≠ w i →
      dirIndex n (q - w i) ≠ (k : ℕ) := by
  classical
  obtain ⟨θ, A, hA0, hAπ, hAΘ, hwin, hsucc, hpred⟩ :=
    exists_hull_windows hn hangle hgen w hmem hsur hmono hm3
  have hEsub : extremeFinset S ⊆ S := fun p hp => mem_of_mem_extremeFinset hp
  have hinj : Function.Injective w := fun x y hxy =>
    hmono.injective (show (fun j => Complex.arg (w j - szCentroid S)) x
      = (fun j => Complex.arg (w j - szCentroid S)) y from by simp only [hxy])
  have himg : Finset.univ.image w = extremeFinset S := by
    apply Finset.ext
    intro x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, -, rfl⟩
      exact hmem i
    · intro hx
      obtain ⟨i, hi⟩ := hsur x hx
      exact ⟨i, hi⟩
  have hcardm : (extremeFinset S).card = m := by
    rw [← himg, Finset.card_image_of_injective _ hinj, Finset.card_univ,
      Fintype.card_fin]
  have hcard2 : 2 < S.card := by
    have h := Finset.card_le_card hEsub
    rw [hcardm] at h
    omega
  have ht : ∀ i, ∃ r t : ℝ, 0 < r ∧ 0 < t ∧ t < A i ∧
      szCentroid S - w i = (r : ℂ) * Complex.exp (((θ i + t : ℝ) : ℂ) * Complex.I) :=
    fun i => centroid_dir_in_window_strict (mem_of_mem_extremeFinset (hmem i))
      hcard2 hgen (hA0 i) (hAπ i) (hwin i)
  have hap : ∑ i : Fin m, A i = (m:ℝ) * π - 2 * π :=
    sum_window_apertures w hS3 hgen hmem hsur hmono hm3 hAπ hsucc hpred ht
  have hmle : m ≤ 2 * n - 1 := hull_card_le hn hAΘ hap hm3
  have hne : ∀ i, w i ≠ w (finRotate m i) := by
    intro i h
    exact finRotate_ne_self hm3 i (hinj h).symm
  have hspan : ∑ i : Fin m, (⌊(n:ℝ) * (θ i + A i) / π⌋ - ⌊(n:ℝ) * θ i / π⌋)
      = (m:ℤ) * n - 2 * n :=
    sum_sector_spans w hap hm3 hne hsucc hpred
  obtain ⟨i0, hi0⟩ := exists_small_span hn hspan hmle
  set P := ⌊(n:ℝ) * θ i0 / π⌋ with hPdef
  set Q := ⌊(n:ℝ) * (θ i0 + A i0) / π⌋ with hQdef
  have hPQ : Q - P ≤ (n:ℤ) - 2 := hi0
  have hn0 : (0:ℤ) < n := by exact_mod_cast (show 0 < n by omega)
  have hklt : ((Q + 1) % (n:ℤ)).toNat < n := by
    have h1 := Int.emod_lt_of_pos (Q + 1) hn0
    have h2 : (((Q + 1) % (n:ℤ)).toNat : ℤ) = (Q + 1) % (n:ℤ) :=
      Int.toNat_of_nonneg (Int.emod_nonneg (Q + 1) hn0.ne')
    have h3 : (((Q + 1) % (n:ℤ)).toNat : ℤ) < (n:ℤ) := by rw [h2]; exact h1
    exact_mod_cast h3
  refine ⟨i0, ⟨((Q + 1) % (n:ℤ)).toNat, hklt⟩, ?_⟩
  intro q hq hne
  obtain ⟨r, t, hr, ht0, htA, hform⟩ := hwin i0 q hq hne
  have hdi : dirIndex n (q - w i0)
      = ((⌊(n:ℝ) * (θ i0 + t) / π⌋ : ℤ) % (n:ℤ)).toNat :=
    dirIndex_polar_eq (by omega) hr hform
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hjP : P ≤ ⌊(n:ℝ) * (θ i0 + t) / π⌋ := by
    rw [hPdef]
    apply Int.floor_le_floor
    have hnp : (0:ℝ) < n / π := div_pos hnR Real.pi_pos
    have hkey : (n:ℝ) * (θ i0 + t) / π - (n:ℝ) * θ i0 / π = (n:ℝ) / π * t := by
      field_simp
      ring
    have hpos : 0 ≤ (n:ℝ) / π * t := mul_nonneg hnp.le ht0
    rw [← sub_nonneg, hkey]
    exact hpos
  have hjQ : ⌊(n:ℝ) * (θ i0 + t) / π⌋ ≤ Q := by
    rw [hQdef]
    apply Int.floor_le_floor
    have hnp : (0:ℝ) < n / π := div_pos hnR Real.pi_pos
    have hkey : (n:ℝ) * (θ i0 + A i0) / π - (n:ℝ) * (θ i0 + t) / π
        = (n:ℝ) / π * (A i0 - t) := by
      field_simp
      ring
    have hAt : 0 ≤ A i0 - t := by linarith [htA]
    have hpos : 0 ≤ (n:ℝ) / π * (A i0 - t) := mul_nonneg hnp.le hAt
    rw [← sub_nonneg, hkey]
    exact hpos
  intro heq
  have h3 : ((⌊(n:ℝ) * (θ i0 + t) / π⌋ : ℤ) % (n:ℤ)).toNat
      = ((Q + 1) % (n:ℤ)).toNat := by
    rw [← hdi]
    exact heq
  have h4 : (((⌊(n:ℝ) * (θ i0 + t) / π⌋ : ℤ) % (n:ℤ)).toNat : ℤ)
      = (⌊(n:ℝ) * (θ i0 + t) / π⌋ : ℤ) % (n:ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ hn0.ne')
  have h5 : (((Q + 1) % (n:ℤ)).toNat : ℤ) = (Q + 1) % (n:ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg (Q + 1) hn0.ne')
  have h6 : (((⌊(n:ℝ) * (θ i0 + t) / π⌋ : ℤ) % (n:ℤ)).toNat : ℤ)
      = (((Q + 1) % (n:ℤ)).toNat : ℤ) := by exact_mod_cast h3
  rw [h4, h5] at h6
  exact emod_ne_of_span_le hn hPQ hjP hjQ h6
