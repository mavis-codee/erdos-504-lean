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

/-! ## Round 6: interior points and rotation isolation -/

set_option maxHeartbeats 1000000 in
/-- Collinearity of a triple is preserved under multiplication by a nonzero
complex number. -/
lemma collinear_const_mul {c a b d : ℂ} (hc : c ≠ 0)
    (h : Collinear ℝ ({a, b, d} : Set ℂ)) :
    Collinear ℝ ({c * a, c * b, c * d} : Set ℂ) := by
  rw [collinear_iff_exists_forall_eq_smul_vadd] at h ⊢
  obtain ⟨p₀, v, hv⟩ := h
  refine ⟨c * p₀, c * v, ?_⟩
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with h1 | hp
  · obtain ⟨r, hr⟩ := hv a (by simp)
    refine ⟨r, ?_⟩
    rw [h1, hr]
    simp only [vadd_eq_add, Complex.real_smul]
    push_cast
    ring
  rcases hp with h2 | h3
  · obtain ⟨r, hr⟩ := hv b (by simp)
    refine ⟨r, ?_⟩
    rw [h2, hr]
    simp only [vadd_eq_add, Complex.real_smul]
    push_cast
    ring
  · obtain ⟨r, hr⟩ := hv d (by simp)
    refine ⟨r, ?_⟩
    rw [h3, hr]
    simp only [vadd_eq_add, Complex.real_smul]
    push_cast
    ring

/-- Contrapositive of `collinear_const_mul`. -/
lemma not_collinear_const_mul {c a b d : ℂ} (hc : c ≠ 0)
    (h : ¬ Collinear ℝ ({a, b, d} : Set ℂ)) :
    ¬ Collinear ℝ ({c * a, c * b, c * d} : Set ℂ) := by
  intro hcol
  have hinv : (c⁻¹ : ℂ) ≠ 0 := inv_ne_zero hc
  have h2 := collinear_const_mul hinv hcol
  rw [inv_mul_cancel_left₀ hc a, inv_mul_cancel_left₀ hc b,
    inv_mul_cancel_left₀ hc d] at h2
  exact h h2

set_option maxHeartbeats 2000000 in
/-- A point of `S` outside the extreme-point set, provided the hull is
strictly smaller than `S`. -/
lemma exists_not_extreme_of_card_lt {S : Finset ℂ}
    (h : (extremeFinset S).card < S.card) :
    ∃ q ∈ S, q ∉ extremeFinset S := by
  by_contra hcon
  have hsub : S ⊆ extremeFinset S := fun q hq => by
    by_contra hne
    exact hcon ⟨q, hq, hne⟩
  exact (not_le.mpr h) (Finset.card_le_card hsub)

set_option maxHeartbeats 1000000 in
/-- Under the strict angle bound, a set of at least `2 ^ n - 1` points has a
point that is not a vertex of the convex hull. -/
lemma exists_interior_point {n : ℕ} (hn : 3 ≤ n)
    {S : Finset ℂ} (hS3 : 3 ≤ S.card)
    (hangle : ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
      EuclideanGeometry.angle p q r < (1 - 1 / (n : ℝ)) * π)
    (hgen : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c →
      ¬ Collinear ℝ ({a, b, c} : Set ℂ))
    (hcard : 2 ^ n - 1 ≤ S.card) :
    ∃ q ∈ S, q ∉ extremeFinset S := by
  classical
  obtain ⟨w, hmem, hsur, hmono⟩ := exists_argSorted_enum hS3 hgen
  have hm3 : 3 ≤ (extremeFinset S).card := three_le_card_extremeFinset hS3 hgen
  obtain ⟨θ, A, hA0, hAπ, hAΘ, hwin, hsucc, hpred⟩ :=
    exists_hull_windows hn hangle hgen w hmem hsur hmono hm3
  have hcard2 : 2 < S.card := by
    have h := two_pow_ge_eight' hn
    have hc := hcard
    omega
  have ht : ∀ i, ∃ r t : ℝ, 0 < r ∧ 0 < t ∧ t < A i ∧
      szCentroid S - w i = (r : ℂ) * Complex.exp (((θ i + t : ℝ) : ℂ) * Complex.I) :=
    fun i => centroid_dir_in_window_strict (mem_of_mem_extremeFinset (hmem i))
      hcard2 hgen (hA0 i) (hAπ i) (hwin i)
  have hap : ∑ i : Fin (extremeFinset S).card, A i
      = ((extremeFinset S).card : ℝ) * π - 2 * π :=
    sum_window_apertures w hS3 hgen hmem hsur hmono hm3 hAπ hsucc hpred ht
  have hmle : (extremeFinset S).card ≤ 2 * n - 1 := hull_card_le hn hAΘ hap hm3
  have hlt : (extremeFinset S).card < S.card := by
    have h3 := two_le_pow_sub n hn
    have hc := hcard
    omega
  exact exists_not_extreme_of_card_lt hlt

set_option maxHeartbeats 1000000 in
/-- At a point `q` with at least two other points of `S`, some pair attains
the maximum angle at `q`. -/
lemma exists_max_angle_at {S : Finset ℂ} {q : ℂ} (hq : q ∈ S)
    (hcard : 2 ≤ (S.erase q).card) :
    ∃ q₁ ∈ S, ∃ q₂ ∈ S, q₁ ≠ q₂ ∧ q₁ ≠ q ∧ q₂ ≠ q ∧
      ∀ z ∈ S, ∀ w ∈ S, z ≠ q → w ≠ q → z ≠ w →
        EuclideanGeometry.angle z q w ≤ EuclideanGeometry.angle q₁ q q₂ := by
  classical
  set T := ((S.erase q).product (S.erase q)).filter (fun p => p.1 ≠ p.2) with hTdef
  have hne : T.Nonempty := by
    have hcard1 : 1 < (S.erase q).card := by omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard1
    refine ⟨(a, b), ?_⟩
    rw [hTdef]
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hab⟩
  obtain ⟨p, hpT, hmax⟩ :=
    Finset.exists_max_image T (fun p => EuclideanGeometry.angle p.1 q p.2) hne
  have hpmem : p.1 ∈ S.erase q ∧ p.2 ∈ S.erase q ∧ p.1 ≠ p.2 := by
    have h := Finset.mem_filter.mp hpT
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp h.1
    exact ⟨ha, hb, h.2⟩
  have hp₁q : p.1 ≠ q := (Finset.mem_erase.mp hpmem.1).1
  have hp₂q : p.2 ≠ q := (Finset.mem_erase.mp hpmem.2.1).1
  have hp₁S : p.1 ∈ S := Finset.mem_of_mem_erase hpmem.1
  have hp₂S : p.2 ∈ S := Finset.mem_of_mem_erase hpmem.2.1
  have hne12 : p.1 ≠ p.2 := hpmem.2.2
  refine ⟨p.1, hp₁S, p.2, hp₂S, hne12, hp₁q, hp₂q, ?_⟩
  intro z hzS w hwS hzq hwq hzw
  have hzE : z ∈ S.erase q := Finset.mem_erase.mpr ⟨hzq, hzS⟩
  have hwE : w ∈ S.erase q := Finset.mem_erase.mpr ⟨hwq, hwS⟩
  have hpair : (z, w) ∈ T := by
    rw [hTdef]
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hzE, hwE⟩, hzw⟩
  exact hmax (z, w) hpair

set_option maxHeartbeats 1000000 in
/-- The angle at `c` between two directions given in polar form, when the
argument difference lies in `[-π, π]`.  The endpoint case `|β - α| = π`
(antipodal rays) is included. -/
lemma angle_polar_abs {a b c : ℂ} {r s α β : ℝ}
    (hr : 0 < r) (hs : 0 < s)
    (ha : a - c = (r : ℂ) * Complex.exp ((α : ℂ) * Complex.I))
    (hb : b - c = (s : ℂ) * Complex.exp ((β : ℂ) * Complex.I))
    (hlo : -π ≤ β - α) (hhi : β - α ≤ π) :
    EuclideanGeometry.angle a c b = |β - α| := by
  have hbridge : EuclideanGeometry.angle a c b
      = InnerProductGeometry.angle (a - c) (b - c) := by
    simp [EuclideanGeometry.angle, vsub_eq_sub]
  have hac : a - c ≠ 0 := by
    rw [ha]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hr))
      (Complex.exp_ne_zero _)
  have habsh : |β - α| ≤ π := abs_le.mpr ⟨hlo, hhi⟩
  rcases lt_or_eq_of_le habsh with hlt | heq
  · obtain ⟨hlo', hhi'⟩ := abs_lt.mp hlt
    rw [hbridge, ha, hb]
    rw [angle_eq_abs_arg (mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hr))
        (Complex.exp_ne_zero _))
      (mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hs))
        (Complex.exp_ne_zero _))]
    have hexp : (starRingEnd ℂ) ((r : ℂ) * Complex.exp ((α : ℂ) * Complex.I))
        * ((s : ℂ) * Complex.exp ((β : ℂ) * Complex.I))
        = ((r * s : ℝ) : ℂ) * Complex.exp (((β - α : ℝ) : ℂ) * Complex.I) := by
      have h1 : (starRingEnd ℂ) ((r : ℂ) * Complex.exp ((α : ℂ) * Complex.I))
          = (r : ℂ) * (starRingEnd ℂ) (Complex.exp ((α : ℂ) * Complex.I)) := by
        rw [map_mul, Complex.conj_ofReal]
      have h2 : (starRingEnd ℂ) (Complex.exp ((α : ℂ) * Complex.I))
          * Complex.exp ((β : ℂ) * Complex.I)
          = Complex.exp (((β - α : ℝ) : ℂ) * Complex.I) := by
        have hβeq : ((β : ℝ) : ℂ) * Complex.I
            = ((α + (β - α) : ℝ) : ℂ) * Complex.I := by
          push_cast
          ring
        rw [hβeq, conj_exp_mul_exp α (β - α)]
      have hre : (r : ℂ) * (starRingEnd ℂ) (Complex.exp ((α : ℂ) * Complex.I))
          * ((s : ℂ) * Complex.exp ((β : ℂ) * Complex.I))
          = ((r * s : ℝ) : ℂ) * ((starRingEnd ℂ) (Complex.exp ((α : ℂ) * Complex.I))
            * Complex.exp ((β : ℂ) * Complex.I)) := by
        push_cast
        ring
      rw [h1, hre, h2]
    rw [hexp]
    rw [arg_of_polar (mul_pos hr hs) hlo' hhi'.le]
  · -- `|β - α| = π`: the two rays are opposite.
    rw [hbridge, heq, InnerProductGeometry.angle_eq_pi_iff]
    refine ⟨hac, ⟨-(s / r), neg_lt_zero.mpr (div_pos hs hr), ?_⟩⟩
    have hba : β - α = π ∨ β - α = -π := by
      rcases le_or_gt 0 (β - α) with hp | hn
      · refine Or.inl ?_
        have h5 : |β - α| = (β - α) := abs_of_nonneg hp
        linarith
      · refine Or.inr ?_
        have h5 : |β - α| = -(β - α) := abs_of_neg hn
        linarith
    have hexprel : Complex.exp ((β : ℂ) * Complex.I)
        = -(Complex.exp ((α : ℂ) * Complex.I)) := by
      rcases hba with h | h
      · have hβ : β = α + π := by linarith
        rw [hβ]
        have hsplit : ((α + π : ℝ) : ℂ) * Complex.I
            = (α : ℂ) * Complex.I + ((π : ℝ) : ℂ) * Complex.I := by
          push_cast
          ring
        rw [hsplit, Complex.exp_add, Complex.exp_pi_mul_I]
        ring
      · have hβ : β = α - π := by linarith
        rw [hβ]
        have hsplit : ((α - π : ℝ) : ℂ) * Complex.I
            = (α : ℂ) * Complex.I + ((-π : ℝ) : ℂ) * Complex.I := by
          push_cast
          ring
        have hexpneg : Complex.exp (((-π : ℝ) : ℂ) * Complex.I) = -1 := by
          have hpi : Complex.exp ((π : ℂ) * Complex.I) = -1 := Complex.exp_pi_mul_I
          have h1 : (starRingEnd ℂ) (Complex.exp ((π : ℂ) * Complex.I))
              = Complex.exp (((-π : ℝ) : ℂ) * Complex.I) := by
            rw [← Complex.exp_conj]
            congr 1
            rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
            push_cast
            ring
          rw [← h1, hpi]
          simp
        rw [hsplit, Complex.exp_add, hexpneg]
        ring
    rw [ha, hb, hexprel]
    rw [Complex.real_smul]
    rw [← mul_assoc, ← Complex.ofReal_mul]
    have hcoef : (-(s / r) * r : ℝ) = -s := by
      rw [neg_mul, div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ (ne_of_gt hr), mul_one]
    rw [hcoef, Complex.ofReal_neg]
    ring

set_option maxHeartbeats 1000000 in
/-- If `conj u * w` has argument `A` (any real number), then `w` has argument
`arg u + A`. -/
lemma polar_of_arg_conj_mul {u w : ℂ} {A : ℝ} (hu0 : u ≠ 0)
    (harg : Complex.arg ((starRingEnd ℂ) u * w) = A) :
    w = (‖w‖ : ℂ) * Complex.exp (((Complex.arg u + A : ℝ) : ℂ) * Complex.I) := by
  have hu : u = (‖u‖ : ℂ) * Complex.exp ((Complex.arg u : ℂ) * Complex.I) :=
    (Complex.norm_mul_exp_arg_mul_I u).symm
  have hconj : (starRingEnd ℂ) u
      = (‖u‖ : ℂ) * Complex.exp (((-Complex.arg u : ℝ) : ℂ) * Complex.I) := by
    conv_lhs => rw [hu]
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    congr 2
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have hprod : (starRingEnd ℂ) u * w
      = ((‖u‖ * ‖w‖ : ℝ) : ℂ) * Complex.exp ((A : ℂ) * Complex.I) := by
    have h1 := Complex.norm_mul_exp_arg_mul_I ((starRingEnd ℂ) u * w)
    rw [harg] at h1
    rw [Complex.norm_mul, Complex.norm_conj] at h1
    exact h1.symm
  have hu0' : (‖u‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (norm_pos_iff.mpr hu0))
  have hstep : Complex.exp (((-Complex.arg u : ℝ) : ℂ) * Complex.I) * w
      = (‖w‖ : ℂ) * Complex.exp ((A : ℂ) * Complex.I) := by
    rw [hconj] at hprod
    have h2 : (‖u‖ : ℂ) * (Complex.exp (((-Complex.arg u : ℝ) : ℂ) * Complex.I) * w)
        = (‖u‖ : ℂ) * ((‖w‖ : ℂ) * Complex.exp ((A : ℂ) * Complex.I)) := by
      have h3 : (‖u‖ : ℂ) * (Complex.exp (((-Complex.arg u : ℝ) : ℂ) * Complex.I) * w)
          = ((‖u‖ : ℂ) * Complex.exp (((-Complex.arg u : ℝ) : ℂ) * Complex.I)) * w :=
        (mul_assoc _ _ _).symm
      have h4 : (‖u‖ : ℂ) * ((‖w‖ : ℂ) * Complex.exp ((A : ℂ) * Complex.I))
          = ((‖u‖ : ℂ) * (‖w‖ : ℂ)) * Complex.exp ((A : ℂ) * Complex.I) :=
        (mul_assoc _ _ _).symm
      have h5 : ((‖u‖ : ℂ) * (‖w‖ : ℂ)) = ((‖u‖ * ‖w‖ : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul]
      rw [h3, h4, h5]
      exact hprod
    exact mul_left_cancel₀ hu0' h2
  have hone : Complex.exp ((Complex.arg u : ℂ) * Complex.I)
      * Complex.exp (((-Complex.arg u : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_add]
    have hz : (Complex.arg u : ℂ) * Complex.I
        + ((-Complex.arg u : ℝ) : ℂ) * Complex.I = 0 := by
      push_cast
      ring
    rw [hz, Complex.exp_zero]
  calc w = (1 : ℂ) * w := (one_mul w).symm
    _ = (Complex.exp ((Complex.arg u : ℂ) * Complex.I)
          * Complex.exp (((-Complex.arg u : ℝ) : ℂ) * Complex.I)) * w := by
        rw [hone]
    _ = Complex.exp ((Complex.arg u : ℂ) * Complex.I)
          * (Complex.exp (((-Complex.arg u : ℝ) : ℂ) * Complex.I) * w) := by
        rw [mul_assoc]
    _ = Complex.exp ((Complex.arg u : ℂ) * Complex.I)
          * ((‖w‖ : ℂ) * Complex.exp ((A : ℂ) * Complex.I)) := by rw [hstep]
    _ = (‖w‖ : ℂ) * Complex.exp (((Complex.arg u + A : ℝ) : ℂ) * Complex.I) := by
        rw [mul_left_comm]
        congr 1
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring

set_option maxHeartbeats 1000000 in
/-- **Core interior isolation.**  If two reference points are seen from `q`
at directions `−δ/2` and `−(δ/2+A)`, and `z` makes an angle at most `A`
with both, where `A + δ = π(1−1/n)` and `δ > 0`, then `z` is not in
colour `0` as seen from `q`. -/
lemma dirIndex_ne_zero_of_max_arc {n : ℕ} {q p₁ p₂ z : ℂ} {A δ r₁ r₂ s : ℝ}
    (hn : 3 ≤ n)
    (hA0 : 0 ≤ A) (hAπ : A < π)
    (hδ0 : 0 < δ)
    (hΘ : A + δ = (1 - 1 / (n : ℝ)) * π)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hs : 0 < s)
    (hp₁ : p₁ - q = (r₁ : ℂ) * Complex.exp ((-(δ / 2) : ℝ) * Complex.I))
    (hp₂ : p₂ - q = (r₂ : ℂ) * Complex.exp ((-(δ / 2 + A) : ℝ) * Complex.I))
    (hform : z - q = (s : ℂ) * Complex.exp ((Complex.arg (z - q) : ℂ) * Complex.I))
    (h₁ : EuclideanGeometry.angle p₁ q z ≤ A)
    (h₂ : EuclideanGeometry.angle p₂ q z ≤ A) :
    dirIndex n (z - q) ≠ 0 := by
  classical
  intro hdir0
  set γ := Complex.arg (z - q) with hγdef
  have hγο1 : -π < γ := Complex.neg_pi_lt_arg _
  have hγο2 : γ ≤ π := Complex.arg_le_pi _
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hnR : (0 : ℝ) < n := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  have h1n : (1 : ℝ) ≤ n := by
    have : (1 : ℕ) ≤ n := by omega
    exact_mod_cast this
  have hΘπ : (1 - 1 / (n : ℝ)) * π < π := theta_lt_pi hn
  have hAΘ : A < (1 - 1 / (n : ℝ)) * π := by rw [← hΘ]; linarith
  have hΘeq : (1 - 1 / (n : ℝ)) * π = π - π / n := by ring
  have hΘ' : A + δ = π - π / n := by rw [hΘ, hΘeq]
  have hπn : 0 < π / n := div_pos hπ hnR
  have hπn1 : π / n ≤ π := div_le_self (by linarith) h1n
  have hδπ : δ < π := by linarith
  have hδsum : δ / 2 + δ / 2 = δ := by ring
  have hδhalf_pos : 0 < δ / 2 := by linarith
  have hδhalf_lt : δ / 2 < π := by linarith
  have hAΘ'' : A < π - π / n := by linarith
  have hhalf : δ / 2 + A < π := by linarith
  have hkey : π / n ≤ 2 * π - δ / 2 - 2 * A := by linarith
  unfold dirIndex at hdir0
  rw [← hγdef] at hdir0
  have hf0 : 0 ≤ (n : ℝ) * Int.fract (γ / π) := by
    apply mul_nonneg (le_of_lt hnR)
    exact Int.fract_nonneg _
  have hfl0 : 0 ≤ ⌊(n : ℝ) * Int.fract (γ / π)⌋ := Int.floor_nonneg.mpr hf0
  have hflz : ⌊(n : ℝ) * Int.fract (γ / π)⌋ = 0 := by
    have h2 : (⌊(n : ℝ) * Int.fract (γ / π)⌋ : ℤ) ≤ 0 :=
      Int.toNat_eq_zero.mp hdir0
    exact le_antisymm h2 hfl0
  have hlt1 : (n : ℝ) * Int.fract (γ / π) < 1 := by
    have h := Int.lt_floor_add_one ((n : ℝ) * Int.fract (γ / π))
    rw [hflz] at h
    linarith
  have hfr : Int.fract (γ / π) < 1 / n := by
    rw [lt_div_iff₀ hnR]
    have h3 : Int.fract (γ / π) * n = (n : ℝ) * Int.fract (γ / π) := by ring
    rw [h3]
    exact hlt1
  rcases le_or_gt 0 γ with hpos | hneg
  · -- `γ ≥ 0`
    rcases lt_or_eq_of_le hγο2 with hltπ | heqπ
    · -- Case 2: `0 ≤ γ < π`, hence `γ < π/n`.  Use `p₂`, possibly with wrap.
      have hγlt : γ < π / n := by
        have hfrpos : Int.fract (γ / π) = γ / π :=
          Int.fract_eq_self.mpr ⟨div_nonneg hpos hπ.le,
            by rw [div_lt_one hπ]; linarith⟩
        rw [hfrpos] at hfr
        have h4 : γ / π * π < (1 / n) * π := mul_lt_mul_of_pos_right hfr hπ
        have h5 : γ / π * π = γ := div_mul_cancel₀ γ (ne_of_gt hπ)
        have h6 : (1 / n) * π = π / n := by ring
        rw [h5, h6] at h4
        exact h4
      by_cases hwrap : γ + δ / 2 + A ≤ π
      · have hang : EuclideanGeometry.angle p₂ q z
            = |γ - (-(δ / 2 + A))| :=
          angle_polar_abs hr₂ hs hp₂ hform (by linarith) (by linarith)
        have hform2 : γ - (-(δ / 2 + A)) = γ + δ / 2 + A := by ring
        rw [hform2] at hang
        rw [abs_of_nonneg (by linarith)] at hang
        linarith
      · have hwgt : π < γ + δ / 2 + A := not_le.mp hwrap
        have hsum2π : γ + δ / 2 + A < 2 * π := by linarith
        have hrew : z - q
            = (s : ℂ) * Complex.exp (((γ - 2 * π : ℝ) : ℂ) * Complex.I) := by
          rw [hform]
          have h := exp_add_int_two_pi (γ - 2 * π) 1
          have h2 : (γ - 2 * π + 2 * π * ((1 : ℤ) : ℝ) : ℝ) = γ := by
            push_cast
            ring
          rw [h2] at h
          rw [h]
        have hang : EuclideanGeometry.angle p₂ q z
            = |γ - 2 * π - (-(δ / 2 + A))| :=
          angle_polar_abs hr₂ hs hp₂ hrew (by linarith) (by linarith)
        have hform2 : γ - 2 * π - (-(δ / 2 + A)) = γ - 2 * π + δ / 2 + A := by
          ring
        rw [hform2] at hang
        have habs : |γ - 2 * π + δ / 2 + A| = -(γ - 2 * π + δ / 2 + A) :=
          abs_of_neg (by linarith)
        rw [habs] at hang
        linarith
    · -- Case 3: `γ = π`.  Use `p₁` with the representation `e^{-iπ}`.
      have hrew : z - q = (s : ℂ) * Complex.exp (((-π : ℝ) : ℂ) * Complex.I) := by
        rw [hform, heqπ]
        have h := exp_add_int_two_pi (-(π : ℝ)) 1
        have h2 : (-(π : ℝ) + 2 * π * ((1 : ℤ) : ℝ) : ℝ) = π := by
          push_cast
          ring
        rw [h2] at h
        rw [h]
      have hang : EuclideanGeometry.angle p₁ q z
          = |(-π : ℝ) - (-(δ / 2))| :=
        angle_polar_abs hr₁ hs hp₁ hrew (by linarith) (by linarith)
      have hform2 : (-π : ℝ) - (-(δ / 2)) = (-π : ℝ) + δ / 2 := by ring
      rw [hform2] at hang
      have habs : |(-π : ℝ) + δ / 2| = -((-π : ℝ) + δ / 2) := abs_of_neg (by linarith)
      rw [habs] at hang
      linarith
  · -- Case 1: `γ < 0`, hence `γ < -Θ`.  Use `p₁`.
    have hflneg : Int.fract (γ / π) = γ / π + 1 := by
      have hfloor : ⌊γ / π⌋ = (-1 : ℤ) := by
        have hlo : ((-1 : ℤ) : ℝ) ≤ γ / π := by
          rw [le_div_iff₀ hπ]
          push_cast
          linarith
        have hhi : γ / π < 0 := by
          rw [div_lt_iff₀ hπ]
          linarith
        have hzero : ((-1 : ℤ) : ℝ) + 1 = 0 := by push_cast; ring
        exact Int.floor_eq_iff.mpr ⟨hlo, by linarith [hhi, hzero]⟩
      have h := Int.floor_add_fract (γ / π)
      rw [hfloor] at h
      linarith
    have hγlt : γ < -(π - π / n) := by
      rw [hflneg] at hfr
      have h2 : γ / π < 1 / n - 1 := by linarith
      have h3 : γ / π * π < (1 / n - 1) * π := mul_lt_mul_of_pos_right h2 hπ
      have h5 : γ / π * π = γ := div_mul_cancel₀ γ (ne_of_gt hπ)
      have h4 : (1 / n - 1) * π = -(π - π / n) := by ring
      rw [h5, h4] at h3
      exact h3
    have hang : EuclideanGeometry.angle p₁ q z = |γ - (-(δ / 2))| :=
      angle_polar_abs hr₁ hs hp₁ hform (by linarith) (by linarith)
    have hform2 : γ - (-(δ / 2)) = γ + δ / 2 := by ring
    rw [hform2] at hang
    have habs : |γ + δ / 2| = -(γ + δ / 2) := abs_of_neg (by linarith)
    rw [habs] at hang
    linarith

set_option maxHeartbeats 1000000 in
/-- **Interior isolation by rotation.**  Under the strict angle bound, after
a suitable rotation of the whole configuration some point of the rotated set
is isolated in colour `0`. -/
theorem exists_isolated_interior {n : ℕ} (hn : 3 ≤ n)
    {S : Finset ℂ} (hS3 : 3 ≤ S.card)
    (hangle : ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
      EuclideanGeometry.angle p q r < (1 - 1 / (n : ℝ)) * π)
    (hgen : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c →
      ¬ Collinear ℝ ({a, b, c} : Set ℂ))
    (hcard : 2 ^ n - 1 ≤ S.card) :
    ∃ c : ℂ, c ≠ 0 ∧ ∃ q ∈ S, q ∉ extremeFinset S ∧
      ∀ p ∈ S.image (fun z => c * z), p ≠ c * q → dirIndex n (p - c * q) ≠ 0 := by
  classical
  obtain ⟨q, hq, hqne⟩ := exists_interior_point hn hS3 hangle hgen hcard
  have hcardE : 2 ≤ (S.erase q).card := by
    have h := two_pow_ge_eight' hn
    have h1 := Finset.card_erase_of_mem hq
    have hc := hcard
    omega
  obtain ⟨q₁, hq₁S, q₂, hq₂S, hq₁q₂, hq₁q, hq₂q, hmax⟩ :=
    exists_max_angle_at hq hcardE
  have hΘπ : (1 - 1 / (n : ℝ)) * π < π := theta_lt_pi hn
  have hu0 : q₁ - q ≠ 0 := sub_ne_zero.mpr hq₁q
  have hw0 : q₂ - q ≠ 0 := sub_ne_zero.mpr hq₂q
  have hbr : EuclideanGeometry.angle q₁ q q₂
      = InnerProductGeometry.angle (q₁ - q) (q₂ - q) := by
    simp [EuclideanGeometry.angle, vsub_eq_sub]
  have habsarg : |Complex.arg ((starRingEnd ℂ) (q₁ - q) * (q₂ - q))|
      = EuclideanGeometry.angle q₁ q q₂ := by
    rw [hbr]
    exact (angle_eq_abs_arg hu0 hw0).symm
  set A := EuclideanGeometry.angle q₁ q q₂ with hAdef
  have hA0 : 0 ≤ A := by rw [hAdef]; exact EuclideanGeometry.angle_nonneg _ _ _
  have hAΘ : A < (1 - 1 / (n : ℝ)) * π := hangle q₁ hq₁S q hq q₂ hq₂S hq₁q hq₂q
  set δ := (1 - 1 / (n : ℝ)) * π - A with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; linarith
  have hAπ : A < π := by linarith
  have hΘ : A + δ = (1 - 1 / (n : ℝ)) * π := by rw [hδdef]; ring
  have hmax₁ : ∀ z ∈ S, z ≠ q → EuclideanGeometry.angle q₁ q z ≤ A := by
    intro z hz hzq
    by_cases hz₁ : z = q₁
    · rw [hz₁]
      have h0 : EuclideanGeometry.angle q₁ q q₁ = 0 := by
        have hbr0 : EuclideanGeometry.angle q₁ q q₁
            = InnerProductGeometry.angle (q₁ - q) (q₁ - q) := by
          simp [EuclideanGeometry.angle, vsub_eq_sub]
        rw [hbr0]
        exact InnerProductGeometry.angle_self (sub_ne_zero.mpr hq₁q)
      rw [h0]
      exact hA0
    · have h1 := hmax z hz q₁ hq₁S hzq hq₁q hz₁
      rwa [EuclideanGeometry.angle_comm z q q₁] at h1
  have hmax₂ : ∀ z ∈ S, z ≠ q → EuclideanGeometry.angle q₂ q z ≤ A := by
    intro z hz hzq
    by_cases hz₂ : z = q₂
    · rw [hz₂]
      have h0 : EuclideanGeometry.angle q₂ q q₂ = 0 := by
        have hbr0 : EuclideanGeometry.angle q₂ q q₂
            = InnerProductGeometry.angle (q₂ - q) (q₂ - q) := by
          simp [EuclideanGeometry.angle, vsub_eq_sub]
        rw [hbr0]
        exact InnerProductGeometry.angle_self (sub_ne_zero.mpr hq₂q)
      rw [h0]
      exact hA0
    · have h1 := hmax z hz q₂ hq₂S hzq hq₂q hz₂
      rwa [EuclideanGeometry.angle_comm z q q₂] at h1
  have hu : q₁ - q
      = (‖q₁ - q‖ : ℂ) * Complex.exp ((Complex.arg (q₁ - q) : ℂ) * Complex.I) :=
    (Complex.norm_mul_exp_arg_mul_I _).symm
  set β := Complex.arg (q₁ - q) with hβdef
  rcases le_or_gt 0 (Complex.arg ((starRingEnd ℂ) (q₁ - q) * (q₂ - q))) with hge | hlt
  · -- `q₂` is CCW from `q₁` by `A`: rotate so that `q₂` lands at `−δ/2`.
    have harg : Complex.arg ((starRingEnd ℂ) (q₁ - q) * (q₂ - q)) = A :=
      (abs_of_nonneg hge).symm.trans habsarg
    have hw := polar_of_arg_conj_mul hu0 harg
    rw [← hβdef] at hw
    set η := Complex.exp ((-((β + A) + δ / 2) : ℝ) * Complex.I) with hηdef
    have hη0 : η ≠ 0 := Complex.exp_ne_zero _
    have hηn : ‖η‖ = 1 := by
      rw [hηdef]
      exact Complex.norm_exp_ofReal_mul_I _
    have hnormη : ∀ x : ℂ, ‖η * x‖ = ‖x‖ := by
      intro x
      rw [norm_mul, hηn, one_mul]
    refine ⟨η, hη0, q, hq, hqne, ?_⟩
    intro p hp pnej
    obtain ⟨z, hzS, rfl⟩ := Finset.mem_image.mp hp
    have hzq : z ≠ q := fun h => pnej (by rw [h])
    have hnorm₁ : (0 : ℝ) < ‖η * q₁ - η * q‖ := by
      have hnz : η * q₁ - η * q ≠ 0 := by
        rw [← mul_sub]
        exact mul_ne_zero hη0 (sub_ne_zero.mpr hq₁q)
      exact norm_pos_iff.mpr hnz
    have hnorm₂ : (0 : ℝ) < ‖η * q₂ - η * q‖ := by
      have hnz : η * q₂ - η * q ≠ 0 := by
        rw [← mul_sub]
        exact mul_ne_zero hη0 (sub_ne_zero.mpr hq₂q)
      exact norm_pos_iff.mpr hnz
    have hnormz : (0 : ℝ) < ‖η * z - η * q‖ := by
      have hnz : η * z - η * q ≠ 0 := by
        rw [← mul_sub]
        exact mul_ne_zero hη0 (sub_ne_zero.mpr hzq)
      exact norm_pos_iff.mpr hnz
    have hexp1 : η * Complex.exp ((β : ℂ) * Complex.I)
        = Complex.exp ((-(δ / 2 + A) : ℝ) * Complex.I) := by
      rw [hηdef, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hexp2 : η * Complex.exp (((β + A : ℝ) : ℂ) * Complex.I)
        = Complex.exp ((-(δ / 2) : ℝ) * Complex.I) := by
      rw [hηdef, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hη₁ : η * q₁ - η * q
        = (‖η * q₁ - η * q‖ : ℂ) * Complex.exp ((-(δ / 2 + A) : ℝ) * Complex.I) := by
      rw [show η * q₁ - η * q = η * (q₁ - q) from by rw [mul_sub], hnormη]
      nth_rewrite 1 [hu]
      rw [mul_left_comm, ← hexp1]
    have hη₂ : η * q₂ - η * q
        = (‖η * q₂ - η * q‖ : ℂ) * Complex.exp ((-(δ / 2) : ℝ) * Complex.I) := by
      rw [show η * q₂ - η * q = η * (q₂ - q) from by rw [mul_sub], hnormη]
      nth_rewrite 1 [hw]
      rw [mul_left_comm, ← hexp2]
    have hform' : η * z - η * q
        = (‖η * z - η * q‖ : ℂ)
          * Complex.exp ((Complex.arg (η * z - η * q) : ℂ) * Complex.I) :=
      (Complex.norm_mul_exp_arg_mul_I _).symm
    have ha₁ : EuclideanGeometry.angle (η * q₂) (η * q) (η * z) ≤ A := by
      rw [euclidean_angle_const_mul hη0]
      exact hmax₂ z hzS hzq
    have ha₂ : EuclideanGeometry.angle (η * q₁) (η * q) (η * z) ≤ A := by
      rw [euclidean_angle_const_mul hη0]
      exact hmax₁ z hzS hzq
    exact dirIndex_ne_zero_of_max_arc hn hA0 hAπ hδ0 hΘ
      hnorm₂ hnorm₁ hnormz hη₂ hη₁ hform' ha₁ ha₂
  · -- `q₂` is CW from `q₁` by `A`: rotate so that `q₁` lands at `−δ/2`.
    have hargneg : -Complex.arg ((starRingEnd ℂ) (q₁ - q) * (q₂ - q)) = A := by
      have habs : |Complex.arg ((starRingEnd ℂ) (q₁ - q) * (q₂ - q))|
          = -Complex.arg ((starRingEnd ℂ) (q₁ - q) * (q₂ - q)) := abs_of_neg hlt
      rw [habsarg] at habs
      linarith
    have harg : Complex.arg ((starRingEnd ℂ) (q₁ - q) * (q₂ - q)) = -A := by
      rw [← hargneg]
      ring
    have hw := polar_of_arg_conj_mul hu0 harg
    rw [← hβdef] at hw
    set η := Complex.exp ((-(β + δ / 2) : ℝ) * Complex.I) with hηdef
    have hη0 : η ≠ 0 := Complex.exp_ne_zero _
    have hηn : ‖η‖ = 1 := by
      rw [hηdef]
      exact Complex.norm_exp_ofReal_mul_I _
    have hnormη : ∀ x : ℂ, ‖η * x‖ = ‖x‖ := by
      intro x
      rw [norm_mul, hηn, one_mul]
    refine ⟨η, hη0, q, hq, hqne, ?_⟩
    intro p hp pnej
    obtain ⟨z, hzS, rfl⟩ := Finset.mem_image.mp hp
    have hzq : z ≠ q := fun h => pnej (by rw [h])
    have hnorm₁ : (0 : ℝ) < ‖η * q₁ - η * q‖ := by
      have hnz : η * q₁ - η * q ≠ 0 := by
        rw [← mul_sub]
        exact mul_ne_zero hη0 (sub_ne_zero.mpr hq₁q)
      exact norm_pos_iff.mpr hnz
    have hnorm₂ : (0 : ℝ) < ‖η * q₂ - η * q‖ := by
      have hnz : η * q₂ - η * q ≠ 0 := by
        rw [← mul_sub]
        exact mul_ne_zero hη0 (sub_ne_zero.mpr hq₂q)
      exact norm_pos_iff.mpr hnz
    have hnormz : (0 : ℝ) < ‖η * z - η * q‖ := by
      have hnz : η * z - η * q ≠ 0 := by
        rw [← mul_sub]
        exact mul_ne_zero hη0 (sub_ne_zero.mpr hzq)
      exact norm_pos_iff.mpr hnz
    have hexp1 : η * Complex.exp ((β : ℂ) * Complex.I)
        = Complex.exp ((-(δ / 2) : ℝ) * Complex.I) := by
      rw [hηdef, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hexp2 : η * Complex.exp (((β + -A : ℝ) : ℂ) * Complex.I)
        = Complex.exp ((-(δ / 2 + A) : ℝ) * Complex.I) := by
      rw [hηdef, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hη₁ : η * q₁ - η * q
        = (‖η * q₁ - η * q‖ : ℂ) * Complex.exp ((-(δ / 2) : ℝ) * Complex.I) := by
      rw [show η * q₁ - η * q = η * (q₁ - q) from by rw [mul_sub], hnormη]
      nth_rewrite 1 [hu]
      rw [mul_left_comm, ← hexp1]
    have hη₂ : η * q₂ - η * q
        = (‖η * q₂ - η * q‖ : ℂ) * Complex.exp ((-(δ / 2 + A) : ℝ) * Complex.I) := by
      rw [show η * q₂ - η * q = η * (q₂ - q) from by rw [mul_sub], hnormη]
      nth_rewrite 1 [hw]
      rw [mul_left_comm, ← hexp2]
    have hform' : η * z - η * q
        = (‖η * z - η * q‖ : ℂ)
          * Complex.exp ((Complex.arg (η * z - η * q) : ℂ) * Complex.I) :=
      (Complex.norm_mul_exp_arg_mul_I _).symm
    have ha₁ : EuclideanGeometry.angle (η * q₁) (η * q) (η * z) ≤ A := by
      rw [euclidean_angle_const_mul hη0]
      exact hmax₁ z hzS hzq
    have ha₂ : EuclideanGeometry.angle (η * q₂) (η * q) (η * z) ≤ A := by
      rw [euclidean_angle_const_mul hη0]
      exact hmax₂ z hzS hzq
    exact dirIndex_ne_zero_of_max_arc hn hA0 hAπ hδ0 hΘ
      hnorm₁ hnorm₂ hnormz hη₁ hη₂ hform' ha₁ ha₂
set_option maxHeartbeats 1000000 in
/-- Multiplication by a nonzero complex number, as an invertible real-linear
map of the plane. -/
noncomputable def mulCLinearEquiv (c : ℂ) (hc : c ≠ 0) : ℂ ≃ₗ[ℝ] ℂ where
  toFun z := c * z
  invFun z := c⁻¹ * z
  map_add' x y := by ring
  map_smul' r x := by
    simp only [Complex.real_smul, RingHom.id_apply]
    ring
  left_inv z := inv_mul_cancel_left₀ hc z
  right_inv z := by
    show c * (c⁻¹ * z) = z
    rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]

set_option maxHeartbeats 1000000 in
/-- Non-extremality is preserved under multiplication by a nonzero complex
number. -/
lemma notMem_extremeFinset_const_mul {S : Finset ℂ} {q : ℂ}
    (hq : q ∉ extremeFinset S) {c : ℂ} (hc : c ≠ 0) :
    c * q ∉ extremeFinset (S.image (fun z => c * z)) := by
  intro hcon
  apply hq
  rw [mem_extremeFinset] at hcon ⊢
  have hcoe : (↑(S.image fun z => c * z) : Set ℂ)
      = ⇑(mulCLinearEquiv c hc) '' (↑S : Set ℂ) := by
    rw [Finset.coe_image]
    exact Set.image_congr (fun z _ => rfl)
  have he : ⇑(mulCLinearEquiv c hc).toLinearMap = ⇑(mulCLinearEquiv c hc) := rfl
  have hconv : convexHull ℝ (⇑(mulCLinearEquiv c hc) '' (↑S : Set ℂ))
      = ⇑(mulCLinearEquiv c hc) '' convexHull ℝ (↑S : Set ℂ) := by
    rw [← he, LinearMap.image_convexHull (mulCLinearEquiv c hc).toLinearMap]
  rw [hcoe, hconv, ← image_extremePoints (mulCLinearEquiv c hc)] at hcon
  obtain ⟨x, hx, heq⟩ :=
    (Set.mem_image ⇑(mulCLinearEquiv c hc) _ (c * q)).mp hcon
  have hxx : ⇑(mulCLinearEquiv c hc) x = c * x := rfl
  have hxeq : x = q := mul_left_cancel₀ hc (hxx.trans heq)
  rw [← hxeq]
  exact hx

set_option maxHeartbeats 2000000 in
/-- **Strict counting bound** (Erdős–Szekeres 1960, Theorem 3).  If every
angle determined by a finite point set is strictly less than `π (1 - 1/n)`
with `n ≥ 3`, then the set has at most `2 ^ n - 2` points. -/
theorem strictCountingBound {n : ℕ} (hn : 3 ≤ n) : StrictCountingBound n := by
  classical
  refine scb_of_no_extremal hn ?_
  intro T hTcard hTangle
  have hgen := hgen_of_hangle_lt hn hTangle
  have hS3 : 3 ≤ T.card := by
    have h := two_pow_ge_eight' hn
    omega
  obtain ⟨η, hη0, q, hqS, hqne, hiso0⟩ :=
    exists_isolated_interior hn hS3 hTangle hgen (le_of_eq hTcard.symm)
  set S' : Finset ℂ := T.image (fun z => η * z) with hS'def
  have hinj : Function.Injective (fun z : ℂ => η * z) :=
    fun x y hxy => mul_left_cancel₀ hη0 hxy
  have hcard' : S'.card = T.card := Finset.card_image_of_injective T hinj
  have hS3' : 3 ≤ S'.card := by omega
  have himgmem : ∀ x ∈ S', ∃ x₀ ∈ T, η * x₀ = x := by
    intro x hx
    rw [hS'def] at hx
    exact Finset.mem_image.mp hx
  have hangle' : ∀ p ∈ S', ∀ q ∈ S', ∀ r ∈ S', p ≠ q → r ≠ q →
      EuclideanGeometry.angle p q r < (1 - 1 / (n : ℝ)) * π := by
    intro p hp q hq r hr hpq hrq
    obtain ⟨p₀, hp₀, hp_eq⟩ := himgmem p hp
    obtain ⟨q₀, hq₀, hq_eq⟩ := himgmem q hq
    obtain ⟨r₀, hr₀, hr_eq⟩ := himgmem r hr
    have hpq0 : p₀ ≠ q₀ := fun h => hpq (by rw [← hp_eq, ← hq_eq, h])
    have hrq0 : r₀ ≠ q₀ := fun h => hrq (by rw [← hr_eq, ← hq_eq, h])
    have h2 : EuclideanGeometry.angle p q r = EuclideanGeometry.angle p₀ q₀ r₀ := by
      rw [← hp_eq, ← hq_eq, ← hr_eq, euclidean_angle_const_mul hη0]
    rw [h2]
    exact hTangle p₀ hp₀ q₀ hq₀ r₀ hr₀ hpq0 hrq0
  have hgen' : ∀ a ∈ S', ∀ b ∈ S', ∀ c ∈ S', a ≠ b → b ≠ c → a ≠ c →
      ¬ Collinear ℝ ({a, b, c} : Set ℂ) := by
    intro a ha b hb c hc hab hbc hac hcol
    obtain ⟨a₀, ha₀, rfl⟩ := himgmem a ha
    obtain ⟨b₀, hb₀, rfl⟩ := himgmem b hb
    obtain ⟨c₀, hc₀, rfl⟩ := himgmem c hc
    have hab0 : a₀ ≠ b₀ := fun h => hab (by rw [h])
    have hbc0 : b₀ ≠ c₀ := fun h => hbc (by rw [h])
    have hac0 : a₀ ≠ c₀ := fun h => hac (by rw [h])
    have h2 := collinear_const_mul (inv_ne_zero hη0) hcol
    rw [inv_mul_cancel_left₀ hη0 a₀, inv_mul_cancel_left₀ hη0 b₀,
      inv_mul_cancel_left₀ hη0 c₀] at h2
    exact hgen a₀ ha₀ b₀ hb₀ c₀ hc₀ hab0 hbc0 hac0 h2
  set q' : ℂ := η * q with hq'def
  have hq'S' : q' ∈ S' := Finset.mem_image.mpr ⟨q, hqS, rfl⟩
  have hqne' : q' ∉ extremeFinset S' := notMem_extremeFinset_const_mul hqne hη0
  obtain ⟨w, hmem, hsur, hmono⟩ := exists_argSorted_enum hS3' hgen'
  have hm3' : 3 ≤ (extremeFinset S').card := three_le_card_extremeFinset hS3' hgen'
  obtain ⟨i, k, hisoH⟩ :=
    exists_isolated_hull_vertex hn hS3' hangle' hgen' w hmem hsur hmono hm3'
  have hwiE : w i ∈ extremeFinset S' := hmem i
  have hwiS' : w i ∈ S' := mem_of_mem_extremeFinset hwiE
  have hpne : q' ≠ w i := by
    intro h
    apply hqne'
    rw [h]
    exact hwiE
  have hn0 : (0 : ℕ) < n := by omega
  set V : Type := {x // x ∈ S'} with hVdef
  haveI : Fintype V := Finset.Subtype.fintype S'
  haveI : DecidableEq V := fun a b => Classical.propDecidable (a = b)
  set p₁ : V := ⟨q', hq'S'⟩ with hp₁def
  set p₂ : V := ⟨w i, hwiS'⟩ with hp₂def
  have hpneV : p₁ ≠ p₂ := fun h => hpne (congrArg Subtype.val h)
  -- If `u → v` is positively oriented, then `v` has no positive outgoing
  -- edge in the sector of `u → v` (strict angle version).
  have key : ∀ u v : V, (u : ℂ) ≠ (v : ℂ) →
      IsPos ((v : ℂ) - (u : ℂ)) →
      ¬ ∃ z : V, (z : ℂ) ≠ (v : ℂ) ∧ IsPos ((z : ℂ) - (v : ℂ)) ∧
        dirIndex n ((z : ℂ) - (v : ℂ)) = dirIndex n ((v : ℂ) - (u : ℂ)) := by
    rintro u v huv hpos ⟨z, hzv, hzpos, hzcol⟩
    have hpq : (v : ℂ) - (u : ℂ) ≠ 0 := sub_ne_zero.mpr huv.symm
    have hqr : (z : ℂ) - (v : ℂ) ≠ 0 := sub_ne_zero.mpr hzv
    have hbig := lt_angle_of_isPos_of_dirIndex_eq hn0 hpq hqr hpos hzpos hzcol.symm
    have hle := hangle' (u : ℂ) u.2 (v : ℂ) v.2 (z : ℂ) z.2 huv hzv
    linarith
  set color : V → V → Fin n :=
    fun u v => ⟨dirIndex n ((v : ℂ) - (u : ℂ)), dirIndex_lt hn0 _⟩ with hcolordef
  have color_val : ∀ u v : V, (color u v : ℕ) = dirIndex n ((v : ℂ) - (u : ℂ)) :=
    fun u v => rfl
  set side : Fin n → V → Bool :=
    fun i v => decide (∃ z : V, (z : ℂ) ≠ (v : ℂ) ∧ IsPos ((z : ℂ) - (v : ℂ)) ∧
      dirIndex n ((z : ℂ) - (v : ℂ)) = (i : ℕ)) with hsidedef
  have hside : ∀ u v : V, u ≠ v → side (color u v) u ≠ side (color u v) v := by
    intro u v huv
    have huv' : (u : ℂ) ≠ (v : ℂ) := fun h => huv (Subtype.ext h)
    have hz : (v : ℂ) - (u : ℂ) ≠ 0 := sub_ne_zero.mpr huv'.symm
    have hdi : dirIndex n ((u : ℂ) - (v : ℂ)) = dirIndex n ((v : ℂ) - (u : ℂ)) := by
      rw [show ((u : ℂ) - (v : ℂ)) = -((v : ℂ) - (u : ℂ)) by ring, dirIndex_neg]
    by_cases hpos : IsPos ((v : ℂ) - (u : ℂ))
    · have e1 : side (color u v) u = true := by
        show decide (∃ z : V, (z : ℂ) ≠ (u : ℂ) ∧ IsPos ((z : ℂ) - (u : ℂ)) ∧
            dirIndex n ((z : ℂ) - (u : ℂ)) = (color u v : ℕ)) = true
        refine decide_eq_true ⟨v, huv'.symm, hpos, ?_⟩
        rw [color_val]
      have e2 : side (color u v) v = false := by
        show decide (∃ z : V, (z : ℂ) ≠ (v : ℂ) ∧ IsPos ((z : ℂ) - (v : ℂ)) ∧
            dirIndex n ((z : ℂ) - (v : ℂ)) = (color u v : ℕ)) = false
        refine decide_eq_false ?_
        rintro ⟨z, hzv, hzpos, hzcol⟩
        rw [color_val] at hzcol
        exact key u v huv' hpos ⟨z, hzv, hzpos, hzcol⟩
      rw [e1, e2]
      simp
    · have hpos' : IsPos ((u : ℂ) - (v : ℂ)) := by
        rw [show ((u : ℂ) - (v : ℂ)) = -((v : ℂ) - (u : ℂ)) by ring]
        exact (isPos_neg_iff hz).mpr hpos
      have e1 : side (color u v) u = false := by
        show decide (∃ z : V, (z : ℂ) ≠ (u : ℂ) ∧ IsPos ((z : ℂ) - (u : ℂ)) ∧
            dirIndex n ((z : ℂ) - (u : ℂ)) = (color u v : ℕ)) = false
        refine decide_eq_false ?_
        rintro ⟨z, hzu, hzpos, hzcol⟩
        rw [color_val] at hzcol
        exact key v u huv'.symm hpos' ⟨z, hzu, hzpos, hzcol.trans hdi.symm⟩
      have e2 : side (color u v) v = true := by
        show decide (∃ z : V, (z : ℂ) ≠ (v : ℂ) ∧ IsPos ((z : ℂ) - (v : ℂ)) ∧
            dirIndex n ((z : ℂ) - (v : ℂ)) = (color u v : ℕ)) = true
        refine decide_eq_true ⟨u, huv', hpos', ?_⟩
        rw [color_val]
        exact hdi
      rw [e1, e2]
      simp
  have hsymm : ∀ u v : V, color u v = color v u := by
    intro u v
    apply Fin.val_injective
    show dirIndex n ((v : ℂ) - (u : ℂ)) = dirIndex n ((u : ℂ) - (v : ℂ))
    rw [show ((u : ℂ) - (v : ℂ)) = -((v : ℂ) - (u : ℂ)) by ring, dirIndex_neg]
  have hN : (Finset.univ : Finset V).card + 1 = 2 ^ n := by
    have hcv : (Finset.univ : Finset V).card = S'.card := Fintype.card_coe S'
    omega
  have hsum := emptyCount_sum_le n V 1 Finset.univ color side
    (fun u _ v _ huv => hside u v huv) hsymm hN
  -- Each isolated point contributes at least `1` to the sum.
  have he1 : (1 : ℕ) ≤ emptyCountIn color Finset.univ p₁ := by
    have hm : (⟨0, hn0⟩ : Fin n) ∈ emptyFilter color Finset.univ p₁ := by
      rw [mem_emptyFilter]
      intro u _ hune hzero
      have hd : dirIndex n ((u : ℂ) - q') ≠ 0 :=
        hiso0 (u : ℂ) u.2 (fun h => hune (Subtype.ext h))
      apply hd
      have hv : (color p₁ u : ℕ) = 0 := congrArg Fin.val hzero
      rw [color_val p₁ u] at hv
      exact hv
    have hcz : (emptyFilter color Finset.univ p₁).card ≠ 0 := by
      intro h0
      rw [Finset.card_eq_zero] at h0
      rw [h0] at hm
      exact Finset.notMem_empty _ hm
    unfold emptyCountIn
    omega
  have he2 : (1 : ℕ) ≤ emptyCountIn color Finset.univ p₂ := by
    have hm : k ∈ emptyFilter color Finset.univ p₂ := by
      rw [mem_emptyFilter]
      intro u _ hune hzero
      have hd : dirIndex n ((u : ℂ) - w i) ≠ (k : ℕ) :=
        hisoH (u : ℂ) u.2 (fun h => hune (Subtype.ext h))
      apply hd
      have hv : (color p₂ u : ℕ) = (k : ℕ) := congrArg Fin.val hzero
      rw [color_val p₂ u] at hv
      exact hv
    have hcz : (emptyFilter color Finset.univ p₂).card ≠ 0 := by
      intro h0
      rw [Finset.card_eq_zero] at h0
      rw [h0] at hm
      exact Finset.notMem_empty _ hm
    unfold emptyCountIn
    omega
  have hlow : (2 : ℕ) ≤ ∑ p ∈ Finset.univ,
      (2 ^ emptyCountIn color Finset.univ p - 1) := by
    have h2le : (2 : ℕ) ≤ (2 ^ emptyCountIn color Finset.univ p₁ - 1)
        + (2 ^ emptyCountIn color Finset.univ p₂ - 1) := by
      have hp1 : (2 : ℕ) ≤ 2 ^ emptyCountIn color Finset.univ p₁ := by
        have h1 := he1
        calc (2:ℕ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ emptyCountIn color Finset.univ p₁ := pow_two_le_pow_two (by omega)
      have hp2 : (2 : ℕ) ≤ 2 ^ emptyCountIn color Finset.univ p₂ := by
        have h2 := he2
        calc (2:ℕ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ emptyCountIn color Finset.univ p₂ := pow_two_le_pow_two (by omega)
      omega
    have hpair : (2 ^ emptyCountIn color Finset.univ p₁ - 1)
        + (2 ^ emptyCountIn color Finset.univ p₂ - 1)
        = ∑ p ∈ ({p₁, p₂} : Finset V),
            (2 ^ emptyCountIn color Finset.univ p - 1) := by
      rw [Finset.sum_insert
        (show p₁ ∉ ({p₂} : Finset V) from fun h => hpneV (Finset.mem_singleton.mp h))]
      rw [Finset.sum_singleton]
    calc (2 : ℕ) ≤ (2 ^ emptyCountIn color Finset.univ p₁ - 1)
            + (2 ^ emptyCountIn color Finset.univ p₂ - 1) := h2le
      _ = ∑ p ∈ ({p₁, p₂} : Finset V),
            (2 ^ emptyCountIn color Finset.univ p - 1) := hpair
      _ ≤ ∑ p ∈ Finset.univ, (2 ^ emptyCountIn color Finset.univ p - 1) :=
            Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  omega
