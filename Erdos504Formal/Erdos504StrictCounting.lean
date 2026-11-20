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