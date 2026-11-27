import Erdos504Formal.Erdos504SendovSe95Correction
import Mathlib.Order.Interval.Set.Infinite

open scoped BigOperators

namespace Erdos504.SendovStage1.Se95Bridge

/-!
The geometric leaves below are the centers of the primitive circles.
The two child disks at each vertex are placed with a common translation.
This preserves their prescribed direction while permitting global avoidance
of all collinear triples of circle centers, including ancestor centers.

The gap in Sendov's Lemma 4.1 (the asserted s = 4 maxima) was first publicly
reported by NoahPuckett-IO in teorth/erdosproblems#494 (2026-10-26,
https://github.com/teorth/erdosproblems/issues/494), and this development
independently supplies exact-coordinate counterexamples, Lean machine checks,
and a refutation of the published proof along the Lemma 4.1 to Lemma 4.2 to
Theorem 4.1 chain.
-/

private noncomputable def det (u v : ℂ) : ℝ := u.re * v.im - u.im * v.re

private noncomputable def turn (a b c : ℂ) : ℝ := det (b - a) (c - a)

private lemma turn_cycle (a b c : ℂ) : turn a b c = turn b c a := by
  simp only [turn, det, Complex.sub_re, Complex.sub_im]
  ring

private lemma turn_swap (a b c : ℂ) : turn a b c = -turn b a c := by
  simp only [turn, det, Complex.sub_re, Complex.sub_im]
  ring

private lemma turn_flip (a b c : ℂ) : turn a b c = -turn a c b := by
  simp only [turn, det]
  ring

/-- A finite set of circle centers in general position. -/
def InGeneralPosition (S : Finset ℂ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → c ≠ a → turn a b c ≠ 0

lemma InGeneralPosition.mono {S T : Finset ℂ} (good : InGeneralPosition T) (sub : S ⊆ T) :
    InGeneralPosition S := by
  intro a ha b hb c hc
  exact good a (sub ha) b (sub hb) c (sub hc)

private lemma generalPosition_insert (S : Finset ℂ) [DecidableEq ℂ]
    (good : InGeneralPosition S) {p : ℂ}
    (freshTurn : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → turn a b p ≠ 0) :
    InGeneralPosition (insert p S) := by
  intro a ha b hb c hc hab hbc hca
  simp only [Finset.mem_insert] at ha hb hc
  rcases ha with rfl | ha
  · have hb := hb.resolve_left hab.symm
    have hc := hc.resolve_left hca
    rw [turn_cycle]
    exact freshTurn b hb c hc hbc
  rcases hb with rfl | hb
  · have hc := hc.resolve_left hbc.symm
    rw [turn_flip, neg_ne_zero]
    exact freshTurn a ha c hc hca.symm
  rcases hc with rfl | hc
  · exact freshTurn a ha b hb hab
  · exact good a ha b hb c hc hab hbc hca

private lemma turn_zero_iff_collinear {a b c : ℂ} (hab : a ≠ b) :
    turn a b c = 0 ↔ Collinear ℝ ({a, b, c} : Set ℂ) := by
  rw [collinear_iff_of_mem (Set.mem_insert a _)]
  constructor
  · intro h
    let v := b - a
    let w := c - a
    change det v w = 0 at h
    have hv : v ≠ 0 := sub_ne_zero.mpr hab.symm
    have hw : ∃ r : ℝ, w = r • v := by
      by_cases hre : v.re = 0
      · have him : v.im ≠ 0 := fun hvim => hv (Complex.ext hre hvim)
        have hwre : w.re = 0 := by
          simp only [det, hre, zero_mul, zero_sub, neg_eq_zero, mul_eq_zero] at h
          exact h.resolve_left him
        refine ⟨w.im / v.im, Complex.ext ?_ ?_⟩
        · simp [hre, hwre]
        · simp only [Complex.smul_im, smul_eq_mul, div_mul_cancel₀ _ him]
      · refine ⟨w.re / v.re, Complex.ext ?_ ?_⟩
        · simp only [Complex.smul_re, smul_eq_mul, div_mul_cancel₀ _ hre]
        · simp only [Complex.smul_im, smul_eq_mul, det, sub_eq_zero] at *
          rw [div_mul_eq_mul_div]
          exact (eq_div_iff hre).mpr (by simpa [mul_comm] using h)
    refine ⟨v, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with hp | hp | hp
    · exact ⟨0, by rw [hp]; simp⟩
    · exact ⟨1, by rw [hp]; change b = (1 : ℝ) • (b - a) + a; simp⟩
    · obtain ⟨r, hr⟩ := hw
      exact ⟨r, by rw [hp]; change c = r • (b - a) + a; rw [← hr]; exact (sub_add_cancel _ _).symm⟩
  · rintro ⟨v, h⟩
    obtain ⟨x, hx⟩ := h b (by simp)
    obtain ⟨y, hy⟩ := h c (by simp)
    change b = x • v + a at hx
    change c = y • v + a at hy
    rw [hx, hy]
    simp only [turn, add_sub_cancel_right, det, Complex.smul_re, Complex.smul_im, smul_eq_mul]
    ring

lemma InGeneralPosition.not_collinear {S : Finset ℂ} (good : InGeneralPosition S)
    {a b c : ℂ} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    ¬ Collinear ℝ ({a, b, c} : Set ℂ) :=
  fun h => good a ha b hb c hc hab hbc hca ((turn_zero_iff_collinear hab).mpr h)

private lemma finite_affineZeros (a b : ℝ) (ha : a ≠ 0) :
    {x : ℝ | a * x + b = 0}.Finite := by
  refine (Set.finite_singleton (-b / a)).subset ?_
  intro x hx
  rw [Set.mem_singleton_iff, eq_div_iff ha]
  change a * x + b = 0 at hx
  linarith only [hx, mul_comm a x]

private lemma steering_exists (W : Finset ℂ) :
    ∃ u : ℂ, u.re = 1 ∧ ∀ w ∈ W, w ≠ 0 → det w u ≠ 0 := by
  classical
  obtain ⟨x, hx⟩ := (W.image (fun w => w.im / w.re)).exists_notMem
  refine ⟨⟨1, x⟩, rfl, ?_⟩
  intro w hw hn hz
  change w.re * x - w.im * 1 = 0 at hz
  have hre : w.re ≠ 0 := by
    intro hr
    rw [hr, zero_mul, mul_one] at hz
    simp only [zero_sub, neg_eq_zero] at hz
    exact hn (Complex.ext hr hz)
  apply hx
  have he : w.im / w.re = x := (div_eq_iff hre).mpr (by linarith [mul_comm w.re x])
  exact Finset.mem_image.mpr ⟨w, hw, he⟩

/-- Two children can be placed along a prescribed signed direction. A single
translation avoids the finitely many forbidden positions for both children. -/
private lemma placeChildren (S : Finset ℂ) [DecidableEq ℂ] (g : InGeneralPosition S)
    (p v : ℂ) (hv : v ≠ 0) (R : ℝ) (hR : 0 < R) :
    ∃ a b : ℂ, a ∉ S ∧ b ∉ S ∧
      ‖a - p‖ < R / 8 ∧ ‖b - p‖ < 3 * R / 8 ∧ ‖b - a‖ = R / 4 ∧
      (∃ r : ℝ, 0 < r ∧ b - a = r • v) ∧ InGeneralPosition (insert b (insert a S)) := by
  classical
  let r := R / 4 / ‖v‖
  have hr : 0 < r := div_pos (by linarith) (norm_pos_iff.mpr hv)
  let w := r • v
  have hw : w ≠ 0 := smul_ne_zero hr.ne' hv
  have hnorm : ‖w‖ = R / 4 := by
    rw [show w = r • v from rfl, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hv)
  let W := insert w (S.product S |>.image (fun (a, b) => b - a))
  obtain ⟨u, hu, huW⟩ := steering_exists W
  have hu0 : u ≠ 0 := fun h => by simp [h] at hu
  have hwdir : det w u ≠ 0 := huW w (by simp [W]) hw
  have hold (a b : S) (h : a.val ≠ b.val) : det (b.val - a.val) u ≠ 0 := by
    apply huW _ _ (sub_ne_zero.mpr h.symm)
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨(a.val, b.val), Finset.mem_product.mpr ⟨a.property, b.property⟩, rfl⟩
  let move (e : Bool) (x : ℝ) := p + x • u + if e then w else 0
  let pointsBad := ⋃ e : Bool, ⋃ a : S, {x : ℝ | (move e x).re = a.val.re}
  let oldBad := ⋃ e : Bool, ⋃ a : S, ⋃ b : {b : S // a.val ≠ b.val},
    {x : ℝ | turn a.val b.val.val (move e x) = 0}
  let pairBad := ⋃ a : S, {x : ℝ | det w (a.val - move false x) = 0}
  have fpoint : pointsBad.Finite := by
    apply Set.finite_iUnion
    intro e
    apply Set.finite_iUnion
    intro a
    refine (finite_affineZeros 1 (p.re + (if e then w else 0).re - a.val.re) one_ne_zero).subset ?_
    intro x hx
    change (move e x).re = a.val.re at hx
    simp only [move, Complex.add_re, Complex.smul_re, smul_eq_mul, hu, mul_one] at hx
    change 1 * x + _ = 0
    linarith
  have fold : oldBad.Finite := by
    apply Set.finite_iUnion
    intro e
    apply Set.finite_iUnion
    intro a
    apply Set.finite_iUnion
    intro b
    refine (finite_affineZeros _ (turn a.val b.val.val (move e 0)) (hold a b.val b.property)).subset ?_
    intro x hx
    change turn a.val b.val.val (move e x) = 0 at hx
    change det (b.val.val - a.val) u * x + turn a.val b.val.val (move e 0) = 0
    calc
      _ = turn a.val b.val.val (move e x) := by
        simp only [turn, det, move, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
          Complex.smul_re, Complex.smul_im, smul_eq_mul]
        ring
      _ = 0 := hx
  have fpair : pairBad.Finite := by
    apply Set.finite_iUnion
    intro a
    refine (finite_affineZeros (-det w u) (det w (a.val - p)) (neg_ne_zero.mpr hwdir)).subset ?_
    intro x hx
    change det w (a.val - move false x) = 0 at hx
    change -det w u * x + det w (a.val - p) = 0
    rw [← hx]
    simp [move, det]
    ring
  let ρ := R / 8 / ‖u‖
  have hρ : 0 < ρ := div_pos (by linarith) (norm_pos_iff.mpr hu0)
  have hinf : (Set.Ioo (-ρ) ρ).Infinite := Set.Ioo_infinite (by linarith)
  obtain ⟨x, hx, hgood⟩ := hinf.exists_notMem_finite ((fpoint.union fold).union fpair)
  have hp0 : x ∉ pointsBad := fun h => hgood (Or.inl (Or.inl h))
  have hp1 : x ∉ oldBad := fun h => hgood (Or.inl (Or.inr h))
  have hp2 : x ∉ pairBad := fun h => hgood (Or.inr h)
  let a := move false x
  let b := move true x
  have hba : b - a = w := by simp [a, b, move]
  have hshift : ‖x • u‖ < R / 8 := by
    rw [norm_smul, Real.norm_eq_abs]
    exact (lt_div_iff₀ (norm_pos_iff.mpr hu0)).mp (abs_lt.mpr hx)
  have fresh (e : Bool) : move e x ∉ S := by
    intro h
    apply hp0
    exact Set.mem_iUnion.mpr ⟨e, Set.mem_iUnion.mpr ⟨⟨move e x, h⟩, rfl⟩⟩
  have clean (e : Bool) (a' : ℂ) (ha' : a' ∈ S) (b' : ℂ) (hb' : b' ∈ S) (h : a' ≠ b') :
      turn a' b' (move e x) ≠ 0 := by
    intro hbad
    apply hp1
    exact Set.mem_iUnion.mpr ⟨e, Set.mem_iUnion.mpr ⟨⟨a', ha'⟩,
      Set.mem_iUnion.mpr ⟨⟨⟨b', hb'⟩, h⟩, hbad⟩⟩⟩
  refine ⟨a, b, fresh false, fresh true, ?_, ?_, hba ▸ hnorm, ⟨r, hr, hba⟩, ?_⟩
  · simpa [a, move, add_comm p] using hshift
  · have hb : b - p = x • u + w := by
      simp only [b, move, if_true]
      abel
    rw [hb]
    have ht := norm_add_le (x • u) w
    linarith
  apply generalPosition_insert _ (generalPosition_insert _ g (clean false))
  intro y hy z hz hyz
  simp only [Finset.mem_insert] at hy hz
  have hab (c : ℂ) (hc : c ∈ S) : turn a b c ≠ 0 := by
    intro h
    apply hp2
    refine Set.mem_iUnion.mpr ⟨⟨c, hc⟩, ?_⟩
    change det w (c - a) = 0
    simpa only [turn, hba] using h
  rcases hy with rfl | hy
  · have hz := hz.resolve_left hyz.symm
    rw [turn_flip, neg_ne_zero]
    exact hab z hz
  rcases hz with rfl | hz
  · rw [turn_cycle]
    exact hab y hy
  · exact clean true y hy z hz hyz

/-- Every circle, including a primitive one, has positive radius. -/
structure Disk where
  center : ℂ
  radius : ℝ
  radius_pos : 0 < radius

def Disk.Inside (child parent : Disk) : Prop :=
  ‖child.center - parent.center‖ + child.radius < parent.radius

def Disk.Separated (left right : Disk) : Prop :=
  left.radius + right.radius < ‖right.center - left.center‖

/-- Both branches use the same remaining directions. The sign convention
orients the prescribed axis from the left child to the right child. -/
inductive CircleTree : List ℂ → Disk → Type
  | primitive (d : Disk) : CircleTree [] d
  | fork {v : ℂ} {axes : List ℂ} {d l r : Disk}
      (left : CircleTree axes l) (right : CircleTree axes r)
      (insideLeft : l.Inside d) (insideRight : r.Inside d)
      (separated : l.Separated r)
      (oriented : ∃ scale : ℝ, 0 < scale ∧ r.center - l.center = scale • v) :
      CircleTree (v :: axes) d

noncomputable def CircleTree.descendants {axes : List ℂ} {d : Disk}
    (tree : CircleTree axes d) : Finset ℂ := by
  classical
  exact match tree with
  | .primitive _ => ∅
  | .fork (l := l) (r := r) left right _ _ _ _ =>
      insert l.center (insert r.center (left.descendants ∪ right.descendants))

noncomputable def CircleTree.centers {axes : List ℂ} {d : Disk}
    (tree : CircleTree axes d) : Finset ℂ := by
  classical
  exact insert d.center tree.descendants

/-- Distinctness refers to vertices of the tree, prior to forgetting the
vertex labels and taking the finite set of centers. -/
def CircleTree.Distinct {axes : List ℂ} {d : Disk} (tree : CircleTree axes d) : Prop :=
  match tree with
  | .primitive _ => True
  | .fork left right _ _ _ _ =>
      left.Distinct ∧ right.Distinct ∧ Disjoint left.centers right.centers ∧
        d.center ∉ left.centers ∧ d.center ∉ right.centers

/-- Build one complete tree by extending an ambient set of centers. The root
has already been placed. All non-root vertices are new, and the enlarged
ambient set remains in general position. -/
theorem CircleTree.place (axes : List ℂ) (valid : ∀ v ∈ axes, v ≠ 0)
    (d : Disk) (S : Finset ℂ) (root : d.center ∈ S) (good : InGeneralPosition S) :
    ∃ tree : CircleTree axes d, tree.Distinct ∧ Disjoint tree.descendants S ∧
      InGeneralPosition (S ∪ tree.descendants) := by
  classical
  induction axes generalizing d S with
  | nil =>
    exact ⟨.primitive d, True.intro, by simp [CircleTree.descendants],
      by simpa [CircleTree.descendants] using good⟩
  | cons v axes ih =>
    obtain ⟨a, b, ha, hb, hda, hdb, hab, horient, hgood⟩ :=
      placeChildren S good d.center v (valid v (by simp)) d.radius d.radius_pos
    let l : Disk := ⟨a, d.radius / 16, by linarith [d.radius_pos]⟩
    let r : Disk := ⟨b, d.radius / 16, by linarith [d.radius_pos]⟩
    have hl : l.Inside d := by dsimp [Disk.Inside, l]; linarith [d.radius_pos]
    have hr : r.Inside d := by dsimp [Disk.Inside, r]; linarith [d.radius_pos]
    have hsep : l.Separated r := by dsimp [Disk.Separated, l, r]; linarith [d.radius_pos]
    have hne : a ≠ b := by
      intro h
      rw [h, sub_self, norm_zero] at hab
      linarith [d.radius_pos]
    let L := insert b (insert a S)
    have hvalid (w : ℂ) (hw : w ∈ axes) : w ≠ 0 := valid w (List.mem_cons_of_mem _ hw)
    obtain ⟨left, leftDistinct, leftFresh, leftGood⟩ :=
      ih hvalid l L (by simp [l, L]) hgood
    let R := L ∪ left.descendants
    obtain ⟨right, rightDistinct, rightFresh, rightGood⟩ :=
      ih hvalid r R (by simp [r, R, L]) leftGood
    let T : CircleTree (v :: axes) d := .fork left right hl hr hsep horient
    have freshLeft (z : ℂ) (hz : z ∈ left.descendants) : z ∉ L :=
      Finset.disjoint_left.mp leftFresh hz
    have freshRight (z : ℂ) (hz : z ∈ right.descendants) : z ∉ R :=
      Finset.disjoint_left.mp rightFresh hz
    have rootL : d.center ∈ L := by simp [L, root]
    have rootR : d.center ∈ R := Finset.mem_union_left _ rootL
    refine ⟨T, ?_, ?_, ?_⟩
    · change left.Distinct ∧ right.Distinct ∧ Disjoint left.centers right.centers ∧
          d.center ∉ left.centers ∧ d.center ∉ right.centers
      refine ⟨leftDistinct, rightDistinct, ?_, ?_, ?_⟩
      · apply Finset.disjoint_left.mpr
        intro z hzL hzR
        simp only [CircleTree.centers, Finset.mem_insert, l, r] at hzL hzR
        rcases hzR with rfl | hzR
        · exact hzL.elim (fun he => hne he.symm) (fun hz => freshLeft _ hz (by simp [L]))
        · apply freshRight z hzR
          rcases hzL with rfl | hzL
          · simp [R, L]
          · exact Finset.mem_union_right _ hzL
      · simp only [CircleTree.centers, Finset.mem_insert, l, not_or]
        exact ⟨fun h => ha (h ▸ root), fun h => freshLeft _ h rootL⟩
      · simp only [CircleTree.centers, Finset.mem_insert, r, not_or]
        exact ⟨fun h => hb (h ▸ root), fun h => freshRight _ h rootR⟩
    · apply Finset.disjoint_left.mpr
      intro z hz hs
      simp only [T, CircleTree.descendants, Finset.mem_insert, Finset.mem_union, l, r] at hz
      rcases hz with rfl | rfl | hz | hz
      · exact ha hs
      · exact hb hs
      · exact freshLeft z hz (by simp [L, hs])
      · exact freshRight z hz (by simp [R, L, hs])
    · apply rightGood.mono
      intro z hz
      simp only [T, R, L, CircleTree.descendants, Finset.mem_insert, Finset.mem_union, l, r] at hz ⊢
      tauto

/-- A leaf address lists one branch choice at each level, starting at the root. -/
def Leaf : ℕ → Type
  | 0 => PUnit
  | n + 1 => Bool × Leaf n

instance leafFintype : (n : ℕ) → Fintype (Leaf n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n + 1 => by
      letI := leafFintype n
      exact inferInstanceAs (Fintype (Bool × Leaf n))

lemma leaf_card (n : ℕ) : Fintype.card (Leaf n) = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Fintype.card (Bool × Leaf n) = _
    rw [Fintype.card_prod, Fintype.card_bool, ih, pow_succ, mul_comm]

/-- The signed directions given by the first unequal branch choices. -/
def wordRay : (axes : List ℂ) → Leaf axes.length → Leaf axes.length → ℂ
  | [], _, _ => 0
  | _ :: axes, (false, p), (false, q) => wordRay axes p q
  | _ :: axes, (true, p), (true, q) => wordRay axes p q
  | v :: _, (false, _), (true, _) => v
  | v :: _, (true, _), (false, _) => -v

noncomputable def CircleTree.leafPoint : {axes : List ℂ} → {d : Disk} →
    CircleTree axes d → Leaf axes.length → ℂ
  | _, _, .primitive d, _ => d.center
  | _, _, .fork left _ _ _ _ _, (false, p) => left.leafPoint p
  | _, _, .fork _ right _ _ _ _, (true, p) => right.leafPoint p

/-- Definition 2.3 on the binary circle tree. The first differing branches
have the lowest range distinguishing the two leaves. -/
noncomputable def CircleTree.generalizedRay : {axes : List ℂ} → {d : Disk} →
    CircleTree axes d → Leaf axes.length → Leaf axes.length → ℂ
  | _, _, .primitive _, _, _ => 0
  | _, _, .fork left _ _ _ _ _, (false, p), (false, q) => left.generalizedRay p q
  | _, _, .fork _ right _ _ _ _, (true, p), (true, q) => right.generalizedRay p q
  | _, _, .fork (l := l) (r := r) _ _ _ _ _ _, (false, _), (true, _) => r.center - l.center
  | _, _, .fork (l := l) (r := r) _ _ _ _ _ _, (true, _), (false, _) => l.center - r.center

lemma CircleTree.leafPoint_mem {axes : List ℂ} {d : Disk} (tree : CircleTree axes d)
    (p : Leaf axes.length) : tree.leafPoint p ∈ tree.centers := by
  classical
  induction tree with
  | primitive d => simp [CircleTree.leafPoint, CircleTree.centers]
  | fork left right _ _ _ _ ihl ihr =>
    obtain ⟨b, q⟩ := p
    cases b
    · have h := ihl q
      simp only [CircleTree.centers, Finset.mem_insert] at h
      simp only [CircleTree.leafPoint, CircleTree.centers, CircleTree.descendants, Finset.mem_insert,
        Finset.mem_union]
      tauto
    · have h := ihr q
      simp only [CircleTree.centers, Finset.mem_insert] at h
      simp only [CircleTree.leafPoint, CircleTree.centers, CircleTree.descendants, Finset.mem_insert,
        Finset.mem_union]
      tauto

lemma CircleTree.leafPoint_injective {axes : List ℂ} {d : Disk} (tree : CircleTree axes d)
    (hd : tree.Distinct) : Function.Injective tree.leafPoint := by
  classical
  induction tree with
  | primitive d =>
    intro p q _
    exact @Subsingleton.elim PUnit _ p q
  | fork left right _ _ _ _ ihl ihr =>
    rcases hd with ⟨dl, dr, disj, _, _⟩
    rintro ⟨b, p⟩ ⟨c, q⟩ h
    cases b <;> cases c
    · exact congrArg (Prod.mk false) (ihl dl h)
    · have he : left.leafPoint p = right.leafPoint q := h
      exact False.elim (Finset.disjoint_left.mp disj (left.leafPoint_mem p)
        (he.symm ▸ right.leafPoint_mem q))
    · have he : right.leafPoint p = left.leafPoint q := h
      exact False.elim (Finset.disjoint_left.mp disj (left.leafPoint_mem q)
        (he ▸ right.leafPoint_mem p))
    · exact congrArg (Prod.mk true) (ihr dr h)

lemma CircleTree.generalizedRay_direction {axes : List ℂ} {d : Disk} (tree : CircleTree axes d)
    (p q : Leaf axes.length) :
    ∃ scale : ℝ, 0 < scale ∧ tree.generalizedRay p q = scale • wordRay axes p q := by
  induction tree with
  | primitive d => exact ⟨1, one_pos, by simp [CircleTree.generalizedRay, wordRay]⟩
  | fork left right _ _ _ oriented ihl ihr =>
    obtain ⟨b, p⟩ := p
    obtain ⟨c, q⟩ := q
    cases b <;> cases c
    · exact ihl p q
    · exact oriented
    · obtain ⟨a, ha, he⟩ := oriented
      refine ⟨a, ha, ?_⟩
      simp only [CircleTree.generalizedRay, wordRay, smul_neg]
      rw [← he, neg_sub]
    · exact ihr p q

private theorem placeForest {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (axes : ι → List ℂ) (disks : ι → Disk) (valid : ∀ i v, v ∈ axes i → v ≠ 0)
    (S : Finset ℂ) (roots : ∀ i, (disks i).center ∈ S) (good : InGeneralPosition S) :
    ∃ trees : ∀ i : I, CircleTree (axes i) (disks i), ∃ extended : Finset ℂ,
      S ⊆ extended ∧ InGeneralPosition extended ∧
      (∀ i, (trees i).Distinct ∧ (trees i).centers ⊆ extended ∧ Disjoint (trees i).descendants S) ∧
      Pairwise (fun i j => Disjoint (trees i).descendants (trees j).descendants) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    refine ⟨fun i => False.elim (Finset.notMem_empty _ i.property), S, fun _ h => h, good, ?_, ?_⟩
    · intro i
      exact False.elim (Finset.notMem_empty _ i.property)
    · intro i
      exact False.elim (Finset.notMem_empty _ i.property)
  | @insert i I hi ih =>
    obtain ⟨old, E, sub, goodE, each, pair⟩ := ih
    obtain ⟨new, nd, nf, ng⟩ := CircleTree.place (axes i) (valid i) (disks i) E
      (sub (roots i)) goodE
    let prior (j : (insert i I : Finset ι)) (hj : j.val ≠ i) : I :=
      ⟨j.val, (Finset.mem_insert.mp j.property).resolve_left hj⟩
    let trees (j : (insert i I : Finset ι)) : CircleTree (axes j) (disks j) :=
      if h : j.val = i then h.symm ▸ new else old (prior j h)
    let extended := E ∪ new.descendants
    have inE : E ⊆ extended := Finset.subset_union_left
    refine ⟨trees, extended, fun _ h => inE (sub h), ng, ?_, ?_⟩
    · rintro ⟨j, hj⟩
      by_cases h : j = i
      · subst j
        simpa only [trees, dif_pos rfl] using
          (show new.Distinct ∧ new.centers ⊆ extended ∧ Disjoint new.descendants S from
            ⟨nd, by
              intro p hp
              rw [CircleTree.centers, Finset.mem_insert] at hp
              exact hp.elim (fun he => inE (he.symm ▸ sub (roots i)))
                (Finset.mem_union_right _), Finset.disjoint_of_subset_right sub nf⟩)
      · obtain ⟨hd, hs, hf⟩ := each (prior ⟨j, hj⟩ h)
        have hs' : (old (prior ⟨j, hj⟩ h)).centers ⊆ extended := fun _ hz => inE (hs hz)
        exact by simpa only [trees, dif_neg h] using And.intro hd (And.intro hs' hf)
    · rintro ⟨j, hj⟩ ⟨k, hk⟩ hjk
      have hne : j ≠ k := fun he => hjk (Subtype.ext he)
      have fromE (m : I) : (old m).descendants ⊆ E := by
        intro z hz
        exact (each m).2.1 (Finset.mem_insert_of_mem hz)
      by_cases hji : j = i
      · subst j
        have hki : k ≠ i := hne.symm
        simpa only [trees, dif_pos rfl, dif_neg hki] using
          Finset.disjoint_of_subset_right (fromE (prior ⟨k, hk⟩ hki)) nf
      · by_cases hki : k = i
        · subst k
          simpa only [trees, dif_neg hji, dif_pos rfl] using
            (Finset.disjoint_of_subset_right (fromE (prior ⟨j, hj⟩ hji)) nf).symm
        · simpa only [trees, dif_neg hji, dif_neg hki] using
            (pair (show prior ⟨j, hj⟩ hji ≠ prior ⟨k, hk⟩ hki from
              fun h => hne (congrArg Subtype.val h)))

/-- A perfect forest whose leaves are points of the generalized configuration.
The shared signed axis list enforces equivalence of the two child contents. -/
structure PerfectGC (s : ℕ) (axes : Fin s → List ℂ) where
  atLeastTwo : 2 ≤ s
  roots : Fin s → Disk
  trees : ∀ i, CircleTree (axes i) (roots i)
  rootSeparated : Pairwise (fun i j => (roots i).Separated (roots j))
  distinctWithin : ∀ i, (trees i).Distinct
  distinctAcross : Pairwise (fun i j => Disjoint (trees i).centers (trees j).centers)
  generalPosition : ∃ S : Finset ℂ, InGeneralPosition S ∧ ∀ i, (trees i).centers ⊆ S

/-- Realize prescribed nonzero directions at every depth. The top-level
centers are fixed, and all circles have globally general-position centers. -/
theorem PerfectGC.place {s : ℕ} (hs : 2 ≤ s)
    (p : Fin s → ℂ) (hpinj : Function.Injective p)
    (hpos : ∀ i j k, i ≠ j → j ≠ k → k ≠ i →
      ¬ Collinear ℝ ({p i, p j, p k} : Set ℂ))
    (axes : Fin s → List ℂ) (valid : ∀ i v, v ∈ axes i → v ≠ 0) :
    ∃ V : PerfectGC s axes, ∀ i, (V.roots i).center = p i := by
  classical
  let S := Finset.univ.image p
  have roots (i : Fin s) : p i ∈ S := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have good : InGeneralPosition S := by
    intro a ha b hb c hc hab hbc hca
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hc
    exact fun h => hpos i j k (fun e => hab (congrArg p e)) (fun e => hbc (congrArg p e))
      (fun e => hca (congrArg p e)) ((turn_zero_iff_collinear hab).mp h)
  let pairs := (Finset.univ : Finset (Fin s × Fin s)).filter (fun q => q.1 ≠ q.2)
  have hpairs : pairs.Nonempty := by
    refine ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    intro h
    exact Nat.zero_ne_one (congrArg Fin.val h)
  let distance (q : Fin s × Fin s) : ℝ := ‖p q.2 - p q.1‖
  let minimum := pairs.inf' hpairs distance
  have hmin : 0 < minimum := by
    obtain ⟨q, hq, he⟩ := Finset.exists_mem_eq_inf' hpairs distance
    have hneq := (Finset.mem_filter.mp hq).2
    change 0 < pairs.inf' hpairs distance
    rw [he]
    exact norm_pos_iff.mpr (sub_ne_zero.mpr (hpinj.ne hneq.symm))
  let disks (i : Fin s) : Disk := ⟨p i, minimum / 3, by linarith⟩
  have separated : Pairwise (fun i j => (disks i).Separated (disks j)) := by
    intro i j hij
    have hm : minimum ≤ distance (i, j) :=
      Finset.inf'_le distance (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩)
    change minimum / 3 + minimum / 3 < distance (i, j)
    linarith
  obtain ⟨placed, extended, _, goodExtended, each, pair⟩ :=
    placeForest Finset.univ axes disks valid S roots good
  let label (i : Fin s) : (Finset.univ : Finset (Fin s)) := ⟨i, Finset.mem_univ _⟩
  refine ⟨⟨hs, disks, fun i => placed (label i), separated, fun i => (each (label i)).1,
    ?_, ⟨extended, goodExtended, fun i => (each (label i)).2.1⟩⟩, fun _ => rfl⟩
  intro i j hij
  have hd := pair (show label i ≠ label j from fun he => hij (congrArg Subtype.val he))
  apply Finset.disjoint_left.mpr
  intro z hz₁ hz₂
  simp only [CircleTree.centers, Finset.mem_insert, disks] at hz₁ hz₂
  rcases hz₁ with rfl | h₁ <;> rcases hz₂ with he | h₂
  · exact hpinj.ne hij he
  · exact Finset.disjoint_left.mp (each (label j)).2.2 h₂ (roots i)
  · exact Finset.disjoint_left.mp (each (label i)).2.2 h₁ (he.symm ▸ roots j)
  · exact Finset.disjoint_left.mp hd h₁ h₂

instance leafInhabited : (n : ℕ) → Inhabited (Leaf n)
  | 0 => ⟨PUnit.unit⟩
  | n + 1 => ⟨(false, (leafInhabited n).default)⟩

/-- The identity correspondence on the leaf words proves Definition 2.4
equivalence for any two trees using the same signed axes. -/
lemma CircleTree.equivalentDirections {axes : List ℂ} {d e : Disk}
    (L : CircleTree axes d) (R : CircleTree axes e) (p q : Leaf axes.length) :
    ∃ a : ℝ, 0 < a ∧ R.generalizedRay p q = a • L.generalizedRay p q := by
  obtain ⟨a, ha, hL⟩ := L.generalizedRay_direction p q
  obtain ⟨b, hb, hR⟩ := R.generalizedRay_direction p q
  refine ⟨b / a, div_pos hb ha, ?_⟩
  rw [hL, hR, smul_smul, div_mul_cancel₀ _ ha.ne']

abbrev PerfectGC.Point {s : ℕ} (axes : Fin s → List ℂ) := Σ i, Leaf (axes i).length

noncomputable def PerfectGC.point {s : ℕ} {axes : Fin s → List ℂ}
    (V : PerfectGC s axes) (p : PerfectGC.Point axes) : ℂ :=
  (V.trees p.1).leafPoint p.2

lemma PerfectGC.point_injective {s : ℕ} {axes : Fin s → List ℂ} (V : PerfectGC s axes) :
    Function.Injective V.point := by
  rintro ⟨i, p⟩ ⟨j, q⟩ h
  change (V.trees i).leafPoint p = (V.trees j).leafPoint q at h
  by_cases hij : i = j
  · subst j
    obtain rfl := (V.trees i).leafPoint_injective (V.distinctWithin i) h
    rfl
  · exact False.elim (Finset.disjoint_left.mp (V.distinctAcross hij)
      ((V.trees i).leafPoint_mem p) (h.symm ▸ (V.trees j).leafPoint_mem q))

lemma PerfectGC.point_card {s : ℕ} {axes : Fin s → List ℂ} (V : PerfectGC s axes) :
    (Finset.univ.image V.point).card = ∑ i, 2 ^ (axes i).length := by
  classical
  rw [Finset.card_image_of_injective _ V.point_injective, Finset.card_univ, Fintype.card_sigma]
  simp only [leaf_card]

noncomputable def PerfectGC.generalizedRay {s : ℕ} {axes : Fin s → List ℂ}
    (V : PerfectGC s axes) (p q : PerfectGC.Point axes) : ℂ :=
  if h : p.1 = q.1 then (V.trees p.1).generalizedRay p.2 (h.symm ▸ q.2)
  else (V.roots q.1).center - (V.roots p.1).center

noncomputable def PerfectGC.generalizedAngle {s : ℕ} {axes : Fin s → List ℂ}
    (V : PerfectGC s axes) (p q r : PerfectGC.Point axes) : ℝ :=
  InnerProductGeometry.angle (V.generalizedRay q p) (V.generalizedRay q r)

private noncomputable def prescribedRay {s : ℕ} {axes : Fin s → List ℂ}
    (p : Fin s → ℂ) (x y : PerfectGC.Point axes) : ℂ :=
  if h : x.1 = y.1 then wordRay (axes x.1) x.2 (h.symm ▸ y.2)
  else p y.1 - p x.1

private lemma PerfectGC.ray_direction {s : ℕ} {axes : Fin s → List ℂ}
    (V : PerfectGC s axes) (x y : PerfectGC.Point axes) :
    ∃ a : ℝ, 0 < a ∧ V.generalizedRay x y = a • prescribedRay (fun i => (V.roots i).center) x y := by
  by_cases h : x.1 = y.1
  · simpa only [PerfectGC.generalizedRay, prescribedRay, dif_pos h] using
      (V.trees x.1).generalizedRay_direction x.2 (h.symm ▸ y.2)
  · exact ⟨1, one_pos, by simp [PerfectGC.generalizedRay, prescribedRay, h]⟩

private lemma PerfectGC.generalizedAngle_eq {s : ℕ} {axes : Fin s → List ℂ}
    (V : PerfectGC s axes) (p q r : PerfectGC.Point axes) :
    V.generalizedAngle p q r =
      InnerProductGeometry.angle (prescribedRay (fun i => (V.roots i).center) q p)
        (prescribedRay (fun i => (V.roots i).center) q r) := by
  obtain ⟨a, ha, h₁⟩ := V.ray_direction q p
  obtain ⟨b, hb, h₂⟩ := V.ray_direction q r
  rw [PerfectGC.generalizedAngle, h₁, h₂,
    InnerProductGeometry.angle_smul_left_of_pos _ _ ha,
    InnerProductGeometry.angle_smul_right_of_pos _ _ hb]

/-- Projective directions are separated by `clearance` on both arcs. -/
def DirectionsSeparated (clearance : ℝ) (u v : ℂ) : Prop :=
  clearance ≤ |projectiveDir v - projectiveDir u| ∧
    |projectiveDir v - projectiveDir u| ≤ 1 - clearance

lemma DirectionsSeparated.symm {clearance : ℝ} {u v : ℂ} (h : DirectionsSeparated clearance u v) :
    DirectionsSeparated clearance v u := by simpa only [DirectionsSeparated, abs_sub_comm] using h

private lemma DirectionsSeparated.neg_left {clearance : ℝ} {u v : ℂ} (h : DirectionsSeparated clearance u v) :
    DirectionsSeparated clearance (-u) v := by
  simpa only [DirectionsSeparated, TwoHighFrame.projectiveDir_neg] using h

private lemma DirectionsSeparated.neg_right {clearance : ℝ} {u v : ℂ} (h : DirectionsSeparated clearance u v) :
    DirectionsSeparated clearance u (-v) := h.symm.neg_left.symm

private lemma angle_le_of_separated {clearance : ℝ} {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0)
    (h : DirectionsSeparated clearance u v) :
    InnerProductGeometry.angle u v ≤ (1 - clearance) * Real.pi := by
  rcases angle_eq_projective_or_supplement hu hv with e | e
  · rw [e]
    exact mul_le_mul_of_nonneg_right h.2 Real.pi_pos.le
  · rw [e]
    exact mul_le_mul_of_nonneg_right (sub_le_sub_left h.1 1) Real.pi_pos.le

private lemma wordRay_of_ne {axes : List ℂ} {p q : Leaf axes.length} (h : p ≠ q) :
    ∃ v ∈ axes, wordRay axes p q = v ∨ wordRay axes p q = -v := by
  induction axes with
  | nil => exact False.elim (h (@Subsingleton.elim PUnit _ p q))
  | cons v axes ih =>
    rcases p with ⟨a, p⟩
    rcases q with ⟨b, q⟩
    cases a <;> cases b
    · obtain ⟨w, hw, he⟩ := ih (fun e => h (congrArg (Prod.mk false) e))
      exact ⟨w, List.mem_cons_of_mem _ hw, he⟩
    · exact ⟨v, List.mem_cons_self, Or.inl rfl⟩
    · exact ⟨v, List.mem_cons_self, Or.inr rfl⟩
    · obtain ⟨w, hw, he⟩ := ih (fun e => h (congrArg (Prod.mk true) e))
      exact ⟨w, List.mem_cons_of_mem _ hw, he⟩

private lemma wordRay_ne_zero {axes : List ℂ} (valid : ∀ v ∈ axes, v ≠ 0)
    {p q : Leaf axes.length} (h : p ≠ q) : wordRay axes p q ≠ 0 := by
  obtain ⟨v, hv, he | he⟩ := wordRay_of_ne h
  · rw [he]
    exact valid v hv
  · rw [he]
    exact neg_ne_zero.mpr (valid v hv)

private lemma wordRay_reverse (axes : List ℂ) (p q : Leaf axes.length) :
    wordRay axes q p = -wordRay axes p q := by
  induction axes with
  | nil => simp [wordRay]
  | cons v axes ih =>
    rcases p with ⟨a, p⟩
    rcases q with ⟨b, q⟩
    cases a <;> cases b
    · exact ih p q
    · rfl
    · simp only [wordRay, neg_neg]
    · exact ih p q

private lemma wordRay_hits {axes : List ℂ} {v : ℂ} (h : v ∈ axes) :
    ∃ p q : Leaf axes.length, p ≠ q ∧ wordRay axes p q = v := by
  induction axes with
  | nil => simp at h
  | cons w axes ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨(false, default), (true, default), fun h' => Bool.false_ne_true (congrArg Prod.fst h'), rfl⟩
    · obtain ⟨p, q, hpq, he⟩ := ih h
      exact ⟨(false, p), (false, q), fun h' => hpq (congrArg Prod.snd h'), he⟩

private lemma axis_wordRay_separated {clearance : ℝ} {v : ℂ} {axes : List ℂ}
    (sep : ∀ w ∈ axes, DirectionsSeparated clearance v w)
    {p q : Leaf axes.length} (h : p ≠ q) :
    DirectionsSeparated clearance v (wordRay axes p q) := by
  obtain ⟨w, hw, he | he⟩ := wordRay_of_ne h
  · rw [he]
    exact sep w hw
  · rw [he]
    exact (sep w hw).neg_right

private lemma two_wordRays {clearance : ℝ} {axes : List ℂ} (hsep : axes.Pairwise (DirectionsSeparated clearance))
    {p q r : Leaf axes.length} (hpq : p ≠ q) (hpr : p ≠ r) :
    wordRay axes p q = wordRay axes p r ∨
      DirectionsSeparated clearance (wordRay axes p q) (wordRay axes p r) := by
  induction axes with
  | nil => exact Or.inl rfl
  | cons v axes ih =>
    obtain ⟨headSep, tailSep⟩ := List.pairwise_cons.mp hsep
    rcases p with ⟨a, p⟩
    rcases q with ⟨b, q⟩
    rcases r with ⟨c, r⟩
    cases a <;> cases b <;> cases c
    · exact ih tailSep (fun he => hpq (congrArg (Prod.mk false) he))
        (fun he => hpr (congrArg (Prod.mk false) he))
    · exact Or.inr (axis_wordRay_separated headSep
        (fun he => hpq (congrArg (Prod.mk false) he))).symm
    · exact Or.inr (axis_wordRay_separated headSep
        (fun he => hpr (congrArg (Prod.mk false) he)))
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inr (axis_wordRay_separated headSep
        (fun he => hpr (congrArg (Prod.mk true) he))).neg_left
    · exact Or.inr (axis_wordRay_separated headSep
        (fun he => hpq (congrArg (Prod.mk true) he))).neg_left.symm
    · exact ih tailSep (fun he => hpq (congrArg (Prod.mk true) he))
        (fun he => hpr (congrArg (Prod.mk true) he))

/-- Conditions on the prescribed directions of a perfect configuration.
The touching condition gives equality in the generalized angle cap. -/
structure AdmissibleAxes {s : ℕ} (D : CenterGapData s) (t : ℝ)
    (axes : Fin s → List ℂ) : Prop where
  nonzero : ∀ i v, v ∈ axes i → v ≠ 0
  internal : ∀ i, (axes i).Pairwise (DirectionsSeparated (1 / t))
  external : ∀ i j, j ≠ i → ∀ v ∈ axes i,
    DirectionsSeparated (1 / t) (D.center j - D.center i) v
  touches : ∃ i j, j ≠ i ∧ ∃ v ∈ axes i,
    |projectiveDir (D.center j - D.center i) - projectiveDir v| = 1 / t ∨
      |projectiveDir (D.center j - D.center i) - projectiveDir v| = 1 - 1 / t

/-- The finite maximum in Definition 2.6, given by an upper bound and
a triple that attains it. -/
def HasGeneralizedAngleMaximum {s : ℕ} {axes : Fin s → List ℂ}
    (V : PerfectGC s axes) (α : ℝ) : Prop :=
  (∀ p q r, p ≠ q → r ≠ q → V.generalizedAngle p q r ≤ α) ∧
    ∃ p q r, p ≠ q ∧ r ≠ q ∧ p ≠ r ∧ V.generalizedAngle p q r = α

private lemma cap_for_prescribedRays {s : ℕ} {D : CenterGapData s} {t : ℝ}
    {axes : Fin s → List ℂ} (ht : 2 ≤ t) (cap : CenterAngleCap D t)
    (ok : AdmissibleAxes D t axes) (p q r : PerfectGC.Point axes)
    (hp : p ≠ q) (hr : r ≠ q) :
    InnerProductGeometry.angle (prescribedRay D.center q p) (prescribedRay D.center q r) ≤
      angleAt t := by
  have hn (i : Fin s) {x y : Leaf (axes i).length} (h : x ≠ y) :=
    wordRay_ne_zero (ok.nonzero i) h
  have hv (i j : Fin s) (h : j ≠ i) : D.center j - D.center i ≠ 0 :=
    sub_ne_zero.mpr (D.injective.ne h)
  have ha : 0 ≤ angleAt t := by
    unfold angleAt
    have ht' : 0 < t := by linarith
    exact mul_nonneg (sub_nonneg.mpr ((div_le_iff₀ ht').mpr (by linarith)))
      Real.pi_pos.le
  rcases p with ⟨i, p⟩
  rcases q with ⟨j, q⟩
  rcases r with ⟨k, r⟩
  by_cases hij : j = i
  · subst i
    have hp' : q ≠ p := fun he => hp (congrArg (Sigma.mk j) he.symm)
    by_cases hjk : j = k
    · subst k
      have hr' : q ≠ r := fun he => hr (congrArg (Sigma.mk j) he.symm)
      simp [prescribedRay]
      rcases two_wordRays (ok.internal j) hp' hr' with he | sep
      · rw [he, InnerProductGeometry.angle_self (hn j hr')]
        exact ha
      · exact angle_le_of_separated (hn j hp') (hn j hr') sep
    · have hkj : k ≠ j := fun h => hjk h.symm
      simp [prescribedRay, hjk]
      exact angle_le_of_separated (hn j hp') (hv j k hkj)
        (axis_wordRay_separated (fun v hv => ok.external j k hkj v hv) hp').symm
  · by_cases hjk : j = k
    · subst k
      have hr' : q ≠ r := fun he => hr (congrArg (Sigma.mk j) he.symm)
      have hij' : i ≠ j := fun h => hij h.symm
      simp [prescribedRay, hij]
      exact angle_le_of_separated (hv j i hij') (hn j hr')
        (axis_wordRay_separated (fun v hv => ok.external j i hij' v hv) hr')
    · simp only [prescribedRay, dif_neg hij, dif_neg hjk]
      exact cap i j k (fun h => hij h.symm) (fun h => hjk h.symm)

private lemma cap_attained_for_prescribedRays {s : ℕ} {D : CenterGapData s} {t : ℝ}
    {axes : Fin s → List ℂ} (ok : AdmissibleAxes D t axes) :
    ∃ p q r : PerfectGC.Point axes, p ≠ q ∧ r ≠ q ∧ p ≠ r ∧
      InnerProductGeometry.angle (prescribedRay D.center q p) (prescribedRay D.center q r) =
        angleAt t := by
  obtain ⟨i, j, hji, v, hmem, touch⟩ := ok.touches
  obtain ⟨a, b, hab, hdir⟩ := wordRay_hits hmem
  let x : PerfectGC.Point axes := ⟨i, a⟩
  let y : PerfectGC.Point axes := ⟨i, b⟩
  let z : PerfectGC.Point axes := ⟨j, default⟩
  have hxy : x ≠ y := fun he => hab (by simpa [x, y] using he)
  have hzx : z ≠ x := fun he => hji (congrArg Sigma.fst he)
  have hzy : z ≠ y := fun he => hji (congrArg Sigma.fst he)
  let w := D.center j - D.center i
  have hw : w ≠ 0 := sub_ne_zero.mpr (D.injective.ne hji)
  have he : prescribedRay D.center x y = v := by simpa [prescribedRay, x, y] using hdir
  have he' : prescribedRay D.center y x = -v := by
    simpa [prescribedRay, x, y, hdir] using wordRay_reverse (axes i) a b
  have hxz : prescribedRay D.center x z = w := by simp [prescribedRay, x, z, hji.symm, w]
  have hyz : prescribedRay D.center y z = w := by simp [prescribedRay, y, z, hji.symm, w]
  have hvw : InnerProductGeometry.angle v w = (1 / t) * Real.pi ∨
      InnerProductGeometry.angle v w = angleAt t := by
    rcases angle_eq_projective_or_supplement (ok.nonzero i v hmem) hw with he₁ | he₂
    · rcases touch with e | e
      · exact Or.inl (he₁.trans (congrArg (· * Real.pi) e))
      · exact Or.inr (he₁.trans (congrArg (· * Real.pi) e))
    · rcases touch with e | e
      · exact Or.inr (by simpa only [angleAt, w, e] using he₂)
      · exact Or.inl (by simp only [w, e] at he₂; linarith only [he₂, show
          (1 - (1 - 1 / t)) * Real.pi = (1 / t) * Real.pi by ring])
  rcases hvw with h | h
  · refine ⟨x, y, z, hxy, hzy, hzx.symm, ?_⟩
    rw [he', hyz, InnerProductGeometry.angle_neg_left, h, angleAt]
    ring
  · exact ⟨y, x, z, hxy.symm, hzx, hzy.symm, by rw [he, hxz, h]⟩

theorem PerfectGC.angleMaximum {s : ℕ} {D : CenterGapData s} {t : ℝ}
    {axes : Fin s → List ℂ} (ht : 2 ≤ t) (cap : CenterAngleCap D t)
    (ok : AdmissibleAxes D t axes) (V : PerfectGC s axes)
    (roots : ∀ i, (V.roots i).center = D.center i) :
    HasGeneralizedAngleMaximum V (angleAt t) := by
  have he := funext roots
  constructor
  · intro p q r hp hr
    rw [V.generalizedAngle_eq, he]
    exact cap_for_prescribedRays ht cap ok p q r hp hr
  · obtain ⟨p, q, r, hp, hr, hpr, h⟩ := cap_attained_for_prescribedRays ok
    exact ⟨p, q, r, hp, hr, hpr, by rw [V.generalizedAngle_eq, he, h]⟩

private lemma fract_distance {x y : ℝ} (hx₀ : 0 ≤ x) (hx₂ : x < 2)
    (hy₀ : 0 ≤ y) (hy₂ : y < 2) (h : |y - x| ≤ 1) :
    |Int.fract y - Int.fract x| = |y - x| ∨
      |Int.fract y - Int.fract x| = 1 - |y - x| := by
  have low {u : ℝ} (h₀ : 0 ≤ u) (h₁ : u < 1) : Int.fract u = u :=
    Int.fract_eq_self.mpr ⟨h₀, h₁⟩
  have high {u : ℝ} (h₁ : 1 ≤ u) (h₂ : u < 2) : Int.fract u = u - 1 := by
    rw [← Int.fract_sub_one u]
    exact low (by linarith) (by linarith)
  by_cases hx : x < 1 <;> by_cases hy : y < 1
  · rw [low hx₀ hx, low hy₀ hy]
    exact Or.inl rfl
  · rw [low hx₀ hx, high (le_of_not_gt hy) hy₂]
    have hpos : 0 ≤ y - x := by linarith [le_of_not_gt hy]
    rw [abs_of_nonneg hpos] at h ⊢
    rw [abs_of_nonpos (show y - 1 - x ≤ 0 by linarith)]
    exact Or.inr (by ring)
  · rw [high (le_of_not_gt hx) hx₂, low hy₀ hy]
    have hneg : y - x ≤ 0 := by linarith [le_of_not_gt hx]
    rw [abs_of_nonpos hneg] at h ⊢
    rw [abs_of_nonneg (show 0 ≤ y - (x - 1) by linarith)]
    exact Or.inr (by ring)
  · rw [high (le_of_not_gt hx) hx₂, high (le_of_not_gt hy) hy₂]
    exact Or.inl (congrArg abs (by ring))

private noncomputable def axisVector (x : ℝ) : ℂ :=
  Complex.exp (((x * Real.pi : ℝ) : ℂ) * Complex.I)

private lemma axisVector_ne (x : ℝ) : axisVector x ≠ 0 := Complex.exp_ne_zero _

private lemma axisVector_dir {x : ℝ} (h₀ : 0 ≤ x) (h₂ : x < 2) :
    projectiveDir (axisVector x) = Int.fract x := by
  have low {u : ℝ} (hu₀ : 0 ≤ u) (hu : u < 1) : projectiveDir (axisVector u) = u := by
    have hθ₀ : 0 ≤ u * Real.pi := mul_nonneg hu₀ Real.pi_pos.le
    have hθ : u * Real.pi < Real.pi := by
      simpa using mul_lt_mul_of_pos_right hu Real.pi_pos
    have harg : Complex.arg (axisVector u) = u * Real.pi := by
      rw [axisVector, Complex.arg_exp_mul_I, (toIocMod_eq_self _).mpr]
      constructor <;> linarith [Real.pi_pos]
    rw [TwoHighFrame.projectiveDir_of_nonneg_arg (harg ▸ hθ₀) (harg ▸ hθ),
      harg, mul_div_cancel_right₀ _ Real.pi_ne_zero]
  by_cases hx : x < 1
  · exact (low h₀ hx).trans (Int.fract_eq_self.mpr ⟨h₀, hx⟩).symm
  · have hx₁ : 0 ≤ x - 1 := by linarith [le_of_not_gt hx]
    have hu : x - 1 < 1 := by linarith
    have he : axisVector x = -axisVector (x - 1) := by
      unfold axisVector
      rw [show (((x * Real.pi : ℝ) : ℂ) * Complex.I) =
        ((((x - 1) * Real.pi : ℝ) : ℂ) * Complex.I) + (Real.pi : ℂ) * Complex.I by
          push_cast
          ring, Complex.exp_add, Complex.exp_pi_mul_I, mul_neg_one]
    rw [he, TwoHighFrame.projectiveDir_neg, low hx₁ hu, ← Int.fract_sub_one x]
    exact (Int.fract_eq_self.mpr ⟨hx₁, hu⟩).symm

private abbrev Mark {s : ℕ} (D : CenterGapData s) (t : ℝ) (i : Fin s) :=
  Σ j : Fin (s - 1), Fin (gapCapacity (t * cyclicGap (D.dir i) j))

private noncomputable def markAngle {s : ℕ} {D : CenterGapData s} {t : ℝ} {i : Fin s}
    (m : Mark D t i) : ℝ := D.dir i m.1 + ((m.2.val : ℝ) + 1) / t

private noncomputable def rowEnd {d : ℕ} (row : Fin d → ℝ) (j : Fin d) : ℝ :=
  if hj : j.val + 1 < d then row ⟨j.val + 1, hj⟩
  else 1 + row ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt⟩

private lemma rowEnd_sub {d : ℕ} (row : Fin d → ℝ) (j : Fin d) :
    rowEnd row j - row j = cyclicGap row j := by
  by_cases h : j.val + 1 < d <;> simp [rowEnd, cyclicGap, h]

private lemma mark_in_gap {s : ℕ} {D : CenterGapData s} {t : ℝ} {i : Fin s}
    (ht : 0 < t) (m : Mark D t i) :
    D.dir i m.1 + 1 / t ≤ markAngle m ∧
      markAngle m + 1 / t ≤ rowEnd (D.dir i) m.1 := by
  have hpos : 0 < gapCapacity (t * cyclicGap (D.dir i) m.1) :=
    Nat.zero_lt_of_lt m.2.isLt
  have hcap := capacity_add_one_le hpos
  have hcount : (m.2.val : ℝ) + 2 ≤ (gapCapacity (t * cyclicGap (D.dir i) m.1) : ℝ) + 1 := by
    exact_mod_cast (show m.2.val + 2 ≤ gapCapacity (t * cyclicGap (D.dir i) m.1) + 1 by
      have h := m.2.isLt
      omega)
  have hd : ((m.2.val : ℝ) + 1) / t + 1 / t ≤ cyclicGap (D.dir i) m.1 := by
    rw [← add_div]
    apply (div_le_iff₀ ht).mpr
    rw [mul_comm (cyclicGap (D.dir i) m.1) t]
    have h := hcount.trans hcap
    linarith only [h]
  constructor
  · unfold markAngle
    have hnonneg : 0 ≤ (m.2.val : ℝ) := Nat.cast_nonneg _
    have hstep : (1 : ℝ) ≤ (m.2.val : ℝ) + 1 := by linarith
    exact add_le_add le_rfl (div_le_div_of_nonneg_right hstep ht.le)
  · unfold markAngle
    have hend := rowEnd_sub (D.dir i) m.1
    linarith only [hd, hend]

private lemma dir_range {s : ℕ} (D : CenterGapData s) (i : Fin s) (j : Fin (s - 1)) :
    0 ≤ D.dir i j ∧ D.dir i j < 1 := by
  rw [D.dir_spec]
  exact projectiveDir_mem _

private lemma end_le_later {s : ℕ} (D : CenterGapData s) (i : Fin s)
    {j k : Fin (s - 1)} (h : j < k) : rowEnd (D.dir i) j ≤ D.dir i k := by
  have h' : j.val + 1 < s - 1 := Nat.lt_of_le_of_lt (Nat.succ_le_of_lt h) k.isLt
  rw [rowEnd, dif_pos h']
  exact (D.dir_strictMono i).monotone (Nat.succ_le_of_lt h)

private lemma mark_range {s : ℕ} {D : CenterGapData s} {t : ℝ} {i : Fin s}
    (ht : 0 < t) (m : Mark D t i) :
    D.dir i ⟨0, Nat.zero_lt_of_lt m.1.isLt⟩ + 1 / t ≤ markAngle m ∧
      markAngle m + 1 / t ≤ D.dir i ⟨0, Nat.zero_lt_of_lt m.1.isLt⟩ + 1 := by
  have first_le : D.dir i ⟨0, Nat.zero_lt_of_lt m.1.isLt⟩ ≤ D.dir i m.1 :=
    (D.dir_strictMono i).monotone (Nat.zero_le _)
  obtain ⟨hl, hr⟩ := mark_in_gap ht m
  refine ⟨(add_le_add first_le le_rfl).trans hl, hr.trans ?_⟩
  unfold rowEnd
  split
  next h =>
    linarith [(dir_range D i ⟨m.1.val + 1, h⟩).2,
      (dir_range D i ⟨0, Nat.zero_lt_of_lt m.1.isLt⟩).1]
  next _ => exact (add_comm _ _).le

private lemma mark_nonneg_lt_two {s : ℕ} {D : CenterGapData s} {t : ℝ} {i : Fin s}
    (ht : 0 < t) (m : Mark D t i) :
    0 ≤ markAngle m ∧ markAngle m < 2 := by
  obtain ⟨hl, hr⟩ := mark_range ht m
  have h := dir_range D i ⟨0, Nat.zero_lt_of_lt m.1.isLt⟩
  constructor <;> linarith [one_div_pos.mpr ht]

private lemma mark_ext_distance {s : ℕ} {D : CenterGapData s} {t : ℝ} {i : Fin s}
    (ht : 0 < t) (m : Mark D t i) (j : Fin (s - 1)) :
    1 / t ≤ |D.dir i j - markAngle m| ∧ |D.dir i j - markAngle m| ≤ 1 - 1 / t := by
  obtain ⟨hl, hr⟩ := mark_in_gap ht m
  obtain ⟨hL, hR⟩ := mark_range ht m
  have hn : D.dir i ⟨0, Nat.zero_lt_of_lt m.1.isLt⟩ ≤ D.dir i j :=
    (D.dir_strictMono i).monotone (Nat.zero_le _)
  have hπ := dir_range D i ⟨0, Nat.zero_lt_of_lt m.1.isLt⟩
  have hj := dir_range D i j
  refine ⟨?_, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  rcases le_or_gt j m.1 with h | h
  · have hh := (add_le_add ((D.dir_strictMono i).monotone h) (le_refl (1 / t))).trans hl
    rw [abs_of_nonpos (by linarith [one_div_pos.mpr ht])]
    linarith
  · have hh := hr.trans (end_le_later D i h)
    rw [abs_of_nonneg (by linarith [one_div_pos.mpr ht])]
    linarith

private lemma mark_int_distance {s : ℕ} {D : CenterGapData s} {t : ℝ} {i : Fin s}
    (ht : 0 < t) {m n : Mark D t i} (hne : m ≠ n) :
    1 / t ≤ |markAngle n - markAngle m| ∧ |markAngle n - markAngle m| ≤ 1 - 1 / t := by
  have hpos := one_div_pos.mpr ht
  obtain ⟨hl, hr⟩ := mark_range ht m
  obtain ⟨hl', hr'⟩ := mark_range ht n
  have he : (⟨0, Nat.zero_lt_of_lt m.1.isLt⟩ : Fin (s - 1)) =
      ⟨0, Nat.zero_lt_of_lt n.1.isLt⟩ := rfl
  rw [he] at hl hr
  refine ⟨?_, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  rcases lt_trichotomy m.1 n.1 with h | h | h
  · have h₁ := (mark_in_gap ht m).2.trans (end_le_later D i h)
    have h₂ := (mark_in_gap ht n).1
    rw [abs_of_nonneg (by linarith)]
    linarith
  · rcases m with ⟨j, a⟩
    rcases n with ⟨k, b⟩
    change j = k at h
    subst k
    have hab : a ≠ b := fun e => hne (congrArg (Sigma.mk j) e)
    change 1 / t ≤ |(D.dir i j + ((b.val : ℝ) + 1) / t) -
      (D.dir i j + ((a.val : ℝ) + 1) / t)|
    rw [show (D.dir i j + ((b.val : ℝ) + 1) / t) -
      (D.dir i j + ((a.val : ℝ) + 1) / t) = ((b.val : ℝ) - a.val) / t by ring,
      abs_div, abs_of_pos ht, div_le_div_iff_of_pos_right ht]
    rcases lt_or_gt_of_ne hab with hab | hba
    · have hcast : (a.val : ℝ) + 1 ≤ b.val := by
        exact_mod_cast (Nat.succ_le_of_lt hab)
      rw [abs_of_nonneg (by linarith)]
      linarith
    · have hcast : (b.val : ℝ) + 1 ≤ a.val := by
        exact_mod_cast (Nat.succ_le_of_lt hba)
      rw [abs_of_nonpos (by linarith)]
      linarith
  · have h₁ := (mark_in_gap ht n).2.trans (end_le_later D i h)
    have h₂ := (mark_in_gap ht m).1
    rw [abs_of_nonpos (by linarith)]
    linarith

private lemma separated_fract_dist {x y clearance : ℝ}
    (hx : 0 ≤ x ∧ x < 2) (hy : 0 ≤ y ∧ y < 2)
    (hl : 0 ≤ clearance) (sep : clearance ≤ |y - x| ∧ |y - x| ≤ 1 - clearance) :
    clearance ≤ |Int.fract y - Int.fract x| ∧ |Int.fract y - Int.fract x| ≤ 1 - clearance := by
  rcases fract_distance hx.1 hx.2 hy.1 hy.2 (by linarith [sep.2]) with h | h
  · rwa [h]
  · rw [h]
    constructor <;> linarith [sep.1, sep.2]

private noncomputable def markEnum {s : ℕ} (D : CenterGapData s) (t : ℝ) (i : Fin s) :
    Mark D t i ≃ Fin (gapExponent D t i) :=
  Fintype.equivFinOfCardEq (by simp [gapExponent, gapCapacity])

/-- The direction at step r+1 in each gap, before reducing modulo π. -/
noncomputable def gapAxes {s : ℕ} (D : CenterGapData s) (t : ℝ) (i : Fin s) : List ℂ :=
  List.ofFn (fun p => axisVector (markAngle ((markEnum D t i).symm p)))

@[simp] lemma gapAxes_length {s : ℕ} (D : CenterGapData s) (t : ℝ) (i : Fin s) :
    (gapAxes D t i).length = gapExponent D t i := by simp [gapAxes]

private lemma mem_gapAxes {s : ℕ} {D : CenterGapData s} {t : ℝ} {i : Fin s} {v : ℂ} :
    v ∈ gapAxes D t i ↔ ∃ m : Mark D t i, axisVector (markAngle m) = v := by
  rw [gapAxes, List.mem_ofFn']
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨m, rfl⟩
    exact ⟨markEnum D t i m, by simp⟩

theorem gapAxes_admissible {s : ℕ} (D : CenterGapData s) (t : ℝ) (ht : 0 < t)
    (positive : ∃ i, 0 < gapExponent D t i) : AdmissibleAxes D t (gapAxes D t) := by
  classical
  have hl := (one_div_pos.mpr ht).le
  have markDir (i : Fin s) (m : Mark D t i) :
      projectiveDir (axisVector (markAngle m)) = Int.fract (markAngle m) := by
    exact axisVector_dir (mark_nonneg_lt_two ht m).1 (mark_nonneg_lt_two ht m).2
  constructor
  · intro i v hv
    obtain ⟨m, rfl⟩ := mem_gapAxes.mp hv
    exact axisVector_ne _
  · intro i
    rw [gapAxes, List.pairwise_ofFn]
    intro a b hab
    have hne := (markEnum D t i).symm.injective.ne hab.ne
    rw [DirectionsSeparated, markDir, markDir]
    exact separated_fract_dist (mark_nonneg_lt_two ht _) (mark_nonneg_lt_two ht _)
      hl (mark_int_distance ht hne)
  · intro i j hji v hv
    obtain ⟨m, rfl⟩ := mem_gapAxes.mp hv
    let k := (D.other i).symm ⟨j, hji⟩
    have he : projectiveDir (D.center j - D.center i) = D.dir i k := by simp [k, D.dir_spec]
    have hr := dir_range D i k
    have hs := separated_fract_dist (mark_nonneg_lt_two ht m) ⟨hr.1, by linarith [hr.2]⟩
      hl (mark_ext_distance ht m k)
    rw [Int.fract_eq_self.mpr hr] at hs
    apply DirectionsSeparated.symm
    simpa [DirectionsSeparated, markDir, he] using hs
  · obtain ⟨i, hi⟩ := positive
    have hc : 0 < Fintype.card (Mark D t i) := by
      rw [Fintype.card_congr (markEnum D t i)]
      simpa using hi
    obtain ⟨⟨j, r⟩⟩ := Fintype.card_pos_iff.mp hc
    let m : Mark D t i := ⟨j, ⟨0, Nat.zero_lt_of_lt r.isLt⟩⟩
    refine ⟨i, (D.other i j).val, (D.other i j).property,
      axisVector (markAngle m), mem_gapAxes.mpr ⟨m, rfl⟩, ?_⟩
    have he : |D.dir i j - markAngle m| = 1 / t := by
      change |D.dir i j - (D.dir i j + ((0 : ℕ) + 1 : ℝ) / t)| = 1 / t
      simp only [Nat.cast_zero, zero_add]
      rw [show D.dir i j - (D.dir i j + (1 : ℝ) / t) = -(1 / t) by ring,
        abs_neg, abs_of_pos (one_div_pos.mpr ht)]
    have hbound := (mark_ext_distance ht m j).2
    have hm := mark_nonneg_lt_two ht m
    have hj := dir_range D i j
    have hx := fract_distance hm.1 hm.2 hj.1 (by linarith [hj.2]) (by linarith)
    simpa only [he, ← D.dir_spec i j, markDir, Int.fract_eq_self.mpr hj] using hx

private lemma norm_sub_triangle (x y z : ℂ) : ‖x - z‖ ≤ ‖x - y‖ + ‖y - z‖ := by
  simpa only [dist_eq_norm] using dist_triangle x y z

lemma Disk.Inside.trans {a b c : Disk} (hab : a.Inside b) (hbc : b.Inside c) :
    a.Inside c := by
  unfold Disk.Inside at *
  linarith [norm_sub_triangle a.center b.center c.center]

lemma Disk.Separated.symm {a b : Disk} (h : a.Separated b) : b.Separated a := by
  simpa only [Disk.Separated, add_comm b.radius a.radius,
    norm_sub_rev a.center b.center] using h

lemma Disk.Separated.of_inside_left {a b x : Disk} (h : a.Separated b) (hx : x.Inside a) :
    x.Separated b := by
  unfold Disk.Separated Disk.Inside at *
  linarith [norm_sub_triangle b.center x.center a.center]

private lemma Disk.Separated.subdisks {a b x y : Disk} (h : a.Separated b)
    (hx : x = a ∨ x.Inside a) (hy : y = b ∨ y.Inside b) : x.Separated y := by
  have hx' : x.Separated b := hx.elim (fun e => e.symm ▸ h) (h.of_inside_left)
  exact hy.elim (fun e => e.symm ▸ hx') (fun hy' => (hx'.symm.of_inside_left hy').symm)

lemma Disk.closedBall_inside_openBall {child parent : Disk} (h : child.Inside parent) :
    Metric.closedBall child.center child.radius ⊆ Metric.ball parent.center parent.radius := by
  intro z hz
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  rw [Metric.mem_ball, dist_eq_norm]
  unfold Disk.Inside at h
  linarith [norm_sub_triangle z child.center parent.center]

lemma Disk.closedBalls_disjoint {a b : Disk} (h : a.Separated b) :
    Disjoint (Metric.closedBall a.center a.radius) (Metric.closedBall b.center b.radius) := by
  apply Set.disjoint_left.mpr
  intro z ha hb
  rw [Metric.mem_closedBall, dist_eq_norm] at ha hb
  have hn := norm_sub_triangle b.center z a.center
  rw [norm_sub_rev b.center z] at hn
  unfold Disk.Separated at h
  linarith

def CircleTree.disks : {axes : List ℂ} → {d : Disk} → CircleTree axes d → List Disk
  | _, _, .primitive d => [d]
  | _, d, .fork left right _ _ _ _ => d :: (left.disks ++ right.disks)

lemma CircleTree.mem_disks {axes : List ℂ} {d : Disk} (T : CircleTree axes d)
    {a : Disk} (h : a ∈ T.disks) : a = d ∨ a.Inside d := by
  induction T with
  | primitive d => exact Or.inl (by simpa [CircleTree.disks] using h)
  | fork left right il ir _ _ ihl ihr =>
    simp only [CircleTree.disks, List.mem_cons, List.mem_append] at h
    rcases h with he | hl | hr
    · exact Or.inl he
    · exact Or.inr ((ihl hl).elim (fun he => he.symm ▸ il) (fun ha => ha.trans il))
    · exact Or.inr ((ihr hr).elim (fun he => he.symm ▸ ir) (fun ha => ha.trans ir))

/-- Pre-order traversal has every later disk strictly within the earlier
disk or at a positive distance, as required by the semi-order in Se95. -/
theorem CircleTree.semiOrdered {axes : List ℂ} {d : Disk} (T : CircleTree axes d) :
    T.disks.Pairwise (fun a b => b.Inside a ∨ a.Separated b) := by
  induction T with
  | primitive d => simp [CircleTree.disks]
  | fork left right il ir sep _ ihl ihr =>
    simp only [CircleTree.disks, List.pairwise_cons, List.mem_append, List.pairwise_append]
    refine ⟨?_, ihl, ihr, ?_⟩
    · intro a h
      apply Or.inl
      rcases h with hl | hr
      · exact (left.mem_disks hl).elim (fun he => he.symm ▸ il) (fun hi => hi.trans il)
      · exact (right.mem_disks hr).elim (fun he => he.symm ▸ ir) (fun hi => hi.trans ir)
    · intro a ha b hb
      exact Or.inr (sep.subdisks (left.mem_disks ha) (right.mem_disks hb))

theorem PerfectGC.separated_across_roots {s : ℕ} {axes : Fin s → List ℂ}
    (V : PerfectGC s axes) {i j : Fin s} (h : i ≠ j) {a b : Disk}
    (ha : a ∈ (V.trees i).disks) (hb : b ∈ (V.trees j).disks) :
    a.Separated b :=
  (V.rootSeparated h).subdisks ((V.trees i).mem_disks ha) ((V.trees j).mem_disks hb)

lemma CircleTree.diskCenter_mem {axes : List ℂ} {d : Disk} (T : CircleTree axes d)
    {a : Disk} (h : a ∈ T.disks) : a.center ∈ T.centers := by
  classical
  induction T with
  | primitive d =>
    have he : a = d := by simpa [CircleTree.disks] using h
    simp [CircleTree.centers, CircleTree.descendants, he]
  | fork left right _ _ _ _ ihl ihr =>
    simp only [CircleTree.disks, List.mem_cons, List.mem_append] at h
    simp only [CircleTree.centers, CircleTree.descendants, Finset.mem_insert, Finset.mem_union]
    rcases h with he | hl | hr
    · exact Or.inl (congrArg Disk.center he)
    · have hh := ihl hl
      simp only [CircleTree.centers, Finset.mem_insert] at hh
      tauto
    · have hh := ihr hr
      simp only [CircleTree.centers, Finset.mem_insert] at hh
      tauto

theorem PerfectGC.circleCenters_not_collinear {s : ℕ} {axes : Fin s → List ℂ}
    (V : PerfectGC s axes) {i j k : Fin s} {a b c : Disk}
    (ha : a ∈ (V.trees i).disks) (hb : b ∈ (V.trees j).disks) (hc : c ∈ (V.trees k).disks)
    (hab : a.center ≠ b.center) (hbc : b.center ≠ c.center) (hca : c.center ≠ a.center) :
    ¬ Collinear ℝ ({a.center, b.center, c.center} : Set ℂ) := by
  obtain ⟨S, good, covered⟩ := V.generalPosition
  exact good.not_collinear (covered i ((V.trees i).diskCenter_mem ha))
    (covered j ((V.trees j).diskCenter_mem hb)) (covered k ((V.trees k).diskCenter_mem hc)) hab hbc hca

/-- The range-1 data are geometrically realized, all capacity slots are
occupied, and equality holds in the generalized angle cap. -/
theorem realize_gap_weight {s : ℕ} (D : CenterGapData s) (t : ℝ) (hs : 2 ≤ s) (ht : 2 ≤ t)
    (cap : Se95Correction.StrictCenterAngleCap D t)
    (positive : ∃ i, 0 < gapExponent D t i) :
    ∃ V : PerfectGC s (gapAxes D t), (∀ i, (V.roots i).center = D.center i) ∧
      HasGeneralizedAngleMaximum V (angleAt t) ∧
      Fintype.card (PerfectGC.Point (gapAxes D t)) = centerWeight D t := by
  have ht₀ : 0 < t := by linarith
  have axes := gapAxes_admissible D t ht₀ positive
  obtain ⟨V, roots⟩ := PerfectGC.place hs D.center D.injective
    (fun _ _ _ => cap.not_collinear ht₀) (gapAxes D t) axes.nonzero
  refine ⟨V, roots, V.angleMaximum ht cap.angleCap axes roots, ?_⟩
  rw [Fintype.card_sigma]
  simp only [leaf_card, gapAxes_length, centerWeight]

private theorem exact_realization {s weight : ℕ} {t : ℝ}
    (p : Fin s → ℂ) (hs : 2 ≤ s) (ht : 2 ≤ t) (hw : s < weight)
    (witness : ∃ D : CenterGapData s, D.center = p ∧ Se95Correction.StrictCenterAngleCap D t ∧
      centerWeight D t = weight) :
    ∃ (axes : Fin s → List ℂ) (V : PerfectGC s axes),
      (∀ i, (V.roots i).center = p i) ∧ HasGeneralizedAngleMaximum V (angleAt t) ∧
      Fintype.card (PerfectGC.Point axes) = weight := by
  obtain ⟨D, coords, cap, w⟩ := witness
  have positive : ∃ i, 0 < gapExponent D t i := by
    by_contra! h
    have he (i : Fin s) : gapExponent D t i = 0 := by
      have hi := h i
      omega
    have hsame : centerWeight D t = s := by simp [centerWeight, he]
    omega
  obtain ⟨V, roots, maxAngle, total⟩ := realize_gap_weight D t hs ht cap positive
  exact ⟨gapAxes D t, V, fun i => (roots i).trans (congrFun coords i), maxAngle, total.trans w⟩

/-- A perfect GC with the four counterexample centers and ten distinct leaves. -/
theorem four_perfect_counterexample :
    ∃ (axes : Fin 4 → List ℂ) (V : PerfectGC 4 axes),
      (∀ i, (V.roots i).center = Se95Correction.fourCenters i) ∧
      HasGeneralizedAngleMaximum V (angleAt (15 / 4)) ∧
      Fintype.card (PerfectGC.Point axes) = 10 ∧
      9 < Fintype.card (PerfectGC.Point axes) := by
  obtain ⟨axes, V, roots, cap, n⟩ := exact_realization Se95Correction.fourCenters
    (by decide) (by norm_num : (2 : ℝ) ≤ 15 / 4) (by decide : 4 < 10) (by
      obtain ⟨D, coords, cap, w, _⟩ := Se95Correction.four_counterexample
      exact ⟨D, coords, cap, w⟩)
  exact ⟨axes, V, roots, cap, n, by rw [n]; decide⟩

/-- The five-center perfect GC directly contradicts the fixed-s step s.2. -/
theorem five_perfect_counterexample :
    ∃ (axes : Fin 5 → List ℂ) (V : PerfectGC 5 axes),
      (∀ i, (V.roots i).center = Se95Correction.fiveCenters i) ∧
      HasGeneralizedAngleMaximum V (angleAt (19 / 4)) ∧
      Fintype.card (PerfectGC.Point axes) = 19 ∧
      17 < Fintype.card (PerfectGC.Point axes) := by
  obtain ⟨axes, V, roots, cap, n⟩ := exact_realization Se95Correction.fiveCenters
    (by decide) (by norm_num : (2 : ℝ) ≤ 19 / 4) (by decide : 5 < 19) (by
      obtain ⟨D, coords, cap, w, _⟩ := Se95Correction.five_counterexample
      exact ⟨D, coords, cap, w⟩)
  exact ⟨axes, V, roots, cap, n, by rw [n]; decide⟩

/-- The six-center perfect GC gives an independent s.2 counterexample. -/
theorem six_perfect_counterexample :
    ∃ (axes : Fin 6 → List ℂ) (V : PerfectGC 6 axes),
      (∀ i, (V.roots i).center = Se95Correction.sixCenters i) ∧
      HasGeneralizedAngleMaximum V (angleAt (23 / 4)) ∧
      Fintype.card (PerfectGC.Point axes) = 36 ∧
      33 < Fintype.card (PerfectGC.Point axes) := by
  obtain ⟨axes, V, roots, cap, n⟩ := exact_realization Se95Correction.sixCenters
    (by decide) (by norm_num : (2 : ℝ) ≤ 23 / 4) (by decide : 6 < 36) (by
      obtain ⟨D, coords, cap, w, _⟩ := Se95Correction.six_counterexample
      exact ⟨D, coords, cap, w⟩)
  exact ⟨axes, V, roots, cap, n, by rw [n]; decide⟩

/-- The fixed-s envelope of Lemma 4.1 s.2 as a claim about perfect GCs. -/
def PerfectFixedS2 : Prop :=
  ∀ (s m : ℕ) (axes : Fin s → List ℂ) (V : PerfectGC s axes) (t : ℝ),
    5 ≤ s → s ≤ m + 1 → (m : ℝ) + 1 / 2 ≤ t → t < (m : ℝ) + 1 →
    HasGeneralizedAngleMaximum V (angleAt t) →
    Fintype.card (PerfectGC.Point axes) ≤ 2 ^ m + 2 ^ (m + 1 - s)

theorem not_perfect_fixedS2 : ¬ PerfectFixedS2 := by
  intro claim
  obtain ⟨axes, V, _, cap, _, w⟩ := five_perfect_counterexample
  exact w.not_ge (claim 5 4 axes V (19 / 4) (by decide) (by decide)
    (by norm_num) (by norm_num) cap)

/-- The upper-bound derivation as described in Se95 pp. 39–42, with the
fixed-s premise now quantified over actual realized circle trees. -/
structure PublishedPerfectRoute (lemma42 lemma43 alphaIdentity theorem41Upper : Prop) : Prop where
  fixedS2 : PerfectFixedS2
  transfer : PerfectFixedS2 → lemma42
  lower : lemma43
  identity : alphaIdentity
  finish : lemma42 → lemma43 → alphaIdentity → theorem41Upper

theorem no_published_perfect_route (lemma42 lemma43 alphaIdentity theorem41Upper : Prop) :
    ¬ PublishedPerfectRoute lemma42 lemma43 alphaIdentity theorem41Upper :=
  fun route => not_perfect_fixedS2 route.fixedS2

end Erdos504.SendovStage1.Se95Bridge
