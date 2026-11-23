import Mathlib.Data.BitVec
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The truth-table simulation and the two-gate pruning argument follow L-meta-139.
namespace Path191
private abbrev T := BitVec 32
private def ins : List T := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]
private def leftOr : T := 0xaaaaaaaa ||| 0xf0f0f0f0
private def rightOr : T := 0xf0f0f0f0 ||| 0xffff0000
private def leftTerm : T := 0xcccccccc &&& leftOr
private def rightTerm : T := 0xff00ff00 &&& rightOr
private def target : T := leftTerm ||| rightTerm
private def required : List T := [leftOr, rightOr, leftTerm, rightTerm, target]

private def possible (w : List T) (z : T) : Bool :=
  z == 0 || z == (-1) || w.any (fun u => z == u || z == ~~~u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit (k : Fin 32) (z : T) := z[k.val]

private theorem read_bit (w : List T) (i : ℕ) (k : Fin 32) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

private theorem read_wire (w : List T) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

private theorem atom {ws : List T} {x : T} (hx : x = 0 ∨ x ∈ ws) :
    possible ws x ∧ possible ws (~~~x) := by
  rcases hx with rfl | hx
  · simp [possible]
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    grind

private theorem pair {ws : List T} {x y : T} (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
    possible ws (x &&& y) ∧ possible ws (x ||| y) := by
  rcases hx with rfl | hx
  · simpa [possible] using (show possible ws 0 ∧ possible ws y from ⟨by simp [possible], (atom hy).1⟩)
  rcases hy with rfl | hy
  · simpa [possible] using (show possible ws 0 ∧ possible ws x from ⟨by simp [possible], (atom (.inr hx)).1⟩)
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    constructor
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inl rfl⟩⟩
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inr rfl⟩⟩

private def step (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private theorem gate_table (w ws : List T) (hw : w ⊆ ws) (g : Gate) (hg : legal g) :
    ∃ z, possible ws z ∧ ∀ k, step (w.map (bit k)) g = (w ++ [z]).map (bit k) := by
  have mem (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ ws := (read_wire w i).imp_right (fun h => hw h)
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl | rfl
    · exact ⟨-1, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
    · exact ⟨0, by simp [possible], by simp [step, GateOp.eval, bit]⟩
    · exact ⟨-1, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl | rfl
      · exact ⟨_, (atom (mem i)).1, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, (atom (mem i)).1, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, (atom (mem i)).2, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl | rfl
        · exact ⟨_, (pair (mem i) (mem j)).1, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
        · exact ⟨_, (pair (mem i) (mem j)).2, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
        · exact ⟨_, (atom (mem i)).2, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩

private def safe : ℕ → List T → Prop
  | 0, ws => ws.contains target = false
  | n + 1, ws => ∀ z, possible ws z → safe n (z :: ws)

private def choices (ws : List T) : List T :=
  (0 :: -1 :: ws.flatMap (fun x => x :: ~~~x :: ws.flatMap (fun y => [x &&& y, x ||| y]))).eraseDups

private theorem choice_iff (ws : List T) (z : T) : z ∈ choices ws ↔ possible ws z := by
  simp [choices, possible, List.any_eq_true]
  grind

-- With two gates left, only an existing wire containing every true bit of
-- the target can serve as the other input to an AND. OR has the dual test.
private def lastTwo (ws : List T) : Bool :=
  let above := ws.filter (fun x => (x &&& target) == target)
  let below := ws.filter (fun x => (x ||| target) == target)
  (choices ws).all fun z => !(z == target || ~~~z == target ||
    above.any (fun x => (x &&& z) == target) ||
    below.any (fun x => (x ||| z) == target))

private theorem lastTwo_safe {ws : List T} (h : lastTwo ws) : safe 2 ws := by
  intro z hz v hv
  have hz' := (choice_iff ws z).2 hz
  have ht (u : T) (hu : u ∈ choices ws) := (List.all_eq_true.mp h) u hu
  have hnot (u : T) (hu : u ∈ choices ws) : u ≠ target ∧ ~~~u ≠ target ∧
      (∀ x ∈ ws, x &&& u ≠ target) ∧ (∀ x ∈ ws, x ||| u ≠ target) := by
    have H := ht u hu
    simp at H
    obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := H
    refine ⟨h1,h2,?_,?_⟩
    · intro x hx he
      apply h3 x hx _ he
      rw [← he, ← BitVec.and_assoc, BitVec.and_self]
    · intro x hx he
      apply h4 x hx _ he
      rw [← he, ← BitVec.or_assoc, BitVec.or_self]
  have H := hnot z hz'
  have base (x : T) (hx : x ∈ ws) := hnot x ((choice_iff ws x).2 (atom (.inr hx)).1)
  have unary (x : T) (hx : x ∈ z :: ws) : x ≠ target ∧ ~~~x ≠ target := by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨H.1, H.2.1⟩
    · exact ⟨(base x hx).1, (base x hx).2.1⟩
  have binary (x y : T) (hx : x ∈ z :: ws) (hy : y ∈ z :: ws) :
      x &&& y ≠ target ∧ x ||| y ≠ target := by
    rcases List.mem_cons.mp hx with hxe | hxm <;> rcases List.mem_cons.mp hy with hye | hym
    · simpa [hxe, hye] using H.1
    · simpa [hxe, BitVec.and_comm, BitVec.or_comm] using And.intro (H.2.2.1 y hym) (H.2.2.2 y hym)
    · simpa [hye] using And.intro (H.2.2.1 x hxm) (H.2.2.2 x hxm)
    · exact ⟨(base y hym).2.2.1 x hxm, (base y hym).2.2.2 x hxm⟩
  have hv' : v ≠ target := by
    simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hv
    rcases hv with ((h | h) | ⟨x, hx, ((h | h) | ⟨y, hy, h | h⟩)⟩) <;> subst v
    · decide
    · decide
    · exact (unary x hx).1
    · exact (unary x hx).2
    · exact (binary x y hx hy).1
    · exact (binary x y hx hy).2
  change (v :: z :: ws).contains target = false
  suffices target ∉ v :: z :: ws by simpa using this
  intro hm
  rcases List.mem_cons.mp hm with he | hm
  · exact hv' he.symm
  · exact (unary target hm).1 rfl

private def masked (ws : List T) (mask want : T) : Bool :=
  let xs := ws.map (fun x => x &&& mask)
  want == 0 || want == mask || xs.any fun x =>
    x == want || (~~~x &&& mask) == want ||
    ((x &&& want) == want && xs.any (fun y => (x &&& y) == want)) ||
    ((x ||| want) == want && xs.any (fun y => (x ||| y) == want))

private def fastTwo (ws : List T) : Bool :=
  !(masked ws (-1) target || masked ws (-1) (~~~target) ||
    ws.any fun x =>
      ((x &&& target) == target && masked ws x target) ||
      ((x ||| target) == target && masked ws (~~~x) (target &&& ~~~x)))

private theorem masked_of_possible {ws : List T} {u : T} (hu : possible ws u) (m : T) :
    masked ws m (u &&& m) := by
  let xs := ws.map (fun x => x &&& m)
  have mem (x : T) (hx : x ∈ ws) : x &&& m ∈ xs := List.mem_map.mpr ⟨x, hx, rfl⟩
  simp only [masked, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.any_eq_true]
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hu
  rcases hu with ((h | h) | ⟨x, hx, ((h | h) | ⟨y, hy, h | h⟩)⟩) <;> subst u
  · exact .inl (.inl (by simp))
  · exact .inl (.inr BitVec.allOnes_and)
  · exact .inr ⟨_, mem x hx, .inl (.inl (.inl rfl))⟩
  · refine .inr ⟨_, mem x hx, .inl (.inl (.inr ?_))⟩
    apply BitVec.eq_of_getElem_eq
    intro i hi
    simp
    cases x[i] <;> cases m[i] <;> rfl
  · refine .inr ⟨_, mem x hx, .inl (.inr ⟨?_, _, mem y hy, ?_⟩)⟩ <;>
      apply BitVec.eq_of_getElem_eq <;> intro i hi <;> simp only [BitVec.getElem_and] <;>
      cases x[i] <;> cases y[i] <;> cases m[i] <;> decide
  · refine .inr ⟨_, mem x hx, .inr ⟨?_, _, mem y hy, ?_⟩⟩ <;>
      apply BitVec.eq_of_getElem_eq <;> intro i hi <;> simp only [BitVec.getElem_and, BitVec.getElem_or] <;>
      cases x[i] <;> cases y[i] <;> cases m[i] <;> decide

private theorem fast_implies_last {ws : List T} (hf : fastTwo ws) : lastTwo ws := by
  simp [fastTwo] at hf
  obtain ⟨⟨hn, hc⟩, hp⟩ := hf
  apply List.all_eq_true.mpr
  intro z hz
  have hz' := (choice_iff _ _).1 hz
  simp
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro he
    have hh := masked_of_possible hz' (-1)
    rw [show z &&& (-1 : T) = z from BitVec.and_allOnes, he] at hh
    simp_all
  · intro he
    have hh := masked_of_possible hz' (-1)
    have he' : z = ~~~target := by rw [← he, BitVec.not_not]
    rw [show z &&& (-1 : T) = z from BitVec.and_allOnes, he'] at hh
    simp_all
  · intro x hx ha he
    have hh := masked_of_possible hz' x
    rw [BitVec.and_comm z x, he] at hh
    have hpair := hp x hx
    simp_all
  · intro x hx ha he
    have hh := masked_of_possible hz' (~~~x)
    have he' : z &&& ~~~x = target &&& ~~~x := by
      rw [← he]
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simp
      cases x[i] <;> cases z[i] <;> rfl
    rw [he'] at hh
    have hpair := hp x hx
    simp_all

-- The value of a wire is determined by a set of older wire values.
private def determined (S : Finset T) (z : T) : Prop :=
  ∀ i j : Fin 32, (∀ u ∈ S, bit i u = bit j u) → bit i z = bit j z

private theorem gate_sources {ws : List T} {z : T} (hz : possible ws z) :
    ∃ S : Finset T, (∀ x ∈ S, x ∈ ws) ∧ S.card ≤ 2 ∧ determined S z := by
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hz
  rcases hz with ((he | he) | ⟨x, hx, ((he | he) | ⟨y, hy, he | he⟩)⟩) <;> subst z
  · exact ⟨∅, by simp, by simp, by simp [determined, bit]⟩
  · refine ⟨∅, by simp, by simp, ?_⟩
    have hall : ∀ k : Fin 32, bit k (-1) = true := by decide
    exact fun i j _ => (hall i).trans (hall j).symm
  · exact ⟨{x}, by simpa using hx, by simp, fun i j h => h x (by simp)⟩
  · refine ⟨{x}, by simpa using hx, by simp, ?_⟩
    intro i j h
    have he := h x (by simp)
    simpa [bit] using congrArg Bool.not he
  · refine ⟨{x,y}, ?_, Finset.card_le_two, ?_⟩
    · intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl <;> assumption
    · intro i j h
      simpa [bit] using congrArg₂ Bool.and (h x (by simp)) (h y (by simp))
  · refine ⟨{x,y}, ?_, Finset.card_le_two, ?_⟩
    · intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl <;> assumption
    · intro i j h
      simpa [bit] using congrArg₂ Bool.or (h x (by simp)) (h y (by simp))

-- Trace a set of needed wires backwards. Replacing one new wire by its two inputs
-- increases the number of needed wires by at most one, including when a wire is reused.
private def blocked (n : ℕ) (ws : List T) : Prop :=
  ∀ S : Finset T, (∀ u ∈ S, u ∈ ws) → S.card ≤ n + 1 → ¬ determined S target

private theorem blocked_safe {n : ℕ} {ws : List T} (h : blocked n ws) : safe n ws := by
  induction n generalizing ws with
  | zero =>
    suffices target ∉ ws by simpa [safe] using this
    intro ht
    exact h {target} (by simpa using ht) (by simp) (fun i j he => he target (by simp))
  | succ n ih =>
    intro z hz
    apply ih
    intro S hS hcard hdet
    by_cases hin : z ∈ S
    · obtain ⟨D, hD, hDC, hDz⟩ := gate_sources hz
      let R := S.erase z ∪ D
      apply h R
      · intro x hx
        rcases Finset.mem_union.mp hx with hs | hd
        · obtain ⟨hne, hxs⟩ := Finset.mem_erase.mp hs
          exact (List.mem_cons.mp (hS x hxs)).resolve_left hne
        · exact hD x hd
      · have ha := Finset.card_union_le (S.erase z) D
        have hp : 0 < S.card := Finset.card_pos.mpr ⟨z, hin⟩
        rw [Finset.card_erase_of_mem hin] at ha
        dsimp [R]
        omega
      · intro i j he
        apply hdet i j
        intro x hx
        by_cases hxe : x = z
        · subst x
          exact hDz i j (fun y hy => he y (Finset.mem_union_right _ hy))
        · exact he x (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hxe, hx⟩))
    · apply h S _ (by omega) hdet
      intro x hx
      exact (List.mem_cons.mp (hS x hx)).resolve_left (fun he => hin (he ▸ hx))

private abbrev Probes := Fin 5 → Fin 32 × Fin 32

private def diffs (p : Probes) (u : T) : Finset (Fin 5) :=
  Finset.univ.filter (fun i => bit (p i).1 u ≠ bit (p i).2 u)

-- Four wires that each distinguish at most one of five pairs miss at least one pair.
-- Choosing pairs that all flip the target gives a lower bound of four more gates.
private theorem probe_blocks (p : Probes) (ws : List T)
    (full : ∀ i, bit (p i).1 target ≠ bit (p i).2 target)
    (light : ∀ u ∈ ws, (diffs p u).card ≤ 1) : blocked 3 ws := by
  intro S hS hcard hdet
  have hall : Finset.univ ⊆ S.biUnion (diffs p) := by
    intro i _
    by_contra hab
    apply full i (hdet _ _ ?_)
    intro u hu
    by_contra hne
    exact hab (Finset.mem_biUnion.mpr ⟨u, hu, by simpa [diffs] using hne⟩)
  have h₁ := Finset.card_le_card hall
  have h₂ := Finset.card_biUnion_le (s := S) (t := diffs p)
  have h₃ : (∑ u ∈ S, (diffs p u).card) ≤ S.card := calc
    _ ≤ ∑ _u ∈ S, 1 := Finset.sum_le_sum fun u hu => light u (hS u hu)
    _ = _ := by simp
  simp only [Finset.card_univ, Fintype.card_fin] at h₁
  omega

-- These six families cover all but six of the 1204 two-gate prefixes.
private def p0 : Probes := ![(10,11), (20,22), (9,13), (18,26), (9,25)]
private def p1 : Probes := ![(18,19), (1,3), (18,22), (5,13), (10,26)]
private def p2 : Probes := ![(18,19), (4,6), (18,22), (18,26), (9,25)]
private def p3 : Probes := ![(10,11), (9,11), (9,13), (4,12), (10,26)]
private def p4 : Probes := ![(18,19), (4,6), (18,22), (5,13), (9,25)]
private def p5 : Probes := ![(2,3), (17,19), (10,14), (18,26), (10,26)]

private def samples : List Probes := [p0, p1, p2, p3, p4, p5]

private def ready (p : Probes) (w : T) : Bool := decide ((diffs p w).card ≤ 1)

private theorem sample_facts : samples.all (fun p =>
    decide (∀ i, bit (p i).1 target ≠ bit (p i).2 target) && ins.all (ready p)) = true := by
  decide +kernel

private def cut (a b : T) : Bool :=
  samples.any (fun p => ready p a && ready p b)

private theorem cut_safe {a b : T} (hh : cut a b) : safe 3 (b :: a :: ins) := by
  obtain ⟨p, hp, ha⟩ := List.any_eq_true.mp hh
  have hf := List.all_eq_true.mp sample_facts p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hf
  simp only [Bool.and_eq_true] at ha
  apply blocked_safe (probe_blocks p _ hf.1 ?_)
  intro u hu
  rcases List.mem_cons.mp hu with rfl | hu
  · exact of_decide_eq_true ha.2
  rcases List.mem_cons.mp hu with rfl | hu
  · exact of_decide_eq_true ha.1
  · exact of_decide_eq_true (hf.2 u hu)

-- At a successful leaf, all five claimed tables must occur among the wires.
private def classifies : ℕ → List T → Prop
  | 0, ws => target ∈ ws → required ⊆ ws
  | n + 1, ws => ∀ z, possible ws z → classifies n (z :: ws)

private theorem safe_classifies {n : ℕ} {ws : List T} (h : safe n ws) : classifies n ws := by
  induction n generalizing ws with
  | zero =>
    have ha : target ∉ ws := by simpa [safe] using h
    exact fun ht => (ha ht).elim
  | succ n ih => exact fun z hz => ih (h z hz)

-- With one gate left, only an old target or the new target can trigger the conclusion.
private def finish (ws : List T) : Bool :=
  (!ws.contains target || required.all (fun u => ws.contains u)) &&
  (!possible ws target || required.all (fun u => (target :: ws).contains u))

private theorem finish_classifies {ws : List T} (h : finish ws) : classifies 1 ws := by
  simp only [finish, Bool.and_eq_true] at h
  obtain ⟨hold, hnew⟩ := h
  intro z hz ht u hu
  rcases List.mem_cons.mp ht with he | hw
  · subst z
    have hall : required.all (fun v => (target :: ws).contains v) = true := by
      simpa only [hz, Bool.not_true, Bool.false_or] using hnew
    simpa using (List.all_eq_true.mp hall) u hu
  · have ht' : ws.contains target = true := by simpa using hw
    have hall : required.all (fun v => ws.contains v) = true := by
      simpa only [ht', Bool.not_true, Bool.false_or] using hold
    exact List.mem_cons_of_mem _ (by simpa using (List.all_eq_true.mp hall) u hu)

private def search : ℕ → List T → Bool
  | 0, ws => !ws.contains target || required.all (fun u => ws.contains u)
  | n + 1, ws => if n = 0 then finish ws else
      (n == 1 && fastTwo ws) || (choices ws).all (fun z => search n (z :: ws))

private theorem search_classifies {n : ℕ} {ws : List T} (h : search n ws) : classifies n ws := by
  induction n generalizing ws with
  | zero =>
    simp [search] at h
    exact fun ht => h.resolve_left (fun hn => hn ht)
  | succ n ih =>
    by_cases he : n = 0
    · subst n
      exact finish_classifies (by exact h)
    simp only [search, he, ↓reduceIte, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
    rcases h with ⟨rfl, ht⟩ | hb
    · exact safe_classifies (lastTwo_safe (fast_implies_last ht))
    · exact fun z hz => ih (hb z ((choice_iff ws z).2 hz))


private def fromFirst (a : T) : Bool :=
  (choices (a :: ins)).all fun b => cut a b || search 3 (b :: a :: ins)

private theorem fromFirst_classifies {a : T} (h : fromFirst a) : classifies 4 (a :: ins) := by
  intro b hb
  have hh := List.all_eq_true.mp h b ((choice_iff _ _).2 hb)
  simp only [Bool.or_eq_true] at hh
  rcases hh with hcut | hsearch
  · exact safe_classifies (cut_safe hcut)
  · exact search_classifies hsearch
-- Each first gate gets its own closed check. This bounds the memory needed for reduction.
set_option maxRecDepth 10000 in
private theorem branch00 : fromFirst 0x00000000 = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem branch01 : fromFirst 0xffffffff = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem branch02 : fromFirst 0xaaaaaaaa = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem branch03 : fromFirst 0x55555555 = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem branch04 : fromFirst 0x88888888 = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem branch05 : fromFirst 0xeeeeeeee = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem branch06 : fromFirst 0xa0a0a0a0 = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem branch07 : fromFirst 0xfafafafa = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem branch08 : fromFirst 0xaa00aa00 = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem branch09 : fromFirst 0xffaaffaa = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem branch10 : fromFirst 0xaaaa0000 = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem branch11 : fromFirst 0xffffaaaa = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem branch12 : fromFirst 0xcccccccc = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem branch13 : fromFirst 0x33333333 = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem branch14 : fromFirst 0xc0c0c0c0 = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem branch15 : fromFirst 0xfcfcfcfc = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem branch16 : fromFirst 0xcc00cc00 = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem branch17 : fromFirst 0xffccffcc = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem branch18 : fromFirst 0xcccc0000 = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem branch19 : fromFirst 0xffffcccc = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem branch20 : fromFirst 0xf0f0f0f0 = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem branch21 : fromFirst 0x0f0f0f0f = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem branch22 : fromFirst 0xf000f000 = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem branch23 : fromFirst 0xfff0fff0 = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem branch24 : fromFirst 0xf0f00000 = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem branch25 : fromFirst 0xfffff0f0 = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem branch26 : fromFirst 0xff00ff00 = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem branch27 : fromFirst 0x00ff00ff = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem branch28 : fromFirst 0xff000000 = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem branch29 : fromFirst 0xffffff00 = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem branch30 : fromFirst 0xffff0000 = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem branch31 : fromFirst 0x0000ffff = true := by decide +kernel

private theorem five_classify : classifies 5 ins := by
  intro z hz
  apply fromFirst_classifies
  have starts : choices ins = [
    0x00000000, 0xffffffff, 0xaaaaaaaa, 0x55555555, 0x88888888,
    0xeeeeeeee, 0xa0a0a0a0, 0xfafafafa, 0xaa00aa00, 0xffaaffaa,
    0xaaaa0000, 0xffffaaaa, 0xcccccccc, 0x33333333, 0xc0c0c0c0,
    0xfcfcfcfc, 0xcc00cc00, 0xffccffcc, 0xcccc0000, 0xffffcccc,
    0xf0f0f0f0, 0x0f0f0f0f, 0xf000f000, 0xfff0fff0, 0xf0f00000,
    0xfffff0f0, 0xff00ff00, 0x00ff00ff, 0xff000000, 0xffffff00,
    0xffff0000, 0x0000ffff] := by decide
  have hm := (choice_iff ins z).2 hz
  rw [starts] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact branch00
  · exact branch01
  · exact branch02
  · exact branch03
  · exact branch04
  · exact branch05
  · exact branch06
  · exact branch07
  · exact branch08
  · exact branch09
  · exact branch10
  · exact branch11
  · exact branch12
  · exact branch13
  · exact branch14
  · exact branch15
  · exact branch16
  · exact branch17
  · exact branch18
  · exact branch19
  · exact branch20
  · exact branch21
  · exact branch22
  · exact branch23
  · exact branch24
  · exact branch25
  · exact branch26
  · exact branch27
  · exact branch28
  · exact branch29
  · exact branch30
  · exact branch31

private theorem classifies_now {n : ℕ} {ws : List T} (h : classifies n ws)
    (ht : target ∈ ws) : required ⊆ ws := by
  induction n generalizing ws with
  | zero => exact h ht
  | succ n ih =>
    have hh := ih (h target (atom (.inr ht)).1) (List.mem_cons_self ..)
    intro u hu
    rcases List.mem_cons.mp (hh hu) with rfl | hm
    · exact ht
    · exact hm

-- Simulate each gate on its 32 inputs simultaneously. The list w is in circuit order,
-- while ws stores the same wire values in the order used by the finite search.
private theorem simulate (gs : List Gate) (hg : ∀ g ∈ gs, legal g)
    (w ws : List T) (hm : ∀ u, u ∈ w ↔ u ∈ ws) (n : ℕ) (hlen : gs.length ≤ n)
    (hc : classifies n ws) :
    ∃ zs : List T, zs.length = gs.length ∧
      (∀ k, gs.foldl step (w.map (bit k)) = (w ++ zs).map (bit k)) ∧
      (target ∈ w ++ zs → required ⊆ w ++ zs) := by
  induction gs generalizing w ws n with
  | nil =>
    refine ⟨[], rfl, by simp, ?_⟩
    simp only [List.append_nil]
    intro ht u hu
    exact (hm u).2 (classifies_now hc ((hm _).1 ht) hu)
  | cons g gs ih =>
    cases n with
    | zero => simp at hlen
    | succ n =>
      obtain ⟨z, hz, hstep⟩ := gate_table w ws (fun {_} h => (hm _).1 h) g (hg g (by simp))
      have hm' : ∀ u, u ∈ w ++ [z] ↔ u ∈ z :: ws := by
        intro u
        simp [hm, or_comm]
      obtain ⟨zs, hl, he, hcov⟩ := ih (fun q hq => hg q (by simp [hq]))
        (w ++ [z]) (z :: ws) hm' n (by simpa using hlen) (hc z hz)
      refine ⟨z :: zs, by simp [hl], ?_, ?_⟩
      · intro k
        rw [List.foldl_cons, hstep, he]
        simp
      · simpa [List.append_assoc] using hcov

private def graph (x : Fin 5 → Bool) :=
  decide (∃ i j : Fin 5, i.val + 1 = j.val ∧ x i = true ∧ x j = true)

private def functions : List ((Fin 5 → Bool) → Bool) :=
  [fun x => x 0 || x 2, fun x => x 2 || x 4, fun x => x 1 && (x 0 || x 2),
   fun x => x 3 && (x 2 || x 4),
   fun x => (x 1 && (x 0 || x 2)) || (x 3 && (x 2 || x 4))]

private def index (x : Fin 5 → Bool) : Fin 32 :=
  Fin.ofNat 32 ((x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat +
    8 * (x 3).toNat + 16 * (x 4).toNat)

private def decode (z : T) (x : Fin 5 → Bool) : Bool := bit (index x) z
private def assignment (k : Fin 32) (i : Fin 5) : Bool := bit k (ins.getD i.val 0)

private theorem decoded : required.map decode = functions := by
  decide

private theorem input_bits : ∀ x, List.ofFn x = ins.map (bit (index x)) := by decide

private def five : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [1, 5]⟩,
    ⟨.and, [3, 6]⟩, ⟨.or, [7, 8]⟩], 9⟩

private theorem minimal_le (C : Circuit) (hmin : IsMinimalCircuit 5 C)
    (hf : circuitFun 5 C = graph) : C.gates.length ≤ 5 := by
  have hok : FanInTwo five := by
    intro g hg
    simp [five] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp
  have he : circuitFun 5 five = graph := by decide
  exact hmin.2 five hok (he.trans hf.symm)

private theorem wires_keep (gs : List Gate) (w : List Bool) : w ⊆ gs.foldl step w := by
  induction gs generalizing w with
  | nil => exact fun {_} h => h
  | cons g gs ih =>
    intro b hb
    exact ih (step w g) (List.mem_append_left _ hb)

-- A NOT gate would output true on the all-false assignment as soon as all earlier wires are false.
private theorem no_not (gs : List Gate) (w : List Bool) (hw : ∀ b ∈ gs.foldl step w, b = false) :
    ∀ g ∈ gs, g.op ≠ GateOp.not := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    have hi : ∀ b ∈ step w g, b = false := fun b hb => hw b ((wires_keep gs _) hb)
    have hr (i : ℕ) : w.getD i false = false := by
      by_cases h : i < w.length
      · have hh := hi w[i] (List.mem_append_left _ (List.getElem_mem h))
        simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h] using hh
      · exact List.getD_eq_default _ _ (by omega)
    have ho := hi (g.op.eval (g.inputs.map fun i => w.getD i false)) (by simp [step])
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · intro hn
      cases ha : q.inputs with
      | nil => simp [hn, ha, GateOp.eval] at ho
      | cons i rest =>
        have hread : w[i]?.getD false = false := by
          simpa only [List.getD_eq_getElem?_getD] using hr i
        simp [hn, ha, GateOp.eval, hread] at ho
    · exact ih (step w g) hw q hq

private theorem solve (hc : classifies 5 ins) (C : Circuit) (hmin : IsMinimalCircuit 5 C)
    (hf : circuitFun 5 C = graph) :
    (∀ g ∈ C.gates, g.op ≠ GateOp.not) ∧
    (∀ j : ℕ, j < 5 → ∃ f ∈ functions, ∀ x,
      (C.wires (List.ofFn x)).getD (5+j) false = f x) ∧
    (∀ f ∈ functions, ∃ j : ℕ, j < 5 ∧ ∀ x,
      (C.wires (List.ofFn x)).getD (5+j) false = f x) := by
  have hle := minimal_le C hmin hf
  obtain ⟨zs, hlen, he, hcov⟩ := simulate C.gates hmin.1 ins ins (fun _ => Iff.rfl) 5 hle hc
  have out : (ins ++ zs).getD C.output 0 = target := by
    apply BitVec.eq_of_getElem_eq
    intro i hi
    let k : Fin 32 := ⟨i, hi⟩
    have hv := congrFun hf (assignment k)
    change (C.gates.foldl step (List.ofFn (assignment k))).getD C.output false = _ at hv
    have hi' : ∀ t, List.ofFn (assignment t) = ins.map (bit t) := by decide
    have ht' : ∀ t, graph (assignment t) = bit t target := by decide
    rw [hi', he, read_bit, ht'] at hv
    exact hv
  have htarget : target ∈ ins ++ zs := by
    have h := read_wire (ins ++ zs) C.output
    rw [out] at h
    exact h.resolve_left (by decide)
  have hcovers : required ⊆ zs := by
    intro u hu
    have hd (a : T) (ha : a ∈ required) : a ∉ ins := by
      have test : required.all (fun v => !ins.contains v) = true := by decide
      simpa using (List.all_eq_true.mp test) a ha
    exact (List.mem_append.mp (hcov htarget hu)).resolve_left (hd u hu)
  have perm : required.Perm zs := (List.subperm_of_subset (by decide) hcovers).perm_of_length_le
    (by change zs.length ≤ 5; omega)
  have hsize : zs.length = 5 := perm.length_eq.symm
  have wire (j : ℕ) (hj : j < zs.length) (x : Fin 5 → Bool) :
      (C.wires (List.ofFn x)).getD (5+j) false = decode zs[j] x := by
    change (C.gates.foldl step (List.ofFn x)).getD (5+j) false = _
    rw [input_bits, he, read_bit, List.getD_append_right _ _ _ _ (by change 5 ≤ 5+j; omega)]
    simp [decode, show ins.length = 5 from rfl, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hj]
  refine ⟨?_, ?_, ?_⟩
  · apply no_not C.gates (ins.map (bit 0))
    rw [he]
    intro b hb
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hb
    have hz (a : T) (ha : a ∈ ins ++ required) : bit 0 a = false := by
      have test : (ins ++ required).all (fun v => !(bit 0 v)) = true := by decide
      simpa using (List.all_eq_true.mp test) a ha
    rcases List.mem_append.mp hu with hu | hu
    · exact hz u (List.mem_append_left _ hu)
    · exact hz u (List.mem_append_right _ (perm.mem_iff.mpr hu))
  · intro j hj
    have hj' : j < zs.length := by omega
    refine ⟨decode zs[j], ?_, wire j hj'⟩
    rw [← decoded]
    exact List.mem_map.mpr ⟨_, perm.mem_iff.mpr (List.getElem_mem hj'), rfl⟩
  · intro f hf'
    rw [← decoded] at hf'
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hf'
    obtain ⟨j, hj, heq⟩ := List.getElem_of_mem (hcovers hz)
    refine ⟨j, by omega, ?_⟩
    intro x
    simpa only [heq] using wire j hj x

end Path191

theorem PEqualNP.Outside.L_meta_191 :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.IsMinimalCircuit 5 C → PEqualNP.MetaComplexity.circuitFun 5 C = (fun x : Fin 5 → Bool => decide (∃ i j : Fin 5, i.val + 1 = j.val ∧ x i = true ∧ x j = true)) → (∀ g ∈ C.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) ∧ (∀ j : ℕ, j < 5 → ∃ f ∈ ([fun x => x 0 || x 2, fun x => x 2 || x 4, fun x => x 1 && (x 0 || x 2), fun x => x 3 && (x 2 || x 4), fun x => (x 1 && (x 0 || x 2)) || (x 3 && (x 2 || x 4))] : List ((Fin 5 → Bool) → Bool)), ∀ x : Fin 5 → Bool, (C.wires (List.ofFn x)).getD (5 + j) false = f x) ∧ (∀ f ∈ ([fun x => x 0 || x 2, fun x => x 2 || x 4, fun x => x 1 && (x 0 || x 2), fun x => x 3 && (x 2 || x 4), fun x => (x 1 && (x 0 || x 2)) || (x 3 && (x 2 || x 4))] : List ((Fin 5 → Bool) → Bool)), ∃ j : ℕ, j < 5 ∧ ∀ x : Fin 5 → Bool, (C.wires (List.ofFn x)).getD (5 + j) false = f x) :=
  Path191.solve Path191.five_classify
