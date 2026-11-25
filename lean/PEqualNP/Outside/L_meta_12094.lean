import PEqualNP.Defs

-- The live-wire certificate derives from L_meta_11413. The restriction proof
-- derives from L_meta_10165. Both are reused under Apache 2.0.

/- The circuit normalization and parity arguments come from the project's
Shannon, Support, Elim, Parity, Parity3, and Parity4 helpers. The first-gate
analysis below needs global sensitivity only for the operands it uses.
The final applications establish the bounds for majority with zero, one,
and two independent parity inputs, then restrict the low bit of one addend. -/

/-!
# Shannon expansion as a straight-line program

Helper for `L-meta-001`. The construction is made at an arbitrary wire offset: the function
reads the first `k` wires of a wire list of length `m`, and the new gates are appended after
wire `m - 1`. So two subcircuits are put one after the other without renumbering any gate.
-/

namespace PEqualNP.Outside.L_meta_12094.FirstGate
open PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds

/-- Run gates on a wire list: the fold inside `Circuit.wires`. -/
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

/-- The four gates that close one Shannon expansion step, appended to the wires `v`: with
`a = v[k]`, `p = v[o0]`, `q = v[o1]` they produce `(¬a ∧ p) ∨ (a ∧ q)` on the last wire. -/
theorem final_gates (v : List Bool) (k o0 o1 : ℕ) (hk : k < v.length) (h0 : o0 < v.length)
    (h1 : o1 < v.length) :
    (wiresFrom [⟨GateOp.not, [k]⟩, ⟨GateOp.and, [v.length, o0]⟩, ⟨GateOp.and, [k, o1]⟩,
      ⟨GateOp.or, [v.length + 1, v.length + 2]⟩] v).getD (v.length + 3) false
      = ((!(v.getD k false) && v.getD o0 false) || (v.getD k false && v.getD o1 false)) := by
  have A : ∀ (t : List Bool) (i : ℕ), i < v.length → (v ++ t)[i]?.getD false = v[i]?.getD false := by
    intro t i h; rw [List.getElem?_append_left h]
  simp [wiresFrom, GateOp.eval, A _ _ hk, A _ _ h0, A _ _ h1]

/-- The allowed gates: AND, OR, NOT reading at most two wires. -/
def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem shannon (k : ℕ) : ∀ (f : (Fin k → Bool) → Bool) (m : ℕ), k ≤ m →
    ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length + 4 ≤ 5 * 2 ^ k ∧
      out < m + gs.length ∧
      ∀ w : List Bool, w.length = m →
        (wiresFrom gs w).getD out false = f (fun i : Fin k => w.getD i false) := by
  induction k with
  | zero =>
    intro f m _
    refine ⟨[⟨if f (fun i => i.elim0) = true then GateOp.and else GateOp.or, []⟩], m, ?_, by simp,
      by simp, ?_⟩
    · intro g hg
      simp only [List.mem_singleton] at hg
      subst hg
      refine ⟨?_, by simp⟩
      by_cases h : f (fun i => i.elim0) = true <;> simp [h]
    · intro w hw
      have hf : (fun i : Fin 0 => w.getD i false) = (fun i => i.elim0) := Subsingleton.elim _ _
      rw [hf]
      by_cases h : f (fun i => i.elim0) = true <;>
        simp [wiresFrom, h, ← hw, GateOp.eval]
  | succ k ih =>
    intro f m hm
    obtain ⟨gs0, o0, ok0, len0, ho0, ev0⟩ :=
      ih (fun y => f (Fin.snoc y false)) m (by omega)
    obtain ⟨gs1, o1, ok1, len1, ho1, ev1⟩ :=
      ih (fun y => f (Fin.snoc y true)) (m + gs0.length) (by omega)
    let M := m + gs0.length + gs1.length
    refine ⟨gs0 ++ gs1 ++ [⟨GateOp.not, [k]⟩, ⟨GateOp.and, [M, o0]⟩, ⟨GateOp.and, [k, o1]⟩,
      ⟨GateOp.or, [M + 1, M + 2]⟩], M + 3, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with (hg | hg) | hg | hg | hg | hg
      · exact ok0 g hg
      · exact ok1 g hg
      all_goals (subst hg; simp [Ok])
    · simp only [List.length_append, List.length_cons, List.length_nil]
      rw [pow_succ]; omega
    · simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · intro w hw
      rw [wiresFrom_append, wiresFrom_append]
      set w1 := wiresFrom gs0 w with hw1
      set w2 := wiresFrom gs1 w1 with hw2
      have l1 : w1.length = m + gs0.length := by rw [hw1, length_wiresFrom, hw]
      have l2 : w2.length = M := by rw [hw2, length_wiresFrom, l1]
      have e0 : w2.getD o0 false = f (Fin.snoc (fun i : Fin k => w.getD i false) false) := by
        rw [hw2, getD_wiresFrom _ _ _ (by omega)]; exact ev0 w hw
      have e1 : w2.getD o1 false = f (Fin.snoc (fun i : Fin k => w.getD i false) true) := by
        rw [ev1 w1 l1]
        congr 2; funext i
        exact getD_wiresFrom _ _ _ (by have := i.isLt; omega)
      have ek : w2.getD k false = w.getD k false := by
        rw [hw2, getD_wiresFrom _ _ _ (by omega), hw1, getD_wiresFrom _ _ _ (by omega)]
      have hx : (fun i : Fin (k + 1) => w.getD i false)
          = Fin.snoc (fun i : Fin k => w.getD i false) (w.getD k false) := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
      rw [hx]
      have hk2 : k < w2.length := by omega
      have h02 : o0 < w2.length := by omega
      have h12 : o1 < w2.length := by omega
      rw [show M = w2.length from l2.symm, final_gates w2 k o0 o1 hk2 h02 h12, ek, e0, e1]
      cases w.getD k false <;> simp

end PEqualNP.Outside.L_meta_12094.FirstGate


/-!
# Supports of wires

Helper for `L-meta-011`. Every wire gets a support: the set of inputs it can depend on, read
off the gates. Two facts: the value of a wire depends only on the inputs in its support, and
any set `W` of wires has a joint support of size at most (number of gates) + `|W|`, because a
gate of fan-in two replaces itself by at most two earlier wires.
-/

namespace PEqualNP.Outside.L_meta_12094.FirstGate
open PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

/-- The support of a gate: the union of the supports of the wires it reads. -/
def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

/-- The supports of all wires, starting from the supports `L` of the wires present. -/
def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

/-- The supports of the input wires: input `i` has support `{i}`. -/
def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

/-- Wire lists `w`, `w'` (for the inputs `x`, `y`) agree on every wire whose support `x` and
`y` agree on. -/
def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

/-- Any set `W` of wires has a joint support of size at most `t + |W|`. -/
def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

/-- A function that depends on each of its `n` inputs has no circuit with fewer than `n - 1`
gates. -/
theorem dep_lower (n : ℕ) (f : (Fin n → Bool) → Bool)
    (hdep : ∀ i : Fin n, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : n ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : ∀ i : Fin n, i ∈ S := by
    intro i
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hcard : S.card = n := by
    rw [Finset.eq_univ_of_forall hall]; simp
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS, hcard] at hc
  omega

end PEqualNP.Outside.L_meta_12094.FirstGate


/-!
# Gate elimination

Helper for `L-meta-014`. The last input of a circuit on `n + 1` inputs is fixed to `b`. One
pass over the gates gives every old wire a status: a constant, or an alias of a wire of the
new circuit on `n` inputs. A gate that reads a constant becomes a constant or an alias and is
not emitted, so if some gate reads the fixed input the new circuit is smaller. If no gate
reads it, the supports of `Support.lean` show the function does not depend on it.
-/

namespace PEqualNP.Outside.L_meta_12094.FirstGate
open PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds

/-- A NOT gate reads only its first wire: drop the others. -/
def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

/-- An allowed gate whose NOT gates read at most one wire. -/
def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

/-- The status of an old wire: a constant, or the wire `j` of the new circuit. -/
inductive Stat : Type
  | const (c : Bool)
  | wire (j : ℕ)

def Stat.val (w : List Bool) : Stat → Bool
  | Stat.const c => c
  | Stat.wire j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Stat.const _ => True
  | Stat.wire j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | Stat.const c :: _ => (none, Stat.const (!c))
  | Stat.wire j :: _ => (some ⟨GateOp.not, [j]⟩, Stat.wire m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c && d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.and, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const false)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c || d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.or, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

/-- What a gate becomes, given the statuses of the wires it reads; `m` is the number of the
next new wire. The result is the gate to emit, if any, and the status of the gate's wire. -/
def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Stat.const false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Stat.const c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

/-- One step of the pass: `acc.1` holds the statuses of the old wires, `acc.2` the new gates. -/
def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

/-- If the status of old wire `k` is a constant and some gate reads wire `k`, one gate is
saved. -/
theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Stat.const false) = Stat.const c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
        omega
      omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Stat.const _, _ => trivial
  | Stat.wire _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Stat.const _, _ => rfl
  | Stat.wire _, hj => List.getD_append _ _ _ _ hj

/-- The invariant of the pass, for one input `y` of the new circuit: `w` are the old wires,
and every old wire has a valid status whose value on the new wires is the old value. -/
def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Stat.const false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Stat.const false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Stat.const false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Stat.const false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Stat.const false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

/-- The statuses at the start: the first `n` old wires are the new input wires, and the last
input is the constant `b`. -/
def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Stat.wire i) ++ [Stat.const b]

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => Stat.wire i)).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, Stat.Valid, Stat.val, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

/-- If no gate reads wire `n`, no other wire has the last input in its support. -/
theorem supp_noread (n : ℕ) (gs : List Gate) : ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, n ∉ g.inputs) → (∀ j : ℕ, j ≠ n → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, j ≠ n → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (fun e => hno g List.mem_cons_self (e ▸ ha)) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem inputSupps_getD (m j : ℕ) (h : j < m) :
    (inputSupps m).getD j ∅ = {⟨j, h⟩} := by
  simp [inputSupps, h]

theorem inputSupps_noread (n : ℕ) : ∀ j : ℕ, j ≠ n →
    Fin.last n ∉ (inputSupps (n + 1)).getD j ∅ := by
  intro j hj
  by_cases hlt : j < n + 1
  · have e : (inputSupps (n + 1)).getD j ∅ = {⟨j, hlt⟩} := inputSupps_getD (n + 1) j hlt
    rw [e, Finset.mem_singleton]
    intro e'
    exact hj (by have := congrArg Fin.val e'; simpa using this.symm)
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

/-- Gate elimination: fix the last input of `f` to `b`. If `f` depends on that input and the
restriction is not constant, a circuit of size `s + 1` for `f` gives one of size `s` for the
restriction. -/
theorem gate_elim (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f (s + 1)) :
    HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s + 1 := hsz
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  have hvalid : (acc.1.getD C.output (Stat.const false)).Valid (n + acc.2.length) := by
    obtain ⟨y, _, _⟩ := hnc
    exact ((hinv y).2 C.output).1
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    have hlen : acc.2.length ≤ s := by
      by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
      · have := elim_len_lt n n gs (initStats n b, []) hnok (by simp [initStats])
          ⟨b, getD_snoc_len _ _ _ _ (by simp)⟩ hread
        rw [← hacc] at this
        have hl : gs.length = C.gates.length := by simp [hgs]
        simp only [List.length_nil, zero_add] at this
        omega
      · exfalso
        push Not at hread
        have hout : C.output ≠ n := by
          intro e
          rw [e, hacc, elim_getD n n _ gs _ (by simp [initStats])] at hst
          have hb : (initStats n b).getD n (Stat.const false) = Stat.const b :=
            getD_snoc_len _ _ _ _ (by simp)
          rw [show ((initStats n b, ([] : List Gate))).1 = initStats n b from rfl, hb] at hst
          cases hst
        obtain ⟨x, hx⟩ := hdep
        apply hx
        have hns := supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) C.output hout
        have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
          (agree_inputs _ _)).2.2 C.output (by
            intro k hk
            have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
            simp [Function.update_of_ne this])
        rw [← hevg, ← hevg]
        exact hag
    refine ⟨⟨acc.2, j⟩, elim_ok n gs _ (by simp), hlen, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

end PEqualNP.Outside.L_meta_12094.FirstGate


/-!
# Parity needs `2 (n - 1)` gates

Helper for `L-meta-020`. The pass of `Elim.lean` fixes the last input of a circuit to a
constant `b`. Here it is shown to save two gates for a suitable `b`, when the function depends
on the last input and both restrictions are non-constant. Either two gates read the fixed
input, or the only gate reading it becomes a constant for a suitable `b` and a later gate
reads that constant, or the output does not depend on the last input. Parity and its
complement satisfy the hypotheses, and their restrictions are again parity or its complement.
-/

namespace PEqualNP.Outside.L_meta_12094.FirstGate
open PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds

/-! ## The pass, cut at one gate -/

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Stat.const false) = Stat.const b :=
  getD_snoc_len _ _ _ _ (by simp)

/-- A normalized allowed gate that reads a constant `b`, where `b` is `false` for an AND gate
and `true` for an OR gate, becomes a constant. -/
theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Stat.const b ∈ ins) : ∃ c, (simplify op m ins).2 = Stat.const c := by
  rcases hop with rfl | rfl | rfl
  · have := hand rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpAnd]
  · have := hor rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

/-- A normalized allowed gate that reads a wire of constant status emits no gate. -/
theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Stat.const false) = Stat.const c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
  rw [hnone]; simp

/-- The value to give the fixed input so that a gate reading it becomes a constant. -/
def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Stat.const false) = Stat.const (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Stat.const false) = Stat.const c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Stat.const false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩

/-! ## Supports -/

theorem suppsFrom_append {n : ℕ} (pre post : List Gate) (L : List (Finset (Fin n))) :
    suppsFrom (pre ++ post) L = suppsFrom post (suppsFrom pre L) := by
  simp [suppsFrom, List.foldl_append]

theorem length_suppsFrom {n : ℕ} (gs : List Gate) : ∀ L : List (Finset (Fin n)),
    (suppsFrom gs L).length = L.length + gs.length := by
  induction gs with
  | nil => intro L; rfl
  | cons g gs ih =>
    intro L
    have h : suppsFrom (g :: gs) L = suppsFrom gs (L ++ [gateSupp L g]) := rfl
    rw [h, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

/-- If no gate reads a wire of the set `D`, no wire outside `D` gets the last input in its
support. -/
theorem supp_noreadD (n : ℕ) (D : ℕ → Prop) (gs : List Gate) :
    ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, ∀ a ∈ g.inputs, ¬ D a) → (∀ j : ℕ, ¬ D j → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, ¬ D j → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (hno g List.mem_cons_self a ha) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

/-! ## Two gates saved -/

/-- If the output wire has the last input in its support and its status is never a constant,
then for some value of the last input the pass emits two gates fewer than it reads. -/
theorem two_saved (n : ℕ) (gs : List Gate) (hnok : ∀ g ∈ gs, NOk g) (o : ℕ)
    (hdep : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅)
    (hout : ∀ b c, (elim n gs (initStats n b, [])).1.getD o (Stat.const false) ≠ Stat.const c) :
    ∃ b, (elim n gs (initStats n b, [])).2.length + 2 ≤ gs.length := by
  have hon : o ≠ n := by
    intro e
    apply hout false false
    rw [e, elim_getD n n _ gs _ (by simp [initStats])]
    exact initStats_last n false
  by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
  swap
  · exfalso
    push Not at hread
    exact supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) o hon hdep
  obtain ⟨g, hg, hng⟩ := hread
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hg
  have hgn : NOk g := hnok g hg
  have hpren : ∀ g' ∈ pre, NOk g' := fun g' h => hnok g' (List.mem_append_left _ h)
  have hpostn : ∀ g' ∈ post, NOk g' :=
    fun g' h => hnok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have hsplit : ∀ b, elim n (pre ++ g :: post) (initStats n b, [])
      = elim n post (elimStep n (elim n pre (initStats n b, [])) g) :=
    fun b => by rw [elim_append, elim_cons]
  have hAn : ∀ b, (elim n pre (initStats n b, [])).1.getD n (Stat.const false) = Stat.const b := by
    intro b
    rw [elim_getD n n _ pre _ (by simp [initStats])]
    exact initStats_last n b
  have hAl : ∀ b, (elim n pre (initStats n b, [])).1.length = n + 1 + pre.length := by
    intro b
    rw [elim_fst_len]
    simp [initStats]
  have hA2 : ∀ b, (elim n pre (initStats n b, [])).2.length ≤ 0 + pre.length :=
    fun b => elim_len n pre (initStats n b, [])
  have hB2 := fun b => elimStep_none n (elim n pre (initStats n b, [])) g hgn n hng b (hAn b)
  have hBl : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.length
      = n + 1 + pre.length + 1 := by
    intro b
    simp [elimStep, hAl b]
  have hBn : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.getD n (Stat.const false)
      = Stat.const b := by
    intro b
    show ((elim n pre (initStats n b, [])).1 ++ [_]).getD n _ = _
    rw [getD_snoc_ne _ _ _ _ (by rw [hAl b]; omega)]
    exact hAn b
  have hF := fun b => elim_len n post (elimStep n (elim n pre (initStats n b, [])) g)
  have hlen : (pre ++ g :: post).length = pre.length + post.length + 1 := by
    simp only [List.length_append, List.length_cons]; omega
  by_cases h1 : ∃ g' ∈ pre, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 : (elim n pre (initStats n false, [])).2.length + 1 ≤ 0 + pre.length :=
      elim_len_lt n n pre (initStats n false, []) hpren (by simp [initStats])
        ⟨false, initStats_last n false⟩ h1
    have := hF false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  by_cases h2 : ∃ g' ∈ post, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 := elim_len_lt n n post (elimStep n (elim n pre (initStats n false, [])) g) hpostn
      (by rw [hBl]; omega) ⟨false, hBn false⟩ h2
    have := hA2 false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  obtain ⟨c, hc⟩ := elimStep_const n (elim n pre (initStats n (fixBit g), [])) g hgn n hng
    (hAn (fixBit g))
  rw [hAl (fixBit g)] at hc
  refine ⟨fixBit g, ?_⟩
  by_cases h3 : ∃ g' ∈ post, (n + 1 + pre.length) ∈ g'.inputs
  · have a1 := elim_len_lt n (n + 1 + pre.length) post
      (elimStep n (elim n pre (initStats n (fixBit g), [])) g) hpostn
      (by rw [hBl]; omega) ⟨c, hc⟩ h3
    have := hA2 (fixBit g)
    have := hB2 (fixBit g)
    rw [hsplit, hlen]
    omega
  · exfalso
    have hom : o ≠ n + 1 + pre.length := by
      intro e
      apply hout (fixBit g) c
      rw [hsplit, e, elim_getD n _ _ post _ (by rw [hBl]; omega)]
      exact hc
    push Not at h1 h2 h3
    have hs : suppsFrom (pre ++ g :: post) (inputSupps (n + 1))
        = suppsFrom post (suppsFrom pre (inputSupps (n + 1))
          ++ [gateSupp (suppsFrom pre (inputSupps (n + 1))) g]) := by
      rw [suppsFrom_append]; rfl
    rw [hs] at hdep
    have hL := supp_noread n pre (inputSupps (n + 1)) h1 (inputSupps_noread n)
    have hLl : (suppsFrom pre (inputSupps (n + 1))).length = n + 1 + pre.length := by
      rw [length_suppsFrom]
      simp [inputSupps]
    refine supp_noreadD n (fun j => j = n ∨ j = n + 1 + pre.length) post _ ?_ ?_ o
      (by simp [hon, hom]) hdep
    · intro g' hg' a ha hD
      rcases hD with rfl | rfl
      · exact h2 g' hg' ha
      · exact h3 g' hg' ha
    · intro j hj
      have hj' : j ≠ n ∧ j ≠ n + 1 + pre.length := by
        constructor
        · exact fun e => hj (Or.inl e)
        · exact fun e => hj (Or.inr e)
      rw [getD_snoc_ne _ _ _ _ (by rw [hLl]; exact hj'.2)]
      exact hL j hj'.1

/-- Gate elimination saving two gates: if `f` depends on its last input and stays non-constant
whichever value that input is fixed to, then for some value `b` the restriction has a circuit
with two gates fewer. -/
theorem gate_elim_two (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∀ b : Bool, ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hl : gs.length = C.gates.length := by simp [hgs]
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  have hinv : ∀ (b : Bool) (y : Fin n → Bool),
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool)))
        (elim n gs (initStats n b, [])) := by
    intro b y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ (b : Bool) (y : Fin n → Bool),
      ((elim n gs (initStats n b, [])).1.getD C.output (Stat.const false)).val
        (wiresFrom (elim n gs (initStats n b, [])).2 (List.ofFn y)) = f (Fin.snoc y b) := by
    intro b y
    rw [((hinv b y).2 C.output).2, hevg]
  have hout : ∀ b c,
      (elim n gs (initStats n b, [])).1.getD C.output (Stat.const false) ≠ Stat.const c := by
    intro b c hst
    obtain ⟨y, y', hne⟩ := hnc b
    apply hne
    rw [← hval b y, ← hval b y', hst]; rfl
  have hsupp : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD C.output ∅ := by
    by_contra hns
    obtain ⟨x, hx⟩ := hdep
    apply hx
    have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hevg, ← hevg]
    exact hag
  obtain ⟨b, hb⟩ := two_saved n gs hnok C.output hsupp hout
  cases hst : (elim n gs (initStats n b, [])).1.getD C.output (Stat.const false) with
  | const c => exact absurd hst (hout b c)
  | wire j =>
    refine ⟨b, (elim n gs (initStats n b, [])).2.length, by omega,
      ⟨(elim n gs (initStats n b, [])).2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval b y
    rw [hst] at this
    exact this

end PEqualNP.Outside.L_meta_12094.FirstGate

namespace PEqualNP.Outside.L_meta_12094

abbrev B := BitVec 31
abbrev Sig := B × B
def top : B := BitVec.allOnes 31
def zero : Sig := (0,0)
def one : Sig := (top,top)
def target : Sig := (top,0)
def neg (a : Sig) : Sig := (~~~a.1,~~~a.2)
def bin (isOr : Bool) (a b : Sig) : Sig :=
  if isOr then (a.1 ||| b.1,a.2 ||| b.2) else (a.1 &&& b.1,a.2 &&& b.2)
def sep (d : Bool) (a : Sig) : B :=
  if d then a.1 ^^^ a.2 else a.1 &&& ~~~a.2
def unionSep (d : Bool) : List Sig → B
  | [] => 0
  | a::l => sep d a ||| unionSep d l

def dropped (del v : List Sig) : List Sig := v.filter (fun x => !(del.contains x))

abbrev Cov := B × B × B

def addCov (z : B) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Sig) : Cov :=
  v.foldr (fun a c => addCov (sep d a) c) (0,0,0)

def takeOne (c : Cov) (a : B) : B := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : B) : B :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private theorem cov_one (c : Cov) (a : B) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private theorem cov_two (c : Cov) (a b : B) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem add_swap (c : Cov) (a b : B) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem cov_perm (d : Bool) {l r : List Sig} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (sep d a)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2

private theorem cov_union (d : Bool) (v : List Sig) : (coverage d v).1=unionSep d v := by
  induction v with
  | nil => rfl
  | cons a v ih => change sep d a ||| (coverage d v).1 = (sep d a ||| unionSep d v); rw [ih]

private lemma bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]



-- Each bit position pairs a positive and a negative input row.
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one

-- A set records the distinct signals needed by the remaining gates.
-- Read backwards, a gate replaces its output with the operand or operands.
def Live : Nat → Nat → Finset Sig → Prop
  | 0, t, S => t = 0 ∧ S = {target}
  | k+1, t, S =>
    (∃ u U a, t = u+1 ∧ S = insert a U ∧ proper a ∧ neg a ∉ insert a U ∧ Live k u (insert (neg a) U)) ∨
    (∃ U a b d, S = insert a (insert b U) ∧ proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live k t (insert (bin d a b) U))

lemma Live.stop : Live 0 0 {target} := ⟨rfl,rfl⟩

lemma Live.unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)) :
      Live (k+1) (t+1) (insert a U) := Or.inl ⟨_,_,_,rfl,rfl,ha,hfresh,tail⟩

lemma Live.binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)) :
      Live (k+1) t (insert a (insert b U)) := Or.inr ⟨_,_,_,_,rfl,ha,hb,hab,hfresh,tail⟩

lemma liveInd {P : ∀ k t S, Live k t S → Prop}
    (stop : P 0 0 {target} Live.stop)
    (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)), P k t (insert (neg a) U) tail → P (k+1) (t+1) (insert a U) (Live.unary ha hfresh tail))
    (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)), P k t (insert (bin d a b) U) tail → P (k+1) t (insert a (insert b U)) (Live.binary ha hb hab hfresh tail))
    {k t S} (h : Live k t S) : P k t S h := by
  induction k generalizing t S with
  | zero =>
    obtain ⟨rfl,rfl⟩ := h
    exact stop
  | succ k ih =>
    rcases h with ⟨u,U,a,rfl,rfl,ha,hf,tail⟩ | ⟨U,a,b,d,rfl,ha,hb,hab,hf,tail⟩
    · exact unary ha hf tail (ih tail)
    · exact binary ha hb hab hf tail (ih tail)

lemma liveCases {P : ∀ k t S, Live k t S → Prop}
    (stop : P 0 0 {target} Live.stop)
    (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)), P (k+1) (t+1) (insert a U) (Live.unary ha hfresh tail))
    (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)), P (k+1) t (insert a (insert b U)) (Live.binary ha hb hab hfresh tail))
    {k t S} (h : Live k t S) : P k t S h := by
  induction k generalizing t S with
  | zero =>
    obtain ⟨rfl,rfl⟩ := h
    exact stop
  | succ k ih =>
    rcases h with ⟨u,U,a,rfl,rfl,ha,hf,tail⟩ | ⟨U,a,b,d,rfl,ha,hb,hab,hf,tail⟩
    · exact unary ha hf tail
    · exact binary ha hb hab hf tail

private lemma target_proper : proper target := by unfold proper target zero one top; decide
private lemma live_proper {k t S} (h : Live k t S) : ∀ a ∈ S, proper a := by
  induction h using liveInd with
  | stop => simpa using target_proper
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {k t S} (h : Live k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h using liveInd with
  | stop => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩

private lemma sep_unary (t : Nat) (a : Sig) (i : Nat)
    (h : (sep (decide (0<t)) (neg a)).getLsbD i = true) :
    (sep true a).getLsbD i = true := by
  by_cases hi : i < 31
  · cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases ht : decide (0<t) <;>
      simp only [sep,neg,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 31 ≤ i)] at h

private lemma sep_binary (t d : Bool) (a b : Sig) (i : Nat)
    (h : (sep t (bin d a b)).getLsbD i = true) :
    (sep t a).getLsbD i = true ∨ (sep t b).getLsbD i = true := by
  by_cases hi : i < 31
  · cases t <;> cases d <;>
      cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases hu : b.1.getLsbD i <;> cases hv : b.2.getLsbD i <;>
      simp only [sep,bin,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,hu,hv] at h ⊢ <;> first | contradiction | decide
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 31 ≤ i)] at h

private lemma sep_weaken (t : Nat) (a : Sig) (i : Nat) (hi : i < 31)
    (h : (sep (decide (0<t)) a).getLsbD i = true) : (sep true a).getLsbD i = true := by
  cases ht : decide (0<t) <;> cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
    simp only [sep,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide

private lemma live_sep {k t S} (h : Live k t S) (i : Nat) (hi : i < 31) :
    ∃ a ∈ S, (sep (decide (0<t)) a).getLsbD i = true := by
  induction h using liveInd with
  | stop =>
    refine ⟨target,by simp,?_⟩
    change (BitVec.allOnes 31 &&& ~~~(0 : B)).getLsbD i = true
    rw [BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_allOnes (v := 31)]
    simp [hi]
  | unary ha hf _ ih =>
    obtain ⟨x,hx,h⟩ := ih
    simp only [Finset.mem_insert] at hx
    simp only [Nat.zero_lt_succ,decide_true]
    rcases hx with rfl | hU
    · exact ⟨_,Finset.mem_insert_self _ _,sep_unary _ _ _ h⟩
    · exact ⟨x,Finset.mem_insert_of_mem hU,sep_weaken _ _ _ hi h⟩
  | binary ha hb hab hf _ ih =>
    obtain ⟨x,hx,h⟩ := ih
    rcases Finset.mem_insert.mp hx with rfl | hU
    · rcases sep_binary _ _ _ _ _ h with h | h
      · exact ⟨_,Finset.mem_insert_self _ _,h⟩
      · exact ⟨_,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),h⟩
    · exact ⟨x,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU),h⟩
private lemma mem_unionSep (d : Bool) (v : List Sig) (i : Nat) :
    (unionSep d v).getLsbD i = true ↔ ∃ a ∈ v, (sep d a).getLsbD i = true := by
  induction v with
  | nil => simp [unionSep]
  | cons a v ih => simp only [unionSep,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]

private lemma live_cover {k t S} {v : List Sig} (h : Live k t S) (he : v.toFinset=S) :
    unionSep (decide (0<t)) v = top := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain ⟨a,hm,ha⟩ := live_sep h i hi
  have hmem : a ∈ v := List.mem_toFinset.mp (he.symm ▸ hm)
  simpa only [top,BitVec.getLsbD_allOnes,hi,decide_true] using (mem_unionSep _ _ _).2 ⟨a,hmem,ha⟩

private lemma union_append (d : Bool) (l r : List Sig) :
    unionSep d (l++r) = unionSep d l ||| unionSep d r := by
  induction l with
  | nil => simp [unionSep]
  | cons a l ih => simp [unionSep,ih,BitVec.or_assoc]

def keepOf (U : Finset Sig) (del : List Sig) : List Sig := del.filter (fun a => decide (a ∈ U))

private lemma edit_list {v del : List Sig} {U : Finset Sig}
    (hv : v.Nodup) (hd : del.Nodup) (he : v.toFinset = del.toFinset ∪ U) :
    (keepOf U del ++ dropped del v).Nodup ∧ (keepOf U del ++ dropped del v).toFinset = U := by
  have memv (x : Sig) : x ∈ v ↔ x ∈ del ∨ x ∈ U := by
    rw [← List.mem_toFinset,he]
    simp
  constructor
  · rw [List.nodup_append]
    refine ⟨hd.filter _,hv.filter _,?_⟩
    intro a ha b hb eq
    subst b
    simp [keepOf] at ha
    simp [dropped] at hb
    exact hb.2 ha.1
  · ext x
    simp only [List.mem_toFinset,List.mem_append,List.mem_filter,keepOf,dropped,decide_eq_true_eq,
      Bool.not_eq_true',List.contains_eq_mem,memv]
    by_cases h : x ∈ del <;> simp_all

private lemma recover_perm (del v : List Sig) (hv : v.Nodup) (hd : del.Nodup)
    (hs : ∀ x ∈ del, x ∈ v) : v.Perm (del ++ dropped del v) := by
  apply List.perm_of_nodup_nodup_toFinset_eq hv
  · rw [List.nodup_append]
    refine ⟨hd,hv.filter _,?_⟩
    intro a ha b hb e
    subst b
    simp [dropped] at hb
    exact hb.2 ha
  · ext x
    simp only [List.mem_toFinset,List.mem_append,dropped,List.mem_filter,Bool.not_eq_true',
      List.contains_eq_mem,decide_eq_false_iff_not]
    by_cases h : x ∈ del <;> simp_all

private lemma one_rest (d : Bool) {v : List Sig} {a : Sig} (hv : v.Nodup) (ha : a ∈ v) :
    v.length-1=(dropped [a] v).length ∧
      takeOne (coverage d v) (sep d a)=unionSep d (dropped [a] v) := by
  have p := recover_perm [a] v hv (by simp) (by simpa using ha)
  constructor
  · have l := p.length_eq; simp at l; omega
  · rw [cov_perm d p]
    exact (cov_one _ _).trans (cov_union _ _)

private lemma two_rest (d : Bool) {v : List Sig} {a b : Sig} (hv : v.Nodup)
    (ha : a ∈ v) (hb : b ∈ v) (hab : a ≠ b) :
    v.length-2=(dropped [a,b] v).length ∧
      takeTwo (coverage d v) (sep d a) (sep d b)=unionSep d (dropped [a,b] v) := by
  have p := recover_perm [a,b] v hv (by simp [hab]) (by simp [ha,hb])
  constructor
  · have l := p.length_eq; simp at l; omega
  · rw [cov_perm d p]
    exact (cov_two _ _ _).trans (cov_union _ _)

open PEqualNP.CircuitLowerBounds

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v

private lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)

private lemma bin_laws (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  obtain ⟨p,n⟩ := a
  simp only [bin,one,zero,top,reduceCtorEq,ite_true,ite_false,BitVec.and_allOnes,BitVec.or_allOnes,BitVec.and_self,BitVec.or_self,Prod.mk.injEq,and_self]
  simp

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one,top]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def isNot (op : GateOp) : Bool := match op with | .not => true | _ => false

def witness (allow : Bool) (w : List Sig) (z : Sig) : Prop :=
  (allow = true ∧ ∃ a ∈ w, proper a ∧ z = neg a) ∨
  (allow = false ∧ ∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

private lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness false w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩ := bin_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨rfl,d,a,b,ham,hbm,hap,hbp,he,rfl⟩)

private lemma gate_rep (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ witness (isNot g.op) w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  have nx (a : Sig) (ha : represented w a) : represented w (neg a) ∨ witness true w (neg a) := by
    rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨rfl,a,hm,hp,rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [gv,isNot,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witness false w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,isNot,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witness false w (w.getD i zero)) (get_rep w i)
      · exact nx _ (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv,isNot,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_rep false (get_rep w i) (get_rep w j)
        · simpa only [gv,isNot,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_rep true (get_rep w i) (get_rep w j)
        · exact nx _ (get_rep w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
private lemma pull_gate {flag : Bool} {w : List Sig} {z : Sig} {k t S} (h : Live k t S)
    (hz : represented w z ∨ witness flag w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ t' ≤ t+flag.toNat ∧ k'+t ≤ k+t'+(!flag).toNat ∧ Live k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,by omega,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨flagOn,a,ha,hp',eq⟩ | ⟨flagOff,d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live k t (insert (neg a) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,by simp [flagOn],by simp [flagOn]; omega,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live k t (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,by omega,by simp [flagOff]; omega,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,by omega,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ t ≤ gs.countP (fun g => isNot g.op) ∧
      k + gs.countP (fun g => isNot g.op) ≤ gs.length + t ∧ Live k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,by simp,by simp,Live.stop,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,hcount,hbin,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hcnt,hbin',hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
    refine ⟨l,u,T,by simp; omega,?_,?_,hu,hT⟩
    · cases hf : isNot g.op <;> simp [hf] at hcnt ⊢ <;> omega
    · cases hf : isNot g.op <;> simp [hf] at hbin' ⊢ <;> omega

def bit (side : Bool) (i : Fin 31) (a : Sig) : Bool :=
  (if side then a.1 else a.2).getLsbD i.val

private lemma bit_zero (s i) : bit s i zero = false := by cases s <;> simp [bit,zero]
private lemma bit_one (s i) : bit s i one = true := by
  cases s <;> change (BitVec.allOnes 31).getLsbD i.val = true <;> rw [BitVec.getLsbD_allOnes] <;> simp
private lemma bit_neg (s i) (a : Sig) : bit s i (neg a) = !(bit s i a) := by
  cases s <;> simp only [bit,neg,reduceCtorEq,ite_true,ite_false,BitVec.getLsbD_not,i.isLt,decide_true,Bool.true_and]
private lemma bit_bin (s i d) (a b : Sig) : bit s i (bin d a b) =
    (if d then bit s i a || bit s i b else bit s i a && bit s i b) := by
  cases s <;> cases d <;> simp only [bit,bin,reduceCtorEq,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or]

private lemma b_read (s i) (w : List Sig) (j : Nat) :
    (w.map (bit s i)).getD j false = bit s i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _ _).symm
  | some a => rfl

private lemma run_bit (s i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit s i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit s i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _ _
    | cons a l ih =>
      change bit s i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit s i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _ _
    | cons a l ih =>
      change bit s i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit s i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit s i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _ _

private lemma execute_bits (gs : List Gate) (s i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit s i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit s i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit s i g w (hg g (by simp))]


def cof (b : Bool) (x : Fin 5 → Bool) : Bool :=
  Nat.testBit (if b then 4269860992 else 4269860864) (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

def sample (raw : List Sig) (s : Bool) (i : Fin 31) (j : Fin 5) := bit s i (raw.getD j.val zero)
private lemma sample_list (raw : List Sig) (raw_id : List.ofFn (fun j : Fin 5 => raw.getD j.val zero) = raw) (s i) : List.ofFn (sample raw s i) = raw.map (bit s i) := by
  calc
    _ = (List.ofFn (fun j : Fin 5 => raw.getD j.val zero)).map (bit s i) := by rw [List.map_ofFn]; rfl
    _ = _ := by rw [raw_id]

private lemma circuit_target (f : (Fin 5 → Bool) → Bool) (raw : List Sig) (raw_id : List.ofFn (fun j : Fin 5 => raw.getD j.val zero) = raw)
    (sample_ok : ∀ s i, f (sample raw s i) = s) (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = f x) : target ∈ execute C.gates raw := by
  let w := execute C.gates raw
  have project (s i) : bit s i (w.getD C.output zero) = s := by
    rw [←b_read]
    change ((execute C.gates raw).map _).getD C.output false = _
    rw [execute_bits _ _ _ _ (fun g hg => (h g hg).1)]
    have eq := he (sample raw s i)
    rw [sample_list raw raw_id,sample_ok] at eq
    exact eq
  have et : w.getD C.output zero = target := by
    apply Prod.ext
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have p := project true ⟨i,hi⟩
      change (w.getD C.output zero).1.getLsbD i = true at p
      change _ = (BitVec.allOnes _).getLsbD _
      simpa only [BitVec.getLsbD_allOnes,hi,decide_true] using p
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have p := project false ⟨i,hi⟩
      change (w.getD C.output zero).2.getLsbD i = false at p
      have hz : (0 : B).getLsbD i=false := by simp
      exact p.trans hz.symm
  have rep := get_rep w C.output
  rw [et] at rep
  exact rep.resolve_right (fun hn => hn target_proper)

private lemma necessary (raw : List Sig) (every_input : raw.all (fun a => unionSep true (raw.erase a) != top) = true) {k t S} (l : Live k t S) (hs : ∀ a ∈ S, a ∈ raw) : raw.toFinset=S := by
  ext a
  rw [List.mem_toFinset]
  refine ⟨fun hr => ?_,hs a⟩
  by_contra hn
  have fail := List.all_eq_true.mp every_input a hr
  have cov : unionSep true (raw.erase a) = top := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    obtain ⟨b,hb,h⟩ := live_sep l i hi
    have ba : b ≠ a := fun he => hn (he ▸ hb)
    have hm := (List.mem_erase_of_ne ba).mpr (hs _ hb)
    have eq := (mem_unionSep true _ _).mpr ⟨b,hm,sep_weaken _ _ _ hi h⟩
    simpa only [top,BitVec.getLsbD_allOnes,hi,decide_true] using eq
  simp [cov] at fail

def special : List Sig := []
def gateAvailable (v : List Sig) (g : Sig) : Bool :=
  !(v.contains g) && g != zero && g != one

def tryGate (k t : Nat) (r : List Sig → Bool) (v rest : List Sig) (n : Nat) (c : B) (g : Sig)
    (keep : List (List Sig)) : Bool :=
  let d := decide (0<t)
  let base := sep d g ||| c
  if n = k-t then
    base == top && gateAvailable v g && r (g::rest)
  else keep.any (fun h => decide (n+h.length+1 ≤ k-t+1) &&
    (base ||| unionSep d h == top) && gateAvailable v g && r (g::(h++rest)))

def unaryAt (k t : Nat) (r : List Sig → Bool) (v : List Sig) (c : Cov) (a : Sig) : Bool :=
  !(special.contains a) &&
    tryGate k t r v (dropped [a] v) (v.length-1) (takeOne c (sep (decide (0<t)) a)) (neg a) [[],[a]]

def unaryMoves (k t : Nat) (r : List Sig → Bool) (v : List Sig) : Bool :=
  let c := coverage (decide (0<t)) v
  v.any (unaryAt k t r v c)

def allowedKeeps (a b : Sig) : List (List Sig) :=
  [[],[a],[b],[a,b]].filter (fun w => w.all fun x => !(special.contains x))

def fastBinary (r : List Sig → Bool) (v : List Sig) (a b : Sig) (ua ub : B) : Bool :=
  let rest := dropped [a,b] v
  let use := fun (g : Sig) => gateAvailable v g && r (g::rest)
  ((ua &&& ~~~b.1) == 0 && (ub &&& ~~~a.1) == 0 &&
    !(special.contains a) && !(special.contains b) && use (bin false a b)) ||
    ((ua &&& b.2) == 0 && (ub &&& a.2) == 0 && use (bin true a b))

def slowBinary (k t : Nat) (r : List Sig → Bool) (v : List Sig) (c : Cov) (a b : Sig) : Bool :=
  let rest := dropped [a,b] v
  let mask := takeTwo c (sep (decide (0<t)) a) (sep (decide (0<t)) b)
  ((!(special.contains a) && !(special.contains b)) &&
    tryGate k t r v rest (v.length-2) mask (bin false a b) [[],[a],[b],[a,b]]) ||
    tryGate k t r v rest (v.length-2) mask (bin true a b) (allowedKeeps a b)

def scanPairs {α : Type} (p : α → α → Bool) : List α → Bool
  | [] => false
  | a :: t => t.any (p a) || scanPairs p t

lemma scanPairs_complete {α : Type} (p : α → α → Bool) {a b : α} {v : List α}
    (ha : a ∈ v) (hb : b ∈ v) (hne : a ≠ b)
    (hab : p a b = true) (hba : p b a = true) : scanPairs p v = true := by
  induction v with
  | nil => simp at ha
  | cons h v ih =>
    simp only [scanPairs, Bool.or_eq_true]
    by_cases eqA : a = h
    · subst h
      exact Or.inl (List.any_eq_true.mpr ⟨b, (List.mem_cons.mp hb).resolve_left (Ne.symm hne), hab⟩)
    · have ha' := (List.mem_cons.mp ha).resolve_left eqA
      by_cases eqB : b = h
      · subst h
        exact Or.inl (List.any_eq_true.mpr ⟨a, ha', hba⟩)
      · exact Or.inr (ih ha' ((List.mem_cons.mp hb).resolve_left eqB))

def binaryMoves (k t : Nat) (r : List Sig → Bool) (v : List Sig) : Bool :=
  let d := decide (0<t)
  let c := coverage d v
  if t == 0 && v.length == k+2 then
    let acts := v.map (fun a => (a, c.2.1 &&& sep false a))
    scanPairs (fun a b => fastBinary r v a.1 b.1 a.2 b.2) acts
  else scanPairs (slowBinary k t r v c) v

def stepTest (k t : Nat) (v : List Sig) (u b : List Sig → Bool) : Bool :=
  if t>k+1 ∨ v.length>k+1-t+1 then false else
    v == [target] || (decide (0<t) && unaryMoves k (t-1) u v) || binaryMoves k t b v

def search : Nat → Nat → List Sig → Bool
  | 0, _, v => v == [target]
  | k+1,t,v => stepTest k t v (search k (t-1)) (search k t)

private lemma gate_found {k t m : Nat} {v rest h : List Sig} {g : Sig} {opts : List (List Sig)}
    {S : Finset Sig} {r : List Sig → Bool} (l : Live m t S)
    (hle : m ≤ k) (hp : proper g) (ha : g ∉ v) (hh : h ∈ opts)
    (hn : (g::(h++rest)).Nodup) (he : (g::(h++rest)).toFinset=S)
    (hr : r (g::(h++rest)) = true) : tryGate k t r v rest rest.length (unionSep (decide (0<t)) rest) g opts = true := by
  obtain ⟨ht,hc⟩ := live_size l
  rw [←he,List.toFinset_card_of_nodup hn] at hc
  simp only [List.length_cons,List.length_append] at hc
  have hl : rest.length+h.length+1 ≤ k-t+1 := by omega
  have cv := live_cover l he
  rw [unionSep,union_append] at cv
  have cov : (sep (decide (0<t)) g ||| unionSep (decide (0<t)) rest) ||| unionSep (decide (0<t)) h = top := by
    rw [← cv]; ac_rfl
  by_cases tight : rest.length=k-t
  · have hz : h.length=0 := by omega
    have hem : h=[] := List.length_eq_zero_iff.mp hz
    subst h
    have ok : sep (decide (0<t)) g ||| unionSep (decide (0<t)) rest = top := by
      simpa [unionSep] using cov
    simp [tryGate,tight,ok,gateAvailable,ha,hp.1,hp.2,hr] at *
  · have hav : gateAvailable v g = true := by simp [gateAvailable, ha, hp.1, hp.2]
    simp only [tryGate, ite_eq_right tight, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq, hav, and_true]
    exact ⟨h,hh,⟨hl,cov⟩,hr⟩

private lemma unique_needed (c : Cov) (a b : Sig) (op : Bool)
    (h : sep false (bin op a b) ||| takeTwo c (sep false a) (sep false b)=top) :
    ((c.2.1 &&& sep false a) &&& (if op then b.2 else ~~~b.1)) |||
    ((c.2.1 &&& sep false b) &&& (if op then a.2 else ~~~a.1))=0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hh := congrArg (fun z : B => z.getLsbD i) h
  clear h
  cases op <;> simp only [sep,bin,ite_false,ite_true,takeTwo,top,BitVec.getLsbD_allOnes,
    BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,
    reduceCtorEq,hi,decide_true,Bool.true_and] at hh ⊢ <;>
    cases ax : a.1.getLsbD i <;> cases ay : a.2.getLsbD i <;>
    cases bx : b.1.getLsbD i <;> cases byy : b.2.getLsbD i <;>
    cases um : c.2.1.getLsbD i <;> simp [ax,ay,bx,byy,um] at hh ⊢

private lemma fast_ok {k r v c a b}
    (hlen : v.length-2=k) (h : slowBinary k 0 r v c a b = true) :
    fastBinary r v a b (c.2.1 &&& sep false a) (c.2.1 &&& sep false b) = true := by
  simp only [slowBinary,tryGate,Nat.sub_zero,hlen,ite_true,Bool.or_eq_true,
    Bool.and_eq_true,beq_iff_eq] at h
  simp only [fastBinary, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  rcases h with ⟨⟨ha,hb⟩,⟨hc,hav⟩,hr⟩ | ⟨⟨hc,hav⟩,hr⟩
  · obtain ⟨h1,h2⟩ := BitVec.or_eq_zero_iff.mp (unique_needed c a b false hc)
    exact Or.inl ⟨⟨⟨⟨h1,h2⟩,ha⟩,hb⟩,hav,hr⟩
  · obtain ⟨h1,h2⟩ := BitVec.or_eq_zero_iff.mp (unique_needed c a b true hc)
    exact Or.inr ⟨⟨h1,h2⟩,hav,hr⟩

private lemma unary_found {m t k : Nat} {U : Finset Sig} {a : Sig} {v : List Sig}
    {r : List Sig → Bool}
    (hv : v.Nodup) (he : v.toFinset = insert a U) (hle : m ≤ k)
    (fresh : neg a ∉ insert a U) (ha : a ∉ special) (l : Live m t (insert (neg a) U))
    (ih : ∀ v : List Sig, v.Nodup → v.toFinset = insert (neg a) U → r v = true) :
    unaryMoves k t r v = true := by
  let h := keepOf U [a]
  let rest := dropped [a] v
  have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  obtain ⟨hn,eq⟩ := edit_list (del := [a]) (U := U) hv (by simp) (by simpa using he)
  change (h++rest).Nodup at hn
  change (h++rest).toFinset=U at eq
  have nn : neg a ∉ v := fun hm => fresh (he ▸ List.mem_toFinset.mpr hm)
  have nz : neg a ∉ U := fun hm => fresh (Finset.mem_insert_of_mem hm)
  have hnd : (neg a::(h++rest)).Nodup := List.nodup_cons.mpr ⟨fun hm => nz (eq ▸ List.mem_toFinset.mpr hm),hn⟩
  have e : (neg a::(h++rest)).toFinset=insert (neg a) U := by rw [List.toFinset_cons,eq]
  have opts : h ∈ [[],[a]] := by by_cases hm : a ∈ U <;> simp [h,keepOf,hm]
  apply List.any_eq_true.mpr
  refine ⟨a,ah,?_⟩
  unfold unaryAt
  obtain ⟨hlen,hmask⟩ := one_rest (decide (0<t)) hv ah
  rw [hlen,hmask]
  apply Bool.and_eq_true_iff.mpr
  exact ⟨by simp [ha], gate_found l hle (live_proper l _ (Finset.mem_insert_self _ _)) nn opts hnd e (ih _ hnd e)⟩

private lemma slow_found {m t k : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} {v : List Sig}
    {r : List Sig → Bool}
    (hv : v.Nodup) (he : v.toFinset = insert a (insert b U)) (hle : m ≤ k)
    (hab : a≠b) (fresh : bin d a b ∉ insert a (insert b U))
    (hra : a ∈ special → d = true ∧ a ∉ U)
    (hrb : b ∈ special → d = true ∧ b ∉ U)
    (l : Live m t (insert (bin d a b) U))
    (ih : ∀ v : List Sig, v.Nodup → v.toFinset = insert (bin d a b) U → r v = true) :
    slowBinary k t r v (coverage (decide (0<t)) v) a b = true := by
  let g := bin d a b
  let h := keepOf U [a,b]
  let rest := dropped [a,b] v
  have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  have bh : b ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  obtain ⟨hn,eq⟩ := edit_list (del := [a,b]) (U := U) hv (by simp [hab]) (by simpa using he)
  change (h++rest).Nodup at hn
  change (h++rest).toFinset=U at eq
  have nn : g ∉ v := fun hm => fresh (he ▸ List.mem_toFinset.mpr hm)
  have nz : g ∉ U := fun hm => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
  have hnd : (g::(h++rest)).Nodup := List.nodup_cons.mpr ⟨fun hm => nz (eq ▸ List.mem_toFinset.mpr hm),hn⟩
  have e : (g::(h++rest)).toFinset=insert g U := by rw [List.toFinset_cons,eq]
  have opts : h ∈ [[],[a],[b],[a,b]] := by
    by_cases ha : a ∈ U <;> by_cases hb : b ∈ U <;> simp [h,keepOf,ha,hb]
  have allow : h ∈ allowedKeeps a b := by
    apply List.mem_filter.mpr
    refine ⟨opts,List.all_eq_true.mpr (fun x hx => ?_)⟩
    have hm : x ∈ U := (List.mem_filter.mp hx).2 |> of_decide_eq_true
    rcases List.mem_cons.mp (List.mem_filter.mp hx).1 with rfl | hx
    · simpa using fun ha : x ∈ special => (hra ha).2 hm
    · obtain rfl := List.mem_singleton.mp hx
      simpa using fun hb : x ∈ special => (hrb hb).2 hm
  obtain ⟨hlen,hmask⟩ := two_rest (decide (0<t)) hv ah bh hab
  unfold slowBinary
  dsimp only
  rw [hlen,hmask]
  cases d with
  | false =>
    have na : a ∉ special := fun ha => Bool.false_ne_true (hra ha).1
    have nb : b ∉ special := fun hb => Bool.false_ne_true (hrb hb).1
    apply Bool.or_eq_true_iff.mpr
    left
    exact Bool.and_eq_true_iff.mpr ⟨by simp [na,nb],
      gate_found l hle (live_proper l _ (Finset.mem_insert_self _ _)) nn opts hnd e (ih _ hnd e)⟩
  | true =>
    apply Bool.or_eq_true_iff.mpr
    right
    exact gate_found l hle (live_proper l _ (Finset.mem_insert_self _ _)) nn allow hnd e (ih _ hnd e)

private lemma binary_found {m t k : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} {v : List Sig}
    {r : List Sig → Bool}
    (hv : v.Nodup) (he : v.toFinset = insert a (insert b U)) (hle : m ≤ k)
    (hab : a≠b) (fresh : bin d a b ∉ insert a (insert b U))
    (hra : a ∈ special → d = true ∧ a ∉ U)
    (hrb : b ∈ special → d = true ∧ b ∉ U)
    (l : Live m t (insert (bin d a b) U))
    (ih : ∀ v : List Sig, v.Nodup → v.toFinset = insert (bin d a b) U → r v = true) :
    binaryMoves k t r v = true := by
  have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  have bh : b ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have h1 := slow_found hv he hle hab fresh hra hrb l ih
  have e' : v.toFinset = insert b (insert a U) := by rwa [Finset.insert_comm b a]
  have hf : bin d b a ∉ insert b (insert a U) := by rwa [bin_comm d b a, Finset.insert_comm b a]
  have ht : Live m t (insert (bin d b a) U) := by rwa [bin_comm d b a]
  have h2 := slow_found hv e' hle hab.symm hf hrb hra ht (by simpa only [bin_comm d b a] using ih)
  unfold binaryMoves
  split
  · rename_i cut
    simp only [Bool.and_eq_true, beq_iff_eq] at cut
    obtain ⟨rfl,hvlen⟩ := cut
    have hlen : v.length - 2 = k := by omega
    let f := fun x => (x, (coverage false v).2.1 &&& sep false x)
    have na : f a ∈ v.map f := List.mem_map_of_mem ah
    have nb : f b ∈ v.map f := List.mem_map_of_mem bh
    exact scanPairs_complete _ na nb (fun e => hab (congrArg Prod.fst e))
      (fast_ok hlen h1) (fast_ok hlen h2)
  · exact scanPairs_complete _ ah bh hab h1 h2

private lemma reduced_step {m t S : Nat} {s : Finset Sig} {v : List Sig} {u b : List Sig → Bool}
    (h : Live m t s) (hb : m ≤ S+1) (hv : v.Nodup) (he : v.toFinset = s)
    (hu : ∀ w, w.Nodup → ∀ l ≤ S, Live l (t-1) w.toFinset → u w = true)
    (hb' : ∀ w, w.Nodup → ∀ l ≤ S, Live l t w.toFinset → b w = true) :
    stepTest S t v u b = true := by
  have size := live_size h
  rw [← he, List.toFinset_card_of_nodup hv] at size
  rw [stepTest, ite_eq_right (by omega)]
  induction h using liveCases with
  | stop =>
    have p : v.Perm [target] := List.perm_of_nodup_nodup_toFinset_eq hv (by simp) (by simp [he])
    have eq := List.perm_singleton.mp p
    simp [eq]
  | @unary m t U a ha hf tail =>
    apply Bool.or_eq_true_iff.mpr
    left
    apply Bool.or_eq_true_iff.mpr
    right
    apply Bool.and_eq_true_iff.mpr
    refine ⟨by simp, unary_found hv he (by omega) hf (by simp [special]) tail ?_⟩
    intro w hn hs
    exact hu w hn m (by omega) (hs.symm ▸ tail)
  | @binary m t U a b d ha hc hab hf tail =>
    apply Bool.or_eq_true_iff.mpr
    right
    apply binary_found hv he (by omega) hab hf (by simp [special]) (by simp [special]) tail
    intro w hn hs
    exact hb' w hn m (by omega) (hs.symm ▸ tail)

lemma search_complete {m t : Nat} {S : Finset Sig} (h : Live m t S) (k : Nat) (hk : m ≤ k)
    (v : List Sig) (hv : v.Nodup) (hs : v.toFinset = S) : search k t v = true := by
  induction k generalizing m t S v with
  | zero =>
    have hm : m = 0 := by omega
    subst m
    obtain ⟨rfl,rfl⟩ := h
    have p : v.Perm [target] := List.perm_of_nodup_nodup_toFinset_eq hv (by simp) (by simp [hs])
    simp [search, List.perm_singleton.mp p]
  | succ k ih =>
    rw [search]
    apply reduced_step h hk hv hs <;>
      exact fun w hn l hl hh => ih hh hl w hn rfl



open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def lo : List Sig := [(0x14d89fcf, 0x35f88bc5), (0xb68e7f3, 0x4f78a5d2), (0x68b707fc, 0x7abb06e8), (0x7ffff87f, 0x5783f), (0x7707ff80, 0x7fc6d700)]
def hi : List Sig := [(0x7d09f1ff, 0x6f08b0db), (0x7a8e7e3f, 0x5b8a562d), (0x70f07fc7, 0x34b06b46), (0xfff8ff8, 0x578db0), (0x7fff000, 0x7fed7000)]
def raw (b : Bool) : List Sig := if b then hi else lo

lemma rawLength (b : Bool) : List.ofFn (fun j : Fin 5 => (raw b).getD j.val zero) = raw b := by
  cases b <;> rfl

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma sample_valid : ∀ b s i, cof b (sample (raw b) s i) = s := by decide +kernel

lemma rawNodup (b : Bool) : (raw b).Nodup := by cases b <;> decide +kernel

lemma rawEssential (b : Bool) : (raw b).all (fun a => unionSep true ((raw b).erase a) != top) = true := by
  cases b <;> decide +kernel

lemma rawCard (b : Bool) : (raw b).toFinset.card = 5 := by cases b <;> decide +kernel

private abbrev SearchState := Nat × List Sig

private def sigLE (a b : Sig) : Bool :=
  if a.1 == b.1 then decide (a.2.toNat ≤ b.2.toNat) else decide (a.1.toNat ≤ b.1.toNat)

private def insertWire (a : Sig) : List Sig → List Sig
  | [] => [a]
  | b :: bs => if sigLE a b then a :: b :: bs else b :: insertWire a bs

private def orderWires : List Sig → List Sig
  | [] => []
  | a :: l => insertWire a (orderWires l)

private lemma insertWire_perm (a : Sig) : ∀ l, (insertWire a l).Perm (a :: l)
  | [] => .refl _
  | b :: l => by
    unfold insertWire
    split
    · exact .refl _
    · exact ((insertWire_perm a l).cons b).trans (.swap a b l)

private lemma orderWires_perm : ∀ l, (orderWires l).Perm l
  | [] => .refl _
  | a :: l => (insertWire_perm a (orderWires l)).trans ((orderWires_perm l).cons a)

private def sameWires (a b : List Sig) : Bool := orderWires a == b

private lemma sameWires_sound {a b : List Sig} (h : sameWires a b = true) :
    a.toFinset = b.toFinset := by
  have ea : orderWires a = b := beq_iff_eq.mp h
  have p := orderWires_perm a
  rw [ea] at p
  ext w
  simp only [List.mem_toFinset]
  exact p.mem_iff.symm

private def checkLink (count : Nat → Nat) (state : Nat → Nat → SearchState)
    (locate : Nat → Nat → SearchState → List Nat) (k i : Nat) (s : SearchState) : Bool :=
  (locate k i s).any (fun j =>
    let u := state k j
    decide (j < count k) && s.1 == u.1 && sameWires s.2 u.2)

private def runCheck (count : Nat → Nat) (state : Nat → Nat → SearchState)
    (locate : Nat → Nat → SearchState → List Nat) (k i : Nat) : Bool :=
  let (t, v) := state k i
  decide v.Nodup && (if k = 0 then v != [target] else
    !(stepTest (k-1) t v
      (fun w => !(checkLink count state locate (k-1) i (t-1,w)))
      (fun w => !(checkLink count state locate (k-1) i (t,w)))))

private lemma runCheck_complete {count : Nat → Nat} {state : Nat → Nat → SearchState}
    {locate : Nat → Nat → SearchState → List Nat} {cap : Nat}
    (checked : ∀ k ≤ cap, ∀ i < count k, runCheck count state locate k i = true) :
    ∀ k ≤ cap, ∀ i < count k, ∀ m ≤ k,
      ¬ Live m (state k i).1 (state k i).2.toFinset := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hcap i hi m hm live
    have checkedHere := checked k hcap i hi
    let t := (state k i).1
    let v := (state k i).2
    change Live m t v.toFinset at live
    change (decide v.Nodup && (if k = 0 then v != [target] else _)) = true at checkedHere
    obtain ⟨hnd, no⟩ := Bool.and_eq_true_iff.mp checkedHere
    have nd := of_decide_eq_true hnd
    by_cases kzero : k = 0
    · have mz : m = 0 := by omega
      subst m
      obtain ⟨_, hs⟩ := live
      have p : v.Perm [target] := List.perm_of_nodup_nodup_toFinset_eq nd (by simp) (by simpa using hs)
      simp [kzero, List.perm_singleton.mp p] at no
    · have imposs : ∀ u w l, l ≤ k-1 → Live l u w.toFinset →
          Bool.not (checkLink count state locate (k-1) i (u,w)) = true := by
        intro u w l hl hn
        by_contra bad
        have good : checkLink count state locate (k-1) i (u,w) = true := by
          cases h : checkLink count state locate (k-1) i (u,w) <;> simp_all
        unfold checkLink at good
        obtain ⟨j, _, hg⟩ := List.any_eq_true.mp good
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hg
        obtain ⟨⟨hh, ht⟩, he⟩ := hg
        have setEq := sameWires_sound he
        rw [ht,setEq] at hn
        exact ih (k-1) (by omega) (by omega) _ hh l hl hn
      have ok := reduced_step (S:=k-1) live (by omega) nd rfl
        (fun w _ l hl hh => imposs _ w l hl hh) (fun w _ l hl hh => imposs _ w l hl hh)
      change (if k = 0 then v != [target] else
        !(stepTest (k-1) t v
          (fun w => !(checkLink count state locate (k-1) i (t-1,w)))
          (fun w => !(checkLink count state locate (k-1) i (t,w))))) = true at no
      rw [if_neg kzero, ok] at no
      exact Bool.false_ne_true no

private def checkBatch (count : Nat → Nat) (state : Nat → Nat → SearchState)
    (locate : Nat → Nat → SearchState → List Nat) (k lo : Nat) : Nat → Bool
  | 0 => true
  | n+1 => runCheck count state locate k lo && checkBatch count state locate k (lo+1) n

private lemma checkBatch_join (count : Nat → Nat) (state : Nat → Nat → SearchState)
    (locate : Nat → Nat → SearchState → List Nat) (k lo l r : Nat)
    (hl : checkBatch count state locate k lo l = true)
    (hr : checkBatch count state locate k (lo+l) r = true) :
    checkBatch count state locate k lo (l+r) = true := by
  induction l generalizing lo with
  | zero => simpa using hr
  | succ l ih =>
    rw [show l+1+r=l+r+1 by omega, checkBatch]
    obtain ⟨here, more⟩ := Bool.and_eq_true_iff.mp hl
    exact Bool.and_eq_true_iff.mpr ⟨here, ih (lo+1) more (by convert hr using 2 <;> omega)⟩

private lemma checkBatch_at {count : Nat → Nat} {state : Nat → Nat → SearchState}
    {locate : Nat → Nat → SearchState → List Nat} {k lo n : Nat}
    (h : checkBatch count state locate k lo n = true) (i : Nat)
    (hlo : lo ≤ i) (hi : i < lo+n) : runCheck count state locate k i = true := by
  induction n generalizing lo with
  | zero => omega
  | succ n ih =>
    obtain ⟨here, more⟩ := Bool.and_eq_true_iff.mp h
    by_cases he : i=lo
    · exact he.symm ▸ here
    · exact ih more (by omega) (by omega)

private def unpack (f : Nat → Nat) (width chunk i : Nat) : Nat :=
  (f (i / chunk) >>> ((i % chunk) * width)) &&& ((1 <<< width) - 1)


private def wireDataPacked (i : Nat) : Nat :=
  (if i < 108 then (if i < 54 then (if i < 27 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then 0x80000000000000010028000000000002024000000000000201200000000000020140000000000002040000000000000108000000000000009 else (if i < 2 then
  0x15e2070000000000540810000000000011400000000000003800c000000000008000000000000001009000000000000114000000000000020420 else 0xc208080000000003080020000000000908081080000000242020000000000090008108000000010a042040000000042810000000000010804204))
  else (if i < 4 then 0x12c20402400000004b0810000000000128e8130000000004a0204000000000128001000000000035c2830000000000d2818918000000030ba02c0 else (if i < 5 then
  0x3800040250800000e0000080d2000003800000000000000200000000000000001ea08180000000006f28304b000000016ea1483400000004f428500 else
  0xf00c2e00b0000003c03080020000000f0015e2070000003c0000000000000038090c2a74800000e024002042000003800042274800000e000108990))) else (if i < 9 then (if i < 7 then
  0xf01ea08180000003c07a80060000000f013de2170000003c04f40850000000f0128e0130000003c04a00040000000f00d7e20f0000003c035c08300 else (if i < 8 then
  0x1c000008189000003e04a3804c000000f80c2e00b0000003e0003800c000000f01ffea1f0000003c07ff887c000000f01ff0a1c0000003c07aba06c0 else
  0xe0009000800000038000000000000001f80004a3fd800007e00010090000001c0042c93c90000070000120f2400001c0000483480000070000100b04)) else (if i < 11 then (if i < 10 then
  0x10f00d7020c0000043c005408100000100000000000000038e0240020000000e001fea1c00000038006f0830000000e0016e214000000380034a06000 else
  0x9000060000a05c024000180002012009000060000201400438006f0830000010e0012c20400000400000000000000010f8015e2070000043c04f408500) else (if i < 12 then
  0x910f861502040002443e1803800c0009100860000000002440018540810000900f07ffeabf5c0240021803800c0009000061502a45c0240001803828d7 else
  0xe0000001d4240003800000065000000e000000154240003800000030090000910f87ffea1f0002443e1cf7885c000910f86d7e20f0002443e1857881c0)))) else (if i < 20 then (if i < 16 then (if i < 14 then
  0x100000000000000038070000770f2400e0038090c0a50803800e0007589d200e003800040240003800002475294200e0000090808000038000010f54b04 else (if i < 15 then
  0x12000180000201404438005b8850000100fc00420100000403800348060000100e0004201000004007e00000000001001c0042010810040070000000000 else
  0x1200f19ffee3fb40480026003800c00120009800000000048000630830a2d01200018c20008000480006003908ed01200018000420b4048000600010028)) else (if i < 18 then (if i < 17 then
  0x1210f98d7e20f0004803e67ffa87c001200f99eae81b0004803e67ab806c001200f98d7e20f0004803e630b802c001200f98c200080004803e6003800c0 else
  0x1b10f9e15e2271406c43e7857881c001b1009e0000000006c03e7b5f88bc501b00f9ec2e02b1406c0027803808c501b0009e0000201406c00078001283f) else (if i < 19 then
  0x1e01c0042c12c1007807000010090001e01c000000000007800e00000000001e000004281000007800000000000001b10f9ed7e20f0006c43e7b0b802c0 else
  0x1e0e001fea1c000078380034a0600001e0e0009000800007838001080400001e01f80d2c1ad1807807e02430294201e01f8042c12c1007807e000100900))) else (if i < 23 then (if i < 21 then
  0x1f0e001fea1c0000783fe034b0690001e0ff809040a4000783fe01090490001e0fc00d2c1ac100783f0034a0600001e0e380d2c1a50807838e034a06000 else (if i < 22 then
  0x4ec000001dc348010700004b081000040c1c00015c3c9010300004b4f1429040c0000439d1890103000000470420040c000001140000103000000020420 else
  0x51ce0016e21400014738004b081000051ce00042010000147070000000000051c000000000000143070010824624050c1c0000081080143000010804000)) else (if i < 25 then (if i < 24 then
  0x5ec1c0042c93c9017b070000570d2005ec00004395000017b000000450000051cfc016e2958901473f005b885000051ce001fea1c00014738007f887000 else
  0x5ec1f80015c348017b07005bff5f2d05ec1c00d3ddbd9817b070010f74f2405ec1c0043dd348017b070010f54b0405ec1c00439d189017b070010d74f24) else (if i < 26 then
  0x5fce000d281800017f07e00010090005fc00000000000017b3f0034f76f2405ece001ffb5c00017b380034e5600005ec1f8043df3fd817b07e010f74f24 else
  0x600c0000011c0481803000000450000600c0000000804817f3fe05b98590005fcfc016ffd7c9017f38007fa8700005fce0016fb5400017f38005b885000))))) else (if i < 40 then (if i < 33 then (if i < 30 then (if i < 28 then
  0x601cf012800100018073c0054081000601c000150204001807000000000000600cf01fffbdf4818030004a0674120600c0012800100018030000544f112 else (if i < 29 then
  0x691c006000080481a43001800478170601cf813de2170018073c07ffa87c00601cf01ff0a1c0018073c07fc087000601cf013de2170018073c04f408500 else
  0x691cf873de217001a473e1cf4085000691cf8615e287481a473e1857881c00691cf073de297481a473c1cf40a5120691c086000000001a470018540a112)) else (if i < 31 then
  0xa03000091968348280c000240020000a03000001160240280c000004500000a030000000202401c873e67ff887c00721cf193d0634b41c833e630bc72d2 else (if i < 32 then
  0xa13e00090008000284c0e0000000000a1300012c204000284c000000000000a03038090028348280c0e0005589d20a03038000020240280c0004b4d9099 else
  0xae30000919480002b8c000007589900ae3000001140000284f8e06f08b0d20a13e381bc20c000284f8007fa870000a13e001bc20c000284f8004b081000))) else (if i < 36 then (if i < 34 then
  0xae30380d3d7af582b8c0e02475a9d20ae3038091d6a6402b8c0e0247529420ae30380919683482b8c0e02455a9d20ae3038090c2a7482b8c0e000558990 else (if i < 35 then
  0xbe31f8091d6a7482f8c7e0005589900b13e001fe21c0002bcf8e06f7db9d20af3e001bdb4c0002b8f8007fed70000ae31f8091debfd82b8c0e06f7db9db else
  0xbf3ff81bc60e4002fcf8007fa870000bf3e001bc20c0002fcf80034a060000bf31f80004024002fcc000000000000be3e380d3d7a7482f8f80034e56000)) else (if i < 38 then (if i < 37 then
  0xeff0000011400003bbc0e02477adf20eef000091948000387f8007fed70000e1fe001bd34c000387c0004b4d10000e1f000001140000383c000004784b0 else
  0xf1fe0016f3540003c7f8005b8850000f1f0000000000003c3c7e03482e6f60effe001ffb5c0003bff8006f6d30000eff0001bdb4c0003bfc0004b6d1000) else (if i < 39 then
  0xfef1f80d3dfbfd83fbc7e000578db00fef1c0043df3ed03fbc00034e560000fef0000439500003fbc000004500000f1fe001fe21c0003c7f8006f083000 else
  0xfff0000439508103ffc00010e540000fff0000431500003ffc000006500000fff0000011400003ffc000000000000fefe001ffb5c0003fbf80034e56000)))) else (if i < 47 then (if i < 43 then (if i < 41 then
  0xfff0001bdb4c0003ffc0005bed50000fff00012d3440243ffc0004b4d10000fff0000d39580003ffc000246520420fff0000919480003ffc00024452000 else (if i < 42 then
  0xfff1f80011400003ffc70010f74f240fff1c00015c34803ffc700004500000fff038091d6a7483ffc0e0005589900fff0380011400003ffc0007fed7000 else
  0xfffe0012d3440003fff80034e560000fffe000d31580003fff80034a060000fffe000911480003fff80010c540000fffe000011400003ffc7e000550900)) else (if i < 45 then (if i < 44 then
  0xfffe001fea1c0003fff8007f8870000fffe001bdb4c0003fff8006f4d30000fffe001bc20c0003fff8005bed50000fffe0016f3540003fff8005b885000 else
  0xfffe001ffb5c9183fff8007fed720d0fffe001ffb5c8103fff8007fed704b0fffe001ffb5c1083fff8007fed70090fffe001ffb5c0003fff8007fcd7000) else (if i < 46 then
  0xfffe381fff7e6403fff8e07ffd79420fffe381ffb7c3483fff8e07fed70420fffe381ffb5c0003fff8007ffd79000fffe001ffbdd0803fff8007fedf090 else
  0xfffff81ffb5c0003ffff007fff7f240ffffc01fffdf4803ffff007ffd7b040ffffc01ffbdd8903ffff007fed72040ffffc01ffb5c0003fff8e07ffdf9d2))) else (if i < 50 then (if i < 48 then
  0x100003f000020240400001c4b0a94b910000070000a12e4400001c000284b010000070000810a4400001c000080990fffff81ffffffd83ffffe07ffd7900 else (if i < 49 then
  0x1010e0712c20400040400fc00000000101000712c204024404001c0000000010001ff0004a36c0400071c00128fbd10001c700008108040000fc00128dfb else
  0x104000e000e0030041000380000000010400061280c90e841000184a0004001040006000e483e841000180001203a10400060000400a0410001800002012)) else (if i < 52 then (if i < 51 then
  0x10400fe1ffea1f0041003f87aba06c010400fe1eae01b0041003f84f7885c010400fe128e0130041003f84a00040010400fe000e0030041003d87ffba7fa else
  0x10d10fe615e2070043440398000000010d00fe73de2974843403f9ca3824d210d000e600e0834843400398000201210d000660004a0fc41043f84f7885c0) else (if i < 53 then
  0x116000f800e403a0458003e00010028116000f800000000458001e0001283f11101c700000000043443f9cf7885c010d10fe728e0130043443f98578a1d2 else
  0x11f000fe0004a0fc47807fc00128db011600ff9eaec1ba045803fe7ab806c011600ff928e413a045803fe4a3804c011600ff8c2e40ba045803fe30b802c0)))))) else (if i < 81 then (if i < 67 then (if i < 60 then (if i < 57 then (if i < 55 then
  0x11f00ffec2e4abfc47c003fca3b2cff11f000fec2ecabfc47c003f8579a9ff11f000fe00e4a3fc47c003f803920fa11f000fe00e423b447c003f803828d7 else (if i < 56 then
  0x14fc03f1bce8f5ac507001c4b0a1429141c007000081080503001c004784b911f10ffe15e6a7fc47c07fc0010090011f00fffffeebffc47c03ffca392cff else
  0x151ce0716e21400054707fc00128db0151c1ff000081080547071c5b8a562d151c1c712c2850a4547071c10824624151c1c7000081080547001c00000000)) else (if i < 58 then
  0x15fc1c70015c348057f071c0002042015ec1ff0015e36c057b071c10f7cfbd151cfc716e2950805473f1c4b0a1420151cfc7042091080547381c5b8a5429 else (if i < 59 then
  0x1640cf613de2974859030184a0024121640c0600015c0e859030180000201215fcfff1fee9f48057f3f1c34a2642015fc1ff00048348057f071c10f74f24 else
  0x16d0cfe728e093485b43039ca3824d21641cfe13de2170059073f84f4085001641cfe128e0130059073d84f40a5121641c0e00000000059033f84a3824d2))) else (if i < 63 then (if i < 61 then
  0x16d1cf673d0294485b47039ca00241216d1c0e615e287485b470398540a11216d1c0e600e083485b470398000201216d1c0673d0294485b433f9cf78a5d2 else (if i < 62 then
  0x16d1cfe728e013005b473f9ca00241216d1cfe615e287485b473f9857881c016d1cfe6150284485b473f9803820d216d1cfe6000080485b473d9cf78a5d2 else
  0x16d1cfe73dea97485b473f9cf79a5fa16d1cfe73de2b75c5b473f9cf78a5d216d1cfe73de217005b473f9cf40a51216d1cfe73d0214005b473f9ca3824d2)) else (if i < 65 then (if i < 64 then
  0x17f1cffec2e08b485fc703f803928ff17f1c0fe0004a0fc5fc703f8000201217f0c0fe00f5e3fc5b473f9fffaa7d216d1cfe7ffe29f485b473f9cf7cf5d2 else
  0x1a13007000000000680c01c004784b917f1cfffffeebffc5fc73fffff8a7d217f1cfff3de6b7fc5fc73ffcf79a5fa17f1cfff3de2b75c5fc73ffcf78a5d2) else (if i < 66 then
  0x1a13e071bc20c000684c7fc00128db01a1303f1bc22c36c684c0fc4b0890991a1303f090028348684c0fc000080901a1300712c224264684c01c00008090 else
  0x1af303f091d6a7486bcc0fc005589901ae31ff0015e36c06b8c0fc2477adfb1a13e3f1bc22c240684f8fc4b0890901a13e3f090028240684f81c6f08b099)))) else (if i < 74 then (if i < 70 then (if i < 68 then
  0x1e1f00712c2a52e4787c01c004784b01bf3fff1fee3e6406fcf8fc34a0e0901bf31ff0004226406fcc71c5bb8db9d1bf303f0000202406c4c7fc00008090 else (if i < 69 then
  0x1e1f03f12d3e52e4787c0fc004784b01e1f0071bdbed3ec787c01c5befd6bd1e1f00712d3e52e4787c01c4b4f94b01e1f00712d3c50a4787c01c4b4d9099 else
  0x1f1f03f0000202407bfc0fc6f7fbdfb1eff03f0015e36c07bfc01c4b7f9db91e1fe071bd3ed2e4787c7fc00578db01e1f1c712d7e7ef4787c0fc4b5f9dfb)) else (if i < 72 then (if i < 71 then
  0x1f1ffff1fe2bd2c07c7ff1c6f0a34201f1fe3f16e2342407c7f81c5bcfd4b91f1f1ff0000a12c07c7c71c4b4f94b91f1f1c70011e12c07c7c71c00020420 else
  0x1fff1c70015e36c07ffc71c004704201fff1c70011400007ffc0fc004580901fff03f0011400007ffc01c4b4f94b91fff0070011e12c07ffc01c00450000) else (if i < 73 then
  0x1fff1ff0011e12c07ffc7fc004704201fff1ff0011602407ffc7fc00128db01fff1ff0004834807ffc7fc001089901fff1ff0000a12c07ffc71c5bffdfbd else
  0x1fff1ff001de36c07ffc7fc00578fb41fff1ff0015e37c87ffc7fc00578db91fff1ff0015e36c07ffc7fc00570d201fff1ff0015626407ffc7fc00550900))) else (if i < 77 then (if i < 75 then
  0x1fff1ff12d7e76c07ffc7fc34f7eff61fff1ff091deb7c87ffc7fc2477adb01fff1ff0915eb7c87ffc7fc10f7cfb41fff1ff043df36c07ffc7fc10d7cfb4 else (if i < 76 then
  0x1fffe071ffbdd0a47fff81c7fedf0991fffe071ffb5c0247fff81c7fed70001fff1ff1fffffffc7ffc7fc6f7fbdfb1fff1ff16fff7ef47ffc7fc4b5f9db9 else
  0x1ffffc71fffffef47ffff1c7fef74201ffffc71ffb5c0007fff8fc7ffffdfb1fffe3f1ffb7c2407fff8fc7fed70001fffe071ffbfd2e47fff81c7feff4b0)) else (if i < 79 then (if i < 78 then
  0x1ffffff1ff7ff6c07fffffc6f5fbdb01ffffff16f7f76c07fffffc4b5f9db01ffffff0d3dfb6c07fffffc2457adb01ffffff0435f36c07fffffc00578db0 else
  0x28003000000020147fffffc7fffffb41ffffff1fffff7c87fffffc7ffffdb91ffffff1fffff6c07fffffc7fff7d201ffffff1fff7e6407fffffc7feff4b0) else (if i < 80 then
  0x2801300015020400a004c000000000028003f01fffb7f14a000c0030865a0528003000c2000800a000c000544d9052800300000116014a000c0000045000 else
  0x28013f80d7e20f00a004fc07ffa87c028013f01ff0a1c00a004fc07fc0870028013f00d7e20f00a004fc035c0830028013f00c2000800a004fc005408100))))) else (if i < 94 then (if i < 87 then (if i < 84 then (if i < 82 then
  0x28913f8615e22714a244fe1857881c028913f06d7e22f14a244fc1b5c08b052891308600000000a244c01854089052891300600002014a240c0180047817 else (if i < 83 then
  0x2921309800000000a480fe630b80ac529203f18d7e22f14a480c0630800a0529203018001560b4a480c060000080528913f86d7e20f00a244fe1b5c08300 else
  0x29b1301ed7022c14a6c0fe7b5f88bc529b03f9ec2e02b14a6c0c27b0b80ac529213f98d7e20f00a484fe635c0830029213f98c2e00b00a484fc635c08b05)) else (if i < 85 then
  0x29b13f9e00002014a6c4fc7b5f88bc529b13f1ed7022c14a6c4c27b0800a0529b1309e15e22714a6c4c278540890529b1309e00e02314a6c4c2780000805 else (if i < 86 then
  0x29b13f9ed7020c00a6c4fe7b0b80ac529b13f9ec2e00b00a6c4fe7b0800a0529b13f9e15e22714a6c4fe7857881c029b13f9e15022414a6c4fe7803808c5 else
  0x29b13f9fffe23f14a6c4fe7b5fcdbc529b13f9ed7ea2f14a6c4fe7b5f98bed29b13f9ed7e2af5ca6c4fe7b5f88bc529b13f9ed7e20f00a6c4fe7b5c08b05))) else (if i < 90 then (if i < 88 then
  0x2e01ff013d021400b807fc035c4d3002e01ff00d7020c00b807c000544d1002e01f00000114000b807c00000000002e00f0000011e05ca6c4fe7fffa8fc5 else (if i < 89 then
  0x2e91f0061513e45cba47c018544f1122e91f00615136414ba47c018540a9172e91f0060011e05cb807fc07fc6d7002e01ff01ff021c00b807fc04f44d500 else
  0x2fb1f01e1517e4fcba47fe1857cf9d72e91ff07fffbff5cba47fc1cf44fd172e91ff06d713ec5cba47c01cf46fd172e91f006d71bec5cba47c01857cf9d7)) else (if i < 92 then (if i < 91 then
  0x2fb1ff9f3d023414bec7fe7b5fcfbd72fb1ff9ed7f36f14bec7fe7b5f8abd72fb1ff9ed7e22f14bec7c278544f9172fb1f09e0011e05cbec7c2780000805 else
  0x39f130fe0004a0fce7c4c3f8000080539f030fe00f5e3fce104ff87ff887c038413f60d7068ce8e100ff84a3c5cc52fb1ff9ffffbff5cbec7fe7fff88fc5) else (if i < 93 then
  0x39f13fffffeebffce7c4ffffff88fc539f13fff28e03314e7c4fffb5f9abff39f13ffed7e62fb4e7c4fffb5f8abd739f13ffed7e22f14e7c4c3f803928ff else
  0x3ed1ffe73df3d748fb47ff9cf78add73ed1ffe73de29748fb47ff9b5c0a3123ed1f0e61513e45cfb47c39800478173ed1f0e600008048fb47c198545f93f)))) else (if i < 101 then (if i < 97 then (if i < 95 then
  0x3ff1f0fe0015e0fcffc7c3f800028173f61fff9ffe21f00fd87c3e057dd1e83f60f079ea00b85cfb47ff9fffeffd73ed1ffe7ffe29f48fb47ff9cf7cfdd7 else (if i < 96 then
  0x3ff1ffff3df7f7fcffc7fffcf78add73ff1ffff3de29748ffc7fffb5fdfbff3ff1fffed7e2af5cffc7fffb5f88bc53ff1fffe15e2a75cffc7c3f857df9ff else
  0x3ff1fffffff3ff5cffc7ffffffaafd73ff1ffffffe6bffcffc7ffffff8afd73ff1ffffffe29f48ffc7ffffff88fc53ff1ffffff02bc5cffc7ffffab82ed7)) else (if i < 99 then (if i < 98 then
  0xc00e0000c21d48a3003800030820200c00e0000001d40a3003800000065000c00e0000001540a3003800000030028c00e000000000000ffc7fffffffffff else
  0xc00e0f01ffea1f0300383c07fc28700c00e0f01eae81b0300383c07a820600c00e0f012800100300383c030800200c00e0001281d50a300380004a020400) else (if i < 100 then
  0xc12e0018001d60b704b800600010028c09f0f87ffea1f03027c3e1857fd1e8c09e0f07ea08b85f003c3c07fc28700c00e0f81eae81b0300383c07fffd7e8 else
  0xc12e0f99eae81b0304b83e67a820600c12e0f98c2ec0ba304b83e630b802c0c12e0f19eaec1ba304b83c67a830628c12e00980000000304b800630830228))) else (if i < 104 then (if i < 102 then
  0xc60fcf013d1b5403183f3c04f408500c60fc00000000003183b3c07fc6d700c60ecf01ea195803183b0004a065400c60ec000001dc0eb183b00000045000 else (if i < 103 then
  0xd04e0061280c10a341380180007703ad04e0060000400a31eff3e7fffa87c0c7bfc01ed70e8ceb1efb027ca3e5cc5c60fcf01ff0a1c03183f3c07a820600 else
  0xd16e0079ea0c18a341383f87aba06c0d04e0fe1ea08180341383f84a3b04e8d04e0fe128e0130341383d87abb06e8d04e0f61ea0c18a3413803800000000)) else (if i < 106 then (if i < 105 then
  0xd16e0f79eaec1ba345b83de7a830628d16e00f928ec13a345b803e4a030428d16e00f8c2ec0ba345b803e30830228d16e00f800e403a345b803e00010028 else
  0xd16e0ff928e0130345b83fe4a010428d16e0ff8c2ec0ba345b83fe30b902e8d16e0ff8c2e00b0345b83fe30810228d16e0ff800e403a345b83fe00010028) else (if i < 107 then
  0xd16e0ff9eae81b0345b83fe7ab906e8d16e0ff9eae01b0345b83fe7a830628d16e0ff9ea08180345b83fe7a810628d16e0ff928ec13a345b83fe4a3904e8 else
  0xd1fe00fe0004a0ff45bc3fe7ffb87e8d16f0ff9eaec1ba345b83fe7ffb87e8d16e0ff9eafd5ba345b83fe7abb26fad16e0ff9eaec3bb745b83fe7abb06e8))))))) else (if i < 162 then (if i < 135 then (if i < 121 then (if i < 114 then (if i < 111 then (if i < 109 then
  0xd1ff00fe000400a347f83fffffbafffd1fe0fffeaecbbff47f83fffabb26fad1fe0fffeaec3bb747f83fffabb06e8d1fe00fe00fde3ff47f803f803928ff else (if i < 110 then
  0xd64ec061281d50a3593b0184a067412d64ec0612815d0eb593b0184a03243ad64ec0600015c0eb47fc3fffffb87e8d1ff0fffeaec1ba347fc3ff857981e8 else
  0xd64fcf613d1fd4eb593b3f84a3f74fad64ecf61ffffdfeb593b3d87a87763ad64ec061ea1dd8eb593b0184f47f53ad64ec06128fdd3eb593b0184a07743a)) else (if i < 112 then
  0xd6dfcfe73df7d7eb5b7f3f9cf7ba5fad6dfcfe73dea974b5b7f3f9cf78a5d2d6dfc0e7281dd0eb5b7f0398005703ad6dfc0e60000804b5b7b019ca077c3f else (if i < 113 then
  0xd76ec0f9281dd0eb5dbb03e0005703ad76ec079281df0ff5b7f3f9fffff7fad6dfcfe7ffea9f4b5b7f3f9fa822612d6dfcfe73dffd7eb5b7f3f9cf7ef5d2 else
  0xd76fcff9eaec1ba35dbf3fe4f418528d76fc0f8000400a35dbb3fe7ffff7fad76ecff9eafddbeb5dbb3fe7abf56e8d76ecff9eaec9beb5dbb3fe7abb06e8))) else (if i < 117 then (if i < 115 then
  0xd7ffcfff28e493eb5fff3ffb5f9a3fad7ffc0fe000480eb5ffb3ffffffffffd7fecfffeafdfbff5ffb03fca3f7cffd7fec0fe0015e0ff5dbf3fe7ffb87e8 else (if i < 116 then
  0xd7ffcfffffea9f4b5fff3fffff9a7fad7ffcfffff0e9ceb5fff3fffabb26fad7ffcfffeaec1ba35fff3ffcf7ffdffd7ffcfff3de697eb5fff3ffcf78a5d2 else
  0xe000000e0000093f800000380000246e000000e0000083780000038000004bd7ffcfffffffdfeb5fff3fffffbafffd7ffcfffffee9feb5fff3fffffb87e8)) else (if i < 119 then (if i < 118 then
  0xe0001f8e00402d1b800070380120f6fe0001c0e0000081380000e380108bdfe000038e0000010b8000003cb08124fe000000e9080893f800000390a0424f else
  0xe000e00fbc20c12f8003803db88520de000e00f2c2040278003803b4a06246e000e00e9000810b8003803a4002000e000e00e42010813800380380000000) else (if i < 120 then
  0xe000e38ed281891b80038e3a4002042e000e38e000000038003803ffa8724fe000e00ffea1c91b8003803ffa8720de000e00ffea1c12f8003803ff88724f else
  0xe010e38fbc20c10b8043803cb081000e000ff8ed2c1ad1b8003fe3a4102b46e000fc0ffee9fdbf80038e3ffb8fbdfe000e38ffea1c93f80038e3ef08304b)))) else (if i < 128 then (if i < 124 then (if i < 122 then
  0xe100e38ed201810b840380390804000e0e0ff8ed2c1ad1b8383fe3a4302b46e0e0e38ed2c1ad1b83838e3a4302942e0e0e00ffff5ed3f83807e3a4302b46 else (if i < 123 then
  0xe100ff8e42412d1b8403fe390804204e100fc0ffea1c93f8403f03db88520de100fc0ed281891b8403f03b4806204e100fc0e420108138403f0380000000 else
  0xe1e0e00ffea1c93f8783803b4a06246e1e0e00ed281800387807e390b04b46e1e01f8e00402d1b8443f03db885204e100ff8ed201891b8403fe3a4002042)) else (if i < 126 then (if i < 125 then
  0xe1e0ff8e420108138783fe380100900e1e0fc0ed2c1ad1b8783f03b4a06204e1e0fc0e42c12c138783f0390804204e1e0e38ed281810b87838e3a4002042 else
  0xe1e0ff8e9040a50b8783fe3a4102900e1e0ff8e9000810b8783fe390b04b46e1e0ff8e42c12c138783fe390904b46e1e0ff8e42412c138783fe390904900) else (if i < 127 then
  0xe1e0ff8ed28188138783fe3b4a06042e1e0ff8ed241ad1b8783fe3b4906b04e1e0ff8ed241a50b8783fe3b4806246e1e0ff8e90c0a50b8783fe3a4102b46 else
  0xe1e0ff8ed2c9bd9b8783fe3b4b0ebd6e1e0ff8ed2c1ad3f8783fe3b4b06b46e1e0ff8ed2c1ac138783fe3b4b06942e1e0ff8ed2c1a4038783fe3b4a06246))) else (if i < 131 then (if i < 129 then
  0xe50cfc0e4209189390338e3a4472462e40ce00fffbdd9bf87c3fe3ffb87b46e1f0ff8ed2c1ad1b8783fe3ffb87b4fe1e0ff8ffee1ed1b8783fe3b4f56b46 else (if i < 130 then
  0xe5ec1c0e43dd3dbf9473f03db885204e51cfc0e4201081394738e3ff887042e51ce00ffea1c93f9473803db88520de51ce00f6e2140039433f03db8a562d else
  0xe5fcff8ed2c1ad1b97b3fe3ffff7f6fe5ecff8ed3ddbd9b97b3fe3b4f56b46e5ecff8ed2c9bd9b97b3fe3b4b06b46e5ecfc0ffffdfdbf97b3f0390f74f24)) else (if i < 133 then (if i < 132 then
  0xe80f3f00d7020c03a03cc0000000000e80e3f01ff1b5c03a038fc07a865600e80e3000c2194803a038c000007582de80e30000011400397f3fe3ffb87b46 else
  0xe92e3018c21d48a3a4b8c0630865a05e92e3018c21568b7a4b8c0630830a2de92e3018001560b7a03cfc07fc28700e80f3f01ea081803a03cfc035c6d300) else (if i < 134 then
  0xe92f3f18d71f6cb7a4b8fe630bf5aede92e3f19ffff7fb7a4b8fc67a875e2de92e3019ea1d78b7a4b8c0635c7db2de92e3018c2fd6bb7a4b8c0630875a2d else
  0xe9bf3f9ed7f76fb7a6fcfe7b5fb8bede9bf3f9ed7ea2f17a6fcfe7b5f88bc5e9bf309ec21d68b7a6fcc278005582de9bf309e00002017a6f8c07b0877a3f))))) else (if i < 148 then (if i < 141 then (if i < 138 then (if i < 136 then
  0xea03e38fbc22c36fa80f8e3a400a0d2ea03e00fffb7cb7fa6fcfe7ffffdfede9bf3f9fffea3f17a6fcfe7fa820e05e9bf3f9ed7ff6fb7a6fcfe7b5fedbc5 else (if i < 137 then
  0xeae3e38ffff7ef7fab8f8e3a475a9d2eae3038e91d6af7fa84f8e3ef083042ea13e38e9000810ba84f803ffa8724fea13e00fbc20c12fa84f803ef083000 else
  0xebf3ff8ed2c1ad1baf8ffe3fffdfbdfebe3ff8ed3d7af5baf8ffe3b4f56b46ebe3ff8ed2c3af5baf8ffe3b4b06b46eb13fc0ffe21c813ac0ff0390c5c294)) else (if i < 139 then
  0xee0ff000d71b4c03b83fc0030865200ee0ff00015134403b83fc0000045000ee0eff01ff1b5c03b83bfc07a865600ee0ef001ea195803afcffe3ffb87b46 else (if i < 140 then
  0xee0fff00d71b4c03b83ffc035c4d300ee0fff00d7020c03b83ffc030845200ee0fff0015134403b83ffc000045000ee0ff0013d1b5403b83fc004a065400 else
  0xee0fff01ff021c03b83ffc07a865600ee0fff01ea115803b83ffc07a820600ee0fff013d1b5403b83ffc04f44d500ee0fff013d021403b83ffc04a045400))) else (if i < 144 then (if i < 142 then
  0xee0fff81ff1b5c03b83ffc07ffed7c0ee0fff01ff1f5ca3b83ffc07fc6f712ee0fff01ff1b7c17b83ffc07fc6d700ee0fff01ff135c03b83ffc07fc28700 else (if i < 143 then
  0xee9fff07ff1bdc4bba7ffc1ffc6df05ee9fff07ff1b5c03ba7fc2180045000ee9ff006151fe4ffba7fc018544f917ee9ff0060011e05fb83ffe07ffed7c0 else
  0xef2ff018001560b7bcbbc0630877a3fef1fff8ffe21c91bba7ffe1fffed7c0ee9fff87ff1b5c03ba7ffe1857cd1c0ee9fff07fffbff5fba7ffc1ffc6ff17)) else (if i < 146 then (if i < 145 then
  0xef2fff98c2f14b03bcbffc67fffdfedef2fff19ff1f7cb7bcbffc67fc7d728ef2fff19ff1b7c17bcbffc67fc6d700ef2ff09800114003bcbfc0630875a2d else
  0xefbfff9ed7136c17befffc7ffffffffefbfff1fff1ffcffbeffc2780045805efbff01ed71fecffbeffc078005783fef2fff99fffb5f03bcbffe67fc6d700) else (if i < 147 then
  0xefbfff9fffea3f17befffe7ffc6df05efbfff9fff1b5c03befffe7fabe5ec5efbfff9f3df37717befffe7b5fffbffefbfff9ed7f36f17befffe7b5f88bc5 else
  0xefff000e0114093fbfbffe3ffffffffefefff8ed3dfbfdbbefffe7ffffdfedefbfff9ffffbff5fbefffe7fffedfc5efbfff9ffffb5f03befffe7fffcdfc5)))) else (if i < 155 then (if i < 151 then (if i < 149 then
  0xefffe00fffb5c12fbfff803ffed7042efffe00fffb5c027bfff803ffed7000efffe00fbd34c12fbfff803dbcd520defffe00ed395891bbfff80380450000 else (if i < 150 then
  0xefffe38fbd34c10bbfff8e3dbcd5000efffe38ed395810bbfff8e3a4452042efffe00fffb5c93fbfff803ffed7246efffe00fffb5c837bfff803ffed7204 else
  0xeffffc0e43150813bfff8e3fffdfbdfefffe38fffb5c93fbfff8e3ffed7246efffe38fffb5c12fbfff8e3ffed7042efffe38fffb5c003bfff8e3ffcd7042)) else (if i < 153 then (if i < 152 then
  0xeffffc0fffb5c91bbffff03ffed720deffffc0fffb5c813bffff03ffed7000effffc0fff35c813bffff03ef4d3000effffc0f6f354813bffff03b4e56204 else
  0xefffff8ffee1ed1bbffffe3ef5d3942efffff8f6f756c13bffffe3b4f56b46efffff8ed315891bbffffe3b4b06b46effffc0ffffdfdbfbffff03ffed724f) else (if i < 154 then
  0xefffff8ffff7ef5bbffffe3fffd7b4fefffff8ffff5ed1bbffffe3fffd7b04efffff8ffff5e50bbffffe3ffed7246efffff8fffb5c813bffffe3ffed7042 else
  0xf0001ffe00483dbfc0007ff80108bdff0001ffe000a1bffc00071f8002062df00003fe0002036fc00001f800286fff000007e00000027bffffe3ffff7f66))) else (if i < 158 then (if i < 156 then
  0xf000e07ffeabdbffc0007ffcb1a9ffff0001ffe90cabfffc0007ff90b2cffff0001ffe004a3fffc0007ff80128ff6f0001ffe004a3ef7c0007ff80128dfb else (if i < 157 then
  0xf010e07f6e214837c04381fcb081009f010e07e00000003c003fffffbafffff000fffe904abfffc003f1fdb8a562df000e3ffbc22c36fc0038ffa400a0db else
  0xf010fc7f2c2858b7c0438ffef08304bf010e3ff2c22436fc0438ffcb081009f010e3fe9000810bc04381fffa8724ff010e07fbc20c12fc04381fef083009)) else (if i < 160 then (if i < 159 then
  0xf110fc7f2c204027c443f1f90804204f110e07f6e214027c403fff9092cffff100fc7e420918b7c3c381fcb7d1909f0e01ffe01de3fffc043fffcb1a9fff else
  0xf1f0e07ffea1c027c783fffffbafffff1e0fffed2cbbfffc783fffb4b2eff6f1e0fffed2c9bdbfc783fffb4b0ebdff1e01ffe004a3fffc443f1fdb88520d) else (if i < 161 then
  0xf41cfc7f2c2858b7d07381fdb8a562df41ce07f2c2850a7d07071fcb0a162df40c1ffe015e3fffc7c3fffffb87b4ff1f0ffff2c606427c7c3fffb4b06b46 else
  0xf51ce07f6e214027d47381fcb081009f51c1ffe004a3fffd47071f8002062df50cfc7f6e2958b7d433f1f9082462df50c1c7e420918b7d073f1fdb8a562d)))))) else (if i < 189 then (if i < 175 then (if i < 168 then (if i < 165 then (if i < 163 then
  0xf51cfc7f2c2850a7d473f1fcb0a1420f51cfc7f2c204027d473f1f9082462df51cfc7e42091893d473f1f90824420f51cfc7e42010813d473f1f80020420 else (if i < 164 then
  0xf51cfc7f6e2958b7d473f1fdb8a5624f51cfc7f6e2950a7d473f1fdb8a5420f51cfc7f6e214837d473f1fdb885204f51cfc7f6e214027d473f1fcb0a162d else
  0xf51cfc7ffea9d8b7d473f1fff8a766ff51cfc7ffe29d8b7d473f1fdbcf562df51cfc7f6ea958b7d473f1fdb9a5f2df51cfc7f6e2b5af7d473f1fdb8a566f)) else (if i < 166 then
  0xf51cfffffe29d9bfd473fffdb9adffff51cffff6e6b7ef7d473fffdb9a5f6ff51cffff6e2b5bffd473fffdb8a562df51cfffe9008918bd473f1fffaa766f else (if i < 167 then
  0xf5fcfc7f6ee97cb7d7f3f1fdbaa562df5fcfc7f6e2958b7d7f38ffffa8704bf5ecffffffffffffd7b3fffb4f7effff5ec1ffe43df3fffd473fffffbaffff else
  0xf5fcfffed2c9bd9bd7f3fffb4b06b46f5fcfffe42493c93d7f3f1fffff7f6ff5fcfc7ffea9d8b7d7f3f1fdbff5f2df5fcfc7f6fbd58b7d7f3f1fdbdf5f2d))) else (if i < 171 then (if i < 169 then
  0xf5fcfffffee9fcb7d7f3fffffb87b4ff5fcfffffea9d9bfd7f3fffff9a7f6ff5fcffffbc68f5afd7f3fffdbffdffff5fcffff6e697cb7d7f3fffdb8a562d else (if i < 170 then
  0xf96e3078c21de8ffe37cff9fffa87c0f8df30673d0e34b7e378c39b0be72d2f5fcfffffffdfdbfd7f3fffffbafffff5fcfffffee9fdbfd7f3fffffba7f66 else
  0xf96f30f8000400a3e5b8ffe7fffdfedf96e3ff9eafd7bb7e5b8ffe7abf56e8f96e3ff9eaec3bb7e5b8ffe7abb06e8f96e30f8c21d68b7e5b8c3e0005582d)) else (if i < 173 then (if i < 172 then
  0xf9ff30fe000420b7e7f8ffffffffffff9fe3fffeafdfbffe7f8c3fb0bf7afff9fe30fe0015e0ffe5bcffe7ffb87e8f96f3ff9eaec1ba3e5bcffe35c18328 else
  0xf9ff3fffff0e3cb7e7fcffffabb0eedf9ff3fffeaec1ba3e7fcfffcf798dedf9ff3ffed7ffefffe7fcfffb5f98bedf9ff3ffed7e22f17e7fcfffb0b90aed) else (if i < 174 then
  0xfa031ffe015e3fffe80c0ffa400a0dbf9ff3fffffff7fb7e7fcffffffbaffff9ff3fffffee3fb7e7fcffffffb87e8f9ff3fffffea3f17e7fcffffff98fed else
  0xfa13e07fbc20c027e84f81fcb089099fa13e07f2c204027e84c7ff80128ffffa1303ff2c22436fe84c0ff800080dbfa03e3ffbc22c36fe80f8ffa400a0db)))) else (if i < 182 then (if i < 178 then (if i < 176 then
  0xfa13e3ff2c224243e84f8ffcb081009fa13e3fe9002836fe84f8ffa400a0d2fa13e3fe90028243e84f8ffa4002042fa13e3fe00020243e84f81fef08b0db else (if i < 177 then
  0xfa13e3ffbc22c34be84f8ffef08b099fa13e3ffbc22c243e84f8ffef08304bfa13e3ffbc20c10be84f8ffef083009fa13e3ff2c22436fe84f8ffcb089099 else
  0xfa13e3fffea3c36fe84f8ffff88f2dffa13e3ffbd36c36fe84f8ffef28b0dbfa13e3ffbc62e76fe84f8ffef0ab4fbfa13e3ffbc22cb7fe84f8ffef08b0db)) else (if i < 180 then (if i < 179 then
  0xfae3ffffffffffffeb8c7ffa477affffa13fffffeebffffe84ffffef1abffffa13ffffbc6af7efe84ffffef18bbdffa13ffffbc2adbffe84f8ffffa8f2df else
  0xfb13e3ffbc22c36febcffffef7fbffffaf3e3fffff7ef7febcf8ffef7db9dbfaf3e3ffbdb6c36febcf8ffef5db9dbfaf3e3ffbce2e76febcf8ffef28b0db) else (if i < 181 then
  0xfbf3fc7ffea1c837efcf8ffffa8f0dbfbf3e3ffbc22c36fef8ffffb4f7effffb13fffffe23cb7fec4ffffef08b0dbfb13fffe42030a53ec4f8ffff88f0db else
  0xfbf3fffffea3cb7fefcffffff98fbdffbf3ffffbc62e76fefcffffef08b0dbfbf3ffff6e636e77efcffffb4b0ebd6fbf3fffed2c1ad1befcffffa410a9d2))) else (if i < 185 then (if i < 183 then
  0xfe1f1fff2d7e7ffff87c01fcb4f96fffbf3fffffff7ef7fefcffffffbafffffbf3fffffee3ef7fefcffffffb8fbd6fbf3fffffee3e76fefcffffffb87b4f else (if i < 184 then
  0xfe1fffffbd7efffff87f8ffffeff6fffe1fe3ffbd3ed3eff87f8ffef4db0dbfe1fe3ffbc2ad3eff87f8ffef08b0dbfe1fe07fffbfdbfff87f81fcb4f94b9 else
  0xfe4fff61ff1f5ca3f93ffd87fc6f712fe4fff61ff1b5c03f93fc3800045000fe4ff061281dd0ebf93fc180005703afe4ef061281df0fff87ffffffffffff)) else (if i < 187 then (if i < 186 then
  0xfedff0e60011c04bfb7fc19cf47fd3ffedff0660015e0fff93fff87ffed7c0fe4fffe1ff1b5c03f93fff84a3c54c0fe4fff61ffffdfebf93ffd87fc7f73a else
  0xfedfffe7eaf9db4bfb7fff9cf7ffdfffedfffe73df3d74bfb7fff9cf78a5d2fedfffe73d13d44bfb7fff9b5fcf3d2fedfff67fffffffffb7ffd9ffc7ff3f) else (if i < 188 then
  0xfedfffe7ffffdfebfb7fff9fffeffd7fedfffe7fffbdf4bfb7fff9fffed7c0fedfffe7fff3df4bfb7fff9fffaa7d2fedfffe7ff1bdc4bfb7fff9ffc6d700 else
  0xff1ffc7f6f3d58b7fc7ff1fdb8ad6bdff1ffc7f6e2958b7fc7f8ffff88f0dbff1fe3ffbc22c36ffbff8fffffffffffeffe3ffbdfef7effbfc7ffef7fbfff))))) else (if i < 202 then (if i < 195 then (if i < 192 then (if i < 190 then
  0xff1fffff6f7f7ffffc7ffffdb8ad6bdff1fffff6e2958b7fc7ffffcb0a94b9ff1ffffed20b9bdbfc7ff1fffeff6ffff1ffc7ffe29d8b7fc7ff1fdbcfd6bd else (if i < 191 then
  0xff1ffffffe6bfffffc7ffffff8af6ffff1ffffffe2bdaf7fc7ffffff8af4fbff1ffffffe29d9bffc7ffffff88f2dfff1fffffbc2ad3effc7ffffef08b0db else
  0xff6fff79ff1ffcfffdbfc3e00055028ff6efff9eafdfbfffdbbfde7fffffffff6ef079ea1df8fffdbbc1e0005783fff1fffffff3fdbfffc7ffffffaaf6ff)) else (if i < 193 then
  0xff6ffff9ffee1fa3fdbfffe7fc7d728ff6ffff9ff1b5c03fdbfffe7abf56e8ff6ffff9eaec1ba3fdbfffe7a875628ff6ffff93df757a3fdbfffe35fdd3e8 else (if i < 194 then
  0xffff1ffe015e3ef7fffc7ff80578dfbfffef0ffeafdfbffffbc7ffb4f7efffff6ffff9ffffdfebfdbfffe7fffdfedff6ffff9ffff5fa3fdbfffe7ffed7c0 else
  0xffffe07f2d344027ffff81fb4e56000ffff1fff6fff7ffffffc7ffcb5f9fffffff1ffe91debffffffc7ff90f7cfffffff1ffe015e3ffffffc7ff80578ff6))) else (if i < 198 then (if i < 196 then
  0xffffe07fffbfdbffffff81fffed724fffffe07fffb5c837ffff81fffed704bffffe07fffb5c027ffff81fffed7000ffffe07fbd34c027ffff81fdbcd5009 else (if i < 197 then
  0xffffe3ffffb5c027ffff8ffffcdf0dbffffe3fffea3c36fffff8ffef4db0dbffffe3ffbd34c12fffff8ffef08b0dbffffe3ff6f374267ffff8ffb4e5e0d2 else
  0xffffe3fffff7e76fffff8ffffeff4fbffffe3ffffb7cb7fffff8ffffedf0dbffffe3ffffb7c34bffff8ffffedf099ffffe3ffffb5c12fffff8ffffed7042)) else (if i < 200 then (if i < 199 then
  0xfffff0fe0011e05fffffc3f80047012fffff0fe00116017ffffc3f8001283ffffff0fe000480ebffffc3f8001082dfffff0fe0000a05fffffc1fffc7ff3f else
  0xfffff0fe15f7e7ffffffc3f8545f93ffffff0fe00f5e3ffffffc3f8007783ffffff0fe0015e0ffffffc3f8005703afffff0fe001560b7ffffc3f80055028) else (if i < 201 then
  0xfffff0ff28fdf3ffffffc3fca077c3ffffff0ff2815f0ffffffc3fb5fffbfffffff0fed71fecffffffc3fb0bf7afffffff0fec21de8ffffffc3fb0857a3f else
  0xfffffc7f6fff7ef7fffff1fdbcf562dfffffc7f6f354837fffff1fdb8a562dfffffc7ed39d9893ffffc3ffa877e3ffffff0ff3dfff7ffffffc3fcf47fd3f)))) else (if i < 209 then (if i < 205 then (if i < 203 then
  0xfffffc7fffbdd893fffff1fffef7429fffffc7fffb5c837fffff1fffed7204fffffc7fffb5c027fffff1fffcf762dfffffc7ffea9d8b7fffff1fef4f3429 else (if i < 204 then
  0xfffffffe015e36c3fffffff803d78fffffffffe0015e0fffffff1ffffffffffffffc7ffffdfcb7fffff1fffeff6bdfffffc7fffbdd9bffffff1fffef762d else
  0xfffffffed35fbfdbfffffffb4b2eff6fffffffec2f5ebfffffffffb0857a3ffffffffe915eb7cbfffffff90d7cfb4fffffffe15f7e7fffffffff8545f93f)) else (if i < 207 then (if i < 206 then
  0xfffffffed7e6affffffffffb5c5fb3ffffffffed3dfbffffffffffb4f7eff6fffffffed3dfbed3fffffffb4f7edf2fffffffed3ddbd9bfffffffb4f5ebd6 else
  0xffffffff3d17f4fffffffffcb5f9db9ffffffff28f5f3fffffffffca057c3ffffffffed7ffeffffffffffb5fdfbfffffffffed7f76fb7fffffffb5fcfbd7) else (if i < 208 then
  0xffffffff6f7d7cb7fffffffdbcfd6bdffffffff6e6b7ef7fffffffcf7ffdffffffffff3df7f7fffffffffcf7df5faffffffff3df3f75ffffffffcf79adff else
  0xffffffffbd76e76ffffffffef4fb4fbffffffffbc6af7effffffffdbffdfbdffffffff6f7f7ffffffffffdbdfdfbdffffffff6f7f7ed3fffffffdbdfddb9))) else (if i < 212 then (if i < 210 then
  0xffffffffeaf5fbffffffffffabb2effffffffffea1df8fffffffffef7fbdfbffffffffbd7efffffffffffef5fbdfbffffffffbd7ef7cbfffffffef5fbdb9 else (if i < 211 then
  0xfffffffffeebfffffffffffffba7f6ffffffffffee3ef7ffffffffffaaf6fffffffffffe6bffffffffffffabf7effffffffffeafddbebffffffffabf5eed else
  0xffffffffff7ffef7fffffffffdffdfbffffffffff3fdbfffffffffffc7ff3fffffffffff1fdcebfffffffffc7df2dffffffffff1bfc5ffffffffffc5ff3f)) else (if i < 214 then (if i < 213 then
  0xffffffffffeabf5fffffffffff9afffffffffffffbfdbfffffffffffeff6bdffffffffffbfd3effffffffffef766fffffffffffb7cb7ffffffffffdfffff else
  0xfffffffffff7ef7fffffffffffdfbd6fffffffffff7e76fffffffffffd7b4ffffffffffff3ff5fffffffffffbafffffffffffffee9febffffffffffb8fed) else (if i < 215 then
  0xffffffffffff5fa3fffffffffff7f6ffffffffffffdfd9bfffffffffff7f2dfffffffffffbff5fffffffffffef7d2fffffffffffb7f17ffffffffffdffff else
  0xffffffffffffffdbfffffffffffffbdfffffffffffffed3ffffffffffffdfbfffffffffffff7cbffffffffffffdb9ffffffffffffdfebfffffffffffdfed))))))))

private def wireData (i : Nat) : Nat := unpack wireDataPacked 62 8 i

private def readSig (i : Nat) : Sig :=
  let a := wireData i
  (BitVec.ofNat 31 (a >>> 31), BitVec.ofNat 31 a)

private def sigHash (s : Sig) : Nat :=
  let h := (s.1.toNat * 0x517cc1b727220a95) ^^^ (s.2.toNat * 0x9e3779b97f4a7c15)
  let g := (h ^^^ (h >>> 57)) * 0xbf58476d1ce4e5b9
  (g ^^^ (g >>> 49)) &&& 0xffffffffffffffff

private def stateHash (s : SearchState) : Nat :=
  s.2.foldl (fun acc x => acc + sigHash x) (s.1 * 0x94d049bb133111eb)


private def decodeWires (code : Nat) : Nat → List Sig
  | 0 => []
  | n+1 => readSig (code &&& 2047) :: decodeWires (code >>> 11) n


private def st3Packed (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0xb9ed39590e0418e99f2b21c0831db3e56238105cf6b0aa47020c6ed61488e0418edaba911c0831a46a326245063b8d064c48a0c651a8fa0824157e2e1f4104831cc223e8209063b8447cc4120abf1a8f5082418d2351a2104831dc68344209063ba9c3804120c631a9ac0604116dac2f60c082353495ec181063b628bd43020c6ed6160860418edabac10c0831a46a358181063b8d06b03020 else 0x8a8d01591ee417f98a2b23dc822a3585407ad048c6b0a08f5a08d4d01501ea41151a72b23c4823034056478904546b0aa4f1208d4d01541e24116dac2a03c48235349540789063a628ac8eea0c76c51589dd418ce352b2326823039556464d063a662ac8c9a0c76cc558993411a9caaa8326831db3450464d05cf6b0ac878a0abf1a8fa0f0418ddac2821de831db575043bd06366b0ac87020) else (if i < 3 then 0xb951a9caab24173dc735856482353955caac9046a72ab695920b9ed616bab24157e43c6a3e882ac48c6b07d1048c6b0bb0fa20918d616d9f4417fa1d2b23e882ff3825647d105fe636ac8fa20c70c51591f441151a02ac3e882ff3145587d10454694a80fa208b8d01501f4418e58a29b3e8831ab585047d1048c694a08fa20c72c9d411f44157e351ff3e8831db145367cd063b64ea08f9a0 else 0x23d46a6b0bd9046a6d0d617b20))

private def st3 (i : Nat) : Nat := unpack st3Packed 51 24 i

private def st4Packed (i : Nat) : Nat :=
  (if i < 15 then (if i < 7 then (if i < 3 then (if i < 1 then
  0xc771a9ac2f90c0a330c6a6b0bd83028c771a9ac2f60c0a2354546b0bd830288d4d61a02f60c0a31dc6a6b0bd43028c771a9ac2f30c0a359e3b6b0b043028d558ee351ac0c0a31dc6a6b0c102fa8c771a9ac3040bca2ff3145647d02ba8c771f1ac30409ca31dc9a6b0bc42728c77775ac2d809ca31dc6a6d4c101e28c771a9d0ae6078a31dd6b8d48101e28c77731d0ab2064a31dddd720ac81928c77825c1ab2064a31dd5a9347d01728c775ae449f405ca31de098767d01728
  else (if i < 2 then
  0xc771a9b4b040c0a31dc7b6b0c103028c771a9ac3040c0a31bc6a6b0c103028c691a9ac3040c0a31dc696b0c103028c771a1ac3040c0a31dc666b0c103028c77189ac3040c0a31dc5e6b0c103028c7716dac3040c0a31dc6a6aec103028c771a9ab3040c0a31dc6a6a8c103028c771a9a83040c0a31dc6a698c103028c771a9a4b040c0a31de09628c103028c771a9ac3030c0a31dc6a6b0c083028c771a9ac3010c0a31dc6a6b0c003028c771a9ac2fe0c0a31dc6a6b0bec3028
  else
  0xc7753a351f4104a31dd4d8d47d04128c775ae341f4104a31dd6b8cc7d04128c775ae311f4104a31dd6b8bc7d04128c775ae2e1f4104a2afc6a8a87d04128d718ee111f4104a31dd6b8d47cc4128c775ae351f2104a31dd6b8d47c04128c775ae351ed104a31dd6b8d47a84128abf1a8fa1e2104a35563b8d46884128c77776b58e0104a2afc6a3e835c4128c775ae351f4102a31dd6b8d47d04028c775a2351f4100a2e7b585643803ca8d4f8ee353580c0a31dc6a6b0c183028))
  else (if i < 5 then (if i < 4 then
  0xc7776dac2b21bca31dc6a6b0bf848a8c7759a351f4122a31a46a6b07d048a8c771a1ac1f4122a35563b8d464c48a8c775ae351f4120a31dc6a6b0c104728c775ae35200104a31dd6b9107d04128d518ee351f4104a31dd6b8d47d04128c735ae351f4104a31a56b8d47d04128c775aa351f4104a31dd698d47d04128c775a2351f4104a31dd678d47d04128c7759a351f4104a31dd648d47d04128c7758a351f4104a31dd608d47d04128ccb57e351f4104a31dd5f8d47d04128
  else
  0xc7775dac2b21c0a31ddd56b0ac87028c7774dac2b21c0a31ddd26b0ac87028cef73dac2b21c0a31ddcf6b0ac87028c77539ac2b21c0a31dd4c6b0ac87028c77775abab21c0a31dddd6a8ac87028c77775a82b21c0a31dddd69cac87028c77775a62b21c0a2e7b58680ac87028d738ed9f2b21c0a31dddd6b0ac47028c77775ac2b01c0a31dddd6b0ab87028c77775ac2ab1c0a31dddd6b0aa47028b9ed61592a01c0a359e3b6b0a447028c77775ac2b21bea31dddd6b0ac86f28)
  else (if i < 6 then
  0x8d4e5559279326a31dc6a742ac8c928c771a9d0ab2322a31dc6a73cac8c8a8918d61411f4314a31dddd6b0ac878a8c775ae351f41e0a31dc6a6b0bec77a8c77765ac2b21dea31bc6a6b0ac877a8c771a9abab21dea359e3b6b0a0877a8c77775ac2b21dca31dc6a6b0c107628c77775ac2d31c0a31dddd71eac87028d658edac2b21c0a31dddd6b0ac87028c75775ac2b21c0a31bddd6b0ac87028c77771ac2b21c0a31dddb6b0ac87028c77769ac2b21c0a31ddd96b0ac87028
  else
  0xc77189d0ab2326a31dc60742ac8c9a8c77179d0ab2326a31dc6a740ac8c9a8c771a9cfab2326a31dc6a73cac8c9a8c771a9ceab2326a31dc6a738ac8c9a8c771a9ccab2326a31dc6a72eac8c9a8c771a9cb2b2326a33ac6a72aac8c9a8c771a9caab2326a23545472aac8c9a8c771a99a2b2326a31dc6a666ac8c9a8d738ed98ab2326a31dc6a742ac4c9a8c771a9d0ab0326a31dc6a742ab8c9a8c771a9d0aab326a31dc6a742aa0c9a88d4e55592a0326a31dc9a742a08c9a8)))
  else (if i < 11 then (if i < 9 then (if i < 8 then
  0xd738ed8a2b23baa31dc6a6b0ac4eea8c77775ac2b23b8a31dc6a742ac8eda8c771a9ccab2358a31dd628d47d0d628c691a9591f4358a31dc685647d0d628c771a9d0ab2354a31dd6b8d47d0d428c771a9ac2fb344a31dc6a738ac8d128c691a9ac2b2344a31dc686b0ac8d128c771a9d0ab2342a31dc6a6b0c10cfa8c771a9d0ae1326a354e3b8d4ac8c9a8c7772dd0ab2326a31dc6a742ac8c9a8c751a9d0ab2326a31a46a742ac8c9a8c771a1d0ab2326a31dc66742ac8c9a8
  else
  0xc771a9ac2b23d0a31dc6a6b0ac8f3a8c77189ac2b23c4a31dc606b0ac8f128c7716dac2b23c4a33bc546b0ac8f128c771a9a82b23c4a31dc626a0ac8f128c771a9a72b23c4a31dc6a692ac8f128ceb1a9a02b23c4a31dc6a6b0aacf128c77189ac2ab3c4a31dc6a6a0aacf128c771a9ac2a93c4a31dc6a6b0aa0f128cc31a9ac2a03c4a2ff3145647d0f128918d61411f43c4a31dc6a6b0ac8f028c771a9ac2b23bea31dc6a738ac8eea8c77765ac2b23baa31d46a6b0ac8eea8)
  else (if i < 10 then
  0xc771a9a4ab23daa31de09628ac8f6a8c771a9ac2b03daa31dc6a6b0ab8f6a8c771a9ac2ab3daa31dc6a6b0a80f6a8c77179ac2a03daa31dc6a698a80f6a8c77269ac2823daa31dc6a6b0ac8f628c771a9ac2b23d6a31dc5e6b0ac8f5a8c77151ac2b23d6a31dc6a694ac8f5a8c771a9ac2b03d6a31dc6a6b0a80f5a8c77269ac2823d6a31dc6a6b0ac8f528c77171ac2b23d4a31dc6a698ac8f528c771a9a02b23d4a31dc6a6b0ab8f528c771a9ac2a03d4a31dc6a6b0ac8f4a8
  else
  0xc771a9ac2b23dca31dc666b0ac8f728c77151ac2b23dca31dc6a6a8ac8f728c771a9a02b23dca31de09628ac8f728c771a9ac2ac3dca31dc6a876d60f6a8c771a9ac2e63daa31dc6a6b0b84f6a8c771a9ac2d83daa31dc6a6b0b4cf6a8c771a9ac2b83daa31dc6a6b0ac8f6a8c771a5ac2b23daa31dc666b0ac8f6a8c77189ac2b23daa31dc5e6b0ac8f6a8c7716dac2b23daa31dc6a6acac8f6a8c771a9aa2b23daa31dc6a6a0ac8f6a8c771a9a62b23daa31dc5e698ac8f6a8))
  else (if i < 13 then (if i < 12 then
  0xc771a9c82b23e0a31dc6a71eac8f828c771a9b52b23e0a31dc6a6d2ac8f828c771a9ae2b23e0a31dc6a6b0ac8f828c77199ac2b23e0a31dc626b0ac8f828c77181ac2b23e0a31dc5e6b0ac8f828c771a9aa2b23e0a31dc6a6a0ac8f828c771a9a62b23e0a31dc6a680ac8f828c77199a02b23e0a31de09628ac8f828c771a9ac2b03e0a31dc6a6b0ab8f828c77199ac2ae3e0a31dc6a680ab8f828c771a9ac2ab3e0a31dc6a6b0aa0f828c77269ac2823e0a31dc6a6b0ac8f7a8
  else
  0xc77225ac2b23e4a31dc7c6b0ac8f928c771edac2b23e4a31dc6e6b0ac8f928c771a9ac2b23e4a31dc666b0ac8f928c77189ac2b23e4a31dc5e6b0ac8f928c77151ac2b23e4a31dc6a6a8ac8f928c77151aa2b23e4a31dc6a6a0ac8f928c771a9a72b23e4a31dc6a698ac8f928c778258a2b23e4a31dc6a6b0ac0f928c77151ac2b03e4a31dc6a6a8ac0f928c771a9ac2ae3e4a31dc6a6b0aacf928c771a9ac2a93e4a31dc9a6b0a08f928c771a9ac2b23e2a31dd5a8d4ac8f828)
  else (if i < 14 then
  0xcdd231ac2823e8a31dc8c6b0a08fa28c77269aba823e8a31dc9a6a8a08fa28c77269a82823e8a31dc9a698a08fa28c77269a52823e8a246358680a08fa28c76d619a2823e8a31db58664a08fa28d718ed93a823e8a31dc9a6b0a04fa28c77269ac2803e8a31dc986b0a00fa28c775ae351ff3e8a31dc6a6b0ac8f9a8c731a9ac2b23e6a31dc226b0ac8f9a8c771a993ab23e6a31de09628ac8f9a8c771a9ac29b3e6a31dc9a6b0a08f9a8c77731ac2b23e4a31ddcb6b0ac8f928
  else
  0xc771a9ac29d3e8a31dd668d4a6cfa28c77259ac29b3e8a31cc6a6b0a6cfa28d718ed8a29b3e8a31dc9a6b0a68fa28c775ae352993e8a31dc966b0a44fa28c6f1a9ac2913e8a31dc6a6aea44fa28c77269ac2903e8a31dd59934a08fa28d638edac2823e8a31dc9a6b0a08fa28c73269ac2823e8a31bc9a6b0a08fa28c77265ac2823e8a31dc986b0a08fa28c7725dac2823e8a31dc966b0a08fa28c77251ac2823e8a31dc936b0a08fa28c77245ac2823e8a31dc8f6b0a08fa28))))
  else (if i < 22 then (if i < 18 then (if i < 16 then
  0xc778258a2ab3e8a31dc6a6b0aa8fa28c771a9ac2a93e8a31dc626b0aa4fa28c77151ac2a93e8a31dc6a69caa4fa28c771a9ac2a83e8a31dc606b0aa0fa28c771a9a82a83e8a31dc6a680aa0fa28c771a9ac2a73e8a31dc6a6b0a98fa28c771a9ac2a53e8a31dc5e6b0a80fa28c77171ac2a03e8a31dc5b6b0a80fa28cdd151ac2a03e8a31dc6a698a80fa28c77179a62a03e8a31dc6a694a80fa28c771a9a4aa03e8a332c6a680a80fa28bfcc51592a03e8a31dc6a6b0a78fa28
  else (if i < 17 then
  0xc771a9a82ae3e8a31dc6a698ab8fa28c771a9a02ae3e8a31dc66680ab8fa28c778258a2ae3e8a31dc6a6b0ab4fa28c771a9ac2ac3e8a31dc666b0ab0fa28c77151ac2ac3e8a31dc6a6a8ab0fa28c771a9a02ac3e8a31de09628ab0fa28c771a9ac2ab3e8a31dc696b0aacfa28c77199ac2ab3e8a31dc626b0aacfa28c77179ac2ab3e8a31dc5b6b0aacfa28c771a9ab2ab3e8a31dc6a6a8aacfa28c771a9a82ab3e8a31dc626a0aacfa28c771a9a62ab3e8a31dc6a692aacfa28
  else
  0xc771a9ac2b03e8a31dc666b0ac0fa28c77189ac2b03e8a31dc5e6b0ac0fa28c77151ac2b03e8a31dc6a6a8ac0fa28c77151aa2b03e8a31dc6a6a0ac0fa28c771a9a62b03e8a31dc6a694ac0fa28c778258a2b03e8a31dc6a6b0abcfa28c7756a352ae3e8a31dd598d4ab8fa28c771a9c82ae3e8a31dc6a6d4ab8fa28c771a9b4aae3e8a31dc6a6b8ab8fa28c771a9ac2ae3e8a31dc666b0ab8fa28c77189ac2ae3e8a31dc5e6b0ab8fa28c77171ac2ae3e8a31dc6a6a8ab8fa28))
  else (if i < 20 then (if i < 19 then
  0xc778198a2b23e8a31de04628ac8fa28c778098a2b23e8a31de01628ac8fa28c778018a2b23e8a346dfe628ac8fa28c777f98a2b23e8a31de09626ac8fa28c77825892b23e8a31db145eaac8fa28c76c517a2b23e8a31bb58582ac8fa28c76d5d60ab23e8a31dc6a6b0ac4fa28c751a9ac2b13e8a31dc6a67cac4fa28c76d6198ab13e8a31de09628ac4fa28c77731ac2b03e8a31dc896b0ac0fa28c77221ac2b03e8a31dc7c6b0ac0fa28c771edac2b03e8a31dc6e6b0ac0fa28
  else
  0xc7716da4ab23e8a31dc6a690ac8fa28c771a9a3ab23e8a31dc6a68cac8fa28c77199a02b23e8a31dc60680ac8fa28c77171a02b23e8a346c54680ac8fa28c778199f2b23e8a31d46a67cac8fa28c778259eab23e8a31de04662ac8fa28c74d6198ab23e8a31de09660ac8fa28c7781993ab23e8a31cc6a64eac8fa28c77825932b23e8a31de09636ac8fa28d6f8ed8a2b23e8a31de09628ac8fa28c758258a2b23e8a31ce09628ac8fa28c778218a2b23e8a31de07628ac8fa28)
  else (if i < 21 then
  0xc771a9a92b23e8a31dc6a6a2ac8fa28c771a9a82b23e8a31dc696a0ac8fa28c77199a82b23e8a31dc626a0ac8fa28c77181a82b23e8a31dc5e6a0ac8fa28c771a9a7ab23e8a31dc6a69cac8fa28c77189a72b23e8a31dc5469cac8fa28c771a9a6ab23e8a31dc6a698ac8fa28c771a5a62b23e8a31dc66698ac8fa28c77189a62b23e8a31dc5e698ac8fa28c77171a62b23e8a31dc6a696ac8fa28c771a9a52b23e8a31dc5e694ac8fa28c77151a52b23e8a31dc6a692ac8fa28
  else
  0xc7716dac2b23e8a31dc5a6b0ac8fa28c7714dac2b23e8a31dc526b0ac8fa28c73089ac2b23e8a31dc6a6aeac8fa28c6f1a9abab23e8a31dc6a6acac8fa28c771a5ab2b23e8a31dc626acac8fa28c77179ab2b23e8a31dc6a6aaac8fa28c77731aa2b23e8a31ddcb6a8ac8fa28c77225aa2b23e8a31dc886a8ac8fa28c771f1aa2b23e8a31dc6e6a8ac8fa28c771a9aa2b23e8a31dc666a8ac8fa28c77189aa2b23e8a31dc5e6a8ac8fa28c77151aa2b23e8a31dc6a6a6ac8fa28)))
  else (if i < 26 then (if i < 24 then (if i < 23 then
  0xc731a9ac2b23e8a31c46a6b0ac8fa28c6f1a9ac2b23e8a31b46a6b0ac8fa28c6b1a9ac2b23e8a31a46a6b0ac8fa28c671a9ac2b23e8a31946a6b0ac8fa28c631a9ac2b23e8a31dc696b0ac8fa28c771a1ac2b23e8a31a4686b0ac8fa28c7719dac2b23e8a31dc666b0ac8fa28c77195ac2b23e8a31dc646b0ac8fa28c7718dac2b23e8a31dc626b0ac8fa28c77185ac2b23e8a31dc606b0ac8fa28c7717dac2b23e8a31dc5e6b0ac8fa28c77175ac2b23e8a31dc5c6b0ac8fa28
  else
  0xc77765c7ab23e8a31dc6a71eac8fa28c77199c7ab23e8a31dc6a710ac8fa28c77825c12b23e8a31dc666d4ac8fa28c771edb4ab23e8a31dc6a6d2ac8fa28c771a9b12b23e8a31dc6a6baac8fa28c77199ae2b23e8a31de056b0ac8fa28c77761ac2b23e8a31ddcb6b0ac8fa28c77715ac2b23e8a31dc956b0ac8fa28c77221ac2b23e8a31dc826b0ac8fa28c771edac2b23e8a31dc756b0ac8fa28c771bdac2b23e8a32ec6a6b0ac8fa28c771a9ac2b23e8a31d46a6b0ac8fa28)
  else (if i < 25 then
  0xc77765ac2d33e8a31dc6a6b0b4cfa28c77179ac2d33e8a31dc916b0b04fa28c77269ac2bd3e8a31dc5e6b0ae0fa28c771a9a62b83e8a31dc6a6b0ad4fa28c77189ac2b53e8a31dc6a6a0ad4fa28c775664b2b23e8a31dd66910ac8fa28c7780e352b23e8a31dd658d4ac8fa28c77566352b23e8a31dd528d4ac8fa28c7756a332b23e8a31dd598ccac8fa28c778261d2b23e8a31de04844ac8fa28c7782610ab23e8a31ddcb738ac8fa28c771a9cdab23e8a31dc66720ac8fa28
  else
  0xc7781a1a3583e8a31dc6a868d60fa28c7717a1a3583e8a31dc91844d60fa28c7726a0fb583e8a31dc6a876d30fa28c771aa1a34c3e8a31dd628d4c9cfa28c775ae353243e8a31de09868c50fa28c771a9b4afb3e8a31dc7b6b0becfa28c771a9ac2fa3e8a31dc9a6b0bb0fa28c77179ac2e63e8a31dc6a698b98fa28c771a9ce2e13e8a31ddcb6b0b84fa28c771a9ac2e13e8a31dc6a698b84fa28c77269ac2db3e8a31dc5e6b0b60fa28c771a9a62d83e8a31dc6a71eb4cfa28))
  else (if i < 28 then (if i < 27 then
  0xc77189ac2b2408a31dc6a6a0ac90228c771a9ac2ab408a31dd628d4d610028c7759a352b2400a31dc886b0ac90028c771a9ac2b2400a31dc6a6a0ac90028c771a9ac2ab400a31dc626b0ac8fd28c771a9a82b23f4a31dc6a6b0aacfd28c771a9ac2b23eea31dc5e6b0ac8fba8c771a9a62b23eea31dd599231a8fa28c775ae43c6a3e8a31de048d50d0fa28c775624d3583e8a31dd62910d60fa28c77586353583e8a31dc908d4d60fa28c7717a1db583e8a31dc6a86ad60fa28
  else
  0xc771a9d0b3b564a31ddd56b0cc55928c77775ac32e564a31de096f8c515928c771a9b4afe564a31dc7b6b0bf95928c771a9ac2fd564a31dc626b0bc55928c771a9a82f1564a31dd598d4bb55928c77259ac2ed564a31dc6a6b0bb55928c77189ac2ed564a31dc6a742b955928c771a9d0ada564a31dddd6b0b5d5928c77755ac2c1564a31dddd6b0afd5928c771a9c1b58556a31dc6a6b0bc555a8c771a9ac2ed556a31dc6a6b0bf948a8c771a9ac30451ca31dc9a6b0bb54128)
  else (if i < 29 then
  0x18edac2b21e2840063b8d47d07821c771aa1a37c6b0a31dc7a8d4d618228c771a9b4358608a31dc6a6b0c718228c77246353585daa31dc6a732d6170a8c77756353585a6a31ddca8d4e855928c777563538f564a31de048d4df15928c7775235358564a31ddcb732d615928c771a9cc358564a31dddd71cd615928c77189c1b58564a31dc6a6fad615928c77819be358564a31dc6a6f8d615928c77189be358564a31dc6a706d415928c771a9be350564a31dc6a732cf95928
  else 0x18ee35358638840063b8d4d6179a10018eea6358564840063b8d4ccd59210018ee352da564840063ba9b1a8fa210018edac3323e8840063b6b0b6cfa210018ed8dab23e8840063b5e8ac8fa21)))))

private def st4 (i : Nat) : Nat := unpack st4Packed 62 24 i

private def edgeMeta4Packed (i : Nat) : Nat :=
  (if i < 7 then (if i < 3 then (if i < 1 then 0x11044110410f43c0e4380e0380d4310c0300c0300b4290a0280a0280a0280a0220801d064150500e0180401001000000000000000000000000000000 else (if i < 2 then
  0x290a4290a1274962509425094244902348922088220882208822088208801f47c1e4781e0781d4711a8651906419061174561444d1304c1304911444 else
  0x40500401003f4f93d4f43d0f13b4e6390e4390e4384e0374d9360d8360d8360d8360d8348d0334cc324c8320c5310c12e8b52d0b42d0b12b4a6290a4)) else (if i < 5 then (if i < 4 then
  0x55951541505415053549521485214851541501405013d4f13c4e5354c5304c12d4b12c4b12c4b12c4b12c4b126491214751c45911441104410d42505 else
  0x6b1ac6b1ac6b1ac6b1ac6b1ac6b1ac6a5a86a1a5685a0681a06759c6659866198661956458a62188615815e9785e1785d5715a96558560581605815d) else (if i < 6 then
  0x6e1b86e1b86e1b86e1b86e1b86e1b86e1b86e1b86e1b86e1b86e1b86e1b86e1b86d5b46c5ad6b1ac6b1ac6b1ac6b1ac6b1ac6b1ac6b1ac6b1ac6b1ac else
  0x7a9e8795e4791e4785dd765d8749d0741d0735cc731c9715c16f5b96e1b86e1b86e1b86e1b86e1b86e1b86e1b86e1b86e1b86e1b86e1b86e1b86e1b8))) else (if i < 11 then (if i < 9 then (if i < 8 then
  0x8f23c8f23c8e6388e2388e2358d2348d2348c62d89a24892218761684610842108420d81a0481204805fd7f1fc7e5f87d5f17c1f07c1f07c1f07c1f0 else
  0x92248922489224892248922489224892248922489224892248922489224892248922489224892248916449063d8f23c8f23c8f23c8f23c8f23c8f23c) else (if i < 10 then
  0xa5294a5294a5291a3686a1281a02809f67c9f2799e2759c6709b6699a2689a2689a2689a262982609825d97259956549525193649922489224892248 else
  0xa82a0a82a0a769ca729ca729ca729ca729ca729ca729ca729ca729ca729ca729ca729ca729ca729ca729ca7299a6298a6298a6298a6298a6298a5694)) else (if i < 13 then (if i < 12 then
  0xaf2bcaf2bcae6b8ae2b8ae2b8ae2b8ae2b8ae2b8ae2b8ae2b8ae2b8ae2b8ae2b5ad2b1ab6acaa6a5a86a0a82a0a82a0a82a0a82a0a82a0a82a0a82a0 else
  0xb22c8b22c8b22c8b22c8b22c8b22c8b22c5b12c4b12c4b12c4b06c0b02c0b02c0b02c0b02c0b02c0b02c0b02c0b02c0b02c0b02c0af6bcaf2bcaf2bc) else (if i < 14 then
  0xb72dcb72dcb72dcb72dcb72dcb72dcb72d9b56d1b42d0b42d0b42d0b42d0b42d0b42d0b42d0b42d0b42d0b42d0b42d0b42d0b36ccb26c8b22c8b22c8 else 0xbb2ecbb2ecbb2ecbb2ecbb2ecbb2ecbb2e9b96e4b92e4b92e1b82e0b82e0b82ddb72dcb72dcb72dcb72dc))))

private def edgeMeta4 (i : Nat) : Nat := unpack edgeMeta4Packed 10 48 i

private def edgeData4Packed (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0x2c54a94864c911204480f1a2870b10247421a3060b6428488367038302003020a103059320203040403c else 0x529d4274c95ec048911a3020050944808904284f473a80f9f3d14ec47e70d9a3268c982c4cb941048bc6) else (if i < 3 then 0x72a13b74ce16b84add5be6cd989324d599a68b0cb482759b0643183162c17af5cb56ac56ad4a654a1525 else 0x1264478d16243850603f7cf5d986a887871aa9c296ee979640cde3b48d9cae080c1153e8dd3a))

private def edgeData4 (i : Nat) : Nat := unpack edgeData4Packed 7 48 i

private def st5Packed (i : Nat) : Nat :=
  (if i < 45 then (if i < 22 then (if i < 11 then (if i < 5 then (if i < 2 then (if i < 1 then
  0xc771a9ac2b23da071863b8d4d61591f4036c31dc6a6b0ac8fa01a618ee353585647d00c30c771a9ac2b53e805d863b8d4d61591f402ec31dc626b0ac8fa017618ee353505647d00bb0c771a9ac2ab3e805d863b8d4d61591f402cc31dc6a6b0ac8fa00f618ee353585647d00730c77199ac2b23e8039863b8d4d61571f401cc31dc6a6b0ac8f800e618ee353585647d00630c771a9aa2b23e8031863b8d4d61581f4018c31dc6a6b0ac8f900c618ee353585647d004b0c771a9ac2b23e801d863b8d4d61591f400cc31dc6a6b0ac8fa004618ee353585647d001b0
  else
  0xc771a9ac2b23e80c5863b8d4d61501f4062c31dc6a6b0ac8fa030618ee353585647d017b0c771aa1db583e80b9863bab51a9591f405cc31dc896b0ac8fa02e618ee353585647d01730c77151ac2b23e80b9863b8d4d01591f405cc31de09628ac8fa02e618ee353585407d01730c77269ac2823e80b9863bad71a8fa08205cc31dc6a6b0ac8fa02d618ee353585647d01630c771a9ac2b23e8091863b8d4d61591f4046c31dc6a6b0ac8fa020618ee353585647d00eb0c771a9ac2b23ee071863b8d4d61591f4038c31dc5e6b0ac8fa01c618ee3534c5647d00e30)
  else (if i < 3 then
  0xc771b9ac2b23e80e5863b8d4d61591f4072c31dc546b0ac8fa039618ee3535c5647d01c30c771a9ac2b23e80e1863b8d4d01591f4070c31dc6a6b0ac8fa037618ee353585647d01b30c771a9ac2b23f40d5863b8d4d61591f406ac31dc6a6b0ac8f1035618ee353585647d01a30c771a9ac2b23e80cd863b8d4e0dac2b2064c31dc6a720ac8fa032618eee63585647d01930c771a9ac2b23e80c9863b8a8d61591f4064c31dc6a680ac8fa032618ef04b145647d01930c771a9ac2b23c40c9863b8d4e8559193064c31dddd6b0ac870032618ee353585707d018b0
  else (if i < 4 then
  0xc771a9ac2b23c40f1863b8d4e8559193078c31dd6b8d47d04103c618ee353586081801e30c771a9ac2b23e80ed863b8ccd61591f4076c31dc626b0ac8fa03b618ee2f3585647d01db0c771a9aa2b23e80ed863b8d4d41591f4076c31dc6a698ac8fa03b618ef04b145647d01db0c771a9ac2b03e80ed863b8d4d61571f4076c31dc6a6b0aacfa03b618ee4d3585047d01db0c771a9ac2b23e40ed863b8d4d61591f0076c31dc6a6b0ac8f683b618ee353a156464c1db0c77775ac2b21c00ed863bad71a8fa082076c31dc6a6b0c103003b618ee353585647d01d30
  else
  0xc771a9ac2b23e8159863b8d4d61591f40aac31dc6a6b0ac8fa051618ee353585647d02830c771a9ac2b23e813d863b8d4d6178ab209cc31dc6a6b0b60fa04e618ee3e3585647d02730c771a9ac2b23e8139863b8a8d61591f409cc31dc6a6b0a80fa04e618ee4d3585047d02730c771a9ac2b23c4139863bbbad61590e009cc31dc6a6b0c103004e618ee353585647d026b0c771a9ac2b23e80f9863b8d4d61591f407ac31dc6a6b0ac90203c618ee353585cc7d01e30c771a9b52b23e80f1863b8d4d61591f4078c31dc6a680ac8fa03c618ee353585407d01e30)))
  else (if i < 8 then (if i < 6 then
  0xc771a9ac3041c0181863bbbad61590e00c0c31dc6a6b0c1041060618eeb5c6a3e82083030c771a9ac2b23e817d863b8d4d61581f40bec31dc6a6b0ac8f905f618ee353585647d02f30c771a9ac2ae3e8179863b8d4d61591f00bcc31dc6a6b0bf95905d618ee353585f67d02eb0c771a9b4ab23e8175863b8f6d61591f40bac31dc6a6b0ac8fa05d618ee353586081802eb0c771a9ac2b23e8171863b8d4d61591f40b6c31dc6a6b0ac8fa05a618ee353585647d02cb0c771a9ac2b23e8161863b8d4d61591f40aec2ff46a6b0ac8fa057618ef04b145647d02bb0
  else (if i < 7 then
  0xc7716dac2b23e8181863b8d4d51591f40c0c31dc6a6a0ac8fa060618ee3534c5647d03030c771a9a4ab23e8181863bc12c51591f40c0c31dc6a6b0ac0fa060618ee3535855c7d03030c771a9ac2ab3e8181863b8d4d614d9f40c0c31dc6a6b0a50fa060618ee4d3585047d03030c771a9ac2b23e4181863b8d4d61591f00c0c31dc6a6b0ac8f6860618ee353586087883030c771a9ac2fb3c4181863b8d4d61501e20c0c31dc6a6b0ac8ee860618ee353585647583030c771a9ac304366181863b8d4d61821ac0c0c31dc6a6b0c10c9860618ee353a156464c3030
  else
  0xc771a9ac304582181863b8d4e0dac2b20c0c31dc6a6b0bf959060618ee353585f6ac83030c771a9ac2f6564181863b8d4d6178ab20c0c31dc6a6b0c1150060618ee353585fca803030c771a9ac304504181863b8d4d61592040c0c31dc6a6b0ac8fd060618ee3543b6b07d03030c771a9ac2fe3e8181863b8d4d617d9f40c0c31dc6a6b0bd8fa060618ee353585cc7d03030c771a9ac2d83e8181863b8d4d615c1f40c0c31dc6a6d2ac8fa060618ee3db585647d03030c771a9ac2b23e8181863b8ccd61591f40c0c31dc626b0ac8fa060618ee2f3585647d03030))
  else (if i < 9 then
  0xd398ee353586081818692c771a9ac3040c0c33de3b8d4d6182060619cb1dc6a6b0c103030cc38ee35358608181863bc131a9ac3040c0c31ddfb8d4d6182060618eeeec6a6b0c103030c775ae35358608181863b9351a9ac3040c0c31dc7c8d4d6182060618ee354546b0c103030c771aa14358608181863b8d4e85ac3040c0c31dc6a6e0d6182060618ee3536a6b0c103030c771a9ac340608181863b8d4d618a3040c0c31dc6a6b0c3582060600031dc6a6b0bf830280018ee353585f61814000c771a9ac2f60c0a31dc6a6b0c117b060618ee35358608b1c3030
  else (if i < 10 then
  0xc771a9a82b23e8201863b8d4d61559f4100c31dc6a6b0ac8fa07f618ee353585647d03f30c771a9ac2b24001f5863bac51a9ac1f40fac31dd668d4ac8fa07d618ee443585647d03eb0c771a9ac2b23e81f5863bad71a8fa0820fac31dc6a6b0ac8fa07c618ee353585647d03db0c771a9ac2b23e81e9863b8d4d61591f40f2c2e7c6a6b0ac8fa079618eeeeb585643803cb0c771a9ac2b23e81e1863b8d4d61591f40eec31dc6a6b0ac8fa063618ee353585647d03130c771a9ac2b23e818586b3c771a9ac3040c0c35863b8d4d618206061aab1dc6a6b0c103030
  else
  0xc775ae352a03e8209863bacd1a9501f4104c31dc6a680a80fa082618ee353585227d04130c771a9ac28a3e8209863bad71a9411f4104c31dc9a6b0a08fa082618eeb5c6a4087d04130c771a9ac2b23e4209863b8d4d61591f0104c31dc6a6b0ac8f6882618ee353585647a84130c775ae351f43c4209863bad71a8fa1b3104c31dd6b8d47d0d1082618ee353a156464c4130c775ae351f4326209863bbbad61590e0104c31dd6b8d47d070082618eeb5c6a3e835c4130c771a9ac2b23e8205863b8d4d51591f4102c31dc6a6b0ac0fa081618ee353585647d04030))))
  else (if i < 16 then (if i < 13 then (if i < 12 then
  0xc775ae352c73e8209863b8d4d615c1f4104c31dd668d4ac8fa082618eeb146a5647d04130c7757e352b23e8209863bab51a9591f4104c31dc6a720ac8fa082618ee3536a5647d04130c771a9ae2b23e8209863b910d61591f4104c31dc6a6b0ac8fa082618ee333585647d04130c77189ac2b23e8209863b8bcd61591f4104c31dc5c6b0ac8fa082618ee353545647d04130c771a9a82b23e8209863b8d4d31591f4104c31dc6a67cac8fa082618ee353375647d04130c778258a2b23e8209863b8d4d61581f4104c31dc6a6b0ab8fa082618ee353585567d04130
  else
  0xc77826b5c6a3e8209863bbbb5ae351f4104c31ddcead71a8fa082600031dd668d47d041280018eeb146a3e82094000c7757e351f4104a31dd6babf1a8fa082618eeb5c9a8d47d04130c775ae44c6a3e8209863bad71aa2a1f4104c31dd6b8d50a0fa082618eeb5c6a8447d04130c775ae353a13e8209863bad71a9b81f4104c31dd668d4d60fa082618eeb146a6b07d04130c7757e353583e8209863b8d50edac1f4104c31dd6b8d4d00fa082618eeb146a6807d04130c775ae353143e8209863bad71a9821f4104c31dc6a6b0b98fa082618ee353585b07d04130)
  else (if i < 14 then
  0xc771a9ac2b23e8241863b8d4d61591f411ec31dc6a6b0ac8fa08e618ee353585647d046b0c771a9ac2b23e8231863b8d4d61591f4116c31dc6a6b0b90fa08a618ee353585647d04530c771a9ac2823e8229863b8d4d61591f4112c31dc6a6b0ac8fa088618ee353585647d043b0c771a9ac2b23e8219863b8d4d61591f410ac31dc6a6b0ac8fa084618ee353585647d041b0c771a9ac2b240020986b8c775ae351f4104c35563bad71a8fa08261a731dd6b8d47d04130d258eeb5c6a3e8209867bc775ae351f4104c33963bad71a8fa082619971dd6b8d47d04130
  else (if i < 15 then
  0xc77179ac2b23e8379863b8d4d61591ed1bcc31dc6a6b0ac8fa0dd618eeeac6a6b0ac86e30c771a9ac2d33e8371863b8d4e3d591f41b8c31ddd96b0ac8fa0dc618ee353585647d06e30c77775ac2b21c0371863b8d4d61591f41b6c31dc6a6b0ac8fa0da618ee353585647d06cb0c771a9ac2b23e8361863b8d4d61591f41aec2afc6a6b0ac8fa0d7618ee353585647d06b30c771a9ac2b23e835586aac771a9ac1f4122c31dd6b8d4d60fa091618ee353586087d048b0c771a9ac2b23e8245863b8d4d61501f4122c31dc6a6b0a08fa091618ee353a156464c48b0
  else
  0xc771a9a82b23e8381863b8d4d39591f41c0c31dc6a698ac8fa0e0618ef04b145647d07030c771a9ac2b03e8381863b8d4d61571f41c0c31dc6a6b0aacfa0e0618ee353585527d07030c77269ac2823e8381863b8d4d61591f21c0c31dc6a6b0ac8f80e0618ee353585647b47030c77775ac2b23c4381863bbb2d61591e21c0c31dc546b0ac8f10e0618eeeeb585646cc7030c771a9ac2b2344381863b8d4d615919b1c0c31dc6a742ac8c98e0618eeeeb5856464c7030c771a9ac2b23e837d863b8ccd61591f41bec31dc6a6b0ac8f80df618ee353585647d06f30)))
  else (if i < 19 then (if i < 17 then
  0xc771a9ac2f1564381863bbbad616c2b21c0c31dddd6b0b1d590e0618eeeeb58564a807030c77775ac2b2522381863bbbad61592821c0c31dc6a6b0ac9020e0618ee353585647e87030c771a9ac2d33e8381863b8d4e3d591f41c0c31ddd96b0ac8fa0e0618eeeab585647d07030c7773dac2b23e8381863bb98d61591f41c0c31dc896b0ac8fa0e0618ee3e3585647d07030c771b9ac2b23e8381863b8d4d61591f41c0c31dc666b0ac8fa0e0618ee313585647d07030c77179ac2b23e8381863b844d61591f41c0c31dc1b6b0ac8fa0e0618ee353545647d07030
  else (if i < 18 then
  0xcef8eeeeb585643818672c77775ac2b21c0c31de09bbad61590e0600031ddd96b0ac870280018eeeab585643814000c7773dac2b21c0a31ddddb9ed61590e0618eeeed6b6b0ac87030c77776ae358564381863bbbb269ac2b21c0c31ddd98d4d61590e0618eeeac6a6b0ac87030c7773e35358564381863bbbb151ac2b21c0c31ddd58a8d61590e0618eeeec286b0ac87030c77775d0b58564381863bbbae41ac2b21c0c31dc6a706d61590e0618eeeeb706b0ac87030c77775ac340564381863bbbad619f2b21c0c31dddd6b0c51590e0618eeeeb58608ac87030
  else
  0xc77269ac2823e83bd863b8d4d61591e21dec31dc6a6b0ac8c98ef618ee353585647d07730c771a9ac2b23e83b5863b8d4d61591f41d8c31dc6a6b0ac8fa0eb618ee353585647d07530c771a9ac2b23e83a5863b8d4d61782b21d0c31dc6a6b0ac8fa0e8618ee3535856464c7430c771a9ac2b23e839d863b8d4d61591f41ccc31dc6a6b0ac8fa0e5618ee353585647d07230c771a9ac2b23e838d863b8d4d61591f41c4c31dc6a6b0ac8fa0e161ae71dddd6b0ac87030d678eeeeb58564381869cc77775ac2b21c0c34963bbbad61590e0619ef1dddd6b0ac87030))
  else (if i < 20 then
  0xc771a9ac2b23e8645863b8d4d31591f4322c31dc6a6b0ac8f6991618ee353585647d0c830c771a9ac2b23e863d863b8d4e65ac2b231cc31dc6a6b0b84fa18e618ee3539c5647d0c730c7772dac2b23e8639863b8d4d61591f431cc31dc6a742ac8c998e618ee353585647d0c6b0c771a9ac2b23e8631863b8d4d61591f4316c31dc6a6b0ac8fa18a61232353585647d0c530c77269ac2823e8629863b8d4d61591f4312c31dc6a6b0ac8fa188618ee353585647d07930d678ee353585643bd863bbbb1a9ac2b21dec31dc6a6b0c11590ef618ee353585647d077b0
  else (if i < 21 then
  0xc77189ac2b23e864d863b8c0d61591f4326c31dc5e6b0ac8fa193618ee353545647d0c9b0c771a9a82b23e864d863b8d4d31591f4326c31dc6a64eac8fa193618ee353205647d0c9b0c778258a2b23e864d863b8d4d61581f4326c31dc6a6b0ab8fa193618ee353585567d0c9b0c771a9ac2a83e864d863b934d61411f4326c31dc6a6b0ac8f9193618ee353585647c0c9b0c771a9ac2b23da64d863b8d4e85591e2326c31dc6a738ac8f1193618ee35340564788c9b0c771a9d0ab236664d863b8d4d61591f4324c31dc6a6a8ac8fa192618ee353585647c8c930
  else
  0xc771a9d0b4056464d863b8d4e65a02b2326c31dc6a742cc559193618ee353a1628ac8c9b0c771a9d0b0456464d863b8d4d6178ab2326c31dc6a742b9959193618ee353a158eac8c9b0c771a9d0ab254064d863b8d4e8559282326c31dc6a742ac93c993618ee35358564810c9b0c771a9ac2b23f464d863b8d4d61709f4326c31dd5a8d4ac8fa193618ee3539c5647d0c9b0c771a9ccab23e864d863b8d4e55591f4326c31dc6a720ac8fa193618ee3536a5647d0c9b0c771a9ae2b23e864d863bb96d61591f4326c31dc6a6b0ac8fa193618ee333585647d0c9b0)))))
  else (if i < 33 then (if i < 27 then (if i < 24 then (if i < 23 then
  0xd738ee353a156464d86aac771a9d0ab2326c34e63b8d4e855919361a4b1dc6a742ac8c9b0cf78ee353a156464d8675c771a9d0ab2326c33963b8d4e8559193618ef04c6a742ac8c9b0c77776353a156464d863bb991a9d0ab2326c31dd6b8d4e8559193618ee4d46a742ac8c9b0c7722e353a156464d863b8d5151d0ab2326c31dc6a850e8559193600031dc6a738ac8c9a80018ee3539956464d4000c771a9caab2326a31dc6a742e5559193618ee353a16e0ac8c9b0c771a9ce35856464d863b8d4e65ac2b2326c31dc6a72ad6159193618ee353836b0ac8c9b0
  else
  0xc771a98a2b23e869d863b8d4d61591f434cc31dc6a6b0ac8fa1a5618ee353585647d0d230d558ee35358564689863b8d4e85ac2b2344c31dc6a6b0c11591a2618ee353585647d0d130c771a9ac2b23c4689863b8d4d61591f4342c31dc6a6b0ac8fa1a0618ee353585647d0cfb0c771a9ac2b23e8679863b8d4d61591f433ac31dc6a6b0ac8fa19c618ee3535856480ccdb0c771a9ac2b23e866d863b8d4d61591f4334c31dc6a6b0ac8fa199618ee353585647d0cc30c771a9ac2b23e865d863b8d4d61591f432cc31dc6a6b0ac8fa195618ee353585647d0ca30)
  else (if i < 25 then
  0xc771a9ac2ab3e86cd863b934d61411f4366c31dc6a6b0ac8f91b3618ee353585647c0d9b0c771a9ac2b23da6cd863b8d4d61591f4364c31dc6a6b0ac8fa1b1618ee353585647d0d830c7b1a9ac2b23e86bd863b8d4d61591f435ec2354546b0ac8fa1af618ee353585647d0d6b0d558ee352b23e86b1863bad71a9591f4358c31dc6a742ac8fa1ac618ee353585647d0d630c771a9a02b23e86b1863b8d4c51591f4358c31dc6a6b0ac8fa1ab618ee353585647d0d530c771a9ac2b23e86a5863b8d4d61591f4350c31dc6a6caac8fa1a7618ee353585647d0d3b0
  else (if i < 26 then
  0xc771a9ac2b23e8759863b8d4d61591f43aac31dc6a6b0ac8fa1d4618ee353585647d0ddb0c771a9ac2b23e86e5863b8d4d61591f4370c31dc6a6b0ac8fa1b7618ee353585647d0db30c77179ac2b23e86d9863b8d4d61591f436ac31dc626b0ac8fa1b5618ee353585647d0da30c77199ac2b23e86d1863b8d4d61591f4366c31dc666b0ac8fa1b3618ee313585647d0d9b0c77179ac2b23e86cd869c8a8d61591f4366c31dc6a6a8ac8fa1b3618ee353505647d0d9b0c771a9a62b23e86cd863bc12c51591f4366c31dc6a6b0ac0fa1b3618ee3535855c7d0d9b0
  else
  0xc771a9a62b23e8789863bc12c51591f43c4c31dc6a6b0ac0fa1e2618ee3535855c7d0f130c771a9ac2ab3e8789863b934d61411f43c4c31dc6a6b0ac8f91e2618ee353585647c0f130c771a9ac2b23da789863b8d4d61591f43c2c31dc6a6b0ac8fa1de61ae71dc6a6b0ac8eeb0c7777635358564775863b8d4e85ac2b23bac31dc6a6b0ac8fa1dd618ef04b145647d0eeb0c771a9ac2b23c4775863b8d4d61591f43b8c31dc6a6b0ac8fa1db618ee353585647d0ed30c771a9ac2b23e8765863b8d4d61591f43b0c31dc6a6b0ac8fa1d7618ee353816b0ac8eb30)))
  else (if i < 30 then (if i < 28 then
  0x18ee35350564789463b8d4d61a82b23c4c31dc6a6b0bf9591e2618ee353585e0ac8f130cf78ee353585567898000c771a9ac2ab3c4a31dc6a6b0ac9559e2618ee3535856480cf130c771a9ac2e13e8789863b8d4d61699f43c4c31dc6a71eac8fa1e2618ee353695647d0f130c7772dac2b23e8789863b8f6d61591f43c4c31dc6a6b0ac8fa1e2617fa353585647d0f130abf1a9ac2b23e8789848c8d4d61591f43c4c31dc666b0ac8fa1e2618ee313585647d0f130c77179ac2b23e8789846a846d61591f43c4c31dc6a6a8ac8fa1e2618ee353505647d0f130
  else (if i < 29 then
  0xc771a9a62b23e87b5863b8d4d61501f43dac33763b8d4d61591eb600031dc6a6b0ac8f5a8c771a9ac2b25047ad863b8d4d61591f43d6c332e3b8d4d61591ea600031dc6a6b0ac8f528c771a9ac2b23e87a9863b8d4d61591f43ccc31dc6a6b0ac8fa1e5618ee353585647d0f230c771a9ac2b23e878d8677c771a9ac2b23c4c33ae3b8d4d61591e2619871dc6a6b0ac8f130c7775635358564789867bc77189ac2b23c4c00063b8c4d61591e2518ee354626b0ac8f130cf71aa14358564789863b8d4e65ac2b23c4c31dc6a702d61591e2619ef1dc6a6a0ac8f130
  else
  0xc775ae353585647b5863b9351a9ac2b23dac33963b8bcd61591ed600031dc5e6b0ac8f6a8c771aa2f3585647b5863b8d5151ac2b23dac31dc6a856d61591ed618ee354286b0ac8f6b0c771a9d0b585647b5863b8d4dc1ac2b23dac33963b8d4d31591ed600031dc6a698ac8f6a8c771a9ac34c5647b5863b8d4d61a02b23dac31dc6a6b0c51591ed618ee35358608ac8f6b0c771a9ac2fb5647b5863b8d4d6163ab23dac33963b8d4d61501ed600031dc6a6b0a80f6a8c771a9ac2b25407b5863b8d4d61592823dac31dc6a6b0ac8fa1ed618ee2f3585647d0f6b0))
  else (if i < 31 then
  0xc771a9ac3045647c1863b8d4d6163ab23e0c34963b8d4d61571f0600031dc6a6b0ab8f828c771a9ac2b255c7c1863b8d4d61592a03e0c31dc6a6b0ac9411f0618ee353585647d0f830c77199ac2b23e87c1863b8d4d01591f43e0c31dc6a6b0ab8fa1f061a371dc6a6b0ac8f7300018ee353585647b9463b8d4d618a2b23dcc31dc6a6b0ac8fa1ee61ac31dc6a6b0ac8f6b0d398ee353585647b58692c771a9ac2b23dac33de3b8d4d61591ed619cb1dc6a6b0ac8f6b0cc38ee353585647b58000c771a9ac2b23daa31de098d4d61591ed618eeeec6a6b0ac8f6b0
  else (if i < 32 then
  0xc771a9ac2b03e87c9869cc771a9ac2b23e0c34963b8d4d61591f0619ef1dc6a6b0ac8f830ceb8ee353585647c18672c771a9ac2b23e0c00063b8d4d61591f0518ef04c6a6b0ac8f830c77776353585647c1863bad71a9ac2b23e0c31dc9a8d4d61591f061a4b1dc666b0ac8f8300018ee333585647c1463b8d5199ac2b23e0c31dc6a8a8d61591f0618ee3542a6b0ac8f830c771aa143585647c1863b8d4e85ac2b23e0c31dc6a738d61591f0618ee353706b0ac8f830d258ee353405647c18000c771a9a02b23e0a31dc6a6b0d01591f0618ee35358628ac8f830
  else
  0xc775ae353585647c9863b9351a9ac2b23e4c34e63b8a8d61591f2600031dc546b0ac8f928c771aa2a3585647c9863b8d50a5ac2b23e4c31dc6a850d61591f2618ee353a16b0ac8f930c771a9b83585647c9869cc771a9aa2b23e4c00063b8d4d51591f2518ee353586a8ac8f930c771a9ac3405647c9863b8d4d618a2b23e4c31dc6a6b0c11591f2618ee3535858eac8f930d398ee353585607c98000c771a9ac2b03e4a31dc6a6b0ac9581f2618ee35358564a80f930c771a9ac2b25047c9863b8d4d61591f43e4c31dc546b0ac8fa1f2618ee353545647d0f930))))
  else (if i < 39 then (if i < 36 then (if i < 34 then
  0xc771a9ac2b23fa7d1863b8d4d61591fc3e8c31dc6a6b0ac8fd9f4618ee353585647e8fa30c771a9ac2b23f27d1863b8d4d61591f83e8c31dc6a6b0ac8fb9f4618ee353585647d8fa30c771a9ac2b23ea7d186b8c771a9ac2b23e6c00063b8d4d61591f3518ef04c6a6b0ac8f9b0c775ae353585647cd863b9351a9ac2b23e6c31dc6a6b0ac8fa1f361a731dc6a6b0ac8f930d258ee353585647c9867bc771a9ac2b23e4c33be3b8d4d61591f2619cb1dc6a6b0ac8f9300018ee353585647c9463bc131a9ac2b23e4c31dddd8d4d61591f2618eeecc6a6b0ac8f930
  else (if i < 35 then
  0xc77189ac2b25007d1863b8d4d6155a803e8c31dc6a6b0ac93f9f4618ee48c6a6b09f8fa30c77566352b24fc7d1863b92cd615927e3e8c31dc6a6b0ac93f1f4618ee4d3585049f8fa30c771a9ac2b24fa7d1863b8d4d615927c3e8c31dc6a6b0ac93d9f4618ee353585649e8fa30c771a9ac2b24f27d1846a72ad61592793e8c31dc6a6b0ac93c1f4618ee353585649dcfa30c771a9ac2b240a7d1863b8d4d61592043e8c31dc6a6b0ac9019f4618ee35358564808fa30c771a9ac2b24027d1863b8d4d61592003e8c31dc6a6b0ac8ff9f4618ee353585647f8fa30
  else
  0xc77225ac2b25047d1863b8f8d61592823e8c31dc6e6b0ac9411f4618ee35358564a08fa30c77199ac2b25047d1863b8c4d61592823e8c31dc5e6b0ac9411f4618ee35354564a08fa30c771a9a82b25047d1863b8d4d31592823e8c31dc6a694ac9411f4618edac331564a08fa30c76d61952b25047d1863bc12c51592823e8c31dc6a6b0ac1411f4618ee3535855ca08fa30c771a9ac2ab5047d1863b934d61502823e8c31dc966b0a81411f4618ee2a358540a08fa30c771a9ac2b25027d1863b8ccd61592813e8c31dc6a6b0ab9409f4618ee35358564a00fa30))
  else (if i < 37 then
  0xc7725a353585047d1863b9231a9ac2823e8c31dc8c8d4d61411f4618ee4d4546b0a08fa30c772462a3585047d1863b8d50edac2823e8c31dc9a850d61411f4618ee4d3a16b0a08fa30c77269c93585047d1863b934dc1ac2823e8c31dc9a6b0d01411f4618ee4d35864ea08fa30c77269ac3145047d1863b934d61822823e8c31dc9a6b0bc5411f4618ee353585cca08fa30c771a9ac2d85047d1863b934d6163a823e8c31dc6a6b0ae1411f4618eeacc6a564a08fa30c77731ac2b25047d1863b92cd61592823e8c31dc916b0ac9411f4618ee46358564a08fa30
  else (if i < 38 then
  0xc771a9ac2d65147d1863b8d4d615928a3e8c31dc6a6b0ac9449f4618ee35358564a20fa30c771a9ac2b250e7d1863b8d4d61592863e8c31dc6a6b0ac9429f4618ee35358564a10fa30c771a9ac2b25067d186b8c77269ac2823e8c359e3b934d61411f461a731dc9a6b0a08fa30d258ee4d3585047d1867bc77269ac2823e8c33963b934d61411f4619bb1dc9a6b0a08fa30c778264d3585047d1863bbbb269ac2823e8c31dd6b934d61411f4618eead49a6b0a08fa300018ee4b3585047d14000c77245ac2823e8a00063b918d61411f4518ee4d48c6b0a08fa30
  else
  0xc771a9ac2b25367d1863bc12c515929b3e8c31dc6a6b0a814d9f4618ee35358564a68fa30c771a9ac2b25327d1863b8d4d61592983e8c31dc6a6b0ac94b9f4618ee35358564a58fa30c771a9ac2b252a7d1863b8d50e5ac2943e8c31dc6a6b0ac94a1f4618ee35358564a4cfa30c771a9ac2b25247d186b3c771a9ac2913e8c31dc9a8d4d61489f4618ee35358608a44fa30c771a9ac2b25227d1863b8d4d61502913e8c31dc6a6b0ac9481f4618ee35358564a3cfa30c771a9ac2b251c7d1863b8d4d615928d3e8c31dc6a6b0ac9461f4618ee35358564a2cfa30)))
  else (if i < 42 then (if i < 40 then
  0xc77566352b25407d1863b8d4da5592a03e8c31dc886b0ac9501f4618ee3db58564a80fa30c771a9ac2b25407d185fe8d4d61592a03e8c2e7c6a6b0ac9501f4618ee33358564a80fa30c77189ac2b25407d1863b8bcd61592a03e8c2353956b0ac9501f4611a9b5b58564a80fa30c771a9aa2b25407d1863b8d4d41592a03e8c31dc6a698ac9501f4618ef04b14564a80fa30c771a9ac2b05407d1863b8d4d61572a03e8c31dc6a6b0aad501f4618ee35358564a7cfa30c771a9ac2b25387d186b8c771a9ac29b3e8c31dd6b8d4d614d9f4618ee4d46a6b0a6cfa30
  else (if i < 41 then
  0xc771a9ac2b25527d18675c771a9ac2a83e8c00063b8d4d61541f4518ee35358564aa0fa30c771a9ac2b25487d1863b8d4d61592a33e8c31dc6a6b0ac9511f4618ee35358564a84fa30cdd8ee353585407d18665c771a9ac2a03e8c330e3b8d4d61501f4618eeb146a6b0a80fa30c77246353585407d18672c77179ac2a03e8c00063b8bcd61501f4518ee3545e6b0a80fa30c771aa1cb585407d186728d4dc1ac2a03e8c33963b8d4d31501f4600031dc6a698a80fa28c771a9ac34c5407d1863b8d4d617daa03e8c31dc6a6b0b91501f4618ee353585aca80fa30
  else
  0xc77776353585567d1863bad71a9ac2ab3e8c31dc9a8d4d61559f4619ef1dc626b0aacfa300018ee313585567d1463b8d5189ac2ab3e8c31dc6a8a8d61559f4618ee354286b0aacfa30c771a9d0b585567d1863b8d4dcdac2ab3e8c31dc6a6e0d61559f4619ef1dc6a6a0aacfa300018ee353505567d1463b8d4d61a82ab3e8c31dc6a6b0d01559f4618ee35358628aacfa30c771a9ac3045567d1863b8d4d617f2ab3e8c31dc6a6b0b1d559f4618ee35358564aacfa30c77189ac2b25567d1863b8d4d41592ab3e8c33be3b8d4d61549f4600031dc6a6b0aa4fa28))
  else (if i < 43 then
  0xc771a9d0b5855c7d1863b8d4dc9ac2ae3e8c31dc6a6e0d61571f461a4b1dc6a680ab8fa300018ee3534055c7d1463b8d4d61a02ae3e8c31dc6a6b0c51571f4618ee35358608ab8fa30c771a9ac2c755c7d1863b8d4d61592ae3e8c31dc666b0ac9571f4618ee35340564ab8fa30d1b8ee353585587d18000c771a9ac2ac3e8a31dc6a6b0c51561f4618ee35358564ab0fa30d618ee353585567d1869cc771a9ac2ab3e8c34963b8d4d61559f4619ef1dc6a6b0aacfa30ce58ee353585567d18661c771a9ac2ab3e8c00063b8d4d61559f4518ef04c6a6b0aacfa30
  else (if i < 44 then
  0xc771a9ac3545607d1863b8d4d61a02b03e8c31dc6a6b0c51581f4618ee35358608ac0fa30c771a9ac2c75607d1863b8d4d61592b03e8c31dc546b0ac9581f4618ee35354564ac0fa30d398ee3535855c7d18692c771a9ac2ae3e8c33de3b8d4d61571f4619cb1dc6a6b0ab8fa30ccb8ee3535855c7d18000c771a9ac2ae3e8a31de098d4d61571f4618eeeec6a6b0ab8fa30c775ae3535855c7d1863bacd1a9ac2ae3e8c31dc9a8d4d61571f461a4b1dc666b0ab8fa300018ee3335855c7d1463b8d5199ac2ae3e8c31dc6a8a8d61571f4618ee354286b0ab8fa30
  else
  0xc77826353585627d1863bbbb1a9ac2b13e8c31dc6a742d61589f4618ee35358564ac4fa30d398ee353585607d18692c771a9ac2b03e8c33de3b8d4d61581f4619cb1dc6a6b0ac0fa30cdd8ee353585607d18000c771a9ac2b03e8a31de098d4d61581f4618eeeec6a6b0ac0fa30c775ae353585607d1863b9351a9ac2b03e8c31dc968d4d61581f461a731dc546b0ac0fa300018ee2a3585607d1463b8d5151ac2b03e8c31dc6a850d61581f4618ee353a16b0ac0fa30c771a9b8b585607d1863b8d4dc1ac2b03e8c34e63b8d4d51581f4600031dc6a6a8ac0fa28))))))
  else (if i < 68 then (if i < 56 then (if i < 50 then (if i < 47 then (if i < 46 then
  0xd678edac2c15647d1863bbbad6160ab23e8c31dc9a6b0b05591f4618ee35358582ac8fa30c77151ac2c15647d1863b6b0c5160ab23e8c31dc6a6b0b01591f4618ee3535857eac8fa30c771a9ac2be5647d1863b8d4d615eab23e8c31dc786b0af1591f4618ee35358578ac8fa30c76d618a2bc5647d1863b8d4d615dab23e8c31dc6a6b0ae9591f4618ee35358572ac8fa30c771a9ac2b85647d1863b8d4d615bab23e8c31dc6a6b0ad9591f4618ee3535856aac8fa30c771a9ac2b45647d1863b8d4d6159ab23e8c35ce3b8d4d61589f4600031dc6a6b0ac4fa28
  else
  0xc771a9ac2cc5647d1863b8d4d6165ab23e8c31dc6a6b0b29591f4618ee3534c594ac8fa30c771a9ac2c95647d1863b8d4d4164ab23e8c31dc6a6b0b21591f4618ee35354590ac8fa30c771a9ac2c75647d1863b8ccd6163ab23e8c31dc626b0b1d591f4618ee2f35858eac8fa30c771a9aa2c75647d1863b8d4d4163ab23e8c31dc6a698b1d591f461a4a3534058eac8fa30c778258a2c75647d1863b8d4d61632b23e8c31dc6a6b0b15591f4618ee35358588ac8fa30c7d1a9ac2c35647d1863b8d4d6161ab23e8c235358680b0d591f4618ee35358584ac8fa30)
  else (if i < 48 then
  0xc771a9ac2e65647d1863b8d4d6172ab23e8c31dc6a6b0b91591f4618ee353585c6ac8fa30c771a9ac2e25647d1863b8d4d6170ab23e8c31dc6a6b0b81591f4618ee353585beac8fa30c771a9ac2de5647d1863b8d4d616eab23e8c31dc6a6b0b71591f4618ee353585b2ac8fa30c771a9ac2d85647d1863b8d4d616bab23e8c31dc6a6b0b59591f4618ee353585aaac8fa30c771a9ac2d45647d1863b8d4d6169ab23e8c31dc6a6b0b49591f4618ee353585a2ac8fa30c771a9ac2d05647d1863b8d4d6167ab23e8c31dc6a6b0b39591f4618ee3535859aac8fa30
  else (if i < 49 then
  0xc771a9ac3005647d1863b8d4d617fab23e8c31dc6a6b0bf9591f4618ee353585f8ac8fa30c771a9ac2fb5647d1863b8d4d617c2b23e8c31de09628be1591f4618ee353585eeac8fa30c771a9ac2f65647d1846a8a8d617b2b23e8c235358680bd9591f4618ee353585eaac8fa30c771a9ac2f25647d1863b8d4d6178ab23e8c31dc6a6b0bc1591f4618ee353585deac8fa30c771a9ac2ee5647d1863b8d4d6176ab23e8c31dc6a6b0bb1591f4618ee353585d6ac8fa30c771a9ac2ea5647d1863b8d4d6174ab23e8c31dc6a6b0ba1591f4618ee353585ceac8fa30
  else
  0xc77819ac3095647d1863b8d4d6184ab23e8c31de09628c25591f4618ee35358610ac8fa30c771a9ac3075647d1863b8d4d61832b23e8c31dc6a6b0c15591f4618ee35358608ac8fa30c6f1a9ac3045647d186348d4d61822b23e8c31dc696b0c11591f4618ee34358608ac8fa30c77199ac3045647d1863b8c4d61822b23e8c31dc5e6b0c11591f4618ee35357608ac8fa30c771a9ab3045647d1863b8d4d51822b23e8c31dc6a6a0c11591f4618ee3534c608ac8fa30c778258a3045647d1863b8d4d6181ab23e8c31dc6a6b0c09591f4618ee35358602ac8fa30)))
  else (if i < 53 then (if i < 51 then
  0xc77199ac3145647d1863b8c4d618a2b23e8c31dc5e6b0c51591f4618ee35354628ac8fa30c771a9a83145647d1863b8d4d318a2b23e8c31de09680c51591f4618ef03340628ac8fa30c77151a03145647d1863b8d4d6189ab23e8c31dc626b0c4d591f4618ee35350626ac8fa30c771a9ac3125647d1863b8bcd61892b23e8c31dc6a698c49591f4618ee35358622ac8fa30c771a9ac3105647d1863b8d4d6187ab23e8c31dc6a6b0c39591f4618ee3535861aac8fa30c771a9ac30c5647d1863b8d4d6185ab23e8c31dc6a6b0c29591f4618ef0246a612ac8fa30
  else (if i < 52 then
  0xc77826b5b145647d1863bc132698a2b23e8c31de068d4c51591f4618ef0246a628ac8fa30c777fa353145647d1863bab51a98a2b23e8c31de098a8c51591f4618ef02454628ac8fa30c778261db145647d1863bc130a18a2b23e8c31de09742c51591f4618ee35390628ac8fa30c77825c1b145647d1863bc12dc18a2b23e8c31dc6a6d4c51591f4618ee3535c628ac8fa30c77819ac3145647d1863bc08d618a2b23e8c31ddfe6b0c51591f4618eee6358628ac8fa30c77225ac3145647d1863b8f8d618a2b23e8c31dc6e6b0c51591f4618ee35358628ac8fa30
  else
  0xc771a9ac3215647d1863baab1a9902b23e8c31dc6a6b0c81591f4618ee3535863eac8fa30c771a9ac31e5647d1863b8d4d618eab23e8c31dc6a6b0c69591f4618ee35358632ac8fa30c771a9ac3185647d1863b8d4d618bab23e8c31dc6a6b0c59591f4618ee3535862aac8fa30d738ef04b145647d186b8c778258a2b23e8c34e63bc12c51591f461a4b1de09628ac8fa30d1b8ef04b145647d1867bc778258a2b23e8c33963bc12c51591f4600031de06628ac8fa280018ef023145647d14000c777f98a2b23e8a31de09bfcc51591f4618ef04ddd628ac8fa30))
  else (if i < 54 then
  0xc77825ac3315647d1863bbbad6198ab23e8c31dc6a6b0cc5591f4618ee2a358662ac8fa30c771a9ac3305647d1863b8d4d6197ab23e8c31dc6a6b0cb9591f4618ee3535865aac8fa30c771a9ac32c5647d1863b8d4d6195ab23e8c31ddc86b0ca9591f4618ee35358654ac8fa30c771a9ac3295647d1863b8d4d61942b23e8c35c63b8d4c9d591f4618ef04c6a64eac8fa30c775ae353275647d1863b8d4d6193ab23e8c31dc6a680c9d591f4618ee3535864cac8fa30c771a9ac3255647d1863b8d4d61922b23e8c31dc6a6b0c8d591f4618ee35358644ac8fa30
  else (if i < 55 then
  0xc77199ac3405647d1863b8c4d61a02b23e8c31dc5e6b0d01591f4618ee35354680ac8fa30c771a9a83405647d1863b8d4d31a02b23e8c31dc6a6b0cfd591f461ae71dc6a67cac8fa30c778263533e5647d1863b8d4e859f2b23e8c31dc6a6b0cf9591f4618ee3534067cac8fa30c771a9ac33d5647d1863b8d4d619e2b23e8c31dc6a6b0ced591f4618ee35358674ac8fa30c771a9ac3395647d1863b8d4d619c2b23e8c31dc6a716cdd591f4618ee3535866eac8fa30c771a9ac3365647d1863b8d4d619aab23e8c31dc6a6b0cd1591f461ae71db58662ac8fa30
  else
  0x18ee353495647d1463b8d4d61a4ab23e8c31dc6a6b0d15591f4618ee35358688ac8fa30c771a9ac3435647d1863b8d4d61a12b23e8c31dc6a6b0d05591f461a371dc6a680ac8fa30ceb8ee353405647d18665c771a9a02b23e8c31de048d4d01591f4618eeb346a680ac8fa30c77556353405647d18692c77199a02b23e8c00063b8ccd01591f4518ee35466680ac8fa30c771a9ce3405647d1863b8d4e2da02b23e8c31dc6a6cad01591f4618eee5b58680ac8fa30c77221ac3405647d1863b8d4d61a02b23e8c2e7c6a6b0d01591f46123235358680ac8fa30))))
  else (if i < 62 then (if i < 59 then (if i < 57 then
  0xd258ee3534c5647d1867bc771a9a62b23e8c33963b8d4d31591f4619971dc6a698ac8fa300018ee3534c5647d1463bc131a9a62b23e8c31dddd8d4d31591f4618eeb5c6a698ac8fa30c7758a3534c5647d1863b9351a9a62b23e8c33963b8bcd31591f4600031dc5e698ac8fa28c771aa2f34c5647d1863b8d5151a62b23e8c31dc6a850d31591f4618ee353a1698ac8fa30c771a9cf34c5647d1863b8d4dc1a62b23e8c31dc6a6b0d31591f4618ee2f358698ac8fa30cdd8ee3534a5647d18000c771a9a52b23e8a31dc6a6b0d29591f4619871dc6a692ac8fa30
  else (if i < 58 then
  0xcf78ee353505647d18675c771a9a82b23e8c33963b8d4d41591f4600031dc6a6a0ac8fa28c77826353505647d1863bbbb1a9a82b23e8c31dd6b8d4d41591f4618eeb446a6a0ac8fa30c7726a353505647d1867bc77189a82b23e8c00063b8c4d41591f4518ee354626a0ac8fa30c771aa2a3505647d1863b8d50a1a82b23e8c31dc6a742d41591f4618ee353996a0ac8fa30c771a9b83505647d1863b8d4d61a82b23e8c31dc626b0d41591f4619df1dc6a69cac8fa300018ee3534e5647d1463b8d4d61a72b23e8c35863b8d4d31591f461a731dc6a698ac8fa30
  else
  0x18ee353565647d1463b8d4d61ab2b23e8c34e63b8d4d51591f461a4b1dc6a6a8ac8fa30d1b8ee353545647d1867bc771a9aa2b23e8c33963b8d4d51591f4600031dc6a6a8ac8fa28c77826353545647d1863bc0d1a9aa2b23e8c31dddd8d4d51591f4618eeb5c6a6a8ac8fa30c7726a353545647d1869cc77151aa2b23e8c00063b8a8d51591f4518ee354546a8ac8fa30c771aa143545647d1863b8d4e85aa2b23e8c31dc6a6e0d51591f4618ee353586a8ac8fa30c77151ac3545647d186b0c771a9a82b23e8c34e63b8d4d41591f461a4b1dc6a6a0ac8fa30))
  else (if i < 60 then
  0xc771a9b53585647d1863b8d4da5ac2b23e8c31dc6a6d0d61591f4618ee353676b0ac8fa30c771a9b33585647d1863b8d4d95ac2b23e8c31dc6a6c8d61591f4618ee353636b0ac8fa30c771a9b0b585647d1863b8d4d81ac2b23e8c31dc6a6bed61591f4618ee3535e6b0ac8fa30c771a9ae3585647d1863b8d4d6dac2b23e8c31dc6a6b4d61591f4618ee353596b0ac8fa30d678ee353575647d18000c771a9abab23e8a31dddd8d4d5d591f4618ee4d46a6aeac8fa30c771a9ac3575647d186b0c771a9ab2b23e8c33de3b8d4d59591f4619cb1dc6a6acac8fa30
  else (if i < 61 then
  0xc771a9bfb585647d1863b8d4df9ac2b23e8c31dc6a6f8d61591f4618ee3537b6b0ac8fa30c771a9bd3585647d1863b8d4de5ac2b23e8c31dc6a6f0d61591f4618ee353776b0ac8fa30c771a9bb3585647d1863b8d4dd5ac2b23e8c31dc6a6e8d61591f4618ee353736b0ac8fa30c771a9b93585647d1863b8d4dc5ac2b23e8c31dc6a6e0d61591f4618ee333706b0ac8fa30c77189b83585647d1863b8bcdc1ac2b23e8c31dc6a6ded61591f4618ee3536e6b0ac8fa30c771a9b6b585647d1863b8d4db1ac2b23e8c32346a6d6d61591f4618ee3536b6b0ac8fa30
  else
  0xc771a9ccb585647d1863b8d4e59ac2b23e8c31dc6a72ad61591f4611aa2a3956b0ac8fa30c771a9ca3585647d1863b8d4e4dac2b23e8c31dc6a724d61591f4618ee353916b0ac8fa30c771a9c83585647d1863b8d4e3dac2b23e8c31dc6a71cd61591f4618ee3538d6b0ac8fa30c771a9c63585647d1863b8d4e2dac2b23e8c31dc6a714d61591f4618ee353896b0ac8fa30c771a9c3b585647d1863b8d4e19ac2b23e8c31dc6a70ad61591f4618ee353846b0ac8fa30c771a9c1b585647d1863b8d4e09ac2b23e8c31dc6a702d61591f4618ee353806b0ac8fa30)))
  else (if i < 65 then (if i < 63 then
  0xc771aa103585647d1863b8d507dac2b23e8c31dc6a83cd61591f4618ee3541d6b0ac8fa30c771aa0e3585647d1863b90b06dac2b23e8c31dc6a836d61591f4618ee3541a6b0ac8fa30c771aa0cb585647d1863b8d4e8dac2b23e8c31dc6a744d61591f4618ee353a16b0ac8fa30c751a9d0b585647d186348d4e85ac2b23e8c31dc68742d61591f4618ee333a16b0ac8fa30c77189d0b585647d1863b8bce85ac2b23e8c31dc6a740d61591f4618ee3539f6b0ac8fa30c771a9cf3585647d1863b8d4e75ac2b23e8c31dc6a738d61591f4618ee3539a6b0ac8fa30
  else (if i < 64 then
  0xc771aa183585647d1863b8d50bdac2b23e8c31dc6a85cd61591f4618ee3542d6b0ac8fa30c771aa163585647d1863b8d50adac2b23e8c31dc6a854d61591f4618ee354296b0ac8fa30c771aa143585647d1863b8cd0a1ac2b23e8c31dc62850d61591f4618ee2f4286b0ac8fa30c771aa13b585647d1863b8d5099ac2b23e8c31dc6a84ad61591f4618ee354246b0ac8fa30c831aa11b585647d1863b8d508dac2b23e8c35c63b844d61591f4618ef04c226b0ac8fa30c7726a113585647d1863b8d5089ac2b23e8c31dc54844d61591f4618ee354216b0ac8fa30
  else
  0xcdd8ee2a3585647d1863bc0d151ac2b23e8c31ddd98a8d61591f4618eee44546b0ac8fa30c7725a2a3585647d1863b90b151ac2b23e8c31dc788a8d61591f4618ee354546b0ac8fa30abf1aa2a3585647d1863b8cd151ac2b23e8c31dc628a8d61591f4618ee2f4546b0ac8fa30c771aa28b585647d1863b8d50f1ac2b23e8c31dc6a876d61591f4618ee3543a6b0ac8fa30c771aa1cb585647d1863b8d50e1ac2b23e8c31dc6a86ed61591f4618ee354366b0ac8fa30c771aa1a3585647d1863b8d50cdac2b23e8c31dc6a864d61591f4618ee354316b0ac8fa30))
  else (if i < 66 then
  0xcf78ee2f3585647d18672c77179ac2b23e8c33763b8bcd61591f4600031dc5e6b0ac8fa28c778262f3585647d1863bbbb179ac2b23e8c31dddb8bcd61591f4618eeb5c5e6b0ac8fa30c7726a2f3585647d1863b923179ac2b23e8c31dc6a8bcd61591f4619971dc5c6b0ac8fa300018ee2e3585647d1463b8d5171ac2b23e8c330e3b8b6d61591f4600031dc5b6b0ac8fa28c771aa2db585647d1863b8d5165ac2b23e8c31dc6a8b0d61591f4618ee354576b0ac8fa30c771aa2b3585647d1863b8d5155ac2b23e8c346e3b8a8d61591f4619df1dc546b0ac8fa30
  else (if i < 67 then
  0xc77776333585647d1863bad7199ac2b23e8c31dc9a8ccd61591f4618ee354666b0ac8fa30d618ee313585647d1869cc77189ac2b23e8c34963b8c4d61591f4619ef1dc626b0ac8fa30cef8ee313585647d18672c77189ac2b23e8c00063b8c4d61591f4518ef04c626b0ac8fa30c77776313585647d1863bbab189ac2b23e8c31dd6b8c4d61591f4618ee4d4626b0ac8fa30c77262313585647d1863b8d5189ac2b23e8c33ae3b8c0d61591f4600031dc606b0ac8fa28c771aa303585647d186b0c77179ac2b23e8c34e63b8bcd61591f461a4b1dc5e6b0ac8fa30
  else
  0xc771ca353585647d1863b8e31a9ac2b23e8c31dc708d4d61591f4618ee3746a6b0ac8fa30c771b6353585647d1863b8d91a9ac2b23e8c31dc6b8d4d61591f461ac31dc696b0ac8fa30cf78ee34b585647d18672c771a5ac2b23e8c00063b8d2d61591f4518ee354696b0ac8fa30d558ee343585647d18000c771a1ac2b23e8a31dd6b8d0d61591f4618ee354686b0ac8fa30d398ee333585647d18692c77199ac2b23e8c346e3b8ccd61591f4619ef1dc666b0ac8fa30ce58ee333585647d18000c77199ac2b23e8a31de098ccd61591f4618ef024666b0ac8fa30)))))
  else (if i < 79 then (if i < 73 then (if i < 70 then (if i < 69 then
  0xc77236353585647d1863b9191a9ac2b23e8c31dc8b8d4d61591f4618ee4546a6b0ac8fa30c77226353585647d1863b9111a9ac2b23e8c31dc878d4d61591f4618ee4346a6b0ac8fa30c77216353585647d1863b9091a9ac2b23e8c31dc838d4d61591f4618ee40c6a6b0ac8fa30c77202353585647d1863b8ff1a9ac2b23e8c31dc7e8d4d61591f4618ee3e46a6b0ac8fa30c771ee353585647d1863b8f51a9ac2b23e8c31dc798d4d61591f4618ee3c46a6b0ac8fa30c771de353585647d1863b8ed1a9ac2b23e8c31dc748d4d61591f4618ee39c6a6b0ac8fa30
  else
  0xc77562353585647d1863baaf1a9ac2b23e8c31dd568d4d61591f4618eeaac6a6b0ac8fa30c77552353585647d1863baa71a9ac2b23e8c31dd518d4d61591f4618eea846a6b0ac8fa30c7753e353585647d1863ba9d1a9ac2b23e8c31dc9c8d4d61591f4618ee4dc6a6b0ac8fa30c7726a353585647d186399351a9ac2b23e8c31bc9a8d4d61591f4618ee4cc6a6b0ac8fa30c77262353585647d1863b92f1a9ac2b23e8c31dc968d4d61591f4618ee4a46a6b0ac8fa30c7724e353585647d1863b9251a9ac2b23e8c31dc918d4d61591f4618ee4746a6b0ac8fa30)
  else (if i < 71 then
  0xc77712353585647d1863bb871a9ac2b23e8c31ddc28d4d61591f4618eee0c6a6b0ac8fa30c775b6353585647d1863bad91a9ac2b23e8c31dd6b8d4d61591f4618e6b5c6a6b0ac8fa30c695ae353585647d1863bad51a9ac2b23e8c31dd698d4d61591f4618eeb446a6b0ac8fa30c7759e353585647d1863bacd1a9ac2b23e8c31dd648d4d61591f4618eeb1c6a6b0ac8fa30c7758a353585647d1863babf1a9ac2b23e8c31dd5e8d4d61591f4618eeaec6a6b0ac8fa30c77572353585647d1863bab71a9ac2b23e8c31dd5a8d4d61591f4618eeacc6a6b0ac8fa30
  else (if i < 72 then
  0xc7777a353585647d1863bbbb1a9ac2b23e8c31d5dd8d4d61591f4618deeec6a6b0ac8fa30c77772353585647d1863bbb71a9ac2b23e8c31ddda8d4d61591f4618eeecc6a6b0ac8fa30c7775e353585647d1863bbad1a9ac2b23e8c31ddd58d4d61591f4618eee946a6b0ac8fa30c77746353585647d1863bba11a9ac2b23e8c31ddcf8d4d61591f4618eee746a6b0ac8fa30c77736353585647d1863bb991a9ac2b23e8c31ddcb8d4d61591f4618eee546a6b0ac8fa30c77726353585647d1863bb911a9ac2b23e8c31ddc78d4d61591f4618eee346a6b0ac8fa30
  else
  0x18de353585647d146aac691a9ac2b23e8c31de348d4d61591f4600031a46a6b0ac8fa28c778c2353585647d1863bc1b1a9ac2b23e8c31de0b8d4d61591f4618ef0546a6b0ac8fa30c77826353585647d1863ac131a9ac2b23e8c31ce098d4d61591f4618ef0446a6b0ac8fa30c7781e353585647d1863bc0d1a9ac2b23e8c31de048d4d61591f4618ef00c6a6b0ac8fa30c77802353585647d1863bbff1a9ac2b23e8c31ddfe8d4d61591f4618eefec6a6b0ac8fa30c777f2353585647d1863bbf71a9ac2b23e8c31ddfa8d4d61591f4618eeefc6a6b0ac8fa30)))
  else (if i < 76 then (if i < 74 then
  0xcbd8ee353585647d1864ac771a9ac2b23e8c324e3b8d4d61591f4619231dc6a6b0ac8fa30c8f8ee353585647d18646c771a9ac2b23e8c322e3b8d4d61591f4619131dc6a6b0ac8fa30c878ee353585647d18642c771a9ac2b23e8c320e3b8d4d61591f4619031dc6a6b0ac8fa30c7f8ee353585647d1863ec771a9ac2b23e8c31ee3b8d4d61591f4618f31dc6a6b0ac8fa30d738ea353585647d1863bc751a9ac2b23e8c00063a8d4d61591f451ae31cc6a6b0ac8fa30c778e6353585647d18000c731a9ac2b23e8a359e378d4d61591f4618ef1bc6a6b0ac8fa30
  else (if i < 75 then
  0xd258ee353585647d18691c771a9ac2b23e8c34863b8d4d61591f461a3f1dc6a6b0ac8fa30d1d8ee353585647d1868dc771a9ac2b23e8c33e63b8d4d61591f4619ef1dc6a6b0ac8fa30cf58ee353585647d18679c771a9ac2b23e8c33c63b8d4d61591f4619df1dc6a6b0ac8fa30ceb8ee353585647d18674c771a9ac2b23e8c339e3b8d4d61591f4619cb1dc6a6b0ac8fa30ce38ee353585647d18670c771a9ac2b23e8c337e3b8d4d61591f4619bb1dc6a6b0ac8fa30ccb8ee353585647d18664c771a9ac2b23e8c330e3b8d4d61591f4619831dc6a6b0ac8fa30
  else
  0xc778263c3585647d1869cc771b9ac2b23e8c3396468d4d61591f4619ef20c6a6b0ac8fa30d258fa353585647d1869cc7b1a9ac2b23e8c35ce3b8d4d61591f461ae31dc6a6b0ac8fa30d6f8ee353585647d186b3c771a9ac2b23e8c35963b8d4d61591f461ac71dc6a6b0ac8fa30d618ee353585647d186abc771a9ac2b23e8c35563b8d4d61591f461aa71dc6a6b0ac8fa30d518ee353585647d186a7c771a9ac2b23e8c35363b8d4d61591f461a731dc6a6b0ac8fa30d378ee353585647d1869ac771a9ac2b23e8c34ce3b8d4d61591f461a631dc6a6b0ac8fa30))
  else (if i < 77 then
  0xc778263539c5647d1863bad71a9ce2b23e8c34963b8d4e41591f4600031dc6a71eac8fa28c771aa2a38f5647d1863bad71a9c5ab23e8c34963b8d4da9591f4600031dc6a6d2ac8fa28c77826353655647d18692c771a9ae2b23e8c31de06bbad61591f4618ef04dd96b0ac8fa30d398eee63585647d18000c7772dac2b23e8a31de06934d61591f4618eeecc9a6b0ac8fa30c777224d3585647d1863bc13259ac2b23e8c31dddd92cd61591f461a731dc896b0ac8fa300018ee443585647d1463bbbb215ac2b23e8c34e63b8f8d61591f4600031dc7b6b0ac8fa28
  else (if i < 78 then
  0xc7758a353586087d1863b9231a9ac3043e8c31dc6a872d61821f4618eeb5c6a6b0becfa30c7726a353585f67d18672c771a9ac2e63e8c31dc9a8d4d61721f4600031dc6a6b0b84fa28c771a9ac3405c27d18672c771a9ac2d83e8c31dd6b8d4d616b1f4600031dc6a6b0b4cfa28c771aa2a3585a67d18672c771a9ac2b83e8c33de3b8d4d615a9f4600031dc6a6b0ad4fa28c77812b5c6a5647d1863bc1359a352b23e8c34963bab51a9591f4600031dd598d4ac8fa28c77566354545647d1863bc091a9d0ab23e8c31dd668d4e85591f4618eeaac6a742ac8fa30
  else
  0xc771a9d0b585fcac9867bc771a9ac2f1564c31dc6a742d61782b2600031dc6a6b0bb55928c771aa2a3585daac9863b8d4d6176ab2540c31dc6a6b0bb559282618ee353585daac93f30cf78ee35358564811863bbbb1a9ac2b2406c00063b8d4d6159200518ee35358680ac90030c771a9ac2b2540801867bc771a9ac2b23f4c33963b8d4d61591f7600031dc6a6b0ac8fba8c7758a4d46a6b07d1863bad7246353583e8c33963b8d50edac1f4600031dc6a868d60fa28c771aa2a4346b07d1863b8d50d1ac3403e8c31dc6a868d618a1f4618ee354346b0c24fa30))))
  else (if i < 85 then (if i < 82 then (if i < 80 then
  0x11a9ac2b23da0ed4800850d61591b3076a4003706b07d0d983b5200163ab23e86cc1da90011a9d0ab23260ed4800bbad61590e0076a40056b8d47d04103b52002353586081801da90011b9ac2b23e80e548008d4d71591f4070a40046a6b0ac8fd03552002353585707d018a9c77756353a16b0ac9863bbbb1a9ccb58564c33de3b8d4e0dac2b2600031dc6a6f8d615928c771aa2a37c6b0ac9863b8d4df1ac340564c31dc6a6f8d618a2b2618ee3537c6b0c255930c7775635358608ac9863b8d4e65ac304564c31dc6a702d61822b2618eeeec6a6b0bf95930
  else (if i < 81 then
  0x18ee353585fc1814800c771a9ac2fb0c0a40063b8d4d617b060520031dc6a608b1c30290018edac30436618148008d4d61591f40b6a40063b628ac8fa05752002354286e0d601da90011aa142c75640ed48008d4dc1639f4076a40046a6b0ac8fa03b52002333585647d01da9001189ac2b23e80ed48008bcd61591f4076a40046a6a8ac8fa03b52002353505647d01da90011a9a62b23e80ed4800c12c51591f4076a40046a6b0ac0fa03b520023535855c7d01da90011a9ac2ab3e80ed4800934d61411f4076a40046a6b0ac8f903b52002353585647c01da9
  else
  0x11a9d0b9556464d4800c771a959279326a40063b742ac8d999352002353585647d0c8290018edac2823e86294800c771a9782b21d0a40063bbbadc1ac0e0520031ddd96b0ac870290018eeeab585643814800c7773dac2b21c0a4005ddb9ed61590e0520031dddd58eac870290011a9ac2b23e836d4800c76d61721f4114a40063bad71aa14082520031dd668d47d041290018eeb146a3e82094800c7757e351f4104a40056babf1a8fa082520031dd6b3e86cc41290018ee351f41ae20948008d4d61591f40fea40063b6b0ac870079520031dc6a6b0c343029))
  else (if i < 83 then
  0x18ee142c75646cd4800c76dc1639f4366a40063b6b0ac8fa1b352002ff3585647d0d9a900173dac2b23e86cd4800abed61591f4366a40048c6b0ac8fa1b352001cab585647d0d9a90018edaa2b23e86cd4800c76d41591f4366a40063b698ac8fa1b3520031db585607d0d9a90018edac2ae3e86cd4800c76d61559f4366a40063b6b0ac8f91b3520031db585647c0d9a90018edac2b23da6cd4800c7ad61591f435ea40063b6caac8fa1a7520031db5856480ccda90018ee353a16e064d4800c771a9ce2b2326a40063b8d4e6559193520031dc6a72aac8c9a9
  else (if i < 84 then
  0x18ee353585647c14800c77199ac2b23e0a40063b8d4d01591f0520031dc6a58eac8f8290018ee3535855c7c14800c771a9ac2b23dca40063b8d4dc1ac1ed520031dc6a6b0ac8f6a90018ee2f3585647b54800c771a9a62b23daa40063b8d4b1d591ed520031dc6a6b0a80f6a90018ee353585647ad4800c771a9ac2b23d4a40063b8c4d61591e2520031dc6a6a0ac8f1290018ee3535855678948008bcd61591f43c4a40046a698ac8fa1e2520031dc6a702d60eb290018edac2b23e86d94800c76d61591f436aa40063b6b0ac8fa1b4520031dc286e0d60d9a9
  else
  0x18ee313585567d14800c771a9a82ab3e8a40063b8d4b1d559f4520031dc6a6b0aa4fa290018ee353585507d14800c77179ac2a03e8a40063b8d4d31501f45200231358564a80fa290011a9a82b25407d14800c771a96b28a3e8a40063b92cd61411f4520031dc916b0a08fa290018ee463585047d14800935231ac2823e8a40063b934b1d411f452002353585649f4fa290018ee353585647cd4800c771a9b83583e4a40063b8d4d61591f2520031dc546b0ac8f9290018ee353545647c94800c771a963ab23e4a40063b8d4d61581f2520031dc6a6e0d60f829)))
  else (if i < 88 then (if i < 86 then
  0x18ee352c95647d14800c771a9642b23e8a40063b8d4b1d591f452002ff46a58eac8fa2900173e352c75647d14800abf1a963ab23e8a40048c8d4b1d591f4520031dc6658eac8fa290018ee312c75647d14800c7717963ab23e8a40046a72ab1d591f4520031f46a586ac8fa290018ee3c2bc5647d14800c771a9ac2b13e8a40063b8d4d61581f4520031dc546b0ac0fa290018ee353545607d14800c771a963ab03e8a40063b8d4d61571f4520031dc666b0ab8fa290018ee3534055c7d14800c771a963aae3e8a40063b8d4d61561f4520031dc6a6b0aacfa29
  else (if i < 87 then
  0x11aa18b585647d148008d4e55ac2b23e8a40046a71ad61591f4520023537a6b0ac8fa290011a9bcb585647d148008d4d9dac2b23e8a40063b8d4d5d591f4520031dc6a6acac8fa290018ee353545647d14800c77151aa2b23e8a40063b8d4d41591f4520031dc626a0ac8fa290018ee3534e5647d14800c771a9a62b23e8a40063b8bcd31591f4520031dc6a694ac8fa290018ee353495647d14800c77199a02b23e8a40063bc0cc51591f4520031de04628ac8fa290018eeff3145647d14800c137f98a2b23e8a40063bc12be1591f4520031dc6a594ac8fa29
  else
  0x1992353585647d14800c8b1a9ac2b23e8a4006408d4d61591f4520031d46a6b0ac8fa290018e6353585647d14800c6f1a9ac2b23e8a4006348d4d61591f452002ff46a6b0ac8fa2900173e353585647d14800b891a9ac2b23e8a40055f8d4d61591f452002abc6a6b0ac8fa29001232353585647d148009031a9ac2b23e8a4004748d4d61591f4520031dc696b0ac8fa290018ee343585647d14800c77199ac2b23e8a40063b8c4d61591f4520031dc606b0ac8fa290018ee2f3585647d14800c77171ac2b23e8a40063b8b6d61591f452002354326b0ac8fa29))
  else (if i < 89 then
  0x1232353706b07d14800c77199b83583e8a40063b8c4dc1ac1f4520031dc5e6e0d60fa290011a9cab706b07d148008d4de9b83583e8a40063b8d4db5ac1f4520032346a6d6d60fa290018ee353706a87d14800c771a9b83503e8a40063b8d4dc1a61f4520031dc6a716cdcfa290018eee43586547d14800c77825b83143e8a40063b8d4d61709f4520031dc6a6b0b4cfa290018ee3535856a7d14800c77566352b23e8a40063b8d4e3d591f4520031dc6a6d2ac8fa290018eee5b585647d14800c77221ac2b23e8a40063b8f6d61591f4520033a46a6b0ac8fa29
  else (if i < 90 then
  0x18ee354286a8ac94800c771aa14350564a40063b8d50a1a62b2520031dd558d4c8159290018ef04c28628ac94800c771a9ac2ed564a40063b8d50a1ac2b0520031dc6a850d6157290018ee354286b0aad4800c771aa1cb58528a40063b9350a1ac282520031dc6a6b0ac900290018ee353585647dd4800c7773ab5c6a3e8a40063b8d50d1ac1f4520031dc9a724d60fa290018ee353736b07d14800c771a9b93583e8a40063b8d4dc5ac1f45200322c6a6e0d60fa290018ee353706b07d14800bfd1a9b83583e8a4005cf8d4dc1ac1f452002afc6a6e0d60fa29
  else
  0x63bbf71a9ac304520031dc6a850dc163a90018ee45c6a742ac94800c77776ae358564a40063b8d50adac2b2520031dc6a854d6159290018ee354296b0ac94800c811aa14358564a40063b8d50a1ac2b252002ff46a850d61592900173e354286b0ac94800abf1aa14358564a40048c8d50a1ac2b2520031dc66850d6159290018ee314286b0ac94800c7717a14358564a40046a8650a1ac2b2520031dc6a84ad615929001906354236b0ac94800c772160db58564a40046a850e55ac2b2520031dc6a6f8d615929)))))))

private def st5 (i : Nat) : Nat := unpack st5Packed 73 24 i

private def adj5Packed (i : Nat) : Nat := (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0x1c200000100e0890040081820892060804820000c20000c000724200010034000f048 else 0x50030430150011560440040c40470830813811c0000040101383004084042000000) else (if i < 3 then 0x20100710008400010104124405e0050802410031cc00708c2800030402c13011c2001086 else 0x318210308400138040000020e0010011000880020c000c00200124508a003004082001)) else (if i < 6 then (if i < 5 then 0xc00402491400410c404100100e08100a00100000000020d2814400000410090000400c1 else 0x400c00030001001c11c00020d61010c02c60012400040040101c0001000000041002007) else (if i < 7 then 0x30c20400800400000c7000082006000004080040003002048001045180042 else 0x2411031830400cf0042821d710304114708a04104008000b0831c11c03400400010001d7))) else (if i < 12 then (if i < 10 then (if i < 9 then 0x3384180000200003040087004041040001080001000000081187602203008051010144 else 0xc00420410c200228f0001030020012e00411000000810420c00010090953c4080000204) else (if i < 11 then 0x1021820015410c10c00c010004900104300010124004a00100100201b4000c00000c5005 else 0x18500600300114004204308104c00804208714018104b0000c52021410434050440c4040)) else (if i < 14 then (if i < 13 then 0x800090c30c100300204f00800f0050c008110014200520000000100d0c114a005040 else 0x810000820d000000000028210d0d500000004028300000c00c00008700000050b005041) else (if i < 15 then 0x10014a0010031c00040010870020000071001020460440011400012c7002003044081003 else 0x401860c22c1001184))))

private def adj5 (i : Nat) : Nat := unpack adj5Packed 6 48 i

private def loc5Packed (i : Nat) : Nat :=
  (if i < 69 then (if i < 34 then (if i < 17 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0x5b61e67be00035d1586000003382ee00034f6b100000014a3e06180004d93c64be224499 else
  0x4b100087471536512d1120000000006b724f03639e2930003e74e987e06154f000) else (if i < 3 then 0x5ca4d16d820b0001df7e532f0000b71e812f0000000004525ba0006604ad62e43d09a else 0x5620e545b0004512df80a6680000006c701d00006322d23300025b00f000378)) else (if i <
  6 then (if i < 5 then 0x67536068d4e30000c749c0002600008402ae0000003e54a700075c11d0f108343c66106c else 0x37900076831e46e1990000008254e868f38f11300000045525c49e1d21564b66d3000197) else (if i < 7 then
  0x40059b8550000000dc2c00002f150b0004a80001ff0002586d432110e3cc060604000118 else 0x5456a80000003770001598311656526980001c30223261ae0000000006d748d000))) else (if i < 12 then (if i < 10 then (if i < 9 then
  0x69432200000000000015e51529a5530000005662d37b51f80000175b28636236ec00003a else 0x51d4ee7eb0000ee51b11f4f200027a1ed5310000ca4ff00000073a0000142f27ae17b736) else (if i < 11 then
  0x3ec0000d904330f5b087d0000000000006620004231cf7de000000000000724090468000 else 0x31d02f1e20000000004a235b3e400000013b0000000000004e20001d907818b00082e000)) else (if i < 14 then (if i < 13 then
  0xf881b00046604440a34a6670007bf49d4b08700000a502476e00014c2866af23b58e1f9 else 0x24200000030c00060840c0000000007b05b90000001740000006ed42c505000872) else (if i < 15 then 0x7470000e82ce0007fb7fd0004cc02c3580000000ae0001434382557f7486000537000 else
  (if i < 16 then 0x27400019c2dd25f4c92080007f00002506502310dd4714250007000850002f00008485a1 else 0x3610000000233328202300005d82020000005c900058f0006cf00054621e0006952ba))))) else (if i < 25 then (if i < 21 then (if i < 19 then (if i < 18 then
  0x10c00041c57b5f30970007893b82f728f0002071100002d086b0002af1bd60a1f61af2b0 else 0x7d600066975516900062a0007410000002d20002a722100000042221a0000005b767b) else (if i < 20 then 0x6294a60003236bd23d39a7e000058a61e6650007846192251705540003343c52d6000000
  else 0x7465e300000000012608283f36776a7d046d64a7540000000001b317a3020e300014d)) else (if i < 23 then (if i < 22 then 0x31c44334231067300000000037400084e53e3090000000317ad6eb83c57f75a865000000 else
  0x2296bb3840004090004a900000078a10d0ec0005fa000000000246000000215179) else (if i < 24 then 0x29448c00005616800055b0005d97c10002bf5f60008850005d556a5f2285846376 else 0x5ab25700000031f81000044a15f0002e778d8260000007775406360000004906e272e3df))) else
  (if i < 29 then (if i < 27 then (if i < 26 then 0x86d1b818e29200000027f0040e048570238e2ec0001f142e7d30000001807530005b10ad else 0x27d0006e42fc0001c90000f90005f519819d0000001de02187645300028d4302a62793fd) else (if i < 28 then
  0x49371c00000033000000000064400044200070e0000712b50000703850004c5000688041 else 0x8396101b91d63a51b70005d07c200010260740883d00002b000838133)) else (if i < 31 then (if i < 30 then
  0x45d65784c4d80007013500fe43200000000050660d0001c170d6ee3a60000007d8000020 else 0xc187c76700000000000000024b54e3620187792d450933a0004ba722000000153000) else (if i < 32 then 0x59a2a977600000000073752d0000002697218020001957325a848900000000052e561178
  else (if i < 33 then 0x4110000b45ed18d7390005590001a12145e21e069a00004b5da000319000797428 else 0x38978f00046536887f0000006f36280000000000003cf7696920002352882893fb852000)))))) else (if i < 51 then (if i < 42 then (if i < 38 then (if i < 36 then (if
  i < 35 then 0x45f20e0000004f06b83f91c55f91dc8290000007ba2067e382d7312840001e7786000 else 0x67600000000015427c0007a25d460b05d1144c80000005363aa3982040000007da55d4a5) else (if i < 37 then
  0xeb1a90008710000004922ac1f38077d26ba0000005e66584e60005b831180900064d000 else 0x40f41b47b05c11a00009307a21344d0005517091850007c91847dd0a270f00044732c)) else (if i < 40 then (if i < 39 then
  0x5c70000000060001c83f300046206e4ed30408d01b00056800000038a34c7ee0000000ef else 0x6720006c65811a70000003fa12e2c870c00062615a8835e50006db7ed000271000139678) else (if i < 41 then
  0x7cd42b2013881d51ba41666f80f8231240540000008580001b00005bc7f24af00085c000 else 0x66b3ae37b53003d61707684550d2aa5384330953f14774127741a060532e00033c00019a))) else (if i < 46 then (if i < 44 then (if i < 43 then
  0x58300000011b0c45753ac1753444782730005030002a87b96f763c3f54f62be2810f02eb else 0x52c00077a0162224630003b272300000000072b0000000001ea1e1313382518816000000) else (if i < 45 then 0x49827e6be0000110000000000002100007a665e6930002c65e07b187980d000843
  else 0x3e60332db2fd5902d71dd86c0663b77b822878c4d50000005c50000002383da000119)) else (if i < 48 then (if i < 47 then 0x460000007f44ce69100c0cf6ae7720190004757ef01f3f00397384e724c00026a000 else
  0x2ea3bb53253f0005c000000000000055f00061f0003a90582660001ca173000216631577) else (if i < 49 then 0x37c0000000006d519600000080400000079813a1600c30000006b20000006f43010993ef else (if i < 50 then
  0x33771752a5c621d83710767100000076c41f00000008c0002680000005bf29c0003a7166 else 0x13c08153959465a84a72500016485e7cb0007e717200010400065f3ee29b0001d7000000))))) else (if i < 60 then (if i < 55 then (if i < 53 then (if i < 52 then
  0x790006ef65d06827518858000054757100013f6153de0000003a12bd00000000073c176 else 0x7ff3fc3e97646fd00000007e0006470bf5dd0002807340006ff1d352477b000684578000) else (if i < 54 then
  0x2a175f00062126b0b945e4356de37d0000001c20727c082b7950f20007033d000000080e else 0x52b00049500000000000054331b5dc00007c1490870000002b27192a210b000069000)) else (if i < 57 then (if i < 56 then
  0x3d72972707f53d66802376890004450d000000000018900000026e00000069d0007ce6f6 else 0x1414f52d50000003c757c5968146254961810006c800000000019f7490001031d03e2000) else (if i < 58 then 0x8f00051600057084981e0fb0000001da1ec43487a15739f0002611c600000015248b
  else (if i < 59 then 0x43f40200009c0007815e804c3bc00087b81100035f1e300087800035423c0003d82ca000 else 0x3eb28b8170000002fa0000005744fb4140000006200b585d1b128e34e0003be0105d76ea)))) else (if i < 64 then (if i < 62 then (if i < 61 then
  0x35c12700034b0001bf0008010000001463200000001c400041d5af0004dd0001480003b5 else 0x64600000000b12802e4910002b100039b0004f181500000000003867d0f477538063533b) else (if i < 63 then
  0x7450007a36e76da68e000000000000444000353073348706000000459683000000000000 else 0x33e0000006b30005600006a00450000891b46e529f54450c69b0000ab1f012b4a4000)) else (if i < 66 then (if i < 65 then
  0x3c40005970000004f461c3003150000007e43ab0cb0006875cc5c10000000006b97080c2 else 0x35a8845580000000000005ea1b20006cb4f93f80000008344d73663d9032720227000) else (if i < 67 then 0x77c06f4aa5730000000000000003572055126411610000002b907d05e00042d53d5341ef
  else (if i < 68 then 0x2ad4bc00007700043988263700000074479e0001000000000000082e07c6446000842697 else 0xa07b32c20006a33976430000000000d40003f77485796f00005b48190007626d60003f2))))))) else (if i < 103 then (if i < 86 then (if i < 77 then (if i < 73
  then (if i < 71 then (if i < 70 then 0x29505575700000067c00049f00082214544943700005000d0b37280000005c46f96a948f else 0x6380000ed63f46a38d00008b0000000b80000bd0003960003b330d6aa) else (if i < 72 then
  0x36400000068b0003d100062b1250000004df0d83ce17139331400036c5bd51c000000000 else 0x1942fe75100000016b3c10000000007b70ea73e0e93f62d900063b6421a44fc5e7000000)) else (if i < 75 then (if i < 74 then
  0x8614fa00033576b7141fe00003f0ba0ff2994847182ed06a8620e4000588000 else 0x5a035e86a3c00006c300081800016f53a2de00000078557a46b0530000001b5000290) else (if i < 76 then 0x5ac00042600038b0000000000000cc0001932523275fb7b21151ab0000000000004fe3a3 else
  0x753bf0861093870000002980d11060002cf0002c919138600071d26382a20d59c000525))) else (if i < 81 then (if i < 79 then (if i < 78 then 0x36f6133af5232f618300081d54120f00000024a6270005cb76000010561b2d800064b500 else
  0x7c86cc0000000007350000c60000001fd1f41380000f76d080c5081e9340) else (if i < 80 then 0x1cb00035271260e7331bb00027b22e4945bb2f45a977f0000005824130001670005db3a4 else 0x64f00058b35682c0005de0006e86fc0000000000000003160c06a10002207297bd5c2000)) else
  (if i < 83 then (if i < 82 then 0x960000d67e160182f56d6f16e00805985112b64ea6c4529 else 0x628542623360001bc0001820000000000003070fc5690006c571062f2bb46c000000) else (if i < 84 then
  0x7bb0d70000030c878b79a0000000000001323b67d556e3b02cb1fb67425d00056c7ea000 else (if i < 85 then 0x74d4da03742057d8067e801c00003e87314467a7882d10000a10000000004214ef7c5796 else
  0x3b90000002fb2cd37000566c34100000084d3d41a600000000055e71f85a24331a750655))))) else (if i < 94 then (if i < 90 then (if i < 88 then (if i < 87 then 0xa96a56660e255683556f0008530000000000000000000004cd851308000218000000 else
  0x3ea1230001345ad39941551f0000003d500023a0003a047e00078323f00033115c09e6dc) else (if i < 89 then 0x4d20000005a24f800000077e64c13d0000006e33a84e40da7aa3c95cd0000004cb000000 else
  0x18f0000000000005670000003a27c30004360a700054235112c00000000000046f4d3000)) else (if i < 92 then (if i < 91 then 0x75d09167e5f85070000005334571350000b15523ad0000000d30590001ad2e100048239c else
  0x520000a84e15174c158609d0000e13ca68147647c00047931744058c000000000000) else (if i < 93 then 0x56485b0006e162200000048100046049700001e00025a6d22c16114670004a329e000108 else
  0x3db18700000000000001a0004b421c00074f7f105161a6bf5be8676965276ca0000004b5))) else (if i < 98 then (if i < 96 then (if i < 95 then 0xbe65c6990018006533910006fe5e40000000000340e70000006fb00081c80372c7715df else
  0x3dc47a5f45c379b0000008360000000000000000005727d90002cc419142000000793000) else (if i < 97 then 0x5721b18a61422b06d2dc1865500150000008330005021a81e533d72a3cd0b68756c0592 else
  0x7ac00000000000023244c6ac27271a7c40004c659e5fd7f63465c821747d0000002f9000)) else (if i < 100 then (if i < 99 then 0x3c343b78000000000078743a00021275971304d16a0000002da00072d7e24c300000042f else
  0x6595d20004c04a059d77300000049b8474de7114f30004730000000f30008595fc6df75e) else (if i < 101 then 0x2440000006455a366a00035500000007f83e00000077008414b0000670090003734bb73b else (if i < 102 then
  0xa402647f5ef00078e57e0000000ac2c44502ef000129000000624000363000000 else 0x69e5480400003c26776ce6a200019225100020a45c3b160f11c7dc000000)))))) else (if i < 120 then (if i < 111 then (if i < 107 then (if i < 105 then (if i < 104 then
  0x35900022f0000ce4a17a77260000003181d400054b0001cc2967a400000051a79f3d3000 else 0x54a0000005f72670006825cf0000fa1515144247914dc2540001a34c400000000069c) else (if i < 106 then
  0x24954d00000055700039d0006ab40420313000000041e0004d60004580745b5461799792 else 0x1500008280000006a404800048e38326534576176f36b1ee00003c17c000000000704805)) else (if i < 109 then (if i < 108 then
  0x4740000f64480497275fe00000a00027677d00075b7f958700026478284f2260006cd0bb else 0x73d34d09824030a0002c758953c0d22e429179d52f5ae0137b400042a00011e464758) else (if i < 110 then 0x84486025e4eb37200000023e4417af2ab6854b984b00052600000055a000 else
  0x13e00050a00000000000000036e62c00058d00056b0000424e06f532a6337e60005d6))) else (if i < 115 then (if i < 113 then (if i < 112 then 0x68a1f56e65850000003240000007df6902e20000000007ab1201406320c539000042945a else
  0x34740574000071e2c500000033300020016c5e14c228704711600023403b343654000000) else (if i < 114 then 0x15b5e904a0925913e36f816e50483284105b3690004313ff83000000032828c1b674e000 else
  0x26d13163410175224d2e53e100065673f5190de0000000001fc8500003ed2a060330e256)) else (if i < 117 then (if i < 116 then 0x7f32f300071b0001f78137a028a00082440700059354c1a25630000007a93390000006b0 else
  0xaa0004ac0007780000a61d10006024560000b044b03038c4885490007ec0000e62bc000) else (if i < 118 then 0x4ca00000040d00086919e2771ac7070002f830300037f6b4 else (if i < 119 then 0x64082100069f6d930b00008e8126a715555c4700000f52110000003dd44e0008570005a7
  else 0x44f36d00000000000061d00068637500060c7fe7db0000001eb72f3f41a54ec53b0d502a))))) else (if i < 129 then (if i < 124 then (if i < 122 then (if i < 121 then 0x2e65ee65b00000000017f32583b5767430003927a808a05a40e12200000000e4273fe else
  0x3492b80db0007940290026793b40df61200000036a0b200070b6c2395000) else (if i < 123 then 0x2390120000000000004036510000002480006f23c855562d0002230bc0004db6bc1d8742 else 0x16200060619b2c300024e0006635ec17d00067f5d30000002b34e570500076d00015d5a5)) else
  (if i < 126 then (if i < 125 then 0x49a51300032d0000c988128300000059f09b76300000016d3945d102750e7bc0004ae000 else 0x80b06500004f5f15b300014e66d00022c00058440681f7e92a37fc40104e7a55a429d630) else (if i < 127 then
  0x4f737a00087752848a0007660000000006b526c0000000880007d76d170a1cd12a6a681a else (if i < 128 then 0x6b11700017722a7f879c3810000640004c786e10f2091c74d45aa8640005f0000000000 else
  0x4fd0005100003ba5657902b70000004d086800021f19003566e18c111000522000094000)))) else (if i < 133 then (if i < 131 then (if i < 130 then 0x3124cf05f0000002e802800000027800000000032b48700048300007b0000006e941826f else
  0x1372ff53551e63e50f7561f200000085652076563d8660000a368c14f4540007ca000599) else (if i < 132 then 0x30537e0007d124782702d7c72e36482a400073020c3e80000007b60000000007a1000 else 0x5ce4170004104b825900002571674c1472190000000006496164801be74a6ad0004bf))
  else (if i < 135 then (if i < 134 then 0x1fa41a00000083a0001e463a00046900010a0000002e91db0008087d41360074b3639000 else 0x64e5eb0005a68807cc50100033f17e6fa3293060003d20cd2b45210006b62820006c174b) else (if i < 136 then
  0x3710007cf5951aa0000002f54b70000af1630000002a56dd85f86f0000000fd000000000 else (if i < 137 then 0x6702530006c90005ff4720000002454b23bd0000000003cb0000000004ab23612100040b else 0x60943e09f1ce4bd7fa2410006640001c0))))))))

private def loc5 (i : Nat) : Nat := unpack loc5Packed 12 24 i

private def edgeMeta5Packed (i : Nat) : Nat :=
  (if i < 23 then (if i < 11 then (if i < 5 then (if i < 2 then (if i < 1 then
  0x30005e40bc017802e205a40b0816002b205440a48141027204c409801290242048008c81110220042407980db0194032006080b9017002c404d808300e401c0038007000c401480210040006400880090010000400000000000 else
  0x4c2096412882490490090411c82310452088410c821804220824100820003f207c40f481e803d007a00f081e003c007800ec81d803b007440e801d003a007400e481c8039007040dc81b1036006a40d08199032206240c08180) else (if i < 3 then
  0x7800f001e003c007640e881c9038206e40d881a9034206720cc4191031206120c20180830006000c0017902e205c00b8017002e005c00b6416882c905900b0415c82b105520a8414c829105200a40144828104f209e01388269 else (if i < 4 then
  0xae215a42b085600ab215442a805500aa015242a085390a7014c429485210a321444284850109f213a827084d909a2130825c84b109521268241846b08c2114822104400856104c204840808100fb01ed03ca07900f041e003c0 else
  0xeb41d283a407410e721ca838d07110e041bc837806e90dd01ba036d06ca0d901b2036406c80d901acc351068b0ce6196c321862b0c1817e82f885f00be017c02f485da0bb017602ec05d10b8416c82d485a10b3215f02bc0578))) else (if i < 8 then (if i < 6 then
  0x12c025644a889501292250449c89311252248448c8911120423e447888db118622e4455089a1130220c43c886310c021804220832104420804100819101420043fc87f10fc41f803ec87d80fb01f283dd07aa0f341e283bd076a else (if i < 7 then
  0x15c42b805690abb15702ae055c0ab815542aa05540aa815502aa05540aa815422a2c5398a5b148628ac50989f413e027884ec89d1139226b04d409a8134226484c80989131026204c4098112f225c44b8097012e025c04b48961 else
  0x19a2332465d0cb81962328864c8c91192032246398c5b18b0316061e0c381854306860c0c1818142fe85f50bda17942ee85d88ba217322e445c10b7216c42d805b00b5916b02d605a50b4816902ccc5948b2116402c2c57d0af1)) else (if i < 9 then
  0x1ca838ec71c0e311c5238307040dfa1be237c06f80de91bc237806f00de01bc037646e88dd01b8436e46dc0db81b6236a46d40d9a1b2236406c48d811af235c46b48d681ac235646a88d491a8234e46918d191a0633c86710cd9 else (if i < 10 then
  0x20544068805100820023fc87f48fda1fa23f087d90fb01f523ea07d40f9a1f143e207c40f881ee63da47b08f601eb23d0c7990f221e403c487880f101df63be077c0eea1dd03ba07740ee81dd03ba07740ed31d763a8c7458e73 else
  0x24304860908921024204824900920023e447888e911c9238246e48d891a9235046848cc9191231246048bc917122d245848a9113b2262446c88510fa21f043a887090d921a2430885590a121164220844106c20d04168825103a)))) else (if i < 17 then (if i < 14 then (if i < 12 then
  0x27a44f409dd93b827464e649c8939026f64da89b4135a26864d009a0134026804d009a0134026804d009a0134026564c4c97d92e325964ab0949929025204a24944127a24e24988930125924a248d09181230246048a49109219 else (if i < 13 then
  0x28b05160a2c145828b05160a2c145828b05160a2c145828b05160a2c145828b05160a2c145828b05160a2c145828b05160a2c145828b05160a2c145828b05160a289450287650c4a14942828265008a0013f227e04f889f013e0 else
  0x2af055e0ab895702ac45580ab015602ab25544aa495412a7254c4a9815222a245408a8015002a0053e4a7c14f829f053a8a7414e829d05368a6c14d829b05360a6c14c3297252c4a5814a929265208a39147028b65160a2c1458)) else (if i < 15 then
  0x2d925b04b5c96b12d605ac0b5816b02d525aa0b5096992d305a60b4516812cf259e0b3516682cd05984b3016602cc05980b25963a2c6258c0b0d960a2c105820b0416082c1057b0ae615ac2b425648ac815902b205624ac4157a else (if i < 16 then
  0x312061ecc3518533076608cc0c981130126004bfc97f12fd25fa0bf417e82fd05f84bec97d82f945f20be417c12f725ee0bd897a92f505ea0bcd17982f305e60bcc17832ee45da4bb4175a2e865cacb8997022dd65b84b6c96d1 else
  0x338066e4cdc19b8337066e0cdc19b8337066c4cd819a233246608cc0197232b6650cc95991332126404c7c98f131d26384c6918d031a06340c6818c931906304c5c98b8317062c4c5498a831426264c4c189831226240c481890))) else (if i < 20 then (if i < 18 then
  0x37126e04dbc9b7136b66d0cd9c9b3136446c64d889b0235e46bc0d749ad335766ae0d5c1a9c351469e8d351a5a349468e8d189a2234326828cfd19ea33d067a0cf099e033c06748ce819d033a06740ce819d033a06740ce119c0 else (if i < 19 then
  0x3a007400e801d003a007400e801d003a0073ace699cbb3946722ce399c5438a07140e281c49388270e4e0e1c1838307044e049c0838107004e001bf237d26fa0ded1bd137a06f40de49bc137726ee0dd89ba937426e64dcc1b91 else
  0x3cb27944f249e413c8078c8f111e203c407880f091e093c107820f041dfa3bf077e0efc1df83bf0778ceec9dd13ba07724ed99da23b247640ebd9d783af075e0ebc1d783af0758ceac9d513aa074ece951d283a347460e8c1d03)) else (if i < 21 then
  0x3f427e64fc89f893f027e00fc01f803ef27de0fbc1f713ed27da0fb41f5a3ea27d24fa41f483e907d20f999f223e407c2cf7d1ef83df07be0f7c1ef83db87af0f4e1e913d1279e8f3c1e783cf079e0f351e683cd07984f301e60 else (if i < 22 then
  0x42a085410a4a141428085010a0214042568469081a0eb41a68325060a0b9416282a5050a09941228241048209041128221044207a40f081e1038a06940d081a1034206840a6810901ca0384054804cffd9fea3fa67eecfd89fa9 else
  0x45a68b25160a2c045568a6914c228a451089e913c227844d489a1129a25044a08941128225044a08941124a248447488a910d2218441487cd0eda1c3435686850cca191431286050bca16a42d085a10b4216142c085810aca151))))) else (if i < 34 then (if i < 28 then (if i < 25 then (if i <
  24 then 0x46408c49188231046208c41188231046128c21184230846108be917c22f845f08be117c22f845e28bc117822f045e08bc117822f045e08bc117822f045e08bc117822f045e08bc117822f045e08bc117822f045e08bc1174a2e8 else
  0x497492a924d249849309245248248948f491a9230a4524892910521ca42a48429065208a40947f48fa91ed23c347568e851c9238946f48de11b8a37046d28d691a5233a46708ce119c233846708ce1195232846508c851902320) else (if i < 26 then
  0x4ca0994132826494c8298e531c26384c6298c131826294c42988130ca6114c129821300a5f94be297a52f0a5d94ba296ed2d1a5994b0695ad2b425684a9894e9295251a4a1493e927524e849c2938126ca4d849b0936126c24ca else (if i < 27 then
  0x50029fe53fc27e34fa49f413e127ab4f509ea13d427a84f509ea13c9a7894f029e013b5a75a4eb09d293a427484e669cc139827304e609cc139827304e609cc139827304e369c0d375a6d34d689a6d341a6794ce299513282650 else
  0x52c4a5814b0296052c0a5814b029445248a41147ca8f151e0a38947028e051b2a36146c28d15192a32145d28aa5150a2a145428a85150a2a145428935112a205440286b50b4a16142528485090a0cd41828305060a0c1411280b))) else (if i < 31 then (if i < 29 then
  0x5644ac2d579aae955c2ab65568aac95582aae5558aab05560aac1554aaa15540aa815502a8b54f4a9e1538aa5b5486a8ad50d2a0353f2a7c54f4a9e153b2a7454e4a9c15380a7014e029b95362a6c14d829b05336a6294c42973 else (if i < 30 then
  0x5930b2616452c815900b2016402c805900b2016402c805900b2016402c8058f2b1e16352c5a58b0b14561dac235840b0816092bfb57c6af2d5d9aba95742ae655c8ab895702adc95b82b7056e0ada55b42b6856d0ad855a5ab33 else
  0x5a14b3cd674acda59a2b3256642cc85990b32165d2cb15960b2c16582cb05960b2c16582cb05960b2896502ca05940b2816502ca05940b26564c2c985930b26164c2c985930b26164c2c985930b26164c2c985930b26164c2c98)) else (if i < 32 then
  0x5c80b9017202e405c80b9017202e405c80b9017202e405c80b9017202e405c80b901715ae215c32b861701adf25be0b7896e5adc85b90b7216e42dc85b90b7216e42dc15b64b6896c92d895b02b5e56b52d5a5a94b4cd6912d19 else (if i < 33 then
  0x5f26be097b5af615eb2bd457a4af415e72bcc57982f1b5e14bc21779aee25dc0bb817702ee05dc0bb817622ea45d08b9e5738ae705cd2b9a17342e685cb4b96172c2e585cb0b96172c2e4a5c90b9217242e485c90b9217242e41 else
  0x6350c6a18d431a86350c6a18d431a16316c5cd8b8317062d2c5a18ad31586286c4c988db10361d6c38586cb0d16192c30585cb0b86162c26d841b07260b6c10d81cb0316052c08580cb0116012c0217f9afe25fc0bf657e1afab)))) else (if i < 40 then (if i < 37 then (if i < 35 then
  0x6574cac595832b06560cac195832b06560ca8995032a06532ca2993d326a64b4c92991d32236416c8058f931e963c2c7658ec31d863b0c7618e531c86390c7218e431c16380c7018e031c06380c6c98d831b06360c6c18d4b1a8 else (if i < 36 then
  0x68e0d1a5a2d344a6874d0a9a0d340a67e6cfa59ed33c36772cec59d4b3a86750cea19d4339a6730ce619cc33986722ce419c833906720ce419c4b37a66d4cd699a5333a6646cc4997db2f165c4cb65968b2c96590cb2196432c8 else
  0x6aa8d541aa835506aa0d541aa835506aa0d541aa835506aa0d541aa835506a92d521aa435416a80d501a9cb5386a70d4c5a9835306a60d4c1a9835306a52d469a8534fa69d4d369a6534b36936d245a44b48168e4d1c1a383470)) else (if i < 38 then
  0x74c4e911d1cba317452e885d093a0273c8e749cda39947304e5adcad393c7238e3f1c71b8cb7158e231c36384c7066e051bfa37d46f68de51bbdb7636e88dc91b8236e46d88da91b45b6736ca8d8d1b0a35f46ba8d6d1aca3574 else (if i < 39 then
  0x7ba6f6eded53d937af6f571ea53d487a82f491e893d107a12f3b1e69bcd07976f28de423c8078f2f18de25bc3a7846f02ddf63be877c2ef49dda3bb07744ee11db5bb537668ecc1d8dbb0375e4eb6dd61baa47540ea49d3a3a70 else
  0x80430082010402080330046004c0018001000200040007fd6ff4dfda3fb07f52fe85fccbf917ef6fd8dfa93f3b7e46fc11f793ef07dd2fb85f6cbed17d68fa89f503e997d22f9d1f2dbe587c86f8adf063e087c02f7e5ef8bde9))) else (if i < 43 then (if i < 41 then
  0x828304ca094c12882350462088c11082210442084c1018201040207cc0f881f103e2078c0e981b5036206540ba817102e205c40b1815302a204d409881310262048c089810301e6038c06980c30166028c049808300e6018c029 else (if i < 42 then
  0x83a107420e841c9839107220e0c1c0838107020dcc1b8837106e20dc41b8837106e20dc41b8836306a60d0c1a0834106820ccc198833106620cc4198832306260c0c17982e305a60b0c15982a305420a84150829305220a44148 else
  0x847308c6114c228845108a21144221843308461084210842108421084210842108261044208841108061004200840108020fcc1f883f107e20fc41f883f107e20fc41f883f107c60f4c1e883d107860f041e083c107660ec41d1)) else (if i < 44 then
  0x84c10982130426084c10982130426084c10982130426084c10982130426084c10982130426084c10982130426084c10982130426084c10982130426084c10982130426084c10982130426084c10982130426084c109661254241 else (if i < 45 then
  0x86330c46184c30886030c0217cc2f185d30ba2170c2e085c10b4a16842c285730ac6154c2a885430a8215042a085410a66148c28985110a22140c28084f309c6134c26884d10986130426084c10982130426084c109821304260 else
  0x21c1438086e50d8a1acc35186930d221a0c34086810d021a0433986630ca6194432186410c821904320))))))

private def edgeMeta5 (i : Nat) : Nat := unpack edgeMeta5Packed 15 48 i

private def edgeData5Packed (i : Nat) : Nat :=
  (if i < 23 then (if i < 11 then (if i < 5 then (if i < 2 then (if i < 1 then 0x8a40000801841e300191008018aa2b9ee7b9ee7a94a299e6518a67b3ee50942509fa4f8a67d93a299f2508d6298a59e8a51b8a5fe8a5b08a5349ee50 else
  0x8a40c7380c0280902e0f5f40a3940902e3601807021e05e4de01c06022359fa527fa7d945b067a7c4d11b3ec308a6298a40301005851ee00d0701404) else (if i < 3 then
  0x8a5a00b4196e81d8a42d8a5360b6294742d060ea330c705540072290b40f8b40e6c40e4d40e8e00d67c0d4700da6e9a996648e6398e22d0bc2e8b237 else (if i < 4 then
  0x481102eb405008acc130c41eac815054170581404c100c42d0602d0b4300c42d0642d0b4300bc2e0b63a0a027098257fc220842007dcd07a296c82d else
  0xd6810d2800ce7f0d281a0a849d28393282a062f15c568ba290c88a0c82c090100a8230ac2903c2206c0e0a01a0342708419098200602507c170581e))) else (if i < 8 then (if i < 6 then
  0x108418a601152868204f12e0a14229152296d054136858a4546556e5a8486e8518a454019370f43c0ec3a504390e07f0dc550dc890da2f0d6000d5b3 else (if i < 7 then
  0x114381383d0d44d1103c130430d04b1083b128491043a11c37118481204a124400e4019dc400fc5413454150551505412c54154541505615044a1c43 else
  0x1851e186561825517cfc18256abead9625895e3f95a3e204808f2290d85c16c5a1502d8a45e175ba55c5a8e059a0458a06388c2295685714c3f0f852)) else (if i < 9 then
  0x204801f8761f87f1f87e1fa408a47e1da5a8787a874798a47e1b86d1b2591ac6768466194641e22947c7e8a4fd1f92f354d21c9401ee291fa3e1863d else (if i < 10 then
  0x8b6292b07d1a4681f06f188781b8671dc66184761b4651d4731b0641d06b180721c8751cc6a18c710dc701f8780107eaa06a1a47e0269018c621fc7e else
  0x344cd26e3223a022393823a5d2365c230fe2365dac2aa97a5f90a5e976322bcad8c62922e5b22c86214841f82d2122922087500a48b4839588295a41)))) else (if i < 17 then (if i < 14 then (if i < 12 then
  0xa48912b890a448f2b0ac2bcae2b09f2b0ac2b0ad2b0a829ca6984a58a6032b09f9820828a0a28e292b1b52549424c9256c908a5392b0a08a4ff2b112 else (if i < 13 then
  0x2d2382c65d2c25d8e2332ac97258aa2a45a28495238a82809429c9f24ca62789c248a52748d0149924098ab89a26c9b2789c268912b0a02b0972b807 else
  0x8a63b31a62314c02fcbe1f8ac2fe29308c18c8bd8f8bc98e3e8ca292e4b803c542b2082ecba829c9a04b7974b68a5cca065d8d0b32c8382b02d8a4b5)) else (if i < 15 then
  0x60e93a0e7390e2384e3380df374dc368db364d5348cf324d4344cd320d3338cc31cd5340cb344d0328cc32cca97e578fe6590a648a0c688839894c5 else (if i < 16 then
  0x4250d444ac28111431100350d43120425064110141503408f93d0f33b4e53e0ec378f73c8eb3d8f13d4ef3acea3b8600ece73c0e9234f03a1003b82d else
  0x4b9284c92541d314b1244c52b48d304a8e54bd291f8780f5224b527239264b5290392649d224550f41d19439184510b45d144291644cde449101843c))) else (if i < 20 then (if i < 18 then
  0x8a55a5522968d5aa3229569ab5c96f53a4951246511a25129450e9350a8b50e94ac678a5a959369492688572488a48f504dea053f4f13b4f83e4f53a else (if i < 19 then
  0x528e75414f524df0094e5395053d483155a5515a51c9051a75521450295b5695a5715b569515695a5695a91e2956a98879565454ca5d4b5294987555 else
  0x5a56458d3b1515a58e29599658bd6292561a66498bd5f578625682da2a295822d57694a269492a2d565454e958534845514c48953511095494b50d51)) else (if i < 21 then
  0x24d8232a8d5fc2d0657c5e9235ecc95e17742976321725bd6c381715b96a365705acea31d6e5c96d3a56d3a0ea9369b9329a89d6989463888918a645 else (if i < 22 then
  0x669963b199658da655931985413544435942519443193035906390163d8d6318a615845f5246257942d8860d87604eb619803accc5fc650d143608cb else
  0x94e297329495a4b6e5b62f9b81a1b7259aa4a1ae6450f6b5a85f5ac69ced6b1a6385ab694670d55a551a949c95499a96940e661914959c4399b65d79))))) else (if i < 34 then (if i < 28 then (if i < 25 then (if i < 24 then
  0x79ba07540071af4cc1b6751a0698b62c193e8fa061bd056250522204dbe04a6239694a4979976905f6568a5bc6ec101f95aa3e5487a1d72294a3a56 else
  0x9aa29731f976dd8706a4702a3702a17026e6fe6d6fe696fea69c2ac9daa59bea49ba9c998300b5bc0b0b90ac2a2e0290a027099bb0902308821081be) else (if i < 26 then
  0x71da54a5c664d10715c263102711c05fdc36fcee705c1715c25a4c6731c77300073003735cc731c6731cc735cc731c6a9e29732718a5cc71ea28a5cc else (if i < 27 then
  0xa822975e32756a4a7ea49ce3251c9974db725dcc1fa9e8a5d48f9d2a929da92728f9d05153d730549a2297462f73e6e99ea99ba2f72db62fdca58d3c else
  0x5b9bf1ac5412d4a3c16d2348c789a6389e15b1df600ef5acce76dd86350376976448cd765955a8db76d956511144aaa9d2281aa27521d66e069730ac))) else (if i < 31 then (if i < 29 then
  0x6a52d239f47b9a84b1f365d147c9837c577451f0780f2345c01b4340cd4b608d02b09f7b57a4adec33de978da74a9e86591379de0605e63c5e5658dc else (if i < 30 then
  0x3e89d26e28268c430ea87ba3e8ed07a92b3782388255e1bd4d21607819f5616057a8f46a92e7f198455fc639047edee611fa78cf37e5cc71c6e0d54c else
  0x7e52f6ae27102456466e82d3e0fdcc56a6c91229926439ba6baae6e924ac74cab2a85c2a45b2a0a7295402920a28e08289fd4cca1468a07d9f527dea)) else (if i < 32 then
  0x5e117768d4815fa6b1308419a45a0f7c187798f6789ac391726fc6017c425695179599375d95c5df618f55c0d37e5d863d057b17b4bcd2785ab5bce3 else (if i < 33 then
  0x7a4f9870b2115fc6b932671197f19041a147cd89841e83e1db731c618444512067edad4c61466d187c9887b57c4c60f79cf7355c01f87610d43509f1 else
  0x131eb7a84b1216859e7578e491c447569d056558219ba55e1e55a1d555af5521a675538598b54a13849515d17353a778422fad20f8b607859f462a12)))) else (if i < 40 then (if i < 37 then (if i < 35 then
  0x835dd1f9d61f55f1f1401ee1e1ea1d1e5331e21a4687785e161da123e87435cd61caae852321520b14cb3149ba1460a1420813dfd6bc4e6744d7d58b else (if i < 36 then
  0x6bce5841ea674de841e3644d883de062cfa83dde5f4e5839e05e4de6e53f8261c731cb301ca5920a7261d721fd71e1a71a167d5c4849ea70ddc7060c else
  0x62e167d58b8a2167d57e896167bd8b88a157d58b859ee5f533851f55e51a851ee5d50784deb3ea127a8fa89e127a8e689612790fa88a117a8fa849e3)) else (if i < 38 then
  0xc62286e087f5af4ce287f5a44ce277f5af486257e1af4ce1e7ddaf4ce1a6751a8a21a6491a89e1a67508866086751a88a186751a869fd6450785df6 else (if i < 39 then
  0x6c9368a5cc8a5fe6c1348a6298a6298a1ba89d40899cd6e9408960a8920a6e87f88e0a56d4087a088961e8122287621875ba2ba20875401561f8760a else
  0x8f9a147ead8a4548ea386811d8a5cc8d6296791b8c9d72f632754c18ca036d5398bdd158a2d574878a55a8bdcf5962d580838be016d1378a47e8b5ff))) else (if i < 43 then (if i < 41 then
  0x222619825d3fe2956ab096a59958fd8a454abe52946293ee4f9398b926445864990d669264768d209e23e750bc8e0b1176292b23e748c28e0b416640 else (if i < 42 then
  0x8a4acac695a2296a1e86a16818a47ea12839fa7d9f2299ea793ea6e9ae689ba6c99e719ba6a402769be66ad65d2e8b095a5420a290b65d2d8b595a53 else
  0x849fd7d5ea731af6758b56933468fa2b07e1502da929fa7aa4a829da9ea4a8a8dab2a5a72b5a528fa26812ec588a42da528ea2a812dc5ea6297a528c)) else (if i < 44 then
  0x62c8b569334cd1a468fa3ea1285a1a8a5fd7d5ea6bd9d62d33468fa2b08faf4ac2b2ba5687e0c87e15036152b6152b71fac10b42d0b6b97322986a16 else (if i < 45 then
  0xaf8acafc7e3e91a4ce2986a1684a7b7f5f57a9cc6bd9d62d5aaf054aed5a62d9d6be2986a1684a507f5f57a9cc032b8731ea7d5fd8a61a85a126bd9d else 0xb002d))))))

private def edgeData5 (i : Nat) : Nat := unpack edgeData5Packed 10 48 i

private def st6Packed (i : Nat) : Nat :=
  (if i < 23 then (if i < 11 then (if i < 5 then (if i < 2 then (if i < 1 then
  0x18ee353585647d01cb0c771a9ac2b23e80ec1cb80018ee353585647d01c30c771a9ac2b23e80ec1c380018ee353585647d01ab0c771a9ac2b23e80ec1ab80018ee353585647d01930c771a9ac3145647d01938c771a9ac2b23e864c1938c771a9ac2b23e838019380018ee353585647d018b0c771a9ac2b23e80ec18b80018ee353585647d01730c771a9ac3145647d01738c771a9ac2b25047d01738c771a9ac2b23e82081738ce58ee353585647d00e380018ee353585647d00e30cf78ee353585647d00bb80018ee353585647d00bb0d258ee353585647d007380018ee353585647d00730d398ee353585647d006380018ee353585647d00630
  else
  0xc77826353585647d01db8c77776353585647d01db8c775ae353585647d01db8c7726a353585647d01db8c771ba353585647d01db8c771aa2a3585647d01db8c771aa143585647d01db8c771a9d0b585647d01db8c771a9b83585647d01db8c771a9ae3585647d01db8c771a9ac3405647d01db8c771a9ac3145647d01db8c771a9ac3045647d01db8c771a9ac2c75647d01db8c771a9ac2b85647d01db8c771a9ac2b25407d01db8c771a9ac2b25047d01db8c771a9ac2b23f47d01db8c771a9ac2b23e87881db8c771a9ac2b23e86cc1db8c771a9ac2b23e864c1db8c771a9ac2b23e83801db8c771a9ac2b23e82081db8c771a9ac2b23e81801db8)
  else (if i < 3 then
  0xc771a9ac2b23e87883038c771a9ac2b23e86cc3038c771a9ac2b23e864c3038c771a9ac2b23e83803038c771a9ac2b23e820830380018ee353585647d02eb0c771a9ac2b25407d02eb8c771a9ac2b23e87882eb8c771a9ac2b23e81802eb80018ee353585647d02bb0c77826353585647d02bb80018ee353585647d02730c771a9ac2b25047d02738c771a9ac2b23e83802738c771a9ac2b23e818027380018ee353585647d01e30c771a9ac2b23e864c1e38c771a9ac2b23e82081e38c771a9ac2b23e81801e38d398ee353585647d01db8d258ee353585647d01db8cf78ee353585647d01db8ce58ee353585647d01db80018ee353585647d01db0
  else (if i < 4 then
  0xd398ee353585647d03038d258ee353585647d03038cf78ee353585647d03038ce58ee353585647d03038cc38ee353585647d03038c77826353585647d03038c777ee353585647d03038c77776353585647d03038c775ae353585647d03038c7726a353585647d03038c771f2353585647d03038c771aa2a3585647d03038c771aa143585647d03038c771a9d0b585647d03038c771a9b83585647d03038c771a9b53585647d03038c771a9ac3405647d03038c771a9ac3145647d03038c771a9ac3045647d03038c771a9ac2c75647d030380018ee353585407d03030c771a9ac2b25407d03038c771a9ac2b25047d030380018ee353585647883030
  else
  0xc771a9d0b585647d04138c771a9b83585647d041380018ee353405647d04130c771a9ac3405647d04138c771a9ac3145647d04138c771a9ac3045647d04138c771a9ac2c75647d041380018ee353585407d04130c771a9ac2b25407d04138c771a9ac2b25047d04138c771a9ac2b24087d04138c771a9ac2b23e87884138c771a9ac2b23e86cc4138c771a9ac2b23e864c4138c771a9ac2b23e838041380018ee353585647d03eb0c771a9ac3405647d03eb8c771a9ac2b25407d03eb8c771a9ac2b23e82083eb80018ee353585647d03cb0c77776353585647d03cb80000031dc6a6b0c1030280018ee35358608ac830300018ee353586087d03030)))
  else (if i < 8 then (if i < 6 then
  0xc771a9ac2b23e87886e38c771a9ac2b23e83806e380018ee353585647d06bb0c775ae353585647d06bb80018ee353585647d048b0c771a9d0b585647d048b80018ee353585647d04530c771a9ac2b23e86cc45380000031dd6b8d47d041280018eeb5c6a6b07d041300018eeb5c6a5647d04130d398ee353585647d04138d258ee353585647d04138cf78ee353585647d04138ce58ee353585647d04138ccb8ee353585647d04138c77826353585647d04138c77776353585647d04138c7773a353585647d04138c775ae353585647d04138c7726a353585647d04138c77226353585647d04138c771aa2a3585647d04138c771aa143585647d04138
  else (if i < 7 then
  0xc77826353585647d07038c77776353585647d07038c775ae353585647d07038c77572353585647d07038c7726a353585647d070380018ee2a3585647d07030c771aa2a3585647d07038c771aa143585647d07038c771a9d0b585647d07038c771a9c83585647d07038c771a9b83585647d07038c771a9ac3405647d07038c771a9ac3145647d07038c771a9ac3045647d07038c771a9ac2d85647d07038c771a9ac2c75647d07038c771a9ac2b25407d07038c771a9ac2b25047d070380018ee353585647887030c771a9ac2b23e87887038c771a9ac2b23e86cc7038c771a9ac2b23e864c70380018ee353585647d06e30c771aa2a3585647d06e38
  else
  0xc771a9ac2c75647d0c9b8c771a9ac2b25407d0c9b8c771a9ac2b25047d0c9b80018ee35358564788c9b0c771a9ac2b23e8788c9b8c771a9ac2b23e86ccc9b80018ee353585647d0c730c771a9ac3405647d0c738c771a9ac2b23e8788c738c771a9ac2b23e864cc7380018ee353585647d0c530c7726a353585647d0c5380018ee353585647d077b0c7726a353585647d077b80018ee353585647d07430c771a9ac2c75647d074380000031dddd6b0ac870280018eeeec6a6b0ac870300018eeeeb585647d07030d398ee353585647d07038d258ee353585647d07038cf78ee353585647d07038cef8ee353585647d07038ce58ee353585647d07038))
  else (if i < 9 then
  0xc771a9ac2b23e86cccdb80000031dc6a742ac8c9a80018ee353a16b0ac8c9b00018ee353a15647d0c9b0d398ee353585647d0c9b8d258ee353585647d0c9b8cf78ee353585647d0c9b8ceb8ee353585647d0c9b8ce58ee353585647d0c9b8c77826353585647d0c9b8c77776353585647d0c9b8c77732353585647d0c9b8c775ae353585647d0c9b8c7726a353585647d0c9b8c7722e353585647d0c9b8c771aa2a3585647d0c9b8c771aa143585647d0c9b8c771a9d0b585647d0c9b8c771a9b83585647d0c9b80018ee353405647d0c9b0c771a9ac3405647d0c9b8c771a9ac3145647d0c9b8c771a9ac3045647d0c9b8c771a9ac2e65647d0c9b8
  else (if i < 10 then
  0xc7726a353585647d0d9b8c771aa2a3585647d0d9b8c771aa143585647d0d9b8c771a9d0b585647d0d9b8c771a9b83585647d0d9b8c771a9b2b585647d0d9b8c771a9ac3405647d0d9b8c771a9ac3145647d0d9b8c771a9ac3045647d0d9b8c771a9ac2e45647d0d9b8c771a9ac2c75647d0d9b8c771a9ac2b25407d0d9b8c771a9ac2b25047d0d9b8c771a9ac2b24067d0d9b8c771a9ac2b23e8788d9b80018ee353585647d0d7b0c771a9ac2b23e86ccd7b80018ee353585647d0d630c771a9ac3045647d0d6380018ee353585647d0d3b0c771a9ac2b23e86ccd3b80018ee353585647d0d130c775ae353585647d0d1380018ee353585647d0cdb0
  else
  0xc771a9ce3585647d0f138c771a9b83585647d0f138c771a9ac3405647d0f138c771a9ac3145647d0f138c771a9ac3045647d0f138c771a9ac2fb5647d0f138c771a9ac2c75647d0f138c771a9ac2b25407d0f138c771a9ac2b25047d0f1380018ee353585647d0eeb0c77826353585647d0eeb80018ee353585647d0eb30c771a9b83585647d0eb380018ee353585647d0dcb0c771aa2a3585647d0dcb8d398ee353585647d0d9b8d258ee353585647d0d9b8cf78ee353585647d0d9b8ce58ee353585647d0d9b8c7b8ee353585647d0d9b80018ee353585647d0d9b0c77826353585647d0d9b8c77776353585647d0d9b8c775ae353585647d0d9b8))))
  else (if i < 17 then (if i < 14 then (if i < 12 then
  0xd398ee353585647d0f9380018ee353585647d0f930001a4b1dc6a6b0ac8f8300000031dc6a6b0ac8f828d258ee353585647d0f8380018ee353585647d0f8300019cb1dc6a6b0ac8f6b00000031dc6a6b0ac8f6a8ce58ee353585647d0f6b80018ee353585647d0f6b00019ef1dc6a6b0ac8f130d398ee353585647d0f138d258ee353585647d0f138cf78ee353585647d0f138ce58ee353585647d0f138c77826353585647d0f138c77776353585647d0f138c77766353585647d0f138c775ae353585647d0f138c7726a353585647d0f138c771aa2a3585647d0f138c771aa16b585647d0f138c771aa143585647d0f138c771a9d0b585647d0f138
  else (if i < 13 then
  0x18ee2a358564a08fa30c771aa2a358564a08fa38c771aa14358564a08fa38c771a9d0b58564a08fa38c771a9c9358564a08fa38c771a9b8358564a08fa38c771a9ac340564a08fa38c771a9ac314564a08fa38c771a9ac304564a08fa38c771a9ac2f1564a08fa38c771a9ac2c7564a08fa380018ee35358540a08fa30c771a9ac2b2540a08fa380018ee353585649f8fa30c771aa2a3585649f8fa38c771a9ac2b25409f8fa38c771a9ac2b25049f8fa380018ee353585649e4fa30c771a9d0b585649e4fa380018ee35358564810fa300018ee3535856480cfa300018ee353585647e8fa30001a731dc6a6b0ac8f9300000031dc6a6b0ac8f928
  else
  0xc771a9ac304564a80fa38c771a9ac2fe564a80fa38c771a9ac2c7564a80fa380018ee35358564a6cfa30c7782635358564a6cfa380018ee35358564a50fa30c771aa14358564a50fa380018ee35358564a44fa30c7777635358564a44fa380018ee35358564a28fa30c771a9ac2c7564a28fa380000031dc9a6b0a08fa280018ee4d46a6b0a08fa300018ee4d358564a08fa30d398ee35358564a08fa38d258ee35358564a08fa38cf78ee35358564a08fa38ce58ee35358564a08fa38cdd8ee35358564a08fa38c7782635358564a08fa38c7777635358564a08fa38c775ae35358564a08fa38c7756a35358564a08fa38c7726a35358564a08fa38))
  else (if i < 15 then
  0xd258ee35358564ab8fa380018ee35358564ab8fa300019ef1dc6a6b0aacfa300000031dc6a6b0aacfa28cf78ee35358564aacfa380018ee35358564aacfa300019cb1dc6a6b0a80fa30d398ee35358564a80fa38d258ee35358564a80fa38cf78ee35358564a80fa38ce58ee35358564a80fa38c7782635358564a80fa38c7777635358564a80fa38c775ae35358564a80fa38c7759a35358564a80fa38c7726a35358564a80fa38c7725a35358564a80fa38c771aa2a358564a80fa38c771aa14358564a80fa38c771a9d0b58564a80fa38c771a9bab58564a80fa38c771a9b8358564a80fa38c771a9ac340564a80fa38c771a9ac314564a80fa38
  else (if i < 16 then
  0xc7726a3535858eac8fa38c771e23535858eac8fa38c771aa2a35858eac8fa38c771aa1435858eac8fa38c771a9d0b5858eac8fa38c771a9b835858eac8fa38c771a9ac34058eac8fa38c771a9ac31458eac8fa38c771a9ac30458eac8fa38c771a9ac2f058eac8fa38c771a9ac2d658eac8fa380018ee35358586ac8fa30c771a9ac2c7586ac8fa380018ee35358582ac8fa30c771a9ac304582ac8fa380018ee35358578ac8fa30c771a9ac2c7578ac8fa380018ee35358570ac8fa30001a731dc6a6b0ac0fa300000031dc6a6b0ac0fa28d398ee35358564ac0fa380018ee35358564ac0fa30001a4b1dc6a6b0ab8fa300000031dc6a6b0ab8fa28
  else
  0xc771a9ac30d608ac8fa380018ee353585fcac8fa300018ee353585f6ac8fa300018ee353585f0ac8fa30c771a9ac3145f0ac8fa380018ee353585ecac8fa30c771a9ac3045ecac8fa380018ee353585e2ac8fa300018ee353585e0ac8fa300018ee353585ccac8fa300018ee353585c8ac8fa300018ee353585b0ac8fa300018ee353585acac8fa300018ee3535859aac8fa30c771a9ac34059aac8fa38d398ee3535858eac8fa38d258ee3535858eac8fa38cf78ee3535858eac8fa38ce58ee3535858eac8fa38c7d8ee3535858eac8fa380018ee3535858eac8fa30c778263535858eac8fa38c777763535858eac8fa38c775ae3535858eac8fa38)))
  else (if i < 20 then (if i < 18 then
  0x18ee35340628ac8fa30c771a9ac340628ac8fa380018ee3535861aac8fa300018ee35358612ac8fa30c771aa2a358612ac8fa38c771a9ac340612ac8fa38c771a9ac314612ac8fa38d678ee35358608ac8fa38d618ee35358608ac8fa38d558ee35358608ac8fa38d398ee35358608ac8fa38d258ee35358608ac8fa38cf78ee35358608ac8fa38ce58ee35358608ac8fa38c7782635358608ac8fa38c7777635358608ac8fa38c775ae35358608ac8fa38c7726a35358608ac8fa38c771aa2a358608ac8fa38c771aa14358608ac8fa38c771a9d0b58608ac8fa38c771a9b8358608ac8fa38c771a9ac340608ac8fa38c771a9ac314608ac8fa38
  else (if i < 19 then
  0xc771a9b8358654ac8fa380018ee3535864eac8fa30c7726a3535864eac8fa380018ee35358640ac8fa30c771aa14358640ac8fa380000031de09628ac8fa280018ef04c6a628ac8fa300018ef04b58628ac8fa30d398ee35358628ac8fa38d258ee35358628ac8fa38d1b8ee35358628ac8fa38cf78ee35358628ac8fa38ce58ee35358628ac8fa38c7782635358628ac8fa38c7777635358628ac8fa38c775ae35358628ac8fa38c7726a35358628ac8fa380018ee2a358628ac8fa30c771aa2a358628ac8fa38c771aa1db58628ac8fa38c771aa14358628ac8fa38c771a9d0b58628ac8fa38c771a9c1b58628ac8fa38c771a9b8358628ac8fa38
  else
  0x18ee35358698ac8fa30001a4b1dc6a680ac8fa30d398ee35358680ac8fa38d258ee35358680ac8fa38cf78ee35358680ac8fa38ce58ee35358680ac8fa38c7782635358680ac8fa38c7781a35358680ac8fa38c7777635358680ac8fa38c775ae35358680ac8fa38c7758a35358680ac8fa38c7726a35358680ac8fa38c771aa2a358680ac8fa38c771aa14358680ac8fa38c771a9d0b58680ac8fa38c771a9ccb58680ac8fa38c771a9b8358680ac8fa380018ee3535867cac8fa30c777763535867cac8fa380018ee3535866eac8fa30c771a9b835866eac8fa380018ee35358662ac8fa30c771a9d0b58662ac8fa380018ee35358654ac8fa30))
  else (if i < 21 then
  0xc77722353706b0ac8fa38c775ae353706b0ac8fa38c7726a353706b0ac8fa38c771aa2a3706b0ac8fa38c771aa143706b0ac8fa38c771a9d0b706b0ac8fa38c771a9c5b706b0ac8fa38c771a9c0b706b0ac8fa380018ee3536b6b0ac8fa30c771a9b836b6b0ac8fa380018ee3536a6b0ac8fa300018ee353656b0ac8fa300018ee3535c6b0ac8fa30001a731dc6a6a8ac8fa300000031dc6a6a8ac8fa28d398ee353586a8ac8fa380018ee353586a8ac8fa300019ef1dc6a6a0ac8fa300000031dc6a6a0ac8fa28cf78ee353586a0ac8fa380018ee353586a0ac8fa300019cb1dc6a698ac8fa300000031dc6a698ac8fa28ce58ee35358698ac8fa38
  else (if i < 22 then
  0xc77826353a16b0ac8fa38c77776353a16b0ac8fa38c775ae353a16b0ac8fa38c7726a353a16b0ac8fa38c771aa2a3a16b0ac8fa38c771aa143a16b0ac8fa380018ee3539c6b0ac8fa300018ee353996b0ac8fa300018ee353956b0ac8fa30c771a9d0b956b0ac8fa380018ee353926b0ac8fa300018ee353906b0ac8fa300018ee3538b6b0ac8fa300018ee353836b0ac8fa300018ee353816b0ac8fa300018ee353756b0ac8fa30d398ee353706b0ac8fa38d258ee353706b0ac8fa38cf78ee353706b0ac8fa38ce58ee353706b0ac8fa38c8d8ee353706b0ac8fa380018ee353706b0ac8fa30c77826353706b0ac8fa38c77776353706b0ac8fa38
  else
  0xcf78ee354286b0ac8fa38ce58ee354286b0ac8fa38c838ee354286b0ac8fa380018ee354286b0ac8fa30c77826354286b0ac8fa38c77776354286b0ac8fa38c775ae354286b0ac8fa38c77556354286b0ac8fa38c7726a354286b0ac8fa38c77216354286b0ac8fa38c771aa2a4286b0ac8fa38c771aa1cc286b0ac8fa380018ee354236b0ac8fa30c771aa144236b0ac8fa380018ee354226b0ac8fa30c775ae354226b0ac8fa380018ee3541b6b0ac8fa30c771aa1441b6b0ac8fa38d738ee353a16b0ac8fa38d558ee353a16b0ac8fa38d398ee353a16b0ac8fa38d258ee353a16b0ac8fa38cf78ee353a16b0ac8fa38ce58ee353a16b0ac8fa38)))))
  else (if i < 34 then (if i < 28 then (if i < 25 then (if i < 24 then
  0x31dc626b0ac8fa28cf78ee354626b0ac8fa380018ee354626b0ac8fa300019cb1dc5e6b0ac8fa300000031dc5e6b0ac8fa28ce58ee3545e6b0ac8fa380018ee3545e6b0ac8fa30001a731dc546b0ac8fa30d398ee354546b0ac8fa38d258ee354546b0ac8fa38cf78ee354546b0ac8fa38ce58ee354546b0ac8fa38c77826354546b0ac8fa38c77812354546b0ac8fa38c77776354546b0ac8fa38c77756354546b0ac8fa38c775ae354546b0ac8fa38c7726a354546b0ac8fa38c77246354546b0ac8fa380018ee3543b6b0ac8fa300018ee354396b0ac8fa300018ee3542d6b0ac8fa30d398ee354286b0ac8fa38d258ee354286b0ac8fa38
  else
  0xd718ee4d46a6b0ac8fa38d678ee4d46a6b0ac8fa38d398ee4d46a6b0ac8fa38d258ee4d46a6b0ac8fa38cf78ee4d46a6b0ac8fa38ce58ee4d46a6b0ac8fa38c778264d46a6b0ac8fa38c777764d46a6b0ac8fa38c775ae4d46a6b0ac8fa380018ee4b46a6b0ac8fa300018ee48c6a6b0ac8fa300018ee4646a6b0ac8fa30c7726a4646a6b0ac8fa380018ee45c6a6b0ac8fa300018ee44c6a6b0ac8fa300018ee42c6a6b0ac8fa300018ee3e46a6b0ac8fa300018ee3c46a6b0ac8fa300018ee3746a6b0ac8fa30001a4b1dc666b0ac8fa300000031dc666b0ac8fa28d258ee354666b0ac8fa380018ee354666b0ac8fa300019ef1dc626b0ac8fa30)
  else (if i < 26 then
  0xce58eeeec6a6b0ac8fa38c77826eec6a6b0ac8fa380018eeecc6a6b0ac8fa300018eeeac6a6b0ac8fa300018eee7c6a6b0ac8fa30c77776e7c6a6b0ac8fa380018eee746a6b0ac8fa300018eee646a6b0ac8fa300018eee446a6b0ac8fa30d718eeb5c6a6b0ac8fa38d558eeb5c6a6b0ac8fa38d398eeb5c6a6b0ac8fa38d258eeb5c6a6b0ac8fa38cf78eeb5c6a6b0ac8fa38ce58eeb5c6a6b0ac8fa38c77826b5c6a6b0ac8fa38c77776b5c6a6b0ac8fa380018eeb346a6b0ac8fa300018eeb146a6b0ac8fa300018eeafc6a6b0ac8fa30c775aeafc6a6b0ac8fa380018eeae46a6b0ac8fa300018eead46a6b0ac8fa300018eeaac6a6b0ac8fa30
  else (if i < 27 then
  0x19bb1dc6a6b0ac8fa300019971dc6a6b0ac8fa300019871dc6a6b0ac8fa3000191b1dc6a6b0ac8fa300019071dc6a6b0ac8fa300018fb1dc6a6b0ac8fa300018f71dc6a6b0ac8fa300000031dc6a6b0ac8fa28d738ef04c6a6b0ac8fa38d718ef04c6a6b0ac8fa38d398ef04c6a6b0ac8fa38d258ef04c6a6b0ac8fa38cf78ef04c6a6b0ac8fa38ce58ef04c6a6b0ac8fa380018ef0346a6b0ac8fa300018ef0246a6b0ac8fa300018eeff46a6b0ac8fa30c77826ff46a6b0ac8fa380018eefdc6a6b0ac8fa30d738eeeec6a6b0ac8fa38d678eeeec6a6b0ac8fa38d398eeeec6a6b0ac8fa38d258eeeec6a6b0ac8fa38cf78eeeec6a6b0ac8fa38
  else
  0x18ee353585647d019310018ee353585647d018b10011a9ac2b23e80ec18b10018ee353585647d017310018ee353585647d00e310018ee353585647d00bb10018ee353585647d007310018ee353585647d00631001ae71dc6a6b0ac8fa30001ae31dc6a6b0ac8fa30001acf1dc6a6b0ac8fa30001ac31dc6a6b0ac8fa30001aab1dc6a6b0ac8fa30d39a4b1dc6a6b0ac8fa38001a371dc6a6b0ac8fa30d619ef1dc6a6b0ac8fa38d399ef1dc6a6b0ac8fa38d259ef1dc6a6b0ac8fa380019df1dc6a6b0ac8fa300019d71dc6a6b0ac8fa30d619cb1dc6a6b0ac8fa38d399cb1dc6a6b0ac8fa38d259cb1dc6a6b0ac8fa38cf79cb1dc6a6b0ac8fa38)))
  else (if i < 31 then (if i < 29 then
  0x11a9ac3405647d01db10011a9ac3145647d01db10011a9ac3045647d01db10018ee352c75647d01db1000002352c75647d01da90011a9ac2c75647d01db10011a9ac2b85647d01db10011a9ac2b25407d01db10011a9ac2b25047d01db10011a9ac2b23f47d01db10011a9ac2b23e87881db10018edac2b23e86cc1db10011a9ac2b23e86cc1db1000001ac2b23e86cc1da90011a9ac2b23e864c1db10011a9ac2b23e83801db10011a9ac2b23e82081db10011a9ac2b23e81801db10018ee353585647d01cb10011a9ac2b23e80ec1cb10018ee353585647d01c310011a9ac2b23e80ec1c310018ee353585647d01ab10011a9ac2b23e80ec1ab1
  else (if i < 30 then
  0x18edac2b23e86cc30310018ee353585647d02eb10018ee353585647d02bb10018ee353585647d027310018ee353585647d01e310018ee354286b0ac81db1000002354286b0ac81da90018ee353706b07d01db1000002353706b07d01da9001a72353585647d01db1001a4a353585647d01db10019ee353585647d01db10019ca353585647d01db10018ee353585647d01db1001826353585647d01db1001776353585647d01db10015ae353585647d01db100126a353585647d01db10011ba353585647d01db10011aa2a3585647d01db10011aa143585647d01db10011a9d0b585647d01db10011a9b83585647d01db10011a9ae3585647d01db1
  else
  0x18ee353585647d06e310018ee353585647d06bb10018ee353585647d048b10018ee353585647d045310018edac2b23e86cc45310018ee354286b0ac841310000031dd6b8d47d041290018eeb5c6a6b07d041310018ee353706b07d041310018eeb5c6a5647d041310018ee353405647d041310018ee352c75647d041310018ee353585407d041310018edac2b23e86cc41310018ee353585647d03eb10018ee353585647d03cb10000031dc6a6b0c1030290018ee354286b0ac830310018ee35358608ac830310018ee353706b07d030310018ee353586087d030310018ee352c75647d030310018ee353585407d030310018ee353585647883031))
  else (if i < 32 then
  0x18edac2b23e86cccdb10000031dc6a742ac8c9a90018ee354286b0ac8c9b10018ee353a16b0ac8c9b10018ee353706b07d0c9b10018ee353a15647d0c9b10018ee353405647d0c9b10018ee352c75647d0c9b10018ee35358564788c9b10018edac2b23e86ccc9b10018ee353585647d0c7310018ee353585647d0c5310018ee353585647d077b10018ee353585647d074310018ee352c75647d074310000031dddd6b0ac870290018eeeec6a6b0ac870310018ee354286b0ac870310018ee353706b07d070310018eeeeb585647d070310018ee2a3585647d070310018ee352c75647d070310018ee3535856478870310018edac2b23e86cc7031
  else (if i < 33 then
  0x18ee353585647d0d9b10018ee2a3585647d0d9b10018ee143585647d0d9b10018edd0b585647d0d9b10018edb83585647d0d9b10018edb2b585647d0d9b10018edac3405647d0d9b10018edac3145647d0d9b10018edac3045647d0d9b10018edac2e45647d0d9b10000031dac75647d0d9a90018ee352c75647d0d9b10018edac2c75647d0d9b10018edac2b25407d0d9b10018edac2b25047d0d9b10018edac2b24067d0d9b10018edac2b23e8788d9b10018ee353585647d0d7b10018edac2b23e86ccd7b10018ee353585647d0d6310018ee353585647d0d3b10018edac2b23e86ccd3b10018ee353585647d0d1310018ee353585647d0cdb1
  else
  0x18ee354286b0ac8f1310018ee353706b07d0f1310019ee353585647d0f1310019ca353585647d0f1310011aa2a3585647d0f1310011a9ac3405647d0f1310018ee352c75647d0f1310018ee353585647d0eeb10018ee353706b07d0eb310018ee353585647d0eb310018ee353585647d0dcb10000031dc286b0ac8d9a90018ee354286b0ac8d9b10000031db706b07d0d9a90018ee353706b07d0d9b1001a731db585647d0d9b1001a4b1db585647d0d9b10019ef1db585647d0d9b10019cb1db585647d0d9b10018f71db585647d0d9b10018ef04b585647d0d9b10018eeeeb585647d0d9b10018eeb5b585647d0d9b10018ee4d3585647d0d9b1))))
  else (if i < 40 then (if i < 37 then (if i < 35 then
  0x18ee35358564a28fa310018ee352c7564a28fa310000031dc9a6b0a08fa290018ee4d46a6b0a08fa310018ee353706b0a08fa310018ee4d358564a08fa310018ee2a358564a08fa310018ee352c7564a08fa310018ee35358540a08fa310018ee353585649f8fa310018ee353585649e4fa310018ee35358564810fa310018ee3535856480cfa310018ee353585647e8fa31001a731dc6a6b0ac8f9310000031dc6a6b0ac8f9290018ee353585647d0f931001a4b1dc6a6b0ac8f8310000031dc6a6b0ac8f8290018ee353585647d0f8310019cb1dc6a6b0ac8f6b10000031dc6a6b0ac8f6a90018ee353585647d0f6b10019ef1dc6a6b0ac8f131
  else (if i < 36 then
  0x18ee352c7586ac8fa310018ee35358582ac8fa310018ee35358578ac8fa310018ee352c7578ac8fa310018ee35358570ac8fa31001a731dc6a6b0ac0fa310000031dc6a6b0ac0fa290018ee35358564ac0fa31001a4b1dc6a6b0ab8fa310000031dc6a6b0ab8fa290018ee35358564ab8fa310019ef1dc6a6b0aacfa310000031dc6a6b0aacfa290018ee35358564aacfa310019cb1dc6a6b0a80fa310018ee353706b0a80fa310019ee35358564a80fa310019ca35358564a80fa310011aa2a358564a80fa310011a9ac340564a80fa310018ee352c7564a80fa310018ee35358564a6cfa310018ee35358564a50fa310018ee35358564a44fa31
  else
  0x18ee353585b0ac8fa310018ee353585acac8fa310018ee3535859aac8fa31001a731dc6a58eac8fa31001a4b1dc6a58eac8fa310019ef1dc6a58eac8fa310019cb1dc6a58eac8fa310018fb1dc6a58eac8fa310018ef04c6a58eac8fa310018eeeec6a58eac8fa310018eeb5c6a58eac8fa310018ee4d46a58eac8fa310018ee3c46a58eac8fa310018ee3545458eac8fa310018ee3542858eac8fa310018ee353a158eac8fa310018ee3537058eac8fa310018ee3535858eac8fa310018ee3534058eac8fa310018ee3531458eac8fa310018ee3530458eac8fa310018ee352f058eac8fa310018ee352d658eac8fa310018ee35358586ac8fa31))
  else (if i < 38 then
  0x1a4b1dc6a680ac8fa31001a4a35358680ac8fa310011aa2a358680ac8fa310018ee3535867cac8fa310018ee3535866eac8fa310018ee35358662ac8fa310018ee35358654ac8fa310018ee3535864eac8fa310018ee35358640ac8fa310000031de09628ac8fa290018ef04c6a628ac8fa310018ef04b58628ac8fa310018ee2a358628ac8fa310018ee35340628ac8fa310018ee3535861aac8fa310018ee35358612ac8fa310018ee353585fcac8fa310018ee353585f6ac8fa310018ee353585f0ac8fa310018ee353585ecac8fa310018ee353585e2ac8fa310018ee353585e0ac8fa310018ee353585ccac8fa310018ee353585c8ac8fa31
  else (if i < 39 then
  0x18ee353996b0ac8fa310018ee353956b0ac8fa31000002353956b0ac8fa290011a9d0b956b0ac8fa310018ee353926b0ac8fa310018ee353906b0ac8fa310018ee3538b6b0ac8fa310018ee353836b0ac8fa310018ee353816b0ac8fa310018ee353756b0ac8fa310018ee353706b0ac8fa310018ee3536b6b0ac8fa310018ee3536a6b0ac8fa310018ee353656b0ac8fa310018ee3535c6b0ac8fa31001a731dc6a6a8ac8fa310000031dc6a6a8ac8fa290018ee353586a8ac8fa310019ef1dc6a6a0ac8fa310000031dc6a6a0ac8fa290018ee353586a0ac8fa310019cb1dc6a698ac8fa310000031dc6a698ac8fa290018ee35358698ac8fa31
  else
  0x18ee44c6a6b0ac8fa310018ee42c6a6b0ac8fa310018ee3e46a6b0ac8fa310018ee3c46a6b0ac8fa310018ee3746a6b0ac8fa31001a4b1dc666b0ac8fa310000031dc666b0ac8fa290018ee354666b0ac8fa310019ef1dc626b0ac8fa310000031dc626b0ac8fa290018ee354626b0ac8fa310019cb1dc5e6b0ac8fa310000031dc5e6b0ac8fa290018ee3545e6b0ac8fa31001a731dc546b0ac8fa31001a72354546b0ac8fa310018ee3543b6b0ac8fa310018ee354396b0ac8fa310018ee3542d6b0ac8fa310018ee354286b0ac8fa310018ee354236b0ac8fa310018ee354226b0ac8fa310018ee3541b6b0ac8fa310018ee3539c6b0ac8fa31)))
  else (if i < 43 then (if i < 41 then
  0x2ff46a6b0ac8fa290018eefdc6a6b0ac8fa310018eeecc6a6b0ac8fa310018eeeac6a6b0ac8fa310018eee7c6a6b0ac8fa31001776e7c6a6b0ac8fa31000002e7c6a6b0ac8fa290018eee746a6b0ac8fa310018eee646a6b0ac8fa310018eee446a6b0ac8fa310018eeb346a6b0ac8fa310018eeb146a6b0ac8fa310018eeafc6a6b0ac8fa310015aeafc6a6b0ac8fa31000002afc6a6b0ac8fa290018eeae46a6b0ac8fa310018eead46a6b0ac8fa310018eeaac6a6b0ac8fa310018ee4b46a6b0ac8fa310018ee48c6a6b0ac8fa310018ee4646a6b0ac8fa3100126a4646a6b0ac8fa310000024646a6b0ac8fa290018ee45c6a6b0ac8fa31
  else (if i < 42 then
  0x18ee353706b0c50fa310018ee353706b0c10fa310000031dc6a6e0b1cfa290018ee353706b0b1cfa31001ae71dc6a6b0ac8fa31001ae31dc6a6b0ac8fa31001acf1dc6a6b0ac8fa31001ac31dc6a6b0ac8fa31001aab1dc6a6b0ac8fa31001a371dc6a6b0ac8fa310019df1dc6a6b0ac8fa310019d71dc6a6b0ac8fa310019bb1dc6a6b0ac8fa310019971dc6a6b0ac8fa310019871dc6a6b0ac8fa3100191b1dc6a6b0ac8fa310019071dc6a6b0ac8fa310018fb1dc6a6b0ac8fa310018f71dc6a6b0ac8fa310000031dc6a6b0ac8fa290018ef0346a6b0ac8fa310018ef0246a6b0ac8fa310018eeff46a6b0ac8fa31001826ff46a6b0ac8fa31
  else
  0x31dc6a850b1d59290018ee354286b0b1d59310018ee354286b0ac950310018ee354286b0ac94a310018ee354286b0ac94131001a731dc6a6e0d60fa31001a4b1dc6a6e0d60fa310019ef1dc6a6e0d60fa310019cb1dc6a6e0d60fa3100191b1dc6a6e0d60fa310018ef04c6a6e0d60fa310018eeeec6a6e0d60fa310018eee446a6e0d60fa310018eeb5c6a6e0d60fa310018ee4d46a6e0d60fa310018ee354546e0d60fa310018ee354286e0d60fa310018ee353a16e0d60fa310018ee3538b6e0d60fa310018ee353816e0d60fa310018ee353706d6d60fa310018ee353706b0d00fa310018ee353706b0cdcfa310018ee353706b0ca8fa31))
  else (if i < 44 then
  0x2352c75647d01daa000001ac2b23e86cc1daa0000031dc6a850dc1ac29001a731dc6a850d615931001a4b1dc6a850d6159310019ef1dc6a850d6159310019cb1dc6a850d6159310019071dc6a850d6159310018ef04c6a850d6159310018eeeec6a850d6159310018eeb5c6a850d6159310018eeaac6a850d6159310018ee4d46a850d6159310018ee42c6a850d6159310018ee35454850d6159310018ee35439850d6159310018ee35428846d6159310018ee35428836d6159310018ee35428742d6159310018ee354286e0d6159310018ee354286b0d0159310018ee354286b0c8159310018ee354286b0c5159310018ee354286b0c115931
  else (if i < 45 then
  0x31dc666b0ac8fa2a0000031dc626b0ac8fa2a0000031dc5e6b0ac8fa2a000002353956b0ac8fa2a0000031dc6a6a8ac8fa2a0000031dc6a6a0ac8fa2a0000031dc6a698ac8fa2a0000031de09628ac8fa2a0000031dc6a6b0ac0fa2a0000031dc6a6b0ab8fa2a0000031dc6a6b0aacfa2a0000031dc9a6b0a08fa2a0000031dc6a6b0ac8f92a0000031dc6a6b0ac8f82a0000031dc6a6b0ac8f6aa0000031dc286b0ac8d9aa0000031db706b07d0d9aa0000031dac75647d0d9aa0000031dc6a742ac8c9aa0000031dddd6b0ac8702a0000031dd6b8d47d0412a0000031dc6a6b0c10302a000002354286b0ac81daa000002353706b07d01daa
  else 0x31dc6a850dc1ac2a0000031dc6a850b1d592a0000031dc6a6e0b1cfa2a0000031dc6a6b0ac8fa2a000002ff46a6b0ac8fa2a000002e7c6a6b0ac8fa2a000002afc6a6b0ac8fa2a0000024646a6b0ac8fa2a))))))

private def st6 (i : Nat) : Nat := unpack st6Packed 84 24 i

private def adj6Packed (i : Nat) : Nat := (if i < 4 then (if i < 2 then (if i < 1 then 0x382603060180a4500e10088c038000100009e0108863181031002218c02 else 0xc020043022040000a501c028006300006180011088410f411b00030120) else (if i < 3 then 0x1c610042518444308a01802708020500640040d080a5080010110408934 else 0x2e00000014a0000010906012922000201004909c03014200804429400)) else (if i < 6 then (if i < 5 then 0x504000802009803c84601018008c02104090840150000280000080a0000a else 0xc03104871080100655210067004a1840210c601804118c62014710182f) else (if i < 7 then 0x80440946210080000011c4950002000167004402982a0b4210044908076 else 0x8c0281231840000040101c1218010040509461)))

private def adj6 (i : Nat) : Nat := unpack adj6Packed 5 48 i

private def loc6Packed (i : Nat) : Nat :=
  (if i < 34 then (if i < 17 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0x8740011d0090002451220200084c990ac0004d0003624763a9812c4000af4ee3f0 else 0x3c29497c196628974000111b6ea0001d06c8df8f4198542001d48004163e425800) else (if i <
  3 then 0x2180014c000000e89b9000000000ed8001f00000000056e0006a3b15747ac00000 else 0x3f800089a6c6ea00000088000058342de3260000029c000000cf9802d41c400405)) else (if i < 6 then (if i < 5 then
  0x3a4d78001684eb02c000003be9a96cb0f39200218a053129fc001950007218d800 else 0x1078be0004497b00000026cfc00000000028000000000002c81b448c9a800) else (if i < 7 then 0x83c000003e212a979d6c3d3d200000044000000d6b220947b93301e42000000000 else
  0x65503147221510e54ccb490008ce0d00079c0000002e000cd145a4c00010003800))) else (if i < 12 then (if i < 10 then (if i < 9 then 0x5c0f2949800064df015bd447a104003af5569dcfc98584cfa13180047220dbd000 else
  0x5da60478bc244cfe400000494cd570b321e836400316292cdcff096000001169d9) else (if i < 11 then 0x6180009200037e7a8000c900000107000000ae5f28005c67885300010e209ec3a7 else 0x82c70dfa000000c400000049ad80a087e000a560034a0000013e92d0003f1a893c)) else (if i <
  14 then (if i < 13 then 0xd380018a29548ae70d41cc5780034c0005680080c0014031927057db6a8f else 0x7600027a000284000001910110f35c196a099c91d2c63957f00075421000121) else (if i < 15 then 0x79190276358073b6000000004100000001680039a000278006ce09c4f000 else
  (if i < 16 then 0x19200019c4000081a159e88006d0d100000022ebbce0a4538c24c4f87a else 0x399c680007c0019d0a969e000910cc000388003b7000b517700079af1993000))))) else (if i < 25 then (if i < 21 then (if i < 19 then (if i < 18 then
  0x8c000b2b5508a0000000085ea1e104383e8d0c001a24f8f3e008000006f0002cf else 0x562418003040c2000b005300033cea2097e6c946c3cb22a7140017416c4a187000) else (if i < 20 then 0x1a000248002ae000a880023ed200000026000000000000000518000004b02e000 else
  0x170000f80003060014a13f4a62a8000000001f481bbf54c4b8000cd0200013c000)) else (if i < 23 then (if i < 22 then 0xbfc001092da5f8002420002d412800134260000000000000000036a63127075 else 0x2f6000000000000012b057000e257e800000000002817327fd920002b8ee9ac3f8)
  else (if i < 24 then 0x3a63e8002856ac30da00006c2b683191b046054f7a377ec000b5b42000000a8000 else 0x79c14b214dc001552c2000000ae800000c2800000858000cda6b000001ec800))) else (if i < 29 then (if i < 27 then (if i < 26 then
  0x70e0016e80000000174800290e5db88007fee8c7417936e8d4468eb000ef954a03 else 0x2b481113be0000021203863103d908ac700c000000000007300020c2b605193b46) else (if i < 28 then 0x7d4b71040000000008539026cb5c4caec6d2a24001b07b8fd43a0004240008a3c3 else
  0x1c65313b000000f74000ef6ba00199804646440330000000000000000000000000)) else (if i < 31 then (if i < 30 then 0x1bca9b828e2c558c64a8e58060a821cf5d45000570001c93733504e4f90fd else 0x101c0000000103c002a50006c80036b5f83b9f480000030a181c245659119000)
  else (if i < 32 then 0x50000432042c0449292708001660000000010010b000bc00002a00011df1ab0 else (if i < 33 then 0x3466194b0004b87cd2d8005b01c0000ff3b49040000066c22ce5a611b8ad8409a5 else
  0xde0019f00000097de28590010d9a5a3445c86d112a400085cf61b342a000000c0)))))) else (if i < 51 then (if i < 42 then (if i < 38 then (if i < 36 then (if i < 35 then 0x452001500ec0004154ebc9000fe86f800402465e630600000000000030001c413d else
  0xf7d311732ccb34002185970aded8000000000012f0009bd1c409852288002f1) else (if i < 37 then 0x4e0c70bfb54000000df1693f4400000003580d4003b558a000003bb82a0017d380 else 0x6699da7e00000194090288ec9d980a000fb0638007229419831d4780fc0c800)) else (if i < 40
  then (if i < 39 then 0x4da990b63c0000f9d5f42e57eef0902a700018911800000000000de5180019faf3 else 0x5f6790ceadb2ece14003ac52e0007d80087600c001435e8745758000005f209bda) else (if i < 41 then
  0xa0d4d18e7d6000001e61c296800000000f48001e06e8000002b236200139097 else 0x356c240000049200000171068f04002d56ca0000021d000f91ce0000c89cc00000))) else (if i < 46 then (if i < 44 then (if i < 43 then
  0x4300000043c00000414f1db6286000138002d20000000000035eab89998a else 0x323064001370dc5be0ebab090b0df8800182e76050a7000000688bc73e06c8b126) else (if i < 45 then 0xca000000005a6c61d039a6f604c00182000ec1cd80031a00086ae61121b000382 else
  0xad400000068a0003f842788ad000000000000fd89d368000003942840ed15000)) else (if i < 48 then (if i < 47 then 0x3fa05d2bad6000518001d661a3f8b819771e0c000000000cb87bb5a000001cc000 else
  0x208001c5000048ef610be61385dc00206000002138000005893480086600000000) else (if i < 49 then 0x6520045b9d5074001f68854862801138e000d4d57bd37724f82c37f00000000207 else (if i < 50 then
  0x65852dcf0bd0be2d0de800316001b82b320e00045111854565838004b02c4ce000 else 0x354680be8003ba8fa0d8001ae1515e000848000c7c225d0000a38783af0f000000))))) else (if i < 60 then (if i < 55 then (if i < 53 then (if i < 52 then
  0x2942d0006117c8003eed1d0692b00032a11bb8004794db0007dc00000000 else 0x616870000005eb07cca4250006905f8f0622b88950000daab0e70000009c50f800) else (if i < 54 then 0xbabf20000000000062a894002c17c20000011e65e16800363000000af05d else
  0x24ddc002672380cc00244164000001253bc00079aa200039c3e03900092114000)) else (if i < 57 then (if i < 56 then 0x4ca16c6e9ae55a311be80087c000dc32049e001a7000434e90e006900000000260 else
  0x62529540000589a00000067a1accf2c0000c7d6502f000408003d50005598d01d) else (if i < 58 then 0x46cff50b35974a8b1828003da6a5eb0371c8000aa0000000003d9e36560000036e else (if i < 59 then 0x7fc0018439330e46052378000000003de80400172c3409a0e00014d75c000301f1
  else 0x2ce0016fb3c000d34d080051b0700004c262ba80000056a49dc18002749e400000)))) else (if i < 64 then (if i < 62 then (if i < 61 then 0x824728001bb4b2468001521ea00047b13742ff0000ed000001bb000 else
  0x1660a208a2063c71e1a8002f4ed00000011c0006700001e0d91800048d020002d1) else (if i < 63 then 0x670561b5437682000fb1c4806001682bb128a656734c176001c60005eeb91b7978 else 0x1aa8fc0001c29e955178000161e4dca9e6ae000000000bc000390e929c0002a8d3)) else (if i <
  66 then (if i < 65 then 0x2dc3803b95379091d8040e374000002a3872515ad8517f6001630000004a5fb820 else 0x10cc283eaa10003034e8d7df781a0008c45732d2105540fb31202850b9043) else (if i < 67 then
  0x74c1d9890261602301e0b9000b260ba7b000a4000161000001a93d000034000000 else (if i < 68 then 0x43f70200000000830000000d20000f5289cf000000000000002e9b3000 else 0x24b62ea7d79000)))))))

private def loc6 (i : Nat) : Nat := unpack loc6Packed 11 24 i

private def st7Packed (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0xd258ee353585647d1867bc771a9ac2b23e8c33963b8d4d61591f4618ef04c6a6b0ac8fa30c77776353585647d1863bad71a9ac2b23e8c31dc9a8d4d61591f4618ee354546b0ac8fa30c771aa143585647d1863b8d4e85ac2b23e8c31dc6a6e0d61591f4618ee35358680ac8fa30c771a9ac3145647d1863b8d4d61822b23e8c31dc6a6b0b1d591f4618ee35358564a80fa30c771a9ac2b25047d1863b8d4d61591f43c4c31dc6a6b0ac8fa1b3618ee353585647d0c9b0c771a9ac2b23e8381863b8d4d61591f4104c31dc6a6b0ac8fa060618ee353585647d01db0 else 0xc77776353585647d18e3bad71a9ac2b23e8c71dc9a8d4d61591f4638ee354546b0ac8fa31c771aa143585647d18e3b8d4e85ac2b23e8c71dc6a6e0d61591f4638ee35358680ac8fa31c771a9ac3145647d18e3b8d4d61822b23e8c40063b8d4b1d591f4538ee3535858eac8fa31c771a9ac2b25407d18e3b8d4d61592823e8c71dc6a6b0ac8fa1e2620031db585647d0d9a9c771a9ac2b23e86cd8e3b8d4d61591f4326c71dc6a6b0ac8fa0e0638ee353585647d04131c771a9ac2b23e81818e3b8d4d61591f4076c40046a6b0ac8fa03b53a731dc6a6b0ac8fa30) else (if i < 3 then 0xc771a9b83585647d1963b8d4d61a02b23e8cb1dc6a6b0c51591f4658ee35358608ac8fa320018ee352c75647d1563b8d4d6163ab23e8cb1dc6a6b0ac9501f4658ee35358564a08fa32c771a9ac2b23e87899000c76d61591f4366ab1dc6a6b0ac8fa1b3658ee353585647d0c9b2c771a9ac2b23e8381963b8d4d61591f4104cb1dc6a6b0ac8fa060658ee353585647d01db20011a9ac2b23e80ed5000c771aa14358564a40063b8d4dc1ac1f453a731dc6a6b0ac8fa31d258ee353585647d18e7bc771a9ac2b23e8c73963b8d4d61591f4638ef04c6a6b0ac8fa31 else 0x63b8d50a1ac2b2560031dc6a6e0d60fa2b0018ee352c75647d15800c76d61591f4366ac0046a6b0ac8fa03b560031dc6a850d61592a0018ee353706b07d1569cc771a9ac2b23e8cb4963b8d4d61591f4659ef1dc6a6b0ac8fa32ce58ee353585647d1963bc131a9ac2b23e8cb1dddd8d4d61591f4658eeb5c6a6b0ac8fa32c7726a353585647d1963b8d5151ac2b23e8cb1dc6a850d61591f4658ee353a16b0ac8fa32))

private def st7 (i : Nat) : Nat := unpack st7Packed 73 24 i

private def adj7Packed (i : Nat) : Nat := 0x118ccb10040004020043a010001084148020

private def adj7 (i : Nat) : Nat := unpack adj7Packed 5 48 i

private def loc7Packed (i : Nat) : Nat := (if i < 3 then (if i < 1 then 0xf4b2900012b71601817a60002b9201f000112ad6 else (if i < 2 then 0xfbb1a02c809af004c2821c314e0000000c8000 else 0x8c000727400012bd31e5c025c8aea07d0003a100)) else (if i < 4 then 0x18da2a00000d8300fd50a08549005a021ca7544c80 else (if i < 5 then 0x50000000002b30202c210002a22349089800b0e35 else 0x468e4e7d20c003ce01040000001a10)))

private def loc7 (i : Nat) : Nat := unpack loc7Packed 7 24 i

private def st8Packed (i : Nat) : Nat := 0x31dc6a6b0ac8fa2cc771a9ac2b23e8af1dc6a6b0ac8fa2ac771a9ac2b23e8a71dc6a6b0ac8fa28

private def st8 (i : Nat) : Nat := unpack st8Packed 62 24 i

private def adj8Packed (i : Nat) : Nat := 0x0

private def adj8 (i : Nat) : Nat := unpack adj8Packed 1 48 i

private def loc8Packed (i : Nat) : Nat := 0x80604040

private def loc8 (i : Nat) : Nat := unpack loc8Packed 3 24 i

private def st11Packed (i : Nat) : Nat := 0xbd8ff11c18becf991c18c2eff11998c36f991998a212c90d98a3f2b10d98af32f4e898b112dce898af3524a618b114f4a618b5147ca498b67440a498

private def st11 (i : Nat) : Nat := unpack st11Packed 40 24 i

private def st12Packed (i : Nat) : Nat :=
  (if i < 4 then (if i < 2 then (if i < 1 then
  0xa3eef92491e4162289961236828bbfc478405051f7de8f080a0b08f45258d241621e8a4a1a482c03fc47c2dd05887d28f85ba0af947c9d8a6416228993b14c82be51f2a02790588a265404f20a3f2b105098416225b9c113082bcd132c226105104145844c20af2704b0898415e68f95213082c45132a4261057ca3e4ec4c20af347c9d898416228993b13082be5132762610588a204ec4c20
  else
  0xaeaff11993b41439fe23327682733fc4664ed051f95886c9da0a3f10d0d93b4147df021b276828fbbe4364ed05177f88289da0a20ff10513b4147df7a0a276828bbef4144ed051f7cc8289da0b112dce893b41622069d127682c43e23a24ed05887a27449da0b00ff0e093b415e5fe1c127682c43e93824ed05807d27049da0b10f98e093b41399fc24b26282733fc48e4c5051b77c92c8f20)
  else (if i < 3 then
  0xaf2fa4e096140f99051c12c282733fc46658104e67b292cafa09dcf452595f413e1df24b2be82733fc46657104e67f88ccaca09ccff1199574147ddf21b2ac828fbef414559051f77c86ca9a0a20ff1051534147df7a0a2a682c43d13a254905797f8704a920b10fa4e09524198ac454929882bcd1f7f853105887a2744a620cc76ce8f94941622883fc292828fbbe43652506177f88cc9da0
  else
  0x9dcf4522161413e1df2442c282c43d1486585051f77c908b0a09ccff1209614185dfe2332c28280bfc46658504e67ea8ccb0a09ccfbd1996141399f4a332c282733e646658505887d28c0b0a0a3efbd17961414a68fa1b2c2828fcac436585051f80c86cb0a0a26ef90d96141441df21b2c28289bef41458505107de828b0a0b43620e8961416225b9d12c282c44483a258505797a2744b0a0))
  else (if i < 6 then (if i < 5 then
  0xc2eff125a3341399fe238466831251f98886d0663a3f2c90da0b6747e5621b416228fcac436800051f95886cc51f958ff10da0a3f2b1df21b4147e5624b43683275889887450662b112f4e8a00016225b9d131622a4cb73a282c451f96e745058896eff0e8a0b112dde89d1416225ba4b3a2830bbfc414705065fb47524b0a0cc568aa49614197ed9d2f2c2832fdf6a0458504e67b2910b0a0
  else
  0xc9d78e0ba4b4193ac441749683266247f892d064ec44ff125a0c2f7d9fe24b4185ef8bfc496830bdee7f892d061bbd8ff125a0c49795fe24b4193af1bfc496830ddf67cc92d0588a3ef752420b11025fe2464147e203fc48a833b5f67f88e10588a3efe51c20b1147df32384193b123fc466833b61b7f88cd0000c2eff11998c2f7d9fe2334185ec43fc466830bd1f7f88cd06179ccff119a0)
  else (if i < 7 then
  0x147e5621b32002c44b73a2672fd88a932f5065fb6747e5920cbf86efb3fc41932c44c449682d2d3598892d0588a6b31125a0c4547e6224b416968fcc4496832758898492d0624a3f30925a0af35265ea4b416229ecbd49682c454996e92d0588a832dd25a0b114fe5ba4b416a28fcb249682d9d1096492d05b3a3f2b125a0b5b47e5624b416aa8fcac49683125e589e92d0624a3f13d25a0
  else 0xc2eff11999)))

private def st12 (i : Nat) : Nat := unpack st12Packed 51 24 i

private def edgeMeta12Packed (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0x292521201d1915141414141414110d090808080808080808080808080808080808080808050100000000000000000000 else 0x6c6c6c6c6c6c6c6c6c6c696868686868686564646464646160606060606060605d5c5c5958585554544e49423a352e2c) else (if i < 3 then 0xc0c0c0c0bdb9b5b1b0b0aaa8a8a8a2a09d99929090909090908a857e7c7c7c7c7c7c79727070707070706d6c6c6c6c6c else 0xf0f0f0f0f0f0f0f0f0f0f0f0f0eae5e1ddd9d5cec9c5c1c0c0))

private def edgeMeta12 (i : Nat) : Nat := unpack edgeMeta12Packed 8 48 i

private def edgeData12Packed (i : Nat) : Nat := (if i < 1 then 0x999ba8baa998b96764549875964323421006199966644464 else 0x532444170666)

private def edgeData12 (i : Nat) : Nat := unpack edgeData12Packed 4 48 i

private def st13Packed (i : Nat) : Nat :=
  (if i < 24 then (if i < 12 then (if i < 6 then (if i < 3 then (if i < 1 then
  0xcc56228f952130a336588a3e4ec4c28cc76228f93b130a331588a3e4ec4c28b556228f93b130a33657ca3e4ec4c28b115f28f93b130a00057ca3e4ec4c20b114fe8f93b130a336588a264ec4c280016228993b13082c451fa264ec4c28af947dfe13b130a2c45137f84ec4c28af947d2593b130a2c45134964ec4c28a3eef90513b130a2c43d13824ec4c28af947cb093b130a2c45132c24ec4c28b114d66224b124a2d2d1f98892c4928b1147e6224b124a331588a925843828
  else (if i < 2 then
  0xb1144e66a4b13ca2c451f98892c4f28cd96228f95013ca331588a3f2f44c28b1147e5ba4b130a2c451f95892c4c28b1147dfe238130a331588a3e5844c28cbf6228f961130a336580a3e5844c28cc55e68f961130a331588a265844c28af947d25961130a2bcd1f4965844c28b1144d25961130a2be5134965844c28b1144125961130a2733fc4665844c28cc747d05161130a2c45134145844c28cc5620e0961130a336588a3e5644c28af947d25956130a2c45134965584c28
  else
  0xc49795fe24b1f8a31251f7f892c7e28b10f44e89611eaa2c451f98892c6928c9d621fe24b1a4a2c251f7f892c6928d6d621e8a4b1a4a2c451f7f89286928b1147e6224b19aa3275887f892c66a8a3eef90d961188a28fbef4145846228c9d621fe24b16ea32c5807f892c5ba8cb1621f4a4b16ea3415887f88f85ba8c9d6220ba4b166a3275e37f892c59a8c9d621fe24b166a28fbbe4365845528af947d2596114ca2c45134965845328cd96228f93b14ca2be51f99a92c4f28))
  else (if i < 4 then
  0xb1147dfe247262a3275887f892c96a8c4947dfe24b25aa2733fc4965849628b1147dfe24b256a2c451f7f892c9528b1147dfe24b252a2c45497a292c94a8b1147dfe24b250a2c451f7f892c93a8b1147dfe24b24aa2c451f98892c8f28c4947dfe24b23ca2c451b7f892c8f28d5f47ddf24b23ca2c451f7f89248f28cd96228f961236a2c451f98892c8d28c4947dfe24b234a31251f7f892c80a8c5945dfe24b202a31651f7de92c80a8d1547dfe23c202a31251f89e92c7e28
  else (if i < 5 then
  0xb10fa5259c1276a2733fc4147049da8b1147dfe1ba276a2c451f7f86b89da8b1147dfe183276a2733fc4665849da8a3eef90d961276a28bbfc4145849da8a3efbd05161276a2c43d13a25849da8b00ff0e0961276a2c43e93825849da8b1147dfe24b274a2c451f7f89109d28b1147dfe24b272a2c451f7f892c9c28b1147dfe24b268a2fb4e67f892c9a28b1147dfe24b266a2c451f7f892c9928c9d621fe24b262a31251f7f892c98a8d4b399fe24b262a2c451f7f092c98a8
  else
  0xc9d621fe1d1276a2c451f7f87449da8001621e89d127682c45497a27449da8b1147de89d1276a2c43fc7a27449da8b10f45259d1276a2c451f7f87349da8b1147dfe1c6276a2c451f7f87149da8d05621fe1c1276a33b5887f87049da8cc5621fe1c1276a2f75887f87049da8d05601fe1c1276a2c45807f87049da8001601fe1c127682c45417f87049da8b0147dfe1c1276a3415887d27049da8001621f49c127682c451f7d27049da8b10ff1f49c1276a2c03fc4967049da8)))
  else (if i < 9 then (if i < 7 then
  0xb6747ddf21b276a2c451f77c86c9da800147ddf21b276828fbfc77c86c9da8a3eef925a1b276a2c451f7f88609da8b1147dfe215276a2c451f7f88389da8d1547dfe20a276a33b51f7f88289da8cc747dfe20a276a2f8d1f7f88289da8b5b47dfe20a276a3455177f88289da8b1145dfe20a276a28fd177f88289da800145dfe20a276834551f7de8289da8b1147df7a0a276a00051f7de8289da0a3eff1f7a0a276a28bbfc4968289da8a3efbd25a0a276a2c451f9887449da8
  else (if i < 8 then
  0xb1147df324b276a2c45497c492c9da8b6747df024b276a2c45417a292c9da8b114fde8a4b276a2c451f79a92c9da8b5b47ddf24b276a2d551f77c92c9da8b1147dfe24a276a2c451f7f89249da8b1147dfe247276a2c451f7f89109da8c9d621fe233276a31251f7f88cc9da8b1147dfe233276a2fb4e67f88cc9da8b11399fe233276a28fce67f88cc9da8001399fe23327682733fc4968cc9da8b1147dfe22a276a2c451f98886c9da8c4947dfe21b276a2c451f7f886c9da8
  else
  0xaf947dfe24b276a2bcd1f7f892c9da8ae347dfe24b276a2c451e7f892c9da8b11475fe24b276a2c451b7f892c9da8b1145dfe24b276a2c45137f892c9da8af944dfe24b276a2c45107f892c9da8bed439fe24b276a2c450b7f892c9da8b11421fe24b276a2f8ce67f892c9da8bdd399fe24b276a2c451f7f692c9da8b1147dfd24b276a2c451f7f092c9da8b1147dfaa4b276a2c451f7e492c9da8b1147df7a4b276a2c45177de92c9da8b1147df4a4b276a2c051f7d292c9da8))
  else (if i < 10 then
  0xb1147e0ba4b276a2c454981a92c9da8b1147e01a4b276a30bdf67f892c9da8c49795fe24b276a3275e37f892c9da8c99621fe24b276a2f2d887f892c9da8bed5d5fe24b276a2d2d357f892c9da8b114d5fe24b276a2c452a7f892c9da8b1148dfe24b276a31151f7f892c9da8bc747dfe24b276a2d2d1f7f892c9da8b4547dfe24b276a2cfd1f7f892c9da8b1947dfe24b276a2c451f7f892c9da8b0f47dfe24b276a2c351f7f892c9da8b0947dfe24b276a2c051f7f892c9da8
  else (if i < 11 then
  0xb1147dfe24b27ca2c451f7f892c9ea8b1147dfe24b278a32fd88a3eff09da8af947dfe273276a2c45137f89cc9da8b1147dfe26b276a2c451f7f89a89da8b1147dfe269276a2c451f7f89509da8b1147dfe251276a2c451f7f893c9da8b1147e8024b276a2c453598892c9da8b4b47e6224b276a2c451f98492c9da8b115265ba4b276a2d9d1f95892c9da8bcb62227a4b276a31251f89e92c9da8b1147e27a4b276a2d9d1f88692c9da8c9d6220ba4b276a2f1d1f82e92c9da8
  else
  0xb556228f9612a0a2c453fa3e584a828af947dfe1612a0a2c45137f8584a828b1147dfe24b29ea331588a3eff0a628b1147dfe24b298a2c45497a292ca628b1147dfe20a298a331d88a3eff0a4a8b1147dfe24b292a2d9d1f77c92ca4a8b1147dfe1c1292a2c451f7f892ca428b1147dfe24b28ea2c451f7f892ca328b6747ddf24b28ca2c451f7f892ca2a8b1147dfe24b288a2c451f7f892ca1a8b1147dfe24b284a2c451f7f892ca0a8b1147dfe24b280a2c451f7f892c9fa8))))
  else (if i < 18 then (if i < 15 then (if i < 13 then
  0xb6747ddf24b2aca2c451f7f886cab28d1547dfe20a2aca3415887f8704ab28b1147dfe24b2aaa2c451f7f892caa28b1147dfe24b2a6a2be51f7f892ca9a8b11441fe24b2a6a2c451f7de92ca9a8b6747ddf24b2a6a331d1f7f8828a9a8b1147dfe24b2a4a2bcd1f7f892ca928b1144dfe24b2a4a2c451f7d292ca928b11525e8a4b2a4a3315887f8704a928cbf6228fbfc2a2a2c451f7f892ca8a8b1147df224b2a0a2c451f7c292ca828b1147dfe23e2a0a2c451f7f88f0a828
  else (if i < 14 then
  0xb6747ddf24b2b2a2c451f7f88ccaca8b00ff1259c12b2a2c43e9496704aca8b1147dfe24b2b0a2c451f7f892caba8b0147dfe24b2aea2c45177f892caba8bed399fe24b2aea2c451f7cc92caba8b1147e27a4b2aca2c451f82e92cab28b1147dfe24b2aca2c3d1f7f892cab28b0147dfe24b2aca2be51f7f892cab28b11479fe24b2aca2c45177f892cab28b1144dfe24b2aca2be5137f892cab28bed399fe24b2aca2c451f7de92cab28b1147df4a4b2aca2c45497a292cab28
  else
  0xb1147df4a4b2b8a2c45497a292cae28b6747ddf24b2b8a2c451f7f88ccae28a2eff125a0a2b8a28fbef496828ae28b1147dfe24b2b6a2c451f7f892cad28bcb621fe24b2b2a2c45357f892caca8b1947dfe24b2b2a2c451f7f892caca8b0d47dfe24b2b2a2c051f7f892caca8af947dfe24b2b2a2c45177f892caca8b1144dfe24b2b2a2fb4e67f892caca8b1147dfda4b2b2a2c451f7ea92caca8b1147df7a4b2b2a2c451f7d292caca8b0147df4a4b2b2a2c45497a292caca8))
  else (if i < 16 then
  0xb1147dfe24b2bea2c44f87f892cafa8a3f3b9fe24b2bea2fb4e67f892cafa8b1147deca4b2bea2c45497a292cafa8b6747ddf24b2bea2c451f7f8910afa8b1147dfe24b2bca2c451f7f892caea8b1148dfe24b2b8a2f1d1f7f892cae28b4b47dfe24b2b8a2c451f7f892cae28b0147dfe24b2b8a2be51f7f892cae28b11475fe24b2b8a2c45177f892cae28b1144dfe24b2b8a2fb4e67f892cae28b1147dfd24b2b8a2c451f7ea92cae28b1147df7a4b2b8a2c45177de92cae28
  else (if i < 17 then
  0xb10fa5259cb2c2a3315887f8704b0a8cbf621fe1c12c2a34157c7f8704b0a8cc55e5fe1c12c2a3315887d2704b0a8b00ff1259c12c2a2bcbfc496704b0a8b10fa5259c12c2a2c03e9496704b0a8b10f99259c12c2a28fbbe436704b0a8cecff1051c12c2a28fbef414704b0a8b10fa5051c12c2a2c43d14966fcb0a8b1147dfe24b2c0a2c051f7f892cb028b1145dfe24b2c0a2fb4e67f892cb028b1147dfaa4b2c0a2c451f7de92cb028b1147df4a4b2c0a2c451f7f88ccb028
  else
  0xb1147e0aa1b2c2a2c45137f886cb0a8cd947ddf21b2c2a331d1f77c86cb0a8a3eef925a1b2c2a28fbbe496868b0a8a2eff125a132c2a28fbef49684cb0a8cc747dfe20a2c2a32fd1f7f8828b0a8d1544dfe20a2c2a331d107f8828b0a8cd947df7a0a2c2a331d1f7de828b0a8a2eff125a0a2c2a2883fc496828b0a8a3efbd25a0a2c2a28bbef496828b0a8a3ef9925a0a2c2a2c43d149674cb0a8cc5621e89d12c2a2c43d1496744b0a8b10f45051d12c2a2c03fc49672cb0a8)))
  else (if i < 21 then (if i < 19 then
  0xbe347dfe23c2c2a2d6d1f7f88f0b0a8b11475fe23c2c2a2c45177f88f0b0a8b1147dfd23c2c2a2c451f7de8f0b0a89ccff125a372c2a3275887f88ccb0a8b11505fe2332c2a31251f7f88ccb0a8b5b47dfe2332c2a3504e67f88ccb0a8d15399fe2332c2a3414e67f88ccb0a8ced399fe2332c2a2c451f7ea8ccb0a8b1147df7a332c2a2c451f7d28ccb0a89ccff125a332c2a3415887f88c0b0a8d1547dfe22f2c2a28fbbe496874b0a8b114fe8fa1b2c2a2c451f98886cb0a8
  else (if i < 20 then
  0xb1147dfe2482c2a2c451f7f891cb0a8aef47dfe2472c2a2c450f7f891cb0a8bed399fe2472c2a2c451f7f091cb0a8b1147dfe2462c2a2c451f7f8914b0a8b1147dfe2442c2a2c44f87f8910b0a8a3f3b9fe2442c2a2fb4e67f8910b0a8b1147deca442c2a2c45497a2910b0a8b6747ddf2442c2a2c451f7f890cb0a8b1147dfe2422c2a2c451f7f8904b0a8bdd621fe23e2c2a2c45417f88f8b0a8b0d47dfe23e2c2a2c051f7f88f8b0a8b1147dfda3e2c2a2c451f7d28f8b0a8
  else
  0xb5747ddf24b2c2a2d551f77c92cb0a8b5147ddf24b2c2a2d3d1f77c92cb0a8b6746ddf24b2c2a2d9d1777c92cb0a8b6744ddf24b2c2a2d9d1077c92cb0a8d2f3e1df24b2c2a2d9d1f77a92cb0a8b5d47ddea4b2c2a2d1d4976092cb0a8b674bdd824b2c2a2fb50276092cb0a8b1147dfe24a2c2a2c251f7f8928b0a8b11039fe24a2c2a2c451f7c8928b0a8b11525e8a4a2c2a2c451f7f8924b0a8b1146dfe2492c2a28fc447f8924b0a8b1147df0a492c2a2d9d1f77c924b0a8))
  else (if i < 22 then
  0xb11521e8a4b2c2a2c45477a292cb0a8b11519e8a4b2c2a2c45457a292cb0a8b11511e8a4b2c2a2c45437a292cb0a8b11505e8a4b2c2a2c453f7a292cb0a8b114f5e8a4b2c2a2c45347a292cb0a8d2f3b9e8a4b2c2a2c45497a092cb0a8b11511e824b2c2a2c451f79a92cb0a8b1147de624b2c2a2d9d2a77c92cb0a8d2b47ddf24b2c2a2d9d1f77c92cb0a8b6547ddf24b2c2a2d8d1f77c92cb0a8b6147ddf24b2c2a2d7d1f77c92cb0a8b5d47ddf24b2c2a2d6d1f77c92cb0a8
  else (if i < 23 then
  0xb1147df424b2c2a2c451f7ce92cb0a8b1147df324b2c2a2c051f7cc92cb0a8b1145df324b2c2a2fb4e67cc92cb0a8b11505f224b2c2a2c251f7c892cb0a8b11525f124b2c2a2d6d1f7c292cb0a8b1146df0a4b2c2a2d9d1f7c092cb0a8b11505eca4b2c2a2d6d1f7b292cb0a8d2f399eca4b2c2a2d9d1f7b092cb0a8b11525eb24b2c2a34b5887a292cb0a8b45525e8a4b2c2a2c45497a292cb0a8b09525e8a4b2c2a2c05497a292cb0a8af9525e8a4b2c2a2bcd497a292cb0a8
  else
  0xb1145df7a4b2c2a2c45137de92cb0a8b11441f7a4b2c2a2fb4e67de92cb0a8b1147df724b2c2a2c451f7da92cb0a8b1147df624b2c2a2c451f7d692cb0a8b1147df524b2c2a2f4d887d292cb0a8b114edf4a4b2c2a2c45357d292cb0a8b114bdf4a4b2c2a2c452a7d292cb0a8b114a1f4a4b2c2a2c651f7d292cb0a8b1147df4a4b2c2a2c351f7d292cb0a8b0147df4a4b2c2a2be51f7d292cb0a8af347df4a4b2c2a2c45177d292cb0a8b1144df4a4b2c2a2fb4e67d292cb0a8)))))
  else (if i < 36 then (if i < 30 then (if i < 27 then (if i < 25 then
  0xb1143dfc24b2c2a2fb4e67f092cb0a8b1147dfba4b2c2a2c451f7ec92cb0a8b1147dfaa4b2c2a2c051f7ea92cb0a8b1145dfaa4b2c2a2fb4e67ea92cb0a8b1147dfa24b2c2a2c451f7e692cb0a8b1147df924b2c2a2c451f7e292cb0a8b1147df824b2c2a2c45237de92cb0a8bc947df7a4b2c2a2d351f7de92cb0a8b4b47df7a4b2c2a2d1d1f7de92cb0a8b4547df7a4b2c2a2c851f7de92cb0a8b1147df7a4b2c2a2c051f7de92cb0a8af947df7a4b2c2a2c451d7de92cb0a8
  else (if i < 26 then
  0xd29399fe24b2c2a2fc4e67f892cb0a8bed399fe24b2c2a2face67f892cb0a8be9399fe24b2c2a2f9ce67f892cb0a8be5399fe24b2c2a2f8ce67f892cb0a8bdd399fe24b2c2a2f64e67f892cb0a8bd7399fe24b2c2a2fb4e57f892cb0a89cd1f5fe24b2c2a28dc447f892cb0a8b09039fe24b2c2a2c451f7f692cb0a8b0d47dfda4b2c2a2c051f7f692cb0a8b1147dfd24b2c2a2c451d7f492cb0a8b1145dfd24b2c2a2c451f7f292cb0a8b1147dfc24b2c2a2bbd1f7f092cb0a8
  else
  0xb11459fe24b2c2a2c45157f892cb0a8b11451fe24b2c2a2c45137f892cb0a8b0f44dfe24b2c2a2c05137f892cb0a8af944dfe24b2c2a2bcd137f892cb0a8b11449fe24b2c2a2c45117f892cb0a8b11441fe24b2c2a2be5107f892cb0a8be343dfe24b2c2a2fb50e7f892cb0a8b1142dfe24b2c2a2c450a7f892cb0a8b11421fe24b2c2a2c45077f892cb0a8bed405fe24b2c2a2f8cf87f892cb0a8bed3ddfe24b2c2a2fb4f27f892cb0a8bdd3b9fe24b2c2a2fb4ec7f892cb0a8))
  else (if i < 28 then
  0xaf947dfe24b2c2a2bdd1f7f892cb0a8af547dfe24b2c2a2bcd1f7f892cb0a8ae347dfe24b2c2a2b851f7f892cb0a8b11479fe24b2c2a2c3d1e7f892cb0a8af9479fe24b2c2a2c451d7f892cb0a8b11471fe24b2c2a2c451b7f892cb0a8b11469fe24b2c2a2c45197f892cb0a8b11461fe24b2c2a2f25177f892cb0a8bc745dfe24b2c2a2d35177f892cb0a8b4745dfe24b2c2a2d15177f892cb0a8b2145dfe24b2c2a2c45177f892cb0a8b0145dfe24b2c2a2be5177f892cb0a8
  else (if i < 29 then
  0xb014a1fe24b2c2a2c45237f892cb0a8c4547dfe24b2c2a2f851f7f892cb0a8bc747dfe24b2c2a2dd51f7f892cb0a8b5947dfe24b2c2a2d2d1f7f892cb0a8b4547dfe24b2c2a2cfd1f7f892cb0a8b3147dfe24b2c2a2c651f7f892cb0a8b1147dfe24b2c2a2c3d1f7f892cb0a8b0d47dfe24b2c2a2c2d1f7f892cb0a8b0947dfe24b2c2a2c1d1f7f892cb0a8b0547dfe24b2c2a2c0d1f7f892cb0a8b0147dfe24b2c2a2bfd1f7f892cb0a8afd47dfe24b2c2a2bed1f7f892cb0a8
  else
  0xb6747e0324b2c2a2c451f80692cb0a8af947e0124b2c2a2c451380492cb0a8c2f7d9fe24b2c2a3125e57f892cb0a8c9d78dfe24b2c2a3265887f892cb0a8bdb621fe24b2c2a2f2d887f892cb0a8bd3601fe24b2c2a2f2d807f892cb0a8bdd5ddfe24b2c2a2fb5757f892cb0a8b45505fe24b2c2a2c45407f892cb0a8b014edfe24b2c2a2c45367f892cb0a8b4b4d5fe24b2c2a2c45357f892cb0a8b014bdfe24b2c2a2d6d2a7f892cb0a8b114a9fe24b2c2a2c052a7f892cb0a8)))
  else (if i < 33 then (if i < 31 then
  0xb114d66224b2c2a2d2d1f98892cb0a8b1147e6124b2c2a2c454996e92cb0a8b6747e5624b2c2a2be51f8a092cb0a8b1144e2824b2c2a2f2d8889e92cb0a8c4947e27a4b2c2a2c451f89e92cb0a8af947e27a4b2c2a2c451f89492cb0a8b115262424b2c2a2d551f88892cb0a8b6747e21a4b2c2a2be51f83092cb0a8b1144e0c24b2c2a32758882e92cb0a8bc747e0ba4b2c2a2c451f82e92cb0a8b1144e0ba4b2c2a2c451f82492cb0a8b114fe0724b2c2a2c454981a92cb0a8
  else (if i < 32 then
  0xcbf6228fbe92c2a32fd88a3ef98b0a8cbf622a4bd12c2a32fdb3a3eef8b0a8b1147dfe2682c2a2c451f7de948b0a8b43622a4a4b2c2a2d5588a5492cb0a8b536228fa4b2c2a2d153fa3e92cb0a8b114fa8fa4b2c2a2d9d29a3e92cb0a8af947e8124b2c2a2c4513a0492cb0a8bdd6228024b2c2a2f8d1fa0092cb0a8b1147e8024b2c2a2be51fa0092cb0a8b1144e8024b2c2a2c453f9f092cb0a8b115267b24b2c2a2d551f9dc92cb0a8b6747e75a4b2c2a2fb5009cc92cb0a8
  else
  0xb1147dfe24b2c8a2c651f7f892cb1a8b1147dfe24b2c6a2c051f7f892cb1a8b1147df4a4b2c6a2c451f7f892cb128af947dfe24b2c4a2c45137f892cb128cbf6228fd022c2a32fd88a5eff0b0a8cbf68e8fbfc2c2a3315a2a3eff0b0a8cbf6228fbfc2c2a331d80a3eff0b0a8cbf6028fbfc2c2a32fd7ca3eff0b0a8cbf5e68fbfc2c2a331588a2eff0b0a8cbf6228bbfc2c2a32fd88a26ff0b0a8cbf622883fc2c2a32fdf69ccff0b0a8cc56228fbef2c2a32fd88a3efbcb0a8))
  else (if i < 34 then
  0xb4b47dfe24b2f0a2c451f7c892cbc28b1147df0a4b2f0a2c451f7f88f8bc28b1147dfe23c2f0a2c451f7f892cbba8b1147dfe24b2e4a2c453fa3e92cb8a8b11505fe24b2e2a2d151f7f892cb8a8b1147dfe24b2e2a2c45497a292cb8a8b1147dfe24b2d8a2d5588a3e92cb5a8b114a9fe24b2d6a2d6d1f7f892cb5a8b1147dfe24b2d6a2d9d1f77c92cb5a8b1147dfe24b2cea2c451f7f892cb328b1148dfe24b2caa2c451f7f892cb2a8b1145dfe24b2caa2c451f7de92cb2a8
  else (if i < 35 then
  0xb1147dfe26347ca2c450f7f892d1f28b11039fe24b47ca2c451f7f892d1ea8b1147dfe266478a2bbd1f7f892d1e28a3f111fe24b478a2c451f7f88f91e28b1147dfe24b476a35d588a3eff11c28ced6228fbfc470a2c451f7f89cd1c28b1147dfe24b470a2fb4e67f892d1c28c37399fe24b466a28fcb277c92d0da8cc747e593fc414a30bd1f7f892d0528a3f2b1fe24b414a2c44bd7a292ce8a8cc56225ebfc382a30bd887f892ce0a8b112ddfe24b382a2c45357f892cbc28
  else
  0xb6747e593b0496a30ddf67f8ec125a8b1147e0ba66496a2f1d1f7f899925a8b1143dfe266496a2c440e7f899925a8b1147dfe265496a2c451f89e98d25a8bcb621fe263496a2bbd1f7f898d25a8a3f111fe263496a2c451f7f898925a8b1147dfe25d496a2c451fa0097125a8bdd621fe25c496a2f8d1f7f897125a8b1147dfe25c496a2fb4e67f897125a8c596228fbfc494a32c588a3eff124a8c376228fbfc490a2c451f99aff123a8b1147e593fc48ca2c451f97aff122a8))))
  else (if i < 42 then (if i < 39 then (if i < 37 then
  0xb1147e66bdd496a314d88a92f4525a8c37622a4bd1496a2c453b99af4525a8b115265ebd1496a2c454197af4525a8b114fe5ebd1496a2c454996ef4525a8b11526593d1496a2c4549956f4525a8b11526523d1496a32c588830f4525a8cab6ce8fbbe496a30ddb3a3eef925a8b4d47e66bbe496a2d9d1f97aef925a8b6747e593be496a2d6d1f964ef925a8b5547e593be496a2d9d1f958ef925a8b6747e55bbe496a2d9d1f948ef925a8c5947e283be496a2c454997aec125a8
  else (if i < 38 then
  0xc376228fbef496a2c451f97afbd25a8b1147e5e3ef496a2c451f964fbd25a8b1147e55bef496a30dd88a3efa525a8b1147e5ebe9496a2c451f964fa525a8b1147e58be9496a2c451f956fa525a8c376228fbe6496a2c451f99af9125a8b1147e623e4496a2c451f964f9125a8b1147e66be2496a2c451f988f8925a8b1147e66be1496a2c451f988f8525a8b1147e5ebe1496a2c451f99af8125a8b1147e623e0496a2c451f99cf7925a8b1147e66bde496a356588a3ef7525a8
  else
  0xc5947e21bfc496a31251f886ff125a8c5b47e20bfc496a31651f882ff125a8d4347e203fc496a31651f880ff125a8c9d6220c3fc496a32758882eff125a8cb1622073fc496a32758881cff125a8c37622073fc496a32c58881aff125a8c9d62206bfc496a32cd88814ff125a8cb1622053fc496a351588812ff125a8cb162204bfc496a2c451f97afed25a8b1147e593fa496a30dd88a3efe525a8b1147e66bf8496a2c451f994fe125a8b1147e5ebf8496a2c451f964fe125a8))
  else (if i < 40 then
  0xb1147e55bfc496a2c051f956ff125a8af947e55bfc496a2c4517956ff125a8b1144e55bfc496a2fb4e6956ff125a8b1147e553fc496a2c451f952ff125a8b1147e543fc496a2c451f94eff125a8b1147e533fc496a2c451f94aff125a8b1147e523fc496a2fb4e6948ff125a8b1147e51bfc496a2c451f944ff125a8b1147e50bfc496a2c451f940ff125a8b1147e4fbfc496a31251f8a0ff125a8c4947e27bfc496a31651f888ff125a8c4947e223fc496a30dd1f888ff125a8
  else (if i < 41 then
  0xb1147e5abfc496a2c451f968ff125a8b1147e59bfc496a2c452a964ff125a8b5b47e593fc496a2c451f964ff125a8b0f47e593fc496a2c251f964ff125a8b0147e593fc496a2be51f964ff125a8aef47e593fc496a2c451c964ff125a8b1145e593fc496a2c4513964ff125a8b11442593fc496a2fb4e6964ff125a8b1147e58bfc496a2c051f962ff125a8b1147e583fc496a2c451f95eff125a8b1147e573fc496a2c451f95aff125a8b6747e563fc496a2c451f958ff125a8
  else
  0xb1147e603fc496a2c451f97eff125a8b1147e5f3fc496a2c454197aff125a8b4547e5ebfc496a2c451f97aff125a8b0b47e5ebfc496a2c051f97aff125a8af947e5ebfc496a2bcd1f97aff125a8b1147a5ebfc496a2c451b97aff125a8b1145e5ebfc496a2c451397aff125a8b1143e5ebfc496a2fb4e697aff125a8b1147e5e3fc496a2c4517978ff125a8b1147e5dbfc496a2c451f974ff125a8b1147e5cbfc496a2c451f970ff125a8b115265bbfc496a2c451f96eff125a8)))
  else (if i < 45 then (if i < 43 then
  0xcab6228dbfc496a30dd88a36ff125a8c376228bbfc496a30dd88a26ff125a8c3562289bfc496a32c588a1eff125a8c9d62287bfc496a32c588a1cff125a8c9d622873fc496a30ddf69ccff125a8c2f7da733fc496a30ddf19ccff125a8c377ba733fc496a3165e99ccff125a8cb1792733fc496a2c453599aff125a8b4b47e66bfc496a2c451f994ff125a8bed39a653fc496a2c451f992ff125a8b1147e643fc496a2c4535988ff125a8b4b47e623fc496a2c451f986ff125a8
  else (if i < 44 then
  0xc4f6228fbfc496a311d88a3eff125a8c3d6228fbfc496a30ed88a3eff125a8c396228fbfc496a30dd88a3eff125a8c356228fbfc496a30cd88a3eff125a8c316228fbfc496a30bd88a3eff125a8c2d6228fbfc496a30dd86a3eff125a8c596128fbfc496a314d84a3eff125a8c376128fbfc496a30dd80a3eff125a8c375f28fbfc496a30d57ca3eff125a8c595de8fbfc496a312577a3eff125a8c595d68fbfc496a312575a3eff125a8c376228ebfc496a32c588a36ff125a8
  else
  0xc9d6228fc17496a327624becff125a8ced86efb3fc496a000617becff125a0001892f2bfc496800064ebc6ff125a0c2f7dac43fc496a30ddeeb10ff125a8c59796c43fc496a3125e5b10ff125a8c9d792c43fc496a3275e3b10ff125a8c2f7da8fbfc496a30ddf1a3eff125a8c497a68fbfc496a3125e5a3eff125a8cb178e8fbfc496a3275e3a3eff125a8cab6228fbfc496a32a588a3eff125a8ca76228fbfc496a326d88a3eff125a8c536228fbfc496a314588a3eff125a8))
  else (if i < 46 then
  0xcbf6228fcb27f8a32fd88a3f291fe28c376228fd00496a327588a9331125a80016229acc449683125b3a3f31125a80016968fcc449682d3588a3f31125a8b4b6228fcc4496a2c453ba3f31125a8b114d68fcc4496a331588a932f525a8b114fe8fcbd496a000588a932dd25a0b115268fcb7496a331db3a3f2c925a8b556228fcb2496a0005b3a3f2b125a0b676228fcac496a000624a3f13d25a0c596228fc4f496a312588a3f13d25a800193ac4417496832c588a3f05d25a8
  else (if i < 47 then
  0x1622a4cb749684005b3a3f2b125a10018928fc4f496840064eb1105d25a100185efb3fc4968400624bcaff125a100193af1bfc496840058889092cb0a100147e0324b2c284004f27f892cb0a100147d25a1a2c284005884966fcb0a1001399fe233276840051f77c86c9da100145dfe20a276840051f7de8289da1001621e89d127684005807f87049da1001621f49c127684003fc49658496210015f28f93b1308400588a264ec4c21cbf86ec451f7f8a32fd88a3f2f5fe28
  else 0x16229acc449684005a5a3f31125a1))))))

private def st13 (i : Nat) : Nat := unpack st13Packed 62 24 i

private def edgeMeta13Packed (i : Nat) : Nat :=
  (if i < 12 then (if i < 6 then (if i < 3 then (if i < 1 then 0x17917816a16815a14a14814814814813a12a1211121091010f20e90e10e00d90d80d10c90ba0aa09a08a08107907807807106906806806806806806804c02c02802802101900a001 else (if i < 2 then
  0x2e12d22c22c02c02c02c02c02c02c02c02c02c02b92aa2a129928a27a27827126925a25124923a23123023022921a2112021f21f01f01f01e91e11d21c91c11b21a91a119918a181 else
  0x3ca3c13ab3a139939138938838838837a36a35a35134934834834134033933833833833833831c3183183183113093083083013003003003003003003003003003003003002f22e9)) else (if i < 4 then
  0x55a54a53a52a51a51850a4fa4f84f84f84f84ea4da4d14c94c14b94a349949848a47a47146946144b44143943843843842a41a40a4013f93f13f03f03f03e93e83e83e83e83e83da else (if i < 5 then
  0x67166266065965865864a6416326296216206206126096016006006006006006006005f95f15e25e05e05e05e05d95d15c95ba5aa5a85a859a58a588588588588588581579571569 else
  0x7307307297217207127106fb6f86ea6e86d36d06d06d06d06d06d06d06d06d06d06d06d06d06d06d06d06c96c16c06c06c06c06c06c06c06c06c06b26a96a1699698691682680679))) else (if i < 9 then (if i < 7 then
  0x7e87e17d97d17d07d07d07d07c27c07c07c07c07c07c07c07c07c07c07c07c07b97b87b87b17a97a17a07a07a07a07a0799791782772770762759751742732730730730730730730 else (if i < 8 then
  0x8408398318298218198118108108108108108108108108108108108108098088088088088088088088017f97f17f07f07f07f07f07f07f07f07f07f07f07e97e87e87e87e87e87e8 else
  0x98898197295b95195095095095095094993a92a91a9119028f98f18e28e08cb8c18b98b88b88b88b88b88aa89a891882879871862859851850850850850850850849848848848841)) else (if i < 10 then
  0xa70a70a70a70a69a68a68a68a68a61a59a51a49a41a39a31a29a21a20a20a20a19a18a11a10a10a10a09a08a01a00a00a00a00a009f29e29d29bb9b19a99a1999991989988988988 else (if i < 11 then
  0xaf0af0af0af0af0af0af0af0ae9ae8adaad8ad8ad8ad8ad8ad1ad0ad0ad0ad0ad0ad0ad0ad0ad0ac9ac8ac1ac0ab9aaaa9aa98a98a91a89a81a80a80a80a80a79a78a78a78a78a71 else
  0xb68b61b59b51b50b50b50b50b50b49b48b48b48b48b48b48b48b48b48b48b41b40b40b39b38b38b38b38b38b2ab28b28b28b28b28b28b28b28b1ab18b18b11b09b08b01b00b00af2)))) else (if i < 18 then (if i < 15 then (if i < 13 then
  0xb89b88b88b88b88b88b88b88b88b81b80b80b80b80b80b80b80b80b80b80b80b80b80b80b80b79b78b78b78b78b78b71b70b70b70b70b70b70b69b68b68b68b68b68b68b68b68b68 else (if i < 14 then
  0xba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0b99b98b98b98b98b98b98b98b98b98b98b91b90b90b90b90b90 else
  0xba9ba8ba8ba8ba1ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0)) else (if i < 16 then
  0xc00c00bf2be2be0be0bd9bd8bd8bd8bd8bd1bd0bd0bd0bd0bd0bd0bd0bd0bd0bd0bd0bd0bd0bd0bd0bc9bc1bc0bb9bb8bb8bb8bb8bb8bb1bb0bb0bb0bb0bb0bb0bb0bb0bb0bb0bb0 else (if i < 17 then
  0xc30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c29c21c19c11c10c10c10c10c10c10c10c10c10c02c00c00 else
  0xd09d01d00d00d00d00d00d00d00d00d00d00d00d00d00d00d00d00d00d00cf9cf8cf1ce9ce8ce8ce8ce8ce8ce8ce8ce8ce8ce1cd2cd0cd0cbbca3c8bc88c7ac6ac53c50c42c32c30))) else (if i < 21 then (if i < 19 then
  0xd50d50d50d50d50d50d50d50d50d50d42d40d40d40d40d39d38d38d38d38d31d30d30d29d28d28d28d28d28d28d28d21d20d20d20d20d20d20d20d20d20d20d20d19d18d18d18d11 else (if i < 20 then
  0xd78d78d78d78d78d78d78d78d78d78d78d78d78d78d78d78d78d78d78d78d78d78d78d78d78d71d70d70d69d68d68d68d68d68d68d68d61d60d60d59d58d58d58d51d50d50d50d50 else
  0xdb8db8db8db8db8db8db8db8db8daada8da8da8da8da8da8da8da8da8da8da8da8da1d99d98d98d98d98d98d98d98d98d98d98d98d98d98d98d8ad88d88d88d88d88d88d88d81d79)) else (if i < 22 then
  0xdd8dd8dd8dd8dd8dd8dd8dd8dd8dd1dd0dd0dd0dd0dd0dd0dd0dd0dd0dd0dd0dc9dc8dc8dc8dc8dc8dc8dc8dc8dc8dc8dc1dc0db9db8db8db8db8db8db8db8db8db8db8db8db8db8 else (if i < 23 then
  0xf19f18f18efcef8edced8ed8ed8ed8ed8eb5eb0e9be91e6de68e53e49e48e48e48e48e48e48e2ce05debde8de8de1de0de0de0de0de0dd9dd8dd8dd8dd8dd8dd8dd8dd8dd8dd8dd8 else 0xf60f60f59f51f50f50f49f48f48f48f48f48f48f48f41f39f38f38f31f30f30f30f30f30f29f21)))))

private def edgeMeta13 (i : Nat) : Nat := unpack edgeMeta13Packed 12 48 i

private def edgeData13Packed (i : Nat) : Nat := (if i < 5 then (if i < 2 then (if i < 1 then 0xc0d0c980a930b0906090504070302010800590807040206050402040003020401020129260b04201d0a02a1a1a09e63 else 0x1a191a199d869c871818171716a29e908d15141514919190874913131212a09f8e8c111011108f8f8e86500f0e0f0e0d) else (if i < 3 then 0x2a297372716f2c706e282628242726282625256d226d21206b67236a6968661f1d1f1b1e1d1f1c1d1c652d281f5a514a else (if i < 4 then 0x1f041e0328020127008b2e8a2d892d26251d1c241b9921942a98209720932992297e2f7e2e2d7b7a797c783077752b75 else 0x3b3a38060537993938370d0c363599363433329433310f0e9d9c232c9190942b8f8e992230a28d878b2fa1a09f8c869e))) else (if i < 8 then (if i < 6 then 0x262546246c4839204b473847371f1e071d1c461b524645454243444443424141282640401f1d8b3f3d3e3e3d3b3a943c else (if i < 7 then 0x1217195e5f60605f5e5d5c5b111015145845574156407d553f5857562d54534f4f3e744e3c294d4c3b4d3d4c3a282708 else 0xa564a4624b524a511649505a09595b881a58534d4c57544756855560445d63139b489a5f435c96184f954e5e42646261)) else (if i < 9 then 0x9490828e8380857fa09e84676fa5a4a384838280817f8b8176887d769674318965920b9a6c348a65970a61626463a361 else (if i < 10 then 0x6d9e9490759b9a996c366b6a6669969594743373716e728b87867e8b8885817d7c7b777a798b8786789b356899953270 else 0xa6a7a8a8a7a6a3a5a4a0998e))))

private def edgeData13 (i : Nat) : Nat := unpack edgeData13Packed 8 48 i

private def st14Packed (i : Nat) : Nat :=
  (if i < 55 then (if i < 27 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then
  0xb1147dfe24b2c20558580a3eff12596102ac2c451f7d292cb0815616228fbfc4965640ab0b1147dfe24b2760558588a3eff125961028c2c451f7f892cb0813616228fbfc4965940930b1148dfe24b2c20498588a3eff125961024c2c45177f892cb0812616228fbef4965840930b1147dfe24b2b80498588a3eff12593b024c2c451f7f892cb0811616228fbfc4965840830b1147dfe24b2c20358588a3eff125961016c2c451f7f892cb080a616228fbfc4965840430b1147dfe24b2c20158588a3eff125961004c2c451f7f892cb0801616228fbfc4965840030
  else (if i < 2 then
  0xb1147dfe24b2760a58588a3eff125961050c2c451f7f892cb0827616228fbfc4965841330b1147e593fc4960958588a3eff12596b04ac2d5588a3e92cb082561622953fc49658412b0b5b47dfe24b2c20958588a3eff12596104ac2d9d1f77c92cb0825616228fbfc4964ec12b0b1147dfe24b2c20898588a3eff125961042c2c451f7f892cb101f616228fbfc4965840fb0af947dfe24b2c207d8588a26ff12596103ec2c451f7f892cab01f616228fbfc4964ec0fb0b1147dfe24b2c20798588a3eff125961032c2c451f7f892cb1815616328fbfc4965840ab0
  else
  0xb1147dfe24b2c212d8588a3eff12593b096c2c451f7f892cb084a616228fbfc49658424b0b1147dfe24b2c21218588a3f2c9fe24b08ec2c451f7f892cb0847616ce8fbbe49658423b0b1147dfe24b27611d8588a3eff12596108cc30dd88a3eff125845616228fbfc49658422b0b1147dfe24b2c21118588a3eff125961086c2c451f7f892c9d843616228fbfc4965842130b1147dfe24b2761098588a3eff125961082c2c451f7f892cb0840616228fbfc4965841fb0b1147dfe24b2c20ad8588a3eff12593b056c2c451f7f892cb082a616228fbfc49658414b0))
  else (if i < 4 then
  0xb1147e26a4b2c21b58588a3eff1259610dac2c451f7a292cb086d616228fbfc4964ec36b0b1147dfe24b2c21b18588a3eff1259610d6c2c451f7f892cb086a616228fbfc49658434b0b1147dfe24b2c21a18588a3eff1259610cec2fb4e67f892cb0867616228fbfc4964ec33b0b1147dfe24b2c21998588a3eff1259610cac2c451f7f892cb0864616228fbfc4965842a30c376228fbfc49614d8588a3eff1259610a6c2fb4e67f892cb0853616228fbfc4964ec29b0b1147dfe24b2c21498588a3eff12593b0a4c2c451f7f892cb084c616228fcab7f892c25b0
  else (if i < 5 then
  0xb114d5fe24b27624985a5a3eff12593b124c2c451f7f892c9d892616228fbfc4965843b30b1147dfe24b2c21d58588a3eff1259610e8c2c451f97aff125873616228fbfc49658439b0b11525e8a4b2c21cd8588a3eff12593b0e6c2c451f7f892cb0872616228fbfc49658438b0b1147e5ebfc4961c18588a3eff1259710e0c331588a3eff0b0870616229fd1f4965843830b11505fe24b2c21c185a2a3eff1259610e0c2c451f7f892cb087061622a4bd14965843830b1147dfe24b2761c18588a3eff1259610dec2c451f7f892c9d86f616228fbfc4965843730
  else
  0xcd96228fa4b2762618588a3f3112593b130c2c451f7a292c9d898616228fbbe4964ec4c30b1147dfe20a2762618588a3eff0e093b130c336588a3e5849d898616228fc154965844bb0b1147dfe24b2c225d8588a3eef92596112ec2c451f7f892c9d897616228fbfc4965844b30b1147dfe24b2c22558588a3eff125961128c2c451f7f892cb089360002c451f98892c4928b1147e66bfc4962498588a3f311fe24b124c2c451f7f892cbc092616228fcc44965844930b114d5fe24b2c224985a5a3eff125961124c2c451f7f892cb0892616228fcc44964ec4930)))
  else (if i < 9 then (if i < 7 then
  0xb1147df4a4b2c22618588a3ef9125961130c2c451f7c292cb0898616228fbd94965844c30b11525e8a4b2c22618588a82f4525961130c2d9d1f77c92cb0898616b68fbbe4965844c30b1147dda24b2c22618588a3eec125961130c2c451f7f88f8b0898616228fbfc4785844c30b1147dfe2332c2261866cb1147d11961130c2c451f7f8878b0898619b2c451f4145844c30a3eef925a0a2c226185887a292ce0961130c2c451f7f892cae098616228fbfc4965644c30cd96228fa4b2ac2618588a3eff125956130c00066cb1147c9d898519b2c451f7f84ec4c30
  else (if i < 8 then
  0xcc76228fa4b2c22618662b1147d25961130c2d5588a3e92cb0898619b2be51f4965844c30b115f28fa4b2c22618000af947d25961130a2c453fa3e92cb0898619b2c45134965844c3000162289a4b2c22614588a3f44d25961130c2c451f98892cb0898616228fc4d4965844c30b1147e0aa4b2c22618588a6aff125961130c2c452a7f892cb0898616968fbfc4965844c30b4547dfe24b2c22618588a3eff125961130c2c051f7f892cb0898615f28fbfc4965844c30b1145dfe24b2c22618588a26ff125961130c2fb4e67f892cb0898616228fbef4965844c30
  else
  0xb1147dfe24b2622798588a3eff12592213cc2c451f7f892cb089d616228fbef4965844eb0b1147dfe24b2b82758588a3eff125961138c2c451f7d292cb089c616228fbfc4965644e30b1147dfe24b2c226d8588a3eff125961134c2c451f7f892cb08996186ec451f7f892c4c30b1147e5ebfc4962618588a3f2c9fe24b130c2c451f956ff125898616228fcbd7a292c4c30b1147e593be4962618588a3eff125971130c2c451f7f892cb589861a0b36588a3e5844c3000198ac451f2c22614662b1147dfe161130c331588a3ef44b0898616228fbfc4a45844c30))
  else (if i < 11 then (if i < 10 then
  0xb1147e66bd14962798588a3f335df24b13cc2c451f7f892cbc09e616228fcc44965844f30b114d5fe24b2c227985a5a3eff12596113cc2c451f7f892cb089e616028fbfc4965844f30af947dfe24b2c22798588a2eff12596113cc2c45137f892cb089e617da733fc4965844f30b1147df7a4b2c22798588a3efa52596113cc2c451f7b292cb089e61622a4bd14965844f30b6747ddf24b2c22798588a3eebd2596113cc2c451f7f892cae09e616228fbfc4965644f30b1147dfe24b2ac2798588a3eff12595013cc2c451f7f89ac9d89e616228fcc44964ec4f30
  else
  0xb1147dfe24b2762a98588a3eff125961152c2c451f7f892cb08a8616228fbfc49658453b0cd96228fa4b2c22998588a3eff12596114cc2c451f7a292cb08a6616228fbbe4965845330b1147dfe24b2762998588a3eff12596114ac2c451f7f892cb08a4616228fbfc49658451b0b1147dfe24b2c22898588a3eff125961142c2c451f7f892cb08a0616228fbfc4965844fb0cd96228fccd4962798588a3f36e66a4b13cc000588a3f3112589e5186ec451f7f892c4f30b1147e623fc4962798588a3f2f5fe24b13cc2c451f964ff12589e616228fcab7f892c4f30)
  else (if i < 12 then
  0xc9d6228fbfc4962cd8588a3eff13324b166c2c451f82e92cb08b36193ac43fc49658459b0bc747dfe24b2c22cd8588a3eff125961166c2c451f82e92c9d8b36193ac43fc4964ec59b0bc747dfe24b2762cd8588a3eff12593b166c2c453a7f892cb08b2616228fbfc4965845930b11399fe24b2c22c98588a3eff12593b164c2c451f7f892cb08b1616228fbfc4965845830b1147dfe24b2c22bd8588a3eff12596115cc2c451f7f892cb08ad616228fbfc4965845630b1147dfe24b2c22ad8588a3eff125961154c2d9d1f77c92cb08aa616228fbfc4365845530
  else
  0xb1145dfe24b2c22dd8588a26ff12596116ec2c44f87f892cb08b7617da733fc4965845bb0b11351fe24b2c22dd8588a3efbd2596116ec2c451f7d292cb08b761622a4bd14965845bb0b6747ddf24b2c22dd8588a3eff12595c16ec2c451f7f892cac8b7616228fbfc4965585bb0c9d621fe24b2762dd8588a3eff12591e16ec2c451f7f892c838b7616228fbfc4965845b30b1145dfe24b2c22d98588a3eff12595c16cc2c451f7f892cb08b56162289bfc4965845ab0b1147dfe24b2ac2d58588a3eff125961168c00064eb10ff1258b351962c451f7f892c59b0))))
  else (if i < 20 then (if i < 16 then (if i < 14 then
  0xb1147dfe24b2c22f18588a3eff12593b178c2c451f7f892cb08bb616228fbfc4965845d30b1147dfe24b2c22e58588a3eff125961170c341658b10ff1258b760003275887f892c5ba8c9d6228fbfc4962dd861bb1147dfe24b16ec32c5889ccff1258b761962c44db7f892c5bb0b1147e5ebfc4962dd8588a3f2c9fe24b16ec2c451f956ff1258b761962c43fc7a292c5bb0b1147dfe2664962dd8588a3eff125a3e16ec2c451f82e92cb08b76193ac43fc4965845bb0bc747dfe24b2c22dd8588a3eff12596116ec2c051f7f892cb08b7615f28fbfc4965845bb0
  else (if i < 15 then
  0xb11525e8a4b2c231185b3a3eef925961188c2c451f7f886cb08c461a2a8fbfc4145846230b1147dfe24b2b83118588a3eff125959188c2c451f7f892cab0c4616228fbfc4964f86230b1147dfe24b2763118588a3eff125961186c2c451f7f892cb08c2616228fbfc49658460b0b1147dfe24b2c23018588a3eff12596117ec2c451f7f8948b08be616228fbfc4965845f30b1147dfe20a2c22f98588a3eff12593b17cc32c588a3eff1258bd616228fccd7f892c5eb0b1147dfe24b2ec2f58588a3eff12596117ac2c451f7f892c9d8bd616228fbfc4964045eb0
  else
  0xb1147dfe24b2c23358588a3eff12593b19ac2c451f7f892cb08cc616228fbfc49658465b0b1147dfe24b2c23298588a3eff125961192c2c451f7f892cb08c8616228fbfc49658463b0b1147dfe24b2c2319857ca3eff12596118cc2c451f7f892cb08c5616028fbfc49658462b0c376228fbfc4963118588a3f2f5fe24b188c2c451f964ff1258c4616228fcab7f892c6230b1147dfe24b2c23118580a3eff125961188c2be51f7f892cb08c4616228bbfc4965846230b1144dfe24b2c231185f69ccff125961188c2c451f7de92cb08c4616228fbe94965846230))
  else (if i < 18 then (if i < 17 then
  0xb1147dfe24b2c23e98588a3eff1259611f2c2c451f7f892cb08f8616228fbfc4965847bb0b1147dfe24b2c23d98588a3eff1259611eac2c45497a292cb08f5616228fbfc3a25847ab0b1147dfe24b2763d58588a3eff1259611e8c2c451f7f892cb08f3616228fbfc4965846a30b1147dfe24b2c234d86b6b1147dfe24b1a4c32c588a3eff1258d2616228fccd7f892c6930b1147dfe24b2c23498588a92f45259611a4c2c451f7f892c9d8d2616228fbfc4964046930b1147dfe24b2c23458588a3eff1259611a0c2c451f7f892cb08cf616228fbfc4965846730
  else
  0xb1147dfe24b2c24018580a3eff125961200c2c451f7f892cac900616228fbfc4965847fb0af947dfe24b2c23fd8588a3eff1259561fec2c451f7f892cb08fe616228fbfc4965847eb00018928fbfc4963f1462cb1147dfe24b1f8c312588a3eff1258fc616228fbfc4c692c7e30b1147e27a4b2c23f185e5b10ff1259611f8c31251f7f892cb08fc616228fbfc4965847e30b1147e27a4b2763f185e5b10ff12593b1f8c31251f7f892c9d8fc616228fbfc4964ec7e30b3947dfe24b2c23ed8588a3eff1259611f6c28fce67f892cb08fb616228fbfc4964ec7db0)
  else (if i < 19 then
  0xb1147e593fc4964058588a3f2adfe24b202c31651f7f8ef925901616228fbfc4c692c80b0b1147dfe24b4784058588a3f13d25961202c2f2d887f892cb0901618928fbfc49658480b0b1147dfe24b2c24058580a3eff125961202c2be51f7f892cb0901616228bbfc49658480b0b1144dfe24b2c2405851f9dcff125961202c2fb4e67f892cb09016147e69bfc49658480b0b1147df7a4b2c24058588a3efa525961202c2c45497a292cb0901616ce8fbbe49658480b0b1147dfe24b2b84058588a3eff125959202c2c451f7f892cab101618928fbfc4964ec80b0
  else
  0xb1147dfe24b2c24298588a3eff125961212c2c451f7f8954b0908616228fbfc4965848430b1147dfe1c12c24218588a3eff12593b210c316588a3eff125907616228fccd7f892c83b0b1147dfe24b2e041d8588a3eff12596120ec2c451f7f892c9d907616228fbfc4965848330b1147dfe24b2c24158588a3eff12593b20ac2c451f7f892cb0904616228fbfc49658481b0b1147dfe24b2c2409868ac5947dfe24b202c000624a3eff12590151892c451f7f892c80b0c376228fbfc496405862ca3f399fe24b202c31651f9b6ff125901616228fcbd7f892c80b0)))
  else (if i < 23 then (if i < 21 then
  0xb1145dfe24b2c243d861bb1147dfe24b21cc2c451f97aff12590e616228fcb27f892c8730b1147e55bfc4964398588a3eff12596121cc2c051f7f892cb090e615f28fbfc4965848730b1145dfe24b2c24398588a26ff12596121cc2fb4e67f892cb090e616228fbef4965848730b1147df4a4b2c24398588a92f452596121cc2d9d1f77c92cb090e61a0ac43fc3825848730b1147dfe24b2b84398588a3eff12595921cc2c451f7f892cab10e616228fbfc4965048730b1147dfe24b2764398588a3eff12596121ac2c451f7f892cb090c616228fbfc49658485b0
  else (if i < 22 then
  0xb1147dfe24b2c247d86afb1147dfe24b23cc316588a3eff12591e616228fccd7f892c8f30b1147dfe24b2c247985b3a3eef92596123cc2c451f7f892c9d91e616228fbfc4965848eb0b1147dfe24b2c24718588a3eff125961236c2c451f7f892cb091a616228fbfc4964ec8d30b1147dfe24b2c24658588a3eff125961230c2c451f7f892cb0917616228fbfc4965848b30b1147dfe24b2c24558588a3eff125961228c2c451f7f892cb0913616228fbfc4965848930b1147dfe24b2c24458588a3eff125961220c2c45137f892cb0910616228fbfc49658487b0
  else
  0xc596228fbfc4964c58588a3eff125961262c2fb4e67f892cb0931616228fbfc4964ec98b0b1147dfe24b2c24c18588a3eff12596125ec2c451f7f892cb092e616228fbfc49658496b0b1147dfe24b2764b58000b1147dfe24b252a2c451f7f8f4525929616228fbfc4968b894b0b1147dfe24b2c24a58588a3eff12596124cc2c451f7f892cb0924616228fbfc49658491b0cb16228fbfc496489862cb1147dfe24b244c2c451f7f898525922616228fbfc4965849130b1147dfe24b2764898588a3eff125961242c2c451f7f892c9d921616228fbfc4965849030))
  else (if i < 25 then (if i < 24 then
  0xb1147dfe2332c24ed8588a3eff10d961276c34551f7f8828b093b616228fbfc3a25849db0d05621fe1c12c24ed8588a3eff0c1961276c2c451f7f892cae13b616228fbfc4965649db0b1147dfe24b2ac4ed8588a3eff125950276c2c451f7f892ca713b616228fbfc49652c9db0c376228fbfc4964dd8588a3eff12596126ec2fb4e67f892cb0937616228fbfc4964ec9bb0b1147dfe24b2c24d98588a3eff12596126ac000588a3eff125934516228fce67f892c9a30b1147dfe24b2c24d18588a3eff125937268c352d88a3eff12593161962c451f7f892c98b0
  else
  0xb1147e6dbfc3064ed8588a3eff125983276c2c451f7f892cbf13b616228fbfc4965f49db0b1147dfe24b2f04ed8588a3eff125976276c2c451f7f892cb813b616228fbfc4d65849db0b1147e27a4b2c24ed8588a3f05d25961276c2f2d887f892cb093b616229abfc4965849db0bc747dfe24b2c24ed85a5a3eff125961276c2c451f7f892cb093b616028fbfc4965849db0af947dfe24b2c24ed8588a2eff125961276c2c45137f892cb093b617da733fc4965849db0b1147df7a4b2c24ed8588a3efa525961276c2c45497a292cb093b616ce8fbbe4965849db0)
  else (if i < 26 then
  0x1a2a8fbfc4144ed468ab1147dfe20a276c2c451f7f89cd0513b61a2a8fbfc4968289db0c4947dfe24b4144ed851f9ccff125a0a276c28fbfc77c92d0513b616228fbfc4968249db00016228fbfc3a24ed4588a9347dfe1d1276c2c451f7f892ce893b616228fbfc49672c9db0001a0ac43fc3824ed4682b1147dfe1c1276c2c451f7f89cce093b61a0ac43fc4967049db0c9d621fe24b3824ed85889ccff1259c1276c2c43fc7a292ce093b616228fbfc4147049db0b1147dfe24b37c4ed8588a3eff125984276c000588a3eff0c193b516228fce47f860c9db0
  else
  0xb1147dfe3a74964ed8588a3eff13724b276c2c451f7f89b52593b616228fbfc4d692c9db0b1147dfe2664964ed8588a3eff131a4b276c2c451f7f89852593b616228fbfc4b092c9db0b1147dfe2554964ed8588a3eff12924b276c2c451f7f892d2013b616228fbfc4968f89db0b1147dfe24b4784ed8588a3eff125a3a276c2fb588a3eff11993b60002c451f7f88cc9da8b1147dfe24b4664ed8588a3eff125a2e276c2c451f7f892d1193b616228fbfc4968789db0b676228fbfc4364ed8000b1147dfe21b276a2c451f7f892d0d93b616228fbfc49684c9db0)))))
  else (if i < 41 then (if i < 34 then (if i < 30 then (if i < 28 then
  0xd156228fbef4964ed8000b1147df7a4b276a2c451f7f8fbd2593b61a0ac451f7d292c9db00016228fbe94964ed4588a3eff1f4a4b276c2c451f7f8f912593b616228fbfc7c492c9db0b1147dfe3e14964ed8588a3eff1f024b276c2c451f7f8f652593b60002c45497a292c9da8b115268fbd14964ed8588a92ff1e8a4b276c2c451f7f8f152593b60002d9d1f77c92c9da8b676228fbbe4964ed85b3a3eff1df24b276c2c451f7f8ef12593b616228fbfc76e92c9db0b1147dfe3b64964ed8588a3eff1da24b276c2c451f7f8ec12593b616228fbfc75e92c9db0
  else (if i < 29 then
  0xb1147e70bfc4964ed8588a3f36dfe24b276c2c451f9a8ff12593b616228fcd37f892c9db0b1147e66bfc4964ed8588a3f311fe24b276c2c451f97aff12593b616228fcb77f892c9db0b1147e593fc4964ed8588a3f2b1fe24b276c2c451f956ff12593b616228fc507f892c9db0b1147e27bfc4964ed8588a3f135fe24b276c2c451f88eff12593b616228fc447f892c9db0b1147e21bfc4964ed8588a3f061fe24b276c2c451f82eff12593b616228fc157f892c9db0b1147e08bfc4964ed8588a3f039fe24b276c2c451f81aff12593b616228fc027f892c9db0
  else
  0xb114ce8fbfc4964ed8588a6347dfe24b276c2c4530a3eff12593b6162297d1f7f892c9db0b114ba8fbfc4964ed8588a5147dfe24b276c345588a2eff12593b60002c45177f892c9da8b1147e8bbfc4964ed866cb1144dfe24b276c000588a26ff12593b516228fd137f892c9db0b1147e87bfc4964ed8588a3f439fe24b276c2c451fa04ff12593b616228fcfe7f892c9db0b1147e7ebfc4964ed8588a3f3e1fe24b276c2c451f9dcff12593b60002fb4e67f892c9da8bed622733fc4964ed85f6a3f399fe24b276c2c451f9c8ff12593b616228fce27f892c9db0))
  else (if i < 32 then (if i < 31 then
  0xb556228fbfc4964ed85a6b1147dfe24b276c2d2d88a3eff12593b6168ec451f7f892c9db0b396228fbfc4964ed8597b1147dfe24b276c2cb588a3eff12593b61656c451f7f892c9db0b296228fbfc4964ed8590b1147dfe24b276c000588a3eff12593b51a0ac051f7f892c9db0b116028fbfc4964ed8000b0147dfe24b276a33657ca3eff12593b61622be51f7f892c9db00015f28fbfc4964ed4588aef47dfe24b276c2c4575a3eff12593b61622a0d1f7f892c9db0b114fe8fbfc4964ed8588a7747dfe24b276c2c453aa3eff12593b616229ad1f7f892c9db0
  else
  0xd056228fbfc4964ed8676b1147dfe24b276c336588a3eff12593b6198ec451f7f892c9db0cc56228fbfc4964ed8658b1147dfe24b276c327588a3eff12593b618b2c451f7f892c9db0c496228fbfc4964ed861bb1147dfe24b276c30bd88a3eff12593b61846c451f7f892c9db0be36228fbfc4964ed85eeb1147dfe24b276c2f4d88a3eff12593b617a2c451f7f892c9db0bcb6228fbfc4964ed85e4b1147dfe24b276c2f1d88a3eff12593b61702c451f7f892c9db0b7b6228fbfc4964ed85b9b1147dfe24b276c2dbd88a3eff12593b616b6c451f7f892c9db0)
  else (if i < 33 then
  0xb1147e6dbfc4e64ed8000b1147dfe26b276a2d9d88a3f3112593b61622a4d1f98892c9db00016228fc4f4964ed4000b1147e0ba4b276a3275f6b10ff12593b60002f2d887f892c9da8c9d622a4bfc4964ed8000b114d5fe24b276a3125f6a3eff12593b60002f1d1f7f892c9da8c496ce8fbfc4964ed8000b4b47dfe24b276a35fd88a3eff12593b61afac451f7f892c9db0d796228fbfc4964ed86b6b1147dfe24b276c357d88a3eff12593b61a96c451f7f892c9db0d416228fbfc4964ed869db1147dfe24b276c34bd88a3eff12593b61a2ac451f7f892c9db0
  else
  0xb1147e5ebfc4965318588a3eff1e8a4b298c2c451f7f892cb094c616228fbfc496584a5b0b1147dfe24b2c25298000b1147dfe24b292a2c451f964ff125949616228fbfc77c92ca4b0b1147dfe24b2c25258000b1147dfe24b28ca2c451f7f8ef925946616228fbfc496900a330b1147dfe24b2c25198000b1147dfe24b288a2c451f7f896125944616228fbfc49688ca230b1147dfe24b2c25118000b1147dfe24b282a2c451f7f895525941616228fbfc496584a0b00016228fbfc4964f94588a3eff12924b27cc2c451f7f892cb093e619b2c451f7f89cc9db0)))
  else (if i < 37 then (if i < 35 then
  0xb1147dfe26b4965598588a3eff125a232acc2c451f7f892d05156616228fbfc496704ab30b1147dfe24b2c2559857ca3eff1259612acc2c45137f892cb09566198ec451f7f892ca9b00016228fbfc49654d4588a3eff1df24b2a6c2c451f7f892cb09536198ac451f7f892ca9300016228fbfc4965494588a3eff1e8a4b2a4c2c451f7f892cb095261962c451f7f892ca830c596228fbfc496541866cb1147dfe1612a0c2c451f7f892cb0950616228fbfc414584a830b1147dfe1c12c25418588a3eff12596129cc2c451f7f892cb094d60002c451f7f892ca628
  else (if i < 36 then
  0xd156228fbfc4965598682b1147dfe24b2acc336588a3eff12595661962c451f7f892cab30c596228fbfc49655985f6b1147dfe24b2acc2d9d88a3eff12595660002c451f7f892cab28cd95f28fbfc4965598588af947dfe24b2acc00057ca3eff12595651622a4d1f7f892cab30cd962289bfc4965598000b1144dfe24b2aca2c451fa26ff125956616228fce67f892cab30b1147e6f3fc4965598588a3f36dfe24b2acc2c451f99aff125956616228fcc47f892cab30b1147dfe3d14965598588a3eff1df24b2acc2c451f7f8ef125956616228fbfc4e692cab30
  else
  0xb1147e733fc4965658588a3f375fe24b2b2c2c451f9b6ff125959616228fccd7f892cacb0d056228fbe94965658000b1147df4a4b2b2a2c451f7f8fa525959616228fbfc7a292cacb0b1147dfe3be4965658588a3eff1de24b2b2c2c451f7f89cd25959616228fbfc4da92cacb0b1147dfe24b4465658588a3eff125a0a2b2c3415887f892ce0959616228fbfc496704acb0b1147dfe24b2c25658580a3eff1259612b2c2c451f7d292cb0959619dac451f7f892cabb00016228fbfc49655d4588a3f399fe24b2aec2c451f7f892cb095761afec451f7f892cab30))
  else (if i < 39 then (if i < 38 then
  0xb1147dfe26e4965718588a3eff125a232b8c34551f7f892d0515c616228fbfc496828ae30b1147dfe24b3825718588a3eff1259612b8c2c45177f892cb095c616228fbef496584ae30d7d6228fbfc49656586a0b1147dfe24b2b2c345588a3eff12595961a0ac451f7f892cacb0cd96228fbfc4965658658b1147dfe24b2b2c327588a3eff125959618b2c451f7f892cacb0c4d6228fbfc49656585f6b1147dfe24b2b2c2d9d88a3eff12595960002c451f7f892caca8d056028fbfc4965658588b0147dfe24b2b2c000580a3eff12595951622a4d1f7f892cacb0
  else
  0xd056228fbfc496571866cb1147dfe24b2b8c32c588a3eff12595c6194ac451f7f892cae30c596228fbfc4965718624b1147dfe24b2b8c2fb588a3eff12595c616cec451f7f892cae300016228fbfc4965714588a9347dfe24b2b8c345588a2eff12595c60002c45177f892cae28b1147e8bbfc4965718588a3f399fe24b2b8c2c451f9b8ff12595c616228fcdb7f892cae30b1147e66bfc496571868ab1147df7a4b2b8c000588a3efbd2595c516228fbfc7de92cae30b1147dfe3d14965718588a3eff1df24b2b8c2c451f7f8ef12595c616228fbfc4e692cae30)
  else (if i < 40 then
  0xb1147dfe24b2dc5858588a3eff12596d2c2c2c451f7f892cb5961616228fbfc4965a8b0b0b1147dfe24b2d25858588a3eff1259682c2c2c451f7f892cb2961616228fbfc49658cb0b0b1147dfe24b2c458586a0b1147dfe24b2c0c345588a3eff12596061a0ac451f7f892cb030bed6228fbfc4965818000b1147dfe24b2c0a2c451f7f892cb096061a5ec451f7f892cafb0bed6228fbfc49657d85b3b1147dfe24b2bec000588a3eff12595f51622a4d1f7f892cafb0b1147dfe24b2c257d86bcb1147dfe24b2b8c350588a3eff12595c61a2ac451f7f892cae30
  else
  0xbdd621fe24b30858585f1a3eff1259842c2c2c451f7f892cc2161617da733fc496610b0b0c236228fbfc3065858588a3eff1259832c2c2c451f7f892cc1161616228fbfc496604b0b0b1147dfe24b3005858588a3eff12597f2c2c2c451f7f892cbf161616228fbfc4965f4b0b0b1147dfe24b2f85858588a3eff12597b2c2c2c451f7f892cbd161616228fbfc4965e4b0b0b1147dfe24b2f05858588a3eff1259762c2c2c451f7f892cba961616228fbfc4965d0b0b0b1147dfe24b2e65858588a3eff1259712c2c2c451f7f892cb8161616228fbfc4965bcb0b0))))
  else (if i < 48 then (if i < 44 then (if i < 42 then
  0xb10ff1f4a4b3825858588a92f45259c12c2c2c453f7a292ce0961616ce8fbbe496704b0b0b10ff1db24b38258585887f8ec1259c12c2c2c451f7f88f0e0961616228fbfc436704b0b0d05621fe20a382585868aa3eff1051c12c2c2733fc496828e0961616228fbfc496700b0b0bd1621fe24b37c5858588a3eff1259be2c2c2c43fc7a292cdf161616228fbfc4966f4b0b0b1147dfe24b3785858588a3eff1259ba2c2c2c451f7f892cd7161616228fbfc49668cb0b0b1147dfe24b30e5858588a3eff1259862c2c2c451f7f892cc2961616228fd00496610b0b0
  else (if i < 43 then
  0xc9d621fe24b38258585eeb10ff1259c12c2c2f45887f892ce096161a0ac03fc496704b0b0b11601fe24b3825858000b00ff1259c12c2a2c45417f892ce0961616229d3fc496704b0b0bc747dfe24b38258585a2a3eff1259c12c2c2c451f7f892ce0961616028fbfc496704b0b0af947dfe24b3825858588a2eff1259c12c2c2c45137f892ce09616162287bfc496704b0b0b113e1fe24b38258585f69ccff1259c12c2c2f8ce67f892ce096161622073fc496704b0b0b1147df7a4b3825858682b10fa5259c12c2c0005887d292ce0961516228fbe9496704b0b0
  else
  0xb1147dfe24b39c5858588a3eff1259cd2c2c2c451f7f892ce616161a0ac43fc49672cb0b0b1147dfe24b39658585889ccff1259cb2c2c2c43fc7a292ce5961616228fbfc496728b0b0b1147dfe24b3925858588a3eff1259c82c2c2c451f7f892ce3961616228fbfc496718b0b0b1147dfe24b38a5858588a3eff1259c42c2c2c451f7f892ce1961616228fbfc496708b0b0d059b2c43fc3825858000cc5621fe1c12c2a331588a3eff0e09616198ac43fc7a2704b0b0b1147e8024b3825858588a3f05d259c12c2c33b5887f892ce09616198ac43fc496704b0b0))
  else (if i < 46 then (if i < 45 then
  0xa3eff1f7a4b4145858588a3efa525a0a2c2c2c45497a292d05161616ce8fbbe496828b0b0b5547ddf24b414585851f7f8edd25a0a2c2c28fbfc76092d05161616228fbfc47c828b0b0b7b47dfe24b4125858588a3eff125a092c2c28fbfc77c92d04961616228fbfc496820b0b0b1147dfe24b40e5858588a3eff125a062c2c2c451f7f892ce9961616228fbfc496748b0b0b1147dfe24b3a25858000b10f45259d12c2a2c45497a292ce8961616228fbd1496744b0b0b10ff1e8a4b3a25858588a3eff1051d12c2c2c451f7f892ce8161616228fbfc49673cb0b0
  else
  0xb114a9fe24b4145858676a3eff125a0a2c2c331d1f7f892d05161618928fbfc496828b0b0be347dfe24b41458585bda3eff125a0a2c2c2d6d1f7f892d05161616728fbfc496828b0b0b1147dfe24b4145858580a3eff125a0a2c2c2be51f7f892d05161615de8fbfc496828b0b0d1545dfe24b4145858588a2eff125a0a2c2c28fd177f892d05161600028bbfc496828b0a8b1144dfe24b414585851f9dcff125a0a2c2c2fb4e67f892d05161617ba733fc496828b0b0a3f111fe24b414585868aa3efbd25a0a2c2c2c451f7de92d05161600028fbef496828b0a8)
  else (if i < 47 then
  0xb1147dfe24b4305858588a3eff125a172c2c2c451f7f892d0b161616228fbfc496854b0b0b1147dfe24b428585868aa3eff125a132c2c2c451f7f892d099616147e733fc49684cb0b0a3eff1df24b4265858588a3eff125a122c2c2c451f7f892d08961616228fbfc496840b0b0b1147dfe24b41e5858588a3eff125a0e2c2c2c451f7f892d06961616228fbfc496830b0b0b1147dfe24b416585868acd947dfe20a2c2c000663a3eff1051615198ec451f7f8828b0b0cc747dfe3be4145858588a3f40125a0a2c2c2c451f89e92d0516161796c43fc496828b0b0
  else
  0xb0147dfe24b446585857ca3eff125a232c2c2c45177f892d119616162289bfc49688cb0b0bed399fe24b4465858588a3efbd25a232c2c2c451f7d292d1196161622a4bd149688cb0b0b6747ddf24b4465858588a3eff125a222c2c2c451f7f892d10961616228fbfc496880b0b0b1147dfe24b43e5858588a3eff12c21e2c2c2c451f7f892d0f161616228fbfc496874b0b0b1147dfe24b438585866cb1147dfe21b2c2c2c451f7f892d0d961616ce8fbbe49686cb0b0b1147ddf24b4365858000a3eef925a1b2c2a28fbfc77c92d0d961616228fbfc496864b0b0)))
  else (if i < 51 then (if i < 49 then
  0xb1147dfe24b46658585f69ccff125a332c2c2c44e67f892d199616147e733fc4968ccb0b0001399fe24b4665854588a3eff125a322c2c2c451f7f892d18961616228fbfc4968c0b0b0b1147dfe24b45e5858588a3eff125a2e2c2c2c45497a292d17161616228fbfc4968b4b0b0b1147dfe24b4585858588a3eff125a2b2c2c2c451f7f892d15161616228fbfc4968a4b0b0b1147dfe24b4505858588a3eff125a272c2c2c451f7f892d13161616228fbfc496894b0b0b1147df4a4b44a5858588a3eff125a242c2c2c451f7de92d12161616228fbfc49688cb0b0
  else (if i < 50 then
  0x16228fbfc4885854588a9347dfe2442c2c2c451f7f892d22161616228fbfc496900b0b0b6747ddf24b4805858588a3eff125a3f2c2c35f588a3eff11f16161a0ac451f7f88f8b0b0b1147dfe27347c5858588a3eff125a3e2c2c35e588a3eff11e16161a2ac451f7f88f0b0b0b1147dfe2734785858588a3eff125a3c2c2c2c451f7f892d1d161616228fbfc4968e4b0b0b1147dfe24b4705858588a3eff125a372c2c2c451f7f892d1b161616228fbfc4968d4b0b0b1147dfe24b46858586a0b1147dfe2332c2c345588a3eff11996161a0ac451f7f88ccb0b0
  else
  0xb1147dfe24e4965858588a3eff126a4b2c2c2c451f7f89312596161adac451f7f8928b0b0cb16228fbfc4945858000b1147dfe24a2c2a2c4549a3eff125161616228fccd7f8928b0b0b1147dfe24b49458586afb1147dfe2492c2c316588a3eff124961616cec451f7f8924b0b00016228fbfc4925854588a3f335fe2492c2c2c451f7f892d2496161a96c451f7f891cb0b0cb16228fbfc48e585862cb1147dfe2472c2c2fb588a3eff12396160002c451f7f891cb0a8b1147dfe24b48e5858697b1147dfe2442c2c2fb588a3eff122161616cec451f7f8910b0b0))
  else (if i < 53 then (if i < 52 then
  0xb1147dfe26a4965858588a3eff134a4b2c2c2c451f7f899d25961616228fbfc4cc92cb0b0b1147dfe2644965858588a3eff131a4b2c2c2c451f7f898525961616228fbfc4c092cb0b0b1147dfe25f4965858588a3eff12f24b2c2c2c451f7f897125961616228fbfc4b692cb0b0b1147dfe25a4965858588a3eff12ca4b2c2c2c451f7f896125961616228fbfc4ae92cb0b0b1147dfe2564965858588a3eff12aa4b2c2c2c451f7f895125961616228fbfc4a692cb0b0b1147dfe2524965858588a3eff128a4b2c2c2c451f7f894125961616228fbfc49e92cb0b0
  else
  0xb1147dfe2734965858587a3eff139a4b2c2c2c351f7f89cd25961616028fbfc4e692cb0b0af947dfe2734965858588a3cff139a4b2c2c2c451d7f89cd25961616228bbfc4e692cb0b0b1144dfe27349658585f69ccff139a4b2c2c2c451f7f69cd25961616228fbfa4e692cb0b0b1147df7a734965858588a3efa539a4b2c2c2c45497a29cd25961616ce8fbbe4e692cb0b0b1147dfe2724965858588a3eff138a4b2c2c2c451f7f89c125961616228fbfc4de92cb0b0b1147dfe26e4965858588a3eff136a4b2c2c2c451f7f89b125961616228fbfc4d692cb0b0)
  else (if i < 54 then
  0xb1147dfe3b14965858588a3f409d824b2c2c2c452f7f8ec1259616168e8fbfc76092cb0b0b1147dfe3b049658585f69ccff1d824b2c2c2c45497a2ec125961616ce8fbbe76092cb0b0b1147e7ebaf4965858588a3eff1d7a4b2c2c2c451f7f8eb925961616228fbfc75a92cb0b0b1147dfe3ac4965858588a3eff1d5a4b2c2c2c451f7f8ea925961616228fbfc75292cb0b0b1147dfe3a84965858588a3eff1d3a4b2c2c2c451f7f8e9925961616228fbfc74a92cb0b0b1147dfe3a44965858588a3eff13b24b2c2c2c451f7f89d525961616228fbfc4e892cb0b0
  else
  0xb1147df4bbd4965858588a3eff1de24b2c2c2c051f7f8ef125961615f28fbfc77892cb0b0b1145dfe3bc4965858588a26ff1de24b2c2c2fb4e67f8ef125961616228fbef77892cb0b0b1147df4bbc4965858588a92f45de24b2c2c2d9d1f77cef125961616228fbfc77692cb0b0b1147dfe3ba4965858588a3eff1dca4b2c2c2c451f7f8ee125961616428fbfc76e92cb0b0b1147dfe3b74965858588a50ff1db24b2c2c2c451f7f8ed925961616228fbfc76a92cb0b0b1147e013b44965858588a3eff1da24b2c2c2c451f7f8ecd25961616228fbfc76492cb0b0))))))
  else (if i < 82 then (if i < 68 then (if i < 61 then (if i < 58 then (if i < 56 then
  0xb1147e0c3be4965858588a3f009df24b2c2c2c452a7f8ef925961617928fbfc77c92cb0b0b5b47dfe3be49658585aaa3eff1df24b2c2c2d351f7f8ef9259616168e8fbfc77c92cb0b0b2147dfe3be4965858588a3eff1df24b2c2c2c051f7f8ef925961615f28fbfc77c92cb0b0aef47dfe3be4965858588a2eff1df24b2c2c2c45137f8ef92596161622883fc77c92cb0b0bed399fe3be4965858588a3efbddf24b2c2c2c451f7d2ef925961616228fbe477c92cb0b0b11525e8bbe49658585b3a3ef45df24b2c2c2c451f7f8ef525961616028fbfc77a92cb0b0
  else (if i < 57 then
  0xb1147dfe3c04965858588a3eff1dfa4b2c2c357db3a3eef92596161a5ed9d1f77c92cb0b0d156ce8fbbe4965858682b6747ddf24b2c2c3365b3a3eef9259616198ed9d1f77c92cb0b0cb16ce8fbbe496585862cb6747ddf24b2c2c2fb5b3a3eef92596160002d6d1f77c92cb0a80016aa8fbbe49658545adb1147ddf24b2c2c2d5588a3eef925961616cea4d1f77c92cb0b0b674be8fbbe4965858588a3f409df24b2c2c2d9d1f9f0ef925961616ce8fce677c92cb0b0b6747e6dbbe49658585b3a3f335df24b2c2c2d9d1f964ef925961616228fc5077c92cb0b0
  else
  0xaf347dfe3d14965858588a2eff1e8a4b2c2c2c45137f8f45259616162287bfc7a292cb0b0bed399fe3d14965858588a3efbde8a4b2c2c2c451f7d2f4525961616228fbe17a292cb0b0b1147dfe3d04965858588a2eff1e824b2c2c2c451f7def4125961616228fbfc79e92cb0b0b1147dfe3ce4965858588a3eff1e5a4b2c2c2c451f7f8f2925961616228fbfc79292cb0b0b1147dfe3c84965858588a3eff1e3a4b2c2c2c451f7f8f1925961616228fbfc78a92cb0b0b1147dfe3c44965858588a3eff1e1a4b2c2c2c451f7f8f0925961616228fbfc78292cb0b0))
  else (if i < 59 then
  0xb47622a4bd14965858000b11505e8a4b2c2a000588a7ef452596151622a0d1f7a292cb0b0b114fe8fbd14965858588a3f409e8a4b2c2c2c45499dcf452596161622a4ce67a292cb0b0b115266dbd14965858588a93335e8a4b2c2c2c454997af4525961616228fc507a292cb0b0b1147e0c3d14965858588a3f009e8a4b2c2c2f4d887f8f452596161622a0bfc7a292cb0b0b114fdfe3d14965858588a76ff1e8a4b2c2c2c452f7f8f452596161622943fc7a292cb0b0b4547dfe3d14965858588a3eff1e8a4b2c2c2c051f7f8f4525961615f28fbfc7a292cb0b0
  else (if i < 60 then
  0xb1147dfe3db4965858588a3eff1ed24b2c2c34bd88a3ef6525961616cec451f7b292cb0b0b115268fbd94965858588a3eff1eca4b2c2c2fb4e67f8f6525961616228fbfc7b092cb0b0b1147dfe3d74965858588a3eff1eb24b2c2c2c451f7f8f5525961616228fbfc7a892cb0b0b1147dfe3d34965858588a3eff1e924b2c2c35b588a92f452596161a5ec45497a292cb0b0d15622a4bd14965858682b11525e8a4b2c2c336588a92f45259616198ac45497a292cb0b0cb1622a4bd1496585862cb11525e8a4b2c2c2fb588a92f4525961616cec45497a292cb0b0
  else
  0xb1147e66be94965858588a3f331f4a4b2c2c2c451f7f8fa525961616028fbfc7d292cb0b0ced6228fbe64965858000b1147df324b2c2a2c451f9ccf9925961616228fbfc7cc92cb0b0b1147dfe3e549658586b6b1147df224b2c2c2c4549a3ef9125961616228fccd7c892cb0b0b1147dfe3e44965858588a3eff1f1a4b2c2c2c451f7f8f892596161abec451f7c292cb0b0b676228fbe14965858588a3f335f0a4b2c2c2c451f7f8f8525961616228fbfc7c092cb0b0b1147dfe3df4965858588a3eff1ef24b2c2c2c451f7f8f7525961616228fbfc7b892cb0b0)))
  else (if i < 64 then (if i < 62 then
  0xb1147e6dbef4965858588a3f335f7a4b2c2c2c451f996fbd25961616228fbfc7de92cb0b0b1145dfe3ef49658586beb1147df4a4b2c2c350588a3efa52596161a2ac451f7d292cb0b0d056228fbe9496585866cb1147df4a4b2c2c331588a3efa52596161962c451f7d292cb0b0c596228fbe949658585f6b1147df4a4b2c2c2d9d88a3efa525961616bac451f7d292cb0b00016228fbe94965854682b0147df4a4b2c2c2c4580a3efa52596160002c051f7d292cb0a8b115268fbe94965858588a8347df4a4b2c2c2c451f9ccfa525961616228fcdb7d292cb0b0
  else (if i < 63 then
  0xd416228fbf5496585868ab1147dfaa4b2c2c341588a3efd525961617dac451f7ea92cb0b00016228fbf54965854588a3eff1faa4b2c2c35e588a3efbd2596161a82c451f7de92cb0b0d156228fbef4965858682b1147df7a4b2c2c336588a3efbd259616198ec451f7de92cb0b0cb16228fbef496585862cb1147df7a4b2c2c2fb588a3efbd25961616cec451f7de92cb0b0b5b6228fbef4965858000b1147df7a4b2c2a2c4549a3efbd2596161622a251f7de92cb0b0d156228bbef4965858000b1145df7a4b2c2a2c451fa2efbd25961616228fce67de92cb0b0
  else
  0xb1147e02bfc4965858588a3f011fe24b2c2c2c451f804ff125961616228fc017f892cb0b0b1147e003fc4965858588a3effdfe24b2c2c2c451f7fcff125961616228fbfd7f892cb0b0d7d6228fbfb4965858682b1147dfda4b2c2c32c588a3efed2596160002c451f7f692cb0a8b1147dfe3fb49658586bcb1147dfd24b2c2c345588a3efe925961618b2c451f7f492cb0b00016228fbfa4965854588a3eff1fd24b2c2c352d88a3efe12596161962c451f7f092cb0b0c596228fbf849658585f6b1147dfc24b2c2c000588a3efe125961516228fbfc7f092cb0b0))
  else (if i < 66 then (if i < 65 then
  0xb1147e1fbfc4965858588a3f0f9fe24b2c2c2c451f87aff125961616228fc187f892cb0b0b1147e0bbfc4965858588a3f059fe24b2c2c2c451f82aff125961616228fc147f892cb0b0b1147e09bfc4965858588a3f045fe24b2c2c2c451f820ff125961616228fc0f7f892cb0b0d6d622073fc4965858658b11039fe24b2c2c2c454981cff125961616228fc0e7f892cb0b0b1139a073fc4965858588a3f035fe24b2c2c2c451f818ff125961616228fc0b7f892cb0b0b1147e053fc4965858588a3f025fe24b2c2c2c451f810ff125961616228fc077f892cb0b0
  else
  0xb1147e53bfc4965858588a3f291fe24b2c2c2c451f93cff125961616228fc9d7f892cb0b0b1147e3ebfc4965858588a3f141fe24b2c2c2c451f89eff125961616228fc4e7f892cb0b0b1147e26bfc4965858588a3f131fe24b2c2c2c451f896ff125961616228fc497f892cb0b0b1147e23bfc4965858588a3f119fe24b2c2c2c451f88aff12596161abe8fc447f892cb0b0c5947e223fc49658585b3a3f111fe24b2c2c2c451f888ff1259616147e734447f892cb0b0b1147e21bfc4965858588a3f109fe24b2c2c2c451f882ff125961616228fc407f892cb0b0)
  else (if i < 67 then
  0xb0947e66bfc4965858580a3f335fe24b2c2c2be51f99aff125961616228f4cd7f892cb0b0b1146e66bfc4965858588a2f335fe24b2c2c2c451399aff125961617da734cd7f892cb0b0b1147e663fc4965858588a3f32dfe24b2c2c2c451f994ff125961616228fcc77f892cb0b0b1147e633fc4965858588a3f315fe24b2c2c2c451f988ff125961616228fcc17f892cb0b0b1147e5ebfc4965858588a3f2ddfe24b2c2c2c451f96cff125961616228fcb27f892cb0b0b1147e563fc4965858588a3f2adfe24b2c2c2c451f954ff125961616228fca97f892cb0b0
  else
  0xb1147e6e3fc4965858588a3f36dfe24b2c2c2c051f9b6ff125961615f28fcdb7f892cb0b0b1145e6dbfc4965858588a2736dfe24b2c2c2fb4e69b6ff125961616228fcda7f892cb0b0b1147e6cbfc4965858588a3f361fe24b2c2c2c451f9aeff125961616228fcd67f892cb0b0b1147e6abfc4965858588a5d351fe24b2c2c2c451f9a8ff125961616528fcd37f892cb0b0b1147e69bfc4965858588a3f349fe24b2c2c2c451f9a2ff125961616228fcd07f892cb0b0b1147e67bfc4965858588a3f339fe24b2c2c2c451f99aff1259616161e8fccd7f892cb0b0))))
  else (if i < 75 then (if i < 71 then (if i < 69 then
  0xb114a2733fc49658585f1a3f399fe24b2c2c2f751f9ccff125961617928fce67f892cb0b0b4d47e733fc49658585a3a3f399fe24b2c2c2c851f9ccff125961616228fce67f892cb0b0b0147e733fc496585857ca3f399fe24b2c2c2c45179ccff1259616162289ce67f892cb0b0bed40a733fc4965858588a3f395fe24b2c2c2be51f9caff1259616162289ce57f892cb0b0b1147e723fc4965858588a3f38dfe24b2c2c2c451f9c4ff125961616228fce17f892cb0b0b1147e703fc4965858588a3f37dfe24b2c2c2c451f9bcff125961616228fcdd7f892cb0b0
  else (if i < 70 then
  0xb1147e75bfc4965858588a3f3a9fe24b2c2c2c451f9d2ff125961616228fce87f892cb0b0b1147e73bfc49658586a5bed399fe24b2c2c3505f69ccff12596161a5efb4e67f892cb0b0d157da733fc4965858682bed399fe24b2c2c33b5f69ccff125961619b2fb4e67f892cb0b0cb17da733fc496585862cbed399fe24b2c2c30ddf69ccff12596160002f8ce67f892cb0a80017ba733fc49658545f6b67399fe24b2c2c2f8d889ccff125961617bac44e67f892cb0b0bd3622733fc49658585f6a93399fe24b2c2c2c453b9ccff1259616162297ce67f892cb0b0
  else
  0xb1147e7f3fc4965858588a3f3f5fe24b2c2c2c451f9f8ff125961616228fcfb7f892cb0b0b1147e7d3fc4965858588a3f3e5fe24b2c2c34bd889f0ff125961617dac44f87f892cb0b0b115267c3fc4965858588a3f3e1fe24b2c2c2c451f9eeff125961616228fcf67f892cb0b0b1147e7abfc4965858588a3f3d1fe24b2c2c2c451f9e6ff125961616228fcf17f892cb0b0b1147e783fc4965858588a3f3bdfe24b2c2c34bd1f9dcff125961617da8fcee7f892cb0b0b6747e773fc4965858588a3f3b9fe24b2c2c2c451f9daff125961616228fcec7f892cb0b0))
  else (if i < 73 then (if i < 72 then
  0x15f289bfc4965854588a9344dfe24b2c2c2c453fa26ff125961616228fd137f892cb0b0af947e89bfc4965858663b11441fe24b2c2c000588a20ff125961516228fd107f892cb0b0d4b62287bfc4965858658b1143dfe24b2c2c2fb588a1eff125961616228fd0f7f892cb0b0b1147e873fc4965858588a3f435fe24b2c2c2c451fa18ff125961616228fd097f892cb0b0b1147e833fc4965858588a3f415fe24b2c2c2c451fa08ff125961616228fd037f892cb0b0b1147e813fc4965858588a3f405fe24b2c2c2c451fa00ff125961616228fcff7f892cb0b0
  else
  0xced6228bbfc496585866cb1145dfe24b2c2c32c588a2eff1259616195ac45177f892cb0b0c596228bbfc49658585f6b1145dfe24b2c2c2f8d88a2eff125961616cec45177f892cb0b00016228bbfc4965854588a9345dfe24b2c2c2c451fa2eff12596161afec45137f892cb0b0d1562289bfc4965858682b1144dfe24b2c2c336588a26ff1259616198ac45137f892cb0b0cb162289bfc4965858657b1144dfe24b2c2c316588a26ff125961617dac45137f892cb0b0b6762289bfc4965858000b1144dfe24b2c2a33657ca26ff12596161622be5137f892cb0b0)
  else (if i < 74 then
  0xb114968fbfc4965858588a4947dfe24b2c2c2c4523a3eff125961616229151f7f892cb0b0b114868fbfc4965858588a4147dfe24b2c2c35fd88a3cff125961619b2c451e7f892cb0b00016228f3fc4965854588a3f479fe24b2c2c35e588a3aff12596161a2ac451d7f892cb0b0c596228ebfc4965858000b11475fe24b2c2a2c451fa3aff12596161abec451b7f892cb0b0c596228dbfc49658585b3b1146dfe24b2c2c000588a36ff125961516228fd1b7f892cb0b0d796228bbfc49658586a0b1145dfe24b2c2c345588a2eff12596161a0ac45177f892cb0b0
  else
  0xb115068fbfc4965858588a7f47dfe24b2c2c2c453ca3eff125961616229dd1f7f892cb0b0b114ea8fbfc4965858588a7347dfe24b2c2c2c4538a3eff125961616229bd1f7f892cb0b0b114d68fbfc4965858588a6947dfe24b2c2c2c4533a3eff125961616229951f7f892cb0b0b114c68fbfc4965858588a6147dfe24b2c2c2c452fa3eff125961616229751f7f892cb0b0b114b68fbfc4965858588a5947dfe24b2c2c2c452ba3eff125961616229551f7f892cb0b0b114a68fbfc4965858588a5147dfe24b2c2c2c4527a3eff125961616229351f7f892cb0b0)))
  else (if i < 78 then (if i < 76 then
  0xd4b5de8fbfc496585862caef47dfe24b2c2c2fb577a3eff12596161622bbd1f7f892cb0b0b115da8fbfc4965858588aeb47dfe24b2c2c2c4574a3eff12596161622b9d1f7f892cb0b0b115ca8fbfc4965858588adf47dfe24b2c2c2c456ea3eff12596161622a5d1f7f892cb0b0b1152a8fbfc4965858588a9347dfe24b2c2c2c2549a3eff12596161602a4d1f7f892cb0b0af95268fbfc4965858588a9147dfe24b2c2c2c4547a3eff12596161622a351f7f892cb0b0b115168fbfc4965858588a8947dfe24b2c2c2c4543a3eff12596161622a151f7f892cb0b0
  else (if i < 77 then
  0xc596028fbfc496585862ab0147dfe24b2c2c2fb580a3eff125961617bac051f7f892cb0b0b676028fbfc4965858588b0147dfe24b2c2c000580a3eff12596151afebe51f7f892cb0b0d155f28fbfc4965858682af947dfe24b2c2c33657ca3eff1259616198ebe51f7f892cb0b0cb15f28fbfc496585862caf947dfe24b2c2c315d7ca3eff125961617dabe51f7f892cb0b0b675f28fbfc49658585aaaf947dfe24b2c2c2c457ca3eff12596160002be51f7f892cb0a8cc55e68fbfc4965858588af347dfe24b2c2c000579a3eff12596151622bc51f7f892cb0b0
  else
  0xb196228fbfc496585858bb1147dfe24b2c2c2c5588a3eff12596161626c451f7f892cb0b0d7f61e8fbfc496585866cb0f47dfe24b2c2c2c4587a3eff12596160002c3d1f7f892cb0a8d7d61a8fbfc4965858682b0d47dfe24b2c2c32c586a3eff12596161622c351f7f892cb0b000161a8fbfc49658546b6b0947dfe24b2c2c32c584a3eff12596161622c251f7f892cb0b00016128fbfc49658546beb0147dfe24b2c2c350580a3eff12596161a2ac051f7f892cb0b0d056028fbfc4965858676b0147dfe24b2c2c336580a3eff12596161962c051f7f892cb0b0))
  else (if i < 80 then (if i < 79 then
  0xb4d6228fbfc49658585a5b1147dfe24b2c2c2d2588a3eff1259616168ec451f7f892cb0b0b456228fbfc49658585a1b1147dfe24b2c2c2d0588a3eff1259616167ac451f7f892cb0b0b3b6228fbfc496585859cb1147dfe24b2c2c2cdd88a3eff1259616166ac451f7f892cb0b0b336228fbfc4965858597b1147dfe24b2c2c2cb588a3eff12596161656c451f7f892cb0b0b296228fbfc4965858593b1147dfe24b2c2c2c9588a3eff12596161646c451f7f892cb0b0b216228fbfc496585858fb1147dfe24b2c2c2c7588a3eff12596161636c451f7f892cb0b0
  else
  0xbc36228fbfc49658585e0b1147dfe24b2c2c2e0588a3eff125961616fec451f7f892cb0b0b7d6228fbfc49658585bdb1147dfe24b2c2c2de588a3eff125961616eec451f7f892cb0b0b736228fbfc49658585b8b1147dfe24b2c2c2dbd88a3eff125961616dac451f7f892cb0b0b6b6228fbfc49658585b4b1147dfe24b2c2c2d9d88a3eff125961616cac451f7f892cb0b0b636228fbfc49658585b0b1147dfe24b2c2c2d7d88a3eff125961616bac451f7f892cb0b0b5b6228fbfc49658585abb1147dfe24b2c2c2d5588a3eff1259616169ec451f7f892cb0b0)
  else (if i < 81 then
  0xc1f6228fbfc496585860eb1147dfe24b2c2c306588a3eff125961617e6c451f7f892cb0b0bf16228fbfc49658585f7b1147dfe24b2c2c2fb588a3eff125961617d6c451f7f892cb0b0be96228fbfc49658585f3b1147dfe24b2c2c2f9588a3eff125961617c6c451f7f892cb0b0bdf6228fbfc49658585eeb1147dfe24b2c2c2f5d88a3eff125961617aac451f7f892cb0b0bd36228fbfc49658585e8b1147dfe24b2c2c2f3d88a3eff1259616179ac451f7f892cb0b0bcb6228fbfc49658585e4b1147dfe24b2c2c2f1d88a3eff1259616178ac451f7f892cb0b0
  else
  0xc9f6228fbfc496585864eb1147dfe24b2c2c325d88a3eff125961618bec451f7f892cb0b0c5d6228fbfc496585862db1147dfe24b2c2c316588a3eff125961618aec451f7f892cb0b0c556228fbfc4965858629b1147dfe24b2c2c313588a3eff12596161896c451f7f892cb0b0c496228fbfc4965858621b1147dfe24b2c2c310588a3eff1259616187ec451f7f892cb0b0c376228fbfc4965858617b1147dfe24b2c2c30ad88a3eff12596161852c451f7f892cb0b0c276228fbfc4965858612b1147dfe24b2c2c308d88a3eff12596161842c451f7f892cb0b0)))))
  else (if i < 96 then (if i < 89 then (if i < 85 then (if i < 83 then
  0xcfb6228fbfc4965858676b1147dfe24b2c2c336d88a3eff125961619b2c451f7f892cb0b0cd76228fbfc496585866ab1147dfe24b2c2c334d88a3eff125961619a2c451f7f892cb0b0ccf6228fbfc4965858666b1147dfe24b2c2c331d88a3eff1259616198ac451f7f892cb0b0cbf6228fbfc496585865cb1147dfe24b2c2c32dd88a3eff1259616196ac451f7f892cb0b0cb36228fbfc4965858658b1147dfe24b2c2c32bd88a3eff1259616195ac451f7f892cb0b0cab6228fbfc4965858652b1147dfe24b2c2c328d88a3eff12596161942c451f7f892cb0b0
  else (if i < 84 then
  0xd416228fbfc496585869fb1147dfe24b2c2c34f588a3eff12596161a76c451f7f892cb0b0d2f6228fbfc4965858696b1147dfe24b2c2c34ad88a3eff12596161a52c451f7f892cb0b0d276228fbfc496585868cb1147dfe24b2c2c345d88a3eff12596161a2ac451f7f892cb0b0d136228fbfc4965858688b1147dfe24b2c2c343d88a3eff12596161a1ac451f7f892cb0b0d0b6228fbfc4965858684b1147dfe24b2c2c341d88a3eff12596161a0ac451f7f892cb0b0d036228fbfc4965858680b1147dfe24b2c2c33fd88a3eff125961619fac451f7f892cb0b0
  else
  0x168a8fbfc49658545f6b3947dfe24b2c2c316594a3eff12596161a2ac851f7f892cb0b0d056328fbfc4965858000b1947dfe24b2c2a35fd88a3eff12596161afac451f7f892cb0b0d7b6228fbfc49658586bcb1147dfe24b2c2c35dd88a3eff12596161aeac451f7f892cb0b0d6d6228fbfc49658586b5b1147dfe24b2c2c35a588a3eff12596161abec451f7f892cb0b0d5d6228fbfc49658586adb1147dfe24b2c2c356588a3eff12596161a96c451f7f892cb0b0d496228fbfc49658586a3b1147dfe24b2c2c351588a3eff12596161a86c451f7f892cb0b0))
  else (if i < 87 then (if i < 86 then
  0xbd1622a4bfc4965858658b11505fe24b2c2c2fb588a82ff12596161a0ac453b7f892cb0b0bed6229d3fc4965858000b114d5fe24b2c2a341588a5eff12596161962c452e7f892cb0b0001622953fc4965854682b114a1fe24b2c2c345588a46ff12596160002c45237f892cb0a8c497da8fbfc496585862cbe347dfe24b2c2c3455e4a3eff12596160002f1d1f7f892cb0a8c496ce8fbfc49658585f1b6747dfe24b2c2c2dedb3a3eff125961618b2d6d1f7f892cb0b0bed6b68fbfc496585868ab4d47dfe24b2c2c0005a5a3eff12596151a2ad1d1f7f892cb0b0
  else
  0xd156228fbfc4a458585aab115268fa4b2c2c2d9d88a7f47d25961619b2c451fa0492cb0b00016228fd004965854588a3f4027324b2c2c2d5588a3f33525961616229fd1f99a92cb0b0b1147e7eccd49658585b3b1147e6224b2c2c2c4549a3f31125961619b2c451f8a092cb0b00016228fc4f4965854588a9347e26a4b2c2c336588a3f0612596160002c451f82e92cb0a8b676228fc15496585866cb1147e0124b2c2c3275f6b10ff12596161962f75887f892cb0b0d057a6c43fc4965858000bcb621fe24b2c2a327588a92ff125961617bac45497f892cb0b0)
  else (if i < 88 then
  0x16228fbfc4965c54588a3eff1e8a4b2e2c2c451f7f892ce097161962c451f7f892cb8300016228fbfc4965ad4588a3eff1df24b2d6c2c451f7f892d0516b61a2ac451f7f892cb2b00016228fbfc4965954682b1147dfe24b2c6c000588a3eff125963519b2c451f7f892cb1300016228fbfc4965894676cd96228fbfc2c2c341663b1147dfe16161a2b31588a3eff0b0b000197ec451f7f8585465fb1147e733fc2c2c32fd88a3eff1e89616197ec451f7f8ef8b0b0cbf6228fbfc7605858611b1147dfe2732c2c336588a3eff12c16161a0ac451f7f8954b0b0
  else
  0xb1147e593fc49688d8588a3f2adfe24b446c30dd88a3eff125a0a6186e8fce67f892d0530b1147e5ebfc4968298588a3f2c9fe24b414c2c451f956ff125a0a6147e593fc77c92d0530b1147dfe25c496829861bb1147dfe24b382c30dd889ccff1259c1616228fcbd7f892ce0b0b1147e593fc4967058588a3f2adfe24b382c2c44bd7f8f45259c1616228fbfc4b892ce0b0c376228fbfc4966118588a3eff12e24b308c2c451f956ff125983616228fcb27f892cc130b1147e5ebfc4966018658b1147dfe24b2f0c316588a3eff125978618b2c451f7f892cbb30)))
  else (if i < 92 then (if i < 90 then
  0xb1147e523fc76092d8588a3f2adfe3a7496c30dd88a3eff139a4b616228fcbd7f89cd25b0b1147e593fc4e692d8588a3f2adfe273496c316588a3eff13324b616228fccd7f899925b0cb16228fbfc4c692d8588a3f335fe263496c2c451f99aff130a4b60002c451f7f897125a8b1147e733fc4b892d8588a3f2c9fe24b480c316588a3eff125a3e616228fccd7f892d1f30cb16228fbfc4968f18588a3f335fe24b478c30dd88a3eff125a3860002c451f7f892d1c28b1147e733fc4968e18588a3f2f5fe24b45cc30dd88a3eff125a23616228fcbd7f892d11b0
  else (if i < 91 then
  0xb676228fcb277c92d861bb1147dfe3be496c2c451f97aff1df24b616ce8fcb27f8ef925b0b1147e593fc77c92d8588a3f2b1fe3be496c2c451f956ff1df24b616228fca47f8ef925b0c376228fbfc77892d8588a3f2f5fe3bc496c2c451f964ff1de24b616228fcab7f8ef125b0b1147e553fc77892d8588a3f2a5fe3bc496c2c451f94eff1de24b616228fcab7f8edd25b0b1147e53bfc76e92d8588a3f2adfe3b6496c2c451f952ff1db24b616228fcab7f8ed125b0b1147e553fc76892d861bb1147dfe3b0496c2c451f97aff1d824b616228fcb27f8ec125b0
  else
  0xb1147e55c0a7f892d8588a3f2ca04bfc496c2c451f957009fe24b61962c451f99af9125b00016228fccd7c892d4588a3f335fe3e4496c2c451f97aff1f224b618b2c451f99af8525b00016228fccd7c292d4588a3f335fe3e1496c2c451f964ff1f0a4b616228fcab7f8f7925b0c376228fbfc7ba92d8588a3f329fe3d9496c000588a932f5e8a4b51622a4d1f97af4525b0c376228fbfc7a292d8588a932f5fe3d1496c2c451f97aff1e8a4b616228fcb77f8f4525b0b1147e593fc7a292d8588a3f2adfe3d1496c2c451f948ff1e8a4b60002d9d1f964ef925a8))
  else (if i < 94 then (if i < 93 then
  0x16228fcab7f892d4588a9347e55bfc496c2c4528a3f2adfe24b616228fce6956ff125b0b1147e6dcab7f892d8588a3f33a55bfc496c2c451f99b2adfe24b60002c451f954ff125a80016228fca97f892d4000b1147e53bfc496a000588a3f291fe24b516228fce6948ff125b0c596228fc507f892d8000c5947e223fc496a316588a3f111fe24b618b28fccd888ff125b0b1147e594447f892d8588a3f2ae20bfc496c2c451f97b101fe24b61962c451f830ff125b0001962c440e7f892d4658b1147e073fc496c32c58899b039fe24b616228fcbd81cff125b0
  else
  0xd056228fcb27f892d866cb1147e593fc496c331d88a3f2c9fe24b61962c451f964ff125b0c596228fcb27f892d85f6b1147e593fc496c2d9d88a3f2c9fe24b60002c451f964ff125a8b115268fcb27f892d8588a5f47e593fc496c2c451f9cd2c9fe24b616228fcdb964ff125b0b1147e66cb27f892d8000b1147e563fc496a345588a3f2adfe24b61a0ac451f956ff125b0cd96228fcab7f892d8659b1147e55bfc496c32c588a3f2adfe24b618b6c451f956ff125b0c596228fcab7f892d85f6b1147e55bfc496c2d9d88a3f2adfe24b61642c451f956ff125b0)
  else (if i < 95 then
  0xcb16228fcc47f892d864eb1147e623fc496c316588a3f311fe24b61892c451f988ff125b0d7b6228fcbd7f892d86a1b1147e5ebfc496c345588a3f2f5fe24b61a0ac451f97aff125b0cd96228fcbd7f892d8662b1147e5ebfc496c32c588a3f2f5fe24b618b2c451f97aff125b0bed6228fcbd7f892d85b3b1147e5ebfc496c2d1d88a3f2f5fe24b60002c451f97aff125a8b115268fcbd7f892d8588a3f39a5ebfc496c2c451f9b72f5fe24b616228fccd97aff125b00016228fcb77f892d46bbb1147e593fc496c351588a3f2c9fe24b61a2ac451f964ff125b0
  else
  0xc37622bbd1f7f892d8629b115268fbfc496c30dd88a9347dfe24b600032c588a1eff125a8cb18b2c450f7f892d8658b1147e87bfc496c30dd88a3f43dfe24b6186ec451fa04ff125b0cab6228fcf87f892d8629b1147e773fc496c00061bbed399fe24b5186efb5889ccff125b0c377da8fce67f892d861bb1147e733fc496c30bd88a3f399fe24b6186ec451f9b6ff125b0d4b6228fccd7f892d864eb1147e66bfc496c312588a3f335fe24b6186ec451f99aff125b0b4d6228fccd7f892d8588a7747e66bfc496c2fb588a3f329fe24b60002c451f994ff125a8))))
  else (if i < 103 then (if i < 99 then (if i < 97 then
  0x1956c451f7f892d46b6c596228fbfc496c32762cb1147dfe24b6000314d88a3eff125a8cb1892c451f7f892d864ec496228fbfc496c35d61bb1147dfe24b61ab30dd88a3eff125b0d1586ec451f7f892d8682c376228fbfc496c33b61bb1147dfe24b619b30dd88a3eff125b0cb186ec451f7f892d862cc376228fbfc496c00061bb1147dfe24b500030bd88a3eff125a8c377dac451f7f892d862cbd36228fbfc496c32c5e4b1147dfe24b61956d9d88a3eff125b0c376cec451f7f892d8658c595de8fbfc496c00062caef47dfe24b518b2c4577a3eff125b0
  else (if i < 98 then
  0x136dfe24b21c31148007f8ef0b090e188a40024b446584870c452001fe24b276438622900147dfe24b2c23014800a3eff12916117ca40051f7f892cbb0bd52003275887f892c5ba900193ac43fc4962cd4800a74ff125961164a40051f77c92cb08aa52002c451f98892c4f2900198ac451f2c22614800b114fe8f961130a40057ca3e92cb089852002c45134965844c290019b2c451f2762614800a3f0552596112ea400588a3f3112589252002c444d49658436a9001399fe24b2c219d4800b1147e55bfc096a400588a3eff12584553abf2c588a3eff125b0
  else
  0x147e6dbfc7783114800a3f2adfe3bc188a40061ba3eff1258c4520028fce47f892c622900147e5ebfc4963114800a3f2c9fe24b188a40051f956ff1258c4520028fcdb49688c622900147dfe24b3063114800a3eff125961188a4005177f892cb08c45200289bfc496584622900147df7a4b2c23114800a3efa525961188a4005497a292cb08c4520028fbbc446584622900147dfe21b2c23114800a3eff0e8961188a40051f7f892cae0c4520028fbfc496564622900147dfe24b2ac3114800a3eff12593e188a40051f7f8ef09d8c4520028fa4b4464ec6229))
  else (if i < 101 then (if i < 100 then
  0x1621fe24b2c24394800b00ff12596121ca40057c7f892cb090e52002c43ef4965848729001621f4a4b2c24394800b66ef92596121ca40058877888cb090e52002c43fc4365848729001621fe1d12c24394800b10ff12595c21ca4005887f892cac90e52002c43fc4965588729001621fe24b2824394800b10ff1de13b21ca40058849688c9d90e52002c43fc4965848529001621fe2552c24214800b10ff12597020ea400624a3eff125901520031251f7f892c7e29001671fe24b2c23ed4800b10f45259611eaa40051f7f892cb08c6520028fbfc49658462a9
  else
  0x1622a4bd14964ed4800b6747ddf24b276a400588a3eff11993b52002c451f77888c9da90016228fbfc4364ed4800d1547dfe20a276a400588a3eff0e893b52003415887f87049da90016228fbfc3064ed4800becff12596126ea400588a3eff12593452002c451f7f892c94a90016228fa614964894800b10ff125961220a4005887f892cb090f52002c44db7f8ef0872900162255bfc7784394800c37621fe24b21ca4005889c8ff12590e52002c44bd7f892c8729001622593fc4964394800b112adfe24b21ca4005889b692d1190e52002c43fc49660c8729)
  else (if i < 102 then
  0x16228fbfc4965314800b1147dfe24b292a400588a3eff12594652002c451f7f892ca2290016228fa4b4465114800b1147dfe24b282a400588a3eff12593e52002c451f956ff09da90016228fbfc7784ed4800b1147dfe26b276a400588a3f13d2593b52002c451f82e92c9da9001796c43fc4964ed4800b114d5fe24b276a4005e3a3eff12593b52002d2d1f7f892c9da90016228fbfc4964ed4800b0147dfe24b276a40057ca3eff12593b52002c45177f892c9da900162289bfc4964ed4800bed399fe24b276a400588a3efbd2593b52002c451f7d292c9da9
  else
  0x1601fe24b3825854800b10fa5259c12c2a4005e8b1092cdf16152002c451f7f86e8b0a90016228fbfc4965814800b1147dfe24b2bea400588a3eff1de15c52002c451f7f892cae290016228bbfc4965714800b1147df7a4b2b8a400588a3e92d1195c52002c451f7f8ef0aca90016228fbfc4965654800b0147dfe24b2b2a400588a3efa52595952002c451f49688caca90016228fbfc49655d4800b1147dfe3bc2aca400588a3eff12595652002be51f7f892cab2900162289bfc4965594800b1147d25a232aca400588a3eff12595352002c451f7f892ca929)))
  else (if i < 106 then (if i < 104 then
  0x16228fa4b4465854800b0147d25a232c2a40057ca3e92d1196152002c451749688cb0a900162289a4b4465854800bed39925a232c2a400588a3e9610f16152002c451f7f886cb0a90016ce8fbbe4365854800b1147ddf21b2c2a40051f77c92d0d96152002c451f44686cb0a900198e8fbfc4145854800b5b47dfe20a2c2a400588a3efbd05161520028bbfc496828b0a900147df7a4b4145854800b7b47d25a092c2a400588a3eff0e896152002c45497a2744b0a9001621e8a4b3a25854800b1147d119d12c2a400662b10ff0e096152002c45417f8704b0a9
  else (if i < 105 then
  0x17c6733fc4965854800bdd399fe24b2c2a400588a3efed2596152002c451f7f492cb0a90016228fbf84965854800b1147dfaa4b2c2a400588a3efbd2596152002c45177de92cb0a90016228fbe94965854800b0147df4a4b2c2a400588a3ef992596152002c45417a292cb0a90016229fbd14965854800b5b47ddf24b2c2a4005aaa3eef92596152002c451f7f8928b0a90016228fbfc4925854800b1147dfe2472c2a400588a3eff12216152002d9d1f496900b0a9001399fe24b4665854800b1152525a2e2c2a400588a3e92d1296152002c451f496890b0a9
  else
  0x16228fd004965854800b1147e27a4b2c2a400588a3f05d2596152002f2d887f892cb0a90016229abfc4965854800b114a9fe24b2c2a400588a46ff12596152002f1d1f7f892cb0a90016968fbfc4965854800b4547dfe24b2c2a40058ca3eff12596152002c3d1f7f892cb0a900161a8fbfc4965854800b0947dfe24b2c2a400580a3eff12596152002be51f7f892cb0a90015e68fbfc4965854800b11479fe24b2c2a400588a3aff12596152002c451b7f892cb0a90016228bbfc4965854800b1144dfe24b2c2a40057ca26ff12596152002c45107f892cb0a9))
  else (if i < 108 then (if i < 107 then
  0x16228fbfc4966094800b1147dfe24b300a400588a3eff12597152002c451f7f892cb5a90016228fbfc4965954800b1147dfe24b2c6a400588a3eff125962520032fd88a3eff0b0a90016228fc3d7f85854800b1147e02bfc2c2a400588a3eff1de16152002c051f7f8ef0b0a90015f28fbfc7785854800b1145dfe3bc2c2a400588a26ff1de16152002fb4e67f8ef0b0a90016228fbef7785854800b1147df4bbc2c2a400588a92f45de16152002d9d1f77cef0b0a90016428fbfc76e5854800b114a1fe3b62c2a400588a3f009da16152002c451f7f89a8b0a9
  else
  0x16228fcdb7d292d4800b1147e66be4496a400588a3f335f0a4b52002c45499b6f4525a9001622a4cbd7a292d4800b6747e6dbbe496a4005b3a3f2c9df24b52002c451f9faebd25a90016228fbfc4b892d4800b1147dfe24b470a400588a3f36dde22352002c451f956ef111a900186ec451f49688d4800b1147e7224b446a400588a3f2f525a2352002c451f96492d11a90016228fcab49688d4800b1147e6dbfc436a400588a3f36dfe1d15200308d88a3eff0c1a90016228fce47f860d4800b1147dfe3bc306a400588a3eff12598352002c451f49688cc1a9)
  else (if i < 109 then
  0x16228fcdb7f892d4800b0147e6dbfc496a40057ca3f36dfe24b52002c45179b6ff125a900162289cdb7f892d4800bed39a6dbfc496a400588a3f369fe24b52002c451f9b2ff125a90016228fcd87f892d4800b114ba6a3fc496a400594a3f34dfe24b52002c451f994ff125a90016228fcbd7f892d4800b1147e5bbfc496a400588a3f2c9fe24b52002c451f958ff125a90016228fcab7f892d4800b1147e553fc496a400588a3f2a5fe24b52002c451f94eff125a90016228fca47f892d4800c5947e223fc496a400658b11039fe24b52002c451f9b6fbd25a9
  else
  0x61bb1147dfe3bc52002c451f9c8ff1de290016228fcbd7f8ef14800b1147e593fc778a400588a3f2adfe3bc52002c451f954ff1de290016228fca97f8ef14800b1147e53bfc778a400655b1147dfe24b5200314d88a3eff125a900186ec451f7f892d4800c2f6228fbfc496a40062caef47dfe24b520032c588a1eff125a90016228fcf47f892d4800b1147e783fc496a40061bbed399fe24b52002c451f9c8ff125a90016228fce37f892d4800b1147e6f3fc496a400588a3f375fe24b52002c451f9b8ff125a9)))))))

private def st14 (i : Nat) : Nat := unpack st14Packed 73 24 i

private def adj14Packed (i : Nat) : Nat := (if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then 0x10000108000804200000234400400814204c1c10000000860450040c02400400c101710a else 0x3410000001010150061c21800422c30852010020c00080020840821820040030400c0002) else (if i < 3 then 0xc00000000010c20000023000400800840c108618300000000c00408230000300318b080 else 0x820440090c21400001004410010860c21400000000405000050400cd0830441c10c0206)) else (if i < 6 then (if i < 5 then 0xc18e0080c01c10ca00100908005b00710a1443c1000200184145006187040600006000 else 0x8404010208f04000100500204500000004a0470061451021c40110400410030c1000) else (if i < 7 then 0x62c009a0030850420c10441cc1890832421011040c82400010c10c00053c01801c2000 else (if i < 8 then 0x8b0000050010800060432400c02c008010b10f0c50c004404004004134118d0080261d1 else 0x800090921800c00800c00430000071451810000000033800c000614310c140003002040)))) else (if i < 14 then (if i < 11 then (if i < 10 then 0xc15000060c70c3181000040042005080000009080088241286106040101182000050240 else 0x13000455c30400032810400410800044000400810583d00800030400040800411c0000) else (if i < 12 then 0x2410073801840001403050c10c20020401820002431c70400800024481411070c1087009 else (if i < 13 then 0x10200034e0100430420400420800043411000010441400430072001400431c30001420c1 else 0x60810460810080c104010a0c90021800010800430021080c10400040cc001083140081))) else (if i < 16 then (if i < 15 then 0x810c21831800001830002480001400460c20000820c110000208000d081003081086200 else 0x40070801820010c11010010020041012440000000010011820831430c12840c024b047) else (if i < 17 then 0x1821010c604000310400129610504804200700700004000d1000060400831c0041093141 else (if i < 18 then 0xe2410020001800002410001801801412c100300008700001300000004000500a001 else 0x10c10000c00840011c20011c1)))))

private def adj14 (i : Nat) : Nat := unpack adj14Packed 6 48 i

private def loc14Packed (i : Nat) : Nat :=
  (if i < 83 then (if i < 41 then (if i < 20 then (if i < 10 then (if i < 5 then (if i < 2 then (if i < 1 then 0x91ba3200000000000038a00008400000048f5f8000000a3c11b0d60005c847f5e700078c else
  0x3aa0003b19ba39b6ac4f15da7a55821ef37272365d70f0008ef1140007a36a660a79a000) else (if i < 3 then 0x9e4a1343000076248096b47327300023a0001114dc00000078d0000ba0003000f1000 else (if i < 4 then
  0x4700000063200088b5953070000007ca1774915d69013848280008e145d00000077145c else 0x4b029f73c00000055f00062e0000009916166c96bb9eb0000009070002040009cf241259))) else (if i < 7 then (if i < 6 then
  0x96d8d48d95335f42147e440a34c4fa74200000038507b000982000810656466175425010 else 0x9f41a06070000000007b29378140008be19b6f006800fa0900004f7a70001320006c3000) else (if i < 8 then
  0x7e855e1f60280000001160008265488f76520008bc04000097d0000001a96143bc000000 else (if i < 9 then 0x13100023571e91f05f00076c6245ed0000003541ff31e65318f1b06c057c00026b00012c else
  0x1569f817d3b282a55914f94a5900000000000b355300064b5d237f7480005a2527033)))) else (if i < 15 then (if i < 12 then (if i < 11 then 0x143298a2b19c33f0000005b303a1740cb4535742a95cb6897bd000282000000000000000 else
  0x39e75da216400000000ec0000007102001e00007c10000009040005830921e920a000000) else (if i < 13 then 0x69271a2ba0004bd00012021f89e63466f82b05e00000092c2dd33900078a48c8ed000 else (if i < 14 then
  0x19033104d31185b76e0009a60004996d96b349800000000075054b4474280007b10005cf else 0x61d0000615cd31d00000045e6cb0005fa0002f000000004959f0004b200032b0c4000468))) else (if i < 17 then (if i < 16 then
  0x4044cb59b05b73363568400029637c3e74483ca2501e5a20834672488000000109000000 else 0x9ca0006fd3272d017126f00000047a9e803e83a50600096205300000023111e00038c4e0) else (if i < 18 then
  0x3383800007c00000000000000003026b6000a1926c0bb00000078b4d683b37a7776de2fd else (if i < 19 then 0x3f00092f0008d587aa3b00000020199c6519980000000000001cd4d21fc00049f000 else
  0x63800000093874a4cd02b8ad68e0006185dc00089600000016b27c6d68ffa1d000000253))))) else (if i < 30 then (if i < 25 then (if i < 22 then (if i < 21 then 0x6335947cd7f800000070c569000000a470000be0003cc0f86500000003510007317612c6 else
  0x2cf0000600004217640000007dc19f0000000004a792100015e0007c900062d88a000164) else (if i < 23 then 0x97a0006ff8000008a82f95d40001b40308890004ff91901a3fb6806a83dc5d14c63af4d7 else (if i < 24 then
  0x19404c02d18967d0a50500000004902e621b00044600028564925f0003402a6699149000 else 0x7430001d641d1ab5e00063060b70000006d52495420008688a90b8000000000027000000))) else (if i < 27 then (if i < 26 then
  0x50500074701e9a200000029a8e8a2274c6a300042d4dd80437e0468f92ec6ee000611 else 0x9b50090007299938771c00003e154560e0007d61a60000000006708e36974037b3) else (if i < 28 then 0x19100012d1170000000000000008f27980006961cb2510002102d5727a080006c56fc3d1 else
  (if i < 29 then 0x5d080e000a1f0a4a2f44442200083264e0f762a7157380000000008a42171656c28095c0 else 0x2a01020005912b12e349d43500000000069a4c156f00000020989700000000000060b)))) else (if i < 35 then (if i < 32 then (if i < 31 then
  0x8e0007c798d0001e25de00048b08075460c4af8cf0000008ac0009ad93422a2c186b000 else 0x9850a300012f0bf00000000007a29b5700000008160000b00005fe6020000007460006d8) else (if i < 33 then
  0xd89718d78cd5ca00004a0000000000005f10000004324f300000000066652c00024a836 else (if i < 34 then 0x18d2341ca77d0004cc5d53e300024e0004810003b93cd9a53e466104e479929000464 else 0x5828e0000008c79f16dc2da0000004cf0008085e233c1fd9da000000000176182))) else
  (if i < 38 then (if i < 36 then 0x2471c800011c87b0000009810000752583999160000a81417fd00010013b6cf2758a1 else (if i < 37 then 0x6bc7127aa70e08b1f733e00000018c4ca000000000000024104a4d92d3693350003e8509 else
  0xa260002be79d5d70004ed28810396a00000099e4020007d900034400000000069f136000)) else (if i < 39 then 0x3479060004a600025681f65b00008fa4300000000035a89a0000003269580000a6933 else (if i < 40 then
  0x3610000006c43a697b1ea000000000000318a0d00e0000007555930004d90000eb6f658a else 0x8e42903902660000000000000002230009aa0000000002ad0006e0000000923)))))) else (if i < 62 then (if i < 51 then (if i < 46 then (if i < 43 then (if i < 42 then
  0x47700043429368500000000000057d0006365db5c900057b3b8389a1a000000 else 0x44b2d639786307c6010f69c43190529f341a29d1518127660d40fb07380c9de0486c18c4) else (if i < 44 then 0x24686a0002609d70000000003da0d27344d00c600052d76a6d23bd4aa54e00000067f else (if
  i < 45 then 0x7f00003a5000069000083a0600000016d00000000000d1b618694e0005bb0000002a1000 else 0x1620005385f20001b90003b32aa0811c489b00145a00081d2ce6a200000084c))) else (if i < 48 then (if i < 47 then
  0x23e0003d80003d90005668ee38634b2cd7a98660001072a40009e0541187472000 else 0xa2520c8b800040914e7ba2a795d66400049400045b00075c0a700023b91200075707643f) else (if i < 49 then 0x3f23170007630c200063b00000062600070a0001db72a6424ab2c86b800000015a36b471
  else (if i < 50 then 0x2740001731183781c714b00025b0e000035f24c1677975ec00000007f30a000000000758 else 0x85313f567000000377000227a0b6cd0007c6000000000000931000996a4883396f7b4051)))) else (if i < 56 then (if i < 53 then (if i < 52 then
  0x9c3000a4900013d00050100000c5113b58c30000000008744605024c78240ff52320b5b8 else 0x58b62342b00012500032e7ed00001f89d09400000052e56c0000003ba00048d4a2000695) else (if i < 54 then 0x39106a7d20fe01c2ee23f86e0004420000000000008ce0000007cb3f67064e838f902
  else (if i < 55 then 0x33226d95c0c33e554449a00015b9fb000263000000000a170000005fc0000c599037d else 0x1be59e5508691f38180000000000005080000000355400005d30003ef80d1050007f532f))) else (if i < 59 then (if i < 57 then
  0x3430000006e251600040840500051a0000a10009a99db00044f0000000007e23040d9a1e else (if i < 58 then 0x7d84b10000f494964691c00093b0000362617fc0000998941bd95209c00002c2c20b5000 else
  0x25c0ae5550000650000001590004117a882f8cc9f60000003c50008ec00078897e264)) else (if i < 60 then 0x2b966c9ef0009c000010f0000007530009bf0320009fe9080002ed1a49d04750190008e5 else (if i < 61 then
  0x25e9890006fa49264c09b26786468100075928100021e0000009fa6a908a9d300033b else 0x5321af3f781c66300019a41078e0e90004c97720001e100047e0003f10720c07b0000000))))) else (if i < 72 then (if i < 67 then (if i < 64 then (if i < 63 then
  0xd36620d16ad3c78daa462910008a3a1236a0006f462077500073719e4610005862ea782 else 0x42c4630000aa3038c92ae31000017c0000009b00000005720000d00000008b510d6d4) else (if i < 65 then 0x6d39b202022243b53e00016a00045020d83d0000cf63a34125500000099400000040b7bc
  else (if i < 66 then 0x6bd05483800085c0007e700042a0008580004e700000083f5ad00000000042f00054a000 else 0x5bd0003b71e753d1a8a406df16e5e594106b0000449c500000000006656a09d000))) else (if i < 69 then (if i < 68 then
  0x4705109ee00041752827189c00000001d0000000008076ea9ec3ae69d1ba31b12612b8ba else 0x8574de2b70002db6900000ee6d78ae62b7f17b70005927f61f98e21f51990000001f4000) else (if i < 70 then 0x5129504fe02900000044063900077976700099700074563e03841b74194b4e4000599
  else (if i < 71 then 0x2120002780ce6199407e300013c4f268f7ae2b89030002a30000003de7f443d00030c342 else 0x667a425890000009e60008de00000000000000000048650b8192200000c9000a300003a7)))) else (if i < 77 then (if i < 74 then (if i < 73 then
  0x8c0000003b651c0008590009fc95e4db0007ce5c1a004a89184fc00059aa398b1000000 else 0x35d0003c12c900000021865c84e0000000003f027b4840004d503795946d106000) else (if i < 75 then 0x82369800089597c5135294fd00036580346b31c2d38a200032c00093a0000007c89a7 else
  (if i < 76 then 0x7092af66800051400000093f4e5a2900083c3150000001e40008fb0000000003dd7ee else 0x74b2800003e04060009dc44e0006a78c06040000003c200064500064398e387018000004))) else (if i < 80 then (if i < 78 then
  0x9bb5e10001837730174c31d70000002c530839602100008600041567511045466b else (if i < 79 then 0x28b61b8f6977000a2700021a6e46280000002f24967878ab7d12370006088c115382c else 0x40e2110b600000000051e4e2a3e6550008760000000820008470269f70000001697e5000)) else
  (if i < 81 then 0x9d80e200057a00000000000000000000000000070700000092e64800000067c394063368 else (if i < 82 then 0x48a7846b58027fb9369cd433a370000003f300063724889f85f0005a158f53b673547 else
  0x1980ef2e42fe5604290000000003ec6475cc33610e00000080b3d60000000000000008dc))))))) else (if i < 124 then (if i < 103 then (if i < 93 then (if i < 88 then (if i < 85 then (if i < 84 then
  0x1e81726f35b02402990000000d73ea0000003531f800000067e35b75f8ca9d5000000000 else 0x1c58f80000000006584b31528aa0424ec8672bb0981a700035e000000a3400000022e000) else (if i < 86 then 0x1f03ff0008a07818017b90003a38850002b211d0002f80006a45a30009bc8fa65e000
  else (if i < 87 then 0x6656b70000001e642768a20f0008d00935564c40001b10007fa95f72b0000dc000395000 else 0x1799cc0007515047680000590000000004a9161000a160001f1a2c0f243c0005f561a328))) else (if i < 90 then (if i < 89 then
  0x73a73000059c0000000c86ab93c0004b76595526a51d581b0001da0003e2000000000 else 0x770004b800079b3090000003830004f920800028300037400000012200000000070d124) else (if i < 91 then 0x1781d30008dd94696300005d52b00070300091e49b0000000003c926e0000df4b47c5000
  else (if i < 92 then 0x24b00052a6ae3f898660086d3570000000002cc6152658825f38060bd58e000000961 else 0x9b40de00009e0070008b23016412e28110006fb8990001b30006220008c200000046e53f)))) else (if i < 98 then (if i < 95 then (if i < 94 then
  0x3ce5469640db0000000002f62ac88c51f0000009d673f00061e0000850005b61ed0009a8 else 0x6122f70fa53100012793d0003888f17ff18175e4b50000f50000008f35aa0001d4) else (if i < 96 then 0x3d00051d058400030d4234410005768d600367a3a43640e5000554000000031000495000
  else (if i < 97 then 0x45764d6ce000a0a60d9607f9795000a2d0003be1c11ee1153814ba0007940004bb41c000 else 0x1d143e0008f066d6c80ab00088f00015f0002df00055a0003df8728e6000277000000348))) else (if i < 100 then (if i < 99 then
  0x8c80970000006442bc00020e2d40000000000003620003670a298300088800087f133401 else 0x2391500000005717198a600000072c15c0006b22a284540f7e13a87391574e19c1000000) else (if i < 101 then 0x2ff0006910000004d37a03660009433d409a0000000fd0006b160957777603b16f
  else (if i < 102 then 0x6130009b82c773d0003ad0009ed00010a45f1688787e039c00053749700035c6d08fd726 else 0x62737684f5b401123d3d72690006e518061c00000029e83e38d6cc4ee000000000000000))))) else (if i < 113 then (if i < 108 then (if i < 105 then (if i <
  104 then 0x4f03a23f900044300010800005613059d012000a453c666aa0734e48590d850000000000 else 0x41f1669309787dd30500000036f00b0000007990b102e8310000000000000d5000) else (if i < 106 then
  0xe300005c0003db99d76f45295b2d22943a10000005ba9bd69e0004d465a5347ec000 else (if i < 107 then 0x8420000000004ae17e9c711946c29200078f55754c22668300000000082d54d07988638e else
  0x45627225d3b00256a17de22f7d41401ec9269b181377f80f0006799ae9b631f0002eb000))) else (if i < 110 then (if i < 109 then 0x7f2722000a0f0000000007698710009e37ef0007e600063d0000000000005a60001ad431 else
  0xb20000000000000009c8000a030005a006d8402624c898700081e00085633412a142121) else (if i < 111 then 0x1b81c932900049c07d0002e70008bb6da0000000005fd4f40004df98029562f00071d9fd else (if i < 112 then
  0x73e0889791880000000008b9000a1118b2061bc39f78567603d184000000890145000015 else 0x524a237c4a1c00068d3e65649246ed7eb2e10004bf57e00014d8430962bd6300009272b0)))) else (if i < 118 then (if i < 115 then (if i < 114 then
  0x7bf9b900071f4f726a95a00050a1b24670000a900000000000085100079699b5615eaa41 else 0x1aa58700099f3ab1700002f37fe000a020000000000009532871233a9000000000478861) else (if i < 116 then
  0x18a83700000000028d0005dd6f20000000004a10000000006e76f500008785d88d5e40af else (if i < 117 then 0x9105659c672d6f80000fc00070095668c8555a50004590000003c000000044c883a31972 else
  0x7b69699670004ce0000000006609485ff000196a4b00069c0009b393e9c248e02f000625))) else (if i < 121 then (if i < 119 then 0x85281751d0005973bb8eba289f000000000000000028f4627210001f28157d3322000363 else (if i < 120 then
  0x9136690e487c00000074e92577e23897597f26800007e207000a1b00096843700091d000 else 0x68871694542e3379d48a70008b60ed71100003c00095585e69463134f64f7ac2139f9000)) else (if i < 122 then
  0x1930000008b38499393a004b0000008b40004d10004075e386f9470005bf8790575ee9e9 else (if i < 123 then 0x3568f48410006544a30000009ff63c1fb8fc0007a600024317f289a106ec00000031363f else
  0x8a58d357928a2b43d28350140001a145569b2ef0000004499706eb00025a973674000451)))))) else (if i < 145 then (if i < 134 then (if i < 129 then (if i < 126 then (if i < 125 then 0x2e90000912fc85a00015800025200031600000082157f7c25e68600000007f31c61eb000
  else 0x75b43a6b90ad6ef61f23241e4da9c986217b0004eb0006e65b934d5300000001d2000) else (if i < 127 then 0x55c0da6e14a5438a3f00000034a000101580a241cc4763cb8480005f63755184fb58c else (if i < 128 then
  0x88046f0950000000002247a400028608d82200000039a00041850e4160000005ef else 0xa448250001551852454e6a2e01b07000000032d06e51956d0ac3820009d24650007783c8))) else (if i < 131 then (if i < 130 then
  0x56ba3353c3257ab588a0e0004f50000009570395ae0005f067b22c82731200000080a3f4 else 0x9322290236aa00000047d0004ac00011f83994f73b99960682909018e112526543a2a705) else (if i < 132 then
  0x9888c500058d0001ac21c2e500029c90b3730000008e97900000000559f5000000525034 else (if i < 133 then 0xe74ad00077084433070833a21600049e3586860000009447495c60005e94c00004f6 else
  0x8549e700075a11a7800ca3cf13e22b0005f97040008051c300071b9955a76b45219a1000)))) else (if i < 139 then (if i < 136 then (if i < 135 then 0x1477744c540d2f49768b74ea62100068782070b000000202a186f990e44d0008d16bf else
  0x24200039841490a00000065f0004c2954a0c0005980001d80008cb53900043914a00040c) else (if i < 137 then 0x7912ca0005c527a0000007bb27e8750000002159e13239749b70006db426000000067 else (if i < 138 then
  0x2449098df7020000002979ac0002e83fa00053a8736290bc5c400000036e783671000000 else 0x5e800098c0000000007be2b66770000003fc13877a36d2de0006100006ba917474549000))) else (if i < 142 then (if i < 140 then
  0x9cb2fb00098f7255d90003bf0ea1df3d50002c37ad7d00000f92faa1400000094d0c7 else (if i < 141 then 0x8f546960f00058500000000017a0000005780006fe0080000000001a36e8128000205000 else 0x1fa00027f3497ea7139a00002d90000000005517010000009e20000002d13fe7d75af))
  else (if i < 143 then 0x7b80006932212e00e871c6f10005d800090f000089000000a0579202a79e000000 else (if i < 144 then 0x7441cf5b788472422d6be0b922868b0003717200000a07a100000000081a0001c2a01000 else
  0x2f10026c60005ce39d3c48e74878fe90592028400037072e0000000000000410001de52f))))) else (if i < 155 then (if i < 150 then (if i < 147 then (if i < 146 then 0x1950131371442d772fa3d0009a300053509f3d344a00095184d0007af00000000092276b else
  0x23092800044500050f7869a49ce00054f79f06252204338b00007100077ca35000891) else (if i < 148 then 0x16c0001b58700001e32c44be4ef5205750000009920000005eb0007189112b5935000 else (if i < 149 then
  0x5df0000000004364e90000e100010c1ce0004e35c313542400051b00007800094c966740 else 0x333a3855d6172545be0009ea5b5000489000a1584a0006ca7df000a4a0000008db5034bc))) else (if i < 152 then (if i < 151 then
  0x1a291a00032a0e600096e30b0000000006f712e46a00057300050d1bf4b600000000006c else 0x1d986c0003590000008e02dc01651500092b0008bd0000000000009df6030000003927c3) else (if i < 153 then 0x9d10006a00000003e98b08ea00000016087e1929ab0000002700005ac9d9000 else
  (if i < 154 then 0x6c70000000dd4a04190006050006e974d0006dd00098a56200076514821d00030f000 else 0x1390001296af00051700000019d0007da0001dc0003ee0000000001ae62c893596682)))) else (if i < 160 then (if i < 157 then (if i < 156 then
  0x74f7f75fb9dd71400024d5361dd39300000000091556e0c172847b0f3a3a4a4887000 else 0xf041348236c6e30002ab0002c02a50008925b150c31a0003795c27565007db4f8000400) else (if i < 158 then 0x73673200014c0009e56784580000008309001bb00076d11300010b000000793000 else
  (if i < 159 then 0x2a80000000000007608467a256300089892a8d25071fe0000cd8c677b0220000b4000 else 0x5a9af78984b00066e5a482e5f70005a88bf00015400000a3240001975b200006479c))) else (if i < 163 then (if i < 161 then
  0x99a2cb0004d83b45a90004127d594298437b5ab33d0002363c300049300065773530e else (if i < 162 then 0x31458100000023334500027d0007e935028c8af20315d0005580002790007cc87d2d8 else 0x36000007404527690c9144b964aa040007b50000003fd6b02253463f53210001340005bc))
  else (if i < 164 then 0x8d8257000000a4c4209659f286588e2190000000005c72f50002b348323c0003ac6d1568 else (if i < 165 then 0x47c06f1460cc00024f3553eb7cf96c32000000035288100016300098ba363ed7170002bf else 0x55b13a1b77529be0001a5))))))))

private def loc14 (i : Nat) : Nat := unpack loc14Packed 12 24 i

private def edgeMeta14Packed (i : Nat) : Nat :=
  (if i < 27 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then
  0x4300430043004300421041103f203e103c203a203820362034203220320031102e302b302a1029102900281027102610242021301d401b2019201810171016101510132010300b5009200720061005100500032003000300030002100110001 else (if i < 2 then
  0x510051004f204f004f004f004f004e104e004e004d104c104c004c004c004c004c004c004c004b104a1049104810480048004710470047004700470047004700452044104400440044004400440044004400440044004400440044004310430 else
  0xa420a2209d509850944090408e208e008e008c208c008c008930863085107f607d207b207920772076107510732071206f206d206a306a0069106900690069006900672064306310621061105f205d205b205a1058205530532052105110510)) else (if i < 4 then
  0xf840f440f220ef30ee10eb30e920e630e150df20de10de00de00dd10dc10db10da10da00d910d810d800d710d520d500d410d130ce30cb30cb00cb00cb00cb00ca10c820c530c230be40be00bd10bc10b750b250b200b110ae30ae00a860a62 else (if i < 5 then
  0x12821262126012601260126012601251124112311221121111f211d211c111c011c011b111a1119111811162116011511141113111211111110110f110e110d110d010d010d010c110b110a110a0107310521041103110030fd30fd00fc10fc0 else
  0x1562154215311512150114e214c214a21482145314501450143214301430142114201411141014101410141013f213c313c013c013c013c013931390137213521332133013301330132113201311131012d412d012a312a012a012a012a012a0))) else (if i < 9 then (if i < 7 then
  0x188018801880187118701870183418031800180017e217e017e017e017e017c217c017a217a017a017a017a0179117811762174217311730172117111701170016f116e116d116c116b116a11691168116711661165116411631160315a61582 else (if i < 8 then
  0x197319251920192019201920192019201920192019201920192019201920192019201920192019201920192019021900190018f118d218c118c018c018c018c018c018c018c018c018c018c018c018c018b118b018b018b018b018b018921881 else
  0x1d011cf11ce11cd11cc11cb11c831c711c161bf21bd21bb21ba11b911b721b521b321b121af21ac31ac01ac01aa21aa01aa01aa01aa01aa01a911a901a721a521a501a501a501a501a501a231a201a201a201a1119e319d119d019c119b119a1)) else (if i < 11 then (if i < 10 then
  0x1f101f101f101f101f011f001f001f001f001f001ee21ee01ee01ee01ee01ed11ed01e941e631e601e601e421e401e401e401e401e221e201e021e001e001e001e001de21dc21db11da11d911d901d811d711d611d511d501d411d311d211d11 else
  0x2040201320102010201020011fd31fc11fb11f921f631f151f101f101f101f101f101f101f101f101f101f101f101f101f101f101f101f101f101f101f101f101f101f101f101f101f101f101f101f101f101f101f101f101f101f101f101f10) else (if i < 12 then
  0x22f422c322a222822262225122502250224122402240224022312221220221f121e121d121c121a221a021a021732170217021702161213321212120211120e32095208120622060206020512050205020502050205020502041204020402040 else
  0x27c627a227a027822762271526c526c0266626512641264025e625c225c025a22582253524e524a424a0248224712470247024702470247024702470247024702461245124412431242124112410240123e223d123b223922381237123522332)))) else (if i < 20 then (if i < 16 then (if i < 14
  then 0x2c522c232c112bf22bc32bb12b922b542b322af42ae12a862a622a422a4029e629c229a229912981297129612942294029312930293029302930293029302930293029302930293029302930292128c628b128a128a028a02891283628212820 else (if i < 15 then
  0x301230012ff12fe12fd12fd02fb22f832f712f522f232f112ef22eb42ea12e912e812e712e612e062de22dc22db12db02db02da12da02da02da02d912d902d812d802d712d702d612d512d502d502d322cf42ce12cd12cd02cd02cb22c742c70 else
  0x354334f534c3347534253420341134103401340033f133f033b4337433613360335133413331331233103310330132c43284327132613251325032233211320131f131f031f031d231c13193317231613133311230d430943054304130403031)) else (if i < 18 then (if i < 17 then
  0x3b303b033ae23ad13ac13ab13ab03a833a623a513a323a303a303a213a203a203a203a113a103a103a013a003a0039c439b139b03965391538e338b33865383337e537b33765373336e536b33692367236523632361235f235e135c235a23573 else
  0x3ef43eb43e923e903e903e813e623e513e413e403e223e113e013de23de03dc23dc03dc03dc03db13d923d723d613d603d513d503d413d313d303d303d303cf43ce13cc23cc03c753c613c423c403c133be33bb33ba13b823b623b513b413b31) else (if i < 19 then
  0x4200420041d341d041d041d041d041d041b241a1417341524114411041014100410040e240d140c140b140b040924081406240604060406040514032403040123ff23fe13fe03fe03fe03fe03fb33fb03fb03fb03fb03f833f713f523f503f32 else
  0x45004500450045004500450045004500450044f144c34493447244614460445144324412440143e243e043c243b14392436343334330433043304321430242f142e142d142c142a242a042824280428042804271425242504232421242014200))) else (if i < 23 then (if i < 21 then
  0x47d247d047d047b247a14782475347234711470146b546834680468046624660466046424631460345f145c345b145a1458245624542452245114501450045004500450045004500450045004500450045004500450045004500450045004500 else (if i < 22 then
  0x4bf14be14be04bc24bc04ba24b824b804b804b804b714b614b424b404b404b404b134ae34ae04ad14ac14ab14a744a344a214a024a0049d349c1499349724970496149514950494149314930492148f348c348c048c0489348814853480547f1 else
  0x50c1508450445031501250104ff24ff04ff04ff04fe14fb34f834f714f614f334f124ee34ee04ee04eb34e834e714e254df34de14dc24dc04dc04db14d924d634d604d604d424d404d134d104d014d004ce24c774c614c424c224c024c004c00)) else (if i < 25 then (if i < 24 then
  0x5370537053705370537053705370537053705370537053705370537053705361536053335312530152e25277524352315212521052105201520051e251e051c251a251a051a051a051915181518051805180514451135110510150f150e150d1 else
  0x575157325712570156e256d156b25683568056715652562356205611560155f155c355b155b055b055b0558355535523550254e254b3548354175410541053f253d253c153a25391538153805371537053705370537053705370537053705370) else (if i < 26 then
  0x5ab25a925a905a905a905a905a905a905a905a905a905a815a715a615a515a415a315a215a0259f159e159c259b15992598159715961595159415922590258f158d258c158b1589258725861584258315821581157f257d257b257a157825762 else
  0x5de15dc25da25d825d625d245ce45ca45ca05ca05ca05c915c905c815c715c615c515c415c315c215c115c105c105c105c105c105c105c015be25be05be05bd15bb25ba15ba05ba05b915b815b715b615b515b415b315b215b115b015af15ad2))))) else (if i < 41 then (if i < 34 then (if i < 30
  then (if i < 28 then 0x62e162d162b262a162826280626262516241622261d561b26183616261426122611160f260b460836071606160245fe45fa45f915f725f525f325f125ef25ed25eb25ea15e915e815e715e615e515e505e415e405e315e215e205e115e015df1 else (if i < 29 then
  0x67c2677567526723671166c566a26673663465f465b465a165916590659065906590658165716570657065706570656165516541651364e364b36483644463f563e163e063e063b36383638063626360635163416322631163106310631062f2 else
  0x6c806c716c436c316c216c116bf26bc36bc06b936b816b716b616b516b236af36ac36a936a636a066a0069f169f069f069e169b3698369806962695169326921692069206920691168f268e168d168b268b068926881687168436822680267e2)) else (if i < 32 then (if i < 31 then
  0x7070707070707070707070617051702370026fd36f856f626f606f426f316f216f026ef16ef06ed26ec16eb16e926e906e906e906e906e906e636e246e026df16df06dd26dc16dc06da26da06d646d426d316d306d126cd46cc16ca26c826c80 else
  0x744074407440744074407440744074407431740373f173e173e073d173a37391738173807371736173517332731272f272e172b3728372627251725072417231721271e371a471647160714271227111710170e270d170c170b1709270907072) else (if i < 33 then
  0x76c076c076b176a176827680768076807680768076807671767076707670765276507641762275f375b475a175827562756075607560756075607560756075607560756075607560754275407531751274e374a4749174817462744274407440 else
  0x784078407840784078407840784078407840784078407840784078407840784078407840783178307830783078307830782178207802780077f177f077d277c177b177a1779177817762774277227720772076f376f076f076c376c076c076c0))) else (if i < 37 then (if i < 35 then
  0x7d037cf17ce17cd17cc17c937c637c337bf47bb47b657b337b307b307b307b037ad37ad07ad07ab27a927a907a817a717a617a427a407a227a117a0179f179d279b2797479527914790178c47884784478407840784078407840784078407840 else (if i < 36 then
  0x80027ff17fe17fe07fe07fa47f647f517f327f307f217f027ec47ec07ec07ec07ec07ec07ec07ec07ec07ea27ea07e917e907e907e907e907e907e907e637e517e417e317e037dd37dc17dc07dc07dc07dc07dc07d937d817d717d617d607d33 else
  0x84008400840084008400840083f183c383b183b083a1837383618351835083418331831282f282d282c182a282828253822381f381f081f081d281c181b181a18182817181708161812480f380d2808580808080808080718052803280218020)) else (if i < 39 then (if i < 38 then
  0x8642864086318612861085d485d085d085d085d085d085d085d085c185a285918581856285428522850284e284b384a1848284628460846084608460846084608460844284318421842084208420842084208420842084208402840084008400 else
  0x8aa08aa08aa08aa08a918a638a608a518a418a138a018a0089f189e189d189b28992898189628933891288e388a488828880888088718861885188508832882187f387b4879287548750875087508741873187218720870286b586a186648660) else (if i < 40 then
  0x8c718c618c518c418c408c408c408c408c408c408c408c408c408c408c318c128bf28bd28bb28b928b728b438b228b028b008b008af18af08af08ad28ad08ac18ac08ac08ac08ac08ac08aa28aa08aa08aa08aa08aa08aa08aa08aa08aa08aa0 else
  0x8f618f428f228f208f208f208f208f118f018ef18ee18ed18eb28e928e728e708e708e438e318e218e118e018df18de18dd18dc18db18db08da18da08d918d728d528d328d128cf28ce18cc28c938c908c908c908c908c908c908c908c908c81)))) else (if i < 48 then (if i < 44 then (if i < 42
  then 0x98729843981397e397c297849744970496d396a396739643960495c495849544950494d394a39473943493f493b49374933492f492c392939254921491d491949154911490c590668fe88fe08fe08fe08fe08fe08fd18fc18fb18fa18f918f72 else (if i < 43 then
  0xa0229ff39fb49f839f629f429f139f019ef19ec39e939e819e449e139dd49db29d839d539d329d039cc49c939c729c439c319c129c019bd39ba39b919b729b529b239b029ad39aa39a829a539a239a0299d399a399739952992398f398c39893 else
  0xa721a702a6f1a6e1a6d1a6b2a6a1a673a661a633a621a5f3a5e1a5d1a5b2a583a544a513a4e3a4b3a4a1a491a481a471a452a423a3e4a3b3a3a1a382a353a323a311a2d4a2a3a264a242a222a1f3a1d2a1a3a173a134a103a0c4a0a2a073a043)) else (if i < 46 then (if i < 45 then
  0xab51ab50ab32ab21ab11ab01aad3aab2aa83aa62aa51aa41aa22aa11a9e3a9b3a983a953a941a931a903a8f1a8f0a8f0a8f0a8f0a8e1a8c2a8b1a8a1a8a0a873a861a851a832a821a811a810a7e3a7d1a7c1a7b1a7a1a7a0a7a0a773a743a731 else
  0xae51ae41ae40ae40ae31ae30ae21ae20ae11ae10ae01adf1ade1ade0ada4ada0ad82ad80ad71ad61ad42ad22ad02acc4acc0aca2ac82ac80ac71ac61ac42ac22ac11ac01abf1abf0abe1abd1abc1abc0abc0abc0abc0abc0abc0aba2ab82ab62) else (if i < 47 then
  0xb2a3b273b207b1c4b1b1b1a1b191b181b171b170b152b150b141b0e6b0b3b083b053b041b022b011aff2afe1afd1afd0afc1afb1afb0af92af90af81af62af51af41af31af21af02aee2aed1aed0aed0aec1aeb1aea1ae82ae71ae70ae70ae61 else
  0xb8d1b8c1b8b1b8a1b8a0b8a0b891b890b890b890b854b850b850b841b831b830b803b7d3b7a3b764b742b722b711b6f2b6c3b684b653b614b5e3b5a4b573b543b513b498b481b444b431b421b420b411b401b3e2b3e0b3d1b376b343b304b2d3))) else (if i < 51 then (if i < 49 then
  0xbd80bd80bd80bd80bd71bd70bd70bd70bd52bd50bd32bd30bd30bd30bd21bd11bcf2bcf0bcd2bcd0bcb2bcb0bca1bc73bc52bc23bbf3bbd2bba3bb64bb24bae4bab3ba83ba26b9f3b9e1b9d1b9c1b966b951b932b912b901b8f1b8f0b8e1b8e0 else (if i < 50 then
  0xbf61bf51bf41bf31bf21bf11bf10bf10bf10bf01bef1bee1bed1bed0bed0bec1bec0bec0bec0bea2bea0be82be71be61be60be60be51be50be41be31be21be20be20be11be01bdf1bde1bdd1bdc1bdc0bdc0bdc0bdb1bda1bd91bd81bd80bd80 else
  0xc1b0c1b0c1b0c1b0c1a1c1a0c1a0c191c181c180c171c161c151c141c131c121c120c111c101c0f1c0e1c0c2c0b1c0a1c082c062c051c050c041c022c011bff2bff0bfd2bfd0bfd0bfd0bfc1bfb1bfb0bfb0bfa1bfa0bf91bf81bf71bf70bf70)) else (if i < 53 then (if i < 52 then
  0xc301c2f1c2e1c2d1c2c1c2b1c2b0c2b0c2a1c291c281c280c280c280c271c261c251c250c250c241c231c230c230c230c221c211c210c210c210c210c201c200c200c200c1f1c1e1c1e0c1e0c1e0c1d1c1d0c1c1c1c0c1c0c1c0c1b1c1b0c1b0 else
  0xc380c380c380c380c380c380c380c380c380c380c380c380c380c380c380c380c380c380c380c380c380c380c380c380c380c380c380c380c380c380c380c380c380c380c380c380c380c380c380c380c380c380c380c362c351c332c321c311) else (if i < 54 then
  0xc4c1c4c0c4c0c4b1c4b0c4a1c4a0c4a0c4a0c4a0c4a0c4a0c491c490c481c471c461c460c460c460c451c450c441c440c431c421c420c420c420c420c420c420c420c420c411c401c3f1c3e1c3d1c3c1c3b1c3a1c391c381c380c380c380c380 else
  0xc671c670c661c651c641c631c621c611c610c610c610c601c600c600c5f1c5e1c5e0c5d1c5c1c5b1c5a1c591c581c571c561c551c541c531c521c511c501c500c500c500c500c4f1c4f0c4e1c4e0c4e0c4e0c4e0c4e0c4e0c4e0c4d1))))))

private def edgeMeta14 (i : Nat) : Nat := unpack edgeMeta14Packed 16 48 i

private def edgeData14Packed (i : Nat) : Nat :=
  (if i < 33 then (if i < 16 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0x59aaad882cc556c488731d62cc598aaac628add563135568c5183152ba42c6eaac62ac6d8db1a56cc655b28b630be955a4a488c68ba9081c6ad98d2b6558c698ab12 else
  0xca17b327582c9992aaf648854001191beab86f2ab428ab5390fc294b3876b1f5564c4802fb646f5190b225f0c85902ba63eae58f20022a3918baac638ad989311) else (if i < 3 then
  0xa011559fe64aaf158b1f580ac15f44b89311e22803004fe1fbbf27e2cc197ae75ccaf55eabc5603e87c8e6006398010e51c00059292b1feca95caaf652fad9330c else
  0x37a0795581c35667c1181d00e668c78210360180d019030058090110200380680c0160280480802c004608bc056050030c31720a80a80715026c0980711c1f807806)) else (if i < 6 then (if i < 5 then
  0x240440800900a084078200300381201c01a02002028018005982ba65eb041300b0149d40f02865c98110b2d4ba87929a1b434aad128276587a4e632b3c8718eb9bf else
  0x4909811aa59556aad5582e05c0b40097f556ac1239735788d0af0297d8f4dc4b72058e31b33276400a01301a04a0900b82c04607c0e8150440840d81404604c10019) else (if i < 7 then
  0x5a8acc780371e23a8780361de3841aaab4dab49592cf068aacd78340660c818a6041c974fe101062c958f83005e0b816c4888c005c23746feda55f83051c0bd37a5d else
  0x804fe5cfb6c0760e01d2d852ca416ba99528aad248393fe61c1daab06a5fd55ab351e5d16a2d3288c956a2b48730ca163a006e0da1c42786f099aeb5c5aab5964ad5))) else (if i < 12 then (if i < 10 then (if i < 9 then
  0x1d63cc740465569b56e2db08aaac2284208210020aab08810cbfabc5a8b516a2bc56a3bc728e207e0f97d03c07a6bc1e83c55641c7eaab64a0ec1d0390710b5d0835 else
  0x58aaa5712aa096b8553aab0948d90b04c30eaac232c658857d6f2dd28ac7d6f2c758d0f219c2875612023c3b85f0ea173586aeb81702df594b79630f50903d4238f4) else (if i < 11 then
  0x58cacc7c0e81c21782e8567d41602a90d0a41442805155615029ab05bcb7827ade590ac0798e91c013826aab2143f98f84c09612824c2975811a06bfa754d8426049 else
  0x20601438102008b2c3906f0d8b90372e30e2778e01be0e4790d80710e01bcf486e0da1b1559010ce19c3305c0c819032864834198308600be184c38630c4acd632e5)) else (if i < 14 then (if i < 13 then
  0x1ae2e04e80716e2404788d116228460891022003f87c0f61e43e87a0f01dc42835664344650840eccc4680bb1060185889c1041d99d8fb1b8b7d6b2ca5ceb257306d else
  0x14a28e1e8a6782291dfbb1760ebdd710475a2c05a8b31642bc570ad158158538b61542a4530a514828c4d09812e2584a0931322544909113e1199b0d81922783b335) else (if i < 15 then
  0x1e4e85d03db73cf61cd8ef1dc3084b095128244498c00f81ec3d0770f2f69c1bd87003945f3c26fcf01bd8e017afc2213701ee2344608988222dec88a87cd907b0a7 else
  0x10e218438c21342644b89213033c0700d01402006417803059ff8e119a1d43a07484507a1a3fd1d82c0568ac8622be158ae0e61cc008f71eceb1d5bc4752f01d30f3)))) else (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then
  0x1862e45409b1ae2e05401389111c510d5174284508a0140300408800fe1f43c0cf0240440800b013062064168143a0738c11782383f0d017623807c4688a33044088 else
  0x16a314620b51681ac688c313e360608851b03445f89e10835c680161ae3386189d02a358680c11060501a8461d8344650b1138360648b11050a61442d85832c558ab) else (if i < 19 then
  0x8743d21cc371e30d8740e716617a19c2e1d7130728be11e0fa25bf21f50d8708cd164176194261d5128700bd15213624bf11f236c6a0da19034c638d916e3485b0c6 else
  0x2404548e91c05a370f211f3d2478838dc22ef608d11864a370850dc226f008b11463e3706e3d221e3706e0dc206408808310e7128798f215413a260ef1dc2401fc3c)) else (if i < 22 then (if i < 21 then
  0x2625049c9342565009e93b26e4d86e13c1ae0649c13c1a00620d13b05cf689c3c226eefc809352684c09792e258371e012d2544a49412602e371ec1272464848c922 else
  0x2c65884f95b2aa550ac153294568a91592ae4ac0d03b2ac538a78dc2a25346c15082e558a894c182f6ca83c529eefca694c10a524a41461b9058a394227e4f89d135) else (if i < 23 then
  0x306614c117230c604ae184300370bc17c2f65f8bc86b2fa5e8b796b2d45b8b49712ce528b816d262130b61642ca370b31682c63460c16c2d058861bdd2ccf10b2bbf else
  0xf46583caf4318aad3e995686778e39d7362630c498a36a684c898b0ecd3d7aab3556851778750e8d6577aaf69ed5177ab96a6d49a8af16a0bc1a7aef69cba039873))) else (if i < 28 then (if i < 26 then (if i < 25 then
  0x32449999af06ba644c698b108640c78830360d4c888231c534408800fe1e03698f0fcd717b07d328659ada964f6bb155a746b4b454c98a31c5303e1923121ec3b86c else
  0x1266257c999556a70d33473bc735559fe69ebdd6319c3342399a207336664468890dc2310488b410228eb999578220cc19752c9ad4ca0f69e21d5c88632c6509a193) else (if i < 27 then
  0x5e2d61abaf8342674c589e34067c4e81d08c6844e19f13669dab2c3552678b189a1322604b8920e06940e2ea5569c5aaada554678b109612a688c50941221bcd39a3 else
  0x368accd98593101602b0571566c8d71ad26c6ac540a73f02999c1f5358630528a30e27d8d68a4560abc510a13526a154a6c5547f5a78a034e694d193534868896337)) else (if i < 30 then (if i < 29 then
  0x35443c6e1cb392728e40381b8714e19c43841246e10d1b8d3d9e0dc3826f0dc1803766dcb21ba36c538da8b13782c1341bb15e99cdd0ae672998dc8ad1581c80f2c6 else
  0x21241c838fd20c4147e0dc1b8370f41e669a2dcf28403ce3705b9e33c27802834c16c7886e0b63b4774ee1db0bed285a8dc16a5e0ea1d33ac744351d53a42d035910) else (if i < 31 then
  0x5fa7b1b135f5f87adf53d277eefddfbbf772ee1db1982060ccd4902064704d41973386c8f49e43bc61cb915c29450c809312004ac7f9122224408690d218428850fe else (if i < 32 then
  0x5707b9c3aff4647b5dfbbe56eef566bbc516eed663ba4dce2d22386462db9b1bb9770ed9dfbb6770ed1dcbb5766edd879ea61c7ad869ec766c2dd935e6047a9b6b60 else
  0x3fc7fcff3d44007fde99fe6d27f8ff1fe7a47f9e7b0a576aacff3ce3ecf35539fb7967c9e51f17927c1e438c3f0e2129a333f2e092c9fa6deda1e3b0b5727b9e3309)))))) else (if i < 50 then (if i < 41 then (if i < 37 then (if i < 35 then (if i < 34 then
  0x408e3580245406f49d9bd2766f5deabd63e6780289ef3a25e4fc1f22ca7dcf714f3ec7c4d69378807d4f81ac25a7d1b31ab172d94d58b887e7f8f59fe6d67bdb5361 else
  0x4288510b3ec428dd10a214428fad862157d4851f42127ce845f32107c6c1955a8d428f89043e1528835f038e60294d2320b712825bea59418f7d85aaf408f7982a8c) else (if i < 36 then
  0x432fcd57a187e8ae50bbef7dafb9f52133ca105029d22f482902166424824a82114104e22221040e66c9380040c7b1b919a178dc4cd0bb8868510a37640add50b36c else
  0x2a263860214412e29142244465197f19d31a2fdc2a22616880f32147d4e11f538157887d0e9e13fcf49bfbd26f8ac10e3bf772de5d9b777d4864e997b3fc851fb3f5)) else (if i < 39 then (if i < 38 then
  0x44a54d20a3e3464e920a3d3444b8e104a4786dcff1f833e30d022032d06786138f4788b8c0a2a44a59d169524588a49ca2b452648940283900e5141b63dc7b4c78c1 else
  0x5289a5f539c5a8b41e93bf770e65d9b974be979179553923212e25b4865ace18c73b49612ba560c0e48633f672660d28a432d4949179544a06e062a403048fcb4a42) else (if i < 40 then
  0x4c447017a634c09752c97f4865c91795c2860b9f52e4256f49719310d21a1fb2637d4988f11fe7a4ea9d42a74d4f49d3ade5b2efddb3a4766e89309e7428fa9cfb9d else
  0x7f66d464c304dafe936a6f4da9ba1526d7f29b537a6d4dd06936c104cf03d79aab4db015344045e4aad369ea832c2d77a6481cc2177264806c1176a648349848e830))) else (if i < 45 then (if i < 43 then (if i < 42 then
  0x848bbd75c1a40a754bea6d3fd0860fab94e108177ae983b06e0d41c4ac76c30a503786110c9d42f89a11e1bb2d899d141ba2ad0d53322237251d32a64276ff0da8ca else
  0x2aea049ea80452658948244c87c4d70d00424f0678204288213e23d3484bd819a019c07d85a573b89b60d40283500159a7a4ea8960d1ef3ac5f936a1484b08d57a73) else (if i < 44 then
  0x530a5d4213f1a8971452402de714699e343a7cc294071a50960425b4a26151f96e5128a8ac2894465214427d27c71025a6d4d07c8d08d1408a0d3ea3e34a5b541229 else
  0x5008acc992a04ac2d839901ac0892c1dd4db06a06c1a816b19612144261090921153283d3020e5288352ca0c4a682d452434148e517a0950882210a064f29e17a27d)) else (if i < 47 then (if i < 46 then
  0x1b47a1104218270486ca5e4a461944a422e28b4ad2894485254e282282098e503a4da99cf71911b0a5d442412e0a71161942b2a04a027c48269c982643fc7d86b823 else
  0x4d0a9151a6753ea113285b0b41653ba763fcaa8fea5d3f8a9cfda593f494cfca433f0a8d179f753e7da129f4534be54e2015368094c29f5065086da5f5468b8ad9cb) else (if i < 48 then
  0x20809d4ca9652861cbfa8a2e4580ae03b50850d552a954e61cbf972098a8cae29f2870696594a220434851071b83706e0dc0ce9b936aa94d8a5935aa74d4a5134a8a else (if i < 49 then
  0x294a814294353ea10a1a9e508980a1a9f4fe974a1a9d5087a4a1a9f4fc790a1a9f50894c99a9f50875c9929f4fa90cd3931538a11179962560a14e27d44a698ca924 else
  0x552a291d97250c90cf21725148e8ef17251490ceb9615468e0b02a446e57151a2f2b8a894ca2f2b8a8d4b2272b8a85179e92b8a8d131de2b8a8d179d7296a8d45225))))) else (if i < 58 then (if i < 54 then (if i < 52 then (if i < 51 then
  0x3bca9d2c9d9528964ec25330eaa52798752c938c3a4d3bc61ceb97f54e858e817f5287fce797f4de964e717f4a675cbba8a4985d948a4b2e4a2921972554a1d21972 else
  0x556a2d222a34605746eaaa532aa5302a85329814b25d554a552eaa952c969539e954ca64f4aa54c07a54a1e4554a4cf22924ba79153a943be964ef2a94aa7794b254) else (if i < 53 then
  0x1c8add55a31514928ba8e35669e8df0625669ece3ab3520924d9c271c2ac10e05355e9d10c2ab3fcac10f1c655e9cd0d1bd560a39243f71c0abd46a461beaad36aab else
  0x5a90e077aab3fc6bd66acc556b19611c00c6b19619cd58cb151b1b485e3a15e21f086ae538a175568515e221398ae53821b37eafd5e2355569b5fc0e5576ae519aab)) else (if i < 56 then (if i < 55 then
  0x61abf627b0e5f913955aab556be955aef5d6ba977aec5d26c579af25de3ee26ae85bcb688fad45a247955ade5b26c02a2d45a0111712e15bc13e1d8f35568516c2d7 else
  0x6e2ccda844d6a41cd9732c64acb595b1f556465f5324650aac8abd263cc898cb182e43718a3132b837188b1028637185b0b614c2d8330160ec0d7f1258a2c3d81450) else (if i < 57 then
  0x6b6d3da1b5a64ad59a7b476aac7d55b3b834d3888346680ceda2921232d09a033b6824808ab3e0530599eb3a0b30c2083fb22f0fde736566ed46154057f910c89be2 else
  0x6f4de22236066846212b756e6dc1fb36f7dedb9f536d880d7d9c114842da9fb3686ced91ebb637a4d8a0ebef7aeefddfbbf8a2d7a2836089ed7e2734f678c958faab))) else (if i < 62 then (if i < 60 then (if i < 59 then
  0x22a0a9de3b1716ef9d838677aeedd7b9a770e65d2bb6748ee9b18dc6dd075dd37a772de46e0dc1b83720d3b2754d85a0baa74ae8dcfb6c68ae7dcd398246e109137f else
  0x84af81c2442882f6598919056f45e63957a0e61c8349796f11c63cf786e21e73ca785101e73c9780e319b91679aecdcbb82754f21b39156df085e437f87d0f5e0b35) else (if i < 61 then
  0x236f69ce383898f61cdb80784e9dbf44a780e99bdbe97cae59f23a3722d21f1bdc71cfa1edb897cef89ed4447ccf89ec3896664681639f7c2ecdd137d7c0da08cb73 else
  0x80900a06b3b8690c615b3b66ccc9ff40d7f5009fcb6b6d4d0a06b766ead1a014356bcce99cbfe7fafd9c9b4a7b6e79c0bc4752df1d9ba873adddbfb69708dd1fab92)) else (if i < 64 then (if i < 63 then
  0x8a51a63445e4db06a12c0869901da2421826d360bc0b8030499fc188190021b416814ffe0a409728cfa08c066f0d2e0c40571f05e0838a86b05a0840570acf60ac0f else
  0x8ab15136a84515069f53d277eaad51a9f4868bcff1722b850c852b68cb18a3021453ea8e0d3ea7a4efd55a8a50890d17a142e4570a190755919230c5f3fd14e29453) else (if i < 65 then
  0x546a7d452844da0d01ec5a0791662c0458af15a2a9722e4570ae143286434398dc8cb192314698c31a22b4538b314a31c5b8b115633c578cd16a2dc5a8b31622bc56 else (if i < 66 then
  0xb219c6e110286570b92ab546a7d452844dac498ab1a8cf19921a2f4287fa0d3ea7a4efc39bbf7a4fa955aa353ea294226d4868bd0a1fe8ba7fa2dc5c4288bd21aab else 0x834fa9e93bf772ee1db463)))))))

private def edgeData14 (i : Nat) : Nat := unpack edgeData14Packed 11 48 i

private def st15Packed (i : Nat) : Nat :=
  (if i < 24 then (if i < 12 then (if i < 6 then (if i < 3 then (if i < 1 then
  0x16228fbfc49658429b0b1147e733fc49658429b8b1147dfe24b2c240429b8b1147dfe24b2c22dc29b80016228fbfc49658425b0b1147dfe3bc49658425b80016228fbfc49658423b0b1147dfe3be49658423b8b1147dfe24b2c240423b8b1147dfe24b2c227823b8c596228fbfc49658421380016228fbfc4965842130cb16228fbfc49658414b80016228fbfc49658414b00016228fbfc49658412b0b1147dfe3be49658412b8b1147dfe24b41458412b8b1147dfe24b2c226012b8cd96228fbfc4965840fb80016228fbfc4965840fb0d056228fbfc4965840ab80016228fbfc4965840ab0d156228fbfc49658409380016228fbfc4965840930
  else (if i < 2 then
  0xb1147dfe24b2c24384c38b1147dfe24b2c24044c38b1147dfe24b2c23104c38b1147dfe24b2c22dc4c38b1147dfe24b2c22784c380016228fbfc4965844bb0b1147dfe24b2c23104bb80016228fbfc49658449300016228fbfc4964ec4930b1147dfe24b2c24ec4938b1147dfe24b2c22784938b1147dfe24b2c226049380016228fbfc49658439b0b1147dfe3d149658439b8b1147dfe24b2c22dc39b8b1147dfe24b2c227839b80016228fbfc4965843830b1147dfe3d14965843838b1147dfe24b3825843838b1147dfe24b2c226038380016228fbfc49658436b0b1147dfe24b2c243836b8bed6228fbfc49658433b80016228fbfc49658433b0
  else
  0xcd96228fbfc4965844c38cb16228fbfc4965844c38c596228fbfc4965844c38bed6228fbfc4965844c38b736228fbfc4965844c38b676228fbfc4965844c38b5b6228fbfc4965844c38b115268fbfc4965844c38b115068fbfc4965844c38b1147e733fc4965844c38b1147e6dbfc4965844c38b1147e66bfc4965844c380016228fbd14965844c30b1147dfe3d14965844c380016228fbbe4965844c30b1147dfe3be4965844c38b1147dfe3bc4965844c38b1147dfe2734965844c38b1147dfe24b4465844c38b1147dfe24b4145844c38b1147dfe24b3825844c38b1147dfe24b2f05844c380016228fbfc4964ec4c30b1147dfe24b2c24ec4c38))
  else (if i < 4 then
  0xb676228fbfc4965844f38b4d6228fbfc4965844f38b115268fbfc4965844f38b114ee8fbfc4965844f38b1147e733fc4965844f38b1147e6dbfc4965844f38b1147e66bfc4965844f38b1147dfe3d14965844f38b1147dfe3be4965844f38b1147dfe3bc4965844f38b1147dfe2734965844f38b1147dfe26b4965844f38b1147dfe24b4465844f38b1147dfe24b4145844f38b1147dfe24b3825844f380016228fbfc4964ec4f30b1147dfe24b2c24ec4f38b1147dfe24b2c24384f38b1147dfe24b2c24044f38b1147dfe24b2c23104f38b1147dfe24b2c22dc4f380019b2c451f4965844c30d156228fbfc4965844c38d056228fbfc4965844c38
  else (if i < 5 then
  0x16228fbfc4964ec5bb0b1147dfe24b2c24ec5bb8b1147dfe24b2c24385bb8b1147dfe24b2c24045bb8b1147dfe24b2c23105bb80016228fbfc49658459b0b1147dfe24b38258459b80016228fbfc4964ec59b0b1147dfe24b2c24ec59b8b1147dfe24b2c22dc59b80016228fbfc4965845930b1147dfe24b2c23105938b676228fbfc49658455380016228fbfc49658455300016228fbfc4965845330b1147dfe27349658453380016228fccd7f892c4f30d156228fbfc4965844f38d056228fbfc4965844f38cd96228fbfc4965844f38cb16228fbfc4965844f38c596228fbfc4965844f38bed6228fbfc4965844f38b6f6228fbfc4965844f38
  else
  0xb1147dfe24b2c23105eb8001962c451f7f892c5bb0d156228fbfc4965845bb8d056228fbfc4965845bb8cd96228fbfc4965845bb8cb16228fbfc4965845bb8c596228fbfc4965845bb8bed6228fbfc4965845bb8bc96228fbfc4965845bb8b676228fbfc4965845bb8b2d6228fbfc4965845bb8b115268fbfc4965845bb8b1147e733fc4965845bb8b1147e6dbfc4965845bb8b1147e66bfc4965845bb8b1147e0c3fc4965845bb8b1147dfe3d14965845bb8b1147dfe3be4965845bb8b1147dfe3bc4965845bb8b1147dfe2734965845bb8b1147dfe26d4965845bb8b1147dfe24b4465845bb8b1147dfe24b4145845bb8b1147dfe24b3825845bb8)))
  else (if i < 9 then (if i < 7 then
  0xb676228fbfc49658462380016228fbfc4965846230b115268fbfc4965846238b114ea8fbfc4965846238b1147e733fc4965846238b1147e6dbfc4965846238b1147e66bfc4965846238b1147e0abfc4965846238b1147dfe3d14965846238b1147dfe3be4965846238b1147dfe3bc4965846238b1147dfe2734965846238b1147dfe2524965846238b1147dfe24b4465846238b1147dfe24b4145846238b1147dfe24b3825846238b1147dfe24b2ec58462380016228fbfc4964ec6230b1147dfe24b2c24ec6238b1147dfe24b2c24386238b1147dfe24b2c240462380016228fbfc4965845f30b1147dfe24b2c23105f380016228fbfc4965845eb0
  else (if i < 8 then
  0xb1147dfe26e49658480b8b1147dfe24b44658480b8b1147dfe24b41458480b8b1147dfe24b38258480b80016228fbfc4964ec80b0b1147dfe24b2c24ec80b8b1147dfe24b2c243880b80016228fbfc4965847e30b1147dfe24b4145847e380016228fbfc4964ec7e30b1147dfe24b2c24ec7e38b1147dfe24b2c24047e380016228fbfc4965847db0b1147dfe24b2c24387db80016228fbfc4965847ab0b115268fbfc4965847ab80016228fbfc4965846930b115268fbfc4965846938d156228fbfc4965846238d056228fbfc4965846238cd96228fbfc4965846238cb16228fbfc4965846238c596228fbfc4965846238bed6228fbfc4965846238
  else
  0xb1147dfe24b2c24ec87380016228fbfc4965848430b1147dfe24b2c243884380016228fbfc49658483b0b1147dfe24b2c243883b80018b2c451f7f892c80b0d156228fbfc49658480b8d056228fbfc49658480b8cd96228fbfc49658480b8cb16228fbfc49658480b8c596228fbfc49658480b8bed6228fbfc49658480b8bd36228fbfc49658480b8b676228fbfc49658480b8b115268fbfc49658480b8b114c68fbfc49658480b8b1147e733fc49658480b8b1147e6dbfc49658480b8b1147e66bfc49658480b8b1147e283fc49658480b8b1147dfe3d149658480b8b1147dfe3be49658480b8b1147dfe3bc49658480b8b1147dfe27349658480b8))
  else (if i < 10 then
  0xd156228fbfc4965848738d056228fbfc4965848738cd96228fbfc4965848738cb16228fbfc4965848738c596228fbfc4965848738bed6228fbfc4965848738b676228fbfc4965848738b396228fbfc49658487380016228fbfc4965848730b115268fbfc4965848738b1147e733fc4965848738b1147e6dbfc4965848738b1147e66bfc4965848738b1147e26bfc4965848738b1147dfe3d14965848738b1147dfe3be4965848738b1147dfe3bc4965848738b1147dfe2734965848738b1147dfe2554965848738b1147dfe24b4465848738b1147dfe24b4145848738b1147dfe24b3825848738b1147dfe24b2e058487380016228fbfc4964ec8730
  else (if i < 11 then
  0xc496228fbfc4965849db8bed6228fbfc4965849db8b676228fbfc4965849db8b115268fbfc4965849db8b1147e733fc4965849db8b1147e723fc4965849db8b1147e6dbfc4965849db8b1147e66bfc4965849db8b1147e623fc4965849db8b1147dfe3d14965849db8b1147dfe3be4965849db8b1147dfe3bc4965849db8b1147dfe2734965849db8b1147dfe24b4465849db8b1147dfe24b4145849db8b1147dfe24b3825849db80016228fbfc4965849bb0b1147e733fc4965849bb8bed6228fbfc49658498b80016228fbfc49658498b00016228fbfc4965849130b1147dfe24b4465849138b676228fbfc4965848f380016228fbfc4965848f30
  else
  0x193ac451f7f892c9db00018b2c451f7f892c9db0001892c451f7f892c9db00017dac451f7f892c9db00016cec451f7f892c9db0001622a4d1f7f892c9db00016228fce67f892c9db00016228fce47f892c9db00016228fcdb7f892c9db00016228fccd7f892c9db00016228fcc47f892c9db00016228fbfc7a292c9db00016228fbfc77c92c9db00016228fbfc77892c9db00016228fbfc4e692c9db00016228fbfc49688c9db00016228fbfc4968289db00016228fbfc4967049db0d156228fbfc4965849db8d056228fbfc4965849db8cd96228fbfc4965849db8cb16228fbfc4965849db8c9d6228fbfc4965849db8c596228fbfc4965849db8))))
  else (if i < 18 then (if i < 15 then (if i < 13 then
  0xb1147e6dbfc49660cb0b80016228fbfc4965f4b0b0b1147e66bfc4965f4b0b80016228fbfc4965e0b0b00016228fbfc4965d8b0b00016228fbfc4965c0b0b0001a2ac451f7f892cae30000002c451f7f892cae28d156228fbfc496584ae380016228fbfc496584ae30001a0ac451f7f892cacb0000002c451f7f892caca8d056228fbfc496584acb80016228fbfc496584acb00019b2c451f7f892cab30000002c451f7f892cab28cd96228fbfc496584ab380016228fbfc496584ab300016228fbfc496584a830b1147e66bfc496584a838001a2ac451f7f892c9db0001a0ac451f7f892c9db00019b2c451f7f892c9db0001962c451f7f892c9db0
  else (if i < 14 then
  0xbe36228fbfc496704b0b8b676228fbfc496704b0b8b115268fbfc496704b0b8b114fe8fbfc496704b0b8001622733fc496704b0b0b1147e733fc496704b0b8b1147e6dbfc496704b0b8b1147e66bfc496704b0b8b1147e23bfc496704b0b8001621fe3d1496704b0b0b1147dfe3d1496704b0b8b1147dfe3be496704b0b8b1147dfe3bc496704b0b8b1147dfe273496704b0b8b1147dfe266496704b0b8b1147dfe24b446704b0b8b1147dfe24b414704b0b80016228fbfc4966f8b0b0b1147dfe24b4466f8b0b80016228fbfc496610b0b0b1147e733fc496610b0b8b1147dfe24b414610b0b8b1147dfe24b382610b0b80016228fbfc49660cb0b0
  else
  0x147e733fc496828b0b0b1147e6dbfc496828b0b8b1147e66bfc496828b0b8b1147e08bfc496828b0b8b1147dfe3d1496828b0b8b1147dfe3be496828b0b800147dfe3be496828b0b0b1147dfe3bc496828b0b8b1147dfe273496828b0b8b1147dfe263496828b0b8b1147dfe24b446828b0b80016228fbfc496824b0b0b1147dfe24b446824b0b80016228fbfc496744b0b0b115268fbfc496744b0b80016228fbfc49672cb0b0b1147dfe27349672cb0b8001a0ac43fc496704b0b0d156228fbfc496704b0b8d056228fbfc496704b0b8cd96228fbfc496704b0b8cb16228fbfc496704b0b8c596228fbfc496704b0b8bed6228fbfc496704b0b8))
  else (if i < 16 then
  0xb1147dfe3d149688cb0b8b1147dfe3be49688cb0b8b1147dfe3bc49688cb0b8b1147dfe27349688cb0b8b1147dfe26149688cb0b8b1147dfe25849688cb0b80016228fbfc496878b0b0b1147dfe24b446878b0b8b676228fbfc49686cb0b80016228fbfc49686cb0b00016228fbfc49684cb0b0b1147dfe27349684cb0b8001a2a8fbfc496828b0b0d156228fbfc496828b0b8d056228fbfc496828b0b8cd96228fbfc496828b0b8cb16228fbfc496828b0b8c596228fbfc496828b0b8bed6228fbfc496828b0b8bdd6228fbfc496828b0b8b676228fbfc496828b0b8b556228fbfc496828b0b8b115268fbfc496828b0b8b1147e733fc496828b0b8
  else (if i < 17 then
  0x16228fbfc496900b0b0b1147dfe3be496900b0b8cb16228fbfc4968f8b0b80016228fbfc4968f8b0b0c596228fbfc4968f0b0b80016228fbfc4968f0b0b0bed6228fbfc4968ccb0b80016228fbfc4968ccb0b00016228fbfc4968b8b0b0b1147dfe3d14968b8b0b8d156228fbfc49688cb0b8d056228fbfc49688cb0b8cd96228fbfc49688cb0b8cb16228fbfc49688cb0b8c596228fbfc49688cb0b8bed6228fbfc49688cb0b8bd16228fbfc49688cb0b8b7b6228fbfc49688cb0b8b676228fbfc49688cb0b80016228fbfc49688cb0b0b115268fbfc49688cb0b8b1147e733fc49688cb0b8b1147e6dbfc49688cb0b8b1147e66bfc49688cb0b8
  else
  0xd156228fbfc4e692cb0b8d056228fbfc4e692cb0b8cd96228fbfc4e692cb0b8cb16228fbfc4e692cb0b8c596228fbfc4e692cb0b8bed6228fbfc4e692cb0b8b676228fbfc4e692cb0b8b115268fbfc4e692cb0b8b1147e733fc4e692cb0b8b1147e6dbfc4e692cb0b8b1147e66bfc4e692cb0b8b1147dfe3d14e692cb0b8b1147dfe3be4e692cb0b8b1147dfe3bc4e692cb0b8b1147dfe3a74e692cb0b80016228fbfc4dc92cb0b00016228fbfc4da92cb0b00016228fbfc4d692cb0b00016228fbfc4cc92cb0b00016228fbfc4c692cb0b00016228fbfc4c292cb0b00016228fbfc4b092cb0b00016228fbfc4aa92cb0b00016228fbfc4a492cb0b0)))
  else (if i < 21 then (if i < 19 then
  0xb114a28fbfc77892cb0b8b1147e733fc77892cb0b8b1147e6dbfc77892cb0b8b1147e66bfc77892cb0b8b1147e55bfc77892cb0b8b1147e013fc77892cb0b8b1147dfe3d177892cb0b8b1147dfe3be77892cb0b80016228fbfc76e92cb0b0b1147dfe3bc76e92cb0b80016228fbfc76c92cb0b0b1147dfe3bc76c92cb0b80016228fbfc76892cb0b0b1147dfe3bc76892cb0b80016228fbfc76092cb0b0b1147e733fc76092cb0b8b1147dfe3d176092cb0b8b1147dfe3be76092cb0b80016228fbfc75e92cb0b0b1147e6dbfc75e92cb0b80016228fbfc74e92cb0b0d7f6228fbfc4e692cb0b8d7d6228fbfc4e692cb0b8d796228fbfc4e692cb0b8
  else (if i < 20 then
  0xd056228fbfc77c92cb0b8cd96228fbfc77c92cb0b8cc76228fbfc77c92cb0b8cb16228fbfc77c92cb0b8c596228fbfc77c92cb0b8bed6228fbfc77c92cb0b8b676228fbfc77c92cb0b8b115268fbfc77c92cb0b8b114be8fbfc77c92cb0b8b1147e733fc77c92cb0b8b1147e6dbfc77c92cb0b8b1147e66bfc77c92cb0b8b1147e593fc77c92cb0b8b1147dfe3d177c92cb0b8d156228fbfc77892cb0b8d056228fbfc77892cb0b8cd96228fbfc77892cb0b8cb16228fbfc77892cb0b8c596228fbfc77892cb0b8bed6228fbfc77892cb0b8b676228fbfc77892cb0b8b216228fbfc77892cb0b80016228fbfc77892cb0b0b115268fbfc77892cb0b8
  else
  0x16228fbfc7c292cb0b0bed6228fbfc7b292cb0b80016228fbfc7b292cb0b0000002c45497a292cb0a8001622a4d1f7a292cb0b0001622a4bfc7a292cb0b0d156228fbfc7a292cb0b8d056228fbfc7a292cb0b8cd96228fbfc7a292cb0b8cc56228fbfc7a292cb0b8cb16228fbfc7a292cb0b8c596228fbfc7a292cb0b8bed6228fbfc7a292cb0b8b676228fbfc7a292cb0b8b476228fbfc7a292cb0b8b115268fbfc7a292cb0b8b1147e733fc7a292cb0b8b1147e6dbfc7a292cb0b8b1147e66bfc7a292cb0b8b1147e5ebfc7a292cb0b8000002d9d1f77c92cb0a80016cec451f77c92cb0b00016ce8fbfc77c92cb0b0d156228fbfc77c92cb0b8))
  else (if i < 22 then
  0x16228fcb27f892cb0b00016228fcab7f892cb0b00016228fc507f892cb0b00016228fc4d7f892cb0b00016228fc477f892cb0b00016228fc447f892cb0b0b1147e66c447f892cb0b80016228fc187f892cb0b00016228fc157f892cb0b00016228fc117f892cb0b00016228fc0e7f892cb0b0b1147e66c0e7f892cb0b80016228fc027f892cb0b0001a2ac451f7de92cb0b0000002c451f7de92cb0a8d156228fbfc7de92cb0b80016228fbfc7de92cb0b0001a0ac451f7d292cb0b0000002c451f7d292cb0a8d056228fbfc7d292cb0b80016228fbfc7d292cb0b0cb16228fbfc7c892cb0b80016228fbfc7c892cb0b0c596228fbfc7c292cb0b8
  else (if i < 23 then
  0x16228fcdb7f892cb0b0b115268fcdb7f892cb0b8b114ba8fcdb7f892cb0b8b1147e7ecdb7f892cb0b8b1147e734db7f892cb0b80016228fcd47f892cb0b0b1147e6dcd47f892cb0b80016228fcd37f892cb0b0b1147e6dcd37f892cb0b8d7f6228fccd7f892cb0b8d6d6228fccd7f892cb0b8d5f6228fccd7f892cb0b8d156228fccd7f892cb0b8d056228fccd7f892cb0b8cd96228fccd7f892cb0b8cb16228fccd7f892cb0b8c596228fccd7f892cb0b8bed6228fccd7f892cb0b8b676228fccd7f892cb0b8b115268fccd7f892cb0b8b1147e734cd7f892cb0b8b1147e6dccd7f892cb0b80016228fcc47f892cb0b00016228fcbd7f892cb0b0
  else
  0x2fb4e67f892cb0a80017dac44e67f892cb0b00017da8fce67f892cb0b0d156228fce67f892cb0b8d056228fce67f892cb0b8ced6228fce67f892cb0b8cd96228fce67f892cb0b8cb16228fce67f892cb0b8c596228fce67f892cb0b8c376228fce67f892cb0b8bed6228fce67f892cb0b8b676228fce67f892cb0b8b115268fce67f892cb0b8b1147e814e67f892cb0b80016228fce47f892cb0b0d156228fcdb7f892cb0b8d056228fcdb7f892cb0b8cd96228fcdb7f892cb0b8cb16228fcdb7f892cb0b8c596228fcdb7f892cb0b8c236228fcdb7f892cb0b8bed6228fcdb7f892cb0b8b676228fcdb7f892cb0b8b296228fcdb7f892cb0b8)))))
  else (if i < 36 then (if i < 30 then (if i < 27 then (if i < 25 then
  0x1622a0d1f7f892cb0b00016229fd1f7f892cb0b00016229dd1f7f892cb0b00016229d51f7f892cb0b000162298d1f7f892cb0b000162297d1f7f892cb0b00016229751f7f892cb0b00016229451f7f892cb0b0001a2ac45177f892cb0b0000002c45177f892cb0a8d156228fd177f892cb0b80016228fd177f892cb0b00019b2c45137f892cb0b0000002c45137f892cb0a8cd96228fd137f892cb0b80016228fd137f892cb0b0c596228fd0f7f892cb0b80016228fd0f7f892cb0b00016228fd027f892cb0b00016228fcfd7f892cb0b0b676228fcf87f892cb0b80016228fcf87f892cb0b00016228fcee7f892cb0b0b115268fcee7f892cb0b8
  else (if i < 26 then
  0x1672c451f7f892cb0b000165ac451f7f892cb0b0001652c451f7f892cb0b0001642c451f7f892cb0b0000002c451f7f892cb0a8001a0ac051f7f892cb0b0d05622c051f7f892cb0b8001622c051f7f892cb0b0000002c051f7f892cb0a80019b2be51f7f892cb0b0cd9622be51f7f892cb0b8001622be51f7f892cb0b0000002be51f7f892cb0a8cb1622bbd1f7f892cb0b8001622bbd1f7f892cb0b0d6d622a4d1f7f892cb0b8d2f622a4d1f7f892cb0b8d15622a4d1f7f892cb0b8d05622a4d1f7f892cb0b8cd9622a4d1f7f892cb0b8cb1622a4d1f7f892cb0b8c59622a4d1f7f892cb0b8bed622a4d1f7f892cb0b8b67622a4d1f7f892cb0b8
  else
  0xd057dac451f7f892cb0b8cd97dac451f7f892cb0b8cb17dac451f7f892cb0b8c597dac451f7f892cb0b80017c6c451f7f892cb0b00017bac451f7f892cb0b00017a6c451f7f892cb0b00017a2c451f7f892cb0b0001792c451f7f892cb0b00016f6c451f7f892cb0b00016e6c451f7f892cb0b00016dec451f7f892cb0b0d5f6cec451f7f892cb0b8d2f6cec451f7f892cb0b8d156cec451f7f892cb0b8d056cec451f7f892cb0b8cd96cec451f7f892cb0b8cb16cec451f7f892cb0b8c596cec451f7f892cb0b8bed6cec451f7f892cb0b80016b6c451f7f892cb0b00016aac451f7f892cb0b000169ac451f7f892cb0b000168ec451f7f892cb0b0))
  else (if i < 28 then
  0xd059b2c451f7f892cb0b800198ec451f7f892cb0b000198ac451f7f892cb0b0d7d962c451f7f892cb0b8d6d962c451f7f892cb0b8d4b962c451f7f892cb0b8d15962c451f7f892cb0b8d05962c451f7f892cb0b8cd9962c451f7f892cb0b800193ac451f7f892cb0b0d798b2c451f7f892cb0b8d5f8b2c451f7f892cb0b8d4b8b2c451f7f892cb0b8d158b2c451f7f892cb0b8d058b2c451f7f892cb0b8cd98b2c451f7f892cb0b8cb18b2c451f7f892cb0b8001892c451f7f892cb0b000186ec451f7f892cb0b0001846c451f7f892cb0b0d4b7dac451f7f892cb0b8d417dac451f7f892cb0b8d2f7dac451f7f892cb0b8d157dac451f7f892cb0b8
  else (if i < 29 then
  0x1962c451f99aff125b00018b2c451f99aff125b0000002c451f97aff125a8000002c451f964ff125a8000002c451f956ff125a80016228fcbd7f8f4525b00016228fcb27f8ef925b00016228fcab7f8ef125b0001afec451f7f892cb0b0001afac451f7f892cb0b0001af2c451f7f892cb0b0001adac451f7f892cb0b0001abec451f7f892cb0b0001a96c451f7f892cb0b0001a82c451f7f892cb0b0001a5ec451f7f892cb0b0d79a2ac451f7f892cb0b8d41a2ac451f7f892cb0b8d7da0ac451f7f892cb0b8d41a0ac451f7f892cb0b8d15a0ac451f7f892cb0b80019dac451f7f892cb0b0d7f9b2c451f7f892cb0b8d159b2c451f7f892cb0b8
  else
  0x1621fe24b2c24384c3100147dfe24b2c23104c310016228fbfc4965844bb100147dfe24b2c23104bb10016228fbfc49658449310016228fbfc4964ec49310016228fbfc49658439b10016228fbfc49658438310016228fbfc49658436b1001621fe24b2c243836b10016228fbfc49658433b10016228fbfc49658429b10016228fbfc77858425b10016228fbfc49658425b10016228fbfc49658423b10016228fbfc49658421310016228fbfc49658414b10016228fbfc49658412b10016228fbfc4965840fb10016228fbfc4965840ab10016228fbfc496584093100196316588a3eff125b00000030dd88a3eff125a800186ec451f9ccff125b0)))
  else (if i < 33 then (if i < 31 then
  0x16228fbfc49658459b10016228fbfc4964ec59b10016228fbfc496584593100147dfe24b2c231059310016228fbfc49658455310016228fbfc49658453310016228fcdb7f892c4f310016228fccd7f892c4f310016228fbfc7785844f310016228fccd4965844f310016228fa4b4465844f310016228fbfc4964ec4f31001621fe24b2c24384f3100147dfe24b2c23104f310016228fcdb7f892c4c310019b2c451f7f85844c310016228fbfc7785844c310019b2c451f4965844c310016228fbd14965844c310016228fbbe4965844c310016228fa4b4465844c310016228fbfc4145844c310016228fbfc3825844c310016228fbfc4964ec4c31
  else (if i < 32 then
  0x28fa4b446584622900147dfe24b446584623100147dfe24b414584623100147dfe24b382584623100147dfe24b2ec58462310016228fbfc4964ec62310000028fbfc4964ec622900147dfe24b2c24ec6231001621fe24b2c2438623100147dfe24b2c24386231000001fe24b2c2438622900147dfe24b2c240462310016228fbfc4965845f3100147dfe24b2c23105f310016228fbfc4965845eb100147dfe24b2c23105eb1001962c451f7f892c5bb10016228fcdb7f892c5bb10016228fbfc7785845bb1001962c43fc4965845bb10016228fa4b4465845bb10016228fbfc4964ec5bb1001621fe24b2c24385bb100147dfe24b2c23105bb1
  else
  0x16228fcdb7f892c62310000028fcdb7f892c62290016228fbfc77858462310000028fbfc7785846229001a2a8fbfc4965846231001a0a8fbfc49658462310019b28fbfc49658462310019628fbfc49658462310018b28fbfc49658462310017da8fbfc49658462310016ce8fbfc49658462310016228fbfc49658462310015268fbfc49658462310014ea8fbfc496584623100147e733fc496584623100147e6dbfc496584623100147e66bfc496584623100147e0abfc496584623100147dfe3d1496584623100147dfe3be496584623100147dfe3bc496584623100147dfe273496584623100147dfe25249658462310016228fa4b4465846231))
  else (if i < 34 then
  0x1621fe24b4465848731001621fe24b4145848731001621fe24b3825848731001621fe24b2e05848731000002c43fc4964ec87290016228fbfc4964ec8731001621fe24b2c24ec87310016228fbfc4965848431001621fe24b2c243884310016228fbfc49658483b1001621fe24b2c243883b10018b2c451f7f892c80b10016228fcdb7f892c80b10016228fbfc77858480b10018b28fbfc49658480b10016228fa4b44658480b10016228fbfc4964ec80b1001621fe24b2c243880b10016228fbfc4965847e310016228fbfc4964ec7e310016228fbfc4965847db1001621fe24b2c24387db10016228fbfc4965847ab10016228fbfc4965846931
  else (if i < 35 then
  0x16228fcdb7f892c8731000002c43fc77858487290016228fbfc7785848731001a2ac43fc4965848731001a0ac43fc49658487310019b2c43fc4965848731001962c43fc49658487310018b2c43fc49658487310017dac43fc49658487310016cec43fc4965848731001672c43fc4965848731001622a4bfc49658487310016228fbfc4965848731001622733fc49658487310016226dbfc496584873100162266bfc496584873100162226bfc4965848731001621fe3d14965848731001621fe3be4965848731001621fe3bc4965848731001621fe2734965848731001621fe2554965848731000002c424b44658487290016228fa4b4465848731
  else
  0x16cec451f7f892c9db1001622a4d1f7f892c9db10016228fce67f892c9db10016228fce47f892c9db10016228fcdb7f892c9db10016228fccd7f892c9db10016228fcc47f892c9db10016228fbfc7a292c9db10016228fbfc77c92c9db10016228fbfc77892c9db10016228fbfc4e692c9db1000002c451f49688c9da90016228fbfc49688c9db10016228fbfc4968289db10016228fbfc4967049db10016228fbfc7785849db10016228fbfc4e65849db10016228fa4b4465849db10016228fbfc4965849bb10016228fbfc49658498b10016228fbfc49658491310016228fa4b44658491310016228fbfc4965848f31000002c44db7f892c8729))))
  else (if i < 42 then (if i < 39 then (if i < 37 then
  0x16228fbfc49660cb0b10016228fbfc4965f4b0b10016228fbfc4965e0b0b10016228fbfc4965d8b0b10016228fbfc4965c0b0b1001a2ac451f7f892cae31000002c451f7f892cae290016228fbfc496584ae31001a0ac451f7f892cacb1000002c451f7f892caca90016228fbfc496584acb10019b2c451f7f892cab31000002c451f7f892cab290016228fbfc496584ab310016228fbfc496584a831000002c451f7f8ef09da9001a2ac451f7f892c9db1001a0ac451f7f892c9db10019b2c451f7f892c9db1001962c451f7f892c9db100193ac451f7f892c9db10018b2c451f7f892c9db1001892c451f7f892c9db10017dac451f7f892c9db1
  else (if i < 38 then
  0x2c451f7f886cb0a90016228fbfc49686cb0b10016228fbfc49684cb0b1001a2ac451f7f8828b0b10016228fbfc778828b0b1001a2a8fbfc496828b0b100147e733fc496828b0b100147dfe3be496828b0b10016228fa4b446828b0b10016228fbfc496824b0b10016228fa4b446824b0b1000002c451f7f8744b0a9001622a4d1f7f8744b0b10016228fbfc496744b0b10016228fbfc49672cb0b1001a0ac451f7f8704b0b10016228fbfc778704b0b1001a0ac43fc496704b0b1001622733fc496704b0b1001621fe3d1496704b0b10016228fa4b446704b0b10016228fbfc4966f8b0b10016228fa4b4466f8b0b10016228fbfc496610b0b1
  else
  0x16228fbfc77888cb0b1001a2ac451f49688cb0b1001a0ac451f49688cb0b10019b2c451f49688cb0b1001962c451f49688cb0b10018b2c451f49688cb0b10017dac451f49688cb0b10017a2c451f49688cb0b10016f6c451f49688cb0b10016cec451f49688cb0b1001622a4d1f49688cb0b10016228fce649688cb0b10016228fcdb49688cb0b10016228fccd49688cb0b10016228fbfc49688cb0b10016228fbd149688cb0b10016228fbbe49688cb0b10016228fbbc49688cb0b10016228fa7349688cb0b10016228fa6149688cb0b10016228fa5849688cb0b10016228fbfc496878b0b10016228fa4b446878b0b10016cec451f7f886cb0b1))
  else (if i < 40 then
  0x16cec451f77c92cb0b10016ce8fbfc77c92cb0b10016228fbfc77892cb0b10016228fbfc76e92cb0b10016228fbfc76c92cb0b10016228fbfc76892cb0b10016228fbfc76092cb0b10016228fbfc75e92cb0b10016228fbfc74e92cb0b10016228fbfc4dc92cb0b10016228fbfc4da92cb0b10016228fbfc4d692cb0b10016228fbfc4cc92cb0b10016228fbfc4c692cb0b10016228fbfc4c292cb0b10016228fbfc4b092cb0b10016228fbfc4aa92cb0b10016228fbfc4a492cb0b10016228fbfc496900b0b10016228fbfc4968f8b0b10016228fbfc4968f0b0b10016228fbfc4968ccb0b10016228fbfc4968b8b0b1000002c451f77888cb0a9
  else (if i < 41 then
  0x16228fcb27f892cb0b10016228fcab7f892cb0b10016228fc507f892cb0b10016228fc4d7f892cb0b10016228fc477f892cb0b10016228fc447f892cb0b10016228fc187f892cb0b10016228fc157f892cb0b10016228fc117f892cb0b10016228fc0e7f892cb0b10016228fc027f892cb0b1001a2ac451f7de92cb0b1000002c451f7de92cb0a90016228fbfc7de92cb0b1001a0ac451f7d292cb0b1000002c451f7d292cb0a90016228fbfc7d292cb0b10016228fbfc7c892cb0b10016228fbfc7c292cb0b10016228fbfc7b292cb0b1000002c45497a292cb0a9001622a4d1f7a292cb0b1001622a4bfc7a292cb0b1000002d9d1f77c92cb0a9
  else
  0x162298d1f7f892cb0b100162297d1f7f892cb0b10016229751f7f892cb0b10016229451f7f892cb0b1001a2ac45177f892cb0b1000002c45177f892cb0a90016228fd177f892cb0b10019b2c45137f892cb0b1000002c45137f892cb0a90016228fd137f892cb0b10016228fd0f7f892cb0b10016228fd027f892cb0b10016228fcfd7f892cb0b10016228fcf87f892cb0b10016228fcee7f892cb0b1000002fb4e67f892cb0a90017dac44e67f892cb0b10017da8fce67f892cb0b10016228fce47f892cb0b10016228fcdb7f892cb0b10016228fcd47f892cb0b10016228fcd37f892cb0b10016228fcc47f892cb0b10016228fcbd7f892cb0b1)))
  else (if i < 45 then (if i < 43 then
  0x1792c451f7f892cb0b10016f6c451f7f892cb0b10016e6c451f7f892cb0b10016dec451f7f892cb0b10016b6c451f7f892cb0b10016aac451f7f892cb0b100169ac451f7f892cb0b100168ec451f7f892cb0b1001672c451f7f892cb0b100165ac451f7f892cb0b1001652c451f7f892cb0b1001642c451f7f892cb0b1000002c451f7f892cb0a9001a0ac051f7f892cb0b1001622c051f7f892cb0b1000002c051f7f892cb0a90019b2be51f7f892cb0b1001622be51f7f892cb0b1000002be51f7f892cb0a9001622bbd1f7f892cb0b1001622a0d1f7f892cb0b10016229fd1f7f892cb0b10016229dd1f7f892cb0b10016229d51f7f892cb0b1
  else (if i < 44 then
  0x16228fbfc77cef0b0b10016228fbfc778edcb0b10016228fbfc778ed8b0b10016228fbfc778ed0b0b10016228fbfc7789ccb0b1001afec451f7f892cb0b1001afac451f7f892cb0b1001af2c451f7f892cb0b1001adac451f7f892cb0b1001abec451f7f892cb0b1001a96c451f7f892cb0b1001a82c451f7f892cb0b1001a5ec451f7f892cb0b10019dac451f7f892cb0b100198ec451f7f892cb0b100198ac451f7f892cb0b100193ac451f7f892cb0b1001892c451f7f892cb0b100186ec451f7f892cb0b1001846c451f7f892cb0b10017c6c451f7f892cb0b10017bac451f7f892cb0b10017a6c451f7f892cb0b10017a2c451f7f892cb0b1
  else
  0x16228fcdb7f8ebd25b10016228fcdb7f89cd25b1000002c451f9b692d11a90016228fcdb7f892d11b10016228fcdb7f892d05310016228fcdb7f892ce0b1000002c451f7f892cc1a90016228fcdb7f892cc1b1001a2ac451f7f8ef0b0b1001a0ac451f7f8ef0b0b10019b2c451f7f8ef0b0b1001962c451f7f8ef0b0b10018b2c451f7f8ef0b0b10017dac451f7f8ef0b0b10016cec451f7f8ef0b0b1001642c451f7f8ef0b0b1001622a4d1f7f8ef0b0b10016229451f7f8ef0b0b10016228fce67f8ef0b0b10016228fcdb7f8ef0b0b10016228fccd7f8ef0b0b10016228fcab7f8ef0b0b10016228fc027f8ef0b0b10016228fbfc7a2ef0b0b1))
  else (if i < 46 then
  0x1962c451f9b6ff125b10018b2c451f9b6ff125b1001846c451f9b6ff125b10017dac451f9b6ff125b10016cec451f9b6ff125b1001652c451f9b6ff125b1001622a4d1f9b6ff125b10016229751f9b6ff125b10016228fcfd9b6ff125b10016228fce69b6ff125b10016228fcdb9a8ff125b10016228fcdb9a6ff125b1001962c451f99aff125b10018b2c451f99aff125b10016228fcdb99aff125b1000002c451f97aff125a9000002c451f964ff125a9000002c451f956ff125a90016228fcdb7f8f4525b10016228fcbd7f8f4525b10016228fcdb7f8ef925b10016228fcb27f8ef925b10016228fcdb7f8ef125b10016228fcab7f8ef125b1
  else (if i < 47 then
  0x2c451f7f8744b0aa000002c451f7f892cae2a000002c451f7f892cacaa000002c451f7f892cab2a000002c451f7f8ef09daa000002c451f49688c9daa000002c44db7f892c872a000002c43fc778584872a000002c424b446584872a000002c43fc4964ec872a0000028fcdb7f892c622a0000028fbfc778584622a0000028fa4b446584622a0000028fbfc4964ec622a000001fe24b2c2438622a000002c451f9b6ff1de29000002c451f956ff1de2900196316588a3eff125b10000030dd88a3eff125a900186ec451f9ccff125b1000002c451f9c8ff125a9001a2ac451f9b6ff125b1001a0ac451f9b6ff125b10019b2c451f9b6ff125b1
  else
  0x2c451f9b6ff1de2a000002c451f956ff1de2a0000030dd88a3eff125aa000002c451f9c8ff125aa000002c451f97aff125aa000002c451f964ff125aa000002c451f956ff125aa000002c451f9b692d11aa000002c451f7f892cc1aa000002c451f7f892cb0aa000002c051f7f892cb0aa000002be51f7f892cb0aa000002c45177f892cb0aa000002c45137f892cb0aa000002fb4e67f892cb0aa000002c451f7de92cb0aa000002c451f7d292cb0aa000002c45497a292cb0aa000002d9d1f77c92cb0aa000002c451f77888cb0aa000002c451f7f886cb0aa))))))

private def st15 (i : Nat) : Nat := unpack st15Packed 84 24 i

private def adj15Packed (i : Nat) : Nat := (if i < 4 then (if i < 2 then (if i < 1 then 0x104010018304f0021840400c220d0830000080420010c61c90000430d9341041082002 else 0xc51440020501001400101800000000000c00460423c20c000618d080001280001007040) else (if i < 3 then 0x52c008224b0c60000470090c01ce14008208408228208232100138c00010a001181 else 0xc01401460c60011470030812842000080001033c02060820001400000003800c10830c1)) else (if i < 6 then (if i < 5 then 0x3cc1412000413401800810001c000100f0c300000000a1862c00022410821000060c2005 else 0x4100528014000000700004014d0030400840c31011c130024b340405040083000040040) else (if i < 7 then 0x10820800070800850420840824c218014004c48100000000124a0000c00041000420c2 else (if i < 8 then 0x400020c21841000421400910463440c200904000700c0000031000000420400020440c0 else 0x13080000))))

private def adj15 (i : Nat) : Nat := unpack adj15Packed 6 48 i

private def loc15Packed (i : Nat) : Nat :=
  (if i < 36 then (if i < 18 then (if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then 0x4d1098f91474a400000000000615953412e48b54a42f17c00000000000fdc00101 else 0x46a000788008a105000000792419e2000548bd0003d37b303dd50c20008c84497f) else (if i <
  3 then 0x24c001adb611eb1d5fe800000000d79c7000766269057a214971b338dc0004d000 else 0x25c22c000006b437012b43001128003007be184aa26c5727295e80000045c00388)) else (if i < 6 then (if i < 5 then
  0xc6950f780051c591aac395ef18a2d13c000001a6800000e940028b000fb8000fe else 0x923e171a16239ae2000001de8005a85448d0e407e0000022e3c4001681bc) else (if i < 7 then 0x2000022000000000354890d0690008d30ba33c220700017aafe2a432800000 else (if i < 8 then
  0x400008f9ff7640001b074000f617f93d708ca42f35143ac0473b4a66a0015b800 else 0xa0023585d1e0259c600047918c001980000015a15f000000003455260020c1ce)))) else (if i < 13 then (if i < 11 then (if i < 10 then
  0x9f8b18850000015d0004b4034c144100004000135408000002f14cea10c1974 else 0x8c3179b546f000b4c2d0004d2000003af4563b0000005d2ab229088640d9826800) else (if i < 12 then 0x862e500025c8e8c5df60008585ccc3bfc3d8744003a272c001ffa910005ad4a800 else
  0x7dc0000086c1edd5b4683a000000000007a4991f379e2eca62f94af1d956800)) else (if i < 15 then (if i < 14 then 0x429b6956294001be0003ae000840000004f847c06000472148ba7bc2c0701dc else 0x2c08a40209f0000018519a5023b944b7b00091c0c1e043709c0002f8d84a94f800)
  else (if i < 16 then 0x23d23e660809690000004505b8e36446ecb4000000001e3000000a0114437 else (if i < 17 then 0x16f30952e0000a1a937a759dd3d2350740000e8592000d00006469f049000 else 0x7ecacc958007f4001c883008a19400000064e08da0006e2000631aa8863cc5c19e)))))
  else (if i < 27 then (if i < 22 then (if i < 20 then (if i < 19 then 0x398000003ea000434e4000286000ca066000da12336e01cc710400049c00000262 else 0x3fc00000002000125fa9bf81a000c880014c0001644479030c0000040ea78001b9) else (if i < 21 then
  0x27b8e4000000aa55200023b900005392c8006ea1f8df1a73c29800038f else 0x1030298002de940000000000002f800400295eba0f68e6712280031f191eb000)) else (if i < 24 then (if i < 23 then 0x1911740001f7420f1030004b62740000000000165a253170fd5e10950a3152f125 else
  0x1000007daf33aa000748004684616aae7284c9800166000e74003b500000100b59) else (if i < 25 then 0x2e924bb34067cea4000008f0cf5a61ed604a88003b3618f74d1a3a00032cfb308 else (if i < 26 then 0x37400443ac23a4000003ed0000001a0000000000040a0007e80039884000174000
  else 0x688001d637a00026c8f2380002347b0001f873435800000cc40030d00000182900)))) else (if i < 31 then (if i < 29 then (if i < 28 then 0x22a0004ec00000896c6dd300053a871e739f74e86a19a5d0000021c016 else
  0x2900002b7f29318f12d3a9004120f90000004181d8610840031f43241000348) else (if i < 30 then 0x5dc24c000008e00011bb622220002517c000c180000039e5e48933c00033c00000 else 0x7869b8938000006c400000000000000f70000009ca660001de3b9e60f452dcdbcd)) else (if i < 33
  then (if i < 32 then 0x88c616f8e25144a076aed0010ec10800550000002c35b237a2a8002b27b800000 else 0x554f9c0022c5629440000087c2bc26410580000338002d894c20000000c1c00000) else (if i < 34 then 0x2424acce4258840001a50a8062a0f05b3b8733a9b53c1301d717c001c1
  else (if i < 35 then 0x3be6d4000000007ae369e7000888c7000524dd8002103d01900039e14705d3933f else 0x1c5a640000e4db0001b4a2000479000ddcd21de73242d4831200043e018bf)))))) else (if i < 54 then (if i < 45 then (if i < 40 then (if i < 38 then (if i < 37
  then 0xdac0d00021836dc32331aacec00076804dc00002d6a8fec0000072a08caec47 else 0x3e2518bd8004de002088000000002c8000001a00045c772bc0002b285000000000) else (if i < 39 then 0x1cae39820000007d20d8006a4000cd80062a6ac0000054d090a9800 else
  0x2260000024865a0000011600000050a1e13c18000425000000fc000000a08f2800)) else (if i < 42 then (if i < 41 then 0x1fa001f8b7d59a001d4226000534000000000009102788c0a4b700000034147a4d else
  0x26c04c0042d832cc9d1ace00000053aa50000022607c0000009c2396c0000bc30b) else (if i < 43 then 0x8460003f8128e3114003644ec00001aa78d04542820a2c2001632ca2cee721e270 else (if i < 44 then
  0x41aa58cfa3b0820000017748000193af86b002dc195548209800121000f1c00000 else 0x83f1f000000000002038000006e00f00069edb1431c6000a70000c70000015fa18)))) else (if i < 49 then (if i < 47 then (if i < 46 then
  0x8ccb0400261000204a202e000aac819f93f6145660005d60009b8a934a1192f8b2 else 0xaa0006b8008380020700062c4d03518c000de021000000001f4a054c62e4e98ab) else (if i < 48 then 0x359760e15f4000a093a0003e000000442000000006bca34e4b735c80005a000 else
  0x8b600121bf40000000000016cbf1f1b2400078d8cb4b00000000000000055ea800)) else (if i < 51 then (if i < 50 then 0x1144ba800000f81118000003355780006284cb6800104e5cc300047af91b7800 else 0x20a8003269a8000004e800037c32000001da00007c5c4e045600000000000)
  else (if i < 52 then 0x338003e50000013980077c0004880035c001059b000003c004121809adfc22f else (if i < 53 then 0x17b2c47d600202000050ef0d100041cda4ae1816b8ec40028c000b9400102 else
  0x182cbd6883b0e443977800280f413bbc5000255f11900002719288e0010a84c9ea))))) else (if i < 63 then (if i < 58 then (if i < 56 then (if i < 55 then 0x35a00188800114a6981a9b1300004b85c000d38000a829ef08d6000000fcd95800 else
  0x43e00227000000b5d43ada42c7740017d3fa0000000087a2b400000396d5d18000) else (if i < 57 then 0x75a230373f02206ce0984f000ec20489458e001878004e25a4000003eae0551800 else 0x8001c03c8b3620001e04053860016db3a17a0013eab0000ca01d21732e001502c5)) else (if i <
  60 then (if i < 59 then 0x63a001f7957000330a29200003bdd70d8748b994cbbb000cb0000005ba7c0d0800 else 0x1fe001ed800000ad9c980025e000000c482c000000004283c8961880ac9540018a) else (if i < 61 then
  0x34c0006e800000c85b192901279000000000000003f223314e0d1330011a80035f else (if i < 62 then 0x49e475e5000700f70003560007f0272241f46255aa315d4af8002bb0009953a800 else 0x8c00021d000000b3d7937f2b483113807000c68988005c03640000000000000000)))) else (if i
  < 68 then (if i < 65 then (if i < 64 then 0x5b8d740000000116400123000240c6854000000003537241885124a0002c400000 else 0x796a6000170000a85c50003010796c0000005240c9652b6bf40013f0863d01e962) else (if i < 66 then
  0xfa18a0008105617dc42000325870000f000068b723b502cb50000000010927a else (if i < 67 then 0x36e000d9448000b219b1db0010d53f800000000000e638a0dcbf00000000036be6 else 0x496e255c4498f65e80000020e0016b199000825ed07d8b02d40880000000038bb6))) else (if i < 70
  then (if i < 69 then 0x88015e27ae1684ee0000487fc000000a00001cc6f8ae7a89e40000032a06c00374 else 0x2200001d40023f000ce19706c001151bca11290000000ac00070843000) else (if i < 71 then 0x119406000308f30000330002f0002366a10ac00457000cd00039a000001df800
  else (if i < 72 then 0x70aedda48d42bc80c2d8d3000df8cb0ea50696000000626029b2b373880a9d0000 else 0x1d832446d5701c)))))))

private def loc15 (i : Nat) : Nat := unpack loc15Packed 11 24 i

private def st16Packed (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0xcd96228fbfc4965858658b1147dfe24b2c2c316588a3eff125961617dac451f7f892cb0b0b676228fbfc4965858588a9347dfe24b2c2c2c451f9ccff125961616228fcdb7f892cb0b0b1147e66bfc4965858588a3eff1e8a4b2c2c2c451f7f8ef925961616228fbfc77892cb0b0b1147dfe2734965858588a3eff125a232c2c2c451f7f892d05161616228fbfc496704b0b00016228fbfc4964ed4588a3eff125961276c2c451f7f892cb090e616228fbfc49658480b0b1147dfe24b2c23118588a3eff12596116ec2c451f7f892cb089e616228fbfc4965844c30 else 0xb115268fbfc4965858d88a3f399fe24b2c2c6c451f9b6ff125961636228fccd7f892cb0b1b1147dfe3d14965858d88a3eff1df24b2c2c6c451f7f8ef125961636228fbfc4e692cb0b10016228fa4b4465854d88a3eff125a232c2c6c451f7f892d05161636228fbfc496704b0b10016228fbfc4964ed4d88a3eff125961276c4005887f892cb090e536228fbfc4965848731b1147dfe24b2c24058d88a3eff125961188c40051f7f892cb08c4536228fbfc4965845bb1b1147dfe24b2c22798d88a3eff125961130c745588a3eff12596161a0ac451f7f892cb0b0) else (if i < 3 then 0xb1147dfe2734965859000b1147d25a232c2aac451f7f892d11961656228fbfc496828b0b2b1147dfe24b3825859000b1147dfe24b276aac451f7f892cb093b64002c43fc496584872ab1147dfe24b2c24399588a3eff125961202cac451f7f892cb08c4640028fbfc496584622ab1147dfe24b2c22dd9588a3eff12596113ccac451f7f892cb089864002c451f9b6ff125a90016228fbfc7785854e8ab1147dfe24b2c2c741588a3eff125961639b2c451f7f892cb0b1cb16228fbfc4965858e2cb1147dfe24b2c2c6fb588a3eff125961636cec451f7f892cb0b1 else 0x588a3f36dfe24b56002c451f7f8ef0b0ab0016228fa4b4465855800b1147dfe24b276ac005887f892cb090e560028fbfc496584622b0016228fcdb7f892d5000b1147dfe3bc2c2ab45588a3eff12596165a0ac451f7f892cb0b2cd96228fbfc4965859658b1147dfe24b2c2cb16588a3eff125961657dac451f7f892cb0b2b676228fbfc4965859588a9347dfe24b2c2cac451f9ccff125961656228fcdb7f892cb0b2b1147e66bfc4965859588a3eff1e8a4b2c2cac451f7f8ef925961656228fbfc77892cb0b2))

private def st16 (i : Nat) : Nat := unpack st16Packed 73 24 i

private def adj16Packed (i : Nat) : Nat := 0x312003180250101001113012000130022010

private def adj16 (i : Nat) : Nat := unpack adj16Packed 4 48 i

private def loc16Packed (i : Nat) : Nat := (if i < 3 then (if i < 1 then 0x3a0003836014ac56200000035a007200b80b000050 else (if i < 2 then 0xcd73a7f225d448092d516ec04664f803c2001080 else 0xbb34080001c04338000280019a8500016843288000)) else (if i < 5 then (if i < 4 then 0x7a700470002f5452380ae020b12730fd30600027 else 0x26100014801524580006e0220060da4db8b28011) else (if i < 6 then 0xad686001e600001400000340004f0001ea0009acd1 else 0x2e0e)))

private def loc16 (i : Nat) : Nat := unpack loc16Packed 7 24 i

private def st17Packed (i : Nat) : Nat := 0x2c451f7f892cb0acb1147dfe24b2c2aec451f7f892cb0aab1147dfe24b2c2a6c451f7f892cb0a8

private def st17 (i : Nat) : Nat := unpack st17Packed 62 24 i

private def adj17Packed (i : Nat) : Nat := 0x0

private def adj17 (i : Nat) : Nat := unpack adj17Packed 1 48 i

private def loc17Packed (i : Nat) : Nat := 0x8080604

private def loc17 (i : Nat) : Nat := unpack loc17Packed 3 24 i

private def dataCount : Nat → Nat
  | 3 => 74
  | 4 => 706
  | 5 => 2182
  | 6 => 1088
  | 7 => 90
  | 8 => 5
  | 11 => 12
  | 12 => 169
  | 13 => 1130
  | 14 => 2638
  | 15 => 1149
  | 16 => 94
  | 17 => 5
  | _ => 0

private def dataSizes : Nat → Nat × Nat
  | 5 => (733,3299)
  | 6 => (367,1637)
  | 7 => (31,137)
  | 8 => (3,11)
  | 14 => (881,3967)
  | 15 => (389,1733)
  | 16 => (37,149)
  | 17 => (3,11)
  | _ => (1,2)

private def stData : Nat → Nat → Nat
  | 3 => st3
  | 4 => st4
  | 5 => st5
  | 6 => st6
  | 7 => st7
  | 8 => st8
  | 11 => st11
  | 12 => st12
  | 13 => st13
  | 14 => st14
  | 15 => st15
  | 16 => st16
  | 17 => st17
  | _ => fun _ => 0

private def adjData : Nat → Nat → Nat
  | 5 => adj5
  | 6 => adj6
  | 7 => adj7
  | 8 => adj8
  | 14 => adj14
  | 15 => adj15
  | 16 => adj16
  | 17 => adj17
  | _ => fun _ => 0

private def locData : Nat → Nat → Nat
  | 5 => loc5
  | 6 => loc6
  | 7 => loc7
  | 8 => loc8
  | 14 => loc14
  | 15 => loc15
  | 16 => loc16
  | 17 => loc17
  | _ => fun _ => 0

private def edgeMetaTable : Nat → Nat → Nat
  | 4 => edgeMeta4
  | 5 => edgeMeta5
  | 12 => edgeMeta12
  | 13 => edgeMeta13
  | 14 => edgeMeta14
  | _ => fun _ => 0

private def edgeDataTable : Nat → Nat → Nat
  | 4 => edgeData4
  | 5 => edgeData5
  | 12 => edgeData12
  | 13 => edgeData13
  | 14 => edgeData14
  | _ => fun _ => 0

private def edgeWidth : Nat → Nat
  | 4 => 2
  | 5 => 3
  | 12 => 2
  | 13 => 3
  | 14 => 4
  | _ => 1

private def levelKey (b : Bool) (k : Nat) : Nat := if b then k+9 else k

private def certCount (b : Bool) (k : Nat) : Nat := dataCount (levelKey b k)

private def certState (b : Bool) (k i : Nat) : SearchState :=
  let x := stData (levelKey b k) i
  (x &&& 7, decodeWires (x >>> 7) ((x >>> 3) &&& 15))

private def edgeList (k i : Nat) : Nat → List Nat
  | 0 => []
  | n+1 => edgeDataTable k i :: edgeList k (i+1) n

private def certLocate (b : Bool) (k i : Nat) (x : SearchState) : List Nat :=
  if k<5 then
    let j := levelKey b (k+1)
    let info := edgeMetaTable j i
    let width := edgeWidth j
    edgeList j (info >>> width) (info &&& ((1 <<< width)-1))
  else
    let k' := levelKey b k
    let (d,n) := dataSizes k'
    let h := stateHash x
    let slot := (h / d + adjData k' (h % d) * (1 + (h / 1031) % (n - 1))) % n
    [locData k' slot]

private def checkCert (b : Bool) :=
  checkBatch (certCount b) (certState b) (certLocate b)


private lemma certLayer_0_0 : checkCert false 0 0 (certCount false 0) = true :=
  by rfl


private lemma certLayer_0_1 : checkCert false 1 0 (certCount false 1) = true :=
  by rfl


private lemma certLayer_0_2 : checkCert false 2 0 (certCount false 2) = true :=
  by rfl

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_0_3_0 : checkCert false 3 0 74 = true := by decide +kernel

private lemma certLayer_0_3 : checkCert false 3 0 (certCount false 3) = true :=
  cert_0_3_0

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_0_4_0 : checkCert false 4 0 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_0_4_120 : checkCert false 4 120 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_0_4_240 : checkCert false 4 240 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_0_4_360 : checkCert false 4 360 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_0_4_480 : checkCert false 4 480 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_0_4_600 : checkCert false 4 600 106 = true := by decide +kernel

private lemma certLayer_0_4 : checkCert false 4 0 (certCount false 4) = true :=
  (checkBatch_join (certCount false) (certState false) (certLocate false) 4 0 360 346
    (checkBatch_join (certCount false) (certState false) (certLocate false) 4 0 120 240
    cert_0_4_0 (checkBatch_join (certCount false) (certState false) (certLocate false) 4 120 120 120
    cert_0_4_120 cert_0_4_240)) (checkBatch_join (certCount false) (certState false) (certLocate false) 4 360 120 226
    cert_0_4_360 (checkBatch_join (certCount false) (certState false) (certLocate false) 4 480 120 106
    cert_0_4_480 cert_0_4_600)))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_0_5_0 : checkCert false 5 0 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_0_5_120 : checkCert false 5 120 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_0_5_240 : checkCert false 5 240 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_0_5_360 : checkCert false 5 360 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_0_5_480 : checkCert false 5 480 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_0_5_600 : checkCert false 5 600 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_0_5_720 : checkCert false 5 720 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_0_5_840 : checkCert false 5 840 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_0_5_960 : checkCert false 5 960 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_0_5_1080 : checkCert false 5 1080 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_0_5_1200 : checkCert false 5 1200 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_0_5_1320 : checkCert false 5 1320 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_0_5_1440 : checkCert false 5 1440 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_0_5_1560 : checkCert false 5 1560 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_0_5_1680 : checkCert false 5 1680 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_0_5_1800 : checkCert false 5 1800 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_0_5_1920 : checkCert false 5 1920 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_0_5_2040 : checkCert false 5 2040 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_0_5_2160 : checkCert false 5 2160 22 = true := by decide +kernel

private lemma certLayer_0_5 : checkCert false 5 0 (certCount false 5) = true :=
  (checkBatch_join (certCount false) (certState false) (certLocate false) 5 0 1080 1102
    (checkBatch_join (certCount false) (certState false) (certLocate false) 5 0 480 600
    (checkBatch_join (certCount false) (certState false) (certLocate false) 5 0 240 240
    (checkBatch_join (certCount false) (certState false) (certLocate false) 5 0 120 120
    cert_0_5_0 cert_0_5_120) (checkBatch_join (certCount false) (certState false) (certLocate false) 5 240 120 120
    cert_0_5_240 cert_0_5_360)) (checkBatch_join (certCount false) (certState false) (certLocate false) 5 480 240 360
    (checkBatch_join (certCount false) (certState false) (certLocate false) 5 480 120 120
    cert_0_5_480 cert_0_5_600) (checkBatch_join (certCount false) (certState false) (certLocate false) 5 720 120 240
    cert_0_5_720 (checkBatch_join (certCount false) (certState false) (certLocate false) 5 840 120 120
    cert_0_5_840 cert_0_5_960)))) (checkBatch_join (certCount false) (certState false) (certLocate false) 5 1080 600 502
    (checkBatch_join (certCount false) (certState false) (certLocate false) 5 1080 240 360
    (checkBatch_join (certCount false) (certState false) (certLocate false) 5 1080 120 120
    cert_0_5_1080 cert_0_5_1200) (checkBatch_join (certCount false) (certState false) (certLocate false) 5 1320 120 240
    cert_0_5_1320 (checkBatch_join (certCount false) (certState false) (certLocate false) 5 1440 120 120
    cert_0_5_1440 cert_0_5_1560))) (checkBatch_join (certCount false) (certState false) (certLocate false) 5 1680 240 262
    (checkBatch_join (certCount false) (certState false) (certLocate false) 5 1680 120 120
    cert_0_5_1680 cert_0_5_1800) (checkBatch_join (certCount false) (certState false) (certLocate false) 5 1920 120 142
    cert_0_5_1920 (checkBatch_join (certCount false) (certState false) (certLocate false) 5 2040 120 22
    cert_0_5_2040 cert_0_5_2160)))))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_0_6_0 : checkCert false 6 0 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_0_6_120 : checkCert false 6 120 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_0_6_240 : checkCert false 6 240 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_0_6_360 : checkCert false 6 360 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_0_6_480 : checkCert false 6 480 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_0_6_600 : checkCert false 6 600 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_0_6_720 : checkCert false 6 720 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_0_6_840 : checkCert false 6 840 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_0_6_960 : checkCert false 6 960 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_0_6_1080 : checkCert false 6 1080 8 = true := by decide +kernel

private lemma certLayer_0_6 : checkCert false 6 0 (certCount false 6) = true :=
  (checkBatch_join (certCount false) (certState false) (certLocate false) 6 0 600 488
    (checkBatch_join (certCount false) (certState false) (certLocate false) 6 0 240 360
    (checkBatch_join (certCount false) (certState false) (certLocate false) 6 0 120 120
    cert_0_6_0 cert_0_6_120) (checkBatch_join (certCount false) (certState false) (certLocate false) 6 240 120 240
    cert_0_6_240 (checkBatch_join (certCount false) (certState false) (certLocate false) 6 360 120 120
    cert_0_6_360 cert_0_6_480))) (checkBatch_join (certCount false) (certState false) (certLocate false) 6 600 240 248
    (checkBatch_join (certCount false) (certState false) (certLocate false) 6 600 120 120
    cert_0_6_600 cert_0_6_720) (checkBatch_join (certCount false) (certState false) (certLocate false) 6 840 120 128
    cert_0_6_840 (checkBatch_join (certCount false) (certState false) (certLocate false) 6 960 120 8
    cert_0_6_960 cert_0_6_1080))))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_0_7_0 : checkCert false 7 0 90 = true := by decide +kernel

private lemma certLayer_0_7 : checkCert false 7 0 (certCount false 7) = true :=
  cert_0_7_0

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_0_8_0 : checkCert false 8 0 5 = true := by decide +kernel

private lemma certLayer_0_8 : checkCert false 8 0 (certCount false 8) = true :=
  cert_0_8_0


private lemma certLayer_1_0 : checkCert true 0 0 (certCount true 0) = true :=
  by rfl


private lemma certLayer_1_1 : checkCert true 1 0 (certCount true 1) = true :=
  by rfl

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_1_2_0 : checkCert true 2 0 12 = true := by decide +kernel

private lemma certLayer_1_2 : checkCert true 2 0 (certCount true 2) = true :=
  cert_1_2_0

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_1_3_0 : checkCert true 3 0 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_1_3_120 : checkCert true 3 120 49 = true := by decide +kernel

private lemma certLayer_1_3 : checkCert true 3 0 (certCount true 3) = true :=
  (checkBatch_join (certCount true) (certState true) (certLocate true) 3 0 120 49
    cert_1_3_0 cert_1_3_120)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_1_4_0 : checkCert true 4 0 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_1_4_120 : checkCert true 4 120 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_1_4_240 : checkCert true 4 240 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_1_4_360 : checkCert true 4 360 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_1_4_480 : checkCert true 4 480 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_1_4_600 : checkCert true 4 600 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_1_4_720 : checkCert true 4 720 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_1_4_840 : checkCert true 4 840 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_1_4_960 : checkCert true 4 960 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_1_4_1080 : checkCert true 4 1080 50 = true := by decide +kernel

private lemma certLayer_1_4 : checkCert true 4 0 (certCount true 4) = true :=
  (checkBatch_join (certCount true) (certState true) (certLocate true) 4 0 600 530
    (checkBatch_join (certCount true) (certState true) (certLocate true) 4 0 240 360
    (checkBatch_join (certCount true) (certState true) (certLocate true) 4 0 120 120
    cert_1_4_0 cert_1_4_120) (checkBatch_join (certCount true) (certState true) (certLocate true) 4 240 120 240
    cert_1_4_240 (checkBatch_join (certCount true) (certState true) (certLocate true) 4 360 120 120
    cert_1_4_360 cert_1_4_480))) (checkBatch_join (certCount true) (certState true) (certLocate true) 4 600 240 290
    (checkBatch_join (certCount true) (certState true) (certLocate true) 4 600 120 120
    cert_1_4_600 cert_1_4_720) (checkBatch_join (certCount true) (certState true) (certLocate true) 4 840 120 170
    cert_1_4_840 (checkBatch_join (certCount true) (certState true) (certLocate true) 4 960 120 50
    cert_1_4_960 cert_1_4_1080))))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_1_5_0 : checkCert true 5 0 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_1_5_120 : checkCert true 5 120 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_1_5_240 : checkCert true 5 240 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_1_5_360 : checkCert true 5 360 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_1_5_480 : checkCert true 5 480 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_1_5_600 : checkCert true 5 600 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_1_5_720 : checkCert true 5 720 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_1_5_840 : checkCert true 5 840 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_1_5_960 : checkCert true 5 960 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_1_5_1080 : checkCert true 5 1080 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_1_5_1200 : checkCert true 5 1200 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_1_5_1320 : checkCert true 5 1320 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_1_5_1440 : checkCert true 5 1440 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_1_5_1560 : checkCert true 5 1560 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_1_5_1680 : checkCert true 5 1680 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_1_5_1800 : checkCert true 5 1800 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_1_5_1920 : checkCert true 5 1920 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_1_5_2040 : checkCert true 5 2040 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_1_5_2160 : checkCert true 5 2160 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_1_5_2280 : checkCert true 5 2280 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_1_5_2400 : checkCert true 5 2400 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_1_5_2520 : checkCert true 5 2520 118 = true := by decide +kernel

private lemma certLayer_1_5 : checkCert true 5 0 (certCount true 5) = true :=
  (checkBatch_join (certCount true) (certState true) (certLocate true) 5 0 1320 1318
    (checkBatch_join (certCount true) (certState true) (certLocate true) 5 0 600 720
    (checkBatch_join (certCount true) (certState true) (certLocate true) 5 0 240 360
    (checkBatch_join (certCount true) (certState true) (certLocate true) 5 0 120 120
    cert_1_5_0 cert_1_5_120) (checkBatch_join (certCount true) (certState true) (certLocate true) 5 240 120 240
    cert_1_5_240 (checkBatch_join (certCount true) (certState true) (certLocate true) 5 360 120 120
    cert_1_5_360 cert_1_5_480))) (checkBatch_join (certCount true) (certState true) (certLocate true) 5 600 360 360
    (checkBatch_join (certCount true) (certState true) (certLocate true) 5 600 120 240
    cert_1_5_600 (checkBatch_join (certCount true) (certState true) (certLocate true) 5 720 120 120
    cert_1_5_720 cert_1_5_840)) (checkBatch_join (certCount true) (certState true) (certLocate true) 5 960 120 240
    cert_1_5_960 (checkBatch_join (certCount true) (certState true) (certLocate true) 5 1080 120 120
    cert_1_5_1080 cert_1_5_1200)))) (checkBatch_join (certCount true) (certState true) (certLocate true) 5 1320 600 718
    (checkBatch_join (certCount true) (certState true) (certLocate true) 5 1320 240 360
    (checkBatch_join (certCount true) (certState true) (certLocate true) 5 1320 120 120
    cert_1_5_1320 cert_1_5_1440) (checkBatch_join (certCount true) (certState true) (certLocate true) 5 1560 120 240
    cert_1_5_1560 (checkBatch_join (certCount true) (certState true) (certLocate true) 5 1680 120 120
    cert_1_5_1680 cert_1_5_1800))) (checkBatch_join (certCount true) (certState true) (certLocate true) 5 1920 360 358
    (checkBatch_join (certCount true) (certState true) (certLocate true) 5 1920 120 240
    cert_1_5_1920 (checkBatch_join (certCount true) (certState true) (certLocate true) 5 2040 120 120
    cert_1_5_2040 cert_1_5_2160)) (checkBatch_join (certCount true) (certState true) (certLocate true) 5 2280 120 238
    cert_1_5_2280 (checkBatch_join (certCount true) (certState true) (certLocate true) 5 2400 120 118
    cert_1_5_2400 cert_1_5_2520)))))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_1_6_0 : checkCert true 6 0 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_1_6_120 : checkCert true 6 120 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_1_6_240 : checkCert true 6 240 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_1_6_360 : checkCert true 6 360 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_1_6_480 : checkCert true 6 480 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_1_6_600 : checkCert true 6 600 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_1_6_720 : checkCert true 6 720 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_1_6_840 : checkCert true 6 840 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_1_6_960 : checkCert true 6 960 120 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_1_6_1080 : checkCert true 6 1080 69 = true := by decide +kernel

private lemma certLayer_1_6 : checkCert true 6 0 (certCount true 6) = true :=
  (checkBatch_join (certCount true) (certState true) (certLocate true) 6 0 600 549
    (checkBatch_join (certCount true) (certState true) (certLocate true) 6 0 240 360
    (checkBatch_join (certCount true) (certState true) (certLocate true) 6 0 120 120
    cert_1_6_0 cert_1_6_120) (checkBatch_join (certCount true) (certState true) (certLocate true) 6 240 120 240
    cert_1_6_240 (checkBatch_join (certCount true) (certState true) (certLocate true) 6 360 120 120
    cert_1_6_360 cert_1_6_480))) (checkBatch_join (certCount true) (certState true) (certLocate true) 6 600 240 309
    (checkBatch_join (certCount true) (certState true) (certLocate true) 6 600 120 120
    cert_1_6_600 cert_1_6_720) (checkBatch_join (certCount true) (certState true) (certLocate true) 6 840 120 189
    cert_1_6_840 (checkBatch_join (certCount true) (certState true) (certLocate true) 6 960 120 69
    cert_1_6_960 cert_1_6_1080))))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_1_7_0 : checkCert true 7 0 94 = true := by decide +kernel

private lemma certLayer_1_7 : checkCert true 7 0 (certCount true 7) = true :=
  cert_1_7_0

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma cert_1_8_0 : checkCert true 8 0 5 = true := by decide +kernel

private lemma certLayer_1_8 : checkCert true 8 0 (certCount true 8) = true :=
  cert_1_8_0


private lemma allChecked (b : Bool) (k : Nat) (hk : k ≤ 8) (i : Nat) (hi : i < certCount b k) :
    runCheck (certCount b) (certState b) (certLocate b) k i = true := by
  have h : checkCert b k 0 (certCount b k) = true := by
    cases b <;> interval_cases k
    · exact certLayer_0_0
    · exact certLayer_0_1
    · exact certLayer_0_2
    · exact certLayer_0_3
    · exact certLayer_0_4
    · exact certLayer_0_5
    · exact certLayer_0_6
    · exact certLayer_0_7
    · exact certLayer_0_8
    · exact certLayer_1_0
    · exact certLayer_1_1
    · exact certLayer_1_2
    · exact certLayer_1_3
    · exact certLayer_1_4
    · exact certLayer_1_5
    · exact certLayer_1_6
    · exact certLayer_1_7
    · exact certLayer_1_8
  exact checkBatch_at h i (Nat.zero_le i) (by simpa using hi)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma roots : ∀ b : Bool, ∀ t : Fin 5,
    t.val < certCount b 8 ∧ (certState b 8 t.val).1 = t.val ∧
      (certState b 8 t.val).2.toFinset = (raw b).toFinset := by decide +kernel

private lemma certify (b : Bool) (t : Fin 5) (m : Nat) (hm : m ≤ 8)
    (h : Live m t.val (raw b).toFinset) : False := by
  obtain ⟨hi,ht,hs⟩ := roots b t
  apply runCheck_complete (allChecked b) 8 (Nat.le_refl 8) t.val hi m hm
  rw [ht,hs]
  exact h

lemma cofactorLower (b : Bool) (s : ℕ) (h : HasCircuitSize 5 (cof b) s) : 9 ≤ s := by
  by_contra small
  obtain ⟨C, hlegal, hsize, heval⟩ := h
  obtain ⟨k,t,S,hk,_,_,live,sub⟩ :=
    extract C.gates (raw b) hlegal (circuit_target (cof b) (raw b) (rawLength b) (sample_valid b) C hlegal heval)
  have eq := necessary (raw b) (rawEssential b) live sub
  have sc : S.card = 5 := by rw [←eq]; exact rawCard b
  have hs := (live_size live).2
  change C.gates.length ≤ s at hsize
  have kt : t ≤ 4 := by omega
  rw [← eq] at live
  exact certify b ⟨t, by omega⟩ k (by omega) live

def f (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4269860992 * 2 ^ 32 + 4269860864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxHeartbeats 0 in
lemma restrict_eq : ∀ (b : Bool) (y : Fin 5 → Bool), f (Fin.snoc y b) = cof b y := by decide +kernel

lemma depends : ∃ x : Fin 6 → Bool, f (Function.update x (Fin.last 5) (!x (Fin.last 5))) ≠ f x := by
  refine ⟨fun i => decide (i.val < 3), ?_⟩
  decide +kernel

lemma nonconstant (b : Bool) : ∃ x y : Fin 5 → Bool, f (Fin.snoc x b) ≠ f (Fin.snoc y b) := by
  refine ⟨fun _ => false, fun _ => true, ?_⟩
  cases b <;> decide +kernel

lemma lower (s : ℕ) (h : HasCircuitSize 6 f s) : 11 ≤ s := by
  obtain ⟨b,t,ht,hs⟩ := FirstGate.gate_elim_two 5 f s depends nonconstant h
  have he : (fun x => f (Fin.snoc x b)) = cof b := funext (restrict_eq b)
  rw [he] at hs
  have hb := cofactorLower b t hs
  omega

def bestCircuit : Circuit := ⟨[⟨.and,[0,1]⟩, ⟨.and,[3,4]⟩, ⟨.or,[6,7]⟩,
  ⟨.or,[4,5]⟩, ⟨.or,[0,1]⟩, ⟨.or,[2,8]⟩, ⟨.and,[3,10]⟩,
  ⟨.and,[8,9]⟩, ⟨.and,[2,13]⟩, ⟨.and,[11,12]⟩, ⟨.or,[14,15]⟩], 16⟩

lemma witness_mono : Monotone2 bestCircuit := by simp [bestCircuit, Monotone2]

set_option maxHeartbeats 0 in
lemma witness_correct : ∀ x : Fin 6 → Bool, bestCircuit.eval (List.ofFn x) = f x := by decide +kernel

end PEqualNP.Outside.L_meta_12094

open PEqualNP.Outside.L_meta_12094 in
theorem PEqualNP.Outside.L_meta_12094 :
∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4269860992 * 2 ^ 32 + 4269860864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4269860992 * 2 ^ 32 + 4269860864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  change ∀ s, PEqualNP.MetaComplexity.HasCircuitSize 6 f s → _
  intro s hs
  exact ⟨bestCircuit, witness_mono, lower s hs, witness_correct⟩
