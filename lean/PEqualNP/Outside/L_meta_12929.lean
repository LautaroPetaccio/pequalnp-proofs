import PEqualNP.Defs

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

namespace PEqualNP.Outside.L_meta_12929.FirstGate
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

end PEqualNP.Outside.L_meta_12929.FirstGate


/-!
# Supports of wires

Helper for `L-meta-011`. Every wire gets a support: the set of inputs it can depend on, read
off the gates. Two facts: the value of a wire depends only on the inputs in its support, and
any set `W` of wires has a joint support of size at most (number of gates) + `|W|`, because a
gate of fan-in two replaces itself by at most two earlier wires.
-/

namespace PEqualNP.Outside.L_meta_12929.FirstGate
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

end PEqualNP.Outside.L_meta_12929.FirstGate


/-!
# Gate elimination

Helper for `L-meta-014`. The last input of a circuit on `n + 1` inputs is fixed to `b`. One
pass over the gates gives every old wire a status: a constant, or an alias of a wire of the
new circuit on `n` inputs. A gate that reads a constant becomes a constant or an alias and is
not emitted, so if some gate reads the fixed input the new circuit is smaller. If no gate
reads it, the supports of `Support.lean` show the function does not depend on it.
-/

namespace PEqualNP.Outside.L_meta_12929.FirstGate
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

end PEqualNP.Outside.L_meta_12929.FirstGate



namespace PEqualNP.Outside.L_meta_12929

abbrev B := BitVec 23
abbrev Sig := B × B
def top : B := BitVec.allOnes 23
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
  by_cases hi : i < 23
  · cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases ht : decide (0<t) <;>
      simp only [sep,neg,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 23 ≤ i)] at h

private lemma sep_binary (t d : Bool) (a b : Sig) (i : Nat)
    (h : (sep t (bin d a b)).getLsbD i = true) :
    (sep t a).getLsbD i = true ∨ (sep t b).getLsbD i = true := by
  by_cases hi : i < 23
  · cases t <;> cases d <;>
      cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases hu : b.1.getLsbD i <;> cases hv : b.2.getLsbD i <;>
      simp only [sep,bin,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,hu,hv] at h ⊢ <;> first | contradiction | decide
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 23 ≤ i)] at h

private lemma sep_weaken (t : Nat) (a : Sig) (i : Nat) (hi : i < 23)
    (h : (sep (decide (0<t)) a).getLsbD i = true) : (sep true a).getLsbD i = true := by
  cases ht : decide (0<t) <;> cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
    simp only [sep,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide

private lemma live_sep {k t S} (h : Live k t S) (i : Nat) (hi : i < 23) :
    ∃ a ∈ S, (sep (decide (0<t)) a).getLsbD i = true := by
  induction h using liveInd with
  | stop =>
    refine ⟨target,by simp,?_⟩
    change (BitVec.allOnes 23 &&& ~~~(0 : B)).getLsbD i = true
    rw [BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_allOnes (v := 23)]
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

def bit (side : Bool) (i : Fin 23) (a : Sig) : Bool :=
  (if side then a.1 else a.2).getLsbD i.val

private lemma bit_zero (s i) : bit s i zero = false := by cases s <;> simp [bit,zero]
private lemma bit_one (s i) : bit s i one = true := by
  cases s <;> change (BitVec.allOnes 23).getLsbD i.val = true <;> rw [BitVec.getLsbD_allOnes] <;> simp
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


def graph (x : Fin 5 → Bool) : Bool :=
  Nat.testBit 0xfeeeeee8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)
def sample (raw : List Sig) (s : Bool) (i : Fin 23) (j : Fin 5) := bit s i (raw.getD j.val zero)
private lemma sample_list (raw : List Sig) (raw_id : List.ofFn (fun j : Fin 5 => raw.getD j.val zero) = raw) (s i) : List.ofFn (sample raw s i) = raw.map (bit s i) := by
  calc
    _ = (List.ofFn (fun j : Fin 5 => raw.getD j.val zero)).map (bit s i) := by rw [List.map_ofFn]; rfl
    _ = _ := by rw [raw_id]

private lemma circuit_target (raw : List Sig) (raw_id : List.ofFn (fun j : Fin 5 => raw.getD j.val zero) = raw)
    (sample_ok : ∀ s i, graph (sample raw s i) = s) (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = graph x) : target ∈ execute C.gates raw := by
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

def raw : List Sig := [(341199, 8330), (707379, 33313), (7539772, 6491156), (8130496, 6032704), (8384512, 4149248)]

set_option maxHeartbeats 0 in
lemma sampleCorrect : ∀ b i, graph (sample raw b i) = b := by decide +kernel

private abbrev SearchState := Nat × List Sig

private def sameWires (a b : List Sig) : Bool :=
  a.all b.contains && b.all a.contains

private lemma sameWires_sound {a b : List Sig} (h : sameWires a b = true) :
    a.toFinset = b.toFinset := by
  obtain ⟨h₁,h₂⟩ := Bool.and_eq_true_iff.mp h
  ext w
  simp only [List.mem_toFinset]
  exact ⟨fun hw => List.contains_iff_mem.mp (List.all_eq_true.mp h₁ _ hw),
    fun hw => List.contains_iff_mem.mp (List.all_eq_true.mp h₂ _ hw)⟩

private def checkLink (count : Nat → Nat) (state : Nat → Nat → SearchState)
    (locate : Nat → SearchState → Nat) (k : Nat) (s : SearchState) : Bool :=
  let i := locate k s
  let u := state k i
  decide (i < count k) && s.1 == u.1 && sameWires s.2 u.2

private def runCheck (count : Nat → Nat) (state : Nat → Nat → SearchState)
    (locate : Nat → SearchState → Nat) (k i : Nat) : Bool :=
  let (t, v) := state k i
  decide v.Nodup && (if k = 0 then v != [target] else
    !(stepTest (k-1) t v
      (fun w => !(checkLink count state locate (k-1) (t-1,w)))
      (fun w => !(checkLink count state locate (k-1) (t,w)))))

private lemma runCheck_complete {count : Nat → Nat} {state : Nat → Nat → SearchState}
    {locate : Nat → SearchState → Nat} {cap : Nat}
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
          Bool.not (checkLink count state locate (k-1) (u,w)) = true := by
        intro u w l hl hn
        by_contra bad
        have good : checkLink count state locate (k-1) (u,w) = true := by
          cases h : checkLink count state locate (k-1) (u,w) <;> simp_all
        simp only [checkLink, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at good
        obtain ⟨⟨hh, ht⟩, he⟩ := good
        have setEq := sameWires_sound he
        rw [ht,setEq] at hn
        exact ih (k-1) (by omega) (by omega) _ hh l hl hn
      have ok := reduced_step (S:=k-1) live (by omega) nd rfl
        (fun w _ l hl hh => imposs _ w l hl hh) (fun w _ l hl hh => imposs _ w l hl hh)
      change (if k = 0 then v != [target] else
        !(stepTest (k-1) t v
          (fun w => !(checkLink count state locate (k-1) (t-1,w)))
          (fun w => !(checkLink count state locate (k-1) (t,w))))) = true at no
      rw [if_neg kzero, ok] at no
      exact Bool.false_ne_true no

private def checkBatch (count : Nat → Nat) (state : Nat → Nat → SearchState)
    (locate : Nat → SearchState → Nat) (k lo : Nat) : Nat → Bool
  | 0 => true
  | n+1 => runCheck count state locate k lo && checkBatch count state locate k (lo+1) n

private lemma checkBatch_join (count : Nat → Nat) (state : Nat → Nat → SearchState)
    (locate : Nat → SearchState → Nat) (k lo l r : Nat)
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
    {locate : Nat → SearchState → Nat} {k lo n : Nat}
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

private def wireDataPacked (i : Nat) : Nat := (if i < 40 then (if i < 20 then (if i < 10 then (if i < 5 then (if i < 2 then (if i < 1 then 0x1800087280001f80a2bf000078000050000198082210000600208d40000780208a0000180082780000180a2ab00000600000000000400d540000008d4050000001c5140 else 0x9810035000026000000000081900305000206000000000806000000002000000000007fe028ffc001e180a3eb00078000050000181808221000600020d840006180208a) else (if i < 3 then 0x166002088400580400d4000160000000000418400c1400106000000000401800000001000000000003e7c0afff0009ff02bffc0026780208a00099900b7780026600208a else (if i < 4 then 0x1fe7023d84007e7c02dca001f810035000079fc08e350019ff00b2780061e400c14001801003000006000000000017e702bffc0059fc0afff00166602088400598408f75 else 0x1e78603cfac0781f80f2bf01e00603caac078000050000180060208840600000d2210060060082280180000708a001fff02bffc007ff80a2ab001ff902bffc007fe400d54))) else (if i < 7 then (if i < 6 then 0x21fff02bffc0861e400c140218180000000826780208a02081e00000008206000000020800000000080062300140200180000000800180000002000000000007fffc0ffff else 0x400000000000f807a3f2bf027fff8ffffc09a6780208a0269998df77809a0780208a02607e8fcafc0980780208a0260188dc2780980600208a0260008d400009800000000) else (if i < 8 then 0x580008d400016000000000041fff02bffc1061e400c1404186000000010599808221041066000000104180000000410000000001001823001404006000000010001800000 else (if i < 9 then 0x600788c00501800023000006000000000017819a3f2bf059fff8ffffc165998082210596618f7dd41641980822105807e8fcafc160198082210580608f48d416018008221 else 0x7e0668f48841f807a3708a07e0008d40001e01fa3823506607e8c82781861f8000000618798c30501861e0000000610788c0050184180000000608788c005018206000000)))) else (if i < 15 then (if i < 12 then (if i < 11 then 0x800000000001ffffe3ffff07ff818d75001fd9fe3ffff07f07e8fcafc1fa7fe3ffff07e87e8fcafc1f9ffa3f3ff07e07e8fcafc1f81f80a2ab07e0788fcafc1f81e235014 else 0x8600071400021800000000081fff02bffc207e0400d400819800000002026780208a08098600000020260000000080800000000200601c014008018000000020001800000) else (if i < 13 then 0xa0980000000282060000000a0000000000278619cf3eb087fff73fffc21a6780208a08699971f77821a6180208a08678673cfac2186180208a08618071c7282186000208a else (if i < 14 then 0xa698000000029a078000000a681800000029a000000000a619e008228298663f71de0a61860082282980780208a0a6006000000298000000000a099e00000028266000000 else 0xa799e00822829d98408f750a6f9e028fac29a7f80a2bf0a699f00b77829a67a3709e0a699e71c72829a6780208a0a699e00000029a6600208a0a699800000029a61800000))) else (if i < 17 then (if i < 16 then 0xe699e008228398000000000d89e08f48d431c781c71ca0c19e00000002fa6780f2ab0a7fff02bffc29fff80a2ab0a7f9f00b72829fe780208a0a79ff00b27829e7f80208a else 0xfe9fe8fcafc3fa7f80a2ab0fe99e8dc2283fa6780208a0fe1feffcffc3f81fa3f2bf0fe0008d400039e7f80208a0e799e00822839c180000000e69fe8c827839a7f80208a) else (if i < 18 then 0x101fff02bffc407e0400d40101e000000004059980822110160600000040580000000101000000000401801c0140100600000000400018000001000000000003ffffe3ffff else (if i < 19 then 0x121e18000000479819cf3eb119fff73fffc46599808221119661737dd44658180822111878673cfac46181808221118600734d844618000822111800071400046000000000 else 0x158660ff4dd45618180822115806602088456001800000158000000000505998000001416600000005058000000014106000000050000000000138e18734d8449d8623709e))))) else (if i < 30 then (if i < 25 then (if i < 22 then (if i < 21 then 0x159666734d84565998082211596660000005659800822115966000000056581800000159600000000564198000001590600000005640000000015899900b77856199808221 else 0x15f66603caac567ffc0afff159ffe028aac567f9c08f61159fe60208845679fc08e35159e7e020884567998082211597e6028fac5659f80a2bf159667023dd456599a3d235) else (if i < 23 then 0x17f6668f48845fd9980822117e67effcffc5f81fa3f2bf17e0008d40005e79f808221179e660208845e59fa3823517967e0208845e5998082211788180000005e000000000 else (if i < 24 then 0x181f81703500607e000000018178070050060580000000180f8070050060260000000180780700500600001c00001800000000005ffffe3ffff17f67e8fcafc5fd9f80a2ab else 0x19ef8673cfac679ff9cf3ff19e78673cfac679e180a2ab19e78073cfac679e01c514019e606734884678619c708a19e000714000661e19c8361186786708728607e1800000))) else (if i < 27 then (if i < 26 then 0x1a7f9e00822869e6780208a1a760000000069be79c21ca1a6f9e00822869a6780208a1a600000000067fffdcffff19f87971705067df9dcffff19f78673cfac67be7dcffff else 0x1d97e6020884765998082211d8980000000760000000001bffff73fffc6fbe79cf3eb1bef9e028aac6fa679c708a1be99e0082286f9e7bff3ff1be78673cfac6f8001c5000) else (if i < 28 then 0x1e07f8fc055077fffdcffff1df7e673cfac77df980a2ab1df66673488477d998082211de7e6ffcffc779e19cf3eb1de000714000767f98082211d9e66020884765f99c8361 else (if i < 29 then 0x1fe0060000007f8003f50001fe0000000007e7ff8082211f9fe60208847e79f8082211f966602088479fff80208a1e7f9e00822879e7f80208a1e699e008228787fe000000 else 0x1fff9e0082287ffe00000001ffe7e0208847ff998082211ff9fe0082287fe6780208a1ff8780000007fdffbff3ff1ff6660208847fbffbff3ff1fe99e0082287f9ffbff3ff)))) else (if i < 35 then (if i < 32 then (if i < 31 then 0xe00001703503800003f5000e000000000007ffffffffff1fffff02bffc7ffffa3f2bf1ffffe73cfac7ffff80a2ab1ffffe0208847ffff80208a1ffff8028aac7fff9808221 else 0xe01801003003805987fdf75e0100100300380400000000e00999fdf77b80200400c00e00800000003801e0000140e0007800005380001ff5d54e00001fd755380000630c14) else (if i < 33 then 0xe200008c000388000000000e1f80703faaf87800005000e01fffffffff807ffc0afffe01ff9003553807e05c0d40e01f810035038061e630c14e0187900305380601c00c00 else (if i < 34 then 0xe4106000000390000230000e40000000003898067f7ddee218798c30538861e400c14e218198c305388606400c00e218010030038821e630c14e208198c305388206000000 else 0xe600798c30539801e230014e600068c000398000230000e58061ff7dd79061e630c14e4187900305390618630c14e4186100300390600400c00e410798c305390418630c14))) else (if i < 37 then (if i < 36 then 0xe618018c30039841e630c14e610788c005398418630c14e610608c000398400230000e608798c30539821e230014e608198c305398206230000e608008c0003981e1a3a3eb else 0xe6187f0030039861fa30000e61879fd75539861e635c14e618798c35539861e630c14e618798c30039861e400c00e618788c00039861e000000e618618c300398606630c00) else (if i < 38 then 0xe61fff8ebfff987fe630d54e61e7f8e38d79879e638f75e61e798c35539879e630c14e619ff8cb27b9867e632ddee619f98c35539867e630c14e6187f8ebaff9861fe30c14 else (if i < 39 then 0xe7e07e8fcaff9f81e235014e7e000fd40039f800235000e7987f8e38d79e61e63de35e798798d70539e61e630c14e6787f8cb27b99e1e637c9ee678798d705399e1e630c14 else 0xe81981003003a0600400c00e80f81703503a02605c0d40e80980000003a00001c0000e800000000039ffffe3ffffe7fff98d75539fe1fe3febfe7f8798d70539f81fffffff)))))) else (if i < 60 then (if i < 50 then (if i < 45 then (if i < 42 then (if i < 41 then 0xea699970b72ba9a663f708aea6981fd7503a9a067f5c14ea6000fd4003a9800000000ea1999003003a82667f0d54e86181fdf77ba07e05c0d40e81f81003503a06605c0d40 else 0xea7999fdf77ba9e00400c00ea7666ff4887a9be7ffffffea69ffffffffa9a67ff7ddeea699f8cb27ba9a67dc2dcaea699efdc22ba9a6780208aea6999fdf77ba9a66632c9e) else (if i < 43 then 0xee18798c3053b8260230000ee00008c0003b6279dc8f61ec71e78cb27bb0679c00c00ebe99fffffffaf8003f5000ea7fffffffffa9ffe7fffffea799f00b22ba9e6780208a else (if i < 44 then 0xee70668c0003b9a67a3208aee699e00822bb9a667f7ddeee68188c0003b98003f5000ee60008c0003b87fe630d54ee19ff8c3053b867e7f0d54ee19f98c3053b861fe30c14 else 0xee79ff8c3053b9e7fc02c8aee79fe8c822bb9e7f80208aee79f9fdf77bb9e7e632c9eee79f98c3053b9e67e32c8aee79818c3003b9e1fe30c14ee7879fd7053b9e1e630c14))) else (if i < 47 then (if i < 46 then 0xefffffffffffbfe7fffffffeff9ff8ffaffbfe1e635c14efe9ffffffffbfa7e7fffffefe000fd4003bf800235000ee7fffffffffb9fffe3afffee79fffdf77bb9e7fe32c9e else 0xf21e1f003003c61807fdf75f01f81703503c07e0400d40f01e01703503c0780400c00f01801003003c05e05c0d40f01601703503c0580000000f00000700003c0000000000) else (if i < 48 then 0xf596618e38d7d65985c8f61f59660ff4887d65807f5d40f59061fd7053d6267bf708af58000fd4003d6000000000f41e61003003d05987f0d54f38e1f8e38d7c9d87dc2dca else (if i < 49 then 0xf59e67023887d6799808221f59e61ff7dd7d6600400c00f597e7ffffffd659ffffffff59667ff7dd7d6599e38e35f59667723d87d6599bfd221f59666020887d65987fdf75 else 0xf61ff98c3553d879fe30c14f61e79fc3553d879e630c14f6187f8c3053d861e630c14f616008c0003d8000230000f5f667ffffffd78003f5000f59fffffffffd67fe7fffff)))) else (if i < 55 then (if i < 52 then (if i < 51 then 0xf79e678e3887de780630c00f7987f8c3053de61e7f5c14f798798c3053de599a38221f79666020887de5987fdf75f790608c0003de207a30000f78000fd4003de000230000 else 0xf7e0008d4003de7fffffffff79fff8ebfffde79fffdf75f79e7f8e38d7de79fe30c14f79e7f023887de79fa38221f79e7e020887de79e7fdf75f79e798e38d7de79e630c14) else (if i < 53 then 0xf80781703503e01e01c0140f8007e728affe00019c0000f80000700003dfffffffffff7fe7fffffffdff9fe3febff7f8798d7053dfd9ffffffff7f679ffffffdf8003f5000 else (if i < 54 then 0xf81981703003e06005c0c00f81781703503e05e01c0140f81601703503e05801c0000f81000700003e03e05c0d40f80f80700503e02605c0d40f80980700003e02001c0000 else 0xf81f87703503e07e1c00c00f81f86700003e07e07f5d54f81f81717503e07e05c0d54f81f81703503e07e05c0c00f81f81003003e07e01c0000f81f80000003e07805c0c00))) else (if i < 57 then (if i < 56 then 0xf87f81703503e07ffdcaffff81ff9703553e07f9dc8f61f81fe1723dd7e07f85c0d54f81fe1703503e07e7dc2dcaf81f9970b77be07e65c0d54f81f99703503e07e1dcafeb else 0xf9e787ffffffe79e19cf3ebf9e780714503e78003f5000f9e000714003e67e1dc8f61f99f81737d87e67e05c5d40f99f81703503e1fe1dc2dcaf87f8171f72be1fe05c5d40) else (if i < 58 then 0xfa1ff9703553e87e7dc0d40fa1f99fc3553e87e65c0d40fa1f87703503e87e05c0d40fa0818700003e80001c0000f9ffff73ffffe7ffe5c5d54f9ff8773ffafe7fe05c5d40 else (if i < 59 then 0xfa7f87703503e9fe07f5d40fa7f81703503e9e67dc2c8afa7819703003e9d819c0000fa699e70822be9a6780208afa6999fdf77be9a601c0000fa6000fd4003e98001c0000 else 0xfbe000714003e9ffffffffffa7fff72bfffe9fe7ff7ddefa7f9f70b72be9fe7dc0d40fa7f9f00b22be9fe79c208afa7f9e00822be9fe67f7ddefa7f9970b72be9fe65c0d40))))) else (if i < 70 then (if i < 65 then (if i < 62 then (if i < 61 then 0xfc1fe1703503f07e1dc0d40fc1f81703503f04181c0000fc0000700003efffffffffffbff9fffffffeffe7dcffebfbff81717503efbe7fffffffbef99ffffffef8003f5000 else 0xfd9e67723887f66185c0c00fd9666720887f6599808221fd9661ff7dd7f65801c0000fd8986700003f60003f5000fd8000700003f07fe5c0d54fc1fe7703503f07f87f0d54) else (if i < 63 then 0xfd9fe7ff7dd7f67f9dc8f61fd9fe7703503f67f9c08e21fd9fe6720887f67f9808221fd9fe1ff7dd7f67f85c8f61fd9fe1703503f67e1dc0d40fd9f81fd7503f67e05c0d40 else (if i < 64 then 0xfe0998fc0003f80003f0000fdfffffffffff7ff9fffffffdffe773ffaff7fe05c5d40fdf7e7fffffff7df87ffffffde000fd4003f78001c5000fd9ffffffffff67ffdcafff else 0xfe1fe1703503f87e67f0d40fe1f99703503f87e07f0d40fe1f81703503f879e7f0c14fe1e798c3053f867e7f0c14fe19f98c3053f861e7f0c14fe18798c3053f85983f0000))) else (if i < 67 then (if i < 66 then 0xfe78798c3053f9a67bf208afe6000fc0003f87ffffaffffe1ffffc3553f87ffe30c14fe1fff703503f87fe7f0d54fe1ff98c3053f87fe5c0d40fe1ff9003003f87f87f0d40 else 0xfe7ffffcb77bf9fffe32c9efe7fff70b72bf9ffe7f7ddefe7ff9fc3553f9ff85c0d40fe7f9ffcb72bf9fe07f0d40fe7f81703503f9f9e630c14fe79fffcb27bf9e1e7f0c14) else (if i < 68 then 0xff9ff9ff7dd7fe7fe7f0d54ff9fe7fe3d87fe7e65c0d40ff9f81fc3503fe7e05c0d40ff9e7ffe38d7fe67e630c14ff9879fc3053fe61e630c14ff9666fe0887fe0003f0000 else (if i < 69 then 0xffe006700003ff8007f5d54ffe000fd4503ff8003f5014ffe000fd4003ff8003f0000ffe0008c0003ff8001c0000ffe000000003fe7ffff8f75ff9fff8e38d7fe7ffdc8f61 else 0xffe078fd4053ff819bfd221ffe060ff48d7ff8183f5014ffe060fd4003ff807bf708affe018fdc27bff8063f5014ffe018fd4003ff801bff2abffe006fd4003ff801a30000)))) else (if i < 75 then (if i < 72 then (if i < 71 then 0xffe7f8fd4553ff9e1bff3ebffe780fd4503ff981bfd221ffe600ff4d87ff9803f5140ffe600fd4003ff861bf708affe180fdc72bff8603f5140ffe180fd4003ff81fbff2bf else 0xffe998fdc22bffa663f5000ffe986fd4003ffa607f5d40ffe980fd4003ffa1e3f5014ffe81efd4003ffa067f5c14ffe818fd4003ffa01bf5000ffe800fd4003ff9ffbff3ff) else (if i < 73 then 0xffef9fffffffffbe7bff3ebffef80fd4503ffa7fffffffffe9feffcaffffa67ff7ddeffe99efdc22bffa67bf5000ffe99e8c822bffa679c208affe99e00822bffa667f7dde else (if i < 74 then 0xfff660ff4887ffd983f5000fff606fd4003ffd807f5d40fff600fd4003ffc1e3f5014fff066fd4003ffc187f5c14fff060fd4003ffc01bf5000fff000fd4003ffbffffffff else 0xfff7e7ffffffffdf9bff3ebfff780fd4503ffd9ffffffffff67effcaffffd99ffdf75fff666ff4887ffd99bf5000fff6668e0887ffd999c8221fff666020887ffd987fdf75))) else (if i < 78 then (if i < 76 then 0xfff87efd4003ffe1e7f5c14fff8798c3053ffe1e3f5000fff8788c0003ffe187f5c00fff860fd4003ffe067f5c00fff818fd4003ffe007f5c00fff800fd4003ffdffffffff else (if i < 77 then 0xfff9fffdf27bffe7fe32c9efff9fefdc22bffe7e7f7ddefff9f9fd7053ffe783f5000fff99ffdf22bffe607f5c00fff980fd4003ffe1ffffebffff87ffd7053ffe1fe30c14 else 0xffff81703503fffe03f5000ffff80700003fff9fffde35fffe7f8e38d7fff9fbfd221fffe79ff7dd7fff9e7f5c14fffe67ff7887fff863f5000fffe01fd7003fff803f5000)) else (if i < 79 then 0xffffe1ff7dd7ffff87f5d40ffff9ffdf72bfffe7dc2dcaffff9efdc22bfffe67f7ddeffff99fd7503fffe1ffffebffff87fd7503fffe1dc0d40ffff86fd4003fffe07f5d40 else (if i < 80 then 0xffffff02baaffffffbff2abfffffe8e8aaffffff9ca2abfffff9ffffffffffe7f5d54fffff98c3053ffffe5c0d40fffff8fd4003ffff9ffdf61ffffe7723d87ffff9bfd221 else 0x3fffffffffebfffffffffafffffffffdf75fffffffebffffffffff7ddeffffff8ebafffffffdcafeb)))))))
private def wireData (i : Nat) : Nat := unpack wireDataPacked 46 12 i
private def readSig (i : Nat) : Sig :=
  let a := wireData i
  (BitVec.ofNat 23 (a >>> 23), BitVec.ofNat 23 a)

private def sigHash (s : Sig) : Nat :=
  let h := (s.1.toNat * 0x517cc1b727220a95) ^^^ (s.2.toNat * 0x9e3779b97f4a7c15)
  let g := (h ^^^ (h >>> 57)) * 0xbf58476d1ce4e5b9
  (g ^^^ (g >>> 49)) &&& 0xffffffffffffffff

private def stateHash (s : SearchState) : Nat :=
  s.2.foldl (fun acc x => acc + sigHash x) (s.1 * 0x94d049bb133111eb)

private def decodeWires (code : Nat) : Nat → List Sig
  | 0 => []
  | n+1 => readSig (code &&& 1023) :: decodeWires (code >>> 10) n

private def st2Packed (i : Nat) : Nat := (if i < 1 then 0xee6e52b0c7750c1f463baaf0fa31dd3dc7d18e3aeeb2cc75133c3863ba928ac31dd4ba5618de765c40c7752095863a89ae1831dd41a7d18e3af2b1cc775bc95863babb8ac31beec38818ee9f83e8c775b09f463bab1cfa31dd4ce5618 else 0x77520bdc63bab90ac31dc4bc5618ede4b2b0c76efc9f463b8838fa31dcd7a7d18)
private def st2 (i : Nat) : Nat := unpack st2Packed 37 20 i
private def adj2Packed (_i : Nat) : Nat := 0x168101
private def adj2 (i : Nat) : Nat := unpack adj2Packed 2 80 i
private def loc2Packed (_i : Nat) : Nat := 0xd000000003419ae0140000237066720101000040001800000002cf5b00000500000000c3c000a540
private def loc2 (i : Nat) : Nat := unpack loc2Packed 5 80 i
private def st3Packed (i : Nat) : Nat := (if i < 19 then (if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then 0xea38e904ac41dd71cf71f483baea1ee3e9075120bdcdb20cdf10bb8ac41dd4eef71f4838ea360e429071d46c1cb2a0e3ad9978ac41c758f469f483a8b1db63e9074946b40b1a0e3b08904ac41c751b33958838ea36183e9075133b6c5620ea2e5948ac41d45cadb2ce83a8c09ee3e90751814825620 else 0xdf6e8990ac41bedd12f958837dc42382b10750fc36c7d20df68d6d96a41dd3dcbf9f48337c41f94010775151f45620ee9e63e8ac41b6e21259588361cdf103e907759bbdc7d20eeb10904ac41dd66f2095883ba9057f2b10774b89f45620e3aeea34ac41dd51b2095883ba7b9b63e9077520b6c5620) else (if i < 3 then 0xcdf10834fa419bde4db2d48337bcac76d9071d46c1a7d20cdef26d95341bee20bfaba839adf68d1b106fb84b6caea0df703a355d41bed1ad9aba837da29b657506fb46ca4aea0df68d8495d41bed86db2ba83a8b96642b106fb46cbe5fa0eea41680ac41bce6f88158837dba2522b106fb7436cb3a0 else 0xcdef281d37419bde52a166836dbca542b10774cb9f45620dcef26d93241b9de5291588373bc9b6575066f88496aa20ddaf2950ac41b9de532158837dba25f57506e7794a85620df68d9515d41b9e212595883a8835b63e9071d843dc7d20ea2e5950ac419be210c1f4837dbca642b10774ca9f45620)) else (if i < 6 then (if i < 5 then 0xea2bc6d8fa41d45cadb2648337bca544dd06e77936c9ba0e3af268137419be64cda6e83b6b7db64dd075f7936c98a0cdf12bc937419bde4da26e8334bc9b64dd06fb46cc8b3a0cdef297d3741bedd0db26e8337c424b4dd075172b6c9ba0db6f26d93741b9de52a26e8337bca524dd07753bc825620 else 0xdbef26d93741bedb72f958836fc424b2b107537936c9ba0e3ae8978ac41bedd0db264837dd868d6d906ed794d65620ee9ee5c4fa41bb62125958837da366b58d06fb75cd65620eeae59acac41dd4507d1588337c42bc3e9066f8bde49ba0ea2bd6d96841c7579469f483a89ad972b1075120b6c5620) else (if i < 7 then 0xea2e56d95d419bde52a188838ea365e58d07633bb6cb420cdf1092cc441b6d1b35988836fb6e6b311066f5b4d66220ea2d89acac419bdb735966836db6e6b2b1066f794c8b3a0dbed99acac419bdb735a6e8373b6e6b2b1066f6dcd6aa20ddadb9acac41b7d1b35ac6836fbae6b2b1070d884825620 else (if i < 8 then 0xcdeef6d937419bddf2a1588365b0e123e906fb46cc2aea0df6ea6d95d41bedd53095883bad95f93e90774bc9f45620cdf119acc4419be2125158838ea364a2b107512536c5620d968d6d96b41b2d1b0aad0836fa366b311074946cb06220e3e8d9acc4419ad1b35988838ea365e57506e746cd66220 else 0xd96c16d94241b2d1b092be8365b05b65a106cb46c20afa0d96c1840fa41d1e6f469888337c8a8d43906c760b6c7d20df6e8950ac41b151b081f483aad95b657d071d46c1cafa0cdedd6d96c419bd833598883ba904fa2b1066f6dcd66220cdf107e546419bd1b341888337bae6b58d066f794a8aa20)))) else (if i < 14 then (if i < 11 then (if i < 10 then 0xeeb8e904ac41d44badb158838ea35f83e9066f74378b620cdf216d94641b2d1b359848365bc9b64d5051b2f2c25620d970b6d95f41c86cb46abe837bba1b62b106cb46b66afa0eda776d96741b2d64db2be83a6a35bc5b106cb60c20afa0eab376d96c41b2e20fb1f48357a361c42906cb46cbeafa0 else 0xcd6936d96c41d1ecb468dc8337b25b6519066f93596a320cde8d9a4c4419bd27082d8833ba35b65b106eb7936c9ba0d96c4840fa419be46efa1c837aa365f2b1076bb2b6c8e20d968a6d95f41c762120958835eb2db6561066f65b6cb5a0e3acb76cfa419bddd65b6c8365a360557d071d46cba5620) else (if i < 12 then 0xd6ecb6d94641add97029f48365b06053e906cb65c2a7d20e668d9acbe41d457adb284835bb25b63e9066f7940a9ba0d968d9855f41b2d82db2be83a8af6033e906ed46cd6aa20d96ea6d95f419bd90db28c8337b22053e906bb65c0e7d20dce8d6f16c41abe20fc9f4835bb2e033e906cb61b6cb620 else (if i < 13 then 0xd56cb814fa41c7597011f483b4a35b657506b765b6ca120e2e8d3e8ac41b9d96db28c837da365f58d066f65c20a320d6ecb6d95f419bdbb35ad88337b2e155a1066f65c0ea320d76cb6d94641b7d1b349588365a365457d066f65c0aac20dea8d6d95d41add970a9f483bab2e0e3e9066f65c0aa320 else 0xea21c630fa41d43dcdb1f48337a361c55906df65b6ca320cd70e3e8ac41bed1b02aba8399a35b657d071d65b40a320df710920ac419be63658b68389b2db6519076965b6ca020d96b46d95f41e066edb24083a8ac61c3e9066f89596a320cd2cb6d94641b2d1b01abe8355b2db6519066f65caca320))) else (if i < 16 then (if i < 15 then 0xe3b61a34fa41af597029f48337bca6b551066f992feaa20dcef06d8ac41bdd1adb2ba83ba8e0fa2b106bd46c38ac20cdf10b90ac419be1a7d1588337a361c5ad066f874388720cde936d16c41c651afc9f48337b121c595071d46c82f720ea2778710e41c751af71f4838eb928d2b107515ec2a7d20 else 0xdf6db6d95d41c867b46ad883a8af6053e906b346cd66220cdecb80d4641d33687d1588359a361c5b10774f73407d20cf7105fd6c41bed1b0e2c28337b6e682b106cb60b6ca320eeb7d92cac41b7db735958835eb2e1c3e9075365b6ca320e3a8d9696c41d44f0db2d88337b766b31106e36ecd65620) else (if i < 17 then 0xd5ef26d937419be60db26e83b5cddb64dd066f65b68a320d9710798fa41b7d1b3597e8337a361a43906af46c347d20cdf31a34c441d471cf71f4837dad1b6575067b87d1ab620cdeb28710e419ed16db2d88337ad2193e9066f7836c9ba0cdf107e50e41d45cb2f9588363a35b657d06fb46cc2b620 else (if i < 18 then 0xcde8d8116c41c866f46ad883c1cde931c106cb61b6cafa0d5ec4870fa41abd1b0e21c8337a35ba5b1066efcaa07d20d5ecb814fa41add1b35988838ca364b2b107515ec207d20cf6c36d96c41b2d1b0821c8337a2e6b31106cb5a4207d20cdeb49acc4419ed1adb2d8838eb060e3e906b765c0aa320 else 0xcd68d8710e41aad1b0e21c83a692db62b1066f46ca6b620cdf235fd58419bd6d0e2d88355ad21c3e906cb60c2a7d20d5eb2870fa41c6efb46aba83a6c3ef22b1066f45378b620cdedb8710e41b7d1b0e21c83a8af5b657d06e346b78b620e437da355d419bd690e28c83baa35ee3e9066f60c388720))))) else (if i < 28 then (if i < 23 then (if i < 21 then (if i < 20 then 0xdf6d997cac41c6d147d1588000ee9ee3e8c6cb65b6cb420cde8d9ad54419be457908a8365a35bc57d06b346c388720ddaf26d954419bd6d0e21c838ea365e2fd066f8dcd66220f0737a347241abd96db28c837da361c425066f744388720cdeb487158419be610e1aa839ba3609439066f88c388720 else 0xe330e870fa41add1b0e21c833da35bc5b1066f49b66b620cf6e86d96c419bd1b35ad483a8c41ee3e9066f87d7a7d20ea2bd6d94641c6d7b469f4837db2db65050750d91f45620e95b63e8ac41add26db2d883ba630fa2b10774ec9f45620cdecb87158419be2549ad88357ad21c3e90669879f45620) else (if i < 22 then 0xcde8d81d6c419bde50e1c68371a366b311066f794ac9ba0cdf12a356c419bdb4db2d8828d839613e9071f46c388720cdeb36d96c419bd96db2b0838ea24fa2b1066f46c38ac20d768d6d96c419bde4de26e833da35b35b1067b6db6cb620e8a8d87108419bd9735aa0837db65b6575071bb2d1aafa0 else 0xcde4b540ac41c7526d02d8837dbadb658d066f87de49ba0e3adb978ac419bd1b0dad88337ad21c43907510c36c7d20e3e8d6f16c419bd9702a1c8337c866b22d074f9eb6cb620e328b3e8ac41bede4db2ce8375b2db651906b7883f27d20cded99acc441b751adb2d883a9a4db65b10667881f45620)) else (if i < 25 then (if i < 24 then 0xe9f656d95f41af620fc9f48337a361c5950751b0b6c7d20e9f8dd94fa41abd830e1f48359ad9b65b1070d883dc7d20cdf0e9acc441dd620f71f4838ca366b3110719874d65620d768d81d6c41b251adb2d8838ec41ee3e9066f744d66220e3a8d904ac419be21259668337b2dbc51906ad46b6cb620 else 0xd968d6d96541b2de4db2cc83a8b85b65b1066f6ec388720e9e5e6d8ac419be20ff2d88337b2e6b2ed074d7936c9ba0cde8d8496c41b151adb2be8357ad21c4390775d44825620cdeea9856c41c6dcb46958833da365f5b1074fbeb6caea0d57107e4fa41dd3147d158837dbae5f2b1066f46cd70c20) else (if i < 26 then 0xe3737a4d6c41abd1ade2d88371b75b65b106fb46b6cb3a0d5e8d87165419bd1b0ca1c8359ada1c3e9066f45b78b620cdf1099cac419be1f65a8c83a6b2db6519074d87d967d20ee9db3e8ac419bd9703ad883a8c42412b1074946b56aea0cdf236414641aed96db2d883b8680fa2b106cb46cd6b0a0 else (if i < 27 then 0xcf6cb6d94641bad1adb2d8833da4dbc5b10001dd4825618d96b2840fa41af5690e1f483b0df5b646907517236c5620cde8d9a96c419bde50e2a08375bc9b65b1066f883dc7d20cde916d96c419bd96db2d0838ebca512b106cb60c067d20cdef26d967419bd690e2008337a4e6b311076ebf9f45620 else 0xcde939516c41d8d70db28c83a67e5b63e9066f60b78b620e328d8710e419bd2702ad88379d968d6d906df46cd6aea0cde8d9ad5241c751ad0ad88337c45b65b106b75a4387d20f03376f11e41b2e0b46abe83aacf5b65b1066f46cd6b1a0dd6936d96c41c751b0721c838ebae5e2b106b746b78b620)))) else (if i < 33 then (if i < 30 then (if i < 29 then 0xd968d8716541adde4db26e8365a3610595066f49b78b620d6ecb6d96841e0e7b468e0838ea360f5b1077520ae25620cdeca6d96c41cdd1ad32be8337a35bc5b106fb46b6cb1a0cdecb9514641d3c1cdb1f48337a4e075b1077d49b6caca0e6e8d6816541d44ef35988835dbc9b64dd06eb794ac5620 else 0xefa8d6d95b419bde4db26e837da365f311071d794545620cdecb97d46419ed1b2a2d88365c417f57d066f46c388720cdef29596c41bed1ade2ba8337b2db651906cb46b6cb420dbee89acac419bd87092d88337cca2e311057adb2cc7d20cdf10904ac41bad1b2b2d88337c3a0e3e906cb6db6cafa0) else (if i < 31 then 0xdf6936d95d41d3e6ede2d8833da361c439067b5a36cb620e3a8d978c441d457cdb2d883ba5f0fa2b106fb7536cb620cf68d9acc4419bd1b359888357a4db65b1066f88466b620ee6773e8ac419be550e21c8337c41805b1067b46c20b620e8a8d6d95d41d7d1adb2be836fa4db65b1067b7936c9ba0 else (if i < 32 then 0xcdef26d954419bdd4db2d88337bca104dd066f49c388720d76936d96c419bd6cdb2d8839ca361c43907755ec387d20cf28d6d96c41e067adb23c837db05b657506e346cd6b620eda826d95d41b8d1adb2d88391a35a05b106e749b6cb620cde8d9596c41d44eede2d88365a35b657d06cb6236cb2a0 else 0xdf6cb6d96641bed1b2faba83a8de5b62b1066f5b378b620efa8d6f15941acd1ade2d88337c39bc5b1066f883f07d20d668d6d96c419be2120bdc83a6a4db65b1066f65c0a8020cdf10974ac41abd1b359888337a4e565b1067b46c24b620e3b79a34ac41abd1b0e2be833da36055b1067b49b6cb620))) else (if i < 35 then (if i < 34 then 0xcdedd6f16c419bd96db2ae8337b6dbc5b1066f8858e7d20ea2ee6d8ac41b7de52a158838ead20e3e906e346c388720e373da356c41add97081f48337a2e1c439071d5941c7d20cdf0e978ac419be22de2d88373bc9b659d066f87d26b620cde8d99e1c419bd26db2d88334a35bc5b1070f7936c9ba0 else 0xd96e86d95f41b9de52f958833da29b65b106fb46c20aea0df28d6d96c4172b6cb31588365a361042906fb7436caea0cdf0fb94ac419ed1b30ad88393a366b311067b8736cb620cde8d9856c41d866edb28c83aadf5b657506df46b78b620cde9397d6c41d8cfadb2be83babca5e2b1067b7536cb620) else (if i < 36 then 0xdf68d6d96241d3f1bbe9588337bc5b65b1066f89afeb620e32936d96c41bed1adb2ba838eb120e3e9071f46b6cb620cf6c16d96c419bd68de2d883a9a35b65b10774f71f45620cd68d6f16c419be20fcab08365a4db657d071946b78b620cd2936d96c419bd1addad8833da35b45b1074ed99f45620 else (if i < 37 then 0xbde8d8710e419bd1affa1c8337b2dae51905973836ca320d96316d95f416851b359888337a3635311066f793529ba0bca216d93741883107d1588000eea412b0cf50bb9f45620d968d8496c419bd86db2d88365a35b659106e746c388720e6b37a350e41d5ceedb2d88337a49b65b106cb624387d20 else 0x3ba7b8fa333bbae7d158828d748fa2b1066f42c388720d4d7f3e8ac4146beadb2ba838e5e0fa2b106cb46b3cafa0cde006d9374154b6c7d15883378d1b6519066ec29f45620df5e26d95d419bd0135988837da3593575066f46b78b4a0cde936d969419ed1adb2d2828d8e9b657d055cd01f45620))))))
private def st3 (i : Nat) : Nat := unpack st3Packed 47 20 i
private def adj3Packed (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0xbc240040a0142120401008e0200e32100010041180041808110c61084031000a0048630021200001240100043200cd02404 else 0x13804320460220264a003110020080509008080012302508401304250142e1040100ca34080000002308000382008023) else (if i < 3 then 0x30c8d18c83002c4188200146c0880218c05004c338422084001842100460080a10944c189613810250c211000010022181c9 else 0x8080030c60184008003))
private def adj3 (i : Nat) : Nat := unpack adj3Packed 5 80 i
private def loc3Packed (i : Nat) : Nat := (if i < 7 then (if i < 3 then (if i < 1 then 0x3956e00000001e6000000024c00000a45746f5881ca510003535458b74001a85c0fd1a00033895cd8369cba2f73817d000004b000af9540c4009ec00462672793a000c40002bb500070d4a60db01047e00000af5e700036b3a1d66c0017d38001c54a63f else (if i < 2 then 0x87887a1456bac003e8009a4004288c2f494166b3a740030a3b4d5d818d5b184ea0028372dd4248c50000142000002d133653000600024e0f9d3906de5ae6289c00002d3002312c800560007e61a23a8b78c008b22d02d300a8000000065c001680000066 else 0xa49d6680045400001030022659800840ee04400881596105d688001943d00042525e900004001c16c400b4000a8c00000008040000000720f56651f01437a48742649c88a240012b59c238140000186718000004c6859d000100000076c76148d200000)) else (if i < 5 then (if i < 4 then 0x64400002d732800000004b5ae4662a8a400b4800aa0000028f8c00c00000208002b4000b000000dba692400000001bf000a4001900020913d23000002c26b00000000308f4004f5a7a10e7a1e822d8000091c20c0083e2f8e6e41be9b77cf30000057e77 else 0x64a980ee5546ed5bb400000486540000000000cc002353792700000a3800b7ef6000700002400141a564d000fb7c52026d144dc0052c0084eda00046001d2ada2b000005bdd600182a95ac00000001b37648b6e8000007b000002b0d9a50003daaa8d800) else (if i < 6 then 0x864007e021392d84fde43014c000cf000ef00000000d49d93e358dc00000000082f02000032000ed0018e26000b640073dde00043a01757bda50000012c00ae0001d6cc49400b197c002bb00107a89696715d71ca5000b3941bb9f8008ce7c710b40e672 else 0x8800002470000039ac000054b12084c544000004c80062d020b400794f100000346f30000029caa0000056869000000516a00105b72540024a03400970008a00000000630000028d24c00001b804c7f00053a65e0000afbbab71b9ff001330180023d10))) else (if i < 11 then (if i < 9 then (if i < 8 then 0xa2486850000000050e6525962319722e800788003cae6000002b8003c000829ee53800000002985b3e47d002a478400029f5002593e1aa6a1210005ead263b6c001b00000000000c124000515cc8f16444880000000e800220b9002ad6040000000 else 0xa28642840026a469f44900260001d792400b8c007ca327a0005e4b78de02000007eec5680005b0007b400a40e997d9eb84006fa5a00050000006b61728a3a1b6f4bc8e35b40e000a900000001dd922f0702ea0f077860005ee3e09e0e0016882e4057000) else (if i < 10 then 0x9eaf1b898795c0003df0aa400556af628005d8000020c002ec15400001564ec0087c00a7ae99e0000014daf0f79140045878000fd079ec0015100000000004a800236ca000002266d071528ba4400026000680025e09400001f407d0da056535d3caac00 else 0x96e962fc0044c000008aae800b2c000a1f39980099000b9c007d800001969580037c00001850d1340000069922360b138400000a80000072484001c2002157ea1c214008181d501b97280058c2e0680000016001bc58697000ff6c8a0446123880043c00)) else (if i < 13 then (if i < 12 then 0x5e800002cf508000029fb5a4205c6700106844009b8000028caca71b066a00000001739a04a6a46b0010467cd0754001e5b66d4009c10b8e0000014f00000ac0d3001806ae1600000024c89600081e9343800245d0000005410c064003aeb14bec9520ce else 0x5180015c005817f000070000093e52134007dd8d624003b1282f9532e126000003d000001ce000004b9a4001d10000000193a995e000380002f100fe254730619800178b34ab9bdb4001770020306c007f897402ae0028688d017a8e800e6cb0c00056ef) else (if i < 14 then 0x274b20002ec00000001f00000273000fca9e2168e34001367f40055c51002887f2e063c0032c710009f002795f800000001140047abf000dd5c400002c2000c936a4380000b1cc3ae481770a38124b47400b95b7425399d4006be7f0000051c00ab2a0 else 0x98400a86b545c00974c70004e002f51e8000000086cb518994001da7ad70000000004704844))))
private def loc3 (i : Nat) : Nat := unpack loc3Packed 10 80 i
private def st4Packed (i : Nat) : Nat := (if i < 64 then (if i < 32 then (if i < 16 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0xe3a8d630fa2b1471d46b2e7d158a3a8af5b63e88351d44eedb2845628cde8d94cfa2b1466f72d1adb264a337b968d948ac51d45cadb19a5628ea277948fa2b1466f46c30db1f4a3a8b95b63d4ac51d45c4db1f45628ea2777b9b63e94751812e27d158a337a35b6558ac51d44ef0a9f45628eda776d8f52b1466f46c2ab4158a3b1cde8d6d96851db66f46b6cb3a8 else 0xcdeda6d8fa2b1471d46c167d158a3a876db63e8ac519bddd46b6c5628e3a8d680fa2fd471d6cb407d158a38ea365e3ccac51c751b2d9f45628cdec7a35b63e9473746b407d14aa38eb11a03e8ac51c751ad02c67d28e3a8d7b9a03e9471d46c82d0158a3a8905b6680ac519be10f736c7d28cdf08905b62b1466f46b6cab958a337badb658cfa51d266f46b6cb1a8) else (if i < 3 then 0xe3a8d905712b14001d43dcdb1f483a8cddee6d8fa51d466f20b6c5628ea28d7b9b63e9475146c82db158a337a36417b9b651c351af736c7d28cde8d6d9642b147753bb5e7d158a337c422a3e8ac51dd51b2f1f45628eea776d8fa2b1466f883187d158a3baaf5b63e8ac519bd1adb2d65628cde8d6d96a3e9466f46c1cdb214a38ea35a0428ac51c7564d01f45628 else 0xdb68d92db62b146db882fe7d158a356a35b63e8ac519be211b9f45628ea2386d8fa2b1466f91afe7d138a35ec417f3e8ac519be20bfaa87d28cdf107b9713e9466f883dc7d158a000ee9713e8ac41dd66eb89f45628cdf107b97f3e947757f2fe7d158a337c428d904ac51dd51ab89f45628cdf10905b62b1471d46bdcb89f4a38ea35ee3e8ac500071d46c825620)) else (if i < 6 then (if i < 5 then 0xeea8d6acfa2b146fb46b6c7b958a37da35b658cf351bed1adb2c65628df6eb6d8f32b146fb46b6cb19f4a37dbadb63e8ac51d43ccdb1f456280037da35b659d06fb46b6cb3958a3a89ddb64c8fa51d44eedb2d05628df68d990fa2b147516436c7d158a37dcde8d6d967519bd1afcb6c8028cdf107e4fa04946ab882fe7d158a337c41e53e8ac519be21259580ea8 else 0xe3ae8680fa2b1466f7436c7d17ea337b665f3e8ac519ad1b2f9f45628cdee897cfa2b1466f75cbe7d158a38ea36777b8fa519bdd1291f45628cd2e86d8fa2b1466f744c87d158a337b0e123e8ac519be20ed9f45628df737c424b2b1471dbed1b25958a3a8df64b6d8ac51bed1b1c36c5628df68d6d9673d54775beafe7d158a337c417c3e8ac519bd1afc36c7d28) else (if i < 7 then 0xdf6d96d8eb2b14001bedd12f958837dba28d97cac51dd71cb89f45628e928d6aceb2b146fb46b6c991d6a37da36523acac51db504db1d65628df737ba25f2b146fb46cbe79958a37dba1b63d4ac51bed1b2f9d65628df6e86d8eb2b146dd46b6c7d158a337c42483e8ac519be21169f45628cde8d979b62fd471d46cbc75958a337c41e63e8ac519bdd12f36c5628 else 0xdf68d9ddb6575466f882feae9f4a337a365e6d95d519be12db2ba7d28cd68d6d95d3e947619bb6c8d1f4a37da365f6d95d51bedd146b6caea8df737a365f57546fb46cbeae9f4a37dba1b6574fa519bdd12faba7d28cdf109057f2b146fb46b6cae93ea337c25b63e8ac519be07469f45628df68d97d5d2b146fb61b6c75958a37da29b63acac51bee20bf9d65628))) else (if i < 12 then (if i < 10 then (if i < 9 then 0xea2f2979b62b14750db32a7d158a337a360d6d8fa51dd5cadb1f45628cdef26d9673d5466f7936cb3958a3a8cdef26d967519bde4db2ce7d28cdef2990fa2b14751b136c7d158a3a8b7db63e8ac519bd1b0d9f45628df68d6d95d3ad466f46cbeae9f4a337ba1b6574fa51bee2146b6caea8df68d6d95d1b146fb46d04db2baa37da35b65751a51c76fb46b6caea8 else 0xdce8d948fa2b146e74536c7d158a373a36643e8ac51aed1b039f45628df6f2a35b657540019be20f71f4837dbc9b63d4ac51bedd0db1f45628dcef26d8fa2b14761bed1adb2baa337a36676d8ac51d46fb46b6cb3a8ddaf26d8e92b1466f7936caa1f4a3babc9a03e8ac519be20ca9f45628eeb3766cfa2b147756fb6c7d158a337ba1b64c8fa51c75e546cbc5628) else (if i < 11 then 0xdce8d92db62b1474146b407d158a38ea35aa3e8ac519bd1adb26c7d28cde8d950fa2cd46e746b6c7d166a36da36543e8ac51b9d1b2a1f45628dda8d950fa2b1466f72d1b2a158a37da35b63acbf51d44ef2a1f45628cdf107b9a03e9474146ca07d158a337a36544c8fa51d45cadb1a45628ea2826d8fa2b146fb46c90db158a337a36524c8fa51b9d1adb2647d28 else 0xcdf10868fa2b1466f7936c991a4a337bca52348ac51db5bedb1a45628dcef2a36542b1466f7936cae9a4a337bca5f348ac51b9de4db1d65628cdef26d8f52b146fb9bde52a158a337bca543a4ac51b9de52a1f45628dcef26d8f52b1466f794a869158a37da35b6574d251b9d1adb2ba7d28df68d6d8f52b1466f744a87d158a373ba1b63e8ac519be211c1f45628)) else (if i < 14 then (if i < 13 then 0xdcf37bc9b64dd466f7951b2a26ea337bca544dcfa519bd1adb2a67d28db68d6d9373e946e746ca89b9f4a337a36524dcfa51c351b20b6c5628cdef26d937225466f7936c90158a387a35b63e8ac519be2146bdc7d28dcef26d9372b147819bb6c69112a337bca07348ac51aede4db1a45628cdef26d0d22b1466f794a2db158a36dbc9b6348ac51b9de52a1a45628 else 0xcdef26d97f4dd46fb46b6cb39f4a337c42f26d937519bde53bb6c9ba8cde8d951543e9466f46cbe9b9f4a3a89de416d8ac519bdd0db26e7d28cde8d92db64dd471d46b409b9f4a387a35b64dcfa51d44eedb26e7d28ebe8d6d9313e9466f4536c9b9f4a38ecde8d7b8fa500066f794a89ba0cdef295137349466f794a8db26ea337bc9b64dccd51b9de4db26e6928) else (if i < 15 then 0xddaf26d8fa2b1471db1d1a7d158a337a366b6d963519bd1b35b2e5628ea2e59adb62b1466f46cd673958a337af28d6d8fa51dd620b89f45628cde8d6d9523e9466f46b6c7d156a364a35b63e8ac519bd94db1f45628cde8d951373e9471d9bde4db26ea337bc9b64dc45519be457936c9ba8edb37bc9b64dd466f7936c9ba62a337bc9b64dd2051e066f7936c9ba8 else 0xcdf1092cfa2b146fb744d6db158a337c42e59acac500066f46cd6aa20cde8d9ad543a5466f46cd6aa158a337a366b550fa51bed1b2a1d65628eea779acfa2b1466f884507d158a337c42c93e8ac51dd66f171f45628cde8d9acf72b1466f46cd6db2a8a000cde8d9ad63419bd1b35ac679a8e3b37a366b58d466f46cd6b19f4a337bae6b3e8ac51c751b141f45628)))) else (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then 0xeca776d8fa2b1471d882e27d158a337b6db63e8b351b7d1adb1f459a8db6db6d8fa2b146fb7436c66958a36fb6db63e8ac51bb5b6db1f45628dbe8d6d8fa2fd46df6cb6c7d158a36fa35b33e8ac51b7dd6db1f45628eca816d8fa2b1471dbed1adb2c6a359ad9b63e8ac51bed1adb26e75a8dcef29adb62b1466f794d674958a337bca543e8ac519bdb7359f45628 else 0xe3a8d838fa0f546df46cd6560b0a337bc9b64dc58519bdb6db26e7d28cdef2950ac161466f7936c74958a337b6e543e8ac51b9db6db1f45628dda8d6d8fa2b146df46b6cae9f4a37da365f2b05851bed1adb1e65628cdedb97cfa2b146df46cbe7d158a337badb63e8ac51b7dd0db1f45628ea1b65f0fa2b1471d46cbc560b0a337b6e5e6d8ac51c751ad59f45628) else (if i < 19 then 0xcd68d9acac16147513bcd6560b0a337b628d9acac519bd1b359662c28db68d9acac1614001b7db735958836fb6e6b2b05851b7db746cd65628cdf328b8ac161466f6ccd6560b0a36fa366b2b05351b7db735b6c5628cde8d9ad3716146fb46cbe7d158a337a366b3a4ac51c751aca9f45628cdee89acac16146fb9bdb735958a36fa366b3ccac519bdb7359582c28 else 0xcdedb9acc4161466f6dd1b35988a337c42413e8ac50006df46cd66220dbf37a366b311466f6dcd6db188a36fa366b3e8c451bed1adb2ba66a8e3a8d76cfa2b146df46b6cb19f4a337b65b63e8c451d4620b89f45628cde8d9acc410d466f46cd6560e4a337c6db63e8ac519be657936c9ba8e3aeb680fa2b1466f6dcd662158a36fa366b310ac519bd17359582c28)) else (if i < 22 then (if i < 21 then 0xe3a8d8a8fa2b1471d9bd1b35988a337a366b348c4519bde546cd66228cde8d9aceb31146fb9bd1b35988a337bc9b6348c451b9d1adb1f46228df68d6d8eb311466f7436c7d188a337a364b6d8c451b7db6db1f46228cdf105fcfa311466f46cbcdb188a337c85b63e88b519bd1ada1f46228cdf1b6d8fa311473346b6c7d17ca337a35b33e8c451bed1b35b6caea8 else 0x365a35b65a106cb46b6cb41f4a365a36153e8a751d46cb46b6cb428d968d854fa2b14750f736cbf9f4a3a8bbdb63e8ac51b2e6f46b6cb428df68d97d5d3ad466f46cd6620b0a337b6db63e8c451b7d1adb1f46228cde8d9de6b311466f46cd717188a337a366b3108b519bdb7359d25628cdf21a366b311466f46cd72c188a399cde8d9acc4519bd1b35b406228) else (if i < 23 then 0xd968d6d96829d46cb9be20fc9f4a38ed968d7e4fa51b2d1af336c7d28eeb655fcfa2b14774db2e27d158a337c41793e8ac51c751abc9f45628d968d6d8fa291466f46c94db158a3ba9f5b63e8ac50006cb46b6cb2a0d968d6d965295466f8bd1a7d158a365b11b63e8a551b2d1adb2ca5628d96c46d8fa2b147516c36c7d158a365cde8d6d96551d8ceedb1f453a8 else 0xcdedb698fa2b1471d46cb47d158a365a35b63e8a6519bcfadb26e7d28cde7d950fa2b1466f77b6c69158a373a365f3e8ac51d45c2db1f45628d968d848fa27d46cb61b6c7d13ea373cdef2950ac51b2d1b091f45628d96c36d8fa2b146fb7536c76158a37da36613e8ac51bedd4db1f4562800337b6e6b311066f46cc2ae9f4a337ba9b6574fa519bdd5309f45628))) else (if i < 28 then (if i < 26 then (if i < 25 then 0xcdec1840fa2b1466f46c20b2958a337b12103e8ac519ad1b081f45628cde8d841422b146b746c387d084a3a4df68d6d95d519be2749b6cb628dbe8d9acfa2b1466f883be7d158a37da36123acac519bd1b0e1f471a8cdecb6d94616d466f46c38871d6a337b06033e8ac519bd1b2a21c5628cdf1f63cfa2b1466f46b4c7d188a337a36543e8c4519bd1b341582c28 else 0xcdf105fcfa2b1466f6db6c7d17ea337a361057cac519bd82db2be5628d6e8d9acac161466f61b6caf958a37db2e8d6d95d51abdb6db1f45628cdf105fd5f2b1471d46b40af958a37dba25f6d8ac519bd96db21c4428cdeb26d95f2b1466f60c20af958a337c41f63e8ac519be20ef1f45628cdec16d90e2b1466f46cf0db2d8a337a3610428ac519bd82db2145628) else (if i < 27 then 0xdbec16d8fa2b146e746b6c7d158a2c1961b63e8ac519bde5081a45628cf6936d96c2b1466f72d1adb26ea337a365457cac51c751b2f1f45628cdf1aa34fa2b146fb7951b2f958a362a35b63e89e519be16db1f45628e3b37a35bc5b1466f46c20ae9f4a337a365f57cac51d43dcdb1f45628cdee86d95f2b1466f60cbe7d158a337a36776f16c519bd1b259583828 else 0xcdeb4814fa2b146cb9bd83081f4a3a8df68d6d95d51b2d82db1f453a8d968d6d95b3e9466f594207d158a337ad1b6518ac51b2d1adb2be4f28dc68d6d8fa2b1466f46b6caf988a337a4db65b003519bd1b081f46228ea277840fa2b1471d46c327d158a337a366b308ac519be1f46a8c5628cdedb6d95f2b146df46b6caf958a337b6e103e8ac519be2146c388728)) else (if i < 30 then (if i < 29 then 0xd96c1840fa279467b46b6c9b9f4a334bc9b6348ac51b2d8346c207d28d6e8d6d8fa2b1471d7934069158a363a35b63e89e51aed96db1f45628d5e8d870fa10946af5a4387d158a36fa366b6d8c451b2d1b019f44f28ec67d6d8fa27946cb46cbe7d13ca365ba1b63e89e51c76cb46b6cafa8eaf3da35b65b146cb46ceedb2bea3a8d968d6d95f51b2e6f60b6cafa8 else 0xd6e8d6d96c00d46cb46b6caf8dca3a3d968d6d95f51b2d1b3eb6cafa8cdecb6d97f519466f49b6c7d188a365a35b657c3d50006cb46c20afa0d968d8415f27946cb60b6caf93ca365b068d6d95f51d3596db23c7d28d96c16d95f3e946cb7536c7d13ca337b0e8d6d96c51b2d1afb36c7d28df68d6d95d22146cb46c207d07aa3b5d968d6d95f50006cb60c207d20) else (if i < 31 then 0xcdecb6d8fa2a5466f60b6cb4158a38eb6da03e8ac500066f65b6cb420cdecb6d96829d466f65c2a7d14ea3a8ae1b63e8ac51e074cdb1f45628cdeb48716c3e9466f46cd47d158a3378b9b6518ac51b2d1b3593c2c28cde936d90e2b145bf46c207d158a365a35b657c5851ccd1adb1f44f28d5eb4a361c3e946cb46cd6db2bea3afa35b63e89e51b2de546b6cafa8 else 0xae28d6d95d3e9457146cbe7d158a2e8ae1b63e8ac51bd51adb1d65628cde8d948fa2b146fb46b6c7b158a3a8ae9b63e8ac51b7d96db1f44428d968d6d90a279466f91b207d110a373bc9b6348ac51bad1b2b1f45628cdeb4950fa2b1466f4536c7d158a337b2db65609c519bde2db1f45628dda8d6d9543e9466f88597071f4a3b4a35b63acac51b6d1adb1f46228))))) else (if i < 48 then (if i < 40 then (if i < 36 then (if i < 34 then (if i < 33 then 0xd568d814fa2b14751c72e27d158a365b2db63e8a7519bd650736c7d28cde8d6d9552b1466f46b207d188a337a36692b058519bdb6c81f45628dbe8d640fa2b1466f5b4d6560b0a337c42333e8ac519bd96db1f44ea8d96b46d8fa27946cb46b6caf906a357b2db63e888519be2179438b628dd6f26d8fa2b1466f6db6ca3158a33dbca8d6d96c519bd82db26e7d28 else 0xcdecb6d9682b1471d65d1b071f4a3a6b2db65b0fa51b2d830836c7d28d668d6d90e2b146b746c067d158a337a36105b00351add1adb2d05628d6e8d854fa2b146b74536c7d158a337c41b43e8ac51d46f4db1f45628e5e8d694fa2b1474f3bb6c7d158a365a35b63e8a551b2d9746b6cafa8cde936d96c349466f65b6c7d116a365b2e8d840fa519bd1b35ad86228) else (if i < 35 then 0xd6e8d7e5b63e946b7882fe7d158a37da35b6584ac519bd96db28c5628e5e8d680fa2b1466f46c24db2d8a337a361c4387251c751ad29f45628cde8d6d9452b1471946afe7d158a35ba36053e8ac519bd17029f45628cdebda36053e947513bc0a7d158a337a3605508ac519bd26db2d84428d968a6d8fa279477546b407d158a3a88a9b63e8ac51d457adb1f44428 else 0xcde8d864fa10946fb9bd1adb2baa337a3605518ac51abd1b0e21c7d28cde8d81d462b1471d46b40a3158a337cc68d2b05b519bdb2db1f45628e268d6d9462b1466f46cbe991f4a337a2db6518ac51aad1afcb6c7d28d568d6d9462b147479bd1a560b0a337b2e153e8ac519bdd0db28c5628cde8d80d462b1466f5a36cb6006a337c9a8d3e8ac51b9d1adb26e7d28)) else (if i < 38 then (if i < 37 then 0x373bc9b64dd06e746b6ca3158a337b2db6478fa51b9d1b029f45628cdef26d8ea2b146eb46b6c9b9f4a337a35b657546519ed1b2a1f45628cde8d8155d3e946cb46c20db2bea337a365f518ac519bdd1029f45628cde8d841373e9466f60c2a7d158a337b2db651883519bd96db2d07d28d968d6d9313e946fb46b6ca0158a337bca8d81d6c51add04db1f45628 else 0xd6e8d6d95f2b146ab46c387d084a337a365f58cfa51add1b081f45628cde8d870fa1c946fb46b6caeab2a337a366b310885146cb1081f45628d6e8d6d8fa31146df46b6ca3158a337a4dbc5b0ac51b7d1b029f45628d6edb6d8fa2b146fb9bd1adb2c6a337b6db6550fa51acd1adb2d87d28cdebda36033e9466f7936c9b910a337a36054dcfa519bd1b2a28c5628) else (if i < 39 then 0xcde8d9515d3e946b765b6c7d14ea337c39b63e8c451d4482db2e25628cdf10a366b311466f46cd66217ca337c418f3e8ac51c751b009f4562800357a361c439066f65b6ca3110a38ea36415fcac51b2d1adb340afa8eeacb680fa2b1466f65c0a7d110a365a35b65189e51b2d1b029f44f28d6ecb6d8fa22146df46cd675958a337b05b6518ac519be6546b6caa28 else 0xcdf10b2db6519466f882e27d158a3a89ddb6518ac51df51adb1d64fa8d6ecba35b6519466f46c0edb2d8a337b2db65189e519bd97081f44428cdecba366b31146b765b6c7d13ca337b2db63e8a7519bd96db28c44a8cf68d9acac16146cb46b6caf910a337a4e543e8ac5172d1adb2b25628cdecb815462b146b765b6ca3158a000cdef26d937419bd97029f44e28))) else (if i < 44 then (if i < 42 then (if i < 41 then 0xea1b6628fa2b146ab65b6c7d110a000d6ecb814fa41b2de4db1a44f28d6ecb814fa22146b765c0adb1f4a39ca35b6438ac51c9d1adb1f45628cdecb6d94222140019bd1b03ad88337a35bc5b11e519bd97019f44428cde8d868fa10946b765b6c7d106a3b1ae1b63e888519bd96db28c6928cdef2958d32b146bb46b6ca3158a37da35b65749e519bd972a1f44428 else 0xcd28d6d96c00d466f46c087d158a337b2db651812519bd9702a8c44280035bb2db651906b79bd96db28ca3a8cdecb6d946519bd96db28c69a8cdecb6d9203e946b765b6ca31f4a3c0cddb634c88519bd972b1f44428dd6cb6d8fa221466965b6c7d110a38ea360e3e8a551c7596d01f44428f0337b2db6519466f65c04db1f4a337c168d57cac519bd97029f40928) else (if i < 43 then 0xcdecb6d8fa2ed46fb65b6c75910a38ea358a3e8ac519bd96db28c75a8df6db6d8eb2b1466f65b6ca09f4a3b0cddb63e888519bd1adb2ba7d28cdf1f5fcfa2b146fb9bd96db28ca337ba1b659cfa519bd1b359583728cde8d8155f2b1466f91d96db28ca337b2db651803519bd6cde1f45628ed337b2db6519466f46c207d158a337b2eb86d94651d8e6f65b6ca328 else 0xe3abda361c3e946b77936c69158a38ea36093e8ac5146cb0db2be5628cde8d8718c3e947515ec38db1f4a000d968d6d95f41c751ad01f46228cde8d7b9b63e94774bfae27d158a38ea36513e8ac519bdc946b6c5628cde8d6d8f92b146b77436c7d158a365a36103e8ac519bd1b359582da8ea27d6d8fa2b1466f46cd6b1958a337b2e6b22058519bdbb0e1f42128)) else (if i < 46 then (if i < 45 then 0xea277990fa2b1466f885e07d158a3bacdddf3e8ac519bd1b0e1f454a800371a35b65b1066f883347d158a38ea35713e8ac51dd51b049f45628eea826d8fa2b1474d46b6cb6006a000cde8d8716541d436ccb9f45628cde8d8716529546fb46cc276158a337a361c594fa519bd1b359e85628cdec4870fa29540019bd26db2d8838ecde8d87165519bd1adb21c6228 else 0xdbf37b6e6b2b1451b2fc127d158a37ba35b63acac51add96db28c4428cdf1f778fa2b146fb46b6c7a158a337a365e2b070519bdbadb1f46228dc68d6d8fa31147515eb6c7d158a000cdecb6d95841b8dbadb1f45628f0337c3cfa2b1476db2d1adb2d8a3a8905b63e8ac519bd9746b6cac2800365b05b657d066f46c38ac158a337c42bd870fa51dd4ef0e1f45628) else (if i < 47 then 0xcdedd9acfa2b1466f46c06af958a337a35bc6816c51cb51adb1f45628e3a8d6815d3e946e346cd67d158a365cdecb6d946519bd1b0e1f45328d5ecba361c3e94750db2f27d158a35ea36053e8ac51d7e6f7936c9ba8cdef2871b64dd466f46c387d08aa36da35b63e8ac51dd750b89f45628df68d871b6575466f91d1adb2b0a28d825b6574fa519bd97039f444a8 else 0xcf68d848fa2b1471d46b40b2958a38ea35a05b003519bd97029f45628cdeb4870fa2b1466f46c3887158a365a361c6d95f519be21459f45628cdef2958fa2b146cb46c387d14aa337bca545b0ac51abd1b0e1f45628e3a8d8396c3e9466f46c387d0d8a38ea36683e8ac51acd1b0e1f421a8d668d870fa2b146b765d1b029f4a337c417f518ac51b8d1b359582ca8)))) else (if i < 56 then (if i < 52 then (if i < 50 then (if i < 49 then 0xcde8d6d94631147839bd1b0e21ca335a35b657cac519bd68db2145628de737a35b62b147519ed1adb2d8a37dba25f3e8ac519bd1b0e21c2ca80033da4db65b1067b46b6cd02d8a35eb2db63e89c51bedd0db2ba75a8cdf1092ce92b146cb60c38db1f4a357ac9b63e8ac51abd1adb2ca5628d5e8d6ccfa2b1466f46c2087158a3ad9f1b63e8ac519bd69359582c28 else 0xcdecb97cfa22146fb46b6cad958a3a8ac5b63e8ac51d6ceedb1f45628cde8b870fa10946cb46ca87d13ca337a35b6434ac51d35e4db23c5628e4737a35bc5b1466f5a36c80158a337a2db65b00351af51b0e1f45628cde8d8720943947839bd1a2c086a357a35b6400ac51abd68db1f45628cdeb46d9582b1466f5a3687d158a33da36613e8ac519bd890e1f45628) else (if i < 51 then 0xcdf306d8d52b1466f46b6887158a337a366b2b058519be54db21c5628e8a8d6d9082b1467b46b6cb6084a3bea35b63b09e519bde4db3369ba8d5eb46d90e2b146eb65d1adb2d8a3a7cddb65b00351b9d96db1f44428e728d6d8fa2b1471d9bd1b20958a35ba365f3e8ac519bd1adb1f45fa8ea2816d8fa2b1471d5a3407d158a337c417f560ac51c751ad31f45628 else 0xdf68d6d9092b146af6236c7d158a337a3603508ac51d151adb1d65628cdf105fd0e2b14737bed1adb2d8a337a365f438ac51abd1b0e1f44f28003a8905b62b106af46cbe7d158a337cb1b63e8ac51abdd0db1f45628d96936d8fa27947755c36c7d158a3a4a35a03ccac51b7d1b081f45628d5e8d6acfa2b1466f8bd1a9b9f4a337a35f96d90e519bd1b0736c8728)) else (if i < 54 then (if i < 53 then 0xcdedb9acd22b146bb46b6cb6158a337ada1c3e8ac519bde4db1aa5628cde936d9a05b1466f5a3367d158a337a4e103e8ac51bed1adb2ba2128df68d6d9ab575466f46b6caea1ca373bc9b6334ac519bd96db2004428cdeb46d95d3e946af46b6cae9f4a337bc9bc348ac51dd4eebf9f4562800373bca542b106fb5a36c75958a337a35b6594ac519bd83029f45628 else 0xeea8d960fa2b1466f46ca4ae9f4a337bc9b64dc4251c751af736c7d28cdec96d8fa221466f5f51adb2d8a3a89de5f3e8ac519bd68db26e7d28cdecb6d95f221466f46c82db158a357bc9b6348ac519be60db1a45628d5e8d950fa2b1466f46cac9b9f4a337a4e563e8ac51b9d68db1f45628cdeb26d90e2b1473d46b6c7d158a000cde936f16c41b9d1b081f45628) else (if i < 55 then 0xe9af26d96c2b146cb46b6caf884a337a35f96d946519bd96db2347d28d968d840fa109466f5a36caf958a357a35b657cac519bd69081f45628d5e8d840fa2b146b760b6c7d158a37db05b63acac51abd82db1f45628e3a8d905b62b1471d46c1c7d158a357a366b2b058519bdb6db21c5628dbe8d6d90e2b146df5a36c7d158a337ac9b63e8ac5174412db1f45628 else 0xf0737a347000d466f46c3887084a38ca366b2b070519bd86db2d84fa8e473da35b65b146fbb2d1adb2b2a337b2e053e84251b9d82db1f45628e468d680fa2b1466f884ef20958a337b6dbc3e8ac51add97029f45628cde8d870fa269466f7936caa158a35ea35b63e8ac51b2d82db1f44f280037da365f57506cb46b6caf9f4a365a35b64389e51d43b2db1f45628))) else (if i < 60 then (if i < 58 then (if i < 57 then 0xcde8d87146109467b9bd1ade2d8a365b05b65b0fa519bd690e1f44428d96db6d8fa279466f46c387d138a337b2e8d8710e51b2e6f5a4387d28d6e8d6d90e2b1466f46b6cb39f4a33777db64dcfa519bd1b0e2be2128cdf10bca5e2b1466f60c387d084a365cf68d6d96c519bd1b0e2a07d28cde8d6d96c27d46eb46b6cb61f4a337ad21c3e89c519be6565b6cb628 else 0xd5e8d870fa0f546cb46b6cb62bea39ba36093e842519bde4db1a459a8dbe8d870fa109466f49b787d158a38ca366b5b0ac519bd1b0e2fe872800337b2db6519067b882fe7d158a365cde8d9acc4519bd97039f45628cdee1a35b65b1466f65bb6db1f4a357ad21c6d8fa51df71b469f45628d5f37a361c43946fb7436cb6158a337a35b3438ac519be20fc9f42128) else (if i < 59 then 0xdf68d6d8ec2b1466b46c387d084a000e3a8d7b8fa419bd1ade21c5628cde8d6ad0e2b146cb46b6c9a9f4a3a89de1c3e842519bd6346c387d28e3b37a2cfa2b1466f46c3880084a337ad21c3e812519bd1b359583828d5f37ad21c3e9466f91bbe7d084a337a361c42842519bde4db1d05628cdef26d8f72b1466f6eb6cb61f4a337b21b63e888519be20fc9f44e28 else 0xcdf30a361c439466f46c387d14aa337c8e8d8710e519bd9746cacb628cdec16d8fa2b1466f46c3887210a337a366b5fcc4519bd96db28c2c28b7e8d6d95f2b146fb46b6c84158a337ad21c43842519bd1b0e21c1ea8e6b7da35b657546fb9bd1b0e21ca357a361c43842519ed26de1f45628f0737a3459109466f46b78b60e4a371a361c3e84251d051ad51f45628)) else (if i < 62 then (if i < 61 then 0xe268d6d8fa2b146eb46b6cb6158a337b761c6d96c519bde546c388728f0737a4db65b1473746b4c7d13ca3c1cde8d6f16c519bde565b6c8f28cde8d6d96c10d466f744387d084a337a361c424fa51d436cc61f45628e6b37a34fa109466f46c38871f4a337ba1b6438ac519bd1adb2845628cde8d8710e355466f7936c69158a3a8df6cb6d96c51c751b079f45628 else 0xcde8d81d6c225466f46b78b61a4a3a7cddb6574fa51d26cb46b6cb628cde8d97cfa2b1466f6dcd6b6158a3ba6817f3e8ac519bdd0db1f45628d5e8d6d9373e9471b9bd1aaf958a337a4db65b12051abd1b0e36c8728ea337b2db65a147513bb6c87158a3bee9db63e8ac519ed2746b6cb628efb65a35b657d46fb46c3875884a337a361c5609c519be1d35ad85628) else (if i < 63 then 0xcdecb6d8fa225466f9951b35988a371a35b65b0fa51adc5cdb1f45628d968d6d95f471474d46b6ca3158a3a6c3e8d3e8ac519bd6cdb2d85628e9a8d6d8fa2b1466f794c87a958a337a36033e8ac51b7d1ad31f45628d76f2a35b65b1466f46b3687158a337a35b64dcfa519bde0db1a45628cdf10a361c5614763bed1adb2d8a39bcde8d8710e519ed26db1f45628 else 0xcde8d6d16c00d471dbdd1a7d158a337b2db65184251c6d1b3b9f45628cdf01a34fa2b1466f87afe7d158a3c1cde8d9acc4519bd82db1f46228ea3376d0fa2b146df46c96db158a36fa35b64dcfa51abd1b0e21c5628ea3346d8fa2b1467b46b6c7d158a3adac1b63e8ac519bd1ada9f45628cde939acac16146b746c0aa3158a337a36053e8ac51d351adb26e7d28)))))) else (if i < 96 then (if i < 80 then (if i < 72 then (if i < 68 then (if i < 66 then (if i < 65 then 0xcdec19acac16147739bd1a7d158a337a36615b0ac519bd1ade2d87d28cde8d6d96c33947759bc967d158a3376d11e3e8ac51df67b46b6cb628e3b65a35b6595457b46b6cac9f4a337c85b63e888519bdcadb23c5628e328d680fa2b146df46b6cb6006a37da35b657453513bb6cb31f45628cdf0f9dcfa2b1466f65b6ca3280a3a69ddb63e8ac51aed1adb1f45628 else 0xea2286d8fa2b1466f61b6c7d158a337a361c43888519bde4db2385628d668d6d96c10d466f65c0ab61f4a337b6db63e8ac51acd1ade1f45628cdf0e6d90e2b1466f7936cd026ea337b11b6594ac51e0f19469f45628e928d960ac16147513bb6cae9f4a3ba9dd713e8ac51b2d1b081f452a8e3a8d680fa2b1466f87d167d158a335a2db63e8ac519bd9746c0aa328) else (if i < 67 then 0xecad76d8fa2b1466f83b6c7d158a337b2e8d6d96851c766b469f45628cde8d6f0fa2b1471d46b667d158a38ea29b63e8ac51c651adb1f45628ee3376d8fa2b146cb9bdd4db2d8a337a366b2fc5851b9de52a36c5628cde8c6d8fa2b1466f46c0a87158a337bca8d6f16c519bdb70e1f42128cdeb497cfa2b146af46b6c87158a33da35b65b0eb51abd1adb1f45628 else 0xcdeb6870fa10d466f5a36c7d188a337a35b65b054519bd830736c7d28e328d6ccfa2b1466f46b6cb607ca337a360e3e870519bd1b0e3408728f0737c38fa2b1466f65ceedb28ca28d979b6564ac519bd1adb2145628df68d6f0eb2b1466f1740a7d158a3bde3a8d3e8ac519ad1adb1f45628cde8d871b6439466f65b687d110a334a35b43e8ac51c751af31f45628)) else (if i < 70 then (if i < 69 then 0xcde8d6d9002b1477f9be207d158a337a3610518ac519bd690e21c7d28cdf325fce92b1466ebfaa07d158a3b4a35b6500ac519bde56fb6c9ba8eea8d698fa2b1466f872fe7d158a337c3ecb478fa51d336cbf9f45628e3735a34fa2b1470b46b6c7d158a3a8af5b65b0fa50006bb46b6cb620cdef2951372b1466f87d1a7d158a37da35b6574ec519b51adb1f45628 else 0xcde8d8496c3e9471d46cef20958a3a89ddb63e8c451c6efb469f45628e9f7d6d8fa2b1466f44b6c7d158a37dcde936d96c519bd1adb2d80f28d968d6d942279466f46c387d086a337a366b3ccac519be20bf9f459a8cde8d7e4fa1c1466f46b6c7d166a36fa4db63e8ac51d3ecadb1f45628d9710a35b657d47515f36c7d158a33792db6478ac51add68db1f45628) else (if i < 71 then 0x337a36125b106ab46b6c7d158a37dcde8d8496c519be45469f42128cdecba35b651946fb9bd86db2d8a337a365f5b00351bed1adb2825628cde8d815582b1466f744207d158a3b1cdef26d96c51bed1adb1e45628cde8d8496c2b146fb46b6cb3158a337a35bc5b15951c6efb46ab25628e9f7d6d9592b147515eb6c7d14ea38ddf68d5b0ac51bed1adb2b25628 else 0xcdeb46d90e2b1466f46b6cb4158a337a36053e8c451b2d82db1f45628cde8d97cfa311466f7936c8f158a000cdef26d954419bd1b3bc388728ea2776d96c00d466f6cb6c7d17ea337a35bc5b08851aed1adb2d87d28cdf0fbc8fa2b1474d7936c7d158a337a35b35b00351d1e6f469583728cdef26d9662b1466f7943869084a337b0db65b0fa51b2d1adb34cafa8))) else (if i < 76 then (if i < 74 then (if i < 73 then 0xcde8d92db62cd46bb46b6cb6112a337a2db63e8ac519be1f46a6e7d28cdf0e9acfa2b1466f7551adb2d8a365a35b63e8a951c6ecb46ad87d28cde936d97f5b140019be21209588337bc9b6540ac51b8d1adb2d82ca8cde8d6f16c279466f46b6c991f4a337a36125b09f519bde4db26e8f28cdec1950fa2b1466f46c38db2caa3b5cddb6348ac519be1f792d85628 else 0xcde8d6d9464dd466f5a438db21ca337af68d6d95f519bd1b35aa05628cde8d9ad612b146e77936c9b9f4a357a35b6428ac519bd1b359883828e328d6d90e2b1466f65b6c7d138a37da35b65b0ec519bd1adb2d84228cde8d871b6561466f46b6cb613aa337a36565b0d3519bdb6da1f45628cde8d6d9513e9466f46b6cac158a337b05bc3e8ac51b2d1adb2beada8) else (if i < 75 then 0xea337a35bc5b1467b46b6caf958a337bca05348ac519be20f736c7d28dbe8d9ad6c2b1466f49c0a7d158a337a365f3e8bf51b7de4db1a45628d968d6d9663e9466f5b36cb6086a3a4cde8d8716c51c751ad021c5628e9f376d95f2b14001acd1adb2d882dfb05b63e8ac51ace6f46b6cb628cdebda35b6519466f5b4d6db2d8a376c417f3e8ac51c751b209f45628 else 0xe328d870fa1c1466f65c38db28ca365b05b63e88851b2d1adb1f45428e3a8d9796c2b1466f46c3887086a365a35b657d59519bd68d59f45628e3765a35593e9466f7936caa1d2a37da35b65fd5d519bd1adb2be9ba8e9f656d9593e9474fb2b6cb61f4a36fa35b63e8ac519ed1adb2d84fa8cf68d6d96c22146cb46b6cac9f4a37da35b6574ac519bdd4db2d85628)) else (if i < 78 then (if i < 77 then 0xdda8d9acfa2b146fb46b6cae9f4a33da35b65b0fa519bd1b30ad87628cde8d985b65b1466f8832e7d158a000cdeea6d96c41d451ad99f45628dce8d9acac161466f7536cb61d8a337af5b6478fa51c751b2c1f45628e3a8d838fa279466f46cc2b61f4a3a8b2e0e6d8fa519bdd4db2d87d28cde8d6d96c34d46cb46b6cb09f4a337a35b33e8ac519be51469f45628 else 0xcdf22a34fa115466f884eef71f4a365a35b657cec51b2d1adb2be75a8cde8d969b65b1466f5a36c7d158a337c424b2b05850006fb46b6cb1a0e328d8716c3e946fbb2d1adb2baa337a366b3e8c4519bd16db26e7d28df68d6d96c575466f65b6cb31f4a000cf68d6d96c419be2125ad85628d9737a35b657d467b9bd1adb2d8a36fa366b31058519bd1ade2d801a8) else (if i < 79 then 0xd5e8d7e5b63e9466f65b6c7d150a337a2cfa2b070519bde4db26e5628cde8d6d96c299466f8736c7d158a35dcde8d6d96c519ed1b0e36cb628cdf0fb2d6c3e9466f46b6cafabaa37da36053acac519bd690736c7d28cde936d96c2b1474edb3407d158a38dcde8d574fa51bed1ad99d65628cdec16d95d3e9466f88482d0158a3a6b2db63e8ac519a51adb1f45628 else 0xcde8d6d8fa30d466f6dc0a7d158a337bca8d6d937519bd1adb1f46228d968d6ccfa279466f49b6c7d158a337c417f400ac519bd26db2d87d28d6e8d6f0fa2b146cb46b6caf9a4a3a89ddb63e8ac500066f46cacb62000375a35b65b1066f46cd662158a337c422e3e8ac51add1b2a1f45628cded96d95d3e9476b9bb6c8e158a38ea365e2b053519bd96db2a07d28)))) else (if i < 88 then (if i < 84 then (if i < 82 then (if i < 81 then 0xcdef26d93700d46e346b6cb6158a38ca361c3e8ac51d4482db2fe5628cde8d870fa275467b46c387d084a355a35b6400ac51b2d1adb2d05628cdecb6d96c51946b765b6cb61f4a337ad21c438ac51abd1b0e1f452a8edb37b2db65b1466f46b78db2d8a373a35b657cac51c7610b89f45628cdef26d96c4dd466f46cc27d158a337b2e05518fa51e066edb23c01a8 else 0xdce8d870fa109466f65b6cac1f4a33da35b65fd6c51b2d1b082be7d28cdf0e8716c3e9466f46b6cb61d4a337a4e073e8ac519bde4db26e7d28cde8d6d9633e947839ed1adb2d8a000cdeb48710e419bd1adb21c5628df68d6d9a0575471b46b407d158a337b2db668146519bd1b0e1f43828cdeb46f0fa2b1466f46c3887024a337cb97f3e8ac519be3cdb1f45628) else (if i < 83 then 0xdd68d6d96c34d474fc6e6e7d158a337a35b64dd0e519be21349f456280037da35b6575071dbed1b0e2d8a337951df3e8ac51b0e6f46b6c7d28cdeb4870fa10947759bb207d158a337b968d6d95d519bdbb46b6cb628d9737a35bc5b146e6efb6c7d158a337a361257cac51aed26db1f45628d6e8d6d9002b1466f874387d0e0a337a35b65b01351d43dcdb2e27d28 else 0xcdec36d96c2b1466f91d1b35ad8a337cb99a3e8ac519be1f659f45628df6e86d95d2b1466f49b6cb6112a000cde8d9acc4419be4d46a8c5628cde8d9ae1c1c1466f46cd6db188a337a35bc5b0ac519bd1b35ad82ca8e3b37b2db6519466f46b6cb6112a337a4e776d96c51b8e6f46b6cb628ea2d76d8fa2b147513bb6cb39f4a3c0cf68d6d96c519be1cdb2d801a8)) else (if i < 86 then (if i < 85 then 0xd968d6d95f27d466f46cd66203aa33db0db63e8ac519edd4db1f45628d9737a4db65b1466f7936c7b158a38ed968d9ad6c51bb51b359d25628d7a8d870fa271466f46cbadb158a3a89ddbc3e8ac519bd96db2d844a8d968d6d9653e946cb46c20b61f4a33da35b65b15b519bd96db1f44da8d5e8d8716c3e9466f46b78b6084a33da35b65b0ec519bde549b6cb628 else 0xcf6b46d8fa2b147513c36c7d158a337a4db65b05851d5ceedb1f45628cdecb6d946479466f46c1cdb2bea357a35b6518ac51dd51b071f45628d968d6d8fa30946b346cd6db2d8a337c168d3e8ac519bd66db1f45628cdf107e4fa2b14775433407d158a38ca35b63e8c4519bd04db28c5628cde8d9acc400d471d46b427d158a337a361c438d2519bdbadb2d85628) else (if i < 87 then 0xcf68d6f0fa2b1466f883f27d110a337b75bc3e8ac51c6ecb469f45628cdf0e870fa2b1466f46cd6de2d8a337b75b65b05951b9d26db1f45628e4e8d6d8fa311451ad9ab27d158a337b2db6518fa519bd05029f45628cde9397cfa2b1466f7936c9b9a4a35ba35b6518ac51b2d82db2be5628cde8d6f0fa3114779d436c7d158a3a8cde8d9acc4500066f7936cb3a0 else 0xcde8d6c8fa2b1467b65d1adb2d8a33da4db65b0fa51c767b46b6cb628cdeb26d90a2b146ab46b6c87158a33dba1b63e8ac51b9d1ade1f45628cdee5a365f2b146cb46b6cbfabea39acde8d3e86c519bd1b0e2c27d28d9737bc9b64dd466f49c38db2d8a365c417f3e89e519bd1ade2d83828cdf2a6d8fa2b1466f46b6cb61e8a337a4db65b09e519bd26db2d88f28))) else (if i < 92 then (if i < 90 then (if i < 89 then 0xd968d840fa27947519bd26db2d8a33da35bc5b0fa51c6e6f46ad801a80037dba1b6575066f453667d158a371a35bc3e8ac519bd26db2be5628ea365bc9b65b1451ad02c27d158a35eb2db63e8ac500066f6eb6cb620d6ecb871b63e9466f89afe7d158a33db6db63e8ac5199d1adb1f45628cf68d6d96c3494774d02e27d158a337b2db664146519bd1b0e1f42128 else 0xcdf0e6d0fa2b1466f743787d158a3becde936d96c519be20ec9f45628df68d6d95d00d466f49b6cae9f4a3a8af5b63e89e519ed1adb2ba7d28df6936d8eb2b1474d4536c7d158a337a35b65b120519bd1adb2d82ca8cde8d991673e946b346b6cb6158a334a35b6574fa51add1adb2ba7d28cde8d9ae1c43947499bd1b35988a337a361c77d0e519bdd4db1f45628) else (if i < 91 then 0xcde8d8716c10d466f4536cb6006a337ad9b63e8ac519be1f46ad801a8eea77680fa2b146cb5936c7d13ca337a35bc4dcfa519ede4db1a45628cde93870fa109466f65b6cac158a337bc9b634cac519bd1b2b2d85628cf68d840fa2b1475172b6c75958a337c42cb9ad6c51bad1adb1f45628d76cb6d8fa225466f9745a7d158a37da365f5b0ac519bd1adb2d87b28 else 0x337a36615b1071d46af87d158a33da35b63e8c451cdecb46b6cafa8cde8d9acac165471d46bb27d158a337b05b6508ac519ed1adb2d84f28dbe8d6f0fa2b146b79bd97029f4a337c4e8d6d96c519bd1ade2feb628cde936f1b65b146cb46c20af958a337a35b65b0a8519ed1adb2d82c28cde8d950fa2b1466f49b6c9b9f4a38ca366b3e8ac519bd1b07b6cb628)) else (if i < 94 then (if i < 93 then 0xd968d6f0fa279466f883007d158a337a36566d96c51cde6f46b6cb2a8d6ecb6d8fa2b146bd5a36c7d158a337ad9b65b0fa519bd1adb2d83928df68d9acf32b146df7951b35958a337c39a03e8ac51c7582d01f45628d9737a36615b1466f65b6ca3240a365a35b63e89e51c7526d01f45628cde8d6d95f2b146b746b6ca1158a3bacdd7f3e8ac519bde4db1c65628 else 0xcdf1092cd22b146fb46cc87a958a3a8b95b65b0ac519a582db1f45628cdecb6d8fa221467b9bd26db2d8a337bcacb6d94651b2d1adb1f45f28cde8d8cdb65b1477dbed1adb2baa373c417f3e8ac519bd1adb28c5628df68d6d95d16146fb9bd1ade2d8a33da35b65b070500066f61b6cb620d968d6d8fa29d466b469f4560e0a365a35b657c03519bdb7359f46228) else (if i < 95 then 0xcdedd9acac165466f9951b0e2d8a3377e5b6478fa51b9cfadb1f45628cdecb870fa2714750f736cd01f4a000cde8d8710e419bd1b039f45628cd710a34fa2b14001abd690e1f48000cdeb66d96c41abd1b029f45628dcef26d96c2b1467b46c0a7d158a357a4db63e8ac51acd1b359582c28cdf0e9acac1c146eb49b6c7d158a337a35bc518ac519ed1ade2d85628 else 0xd968d6d96c27d46df6dcd67d158a337c0e8d574fa519bd1b359d45628a360e6d9593e9466f46c0a80158a33db2db63e888519ed1b2f9f45628cde93a35b65b146df882fe7d158a337c42415c4ac51add26db1f45628cde8d871583e9466f882fe9b9f4a38ea360e3e84251dd66efc9f45628cdf10b2db656147513bb6caf958a337bca8d6d967519bd1adb2c47d28))))) else (if i < 112 then (if i < 104 then (if i < 100 then (if i < 98 then (if i < 97 then 0xcde8d6f16c165467b46b6ca3158a3a89f1b63e8ac519be20cd9f45628d96c16d8fa20d466f46c0eb6158a337a29b6518ac51c751b011f45628cde936d9462b1466f46c38870e0a337b2e8d6f16c519bdd0db2d801a8cdecb815b651947579bd26db2d8a337af68d840fa519bd1b359883928d6e8d6d9373e947459bd1b0e21ca36fa36543e8ac519bd1b321f45628 else 0xcded9979b62b1466f49b78b61f4a337ad28d8710e519be20bfad801a8cdedb9acac075475172b6c7d158a357a35b65b00351c751b281f45628cde8d871bc5b1466f89d1ade2d8a337c418a3e8ac519ee2146b6cb628df68d6d95d56d47819bd1ade2d8a365a35b63e89f51b2e6f46c20afa8cd28d6d95f2b1466f7936c9b83aa337a35bc5b04351aad68db1f45628) else (if i < 99 then 0xcde8d6f15f2b1466f75cd679958a37da36103acac519be2146b78b628cde8d6d9805b1466f6236c7d158a337a35b65b0ec519bdb6db2ba7d28cf6936d96c00d467b46b6cb62b2a38ecde936d96c51dbd1adb1f45628e3a8d8e0fa2b1474f9bb6c7d158a337c42f26d95451be51adb1f45628cdeb66d90e2b1466f46cd70e188a38eb968d9acac51df66f46b78b628 else 0xd9737a361c439466f65b787d110a000cf68d6f16c419bd1b359882128cde8d6f16c161466f46c38b2958a373a35b659cfa51bee6f7936c9ba8cde8d81d6c3e9466f65d26db2d8a33da366b6d96c519bd1b3598829a8cd68d6d96c00d46cb46cc27d13ca357c417f3e8ac51b9d1adb2d801a8cde8d6f16c3ad466f45ca87d158a337a4db65b070519bd2746b78b628)) else (if i < 102 then (if i < 101 then 0xcf68d6d96c00d466f5b51adb2d8a337bca542b01d51b2e6f65c0a7d28cde8d6f15d3e9466f46cd6620b2a000cdecb8154641abd690e1f42128cdf10a366b55147198736c7d158a337bcacb6d93751d5e6f46b6cb628ea3657e5b63e9466f46c3887006a337a366b3109e51acd1adb1f45628cde8d8710e279466f46c0ab6006a337a35b65b15b51beecb46b6cafa8 else 0xdcef2a35b64dd46af46b787d158a3a7cd1b63e8ac51d3efadb2d85628ea337bc9b64dd466f98d1a560b0a3b6df68d6d95d51d8ecb46b6cafa8cde8d8716c43947379bd1b35ad8a36da35b63e8b3519a620db1f45628cdecb9adb6519466f8151af71f4a337c41fe3e8ac500066f46c38ac20cde8d854fa2b1466f49cd6db2d8a33da35b6438ac51abd1acd9f45628) else (if i < 103 then 0xcdf10a4db65b1467b46b78db2d8a337a35b43e8ac519ed1b3bb6cb628efa8d6d95900d471d46bdcbf9f4a337a36545b00351c651adb2d801a8cdef2a35b6551466f46bfcdb2d8a33da35b65b11e51d466f46c388728ea28a6d8fa2b1466f49b6cb62b2a391cde8d6d96c519be6365b6ca328a29b6564fa2b14750db2e27d158a337a366b2ecac519bde4db26e75a8 else 0xcdef26d937279466f5ed1adb284a37da365f2b05351e066f49b6cb628cde8d958fa2b1466f7936c9a958a337a35b6550fa519bd650e1f42128cde936f16c00d466f7936c9b9a6a33da35bc5b00351bedd12f9d65628cdf0fbc91e2b1466f79454db158a337a361c4385851b2d83081f45628dd737a35b65b1467b60b6c7d158a337a4db65b0d351b8d1b0e36cb628))) else (if i < 108 then (if i < 106 then (if i < 105 then 0xcde8d6d9a15b1471d9bd1b0e21ca337c8ef26d96c51d4560db1f45628ea27780cfa2b14668db23c7d158a337b05b65b003519bd1b35aba2c28e1b105c4fa2b146fb46b6c75958a37dba1b6348ac519be20fcad87d28cf68d6d96c2b1466f6eb6c7d158a375bc9b634cac51bee6f7436caea8cdedb6d96c00d466f46c247d158a38dcde8d3e8ac51bee7b46b6cb628 else 0xcde2c6d8fa2b1466eeeb6c7d158a337a358e3e8ac51b9d1adb21c5628d7a8d6d9582b1466f49b6cb6084a337a35b63e8ac519bd26db2d875a8d5e8d6d8fa311466f794d6db26ea337c2db657cac519bd1b2b2d87d28e5e8d804fa2b1466f9933669158a365a35b657cac500066f46b78b620cdef26d96c34d466f46b6cb6006a337c41903e8ac519be0546c825628) else (if i < 107 then 0xcde8d724fa2b140019bde4db2ce877da35fb6d95d519bbc4db2ba7d28a35f56d8eb2b1466f2fbc47d158a37da35b657419500071d46c8256210037da365f5750801bedd0db2ba8737a59b63e8ac519bd1adf9f4562800337c41ee3e908019be21209588400e3a8d7b8fa4200750f736c7d21a364e6d8fa2b1451afe36c7d158a28d6812f3e8ac51c751ad21f45628 else 0xcdde26d8fa2b145a146b6c7d188a2dbb41b63e8ac51bed1adb2fcaea8cde8d9ae32311466f46cd662122a337a79c63e8ac51a551adb1f4562800337a366b55108019bd1b35ac6868d885a93e8ac519bde511b6c9ba8cde8d6a5373e945e510b6c69158a337801b6348ac51b9d1ad49f4562800373bc9b64dd0e6f7936c72158a000ee9713e8ac43a051adb1f45628)) else (if i < 110 then (if i < 109 then 0xd1e8d758fa2b1466f49b6cbaad8a337a4db65b07b51add1ad71f45628d128d6d8fa2b140019bd1ade2d886a8a35b63e8ac519bc62cf1f45628cde8d6a4fa2b1451b10b6c7d158a337a35ff3e8425146c74db1f44f28cde316d95f2b146cb46b6c7d164a37dab1b63e8ac51b2d1adb2f6afa800365a361057d0d1b1cb6caf958a337a69b63e8ac519bd1ac99f45628 else 0xcde8d6d96900d466f65ce4db28ca337a91b63e8ac50006cb46b6cafa1cde806d8fa2b1467b46b6cb6062a28d9c1ae3e8ac519bcfedb1f45628cdecb6b8fa22145973836c7d110a337a35ae518ac5146ce0db28c5628a3670814fa2b1466f65b6ca30c2a337b2db63e8bd519bd96db328a32800337b2e055190e6f1a36c7d110a365a364d6d95f519bc62db1f45628) else (if i < 111 then 0x337a36125b10e6f65b6ca3252a3379edb63e8ac519bd1edb1f45628a35d16d8fa2b1466ec19f456054a337a35b83e8ac519c51adb1f45628e3a8d688fa2b1466f46b047d158a3376d9843e8ac519bd1adb9f45628cde8e6d8fa2b145ef42b6c7d158a337a161c3e842517bd1b0e1f42128bde8d6d90e2b1466f46b6c80958a337a361c78d0e519bd1ad71f45628 else 0xbde8d6d8fa2b1466f46b78baad8a337a35b65d96c500066f49b78b6210033da4db65b10e6f49c80db2d8a000cdecb6d958436851b359582c28cde8d634fa311451ae81f4560d6a28d680fa2b07851a751adb1f4562800337a366b31108019bdbadb2d88400cdef26d937420066f49b6cb6210037da35b657508019ed1adb2d88400cde8d81d6c42006bb46b6cb621)))) else (if i < 120 then (if i < 116 then (if i < 114 then (if i < 113 then 0xcdef26d9370cd451b10b6c9b9f4a37da35b65743350006df6dcd6562100337a36615b10e6f6f36c7d158a000cde8d8716543a8d96db1f45628cde8d604fa2b1466ee32fe7d158a337c41813e8ac519bd3adb1f45628cdef2718fa2b1471d9bb067d158a337a35b642cac519bd3ac09f45628cde9d71cfa2b1466ee33067d158a3379ddc63e8ac51dde6f46b78b628 else 0xcf68d6d96c0cd451b37b6c7d158a337a55b63e8ac519bdb6c69f45628cdde16d8fa2b1466f65b6ca3066a337a359e3e8ac519bd96e31f45628d968d6d95f0cd466f46b6caf834a337a35a33e8ac51b2d58db1f456289e9b648cfa2b1466ef13267d158a3a8cdd813e8ac519bd1b041f45628cde8d9acc40cd466f46b6c7d168a337a766b3e8ac519bc60db1f45628) else (if i < 115 then 0xe3a8d74cfa2b1467f46b6c7d158a347a35a03e8ac519bbb8db26e7d28e3a8d740fa2b1466f46baa7d158a28d755d03e8ac51abd1acc1f45628cdef9a361c439468f46b447d158a349a35b63e8ac51c0d1adb1f45628eef3da35b65b146b546b6c7d158a38e9e9b63e8ac51d451ad11f45628cde8d6f0fa2a9466f46c6a560b0a337a35bc5b033519bd26db2d819a8 else 0xab2a76d8fa2b146df4036c7d158a337a35b6448ac519bd1ad41f45628a36206d8fa2b1468f46cd67d158a337a761c3e8ac519bd1b121f456280037da35b658d0e6f46b6c7d180a337bc9b64dc7b519bd1adb26e3128df68d6d95d1ed466f46b987d158a33da35b65b129519bd68cc1f45628cde8d6795f2b146af42b6c7d158a310a35d03e8ac51a3d1adb1f45628)) else (if i < 118 then (if i < 117 then 0xea2a76d8fa2b1468f46afe7d158a337a366b2f0ac515636cd01f45628cde8d6d93b3e94750ed36c7d158a337a4db65b079500066f7936caa21cf68d6d8f82b146a55636c7d158a3376d9833e8ac519bd1ae41f45628cde806d8fa3114001bed1adb2ce8737a35bc5b07b519bde4db33e9ba80036fa366b3110e6f46c38870f6a365a35b657c7b519bde4d49a45628 else 0xcde8d9021c439462153b6c7d158a3516d97f3e8ac519bd0adb21c562800371a35b65b10ea346b6c7d158a37da35933acac519bd32db1f45628cdee864cfa2b1466f5636c7d158a337a35bc5b127513bb6c931f45628b428d6d8fa2b140019bd86db2d886ac9ddb63e8ac519bd96db28c3da8cde8d6d94613145ef5a36c7d158a000cde8d87158420066f6dcd66221) else (if i < 119 then 0xcdef26d9374a5466f46b847d158a365a35ed6d95f519bd1adb2667d28cf68d6d8fa2a946a37936c7d158a337a361c3e8e551bed1adb2ba94a8cdd813e8ac0b5466f51b6c7d158a000cdeb48710e439bd08db1f45628cde8d674fa2b1466f46b327d158a28d755a03e8ac519bdf4db1f45628cdf105e8fa2b140019ed1ade2d886a7a35b63e8ac500066f65b6ca321 else 0x337a361c4390d1b3836c7d158a3378ae053e8ac519bd6edb1f45628cdef2901b64dd467346b6c7d158a337a35bc3e0ac50006eb46b6cb621d0e8d6d8fa2b1466f46b447d158a337a35b64389251b951adb1f45628d968d678fa279466f883067d158a28d9ddd53e8ac519bd3abf9f45628b3e8d6d8fa2b1466f2a3b87d158a369a35b63e8ac519bda6db1f45628))) else (if i < 124 then (if i < 122 then (if i < 121 then 0xbda8d6d8fa2b1466f46b26ae9f4a365a35b657d29519bd1b35a526228a35e76d95d3e94001d4482db1588737a35cd3e8ac5146b447d1583aa8cde8d648fa2b140019bd96db2d08737bc9b64dc4b51c751acb1f45628cde31840fa2b1471d46b167d158a28d952213e8ac519bd3ad01f456280035bb2e053e90801b9de52a1588737a3598438ac519bd1b399f45628 else 0xcde936d96c4a5466f3d36c7d158a337a361c4a50e5146cbef39f45628cde8d8710e0cd467b46b6cb60f6a28d741b63e8ac51bed1adb1e25628cdecb7b5b651946a33bb6c7d158a348a35d53e8ac519bd1af6b78b628cdf10624fa2b1466f882fa7d158a337a361c7b50e50006cb46b6cb421cde8d9aded31146df46b1a7d158a337a35c33e8ac51b9bb8db1f45628) else (if i < 123 then 0xdf5e26d8eb2b1466ebf9f456060a000d6ecb6d946439bd40db1f4562800365a35b659508019bd1b2b2d88400cdeb66d96c42006af46c388721cde8d718fa2b146cb46b6caf848a37da35ed6d95d519bd1adb2ba12a8df68d901b657545831cb6c7d158a2a76d9193e8ac500066f7536cb621eef37a4db65b1466f49bdadb2d8a000d96c1840fa439ed1af6b6cb628 else 0xcde8d6d9432b146a33d36c7d158a3375fd4f3e8ac519bd1b2b9f45628d368d6d8fa2b146a356b6c7d158a337bc9ed6d93751adc56db1f45628cde936d8f82b14001abd690e1f48737b2e406d946513bb6c7d15840a8cf68d901b65b1466f46b7c7d158a3a89e5b63e8ac51b2c62db1f44f28cde8d6b4fa2b1466f46b6c6e188a337a366b900c451b2d1aea9f45628)) else (if i < 126 then (if i < 125 then 0xa3639840fa2b1466f8830c7d158a37da35d53e8ac51d4452db1f45628cde8d6d8fa2d947513d36c7d158a000cdef295137439bd1adb2945628cde8d901bc5b14001b2d82db2be8737a366b3107b519bd1adb1f46428d968d901b657d45d0f3b6c7d158a000df6e897cac439ed1adb2eab628cde2b6d9462b1466f49b6c7d154a000d668d6d96c439bd01359582c28 else 0x28d6d8fa2c90801bed1adb2fc8400cde8d8d4ac420066f7936ccfa1003376d93712d080146b6cae8328400a35b63c4ac420066ea79f4562100337624fa2b1080146b487d1588737a7db63e8ac519bd82cf1f45628cde8d6f16c4a5466f42b6c7d158a3a8aa9b63e8ac51a3d1b0e1f45628cde8d6d9032b1466f6951b35988a337a361c438db5168500db1f45628) else (if i < 127 then 0x28d8710e0cd08019bd26db2ea8400a35bc5b0334200596db28c19a10028d9acc40cd08017936c9b8668400cde8d2f0ac420066f46cd7192100337a361c78d08019bd1adb2d28400cf68d6d975420066edb2d83ca100337a35ff3e908019bd1a871b68400cde346d8fa420066edb28c30a1003376d8fa2f508019bd96db3288400cddb6390ac420051b1d36c7d21 else (if i < 128 then 0x28d6d96c0c508019bde49ba528400cde1c4387b420066f4698848a100365a35b65ed080146a5e7d1588400d968d57d29420051afab6c5621003376f16c1ed080149b6cb60668400cde8d3e8e542006fb46aba94a1003656d95f1ed08019bd26b62528400cf68d5b129420066f65a8c94a1003379acc41ed08013cb6c7d1588400cf5b65b07b420036c7d15840a1 else 0xdf5b65747b420066f46ad893a10028d6d95f09108019bd1ade2ea8400cde006d8ac420066f46b6cbb21))))))))
private def st4 (i : Nat) : Nat := unpack st4Packed 57 20 i
private def adj4Packed (i : Nat) : Nat := (if i < 5 then (if i < 2 then (if i < 1 then 0x400001420000c01420041870c104000000014c1010000160411c00c10c0040bc000300220004305638600838000000f0400440801050c0183144142 else 0x470022051810480c04000c38000030020012c08450400410c00c00c10010852412441060030410080c1000045009180245280001000181001081040) else (if i < 3 then 0x120554800705d1c004008800506b00004010040324e0420020c33410c11420020000400020010400421c600208004308a0c20000431410c0142047 else (if i < 4 then 0x4d2050030401000c00c10001492560030800c00160021c01801470020810410005820800861004c20120010c100208b0030c004501a280000003106 else 0x110504004114000040204600800110b0400c00440c0144056bc11c10c30030420420c410028914118514018e0c200200368104100a142246358045))) else (if i < 8 then (if i < 6 then 0x9a30300000b0400050020c40c300a0030c50000c20430012426400010c214000000a0860000cb0050550082400040000010820000462c06400000cf else (if i < 7 then 0x480800000801000800420010090000822430000000c02c01191090010000001850820020005800810472401c14041800c0001101044080289000046 else 0x4800b11c000000200124034024f087a0404b0011042422410011c03410030490c23c804008e20248b14140504104105004500210b5810001430c1040)) else (if i < 9 then 0x1000002410410400c51800000000051525000001414c108b00304010f10600000008e0000830420400001d00c80401001080000020c404700014d040 else (if i < 10 then 0xa3011850c60440400830001860cb0003c304808100600208b0030000020820c004d00a0090c10000c00813c104004220005404000734404070a140 else 0x10010c100c0c20006411000e40431404431020c0100bc20830030420c00051c1003041003001000185002))))
private def adj4 (i : Nat) : Nat := unpack adj4Packed 6 80 i
private def loc4Packed (i : Nat) : Nat := (if i < 24 then (if i < 12 then (if i < 6 then (if i < 3 then (if i < 1 then 0x86386829d87535291500010e0002fd9365650000009b00002e15b000097212488f6df0ef4cd9938d82a512c4a40000009ef6bc1e80005d00008dc0008800000dc4466ee0000000000000000000004279191823f45c100000000036a4186599e95c20952f086b00010b0000000003264fd00067e195000000 else (if i < 2 then 0x95a5f785e00078800028613e2fb0007ae0000003d96216090e98fa00085100073f5c629c0002760000008ac8e423700081956d35700086c00000018b00000057e1591ea14f11e0da31a7a83c996c6fd4f121a7174e62f25b96890002713aa0fe59c41c05b5c06392051744680003628430008203863431fa else 0x7d08794d20000007e257d20a00037e9655550000004a60009344864937e41e40008b15872e600090798100014300043a6ad4708c100000084e60600000000003692400000028a4480000008e94ac3ae6d10006ab33e31627201865800093944c00000017b34f67d12f15e18c0003c50b98ca1169ae000252)) else (if i < 4 then 0x19e00046d00041b7b31b60002ea83b00000027007608f0008d154600063a0004f898f68100088b3af0002316ec08948b00000096d0000000000008be78f00058c3f06510003590000000003b60ac97600000051a2fe0000670a05120000000006087cf92c0000004a13cf2060007c15b70005a1848476058 else (if i < 5 then 0x8122f482e63535822f0000912857a50000008220007707a48bc1a776a04990f00061800000000014000073b55d26785f0ee00000033d73c76b08777900000016a26300028f0b55320345e605f4c22e20001070007f600063e0005510009aa34545c2340001aa57c0004246a444763d13024787f00000058e else 0x3718390008f93b23ce0006715cd00002873425308100039a0004435bb9cc0715583367612249080000000000a27ec3103e622500062a39c5865a20005431680a77d100001400071b4526f30008ed51000000000000054420b00000092b00065d3f21bd52284c03d0000007e809c4ff00000096a00044f282))) else (if i < 9 then (if i < 7 then 0xca0005ab00000000078a2ad3220006f200007d04880d00027f42d02a0c946a8f35851e235400000000055018738300000093b1806af7d81ad52f8857164037596130008aa7fb1428e613c2a70000000009f427375224a6841c400026d0002c158940c0297ea6856320000009eb24c22a000000 else (if i < 8 then 0x2505306a171e6f162885d6fc1b59790ea6ce2d18e56b179b06a39b9c02dc2db4fb5483fd4610006a208653f5e937b4e04ed0f070319100097190d2d600035b00006f00032a8ae96f6a760395578b00052500048200049b1e637a4e39ec0230002181660000005773a70002a63ef6375e51728d70003c6223 else 0x9ca0008f000092a00080774751d0009fb0004b800036c4dc97400042106204d0003c159300000000099a0000006001154014e82091af0003470443fa9f93230000009d60002623dd4be0003ad6d84f61296d30000000000007ad2d02e365c3a36800327940004c08456ef4c70095010000000000009ea)) else (if i < 10 then 0x93f5c30002a40e237636e0004340009dd9260009970d50000000002cf0004a257800000039839f0004060005c80e000032959b2de21525921f35c0000002874a80006277de9ce20e05789113a00066600069d46b50940a00081e0004991dd0007962d200082c0af7690264d187e0009e22570000941d6 else (if i < 11 then 0x1041a87f91de23074d0f602b7351f200092764659e9f50003e372e4268bb0000005715820dd77c00001535d5dc48a0d856c72504b0000000bd00000029e0fd27400017800025171200057200094700005379d0000009b942c0002386470000001f13886a065000000052e0680009f80000000f17c8000 else 0x47331821c93700047400043c23f0002f95310007f00987bf0000003b831932b6795754b06f00000008b300097e00000000015f00034600000070a0000007bc0009d936026a99900014800099000042e0000002d70006230000008ec21e0a98238e30005e78820002bf8b200000012000089e56117a064707)))) else (if i < 18 then (if i < 15 then (if i < 13 then 0x1d19cd0000003772c250611b6b99140001df9280120000007c351174f4ce7080000000000bb7ce1770001906480005970000006e89560000000000005ce78c0e123a00092000000000000093a61d4291ce0007dc41a4a07b76680008f628e62400011826e0008d24fa8ba6f67e3216000000000000264000 else (if i < 14 then 0x8ab5de0003354800001390003bb9f000000086200065e0003f610600013500096600089384428c8264388090002012af4e100000000000000000079500000000055204a5838fd0001fc0000050650000000000000250001e31b90c60cb7cb0006220003c20000005388d56b014b3ff9fe0000006b6000000 else 0x7aa9fc00005a00094d0001ae9950007800008063ab0009e634e85b0000005998de0000004b518e60b0561640001c919b75a5053ed00061f0000000000000009c546f0fc0000b00e34a79bf7137510008039db93817e16238f65500057933b69f50f00048783390945f8e01192787d901f4a3295404236)) else (if i < 16 then 0x6e993281f17300000000000089b0170f47c400000064524800000000035388e0cd40d1472ba00000036400059611a3403a082b5f173e00000045e92566362942397b48d77d55600a12b94624354d085161a003a270e22d0000008c00000000000ae0008940002c87658cd1ac85602d91d9ba0000007b0000 else (if i < 17 then 0x4a50009421096c40000006ca6fe1f50000000004070032bc2540460001765a50d07420000009c41004423bf4d46de41d00000000000061b00036f0006ed0002ab0005cf73a6773680008f43960006bb28100058a0003b100000000b9bb0002e000070c80f00000065f87099b29458b3394755f67b18b6000 else 0x10a0003a55021cc93e5aa5675e00000001f88ad0002790009c169e00000040200040b5af48c0006c27f811f00000000086100000068d0000006400001711d94100108717a65e495f78d72a0006c66206fb09d00000000031b41e60c2441b426c37c6ae00000000019230848f1137101bc0009480006dd))) else (if i < 21 then (if i < 19 then 0x9890966f50000004f400038b3b540e0009dc3c39586ac01600087b0003ee77a0000000781c81f63289ad4b16e600020400051603f00042047f4368883b90002357680000003900000005ff3f33413502d32ce4ec6917239e87e10000005fe37f5260000000006579030005b200054a3330006e157a563000 else (if i < 20 then 0x9736679bc00000054516c0709182f80d26ff0006d900014100072674e9330000006aa00000e00087d4f380283400007f8f500050e5a95f200000050a1840c23242eb98600034d79044a8955037bb93d8244980000008040001f08d94d07000004452070000008da2bd00025e0000000006541d7760 else 0x8a77370000523c700084964d0006782290003958270000001581fd0000004ad31e6dc9ab7f200000023b11c5be30c00096174036b0002890000005d612e8c745155a54e0008363e48a495e61e00000000045600082d39d79f1100001b800000078700000000000059850da015f34af7e52c50005dd301000)) else (if i < 22 then 0x9ee2b51bb0000000000000003d63040002a27810f50001850000007290000000008960006d24967720721db8a20001c39e40001dc00000d0000005b51eb5e852a34200050b8541600001a42ef0009b454c0006e098a3ac00021717f2a35b30006c807467329824969a0005530000005d320f7d599c0000fa else (if i < 23 then 0x60e27e63013676f2aa0479b14799be9b70337c76950000000000003e50a50e867a8775a485212500000092d47700027c1991bf76d0004a95bd05c6d68846b70000002cc0000001510c800024b9af0d14d32841890004c40005f56947628531860821d88089886a93110000f752700000053b8898eb34a64e else 0x7219b399e8a348929a00072723d2331791a95207e66c37db85c99f0005423790000002222ed6330000008500000511ef2ee59a0002030ab0008477c00000007587741570009414645925280a617c55900096700021b00027d59d17d6820004d80001698a955e00000060542200087a9d280c000841000000))))) else (if i < 36 then (if i < 30 then (if i < 27 then (if i < 25 then 0x32e1317285da65a9770e74113009d50004ca00000000029b00086d4402b90004f200077505e9a424f0000000005919640003440002f61a10007b43976602b30000000002df1834f54570750000000000000006eb3c86363b74090007b632f5d70001cf2b89e00000000000008b800082527b000000000719 else (if i < 26 then 0x3e700000008e52d0009df00000035e30500041475b69030991a51b04c36688a5006179800000005075642b01500b70000001381ee00000001300025a18d00096200000031200089c5a800068a3512a83cb0001c298200000000088c1550000630240009a564f00091c9d30006cd00000000882900008d0b2 else 0x49e8354cb0007cd00000000000000047c0000002b29c26260b82138b700026500000040868300013200000018192377b7a30000001a000403784f08c8d600057400071f7ca79a0003340006387af0003616ba97d38100000006c11d79361538e0005ba68e91007900078919f1a56b43fe030000000000000)) else (if i < 28 then 0x3eb00000069700000067c0000001ca33100072037000005583719628d7a083d1e195d0003f90007676160005ad81600076400000012d86672c1030005d10005d44eb0006443bc8152b623e5336e24880610008d000000024d1ed0ff7fd9509167186dba040000002689c608800058d31f000000601154389 else (if i < 29 then 0xa0328800000067400076354097f0000000000000003032660006c500000000000030a00021d70200028b4c52cd8426990001539bd8f176e33200000000000000000094900000c0008cc0004309ac5048140f96119d80000c037419c8ee7dd0005197ed0001140005ef00001d0009692b15490000002f5000 else 0x2f10000000001d58ef55b0000000002d97b50009290000005816930a300054f49100030f8b432c0000bc26932d61496847a75400000000031c56266c00000000094c0000000000000008c800095200001b93000020081a3d400062b2e55fd6192ec27519847e08a28000000025d00000010800000045b000))) else (if i < 33 then (if i < 31 then 0x86997a00034900054165322b1e794b0005d20000000006be0000007140005684b356f00075e0009510002a00003c47850000005294ef5140005eb00043b30b81c16d8fe00000040070560a00000000000000000013b4609130c700014900013456a82f6c17997502e96926d794e0ed5a00005bc5d5355000 else (if i < 32 then 0x7c90009170003de25f8103fc8830001da00010f3560000006497d60000006cb36543996b4170000009e377f7b28580000000b64cf0009966870000002b70a100072469800000019a6e708b0000aa3917fc4c978200015d59f09f7228c300043e00600000012700001a0003d545814678e9753ec8dd3275db else 0x4bb0002c69211ec1c53ea0004e266b00070609e0000000930000006520000000ba7c595b00070d57304233f9a61c100000000015b92f55f0543730009c700052c0000000003d125b0008a851e0eb2cb4b90008f79706760000990006c045d00098e1523690009e55c70118760000000005f900000031716f)) else (if i < 34 then 0x8e700078398b03995371c3850000007cc16397c6ea5ac00000000033000000017590491b3939fd9ed7730005844b700000091e99892e0003dc3b313f79100053a00000060d7a70009940000227863b40004e73157df8d468b42a98449d3e104e00053d8213be3f800000052311729f0800200df77784b000 else (if i < 35 then 0x4923ca0001d44db0007e72ac4aa0006965d900034b0000008f811270f0000002200000000c455453911101e9120008a62ca00057062f64381394f8650000009a34250000004698ce3630000004e41c60000000003f189915a4944e59d793500039e0000009b87ee8553077c230e3cd00063b1f907c0008e1 else 0x2da00007a15c0000903e060751561a00000000077100032114e00003810266e00038d00048e0006b82a95c416b1ba0002c000059400091f0000000008280006610004377eb1cd0007ff9e10009b606e0007f547200079c9850004598c681842f12383a79e00057f0002c96c70002be000000000000)))) else (if i < 42 then (if i < 39 then (if i < 37 then 0x9c846286e0007ac62c0006d545008373000000023941698d1b300016e00000067f63100063f0000000004f90000008b08e202f2266d065b00038c0000004e90690f200013d53786764c0000e59608110cc0005a30005ec8975248bf4849870be0007f321249720212886f9f15ea9590006cc0000008fc93c else (if i < 38 then 0x70000000002329f784a2910004670000005d86e300080b00025600090b7d40000001fb0fb0000004b40000007451702c380577e0000005ca36d1447380003db3b089a0000d43a99910000ad6c90000cf6b51e95ae86a56b00066561200098c16743109295c0000000001d25b490600043f576000000557 else 0x24e0002d44850000000000594da00000061c39285a90114d00000000000018f0f82d55605fc74b49027a70188746683e53e5668316bf51c1fe09700062e0c57fe2193e900000096e50c52b00077844e7562286860000000000002929d000000046e5886f96b30ec00000069c0005bf0b1000000000000)) else (if i < 40 then 0x2ff60f0003d23d700000000000000000006b00000057b74c14c8325909057410000008ff0004540002f73750009f34b20000000009f69b580122e0002f31886255692979e70000000004f029629943200000083f6a30001c76d466d7093789cf5c900003100037d8170000001330007330000003a16041f3 else (if i < 41 then 0x42b0457558900004bf14a39989d00000018a9450007840026bd33a3870bf00067000024169b00072d8c90000003da1657531e50000000000010410005f04df9a70005c52609225e20000000002588781f726b0000008df80e7045e39000603bd90c0000004f707343542867b00049c8728c58000b49576f7 else 0x4fc46503e5ee0001b10002c483c0de38490a4134498cf3df63410d64a0430000ce80a85773687c10100004049500010c9310000003820007ba0000006410002fc00002c0000006f400064b1264d920d07b7d300000000000073100094a0009a88f23fb0008c200043d0004c30001ab0000002e86cf744000))) else (if i < 45 then (if i < 43 then 0x3e200f0000003250004124558c49a03480000c30002b40004de00000007e3f73d80007f141f00000009a00086068f49a0000001930003f500098300024006d4157e90000000667f762d00000009b405000a0223c9fa22c0001a66fa94000000068c1d04dd00031d8460e63a65b874a000194000000000 else (if i < 44 then 0x66f0004ee89f70b0004c18400004d67f48a100088d9a965600088600054700035f95439499200091197812a0000e400071572b25c0004b60005fb8af9de8e87ef7b935a8a50002453066a800000000033c6f82770501a20000009c95f45130007b883071d6694bd864000a050001372933722c76e5000000 else 0x1b759560247132003c9024639d404f3d021025577629038a7e00004fe9c33e884d51f24200094422700002700000000005d3d35350003c08d37a95a77be3370007bd1220005fa2831210000006420b31ff0000007576100000002e708400045a33800000040f9b25188cb00072f30d4c60000000000001b0)) else (if i < 47 then (if i < 46 then 0x3670009f20002614ab8fb0003a80003a40db1cb2e40004190000352140001560008735cb54b3ba5cc0001f400000034c0000007a238000073900074376c00000058000000099d4bc67219721153c4cc00090e00048371103a01c0000004ba7d75b60002d87980004786a69ff8a049f4ea0008b544475d else 0x8746b20000006da9cb50848102e88100019d0007da4d782a45300047d0003144c89635a644174844d1055ed2a100056e6642211e00d62dd7490002fa7660d30004ae0000002080000000000000006a59da7a15210009d10a41be0d90000f30007327fa5172bb67555c5b18b983800075c7c67975df792) else (if i < 48 then 0x9a100044b0000001458980c189281d00030200020c0006628590000a80000000000003132ae1d32466880000009a200000066a3cc1c08ea0006e447b1b273d0000000008db7d200081b0d700002100046c0008bd0000005361a30004d500000063c5347ab03b000746000000000000433000000000000 else 0x75f01900000007726f71a58f9435f85e1))))))
private def loc4 (i : Nat) : Nat := unpack loc4Packed 12 80 i
private def st5Packed (i : Nat) : Nat := (if i < 84 then (if i < 42 then (if i < 21 then (if i < 10 then (if i < 5 then (if i < 2 then (if i < 1 then 0xcde8d9ddb64c8fa61d44eedb1f466958c337a35b63e8ac21187519bdcadb1f45630ea2e5a35b63e8ac61d45cb3bb6c7d158c337a3677905b62b1866f46b6c7d1584d30cde8d6d8fa39cac61d46053bb6c7d158c000cde8d6d9682b1466f46b6cb41f45630ea337a36153e8ac600066f46b6cb39f4a337a35b659cfa3d5866f46b6cb39f45630cde8d991b63e8ac61d466f46b6cb39f4c3a8cde8d990fa2b1866f46cc6db1f45630 else 0x337b11b63e8ac519bd88db1f45614ac38ecde8d6d9652b1871d9bd88db1f45630cde8d6d9633e8f3600066f75b6c7d158a337badb63e8f32b1871d9bdd6db1f45630e3abda35b63e8ac61c751b3bae27d158c3bae3a776d8fa2b187519bd0cdb1f45630e1b37a35b63e8ac619bdcf46b6c7d158c3bacde866d8fa2b1866f46ceedb2845630cde8d9de033e8ac61d466f5eb6c7d158c3a8af68d6d8fa2b187515eceedb1f45630) else (if i < 3 then 0x38ea360e3e8ac51c751b0736c7d158c337a35db6d8fa2b1871d46c1cd01f45630cde8d6d9a03e8bf61c751ad01f4560a6c337a35b63e8ac0f9871d9bd1b2f1f45630e3a8d680fa2b0a561cdf1d46b407d158c3a8e3a8d680fa2b187513bb6cd01f45630cdf089ddb63e8ac619bdfd46b6c7d158c3baea28d680fa2b18750db340b89f45630cde8d7b9b6680fa619bd1adb1f474158c000cde8d6d9652b1466f46b6cb29f45630 else (if i < 4 then 0xcde8d6d8fa3c8ac61d466edb2fe7d158c337a35b6560fa2b186bd46b6c7d1584e30cdf10a19b63e8ac619be2146b6cac158c376a35b63e8e92b1866f884eed01f45630eea8d6d9a03e8ac61c76213bb6c7d158c337c42776d8fa2b1871d7f51adb1f45630cdf10b95b63e8ac61dd6213bb6c7d158c3bacde776d8fa2b1866f8851ad79f45630ea2fea35b63e8ac619bd1adb1f456152c337a35b63e8f72b1866f5936cd01f45630 else 0xe1b37c417f3e8ac619be217f2fe7d158c000eeb375fcfa2b147759be20bf9f45630cdf109dd7f3e8ac619be2146ae27d158c38ecdf105fcfa2b18750db340bf9f45630cde8d6d9af3e8ac61c751b3bafe7d158c3a8e3b375fcfa2b18775c766ebf9f45630cdf109dd713e8ac619be0546afe7d158c3a89ddb65fcfa2b18775d466ebf9f45630ea3376d9713e8ac61d451adb2e27d158c337a35ee6d8fa2b1866f46c82db2fe5630))) else (if i < 7 then (if i < 6 then 0xdf68d6d8fa3d4ac619be0d46b6c7d158c3a8a36826d8fa2b1866f46c82db3405630df737a35b63d4ac619bd9146b6c7d158c3b6cde826d8fa2b1866f46b6cbfa005630cde8d6d8fa2b01e619bd1af336c7d158c337c41f95fcfa2b1866f46b6c7d15809b000337c424b3e8ac519be2125b6c7d158c38ecde8d92cfa2b1866f46c70db1f45630cdf23c417f3e8ac619be20bf9f474958c000cdf105c4fa2b1466f882feb89f45630 else 0xdf737a35b33e8ac61bee6f46c96db158c37dcdf105fcfa2b1866f8151adb1f45630e7f37a35b63e8ac619be2146b567d158c337c42826d8fa2b1871dbed1ad01f456300037da35b63ccac51c76fb46b6c79958c37da35b63e8f32b18001c751ad59f45628e3a8d6d9ab3e8ac61c751b4136c7d158c37dcde8d6d8f32b186df9bd1adb1f45630cde8d865b63e8ac61d46fb3bb6c7d158c000df68d6d8f52b14751bed1adb1ea5630) else (if i < 8 then 0xcde8d97cfa3acac619bd1b3bcbe7d158c337a365f8b4fa2b1866f9751b2f9f45630cde8d97cfa334ac619bdd12f9f475958c337a362d6d8fa2b187518851ad01f45630ea2776d8fa3acac619bdd13bb6c7d158c337b7e8d6d8fa2b1866f46ca47d1d65630cdee86d8fa334ac619bdd0db1f475958c000ea2bd6d8fa2b140019bd1b091f4562800337b0db63e8ac519bd86db1f45613ec337b0e8d6d8fa2b1877d9bd1adb1f44fb0 else (if i < 9 then 0x37da365f3e8ac51bed1b2f9f475958c37dcde8d97cfa2b187499bd1ad59f45630df737ba1b63e8ac619be2146c967d158c337c417f3e8eb2b1866f46cbebf9f45630cde8d921b63e8ac619be217436c7d158c337a35b63e8e62b1866f9751adb1f45630cde8d979b63acac600066f46c82db158a337a365f680fa2b1866f46b6caa1f45630e3b37ba1b63e8ac619bd1b2f9f4560a6c337b65b63e8eb2b187359bd1b2f9f45630 else 0xec337a35b6574fa600066f46cbeae9f4a337a365f574fa3ad866f46b6cae9f466b000337ba1b6574fa519bdd0db2ba7d1d6c337ba28d6d95d3e986fb9bd1adb2ba5630df68d6d95d3e8ac619bd1b2faba7d158c38ea365e680fa2b186fb46b6c759584fb0efb7da35b63acac61bed1adb2fe75958c000df68d97ceb2b146fb46cbedb1d65630df68d6d9ab3acac619be4b46b6c7d158c000df6e86d8eb2b146ab46b6cbf9f45630)))) else (if i < 15 then (if i < 12 then (if i < 11 then 0xcde8d869b63e8ac61d466edb3367d158c38acde8d6d8fa2b1866f9951acd9f45630cde8d6d97f3e8b361d466f6fb6c7d158c38ea35a05c4fa2b180019bdd0db1f45628edba89ddb63e8ac61d45bf46b6c7d158c362cde8d6d8fa2b1866f46b6cd89f45630cde8d6d97c3e8ac619bd1adb2ba7d1d6c337a35b63e8ce2b186fb9bd1adb2ba7d30e3b37a35b6574fa61dd71d46b407d158c39acde8d6d95d3e9866f46ceedb2ba7d30 else 0xcdef2a365f3e8ac619bde54136c7d158c37db7e8d6d8fa2b1866f72d1adb1f45630edb37a35b63e8ac600066f7936c74958a337c42f26d8e92b1866f7936c7d1d25630cdf086d97f3e8ac619be20db3367d158c337c42df6d8fa2b1866f7951adb1d25630cde8d6d9652b0a5619be2146b367d158c337b6e8d6d8fa2b1871d7951ad01f45630ea2f26d9a03e8ac619be117936c7d158c337a35b6654fa2b1866f96d1adb1f45630) else (if i < 13 then 0xcdee5a35b6348ac61d44eedb1f469158c337a36826d8fa2b18751b9d1adb1f4563000337a35b64c8fa519bd1adb2647d19ac337a36586d8fa2b1866f46ca47d19a5630dce8d6d8fa334ac61d7ee746b6c7d158c373a35b63e8d22b186e746b6c7d1ea5630dce8d6d9aa3e8ac61d06e746b6c7d158c337a36076d8fa2b186bb46b6c7d15844b0f0337a35b63e88961aede546b6c7d158c337bca8d6d95d3e986fb7951adb1d65630 else (if i < 14 then 0xcde8d92db6348ac619bd1b2a2fe7d158c000dbe8d6d8fa2b146e746b6cbf9f45630dcf10a35b63e8ac61c751ad01f469158c373a35b6680fa2b1866f46ca2db1f45630e3b37a36543e8ac61c76e746b6c7d158c337a35b63e8d22cd86e746b6c7d1580eb0cdf22a36543e8ac619bd1b3bca87d158c337a3654940fa2b186e746ca87d1a456300037da35b6574fa51b9e6f46ca87d158c337a36506d8fa2b186e746ca8db1f45630 else 0xedb37bc9b6348ac619bde4db2fe69158c337c42f26d8d22b187519bbf2db1f45630cdef29ddb6348ac61d466f7936c69158c373bca8d6d8d22b1866f7936c759a45630df737bc9b6348ac600066f794a87d158a000dcef26d8fa2b1466f975d0db1f45630dcef26d8fa348ac61b9e6f7936c7d158c337c21b65c4fa2b1866f46ca87d1d65630cdee86d8fa348ac61bedd146b6c75958c373a35b63e8eb2b186fb9bd1b2a1f45630))) else (if i < 18 then (if i < 16 then 0xcde8d951373e8d2619bd1b2a36c9b9f4c373cde8d6d9373e9866f7936c9b9f45630cde8d6d8fa2b045619bd1adb2627d158c337a36544dcfa2b186e746b6c9b9f45630cdeeba35b63e8ac619bde4db1a456112c3c0cdef26d8d22b1866f7936cd01a45630e3b37bc9b6348ac619bde4db1a45603ac000cdef2950d22b1466f995e4db1a45630cde8d839b63e83d619bde4db1a466958c337b028d6d8fa2b1866f795bedb1a45630 else (if i < 17 then 0x337bc9b63d4ac519be651736c7d158c337a35b63e8ac275866f9251adb1f45630d8f37a35b63e8ac619be5746b6c7d158c337a35b63e8ac299866f46b6c9b9f4693000000cdef26d937419bdb2db3407d158c337a35b64dcfa3ad866f8851adb26e7d30cde8d6d9a04dcfa619be4546b6c9b9f4c3a8cde8d6d9373e980019bd1b321f45628cde8d6d9374c4fa600066f7936c9b9a4a337a35b63e8ac26d80019bd1b2a26e7d28 else 0xdf68d961b63e8ac619bd1b359f474958c337c42779acfa2b1866f8851b171f45630eeb37a366b3e8ac619be2146cb07d158c337c428d950fa2b1866f88340b89f45630cde8d9adb63a4ac619bd1adb3347d158c000cde8d97cfa2b1471d9bd1b2f9f45630cde8d9adb63ccac619bdcb46cd6db158c337c0a8d9acfa2b187513bcd6db1f45630df737ba1b63acac61e266f46b6c7d158c337a362a6d8fa2b1866f64d1adb1f45630)) else (if i < 19 then 0xdbe8d6d8fa3ccac61b7d1adb3567d158c3b2dbe8d6d8fa2b1866f5b51adb1f45630d6737a35b63e8ac619bd6d35b6c7d158c337a2e6b6d8fa2b1866f46ca4db1f45630cd68d9adb63e8ac619bd1b35b6c9b9f4c000cde8d6d9633e9466f794d6db1a45630cde8d9ae543e8ac619be21794d67d158c337a366b66cfa2b1866f7945cdb1f45630cde8d9adb6574fa61bed1b35b6c75958c337ba26b6d8fa2b1871dbed1b359f45630 else (if i < 20 then 0xecb37a35b63e8ac60006fb46b6cae958a000cde8d6d8fa2cd466f46b6c7d1660eb0df6e86d8fa3acac61b6d1adb1f45603ac36dcde8d6d8fa2b1866f46b6c7d1662c30cdedb6d8fa2b01d61b6d1adb1f4560b0c337c86db6d8fa2b187659bdb6db1f456300036fb6db63e8ac51b7db6db1f4560b0c000cded96d8fa2b1466f6cb6c7d15829b0cde8d6d8fa2fc5861b7d1adb1f4560a6c399dbe8d6d8fa2b186df46b6c7d1582c30 else 0xcde8d97cfa2b058619bdb6db1f475958c36fa35b63e8eb2b1866f882fe7d1582c30dbe8d6d97f3e8ac619bd1adb3367d158c337c426b8b8fa2b1866f885b6db1f45630dbf10a35b63e8ac619bd1b2f36c560b0c38ea35a03e8ac161866f6db6cd01f45630e3b37b6db63e8ac61c76df46b6c7d158c3a89ddb63e8ac161866f6dceedb1f45630dbe8d9ddb63e8ac619bdb146b6c7d158c3a8dbe8d6d8fa2b1866f46b6c7d1582bb0))))) else (if i < 31 then (if i < 26 then (if i < 23 then (if i < 22 then 0xcdf10a366b2b058619bd1b35b40560b0c38ecde8d9acac16186df46cd6db1582c30cdef2a366b2b058619bd1b359d6560b0c37dcde8d9acac16180019bdb7359f45628cdedb9acfa2b05861b7e6f46cd67d158c36fa366b6d8fa2b1866f7936c691582c30ea337c417f3e8ac61af62146b6c7d158c337b6db63e8d22b186df46b6c7d1a45630cde8d6d8fa3a4ac619bde56db6c7d158c37dcde8d6d9373e9871d9bd1ab89f45630 else 0xcde8d6d8fa2b08b619bdb6db1f462158c36fa35b63e8c42b1866f46cd6560b021b0f0737a366b2b058619be5346b6c7d158c337a36779acac161871d8451ad01f45630ea337a366b2b058619bd1b3136c7d158c337a366b2b0580758001b7d1b359f45628cdedb6d8fa2b05361c751b3bcd67d158c000cdef26d9372b1466f46cd7171582c30cde8d9acac1605361b7d1b40b6c7d158c36fcde8d9acac16187499bd1b359582c30) else (if i < 24 then 0xdbe8d6d8fa2b01d61bee6f46b6c7d188c37ddce8d6d8fa2b1871d9bd1adb1f46230cde8d9ddb63e8c4619bd1adb1f462116c337c868d6d8fa31187339bd1adb1f46230cde8d9acfa31058600066f6dcd6560b0a000cdedb6d8fa311466f6db6c7d1882c30cdedba35b63e8c4619bd1adb1f4620a6c000dbe8d6d8fa31146df46b6c7d1882c30dbf37a35b63e8c461bb62146b6c7d158c000cde8d9acc42b1466f46cd67d1885630 else (if i < 25 then 0xe6f37a35a63e8ac60006cb46b6c7d14ea337a35b63e8eb311866f795d0db1f45630ea365a35b63e8a761d466f6db6c7d158c3a8d967d6d8fa2b1875146cfadb1f456300035ba35b63e8ac519bddf46b6c7d158c337a366b348ac161866f8251adb1f45630cdedb6d8fa2b05860000019bd1b359888000cde8d9acfa311471d46ceedb1f45630cde8d9adb63e8c4619bd1adb1f469188c337c41b65c4fa2b1866f7951adb1f46230 else 0xcdf10a35a03e8ac61b2e6f46bf2db1f4c337bca8d6d0fa2b187513bb6cb89f45630dbe8d9acfa2b05861d46cadb2fe7d158c38ed968d698fa2b1866f46b6cbc9f45630e5737a35b63e8ac619be2146b4c7d158c3bad968d6d8fa2b1866f7fd1adb1f45630cde8d6d9a0428ac619bd1adb2647d158c000d968d6d8fa2954001c751ad31f4562800357a35b63e8ac519bd1b1436c7d158c3a8a35b6698fa2b1866f8551adb1f45630))) else (if i < 28 then (if i < 27 then 0xea2f29ddb63e8ac61beecb46b6c75958c37dd968d6d8fa27d86cb46b6c7d1584fb00037da35b63b0ac519be215eb6c7d158c337a36126d8fa2b1866f88496bf9f45630df737a35b63b0ac61c751ad01f479958c337a35b6574fa3b1866f46cc2db1f4563000337ba9b63e8ac519bdd4db1f476158c337baa8d6d8fa2b186b346b6c7d15821b0d9737a36613e8ac61b2e6f7536c7d158c365cde8d6ccfa2b186cb9bd14db1f45630 else 0xed737b05b63e8ac619bd82db31e7d158c337c7ec16d8fa2b1866f46b6cc79f45630cde8d6d98c3e8ac61b2e6f46b6c7d188c365cde8d9acac161866f6ddaedb1f45630cde8d698fa2b05861d44eedb1f45614ec365cdedb6d8fa2b1871db2d1b359f45630e9365a35b63e8ac619bd1b2d36c7d158c365cdef26d8d22b186e79bd1adb1f45630d9737a36543e8ac61b9ecb46b6c7d158c37da365f6d8fa2b1875f9bd1adb1f45630) else (if i < 29 then 0xcdf1fa36103e8ac60006fb9bd1adb2baa337b06103e8ac279866f65b6c7d15853b0e3a8d9f5b63e8ac619bd1aef36c7d158c000cde8d870fa295466f60c20db1f45630cdf0ea35b63e8ac61b9d1b35b6c7d158c337af68d6d8fa27987513bb6c7d1584f30cde8d6d9422b09e60006db46b6c7d158a337a36033e8ac27987759bd1abf9f45630cdec16d8fa2b09e619bdd12fb6c7d158c35ecde8d6d8fa2b1866f60b6c7d15853b0 else (if i < 30 then 0xcde8d841b657cac619bd82db2be5613cc37dcf68d6d8fa2b1866f46b6c7d1583730cde8d6d8fa3d8ac61d46fadb2fe7d158c337a36105fcfa2b1866f46c38db1f452b0cdef2a35b65b003619bd1b0736c7d13cc38ea35a03e8ac279866f46c20d01f45630cde8d6d90a2b09e61c762146b407d158c337af68d6d8fa20d866f46cbedb1f45630cdec16d8fa2b03d619bd1adb2feae9f4c3a8cde8d840fa2b1866f46c20ef1f45630 else 0xcde8d6d95f348ac619bd1b081f469158c337ac9b63e8ac279866f60b6c7d1a45630cde8d6d9353e8ac616fd1adb1f45613cc000d96c16d8fa2b1476b9bd1adb1f45630cde8d6d95d3e89e61bed1adb1d65613cc337a35b657ceb2b18001c751ab89f45628e8f37a36103e8ac619bd1adb2b27d158c337a35b657cac279866f46b6caf9583730cde8d9ddb657cac619bd1adb2be8e158c3bacde8d6bcfa2b186cb9bd1adb2ba7d30)))) else (if i < 36 then (if i < 33 then (if i < 32 then 0xd9737a36103e8ac600066f7951adb26ea337a35b63e8c4279866f885e4bf9f45630cde8d840fa2b09e619bd1b359584f0b0c337a35b657cac161866f46b6c7d1582db0cde8d9acfa3ccac619bd1b081f4560b0c337b05b63e8ac16186df46b6c7d1584f30cde8d6d8fa308ac61cd66f46b6c7d158c337a4e8d6d96c00d866f46cd6db2be5630cde8d9ae103e8ac619bd8335b6c7d158c28d961b63e8ac279866f7936c691584f30 else 0xcdf31a36053e8ac619bd1adb1f4560a8c000e3a8d824fa2b146cb46c20db1f44f30cde936d96c2b00361b2d1adb34c7d13cc365a35b63e89e20d86cb46cfadb1f44f30cde936d8fa3acac619bd1b35958440b0c365a35b63e8eb279866f8851b081f45630d9737a35b657c9e619bd1adb2d05614ec365cde8d6d95f3e986cb9bd82db1f44f3000365a36103e8ac519bd82db2be7d158c3b1df68d6d8fa2b186cb9bd1adb2be5630) else (if i < 34 then 0xdeb37a35b63e8ac619bd1b35b6c560e0c337c628d6d8fa2b1866f46b6cd81f45630d968d6d8fa2785861dd6fb46b6c7d158c337bca8d6d8f52b18001b2d1adb2be4f28cde8d6d9a03e8c4619bde546ca869158c337a35b63e8eb2fd86cb46b6caf9f44f30d968d6d8fa3b09e61df6cb46b6c7d13cc337bc9b6478fa2b187419bd1b2a1f45630ec765a35b63e89e619bd1adb2c27d158c365a35b63e89e0f5866f46b6cb61a401b0 else (if i < 35 then 0xcdf10ae1b63e8ac619be4746b6cb61f4c3a8b2db6680fa2b1866f84596db1f45630e3ab8a35b63e8ac61d466f46b787d158c337a36696d8fa2b187519bb6cc81f45630e2337a35b63e8ac61d45973bb6c7d158c337ae28d6d8fa2b186fb46b6c7599a563000335a35b63e8ac500066f65b6c7d14ea000cde936d96c2b140019bd1ade36cb628cde8d6d8fa2ccac61d466f65b6c7d14ec3a8b2eb86d8fa2b1871d9bd1adb26e7d30 else 0xea337bc9b63d4ac619bd1adb1f466958c000ea27d6d8fa2b147619bd1adb1f45630ea37db2db63e8ac619bd1adb26e7d1a6c000cde8d958fa2b1466f46cacdb1f45630d6e8d6d8fa2b00360006eb46b6c7d158a337b2e8d6d0fa2b1866f46b6caea347d30cdf10b2d7f3e8ac61b2d1b0836c7d158c337b2db63e8ac271866f46b6c8d1f45630cdf10b2da03e8ac600066f883207d158a3a8cde4b6d8fa2b187759bd96db1f45630))) else (if i < 39 then (if i < 37 then 0xcde8d948fa348ac61d46cb65b6c7d158c337b2e7d6d8fa2b187639bd1adb1f45630cdecba35b63e8c4619bd8346b6c7d158c337a36055b0fa2b186df65d1adb1f45630cdf21a35b63e8ac619bd1adb2647d1d6c337c42cb9acfa2b1866f46c66db1f45630cdecba36543e8ac619bde565b6c69958c337bc9b63e8d32b1876d9bd96db1f4563000337a4db63e8ac51d44eedb1f456110c37db2e8d6d8eb2b1866f7936c9b9f46930 else (if i < 38 then 0xd6f37a36053e8ac619bd1b00b6c7d158c337a4db63e8d32b1866f46cfadb1f45630edb65a35b63e8ac600066f46b6ca1158a35ba35b63e8ac20d86b746b6c7d1584430cde8d6d95d3e85361add1adb1f45614ec33dcde8d6d8fa2b18769add1adb1f45630d6e8d6d9a53e8ac61add1b3bb6c7d158c3a8cde8d6d8fa2b180019bd1adb2a87d28d968d840fa2b09e619bd9746c207d158c365a366b6d8fa27986cb9bdd0db1f45630 else 0xe3b37a35903e8ac61add1adb2fe7d158c337a35df6d8fa2b1866f46d16db1f45630d6f10a35b63e8ac61add1adb3407d158c38ea35a03e8ac221866f46c207d1584430cde8d815a03e8ac619bd6346b6c7d158c38ecde8d6d95f2b1871dadd1adb1f45630cde8d6d8fa2b087619bd1b029f456138c337a3605804fa2b18001add1b029f45628ebf37a35b64dcfa619bd9746b6cae9f4c35ba36053e8ac221866f883f2db1f45630)) else (if i < 40 then 0xcde8d6f0fa2b059619bd1adb28c56112c337bca8d6d9373e9866f46b787d1582c30cdf31a35b6518ac61d466f46b6ca3158c337a35b6519402b1866f46b6ca31580930cde8d815b6518ac619bd1adb28c56106c38ed968d6d8fa2958001add1adb28c5628cdec19ddb63e8ac619bdb2db1f4560b0c337a365f6d95d3e9866f46c0aa31f45630cdf32a35b65b0ac61b2e6f46b6c7d14ac337a36055fcfa2b1866f8851b2f1f45630 else (if i < 41 then 0xcde8d950fa2b003619bd1adb2ba7d110c334bca8d6d8fa2b180019bd1b082be5628cde8d6d9422b08361bed1adb1d656110c337a35b6518eb2b1866f46b6ca09f45630cdecb6d8fa22012619bd1adb2d87d1a6c337a35b63e8be2b186fb9bd1adb28c5630e3b37a361c3e842619bd1adb1f4620e0c337a35b65fd6c00d866f46b6c7d1585430cde826d8fa2b088619be21793367d158c37dd968d6d96c3e986fbadd1adb1f45630 else 0xe3a8d680fa3acac60006cb9bd1adb2bea337b6db63e8ac221871d9ed1adb1f45630dbe8d6d8fa2b088619be6546b6c74958c337a366b6d9462b1866f46c0a7d15841b0cde8d9ae053e8ac619bd1adb20056024c3378b9b63e8ac221866f98d1adb1f45630cde8d6d9373e888619bd1b3bc207d158c337c768d6d8fa2b1866f46c38d01f4213000000df68d6d95d41b9d1adb1f456110c35bbca8d6d8fa2b1866f46b6c8e1f45630)))))) else (if i < 63 then (if i < 52 then (if i < 47 then (if i < 44 then (if i < 43 then 0xd6ecb6d8fa2b088619bd68db1f456084c000d7a8d6d8fa2b1466f4536cb61f45630d6ecba35b63e8ac600066f5a36c87158a337a35b6518ac279866f46b6caf9584430e5f37a36053e8ac619bd1b029f45613cc337a365e6d8ac14d866f60b6c7d1584430cde8d6d8fa2b0a761b2d1adb1f44f006c337a35b63e8c422187239bd1adb1f45630ed737a35b657cac60006cb46b6caf958a337a35b6518ac161866f6dcd6db1f45630 else 0xd5ef2a35b63e8ac619bd9746b6c7d14ec337b2db63e8d2221866f79596db1f44430cdf105fcfa2b09e619be20db3207d158c337a35b65fd5f2b1866f46c20b61f45630cde8d7e5b63e812619bd1afcb6c7d110c37dd968d6d8ec2b186cb9bd96db1f44430cdf10a35b657cac619be2160b6c7d158c337a4db65b0fa2b1866f65b6ca315844300035bb2db63e8ac519bd1adb2fe7d188c337c428d6d8fa31186fbb2d1adb2d85630) else (if i < 45 then 0xf0337b2db63e888619bd96db3407d110c000dce8d950fa2b1466f5a36c871f45630d9737bca8d6d96c619bd9702b6c7d110c38ecdecb6d8fa221866f46c247d1584fb0e3b37a359b3e8ac600066f65c0a7d110a38edf68d5fcfa2b186cb5c51adb1f456300037da35b6574eb519ed1adb1f456110c337a36103e8ac20d866f91d96db1f44430d6ecba35b63e888619bd1b35b6c62158c000d6ecb6d8fa22146b79bd96db1f44430 else (if i < 46 then 0x33da35b65b0ac50006e746b6c9b9f4a37dcde8d97ceb2b180000066f65b6ca320cdf1fa35b63e8ac61bed1adb1f476158c357a35b63e8ac295871db2d1abf9f4563000000cde8d6f16c400075172b6c7d158a000cdecb6d9463e9466f46d0cdb1f45630ea337a36053e8ac61ade6f46b6ca3158c337b2e8d6d8fa271875146b6cd59f45630cdecb6d8fa34c88619bd9746c0a7d158c337a357f3e8ac1c186b746b6ca31584430 else 0xdc68d6d8fa2b05961d44eedb1f47a958c3abcde8d6d8fa2b1866f8151b0e1f45630cde8da21b63e8ac61d44ef0e36c7d158c3a8cdddf6d8fa2b1866f99620bf9f45630cdf2377db63e8ac619be3946b6c7d158c337a35b6518ac16d866f46d0edb1f45630cdf0fa356c3e8ac619bdb6db3367d158c337b2e6b6d8fa22187479bd1adb2be5630efb37a35b63b0ac619be6565b6c7d158c3abcf68d6d8fa2b186b746c0adb1f45630))) else (if i < 49 then (if i < 48 then 0xd968d6d95f3e8ac61c75cb46b6c7d158c3a8cdeb86d8fa2b1871d9bd1b0e1f452b0cde8d814fa3acac619bde546c0a7d158c337a361c3e8ac29580019bd96db1f444a8cde8d6d96c47803619be2146b6ca3158c38ecde8d77cfa2b1871d46c39049f45630ea337a4db63e8ac61c766f46c127d158c38ecde8d840fa2b1866f46c20db1f45630cde8d6d8fa2b012619bd1b35b6cb6086c337af68d871b63e9866f46b6cd29f45630 else 0xcdf108717f3e8ac600066f46c387d138a337a35b63e8c416586fb46b6cae9d65630cde8d870fa2b09c619bd82db1f475958c337c4277870fa2b180019be20ef9f45628d6e8d6d8fa2b05861e07519bb6c7d158c337c421c77cfa2b1866f46cc27d1d85630cdf10a35df3e8ac61c751b433407d158c3bacde8d870fa2b180019bd68db1f45628cdf10a36053e8ac619bd1b0e36c7d138c337c41df6d8fa2b1866f46c0adb1f45630) else (if i < 50 then 0xec737a35b63e8a7619bd1adb1f45603ac337c8a8d6d8fa2b1871d46c12db1f45630cdf10bca1c3e8ac619be477936c7d158c337ba21c6d8fa2b1866f46b6cb19f45630a36096d8fa3acac619bde546c0e7d158c337a35b63e8ac14d866f46b6c7d1584f30d5e8d6d97f3e8ac619bdbadb1f4560b2c3a8a35b6680fa2b18001b8d1adb1f45628cde8d97cfa2b08861b8e6f46b6c7d158c371a361c6d8fa2b1866f45c38db1f45630 else (if i < 51 then 0xdcf37bc9b6348ac61add1adb1f456024c337ad9b63e8ac10d80019bd1b359582ca80033da35bc3e8ac519bd9760b6c7d158c337b2e053e8ac221866f91d1b359f45630d968d6d96c3e89e619bd1adb21c56086c000cde8d6f0fa2b1466f46c38db1f421b0cde8d9adb62b059619bd1ade36c7d158c337b068d840fa2b1866f46b6c7d18801b0eeb37a35a03e8ac61bee6f46c0a7d158c337bca1c6d8d22b1866f46ca90e1f45630 else 0xcde8d9f1b63e8ac619be2165b207d158c337b2e1c6d8fa221866f46c39029f45630cdf10b2e1c3e8ac619ed1adb1f476158c337a365f3e8f32b1866f46bf2db1f45630cdf23a35b63e8ac619bdb746cd6560b0c337a361c840fa2b1871db2d1b0e1f45630d968d825b63e8ac61dd5fd46b6c7d158c39bcde8d6d8fa2b1866f6dc38db1f45630dbe8d871b63e8ac619bd1b2f9f45613cc337a366b870fa10d866f46c387d15821b0)))) else (if i < 57 then (if i < 54 then (if i < 53 then 0xd5f37ad1b63e8ac619bde546b6c9b9a4c337c428d6d8fa2b186af5a51adb1f45630cde8d6d90a3e8ac600066f5936c7d158a337ac9b63e8ac0f586fb9bd1b081f45630ea28d961b63e8ac619bd6546b6c7d158c337a35b6428ac109866f7951b2a1f45630cdecb6d8fa22083619bd64db1f456084c357a35b6698fa2b18749bed1adb1d65630cde8d9ae1c2b05961bae6f46b6c7d158c38ecde8d5fcfa2b1866f46c20af9f45630 else 0xe3b37ad1b63e8ac619bd82db2d87d158c38ed5e8d6d8fa2b1867b65d1adb1f45630cdeb49ddb63e8ac61abd1b3bb6c7d158c3a8cdeb46d8fa2b186ab46b6c7d1580930cdf109f5b63e8ac61abd1b0e36c7d158c337a4e776d8fa2b1866f72d1adb1d65630d6e8d9adb63e8ac619bd68db3207d158c337ad2b06d8fa2b1875b9bd68db1f45630cde8d8b9b63e8ac619bd68db1f45607ac337ba1b6668fa2b18001abd68db1f45628) else (if i < 55 then 0xcdf10b2db63e888619bd1adb2d87d158c3a8cde8d870fa109866f46b6c7d1aa5630cde8d950fa2b04261b7e6f6db6c7d158c337b2e776d8fa221866f884d6bf9f45630cde8d6d9083e8ac61abd1adb21c7d158c000cde8d8710e109466f46ca9171f45630cdf105fcfa2b042619bd1b081f456006c337a35b6640fa2b187499bd1adb2d85630e3b37b05b63e8ac619bd68db3407d158c357a35b6680fa2b180019bd96db28c4428 else (if i < 56 then 0xcdeb4a35b63e8ac61beeaf46b6c7d158c337a35b65fd0e2b1866f6ec38db1f45630ea337a35b657cac619be2146b6c87158c38ecde8d6d90e2b1866f9851adb21c5630cde8d6f1b65b0ac61d46fb4136c7d158c337a35b6439082b186cbadd1adb1f45630cdeb46d90e2b042619bd9746b6ca3158c337a36543e8ac075866f5a51adb21c5630cde8d6d90e2b03d60006af46b6c87158a357a367c6d8fa2b186af9bd1adb21c5630 else 0xdf68d6d8eb2b04261b9d1adb1f45613cc000df68d6d9592b1466f46b6c871d65630cde8d97cfa2b042619bdb735b6c560b0c000d668d6d8fa2b1466f5a4387d158213000337a2db63e8ac51abd68db1f456084c337a35b6574fa34980019bd1af736c7d28d5e8d6d8fa3acac61bee6f46b6c87158c337a35ab3e8ac109866f46cbe7d1a45630cdeb46d8fa3acac619bd1adb2d838006c337a35b63e8ac20d8001b2d1adb2be7d28))) else (if i < 60 then (if i < 58 then 0xcde8d6d90e348ac619bd68db1f469158c337c428d838fa2b1866f46ca87d1584430df710a35b63acac619bd1b35afe560b0c373a35b63e8ac10986af46b6c7d1a45630cde8d6d8fa38cac619bde546b6c87158c3a86d97f5c4fa2b1866f46c38c81f45630cde8d80cfa2b088619bd1acd9f456084c337bcab46d8fa2b186fb9bd1adb2ba75b0cde8d6d95d3e84261dd62146b407d158c000cde8d9adb631146dfb2d1adb1f45630 else (if i < 59 then 0xcde8d6d8fa2b03d619bd1b0e36cae9f4c365cde8d6d90e2b1866f6db6c7d1582130cdeb46d8fa2b058619bd1adb1f456006c337a4e8d6d8fa2b186af46b6c7d1582c30cdeb49adb63e8ac619bd1b0e2d87d084c337ba28d97cfa2b186af46cd6db1f45630d9737c417f3e8ac619bd1b3bca47d158c37dcdeb46d8fa2b1875b9bd1adb1f4563000337b6db63e8ac51df66f46b667d158c337bc9b6348ac10986b79bd1adb1f45630 else 0xcdf02a35a03e8ac61abd9746b6c7d158c000cde8d950fa2b1466f46b6ca315801b0cde8d9ddb6438ac61b2d1adb1f44f084c3c0cde8d6d0fa2b1866f65b6c7d11001b0eeb376d97f3e8ac619bbbedb1f469158c337a35b6438ac279866f46c067d15841b0cdedda35b63e8ac619bd1b081f456084c39bdf68d6d8fa2b1866f65d1b0736c7d30cdef26d99b348ac619be20bf9f456138c337ad1b63e8ac279866f70d1adb1f45630)) else (if i < 61 then 0xcde8d6d95d3e8ac619bd1b0e21c7d158c3a8cde826d8fa2b1866f5a51b0e1f45630d968d6d9a03e89e619bd690e36c7d158c337b2e8d6d90e2b1866f65d1adb28c4430cde8d6d8fa2b070619bd1ade2d87d158c337a35b6518ac109866f5a36c7d1584430d9737a36053e8ac61add1adb1f456084c38ea366b960fa2b1866f7436c7d1582c30cdedbb2db63e8ac61b9d9746b6c7d158c337b2eb46d8fa2b1866f65d1ade1f45630 else (if i < 62 then 0xcdf13a4db63e8ac61d466f65b6c7d110c337a361c6d90e3e9866f8851b0e1f4213000365b05b63e89e519bdb6db1f45613cc337ad21c6d8fa109866f65bbedb1f45630cdeb0a35b63e8ac61b9de546b6c7d158c337b128d6d8fa2b1866f46b6c801582130d9737a35b64dcfa619bd1b359582c084c365a35b657cac27980019bd1adb26e7d28cde8d6d97f4dcfa61d44eedb1f456084c000cde8d8710e2b1466f46c38871582130 else 0xd6e8d6d9463e8ac619bd1b0e36c7d0e0c337a35b63e8f32b180019bd690e1f42128cde8d871df3e842619be4746c387d084c337a361c3e8420f5866f46b6c7d1a45630e3a8d9dda03e8ac60006af46c387d084a337c9e8d6d8fa2b18751abd1adb1f45630e6f37a361c3e842619bd1b0e1f42c084c337a35b63e8c42f98001b9de4db1a45628df6e8a35b63e8ac619bd26db3407d158c000cde8d871b6439471d9bd1ad79f45630))))) else (if i < 73 then (if i < 68 then (if i < 65 then (if i < 64 then 0xcde8d8710e419bd1b3bb6c9b9f4c337c41a05fcfa2b180019bd1adb1f46228cde8d6d9462b08861d8e6f7936c7d158c3beea28d6d8fa2b18001d45bedb1f45628cde8d839b63e8ac600066f46cd674958a337a36546d8fa2b1866f8851b2f9f45630cde936d8fa348ac619bd1adb21c56110c000cde8d8710e3e9466f5a36cb61f45630cde8d870fa1644261e0e6f46c387d084c373a35b64dcfa349866f49b6c7d15801b0 else 0xcde8d6d8fa2b058619bde52a36c69158c3a2d5e8d6d8fa2b1866f46cbf0e1f4563000337b2e053e8ac51b2d8346b6c7d158c000cde8d6ccfa2b140019bd14db1f45628cde8da29b63e8ac61df51adb2b27d158c337ba1b63e8ac109866f46b66b61f4563000000d968d6d95f419bd7b46b6cb61f4c357cde8d870fa109866f79582db1f45630e3a8d6d9713e8ac61c751ad02fe7d158c37dcde8d870fa10986af8851adb1f45630) else (if i < 66 then 0xe8b37a35b63e8ac619ed1b3bb6c7d158c337c417f3e8ac221866f46b68b61f45630df68d9ddb63acac619be6946b6c7d158c000cde8d6d96c165466f65d1adb1f444b0f1b37a35b63e8ac61acd1b35b6c7d158c000e3737a34fa2b1471b9bd1aac9f45630cde8d6d9323e8d261bee6f65b6c7d110c365bca8d6d8fa279871b9bd1adb1f45630cde8d6d9713e8ac600074f9bb6c7d158a38dcde8d5b0fa2b1871d9bd1ad59f45630 else (if i < 67 then 0xcde8d6d8fa2b04261e0e6f45b6c7d158c337a35b6438ac04986cb9bd1adb2b27d30cdf23a35903e8ac61cde6f46cd67d158c337a35b6628fa2b186db46b6cbf9f45630cdf02a35713e8ac619bd1adb23c7d158c38ecde8d6d8fa2b1866f46b6ca31a45630cde8d9ddee6d8fa61c766f46b6ca3158c337a35b66d0fa2b180019a51adb1f45628f0334a35b63e8ac619bde4db26e69158c337bca936d8fa2b1866f8051adb1f45630 else 0xcdee86d97f3e8ac61e0e6b46b6c7d158c335a35b65b0fa2b1866f60b6c7d1582130cdef2a35b65b08961b7d1adb1f456084c337a36073e8ac225866f46b78db2d87d300033da35b65b003519be2165b6c7d138c337a35b63e8ac16586fb9bd1adb1f45630cdef26d96c348ac61cde6f46b6c7d14ac337a35b64dcfa161872fadd1adb1f45630cde8d6d8fa3d0ac60000019bd26db2d88337a35b63e8c416187799bd1adb1f45630))) else (if i < 70 then (if i < 69 then 0xe3a8d5fd713e8ac619bd1afcb6c7d084c337a35a03e8ac1c186af46b6c7d1581eb0f078ecde8d3e8ac61df71d46b6c7d158c365a35b63e8ac29d871db2d1adb1f44f30e473da35b63e8ac619bd1adb26e7d08ac000cde8d6d95f2b1467b46b6c7d1584fb0d568d6d8fa2b08861b2e6f46c387d084c337a35b63e8bf14d86af46b6c7d1584430cdf0e6d8fa2b07061c651adb1f4560e0c337a35b657cac27d87199bd1adb1f45630 else 0xdf765a35b63e89e619bd1b029f469158c000dbe8d9acac161467b46b6cbf9f45630d6f37b2db63e8ac61e066f8836c7d158c3a7cddb6564fa2b1866f5ed1adb1f44430eff37a35b63e8ac61bed1adb34075958c337a365e6d96c2b186fb9bd14db1f45630cdecb6d9463e888619bd1b0736cb61f4c337b061c6d8fa2b1866f46b6cb608401b0cde8d6d9003e8ac619bd1adb2cc7d158c337a35bc5b0ac00d871d46b40b61f45630) else (if i < 71 then 0xcde8d6d9a63e8ac619bd1adb2be7d158c337a361c6d90e10980019bd1ade2d85628003ba9ddb63e8ac519be20bfad87d158c000cde8d870fa1c1466f46ca87d1d25630cde8d9ae1c3e842619bd1adb21c560e0c337a35b657cac109866f46cd0db1f45630e8337a35b63e8ac619bde4db1a456110c337b2e8d97cfa2b1866f46b207d1582c30e3a8d6d9a63e8ac61b2d1adb1f44f110c3c0cde8d6d8d32b1866edb2fe8f1f45630 else (if i < 72 then 0xcdedb6d97f3e8ac619bd1adb2d85613ec3c5cde8d6d8fa2b1870db2d1adb1f45630e3acba35a03e8ac619bd9746b6c7d158c0000033da35b65b1066f46bdcdb2fe7d30cf737a35b65b0fa61bee6f46b6cac958c337a364b6d8ac075866f7951adb1a65630f0b37a35b63e8ac619bd1adb2d87d13ec38edf68d6acfa2b1867b46c38db1f45630df68d6d9593e8ac619be1146b6c7d158c337a3605518ac221866f88596db2d87d30 else 0xcdf10a35b6574fa600066f46b6ca3158a373a361c6d8fa2b1866f46cd70e1582c30cde8d6d96c3e88961df66f4536c7d158c337a35b66ccfa2b1866f46c96db1f45630cde8d814fa2b003600066f46c387d086a3a8cde2e6d8fa2b1866f5a36c7d1584e30cde8d6d9463e8ac61dee6f46b6c7d158c37da35b65b0eb2b1866f46b6c801584430cde8d6d8fa3d4ac619bdd0db2d87d158c000cde8d6d96c27d466f46c96db2d85630)))) else (if i < 78 then (if i < 75 then (if i < 74 then 0xdce8d6d96c3e8ac619be217936cb6158c3b1cde7d6d8fa2b1866f46c38db2be5630cde8d870fa10803619bd1adb26e7d158c337a361057cac279866f7951adb2be5630ea337bc9b65b0ac619bd9746b6c8f1f4c337bca8d6d91e2b1866f8cd1adb1f45630cdecb6d96c478fa619bd1afb36c7d158c3c1cde8d6d8fa10d866f79596db2d87d30edadfa35b63e8ac619bd1b321f47a958c3a6cde8d6d8fa2b1866f8851b049f45630 else 0x337a366b2b07051bed1b4136c75958c337a36053e8ac109866f46b6caeab27d30cf737a35bc3e8ac619bd9746cac7d158c337a35b63e8c410980019be20cd9f45628cdf32a361c3e8ac600066f46b6c87158a3a8df68d6d96c2b1866f46cbe7d15801b0cdee8b2db63e8ac619bd1adb2d84f006c397cde8d6d8fa2b1866f46b6cb61f421b0cdecb6d8fa22058619bd96db1f475910c000cde8d6d96c225466f46b6c7d1581430) else (if i < 76 then 0xcde8d871b6438ac619be20bf9f45603ac3a3cde8d6d8fa2b186cb46b6cac9f45630efb37a35b63e8ac619bd1adb1f45f958c337a361c438fa109866f65d1adb28c7d3000337a35b65b04351d8e6f65b6c7d110c337a35b64dd1e3e9866f46cbcdb1f4563000373a35b63e8ac500066f49b6cb6006a3c1cde8d6d8ac16580019bd1ada1f45628cdf10a366b5b0ac61e066f46b6c7d158c337cc2b46d8fa2b1871d9bd1b35ad85630 else (if i < 77 then 0xea365a35b63e89e61b2e6f46b6cb61d8c337a35b65b0fa3b1875146c12db1f4563000337b05b63e8ac51d46cb7936c7d158c36fb6e8d6d8fa2b18751b2d1adb2d87d30cde936f1b63e8ac619be1f46b6c7d158c337a4db63e8ac2258001b2d1adb2b27d28d9710a35b63e89e60006af46c387d158a35dcde8d6d8fa2b186cb46b6cb62b27d30cd28d6d96c3e8ac619bd1b0e1f475884c337a36146d8fa2b1866f46b6cb62ba7d30 else 0xea2776d9af3e8ac60006fbb2d1adb2d8a337bcacb6d8d22b1866f79596db1f444b0cdecb6d97f3e888600066f5b36c7d158a391cde8d6f0fa2b180019bd1adb1f45fa8cde8d9e1b63e8ac61e0e6f46b6c7d158c37da361c6d8eb2b1866f6dd1b359f45630d9737a35b63e89f619bdb6db1f474958c337b2e8d6d95f2b1866f46b6c7d1584cb0cdebea35b63e8ac61b2e6f46cbe7d158c337a35b63e8eb2b1866f46b6cd02ba7d30))) else (if i < 81 then (if i < 79 then 0xcdef0a35b63e8ac619bd16db2d87d158c337bca543e8d22b187639bd1adb2d87d30dd68d6d8fa34cac619bd1adb2d89b9f4c3add5e8d6d8fa2b1866f46b6cd02be5630cde8d6d96c34cac600066f46b6cb61a6a337b2db6478fa2b180019bde4db23c5628df737b05b63e8ac61c766f46b787d158c000d968d840fa279466f46b6cb62be56300033dcde8d6d96c519bd1adb2beac958c33da4e8d6d8fa2b187839bd1a7d1583830 else (if i < 80 then 0xea3659ddb63e8ac61b2e6f46cd6db2d8c000cdef2b2db65b146fb9bd9746b6cb630cdee5a35b65b0ac619bd1ade2d87d006c37ddbe8d6d8fa2b1866f7936c6915801b0cdee8a35b63e8ac61c751ad01f456006c38ca35b65b0fa2b1866f46cbeb61f45630ea337b2db65b0fa600066f65b6c8f1f4a337a35b65b0ec2b18001aad1adb1f45628e9337a35b63ccac619bd1b2a1f4560b0c000cde8d854fa2b1466f46b6cae9f42c30 else 0xd5e8d6d8fa2b09e61c751b35b407d158c337a35b65b0eb00d873746c12db1f45630d6e8d6d96c3e8ac619bd68db1f456024c337a35b65191e2b186af46c387d1582130cdf32a366b2b058619bd1adb2ba7d0d8c3a8cdec16d8fa2b186fb9bd1adb2d84fb0003a6a35b63e8ac50006bb46b6c7d158a000cdec1840fa2b140019bde4db26e7d28cde8d6f0fa2b08861e0e6f8851a7d158c37da35b63acac161866f46b6c7d1584fb0)) else (if i < 82 then 0xea28d839b63e8ac619bd6946c387d084c337b05b65fcfa2b1866f46c38db1f46230cde93a35bc3e8ac61dd51b3bb6c7d158c337a366b960ac16186e746ceedb1f45630cde8d6d96c3e8c4619bd1b35c38b6158c000cdef26d8d32b146db46b6c7d1a45630cde8d870fa2b070619be1946b6c7d158c337a35b63e8c42b1874f9bb6cb61f45630cde8d6d8fa2b0a5619bd1adb26e7d13cc33da35b63e8ac16187519bd1adb2d801b0 else (if i < 83 then 0xcdecba361c3e84261beecb9bd1adb2d8c37dcde8d871b65b187519bd1adb1f46230d5f37a35b63e8ac619bd7f46b6c7d158c3a8cde8d950fa2b18001c751b2c1f45628cde8d9ad6c2b070619bd1b0e36cb60b2c394cde8d6d8fa2b1866f46b6cb61f42cb0e3b37a361c5b0fa619bd1b02bbe7d158c337b968d6d8cd2b187819bd1adb2d801b0cde8d6d97f3e8ac619bd1b0e2d87d0e0c337a35b63e8ac221870d46ceedb1f45630 else 0xcde8d839b63e842619bd1b20b6c7d158c365cde8d6d8fa2b1866f46ca8b61f45630cde8d6d9093e8ac619bd1b359f4560e0c337a36543e8ac27987699bd1adb1f4563000337a366b8716c51c766f46cd679958c000cf68d6d96c3e9466f46cd70e36cb630cdeb46d97f3e8ac61d466f3eb6c7d158c337a36416d9712b180019be1f469f45628cdee86d8fa2b0886146b6cd02b27d158c337a35b63e8ac1b180019bd1b081f45628))))))) else (if i < 126 then (if i < 105 then (if i < 94 then (if i < 89 then (if i < 86 then (if i < 85 then 0xd6e8d6d8fa3acac619bd96db2d87d110c365b068d6d8fa27987513bb6c7d15801b0cde8d950fa334ac61d5e6f49b6c7d158c2b8a35b63e8eb2b186af46b6c7d1580930cde8d6d9973e8ac619bd1b3bb6c7d158c337a35b6574fa00d875146cbcdb1f45630cf737a35b65b0ac619bde546b6c7d158c000cdf108b8fa2b1466f5a36c7d15801b0edb7da35b63acac619bd1adb2be5607ac357a35b6438ac109866f46b6cbfa8c5630 else 0xcde93871b63e8ac61c76cb46b407d158c337a36776f0fa2b1866f46b6cb615844b0cdf13a35bc3e8ac619bd1b35cbe7d158c000cde936f0fa2b14001bb51adb1f45628cde936f0fa2b0036146ceedb2b27d158c33dcde936d8fa2b1866f46b6c7d1585230cf68d6f0fa2b003619bd1b35b6c7d158c337b2db6518fa2b18001d4504db1f45628cde8d6f1b65b003619bd1adb3547d158c36fa35b6680fa2b187519ed1adb1f45630) else (if i < 87 then 0xcdee86d8fa3d4ac619bd1adb3427d158c337a36103e8ac0f5866f89d1adb1f45630cde8d6d90e354ac600066f65b6ca3158a337a3677870fa1098763d44eedb1f45630cde8d6f1a03e8ac61df66f46b6cb6006c33da35b6680fa2b1871d9bd26db1f45630003a86d9713e8ac519bd9746b6c9b9f4c337a36776d9462b1876d9bd1adb2d85630cde8d6f0fa2b003600067b46b6c7d158a337a35bc3e8eb2b1866f46c06db1f45630 else (if i < 88 then 0xdd6cba35b63e8ac619ad1b0e36c7d158c000cde8d815462b146af46b6cb61f45630cdee86d8fa2b003619bd1adb1f476158c000cdf107e4fa2b1466f46bdcdb2e27d30df737a4db63e8ac619bd1adb21c7d158c000cde8d81cfa2b1466f46b6c7d15821b0cde8d6f17f3e8ac619bdb346b6c7d158c337a35b6508fa2b1866f49b6cbf9f45630cde8d6d9803e8ac619be2149b6c7d158c33dc428d6d8fa2b1866f46b6caf95841b0 else 0xcdef2a35bc3e8ac619ede546b6c7d158c3c3cde8d6d8fa2b1866f745bedb1f45630e6f37a35b65b0fa61c751ad01f456084c337b2eb86d8fa221866f9951adb1f45630cdef2a35b64dcac600066f46cd6620b0a3a4cde8d6d8fa2b1866f46b6caa1f474b0cdef26d96c478ac61bed1adb1d656006c365cde8d840fa27986b746b6c7d1584f30f03376d91e3e8ac619bd1adb26e7d19ac337a366b5b0ac161866f46cd6db1882c30))) else (if i < 91 then (if i < 90 then 0xcf68d9adb63e8ac619bd835c36c7d158c3a8e3a776d8fa2b1866f46b6c9b9f401b0ea2776d96c3e8ac619ed1adb1f469158c337a35b65b1462b1866f65d1b029f4443000337b05b657cac519bd1ade1f469158c357a35b63e8ac109867b46b78db1f45630cde8d92db62b058619bd1adb2a07d158c337a3677814fa2b180019bdbadb1f45628e3a8d680fa2b03d61b9d1adb1f456006c38ecde8d698fa2b1866f882fe7d15801b0 else 0xcf68d6d8fa2b09e619ed1adb1f456084c000cf6936d8fa2b146cb46b6c7d15852b0cde8d9acac1600361bee6f46b6caf958c337a35d96d8fa2b180019bd1b309f45628cde8d6d90e2b05861c751b0e3407d158c337bca8d871b65b18775d44eedb1f45630cde936d8fa2b05861c766f46b6cb19f4c33da4db63e8ac00d866f6db6c7d15801b0cdecba4db63e8ac619be2146bf27d158c36fa35b63e8ac00d866f46cd6de1f45630) else (if i < 92 then 0xcde8d6d9a0438ac61bed1adb2ba7d1d6c337b05b63e8ac00d80019bd1b359e65628cde8d854fa2b0a761c751b2c36c7d158c337cc28d6d8fa2b1871d9bd1b029f45630d9737a4db63e8ac619be20bf9f456024c337a361c6d9373e9870dbed1adb1f45630df737a35b65b003619bd9746b6cb61a6c365cf68d6d8fa2b1866f3bb6c8f1f45630d9737ad1b63e8ac61b2d1adb2fe7d13cc337ba1b63e8ac279871d46cbcdb1f45630 else (if i < 93 then 0xdbef2a35b63e8ac61d8d7146b6c7d158c334b2e8d6d8fa2b1866f46c387d110213000337ad21c3e8ac51c766f46c5c7d158c365d5e8d6d8fa2b18001c651adb1f45628d568d6d8fa2b042619bdb6db2d87d158c337b2db63e8ac225866f46b6caf95801b0cde8d6f0fa2b09e619bd9746cd6560b0c337a4db63e8ac279866f46c38bf9f42130e938ea35a03e8ac619bd1b029f4560b0c337a361c3e8d2109871d9bd1b2c1f45630 else 0xcdef26d8fa3d4ac61d46b746b6c7d158c33da35b65b0fa2b1874d46b6cb61f45630cde8d6d8fa34cac61d351adb23c7d158c337a35b6438ac00d87459bd1adb21c563000337a35b6574fa519bd96db1f444084c37dcdedb6d8fa2b1867b9bd1adb2d801b0cdee86d8fa2b053619bd1b0e3787d158c337a35b63e8ea2b1866f46c0a7d1580930cdecba35b65b003619bd26db1f456110c3a8c42776d8fa2b1866f46cd6621582c30)))) else (if i < 99 then (if i < 96 then (if i < 95 then 0xd5e8d6d8fa2b003600077546b407d158a337c428d8716c3e9866f882fe7d1a45630cdecb815b63e8ac619bd1adb2d8ac806c337a4e8d6d96c2b1866f46ca87d1a4563000337a36033e8ac50006cb46b6c7d13ea337a361c698fa2b186fb9bd1ade1f45630cde8d6d8fa2b09c61bed1adb1d669158c337a35fe6d8fa2b1866f8ad1adb1f45630d5f37a361c3e8ac61c351adb3407d158c337a35b65b0ac165866f79596db2d85630 else 0xea337a35b6574fa61b2e6f46b6ca3158c3a8cdee86d8fa2b187699bd1adb28c5630cdef2951b63e8ac619be1cdb2d87d158c337a35b65b05800d87519bd1adb21c5630cdecb6d8fa27888619bd1b0e4127d084c337a366b3e8ac165866f46c38db28c563000337a4e8d6d96c519bd1ade1f456084c000cde8d6f16c00d466f46c2adb1f45630f0737a35b65b003600071d46cbc7d158a337cd68d6d8fa2b1876d9bd1adb1ea5630) else (if i < 97 then 0xd6e8d9f5b63e8ac61b2d1b0e36c7d13cc337a36053e8ac2218751795bedb1f45630e6737a35b63e8ac61b2e6f46b787d158c337a35b63e8c407580019bd1adb2d8762800337a4db65b0fa519bd26db2d87d006c337a361c6d8fa2b1867b46b6cb61f401b0cde8d6d96c438ac619bde546cbcdb158c33da35b65b0ac00d866f7959746b6cb630cde8d871b65b003619ed1adb1f456006c337a36816d8fa2b1866f46b6ca11584430 else (if i < 98 then 0x337c39b63e8ac519bd1adb1f456112c337a35b63e8d12b1866f46b6cd02d801b0cde7d6d8fa348ac619bd2735b6c7d158c3a8cde8d6d9682b1871d9bd1b071f45630dce8da09b63e8ac61bed1adb2d8ac958c000cdecb6d8fa271466f65d1b35b6cb630e3b7da361c3e8ac61d3e6f46b6c7d158c355cde8d6d8fa2b180019bd1b029f45628cde8d6d96c2b04361b2d1b3bb6c7d13cc33da35b63e8eb2b186b746b6c7d1a45630 else 0xcde8d6d90e2b042600066f46b6c85158a337a36026d8fa2b1866f46b6cd028c5630cdf16a35b63e8ac619bd1b07b6c7d158c38ea3677870fa2b1871dbed1adb1d65630cde8d9adb65b003619bd1b2fcb07d158c337b068d6d95f2b1873b9bd1adb1f45630e3b37a35b65b003619bdd0db2ba7d158c36fa35b65b0fa2b1866f46b6cd59f45630cdebda35b63e8ac61d866f7436c7d158c337b5e8d6d8fa2b186f79bd1adb1f45630))) else (if i < 102 then (if i < 100 then 0xe3adfa35b63e8ac619bd1adb1f456082c337a36136d8fa2b1866f46ca8d01f45630cde8d6f0fa2b043619bd1b3bb6cb6006c365a35b63e8d2279866f46b6ca01f45630cde8d6d9582b09c61add1b0e36c7d158c365cde8d6d8fa29d866f7351adb1f456300037dba1b63e8ac51d466f46cbe7d158c337a36103e8eb2b180019bd1adb2005628cde8d958fa34cac619bd82db3407d158c337c422e6d8fa2b18751bede4db1f45630 else (if i < 101 then 0xcdf10a361c3e89c619bdd0db3407d158c3bacde8d6d8fa2b180019bd1ade2d87d28cde8d6d9373e81d61c351adb2e27d158c337a36103e8ac295866f8851ac81f45630cde8d6d8fa2ecac61b2d82db1f45613cc337a366b6d90e2b1871d9bd1afc9f45630cdf10a35bc3e8ac619bd1b0e1f421024c337bca8d870fa109866f8851adb2a87d30cde8d6d9a03e8ac61d46fb46b6c75958c000ea2b86d8fa2b1466f46cd70e2d87d30 else 0xd9737b05b63e8ac619bd82db1f456106c37dcde8d848fa2b1866f46b6cb611001b0d96cba35b63e89e619bd1b084127d158c3a4a36586d8fa2b186af46c38db1f42130cde8d825b63e8ac619bde546c207d158c337b2db6640fa221866f88568db1f45630cde8d6d90a2b03d61d457146b6c7d158c337a366b6acfa2b187759bde4db1f45630ea2776d8fa2b083600066f65d1adb28ca000cde8d6d9582b1466f46b6c7d15834b0)) else (if i < 103 then 0xdf68d6d8eb2b053619bd1afcb6cb61f4c38edf68d6d96c2b1866f49d1adb2d87d30cdf10a366b3a4ac619bd26db1f456084c376cde8d6d8fa2b1866f87d1a8f1f45630cdf10a35b65b003619be21793407d158c365cde8d6d96c00d866f7951adb28c5630cde8d6d9373e84261cdecb46b6c7d13cc000cde8d948fa2b140019bdd12f9f45628df737b0db63e8ac619bd1b0e1f44f084c373a35b63e8ac161871db2d1adb2d87d30 else (if i < 104 then 0x337b11b63e8ac539bd1adb1f4560f8c337a35b63e8ac141866f46b6c7d1985630cde8d6d8fa2b066619bd1adb1f4560cac000ea2bd6d8fa2b14801d45cadb1f45629cde8d6d8fa2b006619bd1adb1f458158c337a35b63e8ac021866f46b6c7f1f45630cde8d6f5b63e8ac600066f46b6cb4158a737a35f36d8fa2b180019bd1adb2ce7d2900337a36643e8ac539bd1adb22e7d158c337c8e8d6d8fa27187499bd1b0e1f45630 else 0x3ba9ddb63e8ac539bd1adb1f456078c337a35b63e8ac259866f46b6c9f9f45630cde8d6d8fa380ac619bd1adb23e7d158c337abe8d6d8fa2b18001c751b071f45629cde8d6d8fa2b09561c751ad01f456020c337a35b63e8ac0e9866f46b6c7d1580630ea2776d8fa2b00a619bd1adb1f458958c337a35b63e8ac039866f46b6c7f9f45630ea2776d8fa2b082619bd1adb1f45601ec337a528d6d8fa2b1866f46c8edb1f45630))))) else (if i < 115 then (if i < 110 then (if i < 107 then (if i < 106 then 0xcde8d6d8fa2b07e619bd1adb1f456146c337a35b6580fa2b1866f46b6cad1f45630cdf105fd5c3e8ac619bd1adb1f477958c337a35b63e8ac289866f882fe7d1581cb0003bacdd7f3e8ac520071d46ae27d158a400ea1b65c4fa2b148019bd1b20b6c5629cde8d6d8fa2b037619bd1adb20e7d158c337a35b63e8ac0e1866f46c9edb1f4563000337a35b6560ac52006bd46b6c7d158a737a35fd6d8fa2b18001bb51adb1f45629 else 0xdf68d6d95d42006fb9bd1adb2baa400df68d6d95d3ad48019bd1b2faba7d29cde8d6d97e3e8ac60006fb46cbe75958a400df68d97cfa2b148019bdd12f9f45629cde8d6d8fa2b093619bdd0db1f45609ac337a35b63e8af2b1866f46b6c7d1580ab0cde8d701b63e8ac619bd1adb1f45602ec337a364c6d8fa2b180019bd1b091f456290036fa35b63e8ac52006fb46b6c7a958a400ea2826d8fa2b14801b9d1adb1f45629) else (if i < 108 then 0x337c419b3e8ac520066f7936c7a958a400ea2df6d8fa2b14e6f46cbe7d15849b000337ba1b63e8ac539bd1adb1f4560a2c337a35b65c0fa2b1866f46b6c7d15802b000337a35933e8ac519bd1afdb267d158c337a35b664cfa2b180019bbc4db1f45628cddfb789b63e8ac619bd9d46b6c7d158c337a35fb6d95d3e986fb46bf6db1d65630cde8d97dfb3e8ac619bd1ac99f475958c37da35b63acac065866f46b6cbf2ba7d30 else (if i < 109 then 0xcdef288db6348ac619bd1b2a4467d158c373a36236d8fa2b1851b10b6c7d1a4563000337bc9b64dcfa520066f7936c9b9a4a737a35b667cfa2b180019bde4db26e562900337bca54348ac520066f794a87d158a400df68d6d8f32b14801b9de4db1f45629cde8d950fa2b09860006e746ca87d158a737a35b63e8ac261866f46c4edb1f4563000337a35b64c8fa53b9d1adb1f456036c341cde8d6d8fa2b1866f46ce2db1f45630 else 0xcde8d6d8fa2b052619bde4db1f45605ac337b5a8d6d8fa2b180019bd1adb1f45fa9dbe8d6d8fa2b01c619bd1adb1f456120c337a35d53e8ac1ed80019bdb6db1f45629cde8d6d8fa2b4ac61a5e6f46b6c7d158c337a35b63e8c40cd80019bd1b2a1f456290038ea36583e8ac539bd1adb1f456068c337a35b63e8ac25d866f46b6c7d15805b000337a35a93e8ac519bd1b11b527d158c337a36266d8fa2b180019bd1b291f45629))) else (if i < 112 then (if i < 111 then 0xcded2a01b63e8ac619bd1adb1f45610cc337a36806d8fa2b186d79bd1adb1f45630df68d8e5b63e8ac619bdb76936c7d158c2d0a35b63e8ac161866f46b6c9ba527d30cde8d8c9b63e8c460000019bd1b359888400cde8d6d9543e948019bd1b35b6c622900337a35b6508ac539bd1b1936c7d158c000cdedb9acac16148019bdb7359f456290036fa366b3e8ac52006db46b6c7d158a737b6db63e8ac1498001b7db6db1f45629 else 0xd968d79db63e8ac619bd972036c7d110c337a359e3e8ac27986a59bcf4db1f45630cde316d8fa2b09e619bb6cbfa327d158c00000365a35b657d0e6f46b6c7d1962630cde8d6d9464a4ac60006cb46c207d13ca400d96c16d8fa2b14ecb46b6c919f4563000337a361057cac539bd82db1f4560c6c000cf68d6d8fa2b14e6f46bf4db1f4563000337a36613e8ac52006af46b6c7d158a400ea27d6d8fa2b148019bd00db1f45628) else (if i < 113 then 0xcde8d6d92e3e8ac619bd1adb1f45604cc337a35b63e8dd2b1866f46b6c7e1f45630cde8d739b63e8ac619bd1b2036cae9f4c000cde8d958fa2b14801bad1adb1f4562900337b2db63e89c520066f5a36c7d158a737a35b6524fa2b1866f46b6c7d158223000337b2db63e8a7520066f60b6c7d158a737a35b63e8ac19d866f46b6c7d1ac5630cde8d9359e3e8ac619bd1b18b6c7d158c337bd68d6d8fa2b1866f4c51adb1f45630 else (if i < 114 then 0xcde8d6d97b57cac600066f4eb6c7d158a337a35a93e8d22b186d99bd1adb1f45630cde8d9ca053e8ac60000019bd96db28c8737a35b63e8ac0b180019bd97029f4442900337b6db63e8c452006b765b6c7d110a737a01b63e8ac16180019bd9746b6ca329cde8d6d994518ac619bd3d46b6c7d158c337a35d86d8fa2b180019bd1b02a8c5629cde8d6d9943e8ac619bd1b2a4807d158c337a36053e8e22b18001abd1adb21c5629 else 0x337a361c3e843539bd1adb2f67d158c000cdedd6d8fa2b14801b8d1adb1f45629cde8d6d8fa2b07561add1adb1f45604cc337a35b6444fa2b1866f46b6c9b9f419b0cde8d6d8fa2b047619bd1adb1f45601ac337a358d3e8ac161866f3d36c949f45630cde9d6d8fa2b02a619bd1adb35c7d158c28d9ca706d8fa2b180019bd26db2d87d29cde8d6d8fa368ac619bd1adb1f456100c337a36726d9462b1866f46ceadb1f45630)))) else (if i < 120 then (if i < 117 then (if i < 116 then 0xe3a8d8e5b63e8ac600051b10b6c7d158a337be6b46d8fa2b1866f42b6c7d158213000337a361c438fa52006b765b6c7d158a400cdeb4870fa10948019ed1adb2d8562900337a35b658cfa539bc56db1f456110c384cde8d6d8fa2b1866f46b96db1f45630cdeb46d8fa2b06861a7e6f46b6c7d158c357a35b63e8ac09d80019bd83081f45629cde8d6d8fb3e8ac619ed1b2036c7d158c337a35b63e8d92b18001b2d1adb1f452a9 else 0x38ca35b63e8ac539bd1b3d36c7d158c37da35b63e8ac1d58001d351adb1f45629cde8d71db63e8ac619bde4db1a456096c337a35b63e8ac00580019a51adb1f45629cde8d6d8fa2b05e619bd1adb30e7d158c337a5e8d6d8fa2b1866f46b6c949f4623000337a35b33e8ac539bd1b2fbda7d158c337a35b6518ac1ed866f46d0adb1f45630be6f7a35b63e8ac619bdf346b6c87158c337a35b63e8ac0ad866f46b6cb61583130) else (if i < 118 then 0xcdecb6d9193e8ac600066f46b6c7d188a400cdecb814fa2b148019bd1adb2d869a900337b2db6478fa52006cb46b6cac9f4a400cde8d6d95d3e948019bd1b359583829cfb37a35b63e8ac619bd1adb1f468158c337a35b63e8b72b180019bd1adb21c562900337bc9b6478ac520066f46b6ca3158a7a1cde8d6d8fa2b1866f46b6c7d1c256300037da35b6564ac539bd5746b6c7d158c000cde8d9acf32b14e6f49c80db1f45630 else (if i < 119 then 0x337a35b6428ac539bd1adb1f4560f2c00000337a35bc5b10e6f46b8c7d15816b0cde8d6d8fa328ac61c751af3b6c7d158c000cdecb6d9463e948019bd68db21c5629cde8d85db63e8ac600066f5b36c7d158a737a35b65d0fa2b1866f46b6cb99f45630cde8d901b657cac600066f883be7d158a737a35b65c8fa2b180019bd96db1f444a9cde8d6d8fd3e8ac600071b9bd1a7d158a737c42ad6d8fa2b180019bd1adb2d87629 else 0x337a361c438ac53dde7b46b6c7d158c337a35b63e8ac1a180019bd1ade2d801a900000cde936d96c420066f79596db2d8a400df68d6d8ec2b14e6f46b88db1f45630cdefca35b63e8ac600066f49d1adb2d8a400cf68d6d96c00d4e6f46c387d1b62130cde8d78db63e8ac600066f49b6cb6158a737a361f6d8fa2b1866f46b72db1f4563000337a4dbc3e8ac539bd26db1f4560f2c337a428d6d8fa2b1866f46b6c7d15813b0))) else (if i < 123 then (if i < 121 then 0x33da35b65b0fa539bd1adb1f4560bac000cde8d9ace92b14e6f46bac7d15835b00038ea35ab3e8ac539bd1adb1f45605ac337a35b6410fa2b1866f46b8cdb1f45630cde9e6d8fa2b02d619bd1adb1f46a158c000d968d6d95f3e94e6f6ad1adb1f4563000337a35813e8ac51b2d1b26b6c7d13cc337a7a8d604fa2b1866f46b027d15819b000337ba1b6574fa52006b746b6c7d158a78ed228d6d8fa2b187779bd1ade1f45630 else (if i < 122 then 0xcde776d8fa2b02d619bd1adb1f4560c0c337a35a03e8ac0a9871d46b40981f45630e3b37a35c73e8ac619bd1b2336c7d158c337a35b63e8ac0a9866f46b6c811f45630cde8d9021c3e842619bd1adb1f45d158c337a75b63e8ac0cd86af46b6c7d15819b0cde8d9c9ae3e8ac619bd1adb1f4560b4c000df68d6d95d3e94e6ee3b6cc19f45630cde8d6d9833e8ac619bda146b6c7d158c000cdef2a35b64dd4f519bd3cdb1f45630 else 0xcde8d6d8fa2b046619bd1adb1f4560acc337a35b6574fa0cd866f46b6c7d15850b0cdee86d8fa2b033619bd1b2036cb6006c337a35b6418fa2b180019bd86db1f45629cde8d819b63e8ac619bd1adb1f4560b8c337a35b6578fa2b180019bd1adb26e7d2900337a365f3e8ac52006b746c0a7d158a73da35b63e8ac0c5866f46b6c9e1f45630cdf105fcfa2b033619bd1adb1f456060c337c528d6d8fa2b18001b9de4db1a45629)) else (if i < 124 then 0xcde8d6d8fa2b01a619bd1adb20a7d158c337a35d46d8fa2b1866f46b6c7d1f0563000337b05b657cac53bed1b2036c75958c337a365f3e8ac0cd868f46b6c7d1583db0dbe8d6d9293e8ac619bd1adb1f45604ac337a35b63e8ac231866f6db6c7d15819b0dbe8d6d8fa2b033619bd1af936c7d154c000cde8d951373e94e6f46cd67d1581530cde8d9b5b63e8ac619bd5b46b6c7d158c000cde8d6b8fa2b1466f46b6c7d15810b0 else (if i < 125 then 0xcde8d6d8fa2b029600066f18b6c7d158a000dbe8d6d8fa31148019bb6cc19f45628cde8d6d9462b033619bd1b029f456066c35ba35b63e8ac0cd866f46b6c7d1580b30cde8d6d8fa2b08d619bd1adb2be56066c365a35b63e89e0cd867b46b6c7d1583db0cde8d6d8fa388ac619bd1adb1f44f034c000cde8d9acac1654801acd1adb1f45629cde8d6d8fa2e4ac619bd1adb3447d158c337a35b6538fa2b186cb9bd1adb1f45cb0 else 0xcde8d688fa2b07b619bd1adb2d819806c3a8a35e76d8fa2b1866f46b6c8315812b0cde8d6f0fa2b033619bd1adb1f456092c337a35b65b0fa069866f46b6c7d1581930cdde26d8fa3acac619bd1adb26e7d0f6c337a35b65bcfa2b1866f46c387d08419b0cde8d6d9a93e8ac61c751ad02527d158c337a35b63e8d72b1866f46b6c8715819b0cde8d6d8fa2b014619bd1b0f36c7d158c337a35b63e8ac155868b9bd1adb1f45630)))))) else (if i < 147 then (if i < 136 then (if i < 131 then (if i < 128 then (if i < 127 then 0xa35d06d8fa2b07b619bd4546b6c7d158c28d9ddb63e8ac1d5866f46afe7d1581530cde8d6d97d3e8ac61d469146b6c7d158c337a35b6530fa2b185a56851adb1f45630cde8d6d94b3e8ac619bd1adb1f464958c337aee8d6d8fa2b180019bd1aea9f45628cde8d755b63e8ac600066f46b6cb2958a737a35b63e8ac281866f46bd0db1f45630cde8d6d8fa2a80360006df46cd6560b0a737a366e6d8fa2b180019bd1b0e1f43829 else 0xcde8d6d8fa3b8ac60006e746b6c9b9f4a737a35b63e8ac1e180019bd26db1f45629cde8d7d1b63e8ac61c966f46b6c7d158c337a35c73e8ac0a98001a3d1adb1f45628cdeb46d8fa2b033619bd1adb1f460958c337a35b6430fa2b1866f46b6c7d1581130cded2a35b63e8c461a3e6f46b6c7d158c3bbcde8d6d96c00d80019bd1ade1f45629cde8d6d8fa2b04e619bd1adb1f456094c337a35d06d8fa2b187059bd1adb1f45630) else (if i < 129 then 0xcdef2a35b63e0ac61a366f46b6c7d158c000df68d6d95d2b14801b2d1adb1f44fa9cdf10a35d63e8ac619bd1b2e36c7d158c28d9c1b63e8ac221866f5351adb1f45630cdec2a35b63e8ac6146b6cd01f4560eac337a35b669cfa2b1866f46b6c7d1583530cdee3a35b63e8ac619bd1adb1f4560eec337a35d36d8fa2b1871d9bd1aeb1f45630cde8d6d8fa2b07d619bd973936c7d110c000cdef26d8e92b148019bd0adb1f45628 else (if i < 130 then 0x38ea365e3e8ac53bee6f46b6c83158c000e9f376d8fa2b14e6f7951adb22a5630cde8d6d95d3e87b60006cb9bd1adb2bea737a35b63e8ac1fd866f46b6c961f456300033da4db63e8ac53bed1adb1d6560f6c337a365f3e8ac1ed866f46b6c881f45630cde8d9d9b63e8ac61bfe6f46b6c7d158c347a35b63e8ac1ad86fb46bdadb1d65630cdeb47b5b63e8ac619bde52036c69158c337a35cf6d8fa2b1866f46c76db1f45630 else 0xcde8d911b63e8ac619bd1adb1f45600ec342cde8d6d8fa2b1866edb3067d15819b0cde8d6d8fa314ac619bd8326b6c7d158c337a35b63e8ac0d5866f46b6c7d1883db000000cdef26d937439bd1adb1f456004c337a366b2b07b161866f46b6c7d1583230cde8d6d9133e8ac619bd1aed36c7d158c000cde8d814fa2b14e6f46b6cbd1f45630cde8d935b657cac619bd1adb1f4560e8c337a35b63e8ac229866f46ce8db1f45630))) else (if i < 133 then (if i < 132 then 0xcde8d6d8fa37cac61a466f46b447d158c357be68d6d8fa2b180019ad1adb1f45629cde8d6d8fa2b04f619bd96db1f4440f6c337a36406d9373e9866f46b6caf9583db0cdec1901b63e8ac619bd1adb1f465958c337a35b63e8ac07d866f46c207d1583db0cde8d6d8fa2b048619bd1b3336c7d158c000cdf0fa34fa2b14efb46b6c7595819b0d968d6d8fa2b07560006fb7436c7d158a737a35b63e8ac0c5866f46b6c7d1b85630 else 0xcde8d6d96c1ec03619bd68db2527d158c337a35e36d90e2b1866f46b6c7d1705630cde8d6f0fa2b07b619bdd946b6c7d158c337a4db63e8ac1ed871d9bd1acc1f45630cde8d6d96c3e84c61bee6f46b6c7c158c28d759d06d8fa2b1866f5a36c7d1583db0cded2a366b2b058619bd1b359582c066c337c41ed5fcfa2b1866f46b6c7d1581fb0eb337a35b63e8ac619bd3946b6c7d158c337a36256d8fa2b1866f46be4db1f45630) else (if i < 134 then 0x337a35b65b059539bd5adb2327d158c000d5eb46d8fa2b148019bd58db1f45628cdeaca35b63e8ac619bd1adb1f444098c337a35b63e8ac061800146ba0db1f45628cde8d6d8fa2b02e619bd1b081f456066c337ad68d6d8fa2b1866f46bdadb1f46230d4a8d6d9233e8ac619bdf342b6c7d158c348a35b63e8ac1d5851adb340919f45630003379e9b63e8ac51c751b203407d158c36fa35b63e8ac1ed866f76c56db1f45630 else (if i < 135 then 0xa36776d9233e8ac619bd1adb1f456076c337aaa8d6d8fa2b1866f46c2ec69f45630cde8d841ed3e8ac61d46a546b6c7d158c337b368d6d8fa2b1866f46b6c931f45630cde8d7b5bc3e8ac619bd1adb2687d158c337ab1b64a4fa2b1866f46b6ca21f4563000351a35b63e8ac519bd1b3636c7d158c380cde8d6d8fa2b186a346b6c8c9f45630d9f37a35b63e8ac619bd4f46b6c7d158c337ba1b63e8ac1ed86df6951adb1f45630 else 0xcdf105fd293e8ac619bd8d46b6c7d158c337a361c3e8ac0a980019bd1ae31f45628cde8d6d9193e8ac619bd1adb1f456012c38ecde8d634fa2b180019bd1b35c38b629cde8d6d9ac3e8ac619bd1b1fb6c7d158c0000033da35b65b10e6f49b6c7d15819b0d4b37a35b63e8ac619be20bf9f4560f6c337a35b648cfa2b187513bb6c949f45630cde8d5fcfa2b06b60006af46c387d158a737a3640814fa2b1866f46c22db1f45630)))) else (if i < 141 then (if i < 138 then (if i < 137 then 0xcdee86d9293e8ac619bd1adb2907d158c37da35b648cfa2b180019bd1ad11f45628cde8d6d8fa2b000619bdb6db1f4560f6c36fa35ed6d8fa2b1866f46b6c941f45630cde8d6d8fa2b04c619bd1adb27a7d158c350cde8d6d8fa2b1866f46b6ca69b85630cde8d6d9473e8ac619bd1adb1f46c158c337a35c16d8fa2b180019bd1adb2d844a900337badb63e8ac539bd1b35958488b0c35ba35ed6d8fa2b187079bd1adb1f45630 else 0xcde8d6d8fa2b063600066f46c387d14aa737bc9b6348ac1ed8001bedd0db1d65629002d0a35b63e8ac519bde4db25269158c337a36544a4fa2b18001abd1b0e1f42129cde8d6d95d4a4fa619bd1adb25a7d158c337a361c3e8ac1ad866f7936c8c9f45630cde8d6d93a3e8ac619bd1adb2447d158c337a35b63e8f02b1866f46c92db1f45630cdefba35b63e8ac600066f46b78b61f4a77da35b64a4eb2b1866f7958cdb1f45630) else (if i < 139 then 0xcde8d6d9143e8ac619bd1adb21c560f6c36acde8d6d8fa2b1866f46b6c939f4563000365a36103e8ac539bd1adb3387d158c34ccde8d6d8fa2b18001aed1adb1f45629cde8d6d93e3e892619bd1adb1f456040c337a35b63e8ac1c5866f46b307d1582130cde8d6d9383e8ac619bd1b35a52560b0c337bd28d6d8fa2b1866f46b6c6e1582c30cde8d6d94d3e8ac619bd1b35b6ca6958c000cdeb26d8fa2b14e6f46b6c929f45630 else (if i < 140 then 0xd6e8d6d9293e8ac619bd1adb1f45610ac373a35b63e8ac0cd866f46b6c7d1580db0ab6a7a35b63e8ac619bd1adb2567d158c337b05b64a4fa2b1866f46b6c7d15839b0cdec16d8fa2b03361b2d1adb2527d13cc337a36104a4fa2b1866f46bd6db1f45630cde8d889b63e8ac61a8e6f46b6c7d158c357a36406d8fa2b1866f46b6c921f4563000337a36073e8ac539d66f46b6c7d158c000a9e8d6d8fa2b147519bc56db1f45630 else 0xe3a8d7b5a03e8ac619bd1b0e2527d084c3a8cdead6d8fa2b1866f46bc4db1f4563000365a35b657cac539bd1adb1f449084c000cdf105c4fa2b14e6f52d1adb1f45630cde8d6d9213e8ac61afe6f46b6c7d158c337a35b63e8ac011866f46b6c94a1c5630d5e8d6d9293e8ac619bd1b2136c7d158c337a35b63e8ac249866f65b6c949f44430cde8d6d9163e8ac619bd1adb1f456128c000cde8d9acc42b14e6f46c0a949f45630))) else (if i < 144 then (if i < 142 then 0xcdef27b5b6348ac619bdd346b6c7d158c373a35b63e8ac1ed866f633b8db1f45630cde8d6d91b3e8ac61add1adb1f4560f6c337ae68d6d8fa2b1866f46ca8f69f45630cdf2fa35b63e8ac600066f46c207d158a75ba36726d8fa2b180019bdb2db1f45629cde8d7bdb63e8ac619bd1adb1f46f158c365a35b63e89e09180019bd1adb1f459a9cde8d8d9b63e8ac61ae66f46b6c7d158c337a4db64a4fa2b1867b46b6c949f45630 else (if i < 143 then 0xcde8d6d8fa2b062619bd1af8b6c7d158c337a360a6d8fa2b1866f46b6c7d1583d30cde8d950fa2b033600066f65b6ca3110a758cde8d6d8fa2b1866f46b6c8e9f45630cde8d6d8fa2e41a619bd1b333307d158c373a35ed6d8fa2b1866f46bc0db1f45630ea2777b5b63e8ac61d466eee36c7d158c337c428d660fa2b1866f46c38f69f42130cde8d7a5b63e8ac619bd1adb3307d158c337a35b63e8cf2b1866f3bb6c8c9f45630 else 0xcde8d815ed3e8ac619bd1b359f4560d6c337ba1ed6d8fa2b1866f46b6c7d15808b0cde8d6d8fa2b08f61b066f46b6c7d158c33da35b63e8ac0cd866edb2fe7d15816b000337c39b63e8ac520066f46b3c7d158a2a7a35b64a4fa2b1866f65d1adb1f45530cde8d6d8fa2d4ac61a466f46b6c7d158c337a35b64a8fa2b1866f46beedb1f45630cdf10771b63e8ac619bd1adb3167d158c337a36296d8fa2b186d19bd1adb1f45630)) else (if i < 145 then 0xcde8d9aded2b058619bdd0fdb6c7d158c337a35ed6d96c00d8001b2d1adb1f453a9cdddc6d8fa348ac600066f7936c69958a400eea8d680fa2b14e6f46b6c691583130cde8d6d93e3e8ac600066f65b6ca3158a737a36406d8fa311866f46c207d1ba5630cde8d7b5b6574fa619bd1b22b6c7c158c337a35b64e4fa2b186fbb051adb1f45630cde8d6d8fa2b02361abd1af6b6c7d158c337a35b65b12900d866f9051adb1f45630 else (if i < 146 then 0xea2776d8fa2b03361bc51b1cb6c7d158c337b328d6d8fa2b1866f8853cdb1f45630ea2776d8fa2b07b619bd1ade24e7d158c378d968d6d8fa2b1875146c72db1f45630cdec17b5b63e8ac619bd1b334387d158c365cde8d6d8fa2a9866f46c46db26e7d30cde8d6f1293e8ac619bd1af536c7d158c337a36166d8fa2b18001c751ad31f45629cde8d6d99f4dcfa619bdb72036c7d158c337a36596d8fa2b1866f65d1adb1f465b0 else 0xcdef26d8d22b033619bd1adb1f463158c337a35e46d8fa2b1866f46c56db1f45630cde8d6d8fa2b0aa61b2d1adb1f44f0f6c337a35dc6d8fa2b1866f46bdadb21c563000337a2db63e8ac539bd1adb3227d158c337a361c634fa2b1866f8851ac69f456300033da35bc3e8ac539bd1b2fa527d158c337a35ec6d8fa2b186e746c80db1f4563000337a366b3e8c4539bd1b0eb6c7d158c337b2ded6d8fa221866f65b6c7d11019b0))))) else (if i < 158 then (if i < 152 then (if i < 149 then (if i < 148 then 0xcde8d6d9755b003619bd1b21b6c7d158c374cde8d6d8fa2b180019bd1adb2be5629cde8d981b63e8ac61b366f46b6c7d158c337a35b63e8ac10180019bd1b019f45629cde8d6d8fa3b4ac619bd58db2467d158c337a35e76d8fa2b1866f7051adb1f45630cde8d6d8fa2b02f619bd1af6b6caf958c337a36836d8fa2b1866f7cd1b0e1f42130cde8d6d90f3e8ac619bd1b35b307d158c337a868d6d8fa2b1866f46c8adb2d85630 else 0xcde8d6d98d3e8ac619bd1b17b6c7d158c337a36543e8ac1ed866f79456db1f4563000000cde8d8710e42006b746b6ca3158a400cdf10640fa2b14e6f46b6cb61b85630cde8d6d8fa2b8ac600066f46b78db2d8a737be28d6d8fa2b1866f65bb8db1f45630eef37a4db63e8ac619bd1b0e1f43d884c000cde8d6d0fa2b14e6f46b6c8a9583130cde8d885b63e8ac61b051af3b6c7d158c337a36706d8fa2b180019ee6f46b6cb629) else (if i < 150 then 0xcdf108adb63e8ac619bd82db1f4560f6c337a35b65b0fa249871da951adb1f456300037dd968d6d96c539bd1adb1d65604ac3a89de406d8fa2b180019be21171f45629cde8d6d8fa31cac619bd1adb1f4560dec337a35b6658fa2b1866f46c0a7d1583db0cde9da35b63e8ac619bddb46b6c7d158c33da35ed6d8fa2b1866f46c9b081f45630cde8d7c1b63e8ac619bd1adb2307d158c337a35d66d8fa2b180019bd1b0e36c8729 else (if i < 151 then 0xcde8d901b6438ac619bdef46b6c7d158c357a35b63e8ac1ed86ef9bd1adb1f45630cdecb6d8fa2206161bf66f46b6c7d158c000cdf1092cfa2b14e6f6a51adb1f45630cde8d6d96d3e8ac600066f5a4387d158a737c42405fcfa2b180019bd1af736c7d29a3623885b63e8ac619bd1b1f36c7d158c000cde8d854fa2b14e6f46c81081f4563000337a361c4384253b866f46b6c7d158c337a35ca6d8fa2b1866f46b6cafa525630 else 0xcde8d901b6518ac619bda346b6c7d158c337a361c6d93e3e9866f46b6cb71f45630bde8d6d8fa2b04260007515c36c7d158a68d79db63e8eb2b1866f46b6c7d15836b0cdf10a35c73e8ac600066f883f27d158a737a35ae3e8ac221866f4dd1adb1f45630002f7a35b63e8ac519bd1b32b6c7d158c337a35b63e8ac0d986e746b6c949f45630cde8d7c9b65b0fa600066f46b6cb6086a7b3cde8d6d8fa2b1866f46b6ccf1f45630))) else (if i < 155 then (if i < 153 then 0xcde8d6d8fa2b04d619bdb6db2527d158c337a35ed6d9462b1866f46cd7201582c3000337a366b31058520066f46c387d138a400cde936d96c00d4801aad1adb1f45629cde8d718fa2b033600051b3836c7d158a337a363c6d8fa2b1866f46b6c7d1584730cde8d97e403e8ac60006cb60b6c7d13ca737a363d6d8fa2b180019bd1adb2005629cdee8901b63e8ac619bd1adb1f4560bec000cde8a6d8fa2b14e6f65b6c7d15816b0 else (if i < 154 then 0xcdec5a35b63e8ac619bd1b203787d158c000e3a8d824fa2b14d1b1cb6c7d1584f30ebb37a35b63e8ac61b7d1b2036c7d158c354cde8d6d8fa2b1866f26c62db1f45630cde8d9f9b63e8ac619bd1b0e36c7d154c337bb6cb6d8fa2b1871d46b407d15819b0cde8d715b63e8ac61add1b2036c7d158c337a36396d8fa2b1866f46cd70b9f4563000365a35b657c9e539bdb6f6b6c7d158c337a35b63e8ac071866f46cd6db1f05630 else 0xcde8d6d9813e8ac600066f46b6cb613ea778cde8d6d8fa2b1866f46b6cc31f45630cde8d754fa2b075619bd1b2ab6c7d158c337a35b6454fa2b1866f46bdadb26e7d30cde8d6d8fa2b076619bdb946b6c7d158c337a4ded6d8fa2b1866f46b6c7d15835b0cde8d831b63e8ac619bd1b22b6c7d158c000cde8d6f16c2b14e6f7ed1adb1f45630d968d7b5b63e89e61cc66f46b6c7d158c337a35b65b0ac09586a346b6c949f45630)) else (if i < 156 then 0x337a35b65ecac520066f469f46e958a400cddb63e8ac18d48016851adb1f4562900337a36326d8fa520066f79446db158a400cde8d6a4fa2b148019bd1ac99f4562900000df68d6d95d440066f469f456126a400a35a03e8ac0414801d436c7d1584129002776d8fa2b00a539bd1ad01f4560d6c337ad2406d8fa2b180019bdd4db1f45629cdef3a35b63e8ac61b2d1b2036c7d13cc38ea35a03e8ac1ed866f46b6c7c15801b0 else (if i < 157 then 0x1b660cfa2b033520066f46958488b0a400a36103e8ac0cd480160b6c7d15819a90028d6d95d3e833520051b2f9f456066a400ba1b63e8ac0cd4801dde6f46b6cb629003376d8fa2b05252000019ed1adb2d88800cde8d49cfa2b148019bb6c6915825a900337a34fa36c4252000019bd1b0e21c8800cde8d78db62b148019bd1adb328562900337a35ae3e8ac520066f46b3c7d158a400cde316d8fa2b14800006cb46b6cafa2 else 0x3736d8fa2b07b520068f46b6c7d158a400a35d06d8fa2b1480146b6c7d1ae5629002936d8fa2b03352006cb46c9adb1f4a400cde8d688fa2b1480146c387d08419a9002cb6d8fa22033520071d46a607d158a400a35b63e8b9069480146b6c7d18819a90028d9acac1603352005b6db1f456066a400a35b63e8ac175480146b6c9b9f419a9002f26d8d22b033520066f7cd1b0e1f4a400c417f3e8ac0cd48014eb6c7d15819a9)))) else (if i < 163 then (if i < 160 then (if i < 159 then 0x337ba1ed6d8ac520066f029f4560f6a400cddb63e8cb13148019bb6c7d1883da9003376d8fa2b07f520066f6951b35958a400cddb6574fa1ed4801beb6c759583da90033797cfa2b07b520066f46b027d158a400cddb6454ac18948019bd1a7d1584c2900337758fa2b06b520051b3836c7d158a400741b63e8ac1ed48019bbaa7d1583da9003486d8fa2b075520066ed11f4560f6a737a35b63e8ac20980019bb6ca31583da9 else 0x378a36396d8fa539bd1adb2607d158c000d5e8d4a4fa2b148019bd1a949f4622900337a354d370ac520054f46b6c7d158a400cde7a6d8fa2b14801b7d1a949f4562900337a34fa388ac52006fb46a5275958a737a35b65d4fa2b180019bb6cb60f601a90033da36406d8fa520051adb1f456062a400cdead464fa2b148019bafe7d1581ca9003376f0fa2b07b520066edb1f4560faa400d95b63e89e1ed48019bb6c7d18c5629) else (if i < 161 then 0x35ba35293e8ac520066f3d2527d158a400cde8d4acfa2b148019bb6c871583da900337a352d3e8ac520066f60a527d158a400dce8d4a4fa2b14801b7b6c7d1583da900337a35b65f8fa520066f742527d158a400cde8d4e4fa2b148019bd1aa41f4562900337a355f4a4ac52007513ba527d158a400df68d7edb62b14801a8d1a949f4562900337a365f900fa52006b6db1f4560f6a737a35b6570fa2b1866f46b6c7d1580830 else (if i < 162 then 0x337b6ded6d8ac520066f46bdadb26ea400dce8d7b5b62b148019bb6c9b9f43da900337a35ed6d95d520066f49bdadb158a737be68d6d8fa2b180019bcd6560f62c29003376d9103e8ac520051ac09f456066a400cde8d901b657d48019bd1b2036c8729003376d8fa2b068520067b46a527d158a400cdecb4a4fa221480146b787d15819a900337ab1b63e8ac520066f562527d158a400cde8d519292b1480146b8e7d1581529 else 0xcdef26d937440066f883dabf958a400a35b6418ac095480146b6c7d1580da90038ea35ed680ac52006c146bcedb158a400cde8d999983e948000066f46cd66222cded2a35b63e8ac619bd1adb1f456096c337a36236d8fa2b1866f46b6c7d15848b0cde8d6d8fa2b019600066f76c56db1f4a737a35fb6d8fa2b180019bd1af6b7856290033da35ed6d8ac52000019bd96db28c8b37a35b63e8ac0e580019bd1af6b6c6229))) else (if i < 166 then (if i < 164 then 0x337b19dc6d8ac520051b029f456066a400cde8d7c9b62a9480146b6ca315819a900337a361c7b44252000019bd1ade2d88800cdde26d8fa2b148019bd68f6b6c56290028d6d8fa27824520066f46c0af6958a400d6e8d7b5b62b148019bd68949f4562900337a356c4a403520066f2a1f4560f6a400d968d7b5b6279480153d1a949f4562900337a36107b4ac520066f46b8c7d158a400cddb657cac1ed4e6f46b6c7d1580530 else (if i < 165 then 0x337a01b63e8ac520051adb1f456038a400cde8d4dd293e948019bd1b203787d2900337a4e406d8fa520066f46aba949f4a400d1db63e8ac1ed48019bd1b22b6c7c2900337a3617634ac520066f46baa7d158a400cdeb4901b63e94801b9d1b2036c7d2900337a36406d94652006df46bdadb158a400d468d6d8fa2b148019bd1b2fbda562900337a15b63e8ac520051adb1f45611aa400cdedb901b63e9480146b6caf95819a9 else 0x28d6d8fa2b047520051adb2d819806a400df68d901b63ad48019bd1a94a1c562900000cde936d96c440051adb1f45604ea400e3a8d901a03e94801b7d1b2036c7d290029e6d8fa2b02d520066f6da527d158a400a35b63e8ac09948019bd973936c7d290033d6d8fa2b07b52006af46c80db1f4a400d6e8d901b63e94e6f46b6c7d15830b0003376d8fa2b079520066f0e1f43d884a7bbcde8d6d8fa2b1866f46b6c7d1581230)) else (if i < 167 then 0x3376d8fa22061520066f60c80db1f4a400ea2777b5b62b148019bde52036c6929003576d8fa2b07b520066f081f4560f6a400d5e8d7b5b62b148019bd82f6b6c56290028d6d8eb2b01952005ef46b6c7d158a737a364d6d8fa2b180019bd26949f4562900337a3640814fa520066f7925269158a400cde8d902103e948019bb6c7d15826a900337a3654900fa520051b10b6c7d158a400cde8d9ae401614801b2d1a949f44f29 else (if i < 168 then 0xcde8d7b5b63e8ac600066f46a7c7d124a737a35b63e8db2b18001d44ef2036c7d2900337c42405fcfa520066f4eb6c7d158a400d4a8d48cfa2b148019bdd12036c7d290038e680fa2b07b520066f46ca8f6958a400a36543e8ac0cd48019be20ae1f4562900337a35b65d403539bd1b3936c7d158c000cde8d6d99f3e948019bd96f6b6c4429002b46d8fa2b033520051ae31f456066a400cddb660cfa2b1480146b6c8715819a9 else 0x66f203dadb0f6a400a36407b5b60cd48019bd1b2036c7d2900337a35ed6d8ac520066f46c80f6a52a400cde404a4fa1ed480146c80949f419a900337a35293e8ac5200480db1f43d866a400cddb63e8ac1ed48019bbda949583da90028d7b5292b033520051adb1f456066a4004a4fa2b07b0cd4800f6b6c560f619a9cde8d6d9293e8ac619bd1adb1f4560f6c337a35b63e8ac0cd866f46c80db1f45630))))))))
private def st5 (i : Nat) : Nat := unpack st5Packed 67 20 i
private def adj5Packed (i : Nat) : Nat := (if i < 7 then (if i < 3 then (if i < 1 then 0x4100100f0c00490c034000030200005c0442c900814028104300000118214010108220008208408000110019b001048040005000300007006440040 else (if i < 2 then 0x10004308101c0050ca08804408200304828008004007a11200c38700200704614200000114320f04228e0400040800090431400070000431800081c4 else 0x1810812c00010520431020850020c00020400d11400082431010010461c004104006308010204304814508320f0030830440070842c3002082300201)) else (if i < 5 then (if i < 4 then 0x3800400010001080404450420c02421001400020800000040400450860090120090130430801021410470000400851c40070400411430820c7 else 0x8300008000f0010001050c14001801440c00050852421941c010200100c0cd00800525400209118b0400400800c2081000246007143103081041080) else (if i < 6 then 0xb0023803800050420c704520100f2000400840000c20c00820010040410062021000c20000c704000004230114800300200a0470c20800890cd041 else 0x1dd0010c00000010c31040080001800c400524300300304100100e080341087001003040000142002000000141081004000240103000003007280003))) else (if i < 11 then (if i < 9 then (if i < 8 then 0x200f1000010410010410000c700c00100600000120d0401000013010401c200e0012000812c300b0800001480060c020300114004a20c0400c0000 else 0x54b00004008204400f00004f0c10c408410104808100200100b0812021410030011010581400000430000c00070c60c0000001000006048042000084) else (if i < 10 then 0x11800080020000000451011040421c828900008260000204a0800801c01410040850c50850002830c80030460003c808a006108082180481007080 else 0x10000d1c01000071020490071820800001450021800c10cb0020c01011803820046cb00010c08d0062520000020010021c0040003100180041100004)) else (if i < 13 then (if i < 12 then 0x14a00c1c40002820401420400410073c30c22c90400830004400400820000522000000810190021010c20811c30c80920200450011490c0085003041 else 0x4038404000018f2c00860020010810020400820872840002480400021423930420840c00010420820c900e0400822410020400050c03c1056041045) else (if i < 14 then 0x22400c50813830c518f24000100000e0830000441000831040c004234104214b0411c41400c10810cb089000441040008500105084000009040 else 0x2642102043000))))
private def adj5 (i : Nat) : Nat := unpack adj5Packed 6 80 i
private def loc5Packed (i : Nat) : Nat := (if i < 32 then (if i < 16 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0x4820006ca7dd86255d181bb80a4667000000aec8920007680000000002a100000000005e000000c400009730008d9b2e6f540300057a0003bd8a2000344274ad8000000000b0e7c40cd4b300064f829000a68000000365000ade0000001230003b473f82b000000000c30000607c5659f10659c70f else 0xb209b00001ab0006350001a50000940001f400060219f0000002650000000006f702e00046e64b0a82d4000c4acf49b900000026e11f6650008078b72818f10000008888b59e2000000b15060c3925700000000000000094d1e20000007c1b62a0bd21cc1c78000a4f0005ed0e16cd1ee0005d6c680006c2) else (if i < 3 then 0xceb79b01500000047251700076bc536c49a93316dd187253997462518000b32bc574a0000b4914c5e0c7a6e0008abb235f50000001d7964ba4c5b0df00000015a34f00070384700000061030d000855000000000150000431b7d16f09f900a3e00088aa8d56d000b4c84b54a5f23420002c40a1000424 else 0x1550001216190007746fc7e81d2b199d700035a29873c00000032300000094c00038c0009f17f70000b99ed0000006619d600000099b000bc64965ca000357bd8542a9eb293880caa4451b2e18b9833b311690c5839cc7000000ce100031e21159dbbc00016c00018c00053d06b9e45678f60e82f0af8000)) else (if i < 6 then (if i < 5 then 0x6693d50006e8000400ca62619720001483a507a585c9b000801812310b2aa477067179548750000002c8000a190002f1b6f0001630000000004d80000008453c55080007645a8c88b4241b000b8d0009b300069600096d071000a960003460001dc00011d39b2a4000000927100000d28000744529 else 0xbfc000c4125a00027b0cb709a8f17b000681385693459afa4787a5b36000c71cad62f13d627ac10003b95ffcaf00049ca266e900056b00069a4e000046b174000a7a4afbb50007ba7e2000c7095b9a87bf9266f2823b8e054481000cb100003b871afec205b46a100098c000030a6f52400003f000cdc000) else (if i < 7 then 0xbb900092a2b200000000005a9c287875d000ca730b000796b763b104391e3bf641d0600047553f351112000a7400000051ca379fe543b91876d310410000000000000ccb140000002dacb8000a00bae6167b9bb46c0a756f820a00033e000000cd8aad0e700000006200085c7710004907b8000510000b89 else 0x378000011019000ab13e5bcec5a0008cb000a0fbf900001ca52000597bc900065ba308e40000000001bb417000000186000c0a8e3b256ae1dd0000005ba000a6d000cf50005d18f80000000005d000000030f0000000006bd000c2f0000009cf0004428dd89a866c370009f3487000d1e0000003cf000))) else (if i < 12 then (if i < 10 then (if i < 9 then 0x33586972200081734000000046320964c8b80000b0806000000a5d0ad008000cc00000003acd1600006db9600000031200075b89b92c8c1a6a24e0008870ab09b6f302c1a80008632b46af20b0000000003552ad00057900000060c319a66ced7653aea22a427b7868d1d00058000000009d0009cb9d5 else 0x402000aeac0270e6ce6a0cec0000000009960000b5b265270000005e50000c00002d65ae7c70001ac75a00047fc9c7320b30c657b64814214c6ab00000015b21458ec8b04a00074c000abf6e405685e1c70000333f92ffadb7f22e0719000cc3000469405686000c1c21a0690005910000009b70001434fe) else (if i < 11 then 0x2022440006d50004e70e9000000000a35cca9e924a0009a64b886c5a1073000ac80008c2928000000000c7737e826b7a1de4f800000047900006c55a00065e000745c87a2799c00035993d85718a000a4e339000d220009020000000004eba0683700012f441971000ccecba27fb948a33111b91765f8000 else 0x3f100000074f5cc00010e0003a100032aa820009246aa67383e367d070000003f48857e059300086d52d0004b15763286134c200093441300f00027886f0009aa99800022321c9ab00054100010500a000679053b0a4d72a7000672332a102fe00088c0005255772dd0c168320e30e000c3c7de00080f65c)) else (if i < 14 then (if i < 13 then 0x43f4fb125a914a608f0003179120004b51670007660001d60001650f22174670004f7000a830000000320000000145a4271c165bcc3e9be8d2550026000b80102a65002000bca3692f949828b6940007be436000c950003890004e34917e6536a0daaec6b0bb8364e8000000baf2eb61f0000005c5000 else 0x3b65e8354000ac425f1b2618b22000000ac733b0008e6916000000224000830000af9000a139200000003d373e9940009f000000021368e000ba200021f0000008b3828000000b11558000000c740005f60000d60000fa1be25c0003140000008ec000c078480d18d5aab91326f2920fba2f0000000004de) else (if i < 15 then 0xa97000000bfac2c1710f9ce50000000003ad477870000415a12b160000005881e6000000000000959000000000b430003b36f67840002a200069bb712465f000000032f000000c5f35e00000000000000c6cccc57cc000c89c512641f341c6ea6ba6b7000c64af100017eb095fe000ba9cd600048518898b else 0x596ad7d02ae5425000b6c00048b000c280000d9952ae48f25049df7dc872c5000079f00000000081f0005840000000000000006780008180000000002670e5b0588e61ec549e500074b00051e4320e40003e9c48000cc2a7e953d0e072162712000a6c55f000a627a64dba733b70004a776e0000447f30e0)))) else (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then 0x2e400051985ab61cbc00049fb860000005152595140000004ff8fa407c3181b00000000063f00088f0000004fc4529d900000000000072a32c3660000000000009bb095cfa9fabcb000000b6565500045e0000000000000009308130000006ef987000a434e500029b90e0003ff8492c9c4b894000783000 else 0x82000000000a32a600000000000009e6c98198304cb2000879000b40065a24000000000000c0db5b000beb16d0a300000090524f8440009235e041d1b199ab951a152b84275289941e83800014b23f609000547c8c297ca40004b00008359c00008900006497ee0002b39ef714000000000000) else (if i < 19 then 0xd267ca77005f00029e0bd07fbff7e4a495da56f1d8750215c1a7c90004f3000000941000a367c2abc0660160006bb58f8d60009ca6d70000000000002c300000044d65a021000000a9c00075c67a00079760689510c63d0004a18080003fb7d0000421c807e90003499d00000007ec16b8b60f6000cb0b1f else 0x985000000b920009861f7000643000000b0700000013b8340008bb70239f0009211ae0002680002e8aee1e40000004d34cdcfd000a8115e5a2d0f0000001b500064d9ec12eb6b3d44c831c00000000003136200000065307d422bcd5a309a42dca90003277377df00000037dd0462091b000b1806828c476)) else (if i < 22 then (if i < 21 then 0xb138e0000ce460e1f66ee000000000ccd370000c9a000a2d3c6000a17356c4e0000c41a051391a18ebc70000000008c6631c3d7510002f80003768e20007d10000861eb00010a0000f000000083fc76a1d9a76c60005e300051d0d27b4699d039462ecc9e60000065400098200026d266000881273a1f636 else 0xc94000d2e3906458c38976240000009d3000b735bba39000b6a6667cba5ab1736e56800000007983d7760000570006d00000008e90002750004d67804ee3ddc35c09889937760000000d3045b0000000000000000b7b5f34c0000000000001030000006b30002779929de09cbd02012ee5ce3c2000239000) else (if i < 23 then 0x7fd8220985810008f77e3b660000000000750005ea0004d46d654961c000c1500094263e8ac00000000089300070b2d1000d2c000b120008c4747235acd77c5b20008da0000003da40800062c757a3c00032498f25db9ebf20004ced0a00076f671377247c298db0001a200000098911a59a8bd5511b4000 else 0x1ff0000000000000009012d80002f42df56c000a85b2413512d0376f175e70709000034100000046681c3b20000005454b67346640006d885472c5861e706f006000000b604462ea6a2000386000520000cfe00006100000087e00018db100000002563077303eb00068d2b8cef000c01000b67))) else (if i < 28 then (if i < 26 then (if i < 25 then 0xd178af000000a88000b2dba046f88dcbd94319c5980003503710009e0bec2e33cc00002b0000001669a16686e1d2d00004b00045c8531fb5c9b870001460000000006c37fe000000000b630005e677333c5c424cbf85bd00040c000be07ab00074e0005057a29680000009adaa46970000006c77a9000993 else 0xd1c72b9360008a6000b33c2b0000009a5000530589404000000bd49574a5c4f94a9222199f9b8bcdd47b000c384da4a300063b83c615000000d1a000000baa0000000004b7a3fb7b000ab65460000000004c0a530001b0cd10ea16e00082a000cd05fb93b000bb1ae0000843000b0b3f0704000790302) else (if i < 27 then 0x3522d7000b694c7b5a0008ad4ba000a311898bc2d5218564ae85dc00000b6e7000000cee190b3d116c1900000019b90f382abaa04000cc96a80001771b37f8000000000be64c93a0000c1081628025e000b6e00000000000000088016000081a0007d50000000007af50b0001baac300092b0005ee0587cf else 0x77f8ff0007290003f31cb95a52faaa0005121c20007f1cbe695af5b4f08093c0000007a7d2a9d429389ec00000a1a316000000caa000c275ac0004ed00031aaf7ce0000b0fcd33740009506a9433000a4c9c637b3386b00000000001085900000000002882a97921e10000009836628d8d240000006c15fc)) else (if i < 30 then (if i < 29 then 0x210000140cff0003fecb739d21d000000811af20004e947c6630000000002e50006292623260550fface04f03c36a47d00037364e27dbfd6d243b85d0000000ba3e63aa52c35ba7f00070130a000d1855900068000068b000000c55000c8a000ad5d20000000a9537a5afc1e612000c7aa5c00067e5cb000 else 0xbefb1a5e700014123a9404603919f87150002379afca281ec34000000c79a59a544fa0000ac1d9ac0000000000000a9908c6df29197d0000002a30002ac2bc93271fa8042a8b40000000005ef2c262d5540006a67460b203d5d5a4a0000000000003deb9f66f7d400000057c000286000ae112a1bc) else (if i < 31 then 0x80c000945540130660000860b390a923c614c7358363ca61bed0000003b50005789510f800090cc61ab90008a4000000000000ab5000bee1aa73a5db0005ec5cf000a7c5755df9c41cf0000001d4c4419a3a3000cfc41800029a1243450000000000009668dcd0827942670c0006ed353a020be343ce352a else 0xabe00043ac62b9ba78000000052b1e00000000077a00088600000000000048ac4c6e548db1d02500060f000b781f5bc43800009eb969b01bc16221f0ad1000738000139000a6b2330002060000000001b7000c8400000000000000059e000bd300000000025014a84d0000dc5cdcbfad900042f4440005bf))))) else (if i < 48 then (if i < 40 then (if i < 36 then (if i < 34 then (if i < 33 then 0x7c50000000001a4ad695f78d00089d8d10009b2000000000710000659a3d0000000000d7623000000000000000b815b346c4016929ac00096b0c3c6f449000c9f000d1589148c1c51150002c000034d0004936fe2c7000000a410ed00040b1cc0009c72540000270008a76c500028d8d30001ec7cd7db else 0x36d17c00093a26b0009060ef0003b08218d784a39a0a0bb272d00020dacb99d804929573000000c22000000bbf000049566301bd90002760008aa17970877828f00084ea9d6b9594d10ad08a1000111000555c3ab389ba000b724ea93922b000a8abf1096000000000aaca5fa2a3060009e100007b) else (if i < 35 then 0x1cd4732a638e000180c0b0003e40005570009bc00013a0f3bdf00044fcf20008ea000a4875898d3d27ea00066dbe24d50990009ae1e8c180002cb4f4455c2d05c489c1b83219556000058a00000000039e000d2b6d40001f1a3369ec6965d0005536e64d2b0829cafb7f9000b9065f68850a9158101385de else 0x2fd6843c9b5502dc451451938747ed0e28f4c604b94ca439419775000156865a5b9330000000008cdab47c697c000091000c5d506000b98000000000a38cfb00093f0f166a5ebca10000af1c60007d30000002430007cebdb0007ac00000000000000065019d00024b01dd130005c81449fc7bb3e1bc3d23)) else (if i < 38 then (if i < 37 then 0x7b6000000544000313220531000867acc6bc6564dc000bac7eb000bd169d0dd0015e2000000aeb00062e69044898a6256cba768a896e000a0cae2cb5000000aff00000050100000004700096a000b8aa8b00000000079882066bb340006b400071e69f22100000034ace2000000a28a7d7561541fdc96164 else 0x5c13cb1fe5f95a5a168f580549d0000008fd4bd73d6de92e0008820001782d03ec8fc1929ffc820000de000000000000000258000a553e20001ea7c091700086b21b6d90000003f604856384c0000000000001ceba15377696f4000447be800000012897a00063a0000009904565700000009b10780001b6) else (if i < 39 then 0xc0f1372fc59222e000a01000ba649a00044e4ec9b6c6c000337786000b77cc8cb9c9300000080d5d700000072100076100000001e0004c1919b75cd722600074db28cdab5000093e84041486a6460000000000006a708b1133810000009bf0003640001d072800000000022c000000601b5cb5900018b1db else 0x981aca6707c314d00075570d00014e00085f0008d436f0000006bf20f23800000000040d85097ece9000a456ffb538271f9409b580001d500000046d00041a3efbba5ad00000000038737f7a005d56148600000013c000000000d194aa2b7b0d9db0007e100077d793000000000042c2ec1400057fad3000))) else (if i < 44 then (if i < 42 then (if i < 41 then 0x7330170000009481202001320000006d1023368000785a79000944000a1b00039c0000008b10009350008032c6000000abbcde94e00091c17ac7b605c630000004c615d000a2b2de000204c430000000000005e90bf02f1262fb0008d0ab2000c0c00072600000000000047092571d727000000000 else 0xb49947000ba704e0006e000028568acd9000000949000ca08517d600051f3aba94000bfb2ca88b0003a9000294205b3500051a7f50f70fd0000000d08df000bb075f00096f3793db0004294d900074827a1d1bda063000000617cb43f84f900017d4976ec000c9100078953e11ebad8618c51bd0a6000000) else (if i < 43 then 0xc47000000cf30008cf23bb990000000006042fabc81bfa840008b271c4be00067c64ab9c0007aa3d02039ea6fb2b0d055aaa8e14900056500042c00000038b00015fa2507c7136dc000b2787300e32500000060b11c9a00003c72d3000a113ee000000000000ad400078ecd5979000bf7cab000711 else 0xb82000d1b00000000000097500407077e0003bb79cac900000009e5325099d8c729630005e400000076d0000000000000003f7651bbd500cd4000a51000b3e7d835d394000000aa1000c21c6744a7ef3a4be15a667700000000000000031b2321190d58a00c9b9a67f2ab5b7be3000bb34110000000007f0)) else (if i < 46 then (if i < 45 then 0x407622bd85bb9d0fe7b100089c95cbdd4436b60000001da0009e82123d10003be00049953b000000c751a700000023d35c36c0000008cab687189e7000b44000b840007bc38a000b0c1e91f233aae600000063815c00053300031d48f5dd5f140ea1500014f1011940000005038ed502000c17321be7 else 0x5d20001e58eb36b050b7e0000009cd800000d09000227904000000092000633333cea000000a4091dd129589774880004b2000000000b6d00000043000022f0978dec030008770000004388f300000082478a34700000086ec040000072280000359d100045f90d32b2cc0002e6cf8571295000ba56adc0e) else (if i < 47 then 0x78131838f0003d70ec000cf92453a70da4c5451000b549080000001c30008ae9616580004e22820004ddd000e6000c46000c24000b452f55c000095d00025b3a8ab75fd5392690001332e20008be252093020814000000c5c3d680b82d0005e10000001473dc00057e0001a95c7000000b3c00054c0001f8 else 0x6820890003ca000cbb12c00000000055c00000d10f0003f20f53e0000000aa9000bb6000000000a89adfb478418cc0004d13c8acf13e00076a000cf7360336000000af361b0000001af00097baed0879910000002492990000006e235fc0683b2226c880a7e500000000070a483416494a1841f0001c4000)))) else (if i < 56 then (if i < 52 then (if i < 50 then (if i < 49 then 0x3bc7f4000000000ae37991974230eb00068f0846440008b06b243d000000aaf2ae0000000007d75163f50000002551847407882bb122ae9c128598258ba0003300a53d882c92f00000019ece85b94f000045000001f0003ba2f20009da0000000b17d22a803937cb48cdb5d9b4e000000 else 0xc6e000076372000000000427c839f731f0007a454d4bf93144ca93bd6bf45c3af0a0500000000027c0fc000158000000000723000183adca4d00000000000011ba7b0007956be0512b6652000ba30464cb000bd524845a30896250e6db7e70001d3309ccba929111fa168b1b2b525131567406a00026c918) else (if i < 51 then 0x772000000b3b0008e5b1cd2945879424100000071633d4b4676a5e55b000b210000001290008cea290009dd0b683a000005000b7ca036370007ae9884c4000b2c000000cf004d00055272e628000ab00000005a704c03800036378c00034b00071b2840001e0c495d3c6d000152000000000bab000000 else 0x79e58272f000c5742e000a4bb3f000495000864c85000be5289d0c117000000000000a9b33f0000000008f9000852000000a5079100021600058b0340853d916128ea57c7f27060d0009f6b933a26f065708d0002f6c588c843e0004200003fa000be403a1094bc0007da9b449b22ac7e8a97fac3b7a8064)) else (if i < 54 then (if i < 53 then 0x2f3000c1f611a5802895652108a435970000574000858c920000008f000024216ab5e3ce787000b303fdaa77d900000098e5343970005b5000bcf58c7bd9f2000995074d142082630000004f502a0002f70000005266a3c8d84632d000b3aa706b81ed0882aa0009844744349600000008c94ada670c2b5d else 0x1c124d1fc705454000412000471c33c520eebfe56a9760000001ad8025c2c328eebf0c8600000000000081d54b0000000001750002c1000763cc60006876f947a0005b00002ba97faef0007000005990000007ff45d87d000000a344923ed00000097478f507a23a6300087b4611992db000000a3a000) else (if i < 55 then 0x5ab0000aa000240ada511b510004576d31c95f40007243229bdaa3b8300000000087c0000009a26a510d2a50009cc62b6084f1000c26cac3e30004a472013132e0004cc73567d010000ccc000029153b4a4df0009c96b100000000055e1140009099385875f7000b850008ef0003990007540000003c1528 else 0x76700047e0000000189c8ab8392689ac55be0d8000077759603a860004645d42e950f4ac4068310000002cfb41000384000c66ac20008a5cb300055687f779675aa2000b563959fba0a000ccfc970000000cf00008ec3699e34e2dc2bea3b000000cd29dc000a20cc4b00000a21003d0b3e82368c02afa2c))) else (if i < 60 then (if i < 58 then (if i < 57 then 0xbbb40abd242850d7410000000000004fd000000000000a6479dbc0000621b7f000af40000000004f29a417f00000000059b0c800040f2ce2ed0003340003830007f629d1100005629f50005230bc76c8e10006982c505b000a778fb49e000c8e4a962a0003a6000a714e4b8c9783750006c9731348022000 else 0x898000aa50000a25a9000445059691bc200038dd1f20752e82ea9a0002b10007c8b043ea0678e80005480000000001a30004c300000000001a2d90001dfbdeb880000009c3a98000c1d58d00000029f358000000000add0d40003e700066ca0ea092bfa8c396c653cd9c5c8181943c12b2961917adc59b64) else (if i < 59 then 0x12a693c0cf12292cd000000000bf36260000001e39fd361000173c2521e18f84fa078c70f4000c99999c7d0000000000008fe4ab000685c7c0ae15728799f0000e30009a3000000cb6081a561c0000b378bfafd3df48074979a00094f4a83af000000d01a2e000000c0500019666e303d11ce6182bcc92d else 0x77bb0610b4f6000453000c90b52000225000afcbea1c84d06300000002ef00013401b0006ac000cf64a200000000057222d80e0009070008e7000172000884d32000118000000000bb72907a1000c13b8f1277fb000aa81ef95e00050cd2f53a5c6000b029558096fa63261a5b100078261d0009ce170)) else (if i < 62 then (if i < 61 then 0xc9d56e4650006479c15a0000bdc00056900089f82f0000000006a40130001a6ad254e7fc00006e000000024000a1ca466cf000a9f0364e1aa66ebab327eba800000000096c6da7b563400000090a272283000000000b70b975b8c3f000000a900009f41b864200094bb2b0009b50db000ce7b2fbf6ca51ca else 0x9ee7b30007b0b46000725b4b965af69036e373b00000000015167bbf560a39826a2a00d36b5a7200000000000023e00020c260b744ef159b570004840a77420ce32000000000000069c5958150004e6753c6a6408564cf7770003b8c8f46a04590b000a0800044b000000d27230000967c2a0000b86397b2) else (if i < 63 then 0x5353c4009000a87231000000000000b4d0000002b97a39d2a1e0005b6000d2557d000ca8be90005fa30cb0371a000bbea14c23000b7953852291f3005f300000041003e0009b8910bd74a0000083c08ac63c3000ae7ca3d0dcdfc1100089613600000087a32988328a00010400073642b78b2d274398053c else 0x6fd48e5d813f10700000046854f000000739437c4dabdc42aa000068c0003050004ae9e34bb4400000002e70001850003932343fc07ecae))))))
private def loc5 (i : Nat) : Nat := unpack loc5Packed 12 80 i
private def st6Packed (i : Nat) : Nat := (if i < 29 then (if i < 14 then (if i < 7 then (if i < 3 then (if i < 1 then 0xcde8d6d9a03e8ac14dc0019bd1b2f36c7d158c337a365e6d9a03e8ac700071d46b6cd01f45630e3b37a35b6680fa2b1c66f46ceedb3407d158e000ea28d6d9a03e8ac600066f46b6c7d15852b0e6f8ecde8d6d8fa2b1c775c766f46b6c7d158e000cdebda35b63e8ac619bd7b46ceedb1f45638cde8d9ddb63e8cd2b1c66f72d1b3bb6c7d158e337a36776d9713e8ac719be0546ceedb1f45638003a8cde776d8fa2b187519bd1b3bb6c7d158e000cde8d6d8fa2b0a761db7519bd1adb1f45638 else (if i < 2 then 0x38edf68d6d8fa2b18001d451b3bb6c7d158c3a8df737a35b63e8ac71bee6f46d04db1f45638edb7dcde8d6d8fa2b1c66f46bf2db2fe7d158e337a35b65fcfa2b01d700066f46c96db1f4563000337c41b65fcfa2b1866f46b6cd02fe7d158e000e3b37a357f3e8ac61c766f46b6cbf9f45638cde8d9ddb65fcfa2b1c001d466edb2fe7d158c3a8cde8d6d97f3e8ac700066f46b6cb89f45630e1b37a35b65fcfa2b1c66f8851adb1f456138e000cdf10a35a03e8ac600066f7f51adb1f45630 else 0x373cde8d6d8fa2b180019bd1adb1f456112c3c0cdef2a35b63e8ac719bde546b6c7d1d65638df737bca8d6d8fa2b1c71d9bde546b6c7d158e337ccaf2a35b63e8ac70007519bde4db1f4563000337a35b6574fa3ad8751c766f46b6c7d158e37dcde8d6d8fa3acac719bd1adb2fe7d1d65638cde8d6d9a03e8eb2b1c71d9bd1adb1f475958e000cde8d97cfa3acac600066f46cbedb1f45630cdee8a35b63e8eb2b1c77dbee6f46b6c7d158e0000038ea35a03e8ac51bee6f8851adb1f45638)) else (if i < 5 then (if i < 4 then 0xea337a366b6d8fa2b1c0019bd1b1736c7d158c000cdf32a35b63e8ac619bd1b35cb0db1f45638003bacde8d6d8fa2b180019bd1adb26e7d1a4c00000337bc9b6348ac519be2146b6c7d1d6563800337bca8d6d8d22b180019bde4db1f469158c3a8cde8d6d8fa3acac719bde546b6c7d1a45638df737a35b63e8d22b1c66f46b6cbf9f469158e337c428d6d8fa348ac719bd1adb1f4691580eb800000df68d6d8eb2b140019bd1b2a1f469158c337a36776d8fa348ac719bd1adb1f46919a5638 else 0xea337a35b63e8f52b1c6fb9bd1adb1f4560b0e337a35b65fcfa2b05871c766f46b6c7d1582c38ea337a35b63e8ac161c0019bd1adb1f45603ac337b6e8d6d8fa2b058700066f46b6c7d15829b000000dbe8d6d8fa2b14001b7d1adb1f4560b0c36fcde8d6d8fa2b058700066f46b6c7d15821b0f0737a366b6d8fa2b1c66f46cd6db1f469158e337bca8d9adb63e8ac719bd1b35b6c7d1d65638df737a366b6d8fa2b1c66f8851b35b6c7d158e337a366b6d9a03e8ac700071d9bd1b359f45630) else (if i < 6 then 0xd9737a35b63e8ec2b1c77db2e6f46b6c7d158e000cde8d6d9373e8ac619bd1b35b6cbf9f45638d9737a35b6680fa2b1c66f9962146b6c7d158e000e3b65a35b63e8ac600066f46b6cd31f45630ea337a35b63e8d22b1c6cb9bd1adb34c7d158e39bd9737a35b63e8ac7000751b2d1adb1f45630ea365cde8d6d8fa2b1c6cb9bd1b3eb6c7d158e3b1d9737a35b63e8ac71db66f7951adb1f45638cde8d6d9a03e8ac0f5c0019bd1adb1f462158c337a35b63e8c42b058719bd1adb340b89f45638 else 0x337a36103e8ac27980019bd1b0836c7d158c00000337a35b64dcfa519bd1b0836c7d1584f38e3b37c428d6d8fa2b1c66f46ceedb1f45613ce3a8cde8d6d8fa2b09e719bd9746b6c7d1582c38cde8d6d8fa2b09e20dc6cb9bd1adb1f4560b0e365cde8d9adb63e8ac71b2e6f46b6c7d1a45638e3b37a35b63e8d22b1c6cb9bde546b6c7d158e365cde8d6d8fa3acac719be217951adb1f45638cde8d6d8fa3acac14dc001beecb46b6c7d158c37dd9737a35b63e8ac700066f46b6c7d1d85630))) else (if i < 10 then (if i < 8 then 0x337a367d6d8fa2b1866f65d1adb2d87d158e000cde8d961b63e8ac60000019bd1b359582c28d9737a35b63e8ac279c66f46b6c7d1a456110e000cde8d6d95d3e8ac619bd1adb3407d158443800337c0a8d6d8fa2b1866f46c1cdb3407d158e000cde8d6d8fa3105861d266f46cd6db1f45638cde8d871b63e8ac00dc0019bd1adb2d856006c365cde8d6d97f3e8ac700066f46b6caf9f45630cde8d6d95f3e8ac279c71d9bd1adb1f479958e337a35b6680fa2b09e719bd1b0e36c7d1584f38 else (if i < 9 then 0xcde8d6d8fa2b088049c6cb9be2146b6c7d158e3a8cde8d6d8fa2b088700066f8851abf9f4563000337a35b63e8ac20d866f46c0adb1f456110e337b2e8d6d8fa2b09e71b2e6f65d1adb1f45638cdecba366b6d8fa2b1c0019be217936c7d158c337b2e8d6d8fa3acac719bd1adb1f4561102138df737b2e8d6d8fa2b1c66f65d1adb1f469958e337b2e8d6d97f3e8ac700066f46ca8db1f45630ea337a35b63e8ac109c001d466f65b6c7d158c337bca8d6d8fa2b00371d466f65d1adb1f45638 else 0xd9737a35b63e8ac221c0019bd1aefb6c7d158c337bca8d6d8fa2b088700066f46c0adb1f45630cde8d871b63e8ac221c0019bd7146b6c7d158c37dcde8d6d8fa2b08871bee6f46b6cd59f4563800365a35b63e8ac27986fb9bd1adb1f45613ee000cde8d6d9462b088619bd1b0e36cbf9f4563800337a35b6518fa2b18001ade6f46b6c7d158c337a35b6518fa2b088719bd1adb2fe7d1584438cdef2b2e8d6d8fa2b1c71d9bd1adb1f456110e337b2e8d9ddb63e8ac70000019bd82db1f45628)) else (if i < 12 then (if i < 11 then 0xcde8d9de6b6d8fa2b1c001b2e6f46b6c7d13cc337a36776d8fa2b042719bd1adb21c7d1582138e6f37a361c6d8fa2b1c0019bd1adb2be5613cc000cdf109ddb63e8ac61c766f46b6cb61f45638d6f37a35b63e8ac221c0019bdb6db1f4560b0c0000035ba35b63e8ac500066f46c1cdb1f45630cde8d6d9a03e8ac161c66f46b6c7d1d669158e00000337a4db63e8ac500066f8451adb1f45630cde8d6d8fa348ac279c0000066f6db6c7d158a337b2e8d6d8fa2b088719bd1b35c5cdb1f45638 else 0x37da35b63e8eb2b186fb9bd1b0e36c7d158e000cde8d6d8fa2b059619bd1b0e36c7d1582cb8f0737a361c6d8fa2b1c0019be2146c387d158c000cdedba35b63e8ac619be2146c38db1f456380038ecde8d870fa2b18775d466f46b6c7d158e337a361c77db63e8ac700071d9bd1ad01f45630cde8d6d97f5c4fa2b1c66f46b6c7d1582c03ae337a36776d96c3e8ac719bd1adb1f4759584f3800337c8e8d6d8fa2b180019bd1b04b6c7d158c000e6f37a35b63e8ac61bee6f46b6c7d1584f38) else (if i < 13 then 0x337a35b63e8ac049866f46b6c7d15821024e000cdeb4a35b63e8ac600066f46d0cdb1f45630cdeb4a35b63e8ac109c66f46b6c7d1582107ae337a361c6d9a03e8ac70006af46b6c7d158213000357cde8d6d8fa2b186af9bd1adb1f456084e000cdef2b2db63e8ac600066f46b6c7d1ea5630cde8d9ddb63e8ac20dc66f46c38db1f4560b0e000cde8d9ae1c3e8ac61d271d9bd1adb1f4563800337b2e8d6d8fa22180019bd1afcb6c7d158c337b2e8d6d8fa348ac719bd1adb2fe7d1584f38 else 0x337a35b63e8e92b1866f46b6c7d1a456084e337c8f10a35b63e8ac719be2146b6c7d1584f38cde8d6d96c3e8ac00dc7819bd9746b6c7d158e337bca8d6d8fa2b042719bd1adb1f475958213800337a35b63e8d32b1866f9951b35b6c7d158e337a35b63e8ac2788870000019bd1b081f45628cdf08a35b6680fa2b1c0019bd1adb21c7d158c337a35b65fcfa2b042719be2146b6c7d1582138cde8d6d9a03e8ac109c66f46b6c7d15844106e000cdee86d8fa3acac619bd1b3bb6c7d1584438)))) else (if i < 21 then (if i < 17 then (if i < 15 then 0x3becde8d6d8fa2b180019bd8346b6c7d158c3becde8d6d96c3e8ac700066f46c0a7d1584430cde8d97db63e8eb2b1c66f46cd6db2d87d158e00000337a36543e8ac50006fb9bd1adb1d6563000000cde8d6d95d3e9466f7951b3bb6c7d158e00000337a35b63e8c4519bd1adb1f475958443800337a361c3e8ac109866f7951adb1f456112e000cdf10b2db63e8ac619bd1adb1f47599a5638cdf10a35b63e8ac00dc71d9bd1b4336c7d158e000cdee8a35b63e8ac600066f5a36c7d1582130 else (if i < 16 then 0xea337bca8d6d8fa2b1c66f46b6cb61f456084e337a35b65b0fa2b070719be2146b6c7d1d25638003c1cde8d6d8fa2b1866f7951adb3367d158e000cde8d6d9593e8ac60000019bdd0db1f4562800000cde8d6d90e2b140019bd1b359f4560b0c337a35b65b11e3e8ac719bde56fd1adb1f45638cde8d9ddb63e8ac00dc6cb9bd1adb1f456006e337c42cba35b63e8ac71c766f46b6c7d15852b800337a36826d8fa2b180019bdbf46b6c7d158c337a35b63e8ac22003719bd1adb2d8ac9f45638 else 0xcde8d6d8fa2b09e0f5c0019bd1adb1f479958c000cde8d6d9903e8ac619bd1adb1f47595801b8003b1cde8d6d8fa2b1866f60d1adb1f45613ce000cde8d6d96c3e803619be2146b6cb61f45638cde8d6d8fa2b058109c0019bd9746b6cb61f4c000cdec16d8fa2b09e61d8f519bd1adb1f4563800373a35b63e8d22b187519bd1adb1f456006e337a35b6680fa348ac719bd1adb2d87d1582c38df737a35b6680fa2b1c6e79bd1adb1f469158e000cde8d6d8fa2b09c600066f46b6c7d1583830)) else (if i < 19 then (if i < 18 then 0x36fcde8d6d8fa2b1871db2e6f46b6c7d158e00000337b2db63e888519bd1adb1f4561102c38cdf10a35b63e8ac221c6fb9bd1b3bb6c7d158e000003a89ddb63e8ac519be4746c38db1f45638cdf10bfa8d6d8fa2b1c7519bd1b0e36c7d158e337a35b66816c3e8ac719bd1b35b6c7d1582138cde8d6d96c3e8d22b1c0000066f46b6cb6006a000cde8d6d9ab3e8ac619bde546b6cb61f45638cde8d6d96c3e8eb2b1c7639bd9746b6c7d158e000d6e8d6d8fa2b08860000019bd1b0e1f42128 else 0xcde8d6d9373e8d22b1c67b9bd1adb1f456006e000f0337a35b63e8ac600066f49d1adb1f4563000337bca8d6d96c2b1866f46cef0e36c7d158e337a361c825b63e8ac7000001b2d1adb1f44f28cdf10a36776d8fa2b1c66f46cd70e36c7d158e337a35b65fd6c3e8ac719bd1adb1f45613c01b8cdef2a35b63e8ac161c0019be2146cd67d158c000cde8d6d8fa334ac619bd1b0e36cb61f4563800337a35b666cfa2b1866f65d1adb1f456084e000cf68d6d8fa2b003600066f46cd6db1582c30) else (if i < 20 then 0xcde8d6f0fa2b1466f46c38db1f475958e00000337a35b6518ac500066f46b78db1f4563000000cde8d814fa2b147759be2146b6c7d158e000cde8d9adb65b0ac61c766f46ceedb1f4563800337a35bc3e8ac00d871d9bd1b35b6c7d158e000cde8d6d8fa2b09f61c766f65d1adb1f45638cde8d6d96c3e8ac279c6cb9bd1adb1f456084e00000337a35b657cac519bd1b0e36c7d1a4563800337a4db63e8ac00d866f7951b0e36c7d158e38ecde8d871b63e8ac71b2e6f46ceedb1f45638 else 0xd9737a361c6d8fa2b1c66f7951adb2fe7d158e337a366b6d8fa2b00370000019bd68db1f45628cde8d9ddb63e8eb2b1c66f46b6c7d1a456006e337a361c6d8fa2b04271bee6f46b6cb61f45638cde8d9adb63e8ac161c749bee6f46b6c7d158e000cde8d6d91e3e8ac619bde546b6c7d1584f3800337a361c6d96c3e9866f46b6c7d1a4560b0e37dcde8d6d8fa2b003700066f65b6c7d1584430cde8d6d9a03e8ac00dc7519bd1adb1f45614ee000cde8d871b63e84261e0e6f46b6cb61f45638))) else (if i < 25 then (if i < 23 then (if i < 22 then 0xcde8d6d8fa2b09e161c66f8851adb3407d158e337a35b63e8eb2b05871b2e6f46b6cb61f45638ea337a35b6680fa2b1c71d9bd1adb1f456006e000e3a8d9ddb63e8ac619bd1b3bb6c7d1582c38cde8d6d97f3e8ac049c0000066f882fe7d158a38ecde8d6d8fa2b09e71c766f46b6c7d1582138cde8d6d95d3e8eb2b1c001c366f46b6c7d158c337a4e8d6d8fa2b00370006fb9bd1adb2d8563000337a35b66bcfa2b187519bd1adb35e7d158e0000033da35b63e8ac519bd1b35b6c7d1584438 else 0xcdf10a35b65fcfa2b1c66f46b6cb61f456110e337a35bc6d8fa2b0037000751bed1adb1f4563000337b968d6d8fa2b1866f46b6c7d15821006e337c8ecba35b63e8ac719bd975c51adb1f45638cde8d6d8fa2b05814dc71dbee6f46b6c7d158e3c0cde8d6d96c3e8ac7000001b9d1adb1f45628cde8d6d8fa2b09e109c0019ee6f46b6c7d158c000cde8d6d90e2b042619bd1adb1f4560b001b8cdf10a35b63e8ac161c0000066f46cbe7d158a337bca8d6d9a03e8ac7000001abd1adb1f45628) else (if i < 24 then 0xea337a35b63e8ac029c0019bd1adb1f45614ec400cde8d6d8fa3d4ac639bd9746b6cd01f45638cde8d9adb63e8ac279c001db66f46b6c7d158c337a35b65fcfa2b003719bd1b25b6cbf9f45638cdecba361c6d8fa2b1c7519bd1adb2d87d158e3a8cdf10a35b63e8ac71bee6f46b6c7d1582138cdecba35b63e8ac00dc66f46cd6db1f456086e37dcde8d6d97f3e8ac700066f46b6c7d1581eb000365cde8d6d96c3e98001d266f46b6c7d158c337a36546d8fa348ac719bd9746b6cc81f45638 else 0xcdf105fcfa2b148019be2146afe7d158c400cde8d6d9713e8ac620066f46b6c7d1581cb0cdf10a35b63e8ac0e5c0019bd1adb1f456138c400cdefea35b63e8ac62007759bd1adb1f4563100337a35b64c0fa2b1866f46b6cd02607d158e0000038ea35a03e8ac520071d46b6cd01f45631003a8a35b6680fa2b188019be1146b6c7d158c400cde8d6d8fa2b0a5620071d46ceedb1f45631cde8d9ddb63e8ac209c0019bd7b46b6c7d158c400cdee5a35b63e8ac620066f46b6c7d1580530)) else (if i < 27 then (if i < 26 then 0x337c42f26d8fa2b188019bd1adb3367d158c400cde8d979b63e8ac620066f6fd1adb1f4563100337a35fb6d8fa2b180000066f7436c7d158a40000337a35b6574fa520066f46b6cae9f4563100000df68d6d8eb2b14801bed1adb1f475958c40000337a365f3e8ac520066f46cbe7d1d6563100337ba28d6d8fa2b18efb9bd1adb1f456032e000e3b7da35b63e8ac620066f46b6cd59f45631003a8df68d6d8fa2b188019bd1b4136c7d158c400cde8d6d95c3e8ac600066f46bf2db1f45631 else 0x337a35b63e8ac10d88019be2146cd67d158c400cde8d8b9b63e8ac620066f9951adb1f45631e3b37a35ed6d8fa2b1c66f46c46db1f469158e00000337a35b64dcfa520066f46b6c9b9f4693100337a35b64dcfa2b188000066f7936c69158a40000337a36543e8ac5200001d44eedb1f4562900337a36543e8d22b188019bd1b2a36c7d158c400cde8d6d8fa334ac6200001b9d1adb1f4562900373a35b63e8d22b188019bd1adb1f456096c337bca8d6d8fa2b04b700066f46b6c7d15844b1) else (if i < 28 then 0x337a35b657cac27988019bd1b0836c7d158c400cdec1a35b63e8ac63b2e6f46b6c7d158123800337a35f26d8fa2b180019bd1b0736c7d158c400cded2a35b63e8ac61b2e6f46bdadb1f4563800000cde8d6d8fa31148019bd1adb1f462158c400cde8d92db63e8ac620066f46cd6db1582c31cde8d6d8fa348ac0cdc0019be4746b6c7d158c400cdedba35b63e8ac620066f46b6c7d15829b10036fa35b63e8ac16188019bd1adb31a7d158c337a366b6d8fa2b091719bd1b20472db1f45638 else 0x337a35b6518ac2218e919bd1adb1f4560f6e00000337a36053e8ac520066f46b6c7d15841b100000d6e8d6d8fa2b14801add1adb1f456110c40000337a4db63e8ac520066f46b6c7d15830b0cde8d871b63e8db2b1c0019bde565b6c7d158c400cde8d6d8fa34cac639bd1adb2fe7d15819b800337ae28d6d8fa2b18801abd1adb1f456084c737bca8d6d9293e8ac700066f46b6cd31f456310038ecde8d9acfa2b18801b2e6f46b6c7d13cc400d968d6d8fa2b09e639bd1afdb6c7d1d65638))))) else (if i < 44 then (if i < 36 then (if i < 32 then (if i < 30 then 0x3becde8d6d8fa2b188019bdf346b6c7d158c337a35ed6d98d3e8ac700066f46c38db1f4213100337a35b6438ac10988019bd1aefb6c7d158c737a366b6d9293e8ac700066f46c0a7d158443100337a35b63e8ac04988019bd1adb1f456020c000cde8d6d8fa2b059620066f8851b0e1f4563100337a36096d8fa2b18801cde6f46b6c7d158c400cde8d9c9b63e8ac619bd1adb2eab61f45638cde8d9c9b63e8ac221c0019bdb6db1f4560b0c737a36408adb63e8ac70000019bd96db1f44429 else (if i < 31 then 0x337a4e8d6d8fa2b188000066f60b6c7d158a400cde936d8fa2b00362000019ed1adb1f456290033da35b63e8ac00d88019ee6f46b6c7d158c400cde8d6d9753e8ac619bd1b35c80db1f4563800365cde8d6d96c3e98e6f46c9adb1f45613ce000cdf109ddb63e8ac620066f8151adb1f4563100337a35b63e8ac1c188019bd1adb1f479958c400f0737a35b63e8ac620066f46b6c8f1f45631cde8d901b65b0fa2b1c7519bd1b2036c7d158e000f0337a35b63e8ac62000019bd1adb28c5629 else 0xcded2a35b63e8ac161c66f46b8edb1f456066e3a8cde8d6d8fa2b033700066f46cb0db1f4563100337a35b6640fa2b18e6f4f51adb1f456066e3bbcde8d6d8fa2b003719bd1b0e36c7d1583db8cde8d901b63e8eb2b1c0019bd1adb1f45605ac337ab68d6d9293e8ac7000751b2d1adb1f4563100337a367d6d8fa2b188019bd1adb2d87d006c737a35b64a4fa2b058700066f46b6cb615801b1cde8d6d8fa2b07b161c0000066f46b787d158a400cde8d6f0fa2b00363c766f46b6c7d1583db8)) else (if i < 34 then (if i < 33 then 0xcdef9a35b63e8ac109c66f46b6c7d17256066e337a366b6d8fa2b033700066f46b6cac9f45631cdef2a35b63e8ac0cdc66f65d1adb1f456066e000d5f37a35b63e8ac63bee6f46b6c7d15819b800337a35b63e8ac09580019bd1adb20c7d158c378cde8d901b63e8ac700066f46b6cae9f475b100337a35b657cfa2b18e6f8851adb1f456066e337a35b6680fa2b03370000019bd1adb2d801a9e3b37a35b63e8ac0cdc0019bd1adb1f45607ac400cde8d6d8fa36cac619bd1adb1f4560661538 else 0x337ab68d6d8fa2b1866f46bdadb1f475958e000ea3379ddb63e8ac639bd1adb2527d1b8563800373cde8d6d8fa2b188019be2165b6c7d158c400e3b65a35b63e8ac620066f65d1adb2d87d3100337a36103e8ac27988000066f46b6caf958a737a35b65b0fa2b033700066f46c38db2d87d3100337b2db63e8ac2218e6f46b6c7d15844066e38ecde8d6d8fa2b010700066f46c387d1582131d9737a35b63e8ac0cdc0019bd1adb1f456034c337a35b63e8ac0cc1a700066f46b6c7d1725630) else (if i < 35 then 0xd8337a35ed6d8fa2b1c66f46b6c7d1581985ae000cdf10a35a03e8ac620066f46b6c7d158313000337bca8d6d8d22b18e6f46b6c7d1583d8c4e000cde8d6d9153e8ac619bd1adb2fe7d1583db8cde8d6d8fa2b07b00dc0019bd1adb29a7d158c337a35b63e8ac2207b700066f46b6c7d15835b0df737a35ed6d8fa2b1c66f46bacdb1f4560f6e337a36776d8fa2b07b700066f46b6c7d1583ab000337bc9b63e8d22b188019bd1adb1f456048c37dcde8d901b63e8ac700066f8836cbf9f45631 else 0xcde8d6d8fa2b09e1edc66f46bdadb1f469158e000d4b37a35b63e8ac619bd1b2036cd01f45638d4b37a35b64a4fa2b1c66f46bdadb1f4560b0e337a35b63e8ac1ec75719bd1b20438db1f45638d9737a35b63e8ac1edc001ade6f46b6c7d158c737a35b63e8cb2b07b700066f46c46db1f45630cde8d9adb63e8ac1edc66f65d1adb1f4560c2e337a361c6d9293e8ac719bd1adb1f4691583db8cde8d6d8fa3acac1edc66f46bdadb1f456084e00000337a361c3e84253bee6f46b6c7d1583db8))) else (if i < 40 then (if i < 38 then (if i < 37 then 0x38ecde8d5fcfa2b18e6f46c38db1f456066e000cde8d6d9463e8ac639bd1adb2fe949f45638cde8d9de406d8fa2b1c66f8851adb2527d158e000ea337bc9b63e8ac639bd1adb1f4560f62138e3b37a35b64a4fa2b1c66f46bdaee36c7d158e337a36776d9293e8ac700071d9bd1b0e1f4563100000cde8d9acac16148019bd1b35c387d158c737b1a8d7b5b63e8ac700066f46b6c7d1d25631cde8d6d8fa2b03300dc0019bd1adb2467d158c000cdeb4a35b63e8ac639bd1adb252919f45638 else 0x337ad1b63e8ac10988019bd1aee36c7d158c00000337a35b6438ac539bd1b35bdadb1f4563800337a35b63e8ec2b18e6f46b6c7d1d656066e337b2e8d6d9293e8ac71b2e6f46b6c949f45638cdef2a35b63e8ac1edc66f46b6c949f45613ce000cde8d6f1b63e8ac639bd1adb1f45608419b8cde8d6d93e4a4fa2b1c0000066f5a36c7d158a400cdeeda35b63e8ac600075146ceedb1f456310036fcde8d6d8fa2b18e6f76d1b2036c7d158e337a35b64a4fa2b092700066f46b6c7d1b85630) else (if i < 39 then 0x37dcde8d6d8eb2b188019bd1adb2327d158c000e1b37a35b63e8ac620066f7951adb2d8563100337a35b6660fa2b1866f46c38f6b6c7d158e3a8cde8d7b5b63e8ac700066f46b6c7d1965630cde8d6d9063e8ac0cdc66f65d1af6b6c7d158e337a35b63e8ac27833700066f46bacdb1f45630003a4cde8d6d8fa2b18efb9bd1adb2527d158e337a35b64a4fa2b003700066f46c56db1f45630cde8d7b5e76d8fa2b1c66f46b6c7d1582c066e00000357a35b63e8ac539bd1af6b6c7d1584f38 else 0x337a36866d8fa2b18e6f7951af6b6c7d158e000d2337a35b63e8ac619bd1af6b6cb61f4563800337a7a8d6d8fa2b1866f46c80db1f456110e337b2e8d901b63e8ac700066f46b6c7d158553000000cdedb6d8fa2b14e6f46c80db3307d158e337a35b65b0fa2b07b719bd1af6b6cbf9f4563800337a35e76d8fa2b1866f46b6c949f475958e000cde8d6d8fa2b04c619bd1adb1f4560f635b800337a35b63e8ac2098000006df46b6c7d158a400e3b37a35a03e8ac620066f46c2edb1f45630)) else (if i < 42 then (if i < 41 then 0x37dcde8d6d96c2b18e6f65d1adb1f4560f6e337a35b6680fa2b07b719bd1b2036c7d1a4563800337a35b66bcfa2b18f1d9bd1b2036c7d158e000cde8d6d8fa3e0ac600066f46c8adb1f45630cdf10a35ed6d8fa2b1c001d466edb2fe7d158c737c428d901b63e8ac719bd1adb1f4560f6263800337a35b63e8ac0758e6f46b6cd02527d158e365cde8d901b63e8ac719bd1adb2527d1a45638cde8d9dded6d8fa2b1c000006cb46b6c7d13ca737a35ed6d8fa2b0aa700066f65d1adb1f44431 else 0xcdf10a35b63e8ac1edc0019bd1adb1f4620b0c737a35ed6d8fa2b088700066f46c72db1f45630cde8d916406d8fa2b1c66f46c80db2fe7d158e000cde8d6d93e3e8ac60007519bd96db1f45631003bbcde8d6d8fa2b18001db66f46b6c7d158c737a35b64a4fa2b042700066f46b6c7d158153000337a36666d8fa2b1866f46be4f6b6c7d158e337a35b64a5193e8ac719bd1b2036c7d1584f38cde8d901b63e8ac161c0019bd1adb1f456124c000cdec16d8fa2b09e639bd1b33480db1f45638) else (if i < 43 then 0xcde8d901b63e8ac00dc66f46ceedb1f456066e3a8cde8d6d8fa2b07b719bd1adb1f45606612b800337a35b6438fa2b18e6f46bdadb1f456006e000cde8d9adb65b0ac620066f46b6c7d1584fb1cdef2a36406d8fa2b1c66f46bdadb3407d158e337a36177b5b63e8ac70007639bd1adb1f4563100378cde8d6d8fa2b1866f46b6ca6a527d158e337a36406d8fa2b042719bd1adb2527d158443800337a35b63e8ac0658001beecb46b6c7d158c400cde8d935b63e8ac600066f46cd67d1582c31 else 0x337a35fb6d8fa2b18800006fb46b6c75958a80000337a365f3e8ac540066f46b6cae1f4563100337a35b63e8ac0e588019bd1adb2607d158c400cde8d6d8fa2b00a620066f46b6c7d15848b000337a365f6d8fa2b188019bdd0db1f475958c737a35b65b1293e8ac70006c19bd1adb1f45630ea337a35b64a4fa2b1c66f46b6cbfab87d158e000cde8d815b63e8ac620066f46b8edb1f45630cde8d6d9153e8ac1edc0019bd8d46b6c7d158c337a36406d8fa3e0ac70000019bd1b081f45629)))) else (if i < 51 then (if i < 47 then (if i < 45 then 0x3bbcde8d6d8fa2b188000066f7436c7d158a80000337b2db63e88854000019bd26db1f4562a00000cf68d6d8fa2b150019bd1adb2ea7d158c400cdef9a35b63e8ac62000019bd68db1f4562a00000d5e8d6d8fa2b150000066f46b6caf958a800cde8d9c9b63e8ac620066f46c9adb1f4563100000d968d6d8fa27950000066f46c207d158a800cde8d6d8fa2b02462000019bde4db1a4562a00000cdedb6d8fa2b150000066f46b6c9b9f4a80000337a36543e8ac540066f46b6c7d15825b1 else (if i < 46 then 0x28d9adb63e8ac0cd880146b6c7d1a456066c400a35b6418fa2b033620051adb2fe7d15819b100310a35b63e8ac0cd880146b6c7d15819854c400a35c76d8fa2b033620053d46b6c7d15819b10028d6d8fa2b09e0cd8801b2d1adb1f456066c400cde8d6d8fa2b01a6200001c751ad01f4562a00337a35b63e8b92b188019bd1adb1f45604ac400cde8d6d9063e8ac620051adb3407d15819b10038ea35b63e8ac0cd88019bd1ae3b6c7d158c400a36776d8fa2b033620066f46b6c7d15816b1 else 0x348cddb63e8ac1ed8e6f46b6c7d1583d866e000cdecb6d8fa2b07b620066edb1f4691583db100337bc9b63e8ac1ed88019bb6cbf9f4560f6c400cde8d759b63e8ac620066f3bb6c7d1583db100337a35b63e8ac1d58801a466f46b6c7d158c4000035ba35b63e8ac540066f46b6c7d15819b00028d6d8fa2b03300d880146b6cb61f456066c400a35b63e8eb2b033620059746b6c7d15819b10028d6d8fa2b033069880146b6c7d1582c066c400cde8d6d8fa2b02a62000019bd1b029f4562a)) else (if i < 49 then (if i < 48 then 0x337a35b63e8ac06588019bd1af6b6c56154c400d4b37a35b63e8ac620066f46c38949f45631003376d8fa2b07b00d88000066f46cd6560b0a800cde8d901b63e888620066edb2d87d1583db100337871b63e8ac1ed88019be2146c80db1f4c400cde8d6d8fa2b091620066edb1f4560f63131003376d8fa32cac1ed88019bcd6db1f4560f6c400cddb63e8eb2b07b62006fb9bb6c7d1583db10038ecddb63e8ac1ed88019bb6c7d1583d8d6c400cddd66d8fa2b07b62006fb46b6c7d15819b1 else 0x337a35293e8ac109880146b6c7d1581984ac400cdecba35293e8ac62005e546b6c7d15819b100337a35ed79db62b18801d466edb1f4560f6c400cde8d535293e8ac620066f56d1a949f4563100337a352948cfa2b188019bd1adb2527d158c000d4b37a35293e8ac639bd1adb2527d1583db80028d6d8fa2b0880cd88019bd1a949f4560b0c400cde8d6d8fa2b092620066f46cd6949f4563100337a35a04a4fa2b18801c766f46a527d158c400cde8d6d8fa2b082620066f46b6c8c9f45631) else (if i < 50 then 0x3a8cde8d7b5b62b18801b066f46bdadb158c400df737a35ed6d8ac639bd1af6b6c7d15819b800337a35ed6d8ac00d88019bd9746c80db1f4c400cde8d7b5b62b058620066f46be4db1f4563100337a3677901b63e988019bd1af6b6c75958c400cde8d79db63e8ac62006c19bd1adb1f4563100337ab68d6d8fa2b188019bd1af6b6c69158c400cddb6454fa2b07b620066f46b6c8a9f456310028d6d8fa2b0330b588019bd1a949f456124c400cde8d5b1293e8ac620066f6351af6b6c5631 else 0x337a35ed6d98d2b188019bd1adb3307d158c400cde8d4a4fa2b09e620066f46c38f6b6c563100000dbe8d6d8fa2b150000066f60b6c7d158a800cde8d7b5b62b09e620066f46c46db1f456310028d871b63e8ac0cd88019be20db1f4560f6c400cde8d7b5dc6d8ac62006cb9bd1af6b6c563100337a36456d8fa2b188019bd1af93dadb158c400cde8d8e5b63e8ac62007519bd1a949f4563100337c428d7b5b62b188000066f46b6c7d188a800cde8d6d8fa2b061620066f46ceef6b6c5631))) else (if i < 55 then (if i < 53 then (if i < 52 then 0x337a36406d8fa10988019bd1b2036c7d1d6c400cdeeda35b63e8ac620066f46cd6f6b6c563100337a35b63e8f82b188019bd1b2036cd01f4c400cde8d6d9233e8ac620066f46a7c949f4563100337a35b63e8dc2b188019bd1adb29a7d158c400de337a35b63e8ac620066f46bdadb1f4563000365cde8d901b63e988019bd1af6b6cb6158c400cde8d7b5b65fcac620066f6351adb1f4563100365cde8d4a4fa2b188019bd1af6b6cd0158c400cde8d7b5b62b042639bd1b2036c7d15819b8 else 0xcde8d901ed6d8fa2b1c0000066f46b6c7d158a000de337a36406d8fa620051adb1f45c95819b100000dce8d6d8fa2b1566f46c80db1f4560f6e00000337a35b6438ac540066f46b6c7d158553100337a3645901b63e988019bd1b3336c7d158c400cded2a35b63e8ac620066f65d1af6b6c563100337a35293e8ac00d88019bd1a949f46e158c400cddb63e8ac2207b620066f46c80db1f401b10038ecde8d901b63e98801d466f46c80db1f4c400cde8d901b65b0fa620066edb1f4560f62631) else (if i < 54 then 0x337a35b63e8ac18988019bd1aee36c7d158c400cdef2a36406d8fa620066f46b6cc69f456310028d6d8fa2b0420cd88019bd1b20438db1f4c737a35ed6d8fa2b07b700066f46c80db2fe7d310037dcde8d4a4fa2b18e6f46bdadb2527d158e00000337a35b6574fa540066f46c80db3307d3100337a35b63e8db2b188019bd1b20456db1f4c400cde8d6d93e3e8ac62000019be20bf9f4562a00337a36774a4fa2b188000066f46c387d084a800cdeeda36406d8fa620066f46b6c7d1583db0 else 0x337a35b63e8ac1ad88000066f46b787d158a80000337a35b65b003540071d9bd1af6b6c563100337a36406d8fa2798801bee6f46c80db1f4c400cde8d6d8fa32cac620066edb1f45613c3db100337a366b901b63e988019bd1b2036c7d1f0c400cde9ea35b63e8ac6200001d44eedb1f4562a00337a36176d8fa2b188019bd1b15b6c7d158c737a35b64a4fa2b033700066f46c80db1f4563000337bca8d4a4fa2b188019bd1a949f456110c400cde8d901b63e8d2620066f46c2ef6b6c5631)) else (if i < 57 then (if i < 56 then 0x365cddb63e8ac1ed88019bd1b20472db1f4c400cde8d4a5193e8ac620075146b6c7d15819b100337a357f4a4fa2b18e6f46c80db2527d158e000cddb63e8ac1ec4262000019bd1adb28c562a00337a35b63e8ac13188019bde546bdadb158c400cddb6680fa2b07b620066f8851a949f45631003376d8fa2b07b1d588019bd1b33480db1f4c400cddb63e8ac1ec58620066f46bdadb158443100337a35293e8d22b188019bd1adb1f456020c400cde8d901b63e858620066f46a527d1d65631 else 0x337a35ed6d9292b188019bd1af6b6c56066c4000028d4a4fa2b03352000019bbdadb1583da900000cde8d7b5292b148019bd1af6b6c560f6c400cde8d7b5b63e8ac62000019ba527d1583da90028d6d9293e8ac0cd88019bd1af6a527d158c400cddb64a4fa2b07b620051b2036c7d15819b100337a36406d9293e988019bbdadb1f4560f6c400cde8d6d8fa2b07b620051af6b6c7d15819b100337a35293e8ac1ed88000036c7d1583d866a400cde8d6d8fa2b033620051adb1f4560f619b1) else (if i < 58 then 0xcde8d6d8fa2b150000066f46bda94958a8000028d4a4fa2b0335400000db1f4560f619aa00337a36406d8fa1ed88019bd1b203dadb1f4c40000337a36407b5b652000019bc80db1f43da900000a35ed6d8ac0cd48000051b2036c7d066a400cde8d4a4fa2b033620066f46b6c949f4563100337a36404a4fa2b188000066f46c80949f4a400cde8d901b63e8ac62000019bd1adb1f45629003376d8fa2b07b0cd88019bd1b203dadb158c400cde406d8fa2b07b620066f46c80db1f419b1 else 0x66f46c80f6b6ca8000028d7b5b62b033540000146c80db1f419aa00000cde8d901293e950000066ef6b6c560f6a80000337901b63e87b54000019ba527d1583daa))))))
private def st6 (i : Nat) : Nat := unpack st6Packed 77 20 i
private def adj6Packed (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0x140081009084a2000223040011006102e300402180150046018c2010ca33842101040128002340102da61a88032406205e1 else 0x50b10c206851011c620486028c6001025018200884000060004a0080c21184108c61194a120c010084b1848401c63180c1) else (if i < 3 then 0x404a40c0a801000200804408ce20828f08400101826000200401000613a841081030240000020088c2084200804312926 else (if i < 4 then 0x6880d088000440a284021840008c45080026004200c0d100402000b20540304a73012120822404414bc21614010006118461 else 0x1005401002a380ca08461200210008328021280004806011824204e0581421844011804000010008600c002186928039)))
private def adj6 (i : Nat) : Nat := unpack adj6Packed 5 80 i
private def loc6Packed (i : Nat) : Nat := (if i < 11 then (if i < 5 then (if i < 2 then (if i < 1 then 0xe4c809d733aa740030d000390e4048000635e80004506a8ba0005a8402380005783e112000000021a700082e610000003de0bc0029955e209eb0003a48b487000840000ac9cd752001be000000de4003e38189e4a0b696f695620b4670e001e9000000b780045385887473800 else 0x140c9400000000d2d5cb6e264e34728008e60d0000e6348e81479770004818214c7d6000002c800098c002214000000000002c3787e8006d600129800000c3c3380066a0906781448c000f738936c100000008a0bc45980067ab19a88305400019baa73d4000000006520000017e) else (if i < 3 then 0x6bb0580000006c00140000408a90002717991221a8ef32e109b880011037d3f000001021470174740007bc802be000fba130003d4001020008c1cb80019a000000005270f5bf8001c600000284628bd9a147b3301ccd70007d81c0f12cb0080008fb5f0002b40000027f13809192 else (if i < 4 then 0x5a5ec00000000000002ba800568002450d8131698000d2c74002b20000020c2f026e000f280063e001362fc268fb9af29f47b11493850000528002650005fc001a100060556b2d5628a9483955024b444b1b14a9453f9c40001dc0020e47e61d62000910bc99b40d39e1e875800 else 0x64244c0048560af6879056612f7ca82b07ccd680024b0000021700000001400000546bb42a0dc77e081c30008f049935a2f18af00e39368dc001dba4d7389f4003a800000000000000001b440f0000004f000000000f34540000023138c4180000040659800145bf24ea46800000))) else (if i < 8 then (if i < 6 then 0x1600015096734c018000320001e53d8945502a1e500062072400131000002021d1888128914151ec0005aa8d0002ac000003f40000000001c00000000918d1d2e000000d9c000004720018d0c01941984541d000b84002fe10a0000048b66802d1721069886800021190000002d7 else (if i < 7 then 0x218b56000d6e4092b7540018b37680a0003ec565c4b14000005d0a9400090644000002983ac002468008ca001731624521ee1d0004beb7c000003f290c5b2ab00061a3b8006f00001d3ad0002ec851a83b0f19b83660010fe2b99a000e05bd3d900003400256076e6018c19 else 0xbe52c800000cec0000086e6ae2c80074e000000005baf780008416e0023300029a8799044270481400410000000000610009762f00012713c0014f8d809c000000000008489b230ecdc20ed266b90000003ec0018e1e1236845890000269a5270000001b5dc33e59200212800)) else (if i < 9 then 0x4c2000c78000011f8002ff000d280d0000000010b80790420d998004f8000002485d2b00000005acf895a0fc1e0000ea19f5120000023e000000001f18951b5563d337e271b22ce18d1d8cca3b2a6000000000006f53c11200015448a9c000bdc6825b3bc9b8370000000019e3fa else (if i < 10 then 0x1929e8f99210011c4000003e00002d0e2000000000008d4acca90c406a308003af8a2000e1bcf8f8b1c6b220278001b0385000824c0000000000841b10007fdfb8000367ede8b4f49f03894b441e8000b48000ea0019c8728d6ad80c0d30000e400092000e951c0007e09b45e800 else 0x79080c430006266400032c0005b9fc000000000bd000000008ef8cb5700000036c000000b8c646565b1f035334a000002164a0000002d14e4440000000011d6261bb7e23e8d0000000a280f8006b00240048a0001892600045600000028000000000000006e80025822b0cc9a800)))) else (if i < 16 then (if i < 13 then (if i < 12 then 0x7c800000128000001f98000000013a1540000001c0e884cc44548005d8b0c0000073411c920000009500017005400180b24032d54eac2d30a7e0320004ee3c56c0003d289dd100090cb08674617b8c219fc1c24688cd68005944940026f3d70f0d4800000f5ddd0007640023a000 else 0x7b0ba8003455e64442fa9e0000000000000056c953773c6000001e46b8808962961aa000000007e800183c1a0011c8c51c5630000ae02b0002c534300164410a200052a000e58003fc000000002bca480e1720004f80043b00117400000001224003620182d118a8c00074de1897) else (if i < 14 then 0x4b0d9488005b400000000000230cb3918f251db522c000b54358006a03680020d000ad60fb837ba7d1da8005f4124001bc0007b00000040e76c003c77faeb8000008691fc003ac23c0f0618d409ed000f000714bd4001c2000000bc23582445cdba6200082c000e122860e31800 else (if i < 15 then 0xbc000a28001d2000000001420008e8ae5fa50e230000ae0007fb9900086d5300062ae008b18847910000000828aa4ca42a7968499509913a2e10c00052e1fe41800000304689a2826001e0c5a32a160003170005f4164110010091280064c00243aeb0001f1830a4322b9c878d7 else 0x1d499e42065116000001b5000001b0a37410ffc258436af23a2929b48e31dc7b9d7ca0017746f382000f3c1b7eadbe2c372660fa02e0001e70857daf40001a9f6a880000019190d414e39a91da692525d8800000b9538214000000003942326b097015154772118001723e568000))) else (if i < 19 then (if i < 17 then 0x18e1103d00011618000000000000008ce002039e00000cd8c98e000181c93547ecab8001be17e16400000686000001635de7b427165000df94196813e95c6c1cc746000000e02380004c0ee710ef0003c40d03300000003a555f7800006ed0760000010a0bb0008d10909eabf else (if i < 18 then 0x6da00160c297f864db1a860006096c8006ca41400000816201978a7000888468bc000741f08002d6b8c000002c0700000000531e8d9b8b000a519c16d000728000002f8110d90fb8d20000000064f0e12d05b0000000030c650519fda824e637507c3e000544c613a000000a5800 else 0x1480042b000000000005c0ec22f8531a4e980025e27000000a8700023c002400005a8000230009086d800466dd22589a000ce8000a67d4001cd800864044002412905cdd0800020c0c9790b00068c000000005d40000050a9aa0542746c001a08000000000010c4946c0003bb)) else (if i < 20 then 0x79a0017c00000000000081000000002265a4001cf800576558003bd00025400276082000003d5338aa8fe8000000003b44d00087083000000ed85788e3f82e9193c207ce90001ce000ff8001d9000000f93c92ccadc0009648800023000000f9c0015d000fa4c499b2ae00037b75 else (if i < 21 then 0xa8800000260000b20000001740037d0000019902e316000002667a8000000008120022ac1e0e8001fca0133c1f8002bd88e5bc000d9662d20ee80000000000403000dccdc2dc614818000000005840545c2842f8bc800000b3d0a9f50002880015835e001ed800158e4000000 else 0x29a000af83c40159a864f40717723f8a73ce46800081b028c0f162db5936841c001b9000c38000004c069c000002760013244363c00051bbe01ed340042f280e5a2485138c1341b826000b6c9cb0b492eac43a5265c0001f8008fb0e50f8220000000039e)))))
private def loc6 (i : Nat) : Nat := unpack loc6Packed 11 80 i
private def st7Packed (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0xcde8d6d8fa2b003619bd1b0e36c7d158c38ecde8d6d8fa2b1866f46b6cb61f45630df737a35b63e8ac619bd1adb1f456110c337a35b63e8ac109866f8851adb1f45630cdecba35b63e8ac619bd1b35b6c7d158c337a35b63e8ac27986cb9bd1adb1f45630ea337a35b63e8ac619bd1adb1f4560b0c337a35b65fcfa2b1866f46b6c7d1a45630cdef2a35b63e8ac619bd1adb1f475958c337a35b6680fa2b1866f46ceedb1f45630 else 0xcde8d6d8fa2b042639bd1adb3407d158c737a35b63e8ac00d8e6f46c80db1f45630cde8d6d8fa2b058639bd1adb1f4560f6c337a361c6d8fa2b18ecb9bd1adb1f45631cde8d6d8fa2b088639bd9746b6c7d158c737a35b63e8ac2798e6f46cd6db1f45631cde8d6d8fa348ac639bde546b6c7d158c77dcde8d6d8fa2b18e6f46b6cbf9f45631cdf10a35b63e8ac63c766f46b6c7d158c737a36776d8fa2b18f519bd1adb1f45631) else (if i < 3 then 0x28d6d8fa2b033539bd1adb1f456066c737a361c6d8fa2b1966f46b6c7d1584432cdecba35b63e8ac65b2e6f46b6c7d158cb37a35b63e8ac161966f46cd6db1f45632cdef2a35b63e8ac659bd1b3bb6c7d158cb7dcde8d6d8fa2b1966f46b6cbf9f45632cdf10a35b63e8ac65c766f46b6c7d158cba8cde8d6d8fa2b1966f46b6c949f45630cde8d6d96c3e8ac639bd1adb1f475958c737a35ed6d8fa2b1866f46b6c7d15819b0 else (if i < 4 then 0x3376d8fa2b07b540066f46a527d158ab37a35b64a4fa2b1966f46b6c7d1583db20028d6d8fa2b033559bd1adb3407d158cb37a35b63e8ac109966f46b6c949f4563100337a35ed6d8ac539bd1b2036c7d158c737a35b63e8eb2b190019bd1b2036c7d29cde8d7b5b63e8ac639bd1adb1f469158cb37a35b63e8ac27990019bd1a949f45629cde8d6d8fa2b003640066edb1f4560f6a737a35b63e8ac1ed8e6f46b6cb61f45632 else 0xcde8d901b63e958019bd1af6b6c562b00337a35293e8ac560066edb1f4560f6ac00a35b63e8ac0cd58019bd1b2036c7d2acde8d6d8fa2b033640066f46bdadb158ab37a36406d8fa2b1966f46bdadb1f45632)))
private def st7 (i : Nat) : Nat := unpack st7Packed 67 20 i
private def adj7Packed (_i : Nat) : Nat := 0x1c0118004108632854601421d0405400e42b500
private def adj7 (i : Nat) : Nat := unpack adj7Packed 5 80 i
private def loc7Packed (i : Nat) : Nat := (if i < 1 then 0x29a00c000000000013ab3f0000040001cb2c008663d660c00b52022892800651771068a000241e381878003069d570a8b80451c73ea89c0350141bab4601d260090280 else 0x2d78d801f01664b4110c000346498094017128400e80720000064000150002b8062965808d3d800401001ba4bd4580000811)
private def loc7 (i : Nat) : Nat := unpack loc7Packed 7 80 i
private def st8Packed (_i : Nat) : Nat := 0x19bd1adb1f4562ccde8d6d8fa2b15e6f46b6c7d158ab37a35b63e8ac539bd1adb1f45628
private def st8 (i : Nat) : Nat := unpack st8Packed 57 20 i
private def adj8Packed (_i : Nat) : Nat := 0x0
private def adj8 (i : Nat) : Nat := unpack adj8Packed 1 80 i
private def loc8Packed (_i : Nat) : Nat := 0x20000003000000400000040000000000000000000000000
private def loc8 (i : Nat) : Nat := unpack loc8Packed 3 80 i
private def certCount : Nat → Nat
  | 2 => 27
  | 3 => 760
  | 4 => 2566
  | 5 => 3379
  | 6 => 1167
  | 7 => 90
  | 8 => 5
  | _ => 0
private def certSizes : Nat → Nat × Nat
  | 2 => (11,67)
  | 3 => (257,1151)
  | 4 => (857,3851)
  | 5 => (1129,5077)
  | 6 => (397,1753)
  | 7 => (31,137)
  | 8 => (3,67)
  | _ => (1,2)
private def stData : Nat → Nat → Nat
  | 2 => st2
  | 3 => st3
  | 4 => st4
  | 5 => st5
  | 6 => st6
  | 7 => st7
  | 8 => st8
  | _ => fun _ => 0
private def adjData : Nat → Nat → Nat
  | 2 => adj2
  | 3 => adj3
  | 4 => adj4
  | 5 => adj5
  | 6 => adj6
  | 7 => adj7
  | 8 => adj8
  | _ => fun _ => 0
private def locData : Nat → Nat → Nat
  | 2 => loc2
  | 3 => loc3
  | 4 => loc4
  | 5 => loc5
  | 6 => loc6
  | 7 => loc7
  | 8 => loc8
  | _ => fun _ => 0
private def certState (k i : Nat) : SearchState :=
  let x := stData k i
  (x &&& 7, decodeWires (x >>> 7) ((x >>> 3) &&& 15))

private def certLocate (k : Nat) (x : SearchState) : Nat :=
  let (d,n) := certSizes k
  let h := stateHash x
  let slot := (h / d + adjData k (h % d) * (1 + (h / 1031) % (n - 1))) % n
  locData k slot

private abbrev checkCert := checkBatch certCount certState certLocate
private abbrev joinCert := checkBatch_join certCount certState certLocate

set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert2_0 : checkCert 2 0 27 = true := by decide +kernel

private lemma certLayer2 : checkCert 2 0 (certCount 2) = true :=
  cert2_0

set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert3_0 : checkCert 3 0 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert3_48 : checkCert 3 48 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert3_96 : checkCert 3 96 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert3_144 : checkCert 3 144 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert3_192 : checkCert 3 192 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert3_240 : checkCert 3 240 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert3_288 : checkCert 3 288 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert3_336 : checkCert 3 336 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert3_384 : checkCert 3 384 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert3_432 : checkCert 3 432 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert3_480 : checkCert 3 480 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert3_528 : checkCert 3 528 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert3_576 : checkCert 3 576 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert3_624 : checkCert 3 624 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert3_672 : checkCert 3 672 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert3_720 : checkCert 3 720 40 = true := by decide +kernel

private lemma certLayer3 : checkCert 3 0 (certCount 3) = true :=
  (joinCert 3 0 384 376 (joinCert 3 0 192 192 (joinCert 3 0 96 96 (joinCert 3 0 48 48 cert3_0 cert3_48) (joinCert 3 96 48 48 cert3_96 cert3_144)) (joinCert 3 192 96 96 (joinCert 3 192 48 48 cert3_192 cert3_240) (joinCert 3 288 48 48 cert3_288 cert3_336))) (joinCert 3 384 192 184 (joinCert 3 384 96 96 (joinCert 3 384 48 48 cert3_384 cert3_432) (joinCert 3 480 48 48 cert3_480 cert3_528)) (joinCert 3 576 96 88 (joinCert 3 576 48 48 cert3_576 cert3_624) (joinCert 3 672 48 40 cert3_672 cert3_720))))

set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_0 : checkCert 4 0 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_48 : checkCert 4 48 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_96 : checkCert 4 96 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_144 : checkCert 4 144 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_192 : checkCert 4 192 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_240 : checkCert 4 240 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_288 : checkCert 4 288 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_336 : checkCert 4 336 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_384 : checkCert 4 384 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_432 : checkCert 4 432 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_480 : checkCert 4 480 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_528 : checkCert 4 528 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_576 : checkCert 4 576 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_624 : checkCert 4 624 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_672 : checkCert 4 672 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_720 : checkCert 4 720 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_768 : checkCert 4 768 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_816 : checkCert 4 816 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_864 : checkCert 4 864 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_912 : checkCert 4 912 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_960 : checkCert 4 960 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_1008 : checkCert 4 1008 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_1056 : checkCert 4 1056 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_1104 : checkCert 4 1104 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_1152 : checkCert 4 1152 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_1200 : checkCert 4 1200 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_1248 : checkCert 4 1248 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_1296 : checkCert 4 1296 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_1344 : checkCert 4 1344 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_1392 : checkCert 4 1392 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_1440 : checkCert 4 1440 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_1488 : checkCert 4 1488 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_1536 : checkCert 4 1536 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_1584 : checkCert 4 1584 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_1632 : checkCert 4 1632 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_1680 : checkCert 4 1680 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_1728 : checkCert 4 1728 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_1776 : checkCert 4 1776 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_1824 : checkCert 4 1824 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_1872 : checkCert 4 1872 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_1920 : checkCert 4 1920 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_1968 : checkCert 4 1968 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_2016 : checkCert 4 2016 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_2064 : checkCert 4 2064 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_2112 : checkCert 4 2112 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_2160 : checkCert 4 2160 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_2208 : checkCert 4 2208 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_2256 : checkCert 4 2256 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_2304 : checkCert 4 2304 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_2352 : checkCert 4 2352 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_2400 : checkCert 4 2400 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_2448 : checkCert 4 2448 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_2496 : checkCert 4 2496 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_2544 : checkCert 4 2544 22 = true := by decide +kernel

private lemma certLayer4 : checkCert 4 0 (certCount 4) = true :=
  (joinCert 4 0 1296 1270 (joinCert 4 0 624 672 (joinCert 4 0 288 336 (joinCert 4 0 144 144 (joinCert 4 0 48 96 cert4_0 (joinCert 4 48 48 48 cert4_48 cert4_96)) (joinCert 4 144 48 96 cert4_144 (joinCert 4 192 48 48 cert4_192 cert4_240))) (joinCert 4 288 144 192 (joinCert 4 288 48 96 cert4_288 (joinCert 4 336 48 48 cert4_336 cert4_384)) (joinCert 4 432 96 96 (joinCert 4 432 48 48 cert4_432 cert4_480) (joinCert 4 528 48 48 cert4_528 cert4_576)))) (joinCert 4 624 336 336 (joinCert 4 624 144 192 (joinCert 4 624 48 96 cert4_624 (joinCert 4 672 48 48 cert4_672 cert4_720)) (joinCert 4 768 96 96 (joinCert 4 768 48 48 cert4_768 cert4_816) (joinCert 4 864 48 48 cert4_864 cert4_912))) (joinCert 4 960 144 192 (joinCert 4 960 48 96 cert4_960 (joinCert 4 1008 48 48 cert4_1008 cert4_1056)) (joinCert 4 1104 96 96 (joinCert 4 1104 48 48 cert4_1104 cert4_1152) (joinCert 4 1200 48 48 cert4_1200 cert4_1248))))) (joinCert 4 1296 624 646 (joinCert 4 1296 288 336 (joinCert 4 1296 144 144 (joinCert 4 1296 48 96 cert4_1296 (joinCert 4 1344 48 48 cert4_1344 cert4_1392)) (joinCert 4 1440 48 96 cert4_1440 (joinCert 4 1488 48 48 cert4_1488 cert4_1536))) (joinCert 4 1584 144 192 (joinCert 4 1584 48 96 cert4_1584 (joinCert 4 1632 48 48 cert4_1632 cert4_1680)) (joinCert 4 1728 96 96 (joinCert 4 1728 48 48 cert4_1728 cert4_1776) (joinCert 4 1824 48 48 cert4_1824 cert4_1872)))) (joinCert 4 1920 336 310 (joinCert 4 1920 144 192 (joinCert 4 1920 48 96 cert4_1920 (joinCert 4 1968 48 48 cert4_1968 cert4_2016)) (joinCert 4 2064 96 96 (joinCert 4 2064 48 48 cert4_2064 cert4_2112) (joinCert 4 2160 48 48 cert4_2160 cert4_2208))) (joinCert 4 2256 144 166 (joinCert 4 2256 48 96 cert4_2256 (joinCert 4 2304 48 48 cert4_2304 cert4_2352)) (joinCert 4 2400 96 70 (joinCert 4 2400 48 48 cert4_2400 cert4_2448) (joinCert 4 2496 48 22 cert4_2496 cert4_2544))))))

set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_0 : checkCert 5 0 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_48 : checkCert 5 48 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_96 : checkCert 5 96 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_144 : checkCert 5 144 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_192 : checkCert 5 192 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_240 : checkCert 5 240 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_288 : checkCert 5 288 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_336 : checkCert 5 336 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_384 : checkCert 5 384 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_432 : checkCert 5 432 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_480 : checkCert 5 480 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_528 : checkCert 5 528 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_576 : checkCert 5 576 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_624 : checkCert 5 624 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_672 : checkCert 5 672 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_720 : checkCert 5 720 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_768 : checkCert 5 768 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_816 : checkCert 5 816 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_864 : checkCert 5 864 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_912 : checkCert 5 912 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_960 : checkCert 5 960 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_1008 : checkCert 5 1008 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_1056 : checkCert 5 1056 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_1104 : checkCert 5 1104 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_1152 : checkCert 5 1152 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_1200 : checkCert 5 1200 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_1248 : checkCert 5 1248 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_1296 : checkCert 5 1296 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_1344 : checkCert 5 1344 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_1392 : checkCert 5 1392 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_1440 : checkCert 5 1440 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_1488 : checkCert 5 1488 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_1536 : checkCert 5 1536 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_1584 : checkCert 5 1584 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_1632 : checkCert 5 1632 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_1680 : checkCert 5 1680 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_1728 : checkCert 5 1728 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_1776 : checkCert 5 1776 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_1824 : checkCert 5 1824 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_1872 : checkCert 5 1872 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_1920 : checkCert 5 1920 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_1968 : checkCert 5 1968 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_2016 : checkCert 5 2016 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_2064 : checkCert 5 2064 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_2112 : checkCert 5 2112 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_2160 : checkCert 5 2160 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_2208 : checkCert 5 2208 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_2256 : checkCert 5 2256 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_2304 : checkCert 5 2304 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_2352 : checkCert 5 2352 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_2400 : checkCert 5 2400 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_2448 : checkCert 5 2448 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_2496 : checkCert 5 2496 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_2544 : checkCert 5 2544 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_2592 : checkCert 5 2592 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_2640 : checkCert 5 2640 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_2688 : checkCert 5 2688 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_2736 : checkCert 5 2736 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_2784 : checkCert 5 2784 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_2832 : checkCert 5 2832 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_2880 : checkCert 5 2880 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_2928 : checkCert 5 2928 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_2976 : checkCert 5 2976 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_3024 : checkCert 5 3024 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_3072 : checkCert 5 3072 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_3120 : checkCert 5 3120 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_3168 : checkCert 5 3168 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_3216 : checkCert 5 3216 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_3264 : checkCert 5 3264 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_3312 : checkCert 5 3312 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_3360 : checkCert 5 3360 19 = true := by decide +kernel

private lemma certLayer5 : checkCert 5 0 (certCount 5) = true :=
  (joinCert 5 0 1680 1699 (joinCert 5 0 816 864 (joinCert 5 0 384 432 (joinCert 5 0 192 192 (joinCert 5 0 96 96 (joinCert 5 0 48 48 cert5_0 cert5_48) (joinCert 5 96 48 48 cert5_96 cert5_144)) (joinCert 5 192 96 96 (joinCert 5 192 48 48 cert5_192 cert5_240) (joinCert 5 288 48 48 cert5_288 cert5_336))) (joinCert 5 384 192 240 (joinCert 5 384 96 96 (joinCert 5 384 48 48 cert5_384 cert5_432) (joinCert 5 480 48 48 cert5_480 cert5_528)) (joinCert 5 576 96 144 (joinCert 5 576 48 48 cert5_576 cert5_624) (joinCert 5 672 48 96 cert5_672 (joinCert 5 720 48 48 cert5_720 cert5_768))))) (joinCert 5 816 432 432 (joinCert 5 816 192 240 (joinCert 5 816 96 96 (joinCert 5 816 48 48 cert5_816 cert5_864) (joinCert 5 912 48 48 cert5_912 cert5_960)) (joinCert 5 1008 96 144 (joinCert 5 1008 48 48 cert5_1008 cert5_1056) (joinCert 5 1104 48 96 cert5_1104 (joinCert 5 1152 48 48 cert5_1152 cert5_1200)))) (joinCert 5 1248 192 240 (joinCert 5 1248 96 96 (joinCert 5 1248 48 48 cert5_1248 cert5_1296) (joinCert 5 1344 48 48 cert5_1344 cert5_1392)) (joinCert 5 1440 96 144 (joinCert 5 1440 48 48 cert5_1440 cert5_1488) (joinCert 5 1536 48 96 cert5_1536 (joinCert 5 1584 48 48 cert5_1584 cert5_1632)))))) (joinCert 5 1680 864 835 (joinCert 5 1680 432 432 (joinCert 5 1680 192 240 (joinCert 5 1680 96 96 (joinCert 5 1680 48 48 cert5_1680 cert5_1728) (joinCert 5 1776 48 48 cert5_1776 cert5_1824)) (joinCert 5 1872 96 144 (joinCert 5 1872 48 48 cert5_1872 cert5_1920) (joinCert 5 1968 48 96 cert5_1968 (joinCert 5 2016 48 48 cert5_2016 cert5_2064)))) (joinCert 5 2112 192 240 (joinCert 5 2112 96 96 (joinCert 5 2112 48 48 cert5_2112 cert5_2160) (joinCert 5 2208 48 48 cert5_2208 cert5_2256)) (joinCert 5 2304 96 144 (joinCert 5 2304 48 48 cert5_2304 cert5_2352) (joinCert 5 2400 48 96 cert5_2400 (joinCert 5 2448 48 48 cert5_2448 cert5_2496))))) (joinCert 5 2544 432 403 (joinCert 5 2544 192 240 (joinCert 5 2544 96 96 (joinCert 5 2544 48 48 cert5_2544 cert5_2592) (joinCert 5 2640 48 48 cert5_2640 cert5_2688)) (joinCert 5 2736 96 144 (joinCert 5 2736 48 48 cert5_2736 cert5_2784) (joinCert 5 2832 48 96 cert5_2832 (joinCert 5 2880 48 48 cert5_2880 cert5_2928)))) (joinCert 5 2976 192 211 (joinCert 5 2976 96 96 (joinCert 5 2976 48 48 cert5_2976 cert5_3024) (joinCert 5 3072 48 48 cert5_3072 cert5_3120)) (joinCert 5 3168 96 115 (joinCert 5 3168 48 48 cert5_3168 cert5_3216) (joinCert 5 3264 48 67 cert5_3264 (joinCert 5 3312 48 19 cert5_3312 cert5_3360)))))))

set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_0 : checkCert 6 0 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_48 : checkCert 6 48 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_96 : checkCert 6 96 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_144 : checkCert 6 144 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_192 : checkCert 6 192 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_240 : checkCert 6 240 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_288 : checkCert 6 288 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_336 : checkCert 6 336 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_384 : checkCert 6 384 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_432 : checkCert 6 432 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_480 : checkCert 6 480 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_528 : checkCert 6 528 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_576 : checkCert 6 576 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_624 : checkCert 6 624 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_672 : checkCert 6 672 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_720 : checkCert 6 720 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_768 : checkCert 6 768 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_816 : checkCert 6 816 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_864 : checkCert 6 864 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_912 : checkCert 6 912 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_960 : checkCert 6 960 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_1008 : checkCert 6 1008 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_1056 : checkCert 6 1056 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_1104 : checkCert 6 1104 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_1152 : checkCert 6 1152 15 = true := by decide +kernel

private lemma certLayer6 : checkCert 6 0 (certCount 6) = true :=
  (joinCert 6 0 576 591 (joinCert 6 0 288 288 (joinCert 6 0 144 144 (joinCert 6 0 48 96 cert6_0 (joinCert 6 48 48 48 cert6_48 cert6_96)) (joinCert 6 144 48 96 cert6_144 (joinCert 6 192 48 48 cert6_192 cert6_240))) (joinCert 6 288 144 144 (joinCert 6 288 48 96 cert6_288 (joinCert 6 336 48 48 cert6_336 cert6_384)) (joinCert 6 432 48 96 cert6_432 (joinCert 6 480 48 48 cert6_480 cert6_528)))) (joinCert 6 576 288 303 (joinCert 6 576 144 144 (joinCert 6 576 48 96 cert6_576 (joinCert 6 624 48 48 cert6_624 cert6_672)) (joinCert 6 720 48 96 cert6_720 (joinCert 6 768 48 48 cert6_768 cert6_816))) (joinCert 6 864 144 159 (joinCert 6 864 48 96 cert6_864 (joinCert 6 912 48 48 cert6_912 cert6_960)) (joinCert 6 1008 96 63 (joinCert 6 1008 48 48 cert6_1008 cert6_1056) (joinCert 6 1104 48 15 cert6_1104 cert6_1152)))))

set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert7_0 : checkCert 7 0 48 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert7_48 : checkCert 7 48 42 = true := by decide +kernel

private lemma certLayer7 : checkCert 7 0 (certCount 7) = true :=
  (joinCert 7 0 48 42 cert7_0 cert7_48)

set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert8_0 : checkCert 8 0 5 = true := by decide +kernel

private lemma certLayer8 : checkCert 8 0 (certCount 8) = true :=
  cert8_0

private lemma allChecked (k : Nat) (hk : k ≤ 8) (i : Nat) (hi : i < certCount k) :
    runCheck certCount certState certLocate k i = true := by
  have h : checkCert k 0 (certCount k) = true := by
    have hc : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rfl
    · rfl
    · exact certLayer2
    · exact certLayer3
    · exact certLayer4
    · exact certLayer5
    · exact certLayer6
    · exact certLayer7
    · exact certLayer8
  exact checkBatch_at h i (Nat.zero_le i) (by simpa only [Nat.zero_add] using hi)

private lemma noLiveAt (k : Nat) (hk : k ≤ 8) (r : SearchState)
    (h : checkLink certCount certState certLocate k r = true) :
    ∀ m ≤ k, ¬ Live m r.1 r.2.toFinset := by
  intro m hm hl
  simp only [checkLink, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨hi,ht⟩,hw⟩ := h
  have he := sameWires_sound hw
  rw [ht,he] at hl
  exact runCheck_complete allChecked k hk _ hi m hm hl
lemma lowerCore (s : ℕ) (h : HasCircuitSize 5 graph s) : 9 ≤ s := by
  by_contra! small
  obtain ⟨C,hb,hs,he⟩ := h
  obtain ⟨k,t,S,hk,_,_,live,hsub⟩ := extract C.gates raw hb
    (circuit_target raw rfl sampleCorrect C hb he)
  have eq := necessary raw (by decide +kernel) live hsub
  have hSc : S.card = 5 := by rw [←eq]; decide
  have hc := (live_size live).2
  change C.gates.length ≤ s at hs
  have hlt : k ≤ 8 := by omega
  have cnt : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 := by omega
  rcases cnt with rfl | rfl | rfl | rfl | rfl
  · exact noLiveAt 8 (by decide) (0,raw) (by decide +kernel) k hlt (eq.symm ▸ live)
  · exact noLiveAt 8 (by decide) (1,raw) (by decide +kernel) k hlt (eq.symm ▸ live)
  · exact noLiveAt 8 (by decide) (2,raw) (by decide +kernel) k hlt (eq.symm ▸ live)
  · exact noLiveAt 8 (by decide) (3,raw) (by decide +kernel) k hlt (eq.symm ▸ live)
  · exact noLiveAt 8 (by decide) (4,raw) (by decide +kernel) k hlt (eq.symm ▸ live)

def f (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4277075694 * 2 ^ 32 + 4277071592) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

lemma restrictions : ∀ x : Fin 5 → Bool, f (Fin.snoc x false) = graph x := by decide +kernel

lemma depends : ∃ x : Fin 6 → Bool, f (Function.update x (Fin.last 5) (!x (Fin.last 5))) ≠ f x := by
  refine ⟨fun i => (1 : ℕ).testBit i.val, ?_⟩
  decide +kernel

lemma notConstant : ∃ x y : Fin 5 → Bool, f (Fin.snoc x false) ≠ f (Fin.snoc y false) := by
  exact ⟨fun _ => false, fun _ => true, by decide +kernel⟩

lemma lower (s : ℕ) (h : HasCircuitSize 6 f s) : 10 ≤ s := by
  by_contra! small
  obtain ⟨C,hb,hs,he⟩ := h
  have hc : HasCircuitSize 6 f 9 := ⟨C,hb,by omega,he⟩
  have hh := FirstGate.gate_elim 5 f false 8 depends notConstant hc
  have eq : (fun x => f (Fin.snoc x false)) = graph := funext restrictions
  rw [eq] at hh
  have hs := lowerCore 8 hh
  omega

def best : Circuit := ⟨[⟨.or, [4,5]⟩, ⟨.or, [2,6]⟩, ⟨.or, [0,1]⟩, ⟨.and, [2,6]⟩, ⟨.and, [0,1]⟩, ⟨.or, [8,9]⟩, ⟨.and, [3,11]⟩, ⟨.and, [7,8]⟩, ⟨.or, [10,13]⟩, ⟨.or, [12,14]⟩],15⟩
lemma bestMono : Monotone2 best := by simp [best,Monotone2]
lemma bestEval : ∀ x : Fin 6 → Bool, best.eval (List.ofFn x) = f x := by decide +kernel

end PEqualNP.Outside.L_meta_12929

open PEqualNP.Outside.L_meta_12929 in
theorem PEqualNP.Outside.L_meta_12929 :
∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075694 * 2 ^ 32 + 4277071592) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075694 * 2 ^ 32 + 4277071592) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  change ∀ s, PEqualNP.MetaComplexity.HasCircuitSize 6 f s → _
  intro s hs
  exact ⟨best,bestMono,lower s hs,bestEval⟩
