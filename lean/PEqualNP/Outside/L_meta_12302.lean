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

namespace PEqualNP.Outside.L_meta_12302.FirstGate
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

end PEqualNP.Outside.L_meta_12302.FirstGate


/-!
# Supports of wires

Helper for `L-meta-011`. Every wire gets a support: the set of inputs it can depend on, read
off the gates. Two facts: the value of a wire depends only on the inputs in its support, and
any set `W` of wires has a joint support of size at most (number of gates) + `|W|`, because a
gate of fan-in two replaces itself by at most two earlier wires.
-/

namespace PEqualNP.Outside.L_meta_12302.FirstGate
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

end PEqualNP.Outside.L_meta_12302.FirstGate


/-!
# Gate elimination

Helper for `L-meta-014`. The last input of a circuit on `n + 1` inputs is fixed to `b`. One
pass over the gates gives every old wire a status: a constant, or an alias of a wire of the
new circuit on `n` inputs. A gate that reads a constant becomes a constant or an alias and is
not emitted, so if some gate reads the fixed input the new circuit is smaller. If no gate
reads it, the supports of `Support.lean` show the function does not depend on it.
-/

namespace PEqualNP.Outside.L_meta_12302.FirstGate
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

end PEqualNP.Outside.L_meta_12302.FirstGate


/-!
# Parity needs `2 (n - 1)` gates

Helper for `L-meta-020`. The pass of `Elim.lean` fixes the last input of a circuit to a
constant `b`. Here it is shown to save two gates for a suitable `b`, when the function depends
on the last input and both restrictions are non-constant. Either two gates read the fixed
input, or the only gate reading it becomes a constant for a suitable `b` and a later gate
reads that constant, or the output does not depend on the last input. Parity and its
complement satisfy the hypotheses, and their restrictions are again parity or its complement.
-/

namespace PEqualNP.Outside.L_meta_12302.FirstGate
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

end PEqualNP.Outside.L_meta_12302.FirstGate

namespace PEqualNP.Outside.L_meta_12302.FirstGate
open PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds

/-! ## Clean circuits -/

/-- A gate of a clean circuit, where `m` wires exist before it: a NOT of one earlier wire, or
an AND or OR of two earlier wires. -/
def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

/-- A clean list of gates on `m` inputs. -/
def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate), gs[p]? = some g → CleanGate (m + p) g

theorem CleanGate.nok {m : ℕ} {g : Gate} (h : CleanGate m g) : NOk g := by
  rcases h with ⟨h1, j, _, h2⟩ | ⟨h1 | h1, j, k, _, _, h2⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inr rfl)
    · rw [h2]; simp
    · intro _; rw [h2]; simp
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inl rfl
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inl rfl)
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h

theorem CleanGate.lt {m : ℕ} {g : Gate} (h : CleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  intro a ha
  rcases h with ⟨_, j, hj, h2⟩ | ⟨_, j, k, hj, hk, h2⟩
  · rw [h2] at ha
    simp at ha
    subst ha; exact hj
  · rw [h2] at ha
    simp at ha
    rcases ha with rfl | rfl
    · exact hj
    · exact hk

theorem clean_nok (m : ℕ) (gs : List Gate) (h : CleanL m gs) : ∀ g ∈ gs, NOk g := by
  intro g hg
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hg
  exact (h p g hp).nok

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins, s.Valid m) :
    ∀ g ∈ (simplify op m ins).1, CleanGate m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    refine Or.inr ⟨Or.inl rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    refine Or.inr ⟨Or.inr rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    refine Or.inl ⟨rfl, _, ?_, rfl⟩
    exact hv _ List.mem_cons_self
  · simp at hg
  · simp at hg

theorem toList_getElem? {α : Type} (o : Option α) (k : ℕ) (a : α)
    (h : o.toList[k]? = some a) : k = 0 ∧ a ∈ o := by
  cases o with
  | none => simp at h
  | some b =>
    cases k with
    | zero => simp at h; simp [h]
    | succ k => simp at h

/-- The pass emits a clean list of gates. -/
theorem clean_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro w acc _ _ h; exact h
  | cons g gs ih =>
    intro w acc hok hinv hcl
    have hinv' : Inv n y (wiresFrom [g] w) (elimStep n acc g) :=
      inv_elim n y hy [g] w acc (fun g' hg' => hok g' (by simp at hg'; simp [hg'])) hinv
    refine ih _ (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hinv' ?_
    intro p g' hp
    have hp' : (acc.2 ++ (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)[p]? = some g' := hp
    by_cases hlt : p < acc.2.length
    · rw [List.getElem?_append_left hlt] at hp'
      exact hcl p g' hp'
    · rw [List.getElem?_append_right (by omega)] at hp'
      obtain ⟨h0, hmem⟩ := toList_getElem? _ _ _ hp'
      have hpl : p = acc.2.length := by omega
      rw [hpl]
      exact simplify_clean _ _ _ (fun s hs => by
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        exact (hinv.2 a).1) g' hmem

/-- A clean circuit with at most `s` gates computes `f`. -/
def HasClean (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ (gs : List Gate) (o : ℕ), CleanL n gs ∧ gs.length ≤ s ∧
    ∀ x : Fin n → Bool, (wiresFrom gs (List.ofFn x)).getD o false = f x

/-- The statuses at the start when no input is fixed. -/
def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => Stat.wire i)

theorem inv_id (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (idStats n, []) := by
  refine ⟨by simp [idStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idStats, hlt, Stat.Valid, Stat.val, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [idStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

/-- A circuit for a non-constant function can be cleaned without growing. -/
theorem clean_of (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (h : HasCircuitSize n f s) : HasClean n f s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  have hok : ∀ g ∈ C.gates, Ok g := ok
  set acc := elim n C.gates (idStats n, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ hok (inv_id n y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y)) = f y := by
    intro y
    rw [((hinv y).2 C.output).2, ← hev y]; rfl
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    refine ⟨acc.2, j, ?_, ?_, ?_⟩
    · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
        (inv_id n _) (by intro p g hp; simp at hp)
    · have := elim_len n C.gates (idStats n, [])
      rw [← hacc] at this
      simp only [List.length_nil, zero_add] at this
      omega
    · intro y
      have := hval y
      rw [hst] at this
      exact this

/-! ## Fixing input `i` -/

theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp

/-- The statuses at the start when input `i` is fixed to `b`: the other inputs are the new
input wires, in order. -/
def statAt (n : ℕ) (i : Fin (n + 1)) (b : Bool) : List Stat :=
  List.ofFn (Fin.insertNth i (Stat.const b) (fun k : Fin n => Stat.wire k) : Fin (n + 1) → Stat)

theorem statAt_length (n : ℕ) (i : Fin (n + 1)) (b : Bool) : (statAt n i b).length = n + 1 := by
  simp [statAt]

theorem statAt_at (n : ℕ) (i : Fin (n + 1)) (b : Bool) :
    (statAt n i b).getD i (Stat.const false) = Stat.const b := by
  rw [statAt, getD_ofFn, Fin.insertNth_apply_same]

theorem statAt_above (n : ℕ) (i : Fin (n + 1)) (b : Bool) (k : Fin n) :
    (statAt n i b).getD (i.succAbove k) (Stat.const false) = Stat.wire k := by
  rw [statAt, getD_ofFn, Fin.insertNth_apply_succAbove]

theorem inv_at (n : ℕ) (i : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool))
      (statAt n i b, []) := by
  refine ⟨by simp [statAt], ?_⟩
  have key : ∀ j : Fin (n + 1),
      ((statAt n i b).getD j (Stat.const false)).Valid (n + 0) ∧
      ((statAt n i b).getD j (Stat.const false)).val (List.ofFn y)
        = (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool)).getD j false := by
    intro j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
    · rw [statAt_at, getD_ofFn, Fin.insertNth_apply_same]
      exact ⟨trivial, rfl⟩
    · rw [statAt_above, getD_ofFn, Fin.insertNth_apply_succAbove]
      refine ⟨?_, ?_⟩
      · show (k : ℕ) < n + 0
        have := k.isLt
        omega
      · show (List.ofFn y).getD k false = y k
        exact getD_ofFn n y false k
  intro j
  by_cases hlt : j < n + 1
  · exact key ⟨j, hlt⟩
  · show ((statAt n i b).getD j (Stat.const false)).Valid (n + 0) ∧
      ((statAt n i b).getD j (Stat.const false)).val (List.ofFn y)
        = (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool)).getD j false
    rw [List.getD_eq_default _ _ (by rw [statAt_length]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

/-- The final status of old wire `a` when input `i` is fixed to `b`. -/
def stF (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (a : ℕ) : Stat :=
  (elim n gs (statAt n i b, [])).1.getD a (Stat.const false)

theorem stF_self (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) :
    stF n gs i b i = Stat.const b := by
  show (elim n gs (statAt n i b, [])).1.getD i (Stat.const false) = _
  rw [elim_getD n i _ gs _ (by
    show (i : ℕ) < (statAt n i b).length
    rw [statAt_length]; exact i.isLt)]
  exact statAt_at n i b

/-! ## The pass, position by position -/

theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩

theorem elim_split_getD (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a ≤ acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elimStep n (elim n pre acc) g).1.getD a d := by
  rw [elim_append, elim_cons, elim_getD n a d post _ (by
    show a < ((elim n pre acc).1 ++ [_]).length
    rw [List.length_append, elim_fst_len, List.length_singleton]; omega)]

theorem elim_split_getD_lt (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a < acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elim n pre acc).1.getD a d := by
  rw [elim_split_getD n pre g post acc a d (le_of_lt h)]
  show ((elim n pre acc).1 ++ [_]).getD a d = _
  exact getD_snoc_ne _ _ _ _ (by rw [elim_fst_len]; omega)

/-- A gate that reads an earlier wire whose final status is the absorbing constant of the gate
has a constant final status. -/
theorem const_of_read (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) (p : ℕ) (g : Gate)
    (hp : gs[p]? = some g) (hg : NOk g) (a : ℕ) (ha : a ∈ g.inputs)
    (hlt : a < acc.1.length + p)
    (hc : (elim n gs acc).1.getD a (Stat.const false) = Stat.const (fixBit g)) :
    ∃ c, (elim n gs acc).1.getD (acc.1.length + p) (Stat.const false) = Stat.const c := by
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  rw [elim_split_getD_lt n pre g post acc a _ hlt] at hc
  obtain ⟨c, hc'⟩ := elimStep_const n (elim n pre acc) g hg a ha hc
  refine ⟨c, ?_⟩
  rw [elim_split_getD n pre g post acc _ _ (le_refl _)]
  rw [elim_fst_len] at hc'
  exact hc'

/-- Every position of `S` holds a gate that reads an earlier wire of constant final status: the
pass emits at least `|S|` gates fewer than it reads. -/
theorem elim_count (n : ℕ) (acc : List Stat × List Gate) : ∀ gs : List Gate,
    (∀ g ∈ gs, NOk g) → ∀ S : Finset ℕ,
    (∀ p ∈ S, ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, a < acc.1.length + p ∧
        ∃ c, (elim n gs acc).1.getD a (Stat.const false) = Stat.const c) →
      (elim n gs acc).2.length + S.card ≤ acc.2.length + gs.length := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ S hS
    have hE : S = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro p hp
      obtain ⟨g, hg, _⟩ := hS p hp
      simp at hg
    subst hE
    simp [elim]
  | append_singleton gs g ih =>
    intro hok S hS
    have hstep : elim n (gs ++ [g]) acc = elimStep n (elim n gs acc) g := by
      rw [elim_append]; rfl
    have hpre : ∀ (a : ℕ) (d : Stat), a < acc.1.length + gs.length →
        (elim n (gs ++ [g]) acc).1.getD a d = (elim n gs acc).1.getD a d :=
      fun a d h => elim_split_getD_lt n gs g [] acc a d h
    have hok' : ∀ g' ∈ gs, NOk g' := fun g' h => hok g' (List.mem_append_left _ h)
    have ih' := ih hok' (S.erase gs.length) (by
      intro p hp
      obtain ⟨hne, hpS⟩ := Finset.mem_erase.1 hp
      obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS p hpS
      have hpl : p < gs.length := by
        obtain ⟨h1, _⟩ := List.getElem?_eq_some_iff.1 hg'
        rw [List.length_append, List.length_singleton] at h1
        omega
      rw [List.getElem?_append_left hpl] at hg'
      rw [hpre a _ (by omega)] at hc
      exact ⟨g', hg', a, ha, hlt, c, hc⟩)
    rw [hstep, List.length_append, List.length_singleton]
    by_cases hin : gs.length ∈ S
    · obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS _ hin
      have hgg : g' = g := by
        rw [List.getElem?_concat_length] at hg'
        exact (Option.some.inj hg').symm
      subst hgg
      rw [hpre a _ hlt] at hc
      have h2 := elimStep_none n (elim n gs acc) g' (hok g' (by simp)) a ha c hc
      have hcard := Finset.card_erase_of_mem hin
      have hpos : 1 ≤ S.card := Finset.card_pos.2 ⟨_, hin⟩
      omega
    · have h2 : (elimStep n (elim n gs acc) g).2.length ≤ (elim n gs acc).2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + (elim n gs acc).2.length)
          (g.inputs.map fun i => (elim n gs acc).1.getD i (Stat.const false))).1
        omega
      rw [Finset.erase_eq_of_notMem hin] at ih'
      omega

/-! ## Readers -/

/-- `B` is a set of wires containing input `i`. If every gate outside `B` reads no wire of `B`,
no wire outside `B` has `i` in its support. -/
theorem supp_B (m : ℕ) (i : Fin m) (B : ℕ → Prop) (hi : B i) : ∀ gs : List Gate,
    (∀ p g, gs[p]? = some g → ¬ B (m + p) → ∀ a ∈ g.inputs, ¬ B a) →
    ∀ j, ¬ B j → i ∉ (suppsFrom gs (inputSupps m)).getD j ∅ := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ j hj
    show i ∉ (inputSupps m).getD j ∅
    by_cases hlt : j < m
    · rw [inputSupps_getD m j hlt, Finset.mem_singleton]
      intro e
      apply hj
      have e' : (i : ℕ) = j := congrArg Fin.val e
      rw [← e']; exact hi
    · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp
  | append_singleton gs g ih =>
    intro h j hj
    have ih' := ih (fun p g' hp => h p g' (by
      obtain ⟨hpl, _⟩ := List.getElem?_eq_some_iff.1 hp
      rw [List.getElem?_append_left hpl]; exact hp))
    have hs : suppsFrom (gs ++ [g]) (inputSupps m) = suppsFrom gs (inputSupps m)
        ++ [gateSupp (suppsFrom gs (inputSupps m)) g] := by
      rw [suppsFrom_append]; rfl
    have hl : (suppsFrom gs (inputSupps m)).length = m + gs.length := by
      rw [length_suppsFrom]; simp [inputSupps]
    rw [hs]
    by_cases hjl : j = m + gs.length
    · subst hjl
      rw [getD_snoc_len _ _ _ _ hl]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp _ g _).1 hmem
      exact ih' a (h gs.length g List.getElem?_concat_length hj a ha) hia
    · rw [getD_snoc_ne _ _ _ _ (by rw [hl]; exact hjl)]
      exact ih' j hj

/-- If the wire `o` outside `B` has `i` in its support, some gate outside `B` reads a wire of
`B`. -/
theorem exists_reader (m : ℕ) (i : Fin m) (B : ℕ → Prop) (hi : B i) (gs : List Gate) (o : ℕ)
    (ho : ¬ B o) (hdep : i ∈ (suppsFrom gs (inputSupps m)).getD o ∅) :
    ∃ p g, gs[p]? = some g ∧ ¬ B (m + p) ∧ ∃ a ∈ g.inputs, B a := by
  by_contra hno
  exact supp_B m i B hi gs
    (fun p g hp hB a ha hBa => hno ⟨p, g, hp, hB, a, ha, hBa⟩) o ho hdep

/-- If no gate reads wire `k`, two wire lists that agree off `k` still agree off `k`. -/
theorem agree_except (k : ℕ) (gs : List Gate) : ∀ w w' : List Bool,
    (∀ g ∈ gs, k ∉ g.inputs) → w.length = w'.length →
    (∀ j, j ≠ k → w.getD j false = w'.getD j false) →
    ∀ j, j ≠ k → (wiresFrom gs w).getD j false = (wiresFrom gs w').getD j false := by
  induction gs with
  | nil => intro w w' _ _ h; exact h
  | cons g gs ih =>
    intro w w' hno hl h
    have hno' := hno g List.mem_cons_self
    have e : (g.inputs.map fun i => w.getD i false) = g.inputs.map fun i => w'.getD i false :=
      List.map_congr_left (fun a ha => h a (fun e => hno' (e ▸ ha)))
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
      (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')) (by simp [hl])
    intro j hj
    by_cases hjl : j = w.length
    · rw [hjl, getD_snoc_eq, hl, getD_snoc_eq, e]
    · rw [getD_snoc_ne _ _ _ _ hjl, getD_snoc_ne _ _ _ _ (by omega)]
      exact h j hj

/-! ## Three gates saved -/

/-- Position `p` holds a gate that reads a wire of constant final status. -/
def RC (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (p : ℕ) : Prop :=
  ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, ∃ c, stF n gs i b a = Stat.const c

theorem three_count (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p1 p2 p3 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) :
    (elim n gs (statAt n i b, [])).2.length + 3 ≤ gs.length := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have hcount := elim_count n (statAt n i b, []) gs (clean_nok _ gs hcl) {p1, p2, p3} (by
    intro p hp
    have hR : RC n gs i b p := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl <;> assumption
    obtain ⟨g, hg, a, ha, c, hc⟩ := hR
    refine ⟨g, hg, a, ha, ?_, c, hc⟩
    rw [hL]
    exact (hcl p g hg).lt a ha)
  have hcard : ({p1, p2, p3} : Finset ℕ).card = 3 :=
    Finset.card_eq_three.2 ⟨p1, p2, p3, h12, h13, h23, rfl⟩
  rw [hcard] at hcount
  simpa using hcount

/-- The core of the count. `g0` is the first gate and reads input `i`. Either the status of
`g0` can be made any constant, or another gate reads input `i`. -/
theorem three_core (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (o : ℕ)
    (hsupp : ∀ i : Fin (n + 1), i ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅)
    (hout : ∀ (i : Fin (n + 1)) (b c : Bool), stF n gs i b o ≠ Stat.const c)
    (g0 : Gate) (h0 : gs[0]? = some g0) (i : Fin (n + 1)) (hi0 : (i : ℕ) ∈ g0.inputs)
    (halt : (∀ c, ∃ b, stF n gs i b (n + 1) = Stat.const c) ∨
      ∃ p' g', p' ≠ 0 ∧ gs[p']? = some g' ∧ (i : ℕ) ∈ g'.inputs) :
    ∃ b, (elim n gs (statAt n i b, [])).2.length + 3 ≤ gs.length := by
  have hnok := clean_nok _ gs hcl
  have hxi : ∀ b, stF n gs i b i = Stat.const b := stF_self n gs i
  have hrd : ∀ (b : Bool) (p : ℕ) (g : Gate) (a : ℕ), gs[p]? = some g → a ∈ g.inputs →
      stF n gs i b a = Stat.const (fixBit g) → ∃ c, stF n gs i b (n + 1 + p) = Stat.const c := by
    intro b p g a hp ha hc
    have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
    have := const_of_read n gs (statAt n i b, []) p g hp (hnok g (List.mem_of_getElem? hp)) a ha
      (by rw [hL]; exact (hcl p g hp).lt a ha) hc
    rw [hL] at this
    exact this
  have hg0c : ∃ c0, stF n gs i (fixBit g0) (n + 1) = Stat.const c0 :=
    hrd (fixBit g0) 0 g0 i h0 hi0 (hxi _)
  have hox : o ≠ i := fun e => hout i false false (by rw [e]; exact hxi false)
  have ho0 : o ≠ n + 1 := by
    intro e
    obtain ⟨c0, h⟩ := hg0c
    exact hout i (fixBit g0) c0 (by rw [e]; exact h)
  have R0 : ∀ b, RC n gs i b 0 := fun b => ⟨g0, h0, i, hi0, b, hxi b⟩
  obtain ⟨p, g2, hp, hBp, a, ha, hBa⟩ := exists_reader (n + 1) i
    (fun a => a = i ∨ a = n + 1) (Or.inl rfl) gs o
    (fun h => h.elim hox ho0) (hsupp i)
  have hp0 : p ≠ 0 := fun e => hBp (Or.inr (by omega))
  have ha2 : ∃ c, stF n gs i (fixBit g0) a = Stat.const c := by
    rcases hBa with h | h
    · exact ⟨fixBit g0, by rw [h]; exact hxi _⟩
    · rw [h]; exact hg0c
  -- the third gate, once `g2` has a constant status under some `b`
  have third : ∀ (b c2 : Bool), stF n gs i b (n + 1 + p) = Stat.const c2 →
      ∃ p3 g3, gs[p3]? = some g3 ∧ p3 ≠ 0 ∧ p3 ≠ p ∧
        ∃ a3 ∈ g3.inputs, a3 = (i : ℕ) ∨ a3 = n + 1 ∨ a3 = n + 1 + p := by
    intro b c2 hc2
    obtain ⟨p3, g3, hp3, hB3, a3, ha3, hBa3⟩ := exists_reader (n + 1) i
      (fun a => a = i ∨ a = n + 1 ∨ a = n + 1 + p) (Or.inl rfl) gs o
      (fun h => by
        rcases h with h | h | h
        · exact hox h
        · exact ho0 h
        · exact hout i b c2 (by rw [h]; exact hc2)) (hsupp i)
    exact ⟨p3, g3, hp3, fun e => hB3 (Or.inr (Or.inl (by omega))),
      fun e => hB3 (Or.inr (Or.inr (by omega))), a3, ha3, hBa3⟩
  by_cases hc2 : ∃ c, stF n gs i (fixBit g0) (n + 1 + p) = Stat.const c
  · obtain ⟨c2, hc2⟩ := hc2
    obtain ⟨p3, g3, hp3, h30, h3p, a3, ha3, hBa3⟩ := third (fixBit g0) c2 hc2
    refine ⟨fixBit g0, three_count n gs hcl i (fixBit g0) 0 p p3 (Ne.symm hp0) (Ne.symm h30)
      (Ne.symm h3p) (R0 _) ⟨g2, hp, a, ha, ha2⟩ ⟨g3, hp3, a3, ha3, ?_⟩⟩
    rcases hBa3 with h | h | h
    · exact ⟨fixBit g0, by rw [h]; exact hxi _⟩
    · rw [h]; exact hg0c
    · exact ⟨c2, by rw [h]; exact hc2⟩
  · by_cases hx : (i : ℕ) ∈ g2.inputs
    · obtain ⟨c2, hc2'⟩ := hrd (fixBit g2) p g2 i hp hx (hxi _)
      obtain ⟨p3, g3, hp3, h30, h3p, a3, ha3, hBa3⟩ := third (fixBit g2) c2 hc2'
      rcases hBa3 with h | h | h
      · exact ⟨fixBit g2, three_count n gs hcl i (fixBit g2) 0 p p3 (Ne.symm hp0) (Ne.symm h30)
          (Ne.symm h3p) (R0 _) ⟨g2, hp, i, hx, _, hxi _⟩
          ⟨g3, hp3, a3, ha3, fixBit g2, by rw [h]; exact hxi _⟩⟩
      · exact ⟨fixBit g0, three_count n gs hcl i (fixBit g0) 0 p p3 (Ne.symm hp0) (Ne.symm h30)
          (Ne.symm h3p) (R0 _) ⟨g2, hp, a, ha, ha2⟩
          ⟨g3, hp3, a3, ha3, by rw [h]; exact hg0c⟩⟩
      · exact ⟨fixBit g2, three_count n gs hcl i (fixBit g2) 0 p p3 (Ne.symm hp0) (Ne.symm h30)
          (Ne.symm h3p) (R0 _) ⟨g2, hp, i, hx, _, hxi _⟩
          ⟨g3, hp3, a3, ha3, c2, by rw [h]; exact hc2'⟩⟩
    · have ha' : a = n + 1 := by
        rcases hBa with h | h
        · exact absurd (h ▸ ha) hx
        · exact h
      rw [ha'] at ha
      rcases halt with hG | ⟨p', g', hp'0, hp', hx'⟩
      · obtain ⟨b, hb⟩ := hG (fixBit g2)
        obtain ⟨c2, hc2'⟩ := hrd b p g2 (n + 1) hp ha hb
        obtain ⟨p3, g3, hp3, h30, h3p, a3, ha3, hBa3⟩ := third b c2 hc2'
        refine ⟨b, three_count n gs hcl i b 0 p p3 (Ne.symm hp0) (Ne.symm h30)
          (Ne.symm h3p) (R0 _) ⟨g2, hp, n + 1, ha, _, hb⟩ ⟨g3, hp3, a3, ha3, ?_⟩⟩
        rcases hBa3 with h | h | h
        · exact ⟨b, by rw [h]; exact hxi _⟩
        · exact ⟨fixBit g2, by rw [h]; exact hb⟩
        · exact ⟨c2, by rw [h]; exact hc2'⟩
      · have hpp : p ≠ p' := by
          intro e
          rw [← e, hp] at hp'
          exact hx (Option.some.inj hp' ▸ hx')
        exact ⟨fixBit g0, three_count n gs hcl i (fixBit g0) 0 p p' (Ne.symm hp0)
          (Ne.symm hp'0) hpp (R0 _) ⟨g2, hp, n + 1, ha, hg0c⟩
          ⟨g', hp', i, hx', _, hxi _⟩⟩

/-- The final status of the first gate. -/
theorem stat_first (n : ℕ) (gs : List Gate) (g0 : Gate) (h0 : gs[0]? = some g0)
    (i : Fin (n + 1)) (b : Bool) :
    stF n gs i b (n + 1) = (simplify g0.op n
      (g0.inputs.map fun a => (statAt n i b).getD a (Stat.const false))).2 := by
  obtain ⟨pre, post, rfl, hpre⟩ := split_at gs 0 g0 h0
  have hnil : pre = [] := List.eq_nil_of_length_eq_zero hpre
  subst hnil
  show (elim n ([] ++ g0 :: post) (statAt n i b, [])).1.getD (n + 1) (Stat.const false) = _
  rw [elim_split_getD n [] g0 post _ (n + 1) _ (by
    show n + 1 ≤ (statAt n i b).length + 0
    rw [statAt_length])]
  exact getD_snoc_len (statAt n i b) _ _ _ (statAt_length n i b)

/-- A first gate that reads only input `i` can be given either constant status. -/
theorem first_any (n : ℕ) (gs : List Gate) (g0 : Gate) (h0 : gs[0]? = some g0)
    (i : Fin (n + 1))
    (hshape : (g0.op = GateOp.not ∧ g0.inputs = [(i : ℕ)]) ∨
      ((g0.op = GateOp.and ∨ g0.op = GateOp.or) ∧ g0.inputs = [(i : ℕ), (i : ℕ)])) :
    ∀ c, ∃ b, stF n gs i b (n + 1) = Stat.const c := by
  intro c
  rcases hshape with ⟨hop, hin⟩ | ⟨hop | hop, hin⟩
  · refine ⟨!c, ?_⟩
    rw [stat_first n gs g0 h0, hop, hin]
    simp only [List.map_cons, List.map_nil, statAt_at]
    simp [simplify, simpNot]
  · refine ⟨c, ?_⟩
    rw [stat_first n gs g0 h0, hop, hin]
    simp only [List.map_cons, List.map_nil, statAt_at]
    simp [simplify, simpAnd]
  · refine ⟨c, ?_⟩
    rw [stat_first n gs g0 h0, hop, hin]
    simp only [List.map_cons, List.map_nil, statAt_at]
    simp [simplify, simpOr]

/-- The first gate is an AND or OR of the inputs `i` and `k`, and no other gate reads input
`i`: then the output does not depend on input `i` once input `k` is the absorbing constant. -/
theorem single_reader (n : ℕ) (gs : List Gate) (o : ℕ) (g0 : Gate) (h0 : gs[0]? = some g0)
    (i k : Fin (n + 1)) (hik : k ≠ i) (hop : g0.op = GateOp.and ∨ g0.op = GateOp.or)
    (hin : g0.inputs = [(i : ℕ), (k : ℕ)]) (hoi : o ≠ i)
    (hno : ∀ p' g', gs[p']? = some g' → p' ≠ 0 → (i : ℕ) ∉ g'.inputs)
    (hdep : ∀ u : Fin (n + 1) → Bool,
      (wiresFrom gs (List.ofFn (Function.update u i (!u i)))).getD o false
        ≠ (wiresFrom gs (List.ofFn u)).getD o false) : False := by
  obtain ⟨pre, post, rfl, hpre⟩ := split_at gs 0 g0 h0
  have hnil : pre = [] := List.eq_nil_of_length_eq_zero hpre
  subst hnil
  have hno' : ∀ g ∈ post, (i : ℕ) ∉ g.inputs := by
    intro g hg
    obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg
    exact hno (q + 1) g (by simpa using hq) (by omega)
  let u : Fin (n + 1) → Bool := fun j => if j = k then fixBit g0 else false
  have huk : u k = fixBit g0 := by simp [u]
  have hu'k : Function.update u i (!u i) k = fixBit g0 := by
    rw [Function.update_of_ne hik]; exact huk
  apply hdep u
  show (wiresFrom post (List.ofFn (Function.update u i (!u i)) ++
      [g0.op.eval (g0.inputs.map fun a => (List.ofFn (Function.update u i (!u i))).getD a false)])).getD
        o false
    = (wiresFrom post (List.ofFn u ++
      [g0.op.eval (g0.inputs.map fun a => (List.ofFn u).getD a false)])).getD o false
  apply agree_except i post _ _ hno' (by simp) ?_ o hoi
  intro j hj
  by_cases hjl : j = n + 1
  · rw [hjl, getD_snoc_len _ _ _ _ (by simp), getD_snoc_len _ _ _ _ (by simp), hin]
    simp only [List.map_cons, List.map_nil, getD_ofFn, huk, hu'k]
    rcases hop with hop | hop
    · have hf : fixBit g0 = false := by simp [fixBit, hop]
      rw [hop, hf]; simp [GateOp.eval]
    · have hf : fixBit g0 = true := by simp [fixBit, hop]
      rw [hop, hf]; simp [GateOp.eval]
  · rw [getD_snoc_ne _ _ _ _ (by simpa using hjl), getD_snoc_ne _ _ _ _ (by simpa using hjl)]
    by_cases hlt : j < n + 1
    · have e1 : (List.ofFn (Function.update u i (!u i))).getD j false
          = Function.update u i (!u i) ⟨j, hlt⟩ := getD_ofFn (n + 1) _ false ⟨j, hlt⟩
      have e2 : (List.ofFn u).getD j false = u ⟨j, hlt⟩ := getD_ofFn (n + 1) _ false ⟨j, hlt⟩
      rw [e1, e2]
      exact Function.update_of_ne (fun e => hj (congrArg Fin.val e)) _ _
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

/-- In a clean circuit whose output flips with every input and is never a constant after one
input is fixed, some input and some value of it make the pass emit three gates fewer. -/
theorem three_saved (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (o : ℕ)
    (hdep : ∀ (i : Fin (n + 1)) (u : Fin (n + 1) → Bool),
      (wiresFrom gs (List.ofFn (Function.update u i (!u i)))).getD o false
        ≠ (wiresFrom gs (List.ofFn u)).getD o false)
    (hout : ∀ (i : Fin (n + 1)) (b c : Bool), stF n gs i b o ≠ Stat.const c) :
    ∃ (i : Fin (n + 1)) (b : Bool),
      (elim n gs (statAt n i b, [])).2.length + 3 ≤ gs.length := by
  have hsupp : ∀ i : Fin (n + 1), i ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅ := by
    intro i
    by_contra hns
    refine hdep i (fun _ => false) ?_
    exact (agree_wiresFrom (Function.update (fun _ => false) i (!false)) (fun _ => false) gs _ _ _
      (agree_inputs _ _)).2.2 o (by
        intro k hk
        have : k ≠ i := fun e => hns (e ▸ hk)
        simp [Function.update_of_ne this])
  have hoi : ∀ i : Fin (n + 1), o ≠ i :=
    fun i e => hout i false false (by rw [e]; exact stF_self n gs i false)
  have hg0 : ∃ g0, gs[0]? = some g0 := by
    cases gs with
    | nil =>
      exfalso
      obtain ⟨p, g, hp, _⟩ := exists_reader (n + 1) 0 (fun a => a = ((0 : Fin (n + 1)) : ℕ)) rfl
        [] o (hoi 0) (hsupp 0)
      simp at hp
    | cons g _ => exact ⟨g, rfl⟩
  obtain ⟨g0, h0⟩ := hg0
  rcases hcl 0 g0 h0 with ⟨hop, j, hj, hin⟩ | ⟨hop, j, k, hj, hk, hin⟩
  · obtain ⟨b, hb⟩ := three_core n gs hcl o hsupp hout g0 h0 ⟨j, hj⟩
      (by rw [hin]; exact List.mem_cons_self)
      (Or.inl (first_any n gs g0 h0 ⟨j, hj⟩ (Or.inl ⟨hop, hin⟩)))
    exact ⟨⟨j, hj⟩, b, hb⟩
  · by_cases hjk : j = k
    · subst hjk
      obtain ⟨b, hb⟩ := three_core n gs hcl o hsupp hout g0 h0 ⟨j, hj⟩
        (by rw [hin]; exact List.mem_cons_self)
        (Or.inl (first_any n gs g0 h0 ⟨j, hj⟩ (Or.inr ⟨hop, hin⟩)))
      exact ⟨⟨j, hj⟩, b, hb⟩
    · by_cases hr : ∃ p' g', p' ≠ 0 ∧ gs[p']? = some g' ∧ j ∈ g'.inputs
      · obtain ⟨b, hb⟩ := three_core n gs hcl o hsupp hout g0 h0 ⟨j, hj⟩
          (by rw [hin]; exact List.mem_cons_self) (Or.inr hr)
        exact ⟨⟨j, hj⟩, b, hb⟩
      · exfalso
        exact single_reader n gs o g0 h0 ⟨j, hj⟩ ⟨k, hk⟩
          (fun e => hjk (congrArg Fin.val e).symm) hop hin (hoi ⟨j, hj⟩)
          (fun p' g' hp' hp0 hx => hr ⟨p', g', hp0, hp', hx⟩) (hdep ⟨j, hj⟩)


theorem three_core_at (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (o : ℕ)
    (hsupp : ∀ i : Fin (n + 1), i ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅)
    (hout : ∀ (i : Fin (n + 1)) (b c : Bool), stF n gs i b o ≠ Stat.const c)
    (p0 : ℕ) (g0 : Gate) (h0 : gs[p0]? = some g0) (i : Fin (n + 1)) (hi0 : (i : ℕ) ∈ g0.inputs)
    (halt : (∀ c, ∃ b, stF n gs i b (n + 1 + p0) = Stat.const c) ∨
      ∃ p' g', p' ≠ p0 ∧ gs[p']? = some g' ∧ (i : ℕ) ∈ g'.inputs) :
    ∃ b, (elim n gs (statAt n i b, [])).2.length + 3 ≤ gs.length := by
  have hnok := clean_nok _ gs hcl
  have hxi : ∀ b, stF n gs i b i = Stat.const b := stF_self n gs i
  have hrd : ∀ (b : Bool) (p : ℕ) (g : Gate) (a : ℕ), gs[p]? = some g → a ∈ g.inputs →
      stF n gs i b a = Stat.const (fixBit g) → ∃ c, stF n gs i b (n + 1 + p) = Stat.const c := by
    intro b p g a hp ha hc
    have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
    have := const_of_read n gs (statAt n i b, []) p g hp (hnok g (List.mem_of_getElem? hp)) a ha
      (by rw [hL]; exact (hcl p g hp).lt a ha) hc
    rw [hL] at this
    exact this
  have hg0c : ∃ c0, stF n gs i (fixBit g0) (n + 1 + p0) = Stat.const c0 :=
    hrd (fixBit g0) p0 g0 i h0 hi0 (hxi _)
  have hox : o ≠ i := fun e => hout i false false (by rw [e]; exact hxi false)
  have ho0 : o ≠ n + 1 + p0 := by
    intro e
    obtain ⟨c0, h⟩ := hg0c
    exact hout i (fixBit g0) c0 (by rw [e]; exact h)
  have R0 : ∀ b, RC n gs i b p0 := fun b => ⟨g0, h0, i, hi0, b, hxi b⟩
  obtain ⟨p, g2, hp, hBp, a, ha, hBa⟩ := exists_reader (n + 1) i
    (fun a => a = i ∨ a = n + 1 + p0) (Or.inl rfl) gs o
    (fun h => h.elim hox ho0) (hsupp i)
  have hp0 : p ≠ p0 := fun e => hBp (Or.inr (by omega))
  have ha2 : ∃ c, stF n gs i (fixBit g0) a = Stat.const c := by
    rcases hBa with h | h
    · exact ⟨fixBit g0, by rw [h]; exact hxi _⟩
    · rw [h]; exact hg0c
  -- the third gate, once `g2` has a constant status under some `b`
  have third : ∀ (b c2 : Bool), stF n gs i b (n + 1 + p) = Stat.const c2 →
      ∃ p3 g3, gs[p3]? = some g3 ∧ p3 ≠ p0 ∧ p3 ≠ p ∧
        ∃ a3 ∈ g3.inputs, a3 = (i : ℕ) ∨ a3 = n + 1 + p0 ∨ a3 = n + 1 + p := by
    intro b c2 hc2
    obtain ⟨p3, g3, hp3, hB3, a3, ha3, hBa3⟩ := exists_reader (n + 1) i
      (fun a => a = i ∨ a = n + 1 + p0 ∨ a = n + 1 + p) (Or.inl rfl) gs o
      (fun h => by
        rcases h with h | h | h
        · exact hox h
        · exact ho0 h
        · exact hout i b c2 (by rw [h]; exact hc2)) (hsupp i)
    exact ⟨p3, g3, hp3, fun e => hB3 (Or.inr (Or.inl (by omega))),
      fun e => hB3 (Or.inr (Or.inr (by omega))), a3, ha3, hBa3⟩
  by_cases hc2 : ∃ c, stF n gs i (fixBit g0) (n + 1 + p) = Stat.const c
  · obtain ⟨c2, hc2⟩ := hc2
    obtain ⟨p3, g3, hp3, h30, h3p, a3, ha3, hBa3⟩ := third (fixBit g0) c2 hc2
    refine ⟨fixBit g0, three_count n gs hcl i (fixBit g0) p0 p p3 (Ne.symm hp0) (Ne.symm h30)
      (Ne.symm h3p) (R0 _) ⟨g2, hp, a, ha, ha2⟩ ⟨g3, hp3, a3, ha3, ?_⟩⟩
    rcases hBa3 with h | h | h
    · exact ⟨fixBit g0, by rw [h]; exact hxi _⟩
    · rw [h]; exact hg0c
    · exact ⟨c2, by rw [h]; exact hc2⟩
  · by_cases hx : (i : ℕ) ∈ g2.inputs
    · obtain ⟨c2, hc2'⟩ := hrd (fixBit g2) p g2 i hp hx (hxi _)
      obtain ⟨p3, g3, hp3, h30, h3p, a3, ha3, hBa3⟩ := third (fixBit g2) c2 hc2'
      rcases hBa3 with h | h | h
      · exact ⟨fixBit g2, three_count n gs hcl i (fixBit g2) p0 p p3 (Ne.symm hp0) (Ne.symm h30)
          (Ne.symm h3p) (R0 _) ⟨g2, hp, i, hx, _, hxi _⟩
          ⟨g3, hp3, a3, ha3, fixBit g2, by rw [h]; exact hxi _⟩⟩
      · exact ⟨fixBit g0, three_count n gs hcl i (fixBit g0) p0 p p3 (Ne.symm hp0) (Ne.symm h30)
          (Ne.symm h3p) (R0 _) ⟨g2, hp, a, ha, ha2⟩
          ⟨g3, hp3, a3, ha3, by rw [h]; exact hg0c⟩⟩
      · exact ⟨fixBit g2, three_count n gs hcl i (fixBit g2) p0 p p3 (Ne.symm hp0) (Ne.symm h30)
          (Ne.symm h3p) (R0 _) ⟨g2, hp, i, hx, _, hxi _⟩
          ⟨g3, hp3, a3, ha3, c2, by rw [h]; exact hc2'⟩⟩
    · have ha' : a = n + 1 + p0 := by
        rcases hBa with h | h
        · exact absurd (h ▸ ha) hx
        · exact h
      rw [ha'] at ha
      rcases halt with hG | ⟨p', g', hp'0, hp', hx'⟩
      · obtain ⟨b, hb⟩ := hG (fixBit g2)
        obtain ⟨c2, hc2'⟩ := hrd b p g2 (n + 1 + p0) hp ha hb
        obtain ⟨p3, g3, hp3, h30, h3p, a3, ha3, hBa3⟩ := third b c2 hc2'
        refine ⟨b, three_count n gs hcl i b p0 p p3 (Ne.symm hp0) (Ne.symm h30)
          (Ne.symm h3p) (R0 _) ⟨g2, hp, n + 1 + p0, ha, _, hb⟩ ⟨g3, hp3, a3, ha3, ?_⟩⟩
        rcases hBa3 with h | h | h
        · exact ⟨b, by rw [h]; exact hxi _⟩
        · exact ⟨fixBit g2, by rw [h]; exact hb⟩
        · exact ⟨c2, by rw [h]; exact hc2'⟩
      · have hpp : p ≠ p' := by
          intro e
          rw [← e, hp] at hp'
          exact hx (Option.some.inj hp' ▸ hx')
        exact ⟨fixBit g0, three_count n gs hcl i (fixBit g0) p0 p p' (Ne.symm hp0)
          (Ne.symm hp'0) hpp (R0 _) ⟨g2, hp, n + 1 + p0, ha, hg0c⟩
          ⟨g', hp', i, hx', _, hxi _⟩⟩


end PEqualNP.Outside.L_meta_12302.FirstGate

namespace PEqualNP.Outside.L_meta_12302.FirstGate
open PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds

/-! ## Values of wires -/

/-- The value of wire `j` of the gate list `gs` on the input `u`. -/
def vl {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) : Bool :=
  (wiresFrom gs (List.ofFn u)).getD j false

theorem vl_input {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) (h : j < k) :
    vl gs u j = u ⟨j, h⟩ := by
  unfold vl
  rw [getD_wiresFrom gs _ j (by simpa using h)]
  exact getD_ofFn k u false ⟨j, h⟩

theorem vl_gate {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) :
    vl gs u (k + p) = g.op.eval (g.inputs.map (vl gs u)) := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hwl : (wiresFrom pre (List.ofFn u)).length = k + pre.length := by
    rw [length_wiresFrom]; simp
  have e : wiresFrom (pre ++ g :: post) (List.ofFn u)
      = wiresFrom post (wiresFrom pre (List.ofFn u) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have full : ∀ j, j < k + pre.length →
      (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false
        = (wiresFrom pre (List.ofFn u)).getD j false := by
    intro j hj
    rw [e, getD_wiresFrom _ _ j (by simp [hwl]; omega), getD_snoc_ne _ _ _ _ (by omega)]
  have top : (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
      = g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false) := by
    rw [e, getD_wiresFrom _ _ _ (by simp [hwl]), getD_snoc_len _ _ _ _ hwl]
  show (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
    = g.op.eval (g.inputs.map fun j => (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false)
  rw [top]
  congr 1
  apply List.map_congr_left
  intro a ha
  exact (full a (hlt a ha)).symm

theorem vl_congr {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) (h : ∀ a ∈ g.inputs, vl gs u a = vl gs u' a) :
    vl gs u (k + p) = vl gs u' (k + p) := by
  rw [vl_gate gs hcl u p g hp, vl_gate gs hcl u' p g hp]
  congr 1
  exact List.map_congr_left h

/-- An AND or OR gate with an input at its absorbing value has that value. -/
theorem vl_abs {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (p : ℕ) (g : Gate)
    (hp : gs[p]? = some g) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (w : ℕ)
    (hw : w ∈ g.inputs) (hv : vl gs u w = fixBit g) : vl gs u (k + p) = fixBit g := by
  rw [vl_gate gs hcl u p g hp]
  rcases hop with h | h
  · have hf : fixBit g = false := by simp [fixBit, h]
    rw [hf] at hv ⊢
    rw [h]
    show (g.inputs.map (vl gs u)).all id = false
    rw [List.all_eq_false]
    exact ⟨vl gs u w, List.mem_map.2 ⟨w, hw, rfl⟩, by simp [hv]⟩
  · have hf : fixBit g = true := by simp [fixBit, h]
    rw [hf] at hv ⊢
    rw [h]
    show (g.inputs.map (vl gs u)).any id = true
    rw [List.any_eq_true]
    exact ⟨vl gs u w, List.mem_map.2 ⟨w, hw, rfl⟩, by simp [hv]⟩

/-- Two inputs that agree outside the wire set `B` give wires that agree outside `B`, below the
bound `L`, as soon as every gate outside `B` that reads `B` agrees whenever the earlier wires
outside `B` do. -/
theorem agree_B {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool)
    (B : ℕ → Prop) (L : ℕ) (hin : ∀ j, j < k → ¬ B j → vl gs u j = vl gs u' j)
    (hstep : ∀ p g, gs[p]? = some g → k + p < L → ¬ B (k + p) → (∃ a ∈ g.inputs, B a) →
      (∀ j, j < k + p → ¬ B j → vl gs u j = vl gs u' j) → vl gs u (k + p) = vl gs u' (k + p)) :
    ∀ j, j < L → ¬ B j → vl gs u j = vl gs u' j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjL hB
    by_cases hjk : j < k
    · exact hin j hjk hB
    · obtain ⟨p, rfl⟩ : ∃ p, j = k + p := ⟨j - k, by omega⟩
      cases hp : gs[p]? with
      | none =>
        have hlen : gs.length ≤ p := List.getElem?_eq_none_iff.1 hp
        have h1 : ∀ v : Fin k → Bool, vl gs v (k + p) = false := by
          intro v
          unfold vl
          exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)
        rw [h1, h1]
      | some g =>
        by_cases hr : ∃ a ∈ g.inputs, B a
        · exact hstep p g hp hjL hB hr (fun j' hj' hB' => ih j' hj' (by omega) hB')
        · exact vl_congr gs hcl u u' p g hp (fun a ha =>
            ih a ((hcl p g hp).lt a ha) (by have := (hcl p g hp).lt a ha; omega)
              (fun hBa => hr ⟨a, ha, hBa⟩))

/-- A wire that is not a constant function takes both values. -/
theorem takes {k : ℕ} (gs : List Gate)
    (hM1 : ∀ p g, gs[p]? = some g → ∀ c, ¬ ∀ u : Fin k → Bool, vl gs u (k + p) = c)
    (w : ℕ) (hw : w < k + gs.length) (c : Bool) : ∃ u : Fin k → Bool, vl gs u w = c := by
  by_cases hwk : w < k
  · exact ⟨fun _ => c, by rw [vl_input gs _ w hwk]⟩
  · obtain ⟨p, rfl⟩ : ∃ p, w = k + p := ⟨w - k, by omega⟩
    have hpl : p < gs.length := by omega
    by_contra hno
    apply hM1 p gs[p] (List.getElem?_eq_getElem hpl) (!c)
    intro u
    have h := fun h => hno ⟨u, h⟩
    revert h
    cases vl gs u (k + p) <;> cases c <;> simp

theorem gate_eq {gs : List Gate} {p q : ℕ} {g g' : Gate} (h : gs[p]? = some g)
    (h' : gs[q]? = some g') (e : p = q) : g = g' := by
  subst e
  rw [h] at h'
  exact Option.some.inj h'

theorem two_inputs {m : ℕ} {g : Gate} (hg : CleanGate m g) (a b w : ℕ) (ha : a ∈ g.inputs)
    (hb : b ∈ g.inputs) (hab : a ≠ b) (hw : w ∈ g.inputs) : w = a ∨ w = b := by
  rcases hg with ⟨_, j, _, hin⟩ | ⟨_, j, k, _, _, hin⟩ <;> rw [hin] at ha hb hw <;>
    simp at ha hb hw <;> omega

/-! ## Dropping a gate -/

theorem drop_core (k : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (hcl : CleanL k (pre ++ g :: post)) (o : ℕ) (S : Stat)
    (hS : ∀ y : Fin k → Bool, S.Valid (k + (elim k pre (idStats k, [])).2.length) ∧
      S.val (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y))
        = vl (pre ++ g :: post) y (k + pre.length))
    (hnc : ∃ y y' : Fin k → Bool, vl (pre ++ g :: post) y o ≠ vl (pre ++ g :: post) y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ (pre ++ g :: post).length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl (pre ++ g :: post) y o := by
  have hok : ∀ g' ∈ pre ++ g :: post, Ok g' := fun g' hg' => (clean_nok _ _ hcl g' hg').1
  have hokpre : ∀ g' ∈ pre, Ok g' := fun g' h => hok g' (List.mem_append_left _ h)
  have hokpost : ∀ g' ∈ post, Ok g' :=
    fun g' h => hok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have inv1 : ∀ y : Fin k → Bool, Inv k (List.ofFn y) (wiresFrom pre (List.ofFn y))
      (elim k pre (idStats k, [])) :=
    fun y => inv_elim k _ (by simp) pre _ _ hokpre (inv_id k y)
  have hwl : ∀ y : Fin k → Bool, (wiresFrom pre (List.ofFn y)).length = k + pre.length := by
    intro y; rw [length_wiresFrom]; simp
  have hfull : ∀ y : Fin k → Bool, wiresFrom (pre ++ g :: post) (List.ofFn y)
      = wiresFrom post (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)]) := by
    intro y; rw [wiresFrom_append]; rfl
  have hgv : ∀ y : Fin k → Bool, vl (pre ++ g :: post) y (k + pre.length)
      = g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false) := by
    intro y
    show (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD (k + pre.length) false = _
    rw [hfull, getD_wiresFrom _ _ _ (by simp [hwl y]), getD_snoc_len _ _ _ _ (hwl y)]
  have inv2 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)])
      ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2) := by
    intro y
    obtain ⟨hl, hi⟩ := inv1 y
    refine ⟨by simp [hl], ?_⟩
    intro a
    show (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Stat.const false)).Valid
        (k + (elim k pre (idStats k, [])).2.length) ∧
      (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Stat.const false)).val
        (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y)) = _
    by_cases hal : a = (elim k pre (idStats k, [])).1.length
    · rw [hal, getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨(hS y).1, by rw [(hS y).2, hgv]⟩
    · rw [getD_snoc_ne _ _ _ _ hal, getD_snoc_ne _ _ _ _ (by omega)]
      exact hi a
  have inv3 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom (pre ++ g :: post) (List.ofFn y))
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)) := by
    intro y
    rw [hfull]
    exact inv_elim k _ (by simp) post _ _ hokpost (inv2 y)
  have hc1 : CleanL k (elim k pre (idStats k, [])).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) pre _ _ hokpre (inv_id k _)
      (by intro p g' hp; simp at hp)
  have hc3 : CleanL k
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) post _ _ hokpost (inv2 _) hc1
  have hlen : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).2.length + 1 ≤ (pre ++ g :: post).length := by
    have h1 : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
        (elim k pre (idStats k, [])).2)).2.length
        ≤ (elim k pre (idStats k, [])).2.length + post.length := elim_len k post _
    have h2 : (elim k pre (idStats k, [])).2.length ≤ 0 + pre.length :=
      elim_len k pre (idStats k, [])
    simp only [List.length_append, List.length_cons]
    omega
  have hval : ∀ y : Fin k → Bool,
      ((elim k post ((elim k pre (idStats k, [])).1 ++ [S],
        (elim k pre (idStats k, [])).2)).1.getD o (Stat.const false)).val
        (wiresFrom (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
          (elim k pre (idStats k, [])).2)).2 (List.ofFn y))
      = vl (pre ++ g :: post) y o := fun y => ((inv3 y).2 o).2
  cases hst : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).1.getD o (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]
    rfl
  | wire j =>
    refine ⟨_, j, hc3, hlen, ?_⟩
    intro y
    have h := hval y
    rw [hst] at h
    exact h

/-- A gate that computes the same function as an earlier wire can be dropped. -/
theorem drop_alias (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p j : ℕ) (hp : p < gs.length)
    (hj : j < k + p) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = vl gs y j)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  apply drop_core k pre g post hcl o ((elim k pre (idStats k, [])).1.getD j (Stat.const false))
    ?_ hnc
  intro y
  have hokpre : ∀ g' ∈ pre, Ok g' :=
    fun g' h => (clean_nok _ _ hcl g' (List.mem_append_left _ h)).1
  have inv1 := inv_elim k (List.ofFn y) (by simp) pre _ _ hokpre (inv_id k y)
  refine ⟨(inv1.2 j).1, ?_⟩
  rw [(inv1.2 j).2, heq y]
  show (wiresFrom pre (List.ofFn y)).getD j false
    = (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD j false
  rw [wiresFrom_append, getD_wiresFrom (g :: post) (wiresFrom pre (List.ofFn y)) j
    (by rw [length_wiresFrom]; simp; omega)]

/-- A gate that computes a constant can be dropped. -/
theorem drop_const (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ) (c : Bool)
    (hp : p < gs.length) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = c)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  exact drop_core k pre g post hcl o (Stat.const c) (fun y => ⟨trivial, (heq y).symm⟩) hnc

/-! ## Statuses -/

/-- The input `y` with the value `b` inserted at position `i`. -/
abbrev ins {n : ℕ} (i : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) : Fin (n + 1) → Bool :=
  Fin.insertNth i b y

/-- The gates the pass emits when input `i` is fixed to `b`. -/
def passG (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) : List Gate :=
  (elim n gs (statAt n i b, [])).2

/-- The final status of wire `a` is a constant when input `i` is fixed to `b`. -/
def IsC (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (a : ℕ) : Prop :=
  ∃ c, stF n gs i b a = Stat.const c

theorem inv_stF (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (y : Fin n → Bool) :
    Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (ins i b y))) (elim n gs (statAt n i b, [])) :=
  inv_elim n _ (by simp) gs _ _ (fun g hg => (clean_nok _ gs hcl g hg).1) (inv_at n i b y)

theorem st_val_const (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (j : ℕ) (c : Bool) (h : stF n gs i b j = Stat.const c) (y : Fin n → Bool) :
    vl gs (ins i b y) j = c := by
  have h1 := ((inv_stF n gs hcl i b y).2 j).2
  rw [show (elim n gs (statAt n i b, [])).1.getD j (Stat.const false) = Stat.const c from h] at h1
  exact h1.symm

theorem st_val_wire (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (j q : ℕ) (h : stF n gs i b j = Stat.wire q) (y : Fin n → Bool) :
    vl gs (ins i b y) j = vl (passG n gs i b) y q := by
  have h1 := ((inv_stF n gs hcl i b y).2 j).2
  rw [show (elim n gs (statAt n i b, [])).1.getD j (Stat.const false) = Stat.wire q from h] at h1
  exact h1.symm

theorem st_other (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (X : Fin (n + 1))
    (h : X ≠ i) : ∃ k, k < n ∧ stF n gs i b X = Stat.wire k := by
  rcases Fin.eq_self_or_eq_succAbove i X with e | ⟨k, e⟩
  · exact absurd e h
  · refine ⟨k, k.isLt, ?_⟩
    rw [e]
    show (elim n gs (statAt n i b, [])).1.getD (i.succAbove k) (Stat.const false) = _
    rw [elim_getD n _ _ gs _ (by
      show ((i.succAbove k : Fin (n + 1)) : ℕ) < (statAt n i b).length
      rw [statAt_length]; exact (i.succAbove k).isLt)]
    exact statAt_above n i b k

/-- The final status of a gate is what `simplify` makes of the final statuses of its inputs. -/
theorem st_gate (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (p : ℕ) (g : Gate) (hp : gs[p]? = some g) :
    ∃ t, stF n gs i b (n + 1 + p)
      = (simplify g.op (n + t) (g.inputs.map (stF n gs i b))).2 := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  refine ⟨(elim n pre (statAt n i b, [])).2.length, ?_⟩
  have e1 : stF n (pre ++ g :: post) i b (n + 1 + pre.length)
      = (elimStep n (elim n pre (statAt n i b, [])) g).1.getD (n + 1 + pre.length)
        (Stat.const false) :=
    elim_split_getD n pre g post _ _ _ (by rw [hL])
  have e2 : (elimStep n (elim n pre (statAt n i b, [])) g).1.getD (n + 1 + pre.length)
        (Stat.const false)
      = (simplify g.op (n + (elim n pre (statAt n i b, [])).2.length)
          (g.inputs.map fun a => (elim n pre (statAt n i b, [])).1.getD a (Stat.const false))).2 :=
    getD_snoc_len _ _ _ _ (by rw [elim_fst_len, hL])
  have e3 : (g.inputs.map fun a => (elim n pre (statAt n i b, [])).1.getD a (Stat.const false))
      = g.inputs.map (stF n (pre ++ g :: post) i b) :=
    List.map_congr_left (fun a ha =>
      (elim_split_getD_lt n pre g post _ a _ (by rw [hL]; exact hlt a ha)).symm)
  rw [e1, e2, e3]

theorem simp_allconst (op : GateOp) (t : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (h : ∀ s ∈ ins, ∃ c, s = Stat.const c) : ∃ c, (simplify op t ins).2 = Stat.const c := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      obtain ⟨c', rfl⟩ := h d (by simp)
      exact ⟨_, rfl⟩
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      obtain ⟨c', rfl⟩ := h d (by simp)
      exact ⟨_, rfl⟩
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩

theorem simp_fresh (g : Gate) (m : ℕ) (hg : CleanGate m g) (t : ℕ) (F : ℕ → Stat)
    (h : ∀ a ∈ g.inputs, ∀ c, F a ≠ Stat.const c) :
    (simplify g.op t (g.inputs.map F)).2 = Stat.wire t := by
  rcases hg with ⟨hop, j, _, hin⟩ | ⟨hop | hop, j, k, _, _, hin⟩
  · have h1 := h j (by rw [hin]; simp)
    rw [hop, hin]
    cases hF : F j with
    | const c => exact absurd hF (h1 c)
    | wire q => simp [simplify, simpNot, hF]
  · have h1 := h j (by rw [hin]; simp)
    have h2 := h k (by rw [hin]; simp)
    rw [hop, hin]
    cases hF : F j with
    | const c => exact absurd hF (h1 c)
    | wire q =>
      cases hF' : F k with
      | const c => exact absurd hF' (h2 c)
      | wire q' => simp [simplify, simpAnd, hF, hF']
  · have h1 := h j (by rw [hin]; simp)
    have h2 := h k (by rw [hin]; simp)
    rw [hop, hin]
    cases hF : F j with
    | const c => exact absurd hF (h1 c)
    | wire q =>
      cases hF' : F k with
      | const c => exact absurd hF' (h2 c)
      | wire q' => simp [simplify, simpOr, hF, hF']

theorem st_allconst (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (h : ∀ a ∈ g.inputs, IsC n gs i b a) : IsC n gs i b (n + 1 + p) := by
  obtain ⟨t, ht⟩ := st_gate n gs hcl i b p g hp
  have hn := (hcl p g hp).nok
  obtain ⟨c, hc⟩ := simp_allconst g.op (n + t) (g.inputs.map (stF n gs i b)) hn.1.1
    (by simpa using hn.1.2) (by
      intro s hs
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hs
      exact h a ha)
  exact ⟨c, by rw [ht]; exact hc⟩

/-- A gate that reads no wire of constant status gets a fresh wire. -/
theorem st_fresh (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (h : ∀ a ∈ g.inputs, ∀ c, stF n gs i b a ≠ Stat.const c) :
    ∃ q, n ≤ q ∧ stF n gs i b (n + 1 + p) = Stat.wire q := by
  obtain ⟨t, ht⟩ := st_gate n gs hcl i b p g hp
  exact ⟨n + t, by omega, by rw [ht]; exact simp_fresh g _ (hcl p g hp) _ _ h⟩

theorem rc_of_const (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (hc : IsC n gs i b (n + 1 + p)) :
    RC n gs i b p := by
  by_contra hno
  obtain ⟨q, _, hq⟩ := st_fresh n gs hcl i b p g hp
    (fun a ha c' hc' => hno ⟨g, hp, a, ha, c', hc'⟩)
  obtain ⟨c, hc⟩ := hc
  rw [hq] at hc
  cases hc

theorem const_read (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (a : ℕ) (ha : a ∈ g.inputs)
    (hc : stF n gs i b a = Stat.const (fixBit g)) : IsC n gs i b (n + 1 + p) := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have h := const_of_read n gs (statAt n i b, []) p g hp ((hcl p g hp).nok) a ha
    (by rw [hL]; exact (hcl p g hp).lt a ha) hc
  rw [hL] at h
  exact h

/-- A gate of non-constant status that reads a wire of constant status `c`: it is an AND or OR
gate, `c` is not its absorbing value, and another input has non-constant status. -/
theorem st_shape (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (a : ℕ) (ha : a ∈ g.inputs) (c : Bool)
    (hc : stF n gs i b a = Stat.const c) (hn : ∀ c', stF n gs i b (n + 1 + p) ≠ Stat.const c') :
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ c ≠ fixBit g ∧
      ∃ w ∈ g.inputs, ∀ c', stF n gs i b w ≠ Stat.const c' := by
  have hw : ∃ w ∈ g.inputs, ∀ c', stF n gs i b w ≠ Stat.const c' := by
    by_contra hno
    obtain ⟨c', hc'⟩ := st_allconst n gs hcl i b p g hp (fun a' ha' => by
      by_contra h'
      exact hno ⟨a', ha', fun c' hc' => h' ⟨c', hc'⟩⟩)
    exact hn c' hc'
  refine ⟨?_, ?_, hw⟩
  · rcases hcl p g hp with ⟨_, j, _, hin⟩ | ⟨hop, _⟩
    · exfalso
      obtain ⟨w, hw1, hw2⟩ := hw
      have e1 : w = j := by rw [hin] at hw1; simpa using hw1
      have e2 : a = j := by rw [hin] at ha; simpa using ha
      exact hw2 c (by rw [e1, ← e2]; exact hc)
    · exact hop
  · intro e
    obtain ⟨c', hc'⟩ := const_read n gs hcl i b p g hp a ha (by rw [← e]; exact hc)
    exact hn c' hc'

theorem four_count (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p1 p2 p3 p4 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4)
    (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) (h4 : RC n gs i b p4) :
    (passG n gs i b).length + 4 ≤ gs.length := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have hcount := elim_count n (statAt n i b, []) gs (clean_nok _ gs hcl) {p1, p2, p3, p4} (by
    intro p hp
    have hR : RC n gs i b p := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> assumption
    obtain ⟨g, hg, a, ha, c, hc⟩ := hR
    refine ⟨g, hg, a, ha, ?_, c, hc⟩
    rw [hL]
    exact (hcl p g hg).lt a ha)
  have hcard : ({p1, p2, p3, p4} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [h12, h13, h14]),
      Finset.card_eq_three.2 ⟨p2, p3, p4, h23, h24, h34, rfl⟩]
  rw [hcard] at hcount
  simpa [passG] using hcount

def f (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4276676840 * 2 ^ 32 + 3907577984) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def flip (x : Fin 6 → Bool) (i : Fin 6) : Fin 6 → Bool := Function.update x i (!x i)

lemma essential : ∀ i : Fin 6, ∃ x : Fin 6 → Bool, f (flip x i) ≠ f x := by
  decide +kernel

lemma nonconstantPins (i : Fin 6) (b : Bool) :
    f (ins i b (fun _ => false)) ≠ f (ins i b (fun _ => true)) := by
  have h : ∀ (i : Fin 6) (b : Bool),
      f (ins i b (fun _ => false)) ≠ f (ins i b (fun _ => true)) := by decide +kernel
  exact h i b

def lowCount (x : Fin 6 → Bool) : ℕ :=
  (if x 3 then 1 else 0) + (if x 4 then 1 else 0) + (if x 5 then 1 else 0)

def supporting (i : Fin 6) (x : Fin 6 → Bool) (j : Fin 6) : Bool :=
  if 3 ≤ j.val then x j else if j = i then false else
    if lowCount x = 0 then true else if lowCount x = 3 then false else
    j == (if i = 0 then 1 else 0)

set_option maxHeartbeats 0 in
lemma supportingFlip : ∀ (i : Fin 6) (x : Fin 6 → Bool), i.val < 3 →
    f (flip (supporting i x) i) ≠ f (supporting i x) := by decide +kernel

def whenHigh (i : Fin 6) (b : Bool) (j : Fin 6) : Bool :=
  if 3 ≤ j.val then !b else if j = i then false else b

lemma whenHighFlip : ∀ (i : Fin 6) (b : Bool), i.val < 3 →
    f (flip (whenHigh i b) i) ≠ f (whenHigh i b) := by decide +kernel

lemma noReaderChange (gs : List Gate) (o p : ℕ) (g : Gate) (i : Fin 6) (w : ℕ)
    (hcl : CleanL 6 gs) (hp : gs[p]? = some g) (hoi : o ≠ (i : ℕ))
    (hop : g.op = .and ∨ g.op = .or) (hw : w ∈ g.inputs) (hwi : w ≠ (i : ℕ))
    (onlyReader : ∀ q g', gs[q]? = some g' → (i : ℕ) ∈ g'.inputs → q = p)
    (u : Fin 6 → Bool) (hu : vl gs u w = fixBit g) :
    vl gs (flip u i) o = vl gs u o := by
  apply agree_B gs hcl (flip u i) u (fun j => j = (i : ℕ)) (o + 1) ?_ ?_ o (by omega) hoi
  · intro j hj hjne
    rw [vl_input gs _ j hj, vl_input gs _ j hj]
    exact Function.update_of_ne (fun e => hjne (congrArg Fin.val e)) _ _
  · intro q g' hq _ _ hr earlier
    obtain ⟨j, hj, rfl⟩ := hr
    have hqp := onlyReader q g' hq hj
    subst q
    have hg : g' = g := gate_eq hq hp rfl
    subst g'
    have hww : vl gs (flip u i) w = vl gs u w := earlier w ((hcl p g hp).lt w hw) hwi
    rw [vl_abs gs hcl _ p g hp hop w hw (hww.trans hu),
      vl_abs gs hcl u p g hp hop w hw hu]

lemma notStatus (gs : List Gate) (hcl : CleanL 6 gs) (i : Fin 6) (p : ℕ) (g : Gate)
    (hp : gs[p]? = some g) (hop : g.op = .not) (hin : g.inputs = [(i : ℕ)]) (b : Bool) :
    stF 5 gs i b (6 + p) = Stat.const (!b) := by
  obtain ⟨c, hc⟩ := st_allconst 5 gs hcl i b p g hp (fun a ha => by
    rw [hin] at ha
    have e : a = (i : ℕ) := by simpa using ha
    rw [e]; exact ⟨b, stF_self 5 gs i b⟩)
  have he := st_val_const 5 gs hcl i b (6 + p) c hc (fun _ => false)
  have hv : vl gs (ins i b fun _ => false) (i : ℕ) = b := by
    rw [vl_input gs _ i i.isLt]
    simp [ins]
  have hn : c = !b := by
    rw [← he, vl_gate gs hcl _ p g hp, hop, hin]
    simp [GateOp.eval, hv]
  rw [hc, hn]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem structural
    (cofactorLower : ∀ (i : Fin 6), i.val < 3 → ∀ (b : Bool) (s : ℕ),
      HasCircuitSize 5 (fun y : Fin 5 → Bool => f (ins i b y)) s → 9 ≤ s)
    (s : ℕ) (h : HasCircuitSize 6 f s) : 12 ≤ s := by
  classical
  have hf0 : f (fun _ => false) ≠ f (fun _ => true) := by decide
  have h0 : HasClean 6 f s := clean_of 6 f s ⟨fun _ => false, fun _ => true, hf0⟩ h
  have existsClean : ∃ t, HasClean 6 f t := ⟨s,h0⟩
  obtain ⟨gs,o,hcl,hlen,hev0⟩ := Nat.find_spec existsClean
  have hs := Nat.find_min' existsClean h0
  have hev : ∀ x : Fin 6 → Bool, vl gs x o = f x := hev0
  have hmin : ∀ (gs' : List Gate) (o' : ℕ), CleanL 6 gs' →
      (∀ x : Fin 6 → Bool, vl gs' x o' = f x) → gs.length ≤ gs'.length := by
    intro ds j hc he
    have hm := Nat.find_min' existsClean (show HasClean 6 f ds.length from ⟨ds,j,hc,le_rfl,he⟩)
    omega
  have hncf : ∃ x y : Fin 6 → Bool, vl gs x o ≠ vl gs y o := by
    refine ⟨fun _ => false, fun _ => true, ?_⟩
    simpa only [hev] using hf0
  by_contra hsmall
  have hout : ∀ (i : Fin 6) (b c : Bool), stF 5 gs i b o ≠ Stat.const c := by
    intro i b c hh
    apply nonconstantPins i b
    rw [← hev, ← hev, st_val_const 5 gs hcl i b o c hh, st_val_const 5 gs hcl i b o c hh]
  have hsupp : ∀ i : Fin 6, i ∈ (suppsFrom gs (inputSupps 6)).getD o ∅ := by
    intro i
    by_contra hns
    obtain ⟨u,hu⟩ := essential i
    apply hu
    rw [← hev, ← hev]
    exact (agree_wiresFrom (Function.update u i (!u i)) u gs _ _ _ (agree_inputs _ _)).2.2 o (by
      intro j hj
      have hjne : j ≠ i := fun e => hns (e ▸ hj)
      exact Function.update_of_ne hjne _ _)
  have noThree (i : Fin 6) (hi : i.val < 3) (b : Bool) :
      ¬ (passG 5 gs i b).length + 3 ≤ gs.length := by
    intro hsave
    cases hst : stF 5 gs i b o with
    | const c => exact hout i b c hst
    | wire j =>
      have basis : FanInTwo (⟨passG 5 gs i b,j⟩ : Circuit) := by
        intro g hg
        exact (clean_nok 5 _ (clean_elim 5 (List.ofFn fun _ : Fin 5 => false)
          (by simp) gs _ _ (fun g hg' => (clean_nok 6 gs hcl g hg').1)
          (inv_at 5 i b _) (by intro p g hp; simp at hp)) g hg).1
      have hc : HasCircuitSize 5 (fun y => f (ins i b y)) (passG 5 gs i b).length := by
        refine ⟨⟨passG 5 gs i b,j⟩, basis, le_rfl, ?_⟩
        intro y
        exact (st_val_wire 5 gs hcl i b o j hst y).symm.trans (hev _)
      have lower := cofactorLower i hi b _ hc
      omega
  have hoi : ∀ i : Fin 6, o ≠ (i : ℕ) := fun i e => hout i false false (by
    rw [e]
    exact stF_self 5 gs i false)
  have hexRead : ∃ p : ℕ, ∃ g : Gate, gs[p]? = some g ∧
      ∃ i : Fin 6, i.val < 3 ∧ (i : ℕ) ∈ g.inputs := by
    let i : Fin 6 := 0
    obtain ⟨p,g,hp,houtside,w,hw,he⟩ := exists_reader 6 i
      (fun a => a = (i : ℕ)) rfl gs o (hoi i) (hsupp i)
    exact ⟨p,g,hp,i,by decide,he ▸ hw⟩
  let p := Nat.find hexRead
  obtain ⟨g,hp,i,hi,hri⟩ := Nat.find_spec hexRead
  have onlyReader : ∀ q g', gs[q]? = some g' → (i : ℕ) ∈ g'.inputs → q = p := by
    intro q g' hq hread
    by_contra hne
    obtain ⟨b,hb⟩ := three_core_at 5 gs hcl o hsupp hout p g hp i hri (Or.inr ⟨q,g',hne,hq,hread⟩)
    exact noThree i hi b hb
  obtain ⟨w,hwl,hw,hin,hop⟩ :
      ∃ w, w < 6 + p ∧ w ∈ g.inputs ∧
        (g.inputs = [(i : ℕ),w] ∨ g.inputs = [w,(i : ℕ)]) ∧ (g.op = .and ∨ g.op = .or) := by
    rcases hcl p g hp with ⟨hop,j,_,hin⟩ | ⟨hop,j,k,hj,hk,hin⟩
    · have hji : (i : ℕ) = j := by simpa [hin] using hri
      have hin' : g.inputs = [(i : ℕ)] := by rw [hin,hji]
      have hnc : ∀ c, ∃ b, stF 5 gs i b (6+p) = Stat.const c := by
        intro c
        exact ⟨!c, by simpa using notStatus gs hcl i p g hp hop hin' (!c)⟩
      obtain ⟨b,hb⟩ := three_core_at 5 gs hcl o hsupp hout p g hp i hri (Or.inl hnc)
      exact (noThree i hi b hb).elim
    · have hmem : (i : ℕ) = j ∨ (i : ℕ) = k := by simpa [hin] using hri
      rcases hmem with hj' | hk'
      · exact ⟨k,hk,by simp [hin],Or.inl (by rw [hin,hj']),hop⟩
      · exact ⟨j,hj,by simp [hin],Or.inr (by rw [hin,hk']),hop⟩
  have aliasIsImpossible (hwAlias : ∀ u : Fin 6 → Bool, vl gs u (6+p) = vl gs u (i : ℕ)) : False := by
    have hpLt := (List.getElem?_eq_some_iff.1 hp).1
    obtain ⟨ds,j,hc,hl,he⟩ := drop_alias 6 gs hcl o p i hpLt (by have := i.isLt; omega) hwAlias hncf
    have hm := hmin ds j hc (fun u => (he u).trans (hev u))
    omega
  by_cases hwi : w = (i : ℕ)
  · apply aliasIsImpossible
    intro u
    rw [vl_gate gs hcl u p g hp]
    rcases hin with hh | hh <;> rw [hh,hwi]
    all_goals rcases hop with ho|ho <;> simp [ho,GateOp.eval]
  have notAbsorbing (u : Fin 6 → Bool) (hu : f (flip u i) ≠ f u) :
      vl gs u w ≠ fixBit g := by
    intro hab
    apply hu
    rw [← hev, ← hev]
    exact noReaderChange gs o p g i w hcl hp (hoi i) hop hw hwi onlyReader u hab
  have hwLow : 3 ≤ w := by
    by_contra! hlt
    let j : Fin 6 := ⟨w,by omega⟩
    have hji : j ≠ i := fun e => hwi (congrArg Fin.val e)
    let u := whenHigh i (fixBit g)
    have hu : f (flip u i) ≠ f u := whenHighFlip i _ hi
    apply notAbsorbing u hu
    rw [vl_input gs u w (by omega)]
    simp [u,whenHigh,j,hji,not_le.mpr hlt]
  have earlySame (u v : Fin 6 → Bool) (hLight : ∀ j : Fin 6, 3 ≤ j.val → u j = v j) :
      vl gs u w = vl gs v w := by
    apply agree_B gs hcl u v (fun a => a < 3) (6+p) ?_ ?_ w hwl (by omega)
    · intro j hj hj'
      rw [vl_input gs _ j hj,vl_input gs _ j hj]
      change ¬ j < 3 at hj'
      exact hLight ⟨j,hj⟩ (show 3 ≤ j by omega)
    · intro q g' hq hqp _ reads _
      obtain ⟨a,ha,ha'⟩ := reads
      have hq' : q < p := by omega
      exact (Nat.find_min hexRead hq' ⟨g',hq,⟨a,by omega⟩,ha',ha⟩).elim
  have neutral (u : Fin 6 → Bool) : vl gs u w ≠ fixBit g := by
    intro hu
    let v := supporting i u
    have hSame := earlySame v u (fun j hj => by simp [v,supporting,hj])
    exact notAbsorbing v (supportingFlip i u hi) (hSame.trans hu)
  apply aliasIsImpossible
  intro u
  have hh := neutral u
  rw [vl_gate gs hcl u p g hp]
  rcases hin with hh' | hh' <;> rw [hh']
  all_goals
    rcases hop with ho|ho <;> rw [ho]
    · have hW : vl gs u w = true := by
        have hb : fixBit g = false := by simp [fixBit,ho]
        rw [hb] at hh
        cases hv : vl gs u w <;> simp_all
      simp [GateOp.eval,hW]
    · have hW : vl gs u w = false := by
        have hb : fixBit g = true := by simp [fixBit,ho]
        rw [hb] at hh
        cases hv : vl gs u w <;> simp_all
      simp [GateOp.eval,hW]

end PEqualNP.Outside.L_meta_12302.FirstGate
-- The live-wire checker is adapted from ljste's PR 2918 and jfsantoropereira's L-meta-1007.
-- Adapted from the signed live-wire certificate in L_meta_8721. Apache-2.0.
namespace PEqualNP.Outside.L_meta_12302.Core

abbrev B := BitVec 52
abbrev Sig := B × B
def top : B := BitVec.allOnes 52
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
  by_cases hi : i < 52
  · cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases ht : decide (0<t) <;>
      simp only [sep,neg,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 52 ≤ i)] at h

private lemma sep_binary (t d : Bool) (a b : Sig) (i : Nat)
    (h : (sep t (bin d a b)).getLsbD i = true) :
    (sep t a).getLsbD i = true ∨ (sep t b).getLsbD i = true := by
  by_cases hi : i < 52
  · cases t <;> cases d <;>
      cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases hu : b.1.getLsbD i <;> cases hv : b.2.getLsbD i <;>
      simp only [sep,bin,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,hu,hv] at h ⊢ <;> first | contradiction | decide
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 52 ≤ i)] at h

private lemma sep_weaken (t : Nat) (a : Sig) (i : Nat) (hi : i < 52)
    (h : (sep (decide (0<t)) a).getLsbD i = true) : (sep true a).getLsbD i = true := by
  cases ht : decide (0<t) <;> cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
    simp only [sep,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide

private lemma live_sep {k t S} (h : Live k t S) (i : Nat) (hi : i < 52) :
    ∃ a ∈ S, (sep (decide (0<t)) a).getLsbD i = true := by
  induction h using liveInd with
  | stop =>
    refine ⟨target,by simp,?_⟩
    change (BitVec.allOnes 52 &&& ~~~(0 : B)).getLsbD i = true
    rw [BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_allOnes (v := 52)]
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

def bit (side : Bool) (i : Fin 52) (a : Sig) : Bool :=
  (if side then a.1 else a.2).getLsbD i.val

private lemma bit_zero (s i) : bit s i zero = false := by cases s <;> simp [bit,zero]
private lemma bit_one (s i) : bit s i one = true := by
  cases s <;> change (BitVec.allOnes 52).getLsbD i.val = true <;> rw [BitVec.getLsbD_allOnes] <;> simp
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


def graph (b : Bool) (x : Fin 5 → Bool) : Bool := Nat.testBit (if b then 0xfeeeeee8 else 0xe8888880) (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)
def sample (raw : List Sig) (s : Bool) (i : Fin 52) (j : Fin 5) := bit s i (raw.getD j.val zero)
private lemma sample_list (raw : List Sig) (raw_id : List.ofFn (fun j : Fin 5 => raw.getD j.val zero) = raw) (s i) : List.ofFn (sample raw s i) = raw.map (bit s i) := by
  calc
    _ = (List.ofFn (fun j : Fin 5 => raw.getD j.val zero)).map (bit s i) := by rw [List.map_ofFn]; rfl
    _ = _ := by rw [raw_id]

private lemma circuit_target (b : Bool) (raw : List Sig) (raw_id : List.ofFn (fun j : Fin 5 => raw.getD j.val zero) = raw)
    (sample_ok : ∀ s i, graph b (sample raw s i) = s) (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = graph b x) : target ∈ execute C.gates raw := by
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

-- The bit permutation applies independently to the positive and negative rows.
private def bitsFrom : (n : Nat) → (Nat → Bool) → BitVec n
  | 0, _ => 0
  | n + 1, f => BitVec.cons (f n) (bitsFrom n f)

private theorem bitsFrom_get (n : Nat) (f : Nat → Bool) (i : Nat) (h : i < n) :
    (bitsFrom n f).getLsbD i = f i := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [bitsFrom, BitVec.getLsbD_cons]
    by_cases hi : i = n
    · simp [hi]
    · rw [ite_eq_right hi, ih (by omega)]

private def bitsMap {n : Nat} (p : Equiv.Perm (Fin n)) (a : BitVec n) : BitVec n :=
  bitsFrom n (fun i => if h : i < n then a.getLsbD (p ⟨i, h⟩).val else false)

private theorem bitsMap_get {n : Nat} (p : Equiv.Perm (Fin n)) (a : BitVec n)
    (i : Nat) (h : i < n) : (bitsMap p a).getLsbD i = a.getLsbD (p ⟨i, h⟩).val := by
  rw [bitsMap,bitsFrom_get _ _ _ h,dite_eq_left h]

private def bitsEquiv {n : Nat} (p : Equiv.Perm (Fin n)) : Equiv.Perm (BitVec n) :=
  ⟨bitsMap p, bitsMap p.symm,
    fun a => BitVec.eq_of_getLsbD_eq fun i hi => by
      rw [bitsMap_get _ _ _ hi,bitsMap_get _ _ _ (p.symm ⟨i, hi⟩).isLt]
      simp,
    fun a => BitVec.eq_of_getLsbD_eq fun i hi => by
      rw [bitsMap_get _ _ _ hi,bitsMap_get _ _ _ (p ⟨i, hi⟩).isLt]
      simp⟩

private abbrev bitCount : Nat := 52

private def permSignal (p : Equiv.Perm (Fin bitCount)) : Equiv.Perm Sig :=
  Equiv.prodCongr (bitsEquiv p) (bitsEquiv p)

private theorem bitsMap_zero {n : Nat} (p : Equiv.Perm (Fin n)) :
    bitsMap p 0 = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i h
  rw [bitsMap_get _ _ _ h]
  simp

private theorem bitsMap_ones {n : Nat} (p : Equiv.Perm (Fin n)) :
    bitsMap p (BitVec.allOnes n) = BitVec.allOnes n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i h
  rw [bitsMap_get _ _ _ h]
  simp [(p ⟨i,h⟩).isLt,h]

private theorem bitsMap_not {n : Nat} (p : Equiv.Perm (Fin n)) (a : BitVec n) :
    bitsMap p (~~~a) = ~~~(bitsMap p a) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i h
  simp only [bitsMap_get _ _ _ h,BitVec.getLsbD_not,(p ⟨i,h⟩).isLt,h,decide_true,Bool.true_and]

private theorem bitsMap_and {n : Nat} (p : Equiv.Perm (Fin n)) (a b : BitVec n) :
    bitsMap p (a &&& b) = bitsMap p a &&& bitsMap p b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i h
  simp only [bitsMap_get _ _ _ h,BitVec.getLsbD_and]

private theorem bitsMap_or {n : Nat} (p : Equiv.Perm (Fin n)) (a b : BitVec n) :
    bitsMap p (a ||| b) = bitsMap p a ||| bitsMap p b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i h
  simp only [bitsMap_get _ _ _ h,BitVec.getLsbD_or]

private theorem permSignal_zero (p : Equiv.Perm (Fin bitCount)) :
    permSignal p zero = zero := by
  change (bitsMap p 0, bitsMap p 0) = (0,0)
  rw [bitsMap_zero]

private theorem permSignal_one (p : Equiv.Perm (Fin bitCount)) :
    permSignal p one = one := by
  change (bitsMap p top, bitsMap p top) = (top,top)
  unfold top
  rw [bitsMap_ones]

private theorem permSignal_target (p : Equiv.Perm (Fin bitCount)) :
    permSignal p target = target := by
  change (bitsMap p top, bitsMap p 0) = (top,0)
  unfold top
  rw [bitsMap_ones,bitsMap_zero]

private theorem permSignal_neg (p : Equiv.Perm (Fin bitCount)) (a : Sig) :
    permSignal p (neg a) = neg (permSignal p a) := by
  change (bitsMap p (~~~a.1), bitsMap p (~~~a.2)) = (~~~(bitsMap p a.1), ~~~(bitsMap p a.2))
  simp [bitsMap_not]

private theorem permSignal_bin (p : Equiv.Perm (Fin bitCount)) (d : Bool) (a b : Sig) :
    permSignal p (bin d a b) = bin d (permSignal p a) (permSignal p b) := by
  cases d
  · change (bitsMap p (a.1 &&& b.1), bitsMap p (a.2 &&& b.2)) =
      (bitsMap p a.1 &&& bitsMap p b.1,bitsMap p a.2 &&& bitsMap p b.2)
    simp [bitsMap_and]
  · change (bitsMap p (a.1 ||| b.1), bitsMap p (a.2 ||| b.2)) =
      (bitsMap p a.1 ||| bitsMap p b.1,bitsMap p a.2 ||| bitsMap p b.2)
    simp [bitsMap_or]

private theorem proper_permSignal (p : Equiv.Perm (Fin bitCount)) {a : Sig}
    (ha : proper a) : proper (permSignal p a) := by
  exact ⟨fun h => ha.1 ((permSignal p).injective (h.trans (permSignal_zero p).symm)),
    fun h => ha.2 ((permSignal p).injective (h.trans (permSignal_one p).symm))⟩

theorem live_permSignal (p : Equiv.Perm (Fin bitCount)) {k t s} (h : Live k t s) :
    Live k t (s.map (permSignal p).toEmbedding) := by
  induction h using liveInd with
  | stop =>
    simpa [permSignal_target] using Live.stop
  | @unary m t U a ha hf tail ih =>
    simp only [Finset.map_insert, Equiv.toEmbedding_apply] at ih ⊢
    rw [permSignal_neg] at ih
    apply Live.unary (proper_permSignal p ha) _ ih
    rw [← permSignal_neg, ← Equiv.toEmbedding_apply, ← Finset.map_insert]
    exact fun h => hf (Finset.mem_map.mp h |>.elim fun b ⟨hb, hab⟩ =>
      (permSignal p).injective hab ▸ hb)
  | @binary m t U a b d ha hb hab hf tail ih =>
    simp only [Finset.map_insert, Equiv.toEmbedding_apply] at ih ⊢
    rw [permSignal_bin] at ih
    apply Live.binary (proper_permSignal p ha) (proper_permSignal p hb)
      (fun h => hab ((permSignal p).injective h)) _ ih
    have hnMap : (permSignal p).toEmbedding (bin d a b) ∉
        (insert a (insert b U)).map (permSignal p).toEmbedding := by
      intro h
      obtain ⟨c, hc, he⟩ := Finset.mem_map.mp h
      exact hf ((permSignal p).injective he ▸ hc)
    simpa only [Finset.map_insert, Equiv.toEmbedding_apply, permSignal_bin] using hnMap

private lemma guarded_any {α : Type} (c : Bool) (v : List α) (r : α → Bool) :
    (if c then v else []).any r = (c && v.any r) := by cases c <;> rfl

private def gateKids (k t : Nat) (v rest : List Sig) (n : Nat) (c : B) (g : Sig)
    (keep : List (List Sig)) : List (List Sig) :=
  let d := decide (0<t)
  let base := sep d g ||| c
  if n = k-t then
    if base == top && gateAvailable v g then [g::rest] else []
  else keep.filterMap fun h => if decide (n+h.length+1 ≤ k-t+1) &&
    (base ||| unionSep d h == top) && gateAvailable v g then some (g::(h++rest)) else none

private lemma gateKids_any (k t : Nat) (r : List Sig → Bool) (v rest : List Sig)
    (n : Nat) (c : B) (g : Sig) (keep : List (List Sig)) :
    (gateKids k t v rest n c g keep).any r = tryGate k t r v rest n c g keep := by
  simp only [gateKids, tryGate]
  split
  · simp only [guarded_any, List.any_cons, List.any_nil, Bool.or_false]
  · rw [List.any_filterMap]
    apply List.any_congr rfl
    intro h
    split <;> simp_all [Bool.and_assoc]

private def unaryKids (k t : Nat) (v : List Sig) : List (List Sig) :=
  let c := coverage (decide (0<t)) v
  v.flatMap fun a => if !(special.contains a) then
    gateKids k t v (dropped [a] v) (v.length-1) (takeOne c (sep (decide (0<t)) a)) (neg a) [[],[a]]
    else []

private lemma unaryKids_any (k t : Nat) (r : List Sig → Bool) (v : List Sig) :
    (unaryKids k t v).any r = unaryMoves k t r v := by
  simp only [unaryKids, unaryMoves, List.any_flatMap]
  apply List.any_congr rfl
  intro a
  simp only [unaryAt, guarded_any, gateKids_any]

private def fastKids (v : List Sig) (a b : Sig) (ua ub : B) : List (List Sig) :=
  let rest := dropped [a,b] v
  let use := fun (g : Sig) => if gateAvailable v g then [g::rest] else []
  (if (ua &&& ~~~b.1) == 0 && (ub &&& ~~~a.1) == 0 &&
    !(special.contains a) && !(special.contains b) then use (bin false a b) else []) ++
    (if (ua &&& b.2) == 0 && (ub &&& a.2) == 0 then use (bin true a b) else [])

private lemma fastKids_any (r : List Sig → Bool) (v : List Sig) (a b : Sig) (ua ub : B) :
    (fastKids v a b ua ub).any r = fastBinary r v a b ua ub := by
  simp only [fastKids, fastBinary, List.any_append, guarded_any, List.any_cons, List.any_nil,
    Bool.or_false, Bool.and_assoc]

private def slowKids (k t : Nat) (v : List Sig) (c : Cov) (a b : Sig) : List (List Sig) :=
  let rest := dropped [a,b] v
  let mask := takeTwo c (sep (decide (0<t)) a) (sep (decide (0<t)) b)
  (if !(special.contains a) && !(special.contains b) then
    gateKids k t v rest (v.length-2) mask (bin false a b) [[],[a],[b],[a,b]] else []) ++
    gateKids k t v rest (v.length-2) mask (bin true a b) (allowedKeeps a b)

private lemma slowKids_any (k t : Nat) (r : List Sig → Bool) (v : List Sig)
    (c : Cov) (a b : Sig) :
    (slowKids k t v c a b).any r = slowBinary k t r v c a b := by
  simp only [slowKids, slowBinary, List.any_append, guarded_any, gateKids_any]

private def flatPairs {α β : Type} (p : α → α → List β) : List α → List β
  | [] => []
  | a :: t => t.flatMap (p a) ++ flatPairs p t

private lemma flatPairs_any {α β : Type} (p : α → α → List β) (r : β → Bool)
    (v : List α) : (flatPairs p v).any r = scanPairs (fun a b => (p a b).any r) v := by
  induction v with
  | nil => rfl
  | cons a t ih => simp [flatPairs, scanPairs, ih]

private def binaryKids (k t : Nat) (v : List Sig) : List (List Sig) :=
  let d := decide (0<t)
  let c := coverage d v
  if t == 0 && v.length == k+2 then
    let acts := v.map (fun a => (a, c.2.1 &&& sep false a))
    flatPairs (fun a b => fastKids v a.1 b.1 a.2 b.2) acts
  else flatPairs (slowKids k t v c) v

private lemma binaryKids_any (k t : Nat) (r : List Sig → Bool) (v : List Sig) :
    (binaryKids k t v).any r = binaryMoves k t r v := by
  unfold binaryKids binaryMoves
  split <;> simp [flatPairs_any, fastKids_any, slowKids_any]

private abbrev SearchState := Nat × List Sig

private def kids (k : Nat) (s : SearchState) : List SearchState :=
  let (t,v) := s
  if t>k+1 ∨ v.length>k+1-t+1 then [] else
    (if 0<t then (unaryKids k (t-1) v).map (t-1, ·) else []) ++
      (binaryKids k t v).map (t, ·)

private lemma stepTest_kids (k t : Nat) (v : List Sig) (r : SearchState → Bool) :
    stepTest k t v (fun w => r (t-1,w)) (fun w => r (t,w)) =
      ((decide (¬ (t>k+1 ∨ v.length>k+1-t+1)) && (v == [target])) ||
        (kids k (t,v)).any r) := by
  unfold stepTest kids
  split
  · simp_all
  · rename_i h
    simp only [h, ite_false, not_false_eq_true, decide_true, Bool.true_and]
    rw [List.any_append, List.any_map, binaryKids_any]
    by_cases ht : 0<t <;> simp [ht, List.any_map, unaryKids_any, Bool.or_assoc, Function.comp_def]


private abbrev BitPerm := Equiv.Perm (Fin bitCount)

private def dual (a : Sig) : Sig := (~~~a.2,~~~a.1)

private def dualEquiv : Equiv.Perm Sig :=
  ⟨dual,dual,by intro a; simp [dual],by intro a; simp [dual]⟩

private theorem dual_zero : dual zero = one := by decide +kernel
private theorem dual_one : dual one = zero := by decide +kernel
private theorem dual_target : dual target = target := by decide +kernel

private theorem dual_proper {a : Sig} (ha : proper a) : proper (dual a) := by
  exact ⟨fun h => ha.2 (dualEquiv.injective (h.trans dual_one.symm)),
    fun h => ha.1 (dualEquiv.injective (h.trans dual_zero.symm))⟩

private theorem dual_neg (a : Sig) : dual (neg a) = neg (dual a) := rfl

private theorem dual_bin (a b : Sig) (d : Bool) : dual (bin d a b) = bin (!d) (dual a) (dual b) := by
  cases d <;> simp [dual,bin,BitVec.not_and,BitVec.not_or]

private theorem live_dual {k t s} (h : Live k t s) : Live k t (s.map dualEquiv.toEmbedding) := by
  induction h using liveInd with
  | stop =>
    simpa [show dualEquiv target = target from dual_target] using Live.stop
  | @unary m t U a ha hf tail ih =>
    have hneg : ∀ a, dualEquiv (neg a) = neg (dualEquiv a) := dual_neg
    simp only [Finset.map_insert, Equiv.toEmbedding_apply, hneg] at ih ⊢
    apply Live.unary (dual_proper ha) _ ih
    have hg : dualEquiv.toEmbedding (neg a) ∉ (insert a U).map dualEquiv.toEmbedding := by
      intro h
      obtain ⟨c,hc,he⟩ := Finset.mem_map.mp h
      exact hf (dualEquiv.injective he ▸ hc)
    change neg (dualEquiv a) ∉ insert (dualEquiv a) (Finset.map dualEquiv.toEmbedding U)
    simpa only [Finset.map_insert, Equiv.toEmbedding_apply, hneg] using hg
  | @binary m t U a b d ha hb hab hf tail ih =>
    have hbin : ∀ a b d, dualEquiv (bin d a b) = bin (!d) (dualEquiv a) (dualEquiv b) := dual_bin
    simp only [Finset.map_insert, Equiv.toEmbedding_apply, hbin] at ih ⊢
    apply Live.binary (dual_proper ha) (dual_proper hb) (fun h => hab (dualEquiv.injective h)) _ ih
    have hg : dualEquiv.toEmbedding (bin d a b) ∉
        (insert a (insert b U)).map dualEquiv.toEmbedding := by
      intro h
      obtain ⟨c,hc,he⟩ := Finset.mem_map.mp h
      exact hf (dualEquiv.injective he ▸ hc)
    change bin (!d) (dualEquiv a) (dualEquiv b) ∉
      insert (dualEquiv a) (insert (dualEquiv b) (Finset.map dualEquiv.toEmbedding U))
    simpa only [Finset.map_insert, Equiv.toEmbedding_apply, hbin] using hg

private abbrev Sym := BitPerm × Bool

private def symMove (p : Sym) : Equiv.Perm Sig :=
  if p.2 then (permSignal p.1).trans dualEquiv else permSignal p.1

private theorem live_sym (p : Sym) {k t s} (h : Live k t s) :
    Live k t (s.map (symMove p).toEmbedding) := by
  have hp := live_permSignal p.1 h
  unfold symMove
  split
  · simpa only [Finset.map_map, Equiv.trans_toEmbedding] using live_dual hp
  · exact hp

private def checkOrbit (syms : List Sym) (reps : List SearchState)
    (c : SearchState) (key : Nat × Nat) : Bool :=
  match syms[key.1]?, reps[key.2]? with
  | some p, some r =>
    c.1 == r.1 && decide ((c.2.toFinset.map (symMove p).toEmbedding) = r.2.toFinset)
  | _, _ => false

private theorem checkOrbit_ok {syms : List Sym} {reps : List SearchState}
    {c : SearchState} {key : Nat × Nat} (h : checkOrbit syms reps c key = true) :
    ∃ (p : Sym) (r : SearchState), r ∈ reps ∧ c.1 = r.1 ∧
      c.2.toFinset.map (symMove p).toEmbedding = r.2.toFinset := by
  unfold checkOrbit at h
  split at h
  · rename_i p r hp hr
    exact ⟨p,r,List.mem_of_getElem? hr,by simpa only [Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] using h⟩
  · contradiction

private def checkOrbits (syms : List Sym) (reps : List SearchState) :
    List SearchState → List (Nat × Nat) → Bool
  | [], [] => true
  | c::cs, key::keys => checkOrbit syms reps c key && checkOrbits syms reps cs keys
  | _, _ => false

private theorem checkOrbits_ok {syms : List Sym} {reps : List SearchState}
    {cs : List SearchState} {keys : List (Nat × Nat)}
    (h : checkOrbits syms reps cs keys = true) {c : SearchState} (hc : c ∈ cs) :
    ∃ (p : Sym) (r : SearchState), r ∈ reps ∧ c.1 = r.1 ∧
      c.2.toFinset.map (symMove p).toEmbedding = r.2.toFinset := by
  induction cs generalizing keys with
  | nil => simp at hc
  | cons a cs ih =>
    cases keys with
    | nil => simp [checkOrbits] at h
    | cons key keys =>
      obtain ⟨h1,h2⟩ := Bool.and_eq_true_iff.mp h
      rcases List.mem_cons.mp hc with rfl | hc
      · exact checkOrbit_ok h1
      · exact ih h2 hc

private theorem noLive_by_cover {k t : Nat} {v : List Sig}
    (hv : v.Nodup) (hn : v ≠ [target]) (reps : List SearchState)
    (cover : ∀ c ∈ kids k (t,v), ∃ (p : Sym) (r : SearchState), r ∈ reps ∧ c.1 = r.1 ∧
      c.2.toFinset.map (symMove p).toEmbedding = r.2.toFinset)
    (excluded : ∀ r ∈ reps, ∀ j ≤ k, ¬ Live j r.1 r.2.toFinset) :
    ∀ m ≤ k+1, ¬ Live m t v.toFinset := by
  classical
  intro m hm hl
  let test : SearchState → Bool := fun c => decide (∃ l ≤ k, Live l c.1 c.2.toFinset)
  have hz : stepTest k t v (fun w => test (t-1,w)) (fun w => test (t,w)) = true :=
    reduced_step hl hm hv rfl
      (fun _ _ j hj hh => decide_eq_true ⟨j,hj,hh⟩)
      (fun _ _ j hj hh => decide_eq_true ⟨j,hj,hh⟩)
  rw [stepTest_kids] at hz
  simp only [beq_iff_eq, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, hn,
    and_false, false_or, List.any_eq_true] at hz
  obtain ⟨c,hc,ht⟩ := hz
  obtain ⟨p,r,hr,he,himage⟩ := cover c hc
  obtain ⟨l,hk,hl⟩ : ∃ l ≤ k, Live l c.1 c.2.toFinset := of_decide_eq_true ht
  have h2 := live_sym p hl
  rw [he,himage] at h2
  exact excluded r hr l hk h2

private theorem noLive_layer {k : Nat} {src dst : List SearchState}
    {syms : List Sym} {keys : List (Nat × Nat)}
    (covered : checkOrbits syms dst (src.flatMap (kids k)) keys = true)
    (hsrc : src.all (fun s => decide (s.2.Nodup ∧ s.2 ≠ [target])) = true)
    (hdst : ∀ r ∈ dst, ∀ j ≤ k, ¬ Live j r.1 r.2.toFinset) :
    ∀ r ∈ src, ∀ j ≤ k+1, ¬ Live j r.1 r.2.toFinset := by
  intro r hr
  obtain ⟨hnd, hn⟩ : r.2.Nodup ∧ r.2 ≠ [target] := of_decide_eq_true (List.all_eq_true.mp hsrc r hr)
  apply noLive_by_cover hnd hn dst _ hdst
  intro c hc
  exact checkOrbits_ok covered (List.mem_flatMap.mpr ⟨r,hr,hc⟩)

private theorem noLive_by_search {k : Nat} {src : List SearchState}
    (checked : src.all (fun r => decide r.2.Nodup && !(search k r.1 r.2)) = true) :
    ∀ r ∈ src, ∀ j ≤ k, ¬ Live j r.1 r.2.toFinset := by
  intro r hr j hj hl
  have ok := List.all_eq_true.mp checked r hr
  obtain ⟨hnd, hbad⟩ := Bool.and_eq_true_iff.mp ok
  have hgood := search_complete hl k hj r.2 (of_decide_eq_true hnd) rfl
  simp [hgood] at hbad

def rawLow : List Sig := [(0xfff00ffffffff, 0xaaa2b2b2b2b2b), (0xfffff00ffffff, 0x5555555555555), (0x333ffff0000ff, 0x3339e9e9e9e9e), (0xc3cffff00ff00, 0xc3ce6e6e6e6e6), (0xfc0ffffff0000, 0xfc0f8f8f8f8f8)]

def raw (b : Bool) : List Sig :=
  if b then rawLow.map dual else rawLow

set_option maxRecDepth 24000 in
theorem sampleCorrect : ∀ b s i, graph b (sample (raw b) s i) = s := by decide +kernel

private lemma raw_dual : ((raw true).toFinset.map dualEquiv.toEmbedding) = rawLow.toFinset := by
  decide +kernel


private def coord (p : Nat) (i : Fin bitCount) : Fin bitCount :=
  Fin.ofNat bitCount ((p >>> (6*i.val)) &&& 63)

private def makePerm (p q : Nat) (h : ∀ i, coord q (coord p i) = i)
    (h' : ∀ i, coord p (coord q i) = i) : BitPerm :=
  ⟨coord p, coord q, h, h'⟩
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private def sym0 : Sym := (makePerm 0xcf2c70beeb6caeaa689e69648e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040 0xcf2c70beeb6caeaa689e69648e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040 (by decide +kernel) (by decide +kernel), false)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private def sym1 : Sym := (makePerm 0xcf2b6caeac70beea689e69628648e07de75a65c6d83ce34a24c2c85d65524544d01c61420440c0 0xcf2b6caeac70beea689e69628648e07de75a65c6d83ce34a24c2c85d65524544d01c61420440c0 (by decide +kernel) (by decide +kernel), false)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private def sym2 : Sym := (makePerm 0xc70cf2beeb6ca68aea9e48e69628607dc6de75a6585d44d65524501c40c61420403cc2ce34a248 0xc70cf2beeb6ca68aea9e48e69628607dc6de75a6585d44d65524501c40c61420403cc2ce34a248 (by decide +kernel) (by decide +kernel), false)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private def sym3 : Sym := (makePerm 0xc70b6ca68cf2beeaea9e48e28669607dc6da65e7581c40c20461405d44d24565503cc2ca24e348 0xb6ccf2aeac70a68bee9e28669648e07da65e75c6d83ca24e34c2c81c20461440c05d24565544d0 (by decide +kernel) (by decide +kernel), false)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private def sym4 : Sym := (makePerm 0xb6ccf2aeac70a68bee9e28669648e07da65e75c6d83ca24e34c2c81c20461440c05d24565544d0 0xc70b6ca68cf2beeaea9e48e28669607dc6da65e7581c40c20461405d44d24565503cc2ca24e348 (by decide +kernel) (by decide +kernel), false)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private def sym5 : Sym := (makePerm 0xb6cc70a68cf2aeabee9e28648e69607da65c6de7581c20440c61403ca24c2ce3485d24544d6550 0xb6cc70a68cf2aeabee9e28648e69607da65c6de7581c20440c61403ca24c2ce3485d24544d6550 (by decide +kernel) (by decide +kernel), false)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private def sym6 : Sym := (makePerm 0xcb3c31bafb2daaba297dd79b7196989e59a39218a05d55935114903cd38b3092881c5183101080 0xcb3c31bafb2daaba297dd79b7196989e59a39218a05d55935114903cd38b3092881c5183101080 (by decide +kernel) (by decide +kernel), false)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private def sym7 : Sym := (makePerm 0xcb3b2daabc31bafa297dd79969b7189e59a18a39203cd38928b3085d55914935101c5181083100 0xcb3b2daabc31bafa297dd79969b7189e59a18a39203cd38928b3085d55914935101c5181083100 (by decide +kernel) (by decide +kernel), false)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private def sym8 : Sym := (makePerm 0xc31cb3bafb2da29aab7db71d7996989e39259a18a05d35155914901c31051810803cb30d389288 0xc31cb3bafb2da29aab7db71d7996989e39259a18a05d35155914901c31051810803cb30d389288 (by decide +kernel) (by decide +kernel), false)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private def sym9 : Sym := (makePerm 0xc31b2da29cb3bafaab7db71969d7989e39218a59a01c31010851805d35114955903cb30928d388 0xb2dcb3aabc31a29baf7d969d79b7189e18a59a39203c928d38b3081c10851831005d1495593510 (by decide +kernel) (by decide +kernel), false)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private def sym10 : Sym := (makePerm 0xb2dcb3aabc31a29baf7d969d79b7189e18a59a39203c928d38b3081c10851831005d1495593510 0xc31b2da29cb3bafaab7db71969d7989e39218a59a01c31010851805d35114955903cb30928d388 (by decide +kernel) (by decide +kernel), false)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private def sym11 : Sym := (makePerm 0xb2dc31a29cb3aabbaf7d969b71d7989e18a39259a01c10831051803c928b30d3885d1493515590 0xb2dc31a29cb3aabbaf7d969b71d7989e18a39259a01c10831051803c928b30d3885d1493515590 (by decide +kernel) (by decide +kernel), false)
private def syms : List Sym := [sym0, sym1, sym2, sym3, sym4, sym5, sym6, sym7, sym8, sym9, sym10, sym11]

private def roots0 : List SearchState := [(0, rawLow)]
private def frontier0_1 : List SearchState := [(0, [(0x333ffff0000ff, 0x3339e9e9e9e9e), (0xc3cffff00ff00, 0xc3ce6e6e6e6e6), (0xfc0ffffff0000, 0xfc0f8f8f8f8f8), (0xfff0000ffffff, 0x101010101), (0xfff00ffffffff, 0xaaa2b2b2b2b2b), (0xfffff00ffffff, 0x5555555555555)]),
  (0, [(0x333ffff0000ff, 0x3339e9e9e9e9e), (0xc3cffff00ff00, 0xc3ce6e6e6e6e6), (0xfc0ffffff0000, 0xfc0f8f8f8f8f8), (0xfff00ffffffff, 0xaaa2b2b2b2b2b), (0xfffff00ffffff, 0x5555555555555), (0xfffffffffffff, 0xfff7f7f7f7f7f)]),
  (0, [(0x33300ff0000ff, 0x2220a0a0a0a0a), (0x333ffff0000ff, 0x3339e9e9e9e9e), (0xc3cffff00ff00, 0xc3ce6e6e6e6e6), (0xfc0ffffff0000, 0xfc0f8f8f8f8f8), (0xfff00ffffffff, 0xaaa2b2b2b2b2b), (0xfffff00ffffff, 0x5555555555555)]),
  (0, [(0x333ffff0000ff, 0x3339e9e9e9e9e), (0xc3cffff00ff00, 0xc3ce6e6e6e6e6), (0xfc0ffffff0000, 0xfc0f8f8f8f8f8), (0xfff00ffffffff, 0xaaa2b2b2b2b2b), (0xfffff00ffffff, 0x5555555555555), (0xfffffffffffff, 0x777dfdfdfdfdf)]),
  (0, [(0x30ffff000000, 0x308686868686), (0x333ffff0000ff, 0x3339e9e9e9e9e), (0xc3cffff00ff00, 0xc3ce6e6e6e6e6), (0xfc0ffffff0000, 0xfc0f8f8f8f8f8), (0xfff00ffffffff, 0xaaa2b2b2b2b2b), (0xfffff00ffffff, 0x5555555555555)]),
  (0, [(0x333ffff0000ff, 0x3339e9e9e9e9e), (0xc3cffff00ff00, 0xc3ce6e6e6e6e6), (0xf3fffff00ffff, 0xf3ffefefefefe), (0xfc0ffffff0000, 0xfc0f8f8f8f8f8), (0xfff00ffffffff, 0xaaa2b2b2b2b2b), (0xfffff00ffffff, 0x5555555555555)])]
private def keys0_1 : List (Nat × Nat) := [(0, 0), (0, 1), (0, 2), (6, 3), (2, 2), (8, 3), (4, 2), (10, 3), (6, 2), (0, 3), (8, 2), (2, 3), (10, 2), (4, 3), (0, 4), (0, 5), (1, 4), (1, 5), (3, 4), (3, 5)]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma layer0_1 : checkOrbits syms frontier0_1 (roots0.flatMap (kids 7)) keys0_1 = true := by decide +kernel

private def roots1 : List SearchState := [(1, rawLow)]
private def frontier1_1 : List SearchState := [(0, [(0xff000000, 0xaaaaaaaaaaaaa), (0x333ffff0000ff, 0x3339e9e9e9e9e), (0xc3cffff00ff00, 0xc3ce6e6e6e6e6), (0xfc0ffffff0000, 0xfc0f8f8f8f8f8), (0xfff00ffffffff, 0xaaa2b2b2b2b2b), (0xfffff00ffffff, 0x5555555555555)]),
  (0, [(0x3f000000ffff, 0x3f0707070707), (0x333ffff0000ff, 0x3339e9e9e9e9e), (0xc3cffff00ff00, 0xc3ce6e6e6e6e6), (0xfc0ffffff0000, 0xfc0f8f8f8f8f8), (0xfff00ffffffff, 0xaaa2b2b2b2b2b), (0xfffff00ffffff, 0x5555555555555)]),
  (1, [(0x333ffff0000ff, 0x3339e9e9e9e9e), (0xc3cffff00ff00, 0xc3ce6e6e6e6e6), (0xfc0ffffff0000, 0xfc0f8f8f8f8f8), (0xfff0000ffffff, 0x101010101), (0xfff00ffffffff, 0xaaa2b2b2b2b2b), (0xfffff00ffffff, 0x5555555555555)]),
  (1, [(0x333ffff0000ff, 0x3339e9e9e9e9e), (0xc3cffff00ff00, 0xc3ce6e6e6e6e6), (0xfc0ffffff0000, 0xfc0f8f8f8f8f8), (0xfff00ffffffff, 0xaaa2b2b2b2b2b), (0xfffff00ffffff, 0x5555555555555), (0xfffffffffffff, 0xfff7f7f7f7f7f)]),
  (1, [(0x33300ff0000ff, 0x2220a0a0a0a0a), (0x333ffff0000ff, 0x3339e9e9e9e9e), (0xc3cffff00ff00, 0xc3ce6e6e6e6e6), (0xfc0ffffff0000, 0xfc0f8f8f8f8f8), (0xfff00ffffffff, 0xaaa2b2b2b2b2b), (0xfffff00ffffff, 0x5555555555555)]),
  (1, [(0x333ffff0000ff, 0x3339e9e9e9e9e), (0xc3cffff00ff00, 0xc3ce6e6e6e6e6), (0xfc0ffffff0000, 0xfc0f8f8f8f8f8), (0xfff00ffffffff, 0xaaa2b2b2b2b2b), (0xfffff00ffffff, 0x5555555555555), (0xfffffffffffff, 0x777dfdfdfdfdf)]),
  (1, [(0x30ffff000000, 0x308686868686), (0x333ffff0000ff, 0x3339e9e9e9e9e), (0xc3cffff00ff00, 0xc3ce6e6e6e6e6), (0xfc0ffffff0000, 0xfc0f8f8f8f8f8), (0xfff00ffffffff, 0xaaa2b2b2b2b2b), (0xfffff00ffffff, 0x5555555555555)]),
  (1, [(0x333ffff0000ff, 0x3339e9e9e9e9e), (0xc3cffff00ff00, 0xc3ce6e6e6e6e6), (0xf3fffff00ffff, 0xf3ffefefefefe), (0xfc0ffffff0000, 0xfc0f8f8f8f8f8), (0xfff00ffffffff, 0xaaa2b2b2b2b2b), (0xfffff00ffffff, 0x5555555555555)])]
private def keys1_1 : List (Nat × Nat) := [(6, 0), (0, 0), (3, 1), (1, 1), (0, 1), (0, 2), (0, 3), (0, 4), (6, 5), (2, 4), (8, 5), (4, 4), (10, 5), (6, 4), (0, 5), (8, 4), (2, 5), (10, 4), (4, 5), (0, 6), (0, 7), (1, 6), (1, 7), (3, 6), (3, 7)]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma layer1_1 : checkOrbits syms frontier1_1 (roots1.flatMap (kids 7)) keys1_1 = true := by decide +kernel

private def roots2 : List SearchState := [(2, rawLow)]
private def frontier2_1 : List SearchState := [(1, [(0xff000000, 0xaaaaaaaaaaaaa), (0x333ffff0000ff, 0x3339e9e9e9e9e), (0xc3cffff00ff00, 0xc3ce6e6e6e6e6), (0xfc0ffffff0000, 0xfc0f8f8f8f8f8), (0xfff00ffffffff, 0xaaa2b2b2b2b2b)]),
  (1, [(0xff000000, 0xaaaaaaaaaaaaa), (0x333ffff0000ff, 0x3339e9e9e9e9e), (0xc3cffff00ff00, 0xc3ce6e6e6e6e6), (0xfc0ffffff0000, 0xfc0f8f8f8f8f8), (0xfff00ffffffff, 0xaaa2b2b2b2b2b), (0xfffff00ffffff, 0x5555555555555)]),
  (1, [(0x3f000000ffff, 0x3f0707070707), (0x333ffff0000ff, 0x3339e9e9e9e9e), (0xc3cffff00ff00, 0xc3ce6e6e6e6e6), (0xfff00ffffffff, 0xaaa2b2b2b2b2b), (0xfffff00ffffff, 0x5555555555555)]),
  (1, [(0x3f000000ffff, 0x3f0707070707), (0x333ffff0000ff, 0x3339e9e9e9e9e), (0xc3cffff00ff00, 0xc3ce6e6e6e6e6), (0xfc0ffffff0000, 0xfc0f8f8f8f8f8), (0xfff00ffffffff, 0xaaa2b2b2b2b2b), (0xfffff00ffffff, 0x5555555555555)]),
  (2, [(0x333ffff0000ff, 0x3339e9e9e9e9e), (0xc3cffff00ff00, 0xc3ce6e6e6e6e6), (0xfc0ffffff0000, 0xfc0f8f8f8f8f8), (0xfff0000ffffff, 0x101010101), (0xfff00ffffffff, 0xaaa2b2b2b2b2b), (0xfffff00ffffff, 0x5555555555555)]),
  (2, [(0x333ffff0000ff, 0x3339e9e9e9e9e), (0xc3cffff00ff00, 0xc3ce6e6e6e6e6), (0xfc0ffffff0000, 0xfc0f8f8f8f8f8), (0xfff00ffffffff, 0xaaa2b2b2b2b2b), (0xfffff00ffffff, 0x5555555555555), (0xfffffffffffff, 0xfff7f7f7f7f7f)]),
  (2, [(0x33300ff0000ff, 0x2220a0a0a0a0a), (0x333ffff0000ff, 0x3339e9e9e9e9e), (0xc3cffff00ff00, 0xc3ce6e6e6e6e6), (0xfc0ffffff0000, 0xfc0f8f8f8f8f8), (0xfff00ffffffff, 0xaaa2b2b2b2b2b), (0xfffff00ffffff, 0x5555555555555)]),
  (2, [(0x333ffff0000ff, 0x3339e9e9e9e9e), (0xc3cffff00ff00, 0xc3ce6e6e6e6e6), (0xfc0ffffff0000, 0xfc0f8f8f8f8f8), (0xfff00ffffffff, 0xaaa2b2b2b2b2b), (0xfffff00ffffff, 0x5555555555555), (0xfffffffffffff, 0x777dfdfdfdfdf)]),
  (2, [(0x30ffff000000, 0x308686868686), (0x333ffff0000ff, 0x3339e9e9e9e9e), (0xc3cffff00ff00, 0xc3ce6e6e6e6e6), (0xfc0ffffff0000, 0xfc0f8f8f8f8f8), (0xfff00ffffffff, 0xaaa2b2b2b2b2b), (0xfffff00ffffff, 0x5555555555555)]),
  (2, [(0x333ffff0000ff, 0x3339e9e9e9e9e), (0xc3cffff00ff00, 0xc3ce6e6e6e6e6), (0xf3fffff00ffff, 0xf3ffefefefefe), (0xfc0ffffff0000, 0xfc0f8f8f8f8f8), (0xfff00ffffffff, 0xaaa2b2b2b2b2b), (0xfffff00ffffff, 0x5555555555555)])]
private def keys2_1 : List (Nat × Nat) := [(6, 0), (6, 1), (0, 0), (0, 1), (3, 2), (3, 3), (1, 2), (1, 3), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (6, 7), (2, 6), (8, 7), (4, 6), (10, 7), (6, 6), (0, 7), (8, 6), (2, 7), (10, 6), (4, 7), (0, 8), (0, 9), (1, 8), (1, 9), (3, 8), (3, 9)]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma layer2_1 : checkOrbits syms frontier2_1 (roots2.flatMap (kids 7)) keys2_1 = true := by decide +kernel

private def roots3 : List SearchState := [(3, rawLow)]
private def frontier3_1 : List SearchState := [(2, [(0xff000000, 0xaaaaaaaaaaaaa), (0x333ffff0000ff, 0x3339e9e9e9e9e), (0xc3cffff00ff00, 0xc3ce6e6e6e6e6), (0xfc0ffffff0000, 0xfc0f8f8f8f8f8), (0xfff00ffffffff, 0xaaa2b2b2b2b2b)]),
  (2, [(0xff000000, 0xaaaaaaaaaaaaa), (0x333ffff0000ff, 0x3339e9e9e9e9e), (0xc3cffff00ff00, 0xc3ce6e6e6e6e6), (0xfc0ffffff0000, 0xfc0f8f8f8f8f8), (0xfff00ffffffff, 0xaaa2b2b2b2b2b), (0xfffff00ffffff, 0x5555555555555)]),
  (2, [(0x3f000000ffff, 0x3f0707070707), (0x333ffff0000ff, 0x3339e9e9e9e9e), (0xc3cffff00ff00, 0xc3ce6e6e6e6e6), (0xfff00ffffffff, 0xaaa2b2b2b2b2b), (0xfffff00ffffff, 0x5555555555555)]),
  (2, [(0x3f000000ffff, 0x3f0707070707), (0x333ffff0000ff, 0x3339e9e9e9e9e), (0xc3cffff00ff00, 0xc3ce6e6e6e6e6), (0xfc0ffffff0000, 0xfc0f8f8f8f8f8), (0xfff00ffffffff, 0xaaa2b2b2b2b2b), (0xfffff00ffffff, 0x5555555555555)])]
private def keys3_1 : List (Nat × Nat) := [(6, 0), (6, 1), (0, 0), (0, 1), (3, 2), (3, 3), (1, 2), (1, 3), (0, 2), (0, 3)]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma layer3_1 : checkOrbits syms frontier3_1 (roots3.flatMap (kids 7)) keys3_1 = true := by decide +kernel

private def roots4 : List SearchState := [(4, rawLow)]
private def frontier4_1 : List SearchState := [(3, [(0xff000000, 0xaaaaaaaaaaaaa), (0x333ffff0000ff, 0x3339e9e9e9e9e), (0xc3cffff00ff00, 0xc3ce6e6e6e6e6), (0xfc0ffffff0000, 0xfc0f8f8f8f8f8), (0xfff00ffffffff, 0xaaa2b2b2b2b2b)]),
  (3, [(0x3f000000ffff, 0x3f0707070707), (0x333ffff0000ff, 0x3339e9e9e9e9e), (0xc3cffff00ff00, 0xc3ce6e6e6e6e6), (0xfff00ffffffff, 0xaaa2b2b2b2b2b), (0xfffff00ffffff, 0x5555555555555)])]
private def keys4_1 : List (Nat × Nat) := [(6, 0), (0, 0), (3, 1), (1, 1), (0, 1)]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma layer4_1 : checkOrbits syms frontier4_1 (roots4.flatMap (kids 7)) keys4_1 = true := by decide +kernel

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


private def wireDataPacked (i : Nat) : Nat := (if i < 24 then (if i < 12 then (if i < 6 then (if i < 3 then (if i < 1 then 0x80820202020200000000000000545505050505000000000000003c31818181818000000000000028208080808080000000000000080000000000000000000000000400000000000000000000000003f0606060606000000000000002a020202020200000000000000150404040404000000000000000800000000000000000000000000808080808000000000000000000101010101 else (if i < 2 then 0xff000000828222222222200000ff000000800a0a0a0a0a000000ff0000002228a8a8a8a8a00000ff0000002220a0a0a0a0a00000ff000000200888888888800000ff000000020828282828200000ff00000000000000000000000000000000ccc60606060600000000000000a8a28282828280000000000000888a0a0a0a0a00000000000000888202020202000000000000008802020202020 else 0xff00000000515d4d4d4d4d4000ff000000001119494949494000ff000000000108484848484000ff00000000000000000000000000ff000000aaaaaaaaaaaaa00000ff000000aaa2a2a2a2a2a00000ff000000aa8aaaaaaaaaa00000ff000000aa2aaaaaaaaaa00000ff000000a80a8a8a8a8a800000ff000000a80282828282800000ff000000a2aaaaaaaaaaa00000ff000000828a2a2a2a2a2)) else (if i < 4 then 0xc000000ff0000c010101010100300000000ff0030101010101000ffff000000ffffefefefefe000ffff000000fff7e7e7e7e7e000ffff000000fc0f8f8f8f8f8000ffff000000c3ce6e6e6e6e6000ffff0000003339e9e9e9e9e000ffff0000000008080808080000ff00000000dddf4f4f4f4f4000ff00000000555d4d4d4d4d4000ff000000005555454545454000ff00000000540d0d0d0d0d0 else (if i < 5 then 0x30ffff000000575d6d6d6d6d6030ffff0000002328e8e8e8e8e030ffff0000000308686868686030ffff0000000300606060606030ffff0000000208282828282030ffff0000000108484848484030ff00000000010040404040403000ff0000000200202020202030000000000003006060606060300000000000000000000000000f000000ffff00f010101010100c000000ff0001d0505050505 else 0x3c000000ff0003c060606060603c000000ff00028020202020203c000000ff000140404040404033ffff0000ff3339e9e9e9e9e033ffff0000ff0338686868686033ffff0000ff0328686868686033ffff0000ff031868686868603300000000ff033060606060603300000000ff022020202020203300000000ff0110404040404030ffff000000abaaeaeaeaeae030ffff000000838a6a6a6a6a6))) else (if i < 9 then (if i < 7 then 0x3f000000ffff03f060606060603f000000ffff03e070707070703f000000ffff03d070707070703f000000ffff03b070707070703f000000ffff037070707070703f000000ffff02a030303030303f000000ffff015050505050503f000000ffff000010101010103cffff00ff00c3ce6e6e6e6e603cffff00ff0003c868686868603cffff00ff00038868686868603cffff00ff000348686868686 else (if i < 8 then 0xc00000ff00000c001010101010c00000ff00000c000000000000c00000ff000008001010101010c00000ff0000040010101010103fffff00fffffffffffffffff03fffff00ffff03f878787878703fffff00ffff03f868686868603fff0000ffff57fd7d7d7d7d703f00ff00ffffabfafafafafaf03f000000ffff8bf272727272703f000000ffff03f878787878703f000000ffff03f0707070707 else 0x300ffff0000003229a9a9a9a9a300ffff0000003009898989898300ffff0000003001818181818300ff00000000100101010101030000ff0000002000808080808300000000000000000000000000ff0000ffffff0ff07070707070f0ffffff00000f087878787870c0ffffff00000c080808080800c0ff00ff00005d5d5d5d5d5d50c000ffff0000aeaababababab0c00000ff00001c11111111111)) else (if i < 10 then 0x33300ff0000ff2220a0a0a0a0a33300ff0000ff200080808080833300ff0000ff020020202020233300000000ff0000000000000330ffff0000003309e9e9e9e9e33000ff0000002200a0a0a0a0a303ffff0000ff3339e9e9e9e9e303ffff0000ff303989898989830300000000ff303181818181830300000000ff2020808080808300ffff000000baabababababa300ffff000000b80b8b8b8b8b8 else (if i < 11 then 0x333ffff0000ff1311616161616333ffff0000ff1119494949494333ffff0000ff1111414141414333ffff0000ff0308686868686333ffff0000ff0300606060606333ffff0000ff0008080808080333ff000000ff1331616161616333ff000000ff111141414141433300ff0000ffaaaaaaaaaaaaa33300ff0000ffaaa2a2a2a2a2a33300ff0000ff2330e0e0e0e0e33300ff0000ff2228a8a8a8a8a else 0x333ffff0000ff3221a1a1a1a1a333ffff0000ff3119c9c9c9c9c333ffff0000ff3111c1c1c1c1c333ffff0000ff3009898989898333ffff0000ff3001818181818333ffff0000ff2338e8e8e8e8e333ffff0000ff2328e8e8e8e8e333ffff0000ff2320e0e0e0e0e333ffff0000ff2228a8a8a8a8a333ffff0000ff2220a0a0a0a0a333ffff0000ff1339696969696333ffff0000ff1319696969696)))) else (if i < 18 then (if i < 15 then (if i < 13 then 0x333ffff0000ff3739e9e9e9e9e333ffff0000ff33f9e9e9e9e9e333ffff0000ff33b9e9e9e9e9e333ffff0000ff3379e9e9e9e9e333ffff0000ff3339e9e9e9e9e333ffff0000ff3331e1e1e1e1e333ffff0000ff3329e9e9e9e9e333ffff0000ff3321e1e1e1e1e333ffff0000ff3319e9e9e9e9e333ffff0000ff3311e1e1e1e1e333ffff0000ff3309e9e9e9e9e333ffff0000ff3229a9a9a9a9a else (if i < 14 then 0x33fffff00ffff3379e9e9e9e9e33fff0000ffff13f171717171733fff0000ffff115151515151533f00ff00ffff23f0f0f0f0f0f33f00ff00ffff22a0b0b0b0b0b333ffff0000ffffffefefefefe333ffff0000ffbbbbebebebebe333ffff0000ffbb3bebebebebe333ffff0000ffb3bbebebebebe333ffff0000ff777dedededede333ffff0000ff3f39e9e9e9e9e333ffff0000ff3b39e9e9e9e9e else 0x3c30000ff00ff3c319191919193c30000ff00ff34319191919193c30000ff00ff14111111111113c30000ff00ff00001010101013c0ffffff0000fc0f8f8f8f8f83c0ffffff00003c098989898983c00000ff00003c0181818181833fffff00ffff33f9f9f9f9f9f33fffff00ffff33f9e9e9e9e9e33fffff00ffff33b9f9f9f9f9f33fffff00ffff33b9e9e9e9e9e33fffff00ffff3379f9f9f9f9f)) else (if i < 16 then 0xc00ffff000000400c0c0c0c0c0c00ff000000004004040404040c0000ff0000008002020202020c00000000000000000000000003ff0000ffffff3ff1f1f1f1f1f3f3ffffff00ff3f39f9f9f9f9f3f3ffffff00ff3f39e9e9e9e9e3f300ffff00ff3e31b1b1b1b1b3c3ffffff00fffffffffffffff3c300ffff00ffbebbbbbbbbbbb3c30000ff00ffbcb39393939393c30000ff00ff3c39999999999 else (if i < 17 then 0xc30ffff000000c30e6e6e6e6e6c30ffff000000c20e2e2e2e2e2c0cffff00ff00c3ce6e6e6e6e6c0cffff00ff00c1ce4e4e4e4e4c0cffff00ff00c0ce0e0e0e0e0c0cff0000ff00c1ce4e4e4e4e4c0c000000ff00c0c6060606060c00ffff000000eaaeaeaeaeaeac00ffff000000e80e8e8e8e8e8c00ffff000000c28e2e2e2e2e2c00ffff000000c00e0e0e0e0e0c00ffff000000c006060606060 else 0xc3cffff00ff000308686868686c3cffff00ff000300606060606c3cffff00ff000008080808080c3cff0000ff0043c4646464646c3cff0000ff004144444444444c3c00ff00ff00aaaaaaaaaaaaac3c00ff00ff00aaa2a2a2a2a2ac3c00ff00ff0083c2626262626c3c00ff00ff00828a2a2a2a2a2c3c00ff00ff008282222222222c3c00ff00ff000200202020202c3c000000ff000000000000000))) else (if i < 21 then (if i < 19 then 0xc3cffff00ff00c006060606060c3cffff00ff0083ca6a6a6a6a6c3cffff00ff00838a6a6a6a6a6c3cffff00ff008382626262626c3cffff00ff00828a2a2a2a2a2c3cffff00ff008282222222222c3cffff00ff0043cc6c6c6c6c6c3cffff00ff00434c6c6c6c6c6c3cffff00ff004344646464646c3cffff00ff00420c2c2c2c2c2c3cffff00ff00414c4c4c4c4c4c3cffff00ff004144444444444 else (if i < 20 then 0xc3cffff00ff00c3c6666666666c3cffff00ff00c38e6e6e6e6e6c3cffff00ff00c386666666666c3cffff00ff00c34e6e6e6e6e6c3cffff00ff00c346666666666c3cffff00ff00c30e6e6e6e6e6c3cffff00ff00c28e2e2e2e2e2c3cffff00ff00c286262626262c3cffff00ff00c20e2e2e2e2e2c3cffff00ff00c14e4e4e4e4e4c3cffff00ff00c146464646464c3cffff00ff00c00e0e0e0e0e0 else 0xc3cffff00ff00ffffefefefefec3cffff00ff00ebeeeeeeeeeeec3cffff00ff00ebceeeeeeeeeec3cffff00ff00e3eeeeeeeeeeec3cffff00ff00d7df6f6f6f6f6c3cffff00ff00cfce6e6e6e6e6c3cffff00ff00cbce6e6e6e6e6c3cffff00ff00c7ce6e6e6e6e6c3cffff00ff00c3fe6e6e6e6e6c3cffff00ff00c3ee6e6e6e6e6c3cffff00ff00c3de6e6e6e6e6c3cffff00ff00c3ce6e6e6e6e6)) else (if i < 22 then 0xcc0ff00ff0000dc0f0f0f0f0f0cc00000ff0000cc06060606060c3fffff00ffffc3fe7e7e7e7e7c3fffff00ffffc3fe6e6e6e6e6c3fffff00ffffc3ee7e7e7e7e7c3fffff00ffffc3ee6e6e6e6e6c3fffff00ffffc3de7e7e7e7e7c3fffff00ffffc3de6e6e6e6e6c3fff0000ffff43f4747474747c3fff0000ffff4154545454545c3f00ff00ffff83f2727272727c3f00ff00ffff82a2323232323 else (if i < 23 then 0xcccffffffff00fffffffffffffcccff00ffff00dddf5f5f5f5f5cccff00ffff005555555555555ccc00ffffff00eeeebebebebebccc0000ffff00ccce1e1e1e1e1ccc0000ffff00ccc6161616161ccc0000ffff008882121212121ccc0000ffff004444141414141ccc0000ffff000000101010101cc0ffffff0000fc0f8f8f8f8f8cc0ffffff0000dc0f0f0f0f0f0cc0ffffff0000cc0e0e0e0e0e0 else 0xf33ffff0000ffe22eaeaeaeaeaf33ffff0000ff3339e9e9e9e9ef0f000000fffff0f7878787878f00ffff000000f00f8f8f8f8f8f00ffff000000e00e8e8e8e8e8f00ff000000005005050505050f0000ff000000a002828282828cffff00ffffffdfff7f7f7f7f7cff0000ffffffcff6767676767cfcffffffff00dfdf7f7f7f7f7cfcffffffff00cfce7e7e7e7e7cfcffffffff00cfce6e6e6e6e6))))) else (if i < 36 then (if i < 30 then (if i < 27 then (if i < 25 then 0xf3fffff00ffff0308686868686f3fff0000ffff5155454545454f3fff0000ffff4144444444444f3fff0000ffff1111414141414f3f00ff00ffffa2a2a2a2a2a2af3f00ff00ffff8282222222222f3f00ff00ffff2220a0a0a0a0af3f000000ffff0000000000000f3cffff00ff00f3cfefefefefef3cffff00ff00e3ceeeeeeeeeef3cffff00ff00c3ce6e6e6e6e6f33ffff0000fff33fefefefefe else (if i < 26 then 0xf3fffff00ffffe3eeeeeeeeeeef3fffff00ffffd3df6f6f6f6f6f3fffff00ffffc3ce6e6e6e6e6f3fffff00ffffc3c6666666666f3fffff00ffffb3bbebebebebef3fffff00ffffa3aaeaeaeaeaef3fffff00ffff9393636363636f3fffff00ffff737dededededef3fffff00ffff6364e4e4e4e4ef3fffff00ffff535d6d6d6d6d6f3fffff00ffff3339e9e9e9e9ef3fffff00ffff3331e1e1e1e1e else 0xfc00000ff00000000000000000f3fffff00fffffbffefefefefef3fffff00fffff7ffefefefefef3fffff00fffff3ffffffffffff3fffff00fffff3ffefefefefef3fffff00fffff3f7e7e7e7e7ef3fffff00fffff3efefefefefef3fffff00fffff3dfefefefefef3fffff00fffff3bfefefefefef3fffff00fffff37fefefefefef3fffff00fffff2afafafafafaf3fffff00fffff15fcfcfcfcfc)) else (if i < 28 then 0xfc0ffffff0000540d0d0d0d0d0fc0ffffff00005405050505050fc0ffffff00003009898989898fc0ffffff00003001818181818fc0ffffff00000008080808080fc0ff00ff00005405050505050fc000ffff0000aaaaaaaaaaaaafc000ffff0000aaa2a2a2a2a2afc000ffff0000a80a8a8a8a8a8fc000ffff0000a802828282828fc000ffff00002000808080808fc00000ff0000fc07878787878 else (if i < 29 then 0xfc0ffffff0000d40f0f0f0f0f0fc0ffffff0000d407070707070fc0ffffff0000c00e0e0e0e0e0fc0ffffff0000c006060606060fc0ffffff0000b80b8b8b8b8b8fc0ffffff0000b803838383838fc0ffffff0000a80a8a8a8a8a8fc0ffffff0000a802828282828fc0ffffff00007c0d8d8d8d8d8fc0ffffff0000740d8d8d8d8d8fc0ffffff00007405858585858fc0ffffff0000600c8c8c8c8c8 else 0xfc0ffffff0000fc1f8f8f8f8f8fc0ffffff0000fc0f9f9f9f9f9fc0ffffff0000fc0f8f8f8f8f8fc0ffffff0000fc07878787878fc0ffffff0000f80f8f8f8f8f8fc0ffffff0000f807878787878fc0ffffff0000f40f8f8f8f8f8fc0ffffff0000f407878787878fc0ffffff0000f00f8f8f8f8f8fc0ffffff0000e80e8e8e8e8e8fc0ffffff0000e806868686868fc0ffffff0000e00e8e8e8e8e8))) else (if i < 33 then (if i < 31 then 0xfc0ffffff0000ffffefefefefefc0ffffff0000feafafafafafafc0ffffff0000fe8fafafafafafc0ffffff0000fe2fafafafafafc0ffffff0000fd5fcfcfcfcfcfc0ffffff0000fccf8f8f8f8f8fc0ffffff0000fcaf8f8f8f8f8fc0ffffff0000fc8f8f8f8f8f8fc0ffffff0000fc5f8f8f8f8f8fc0ffffff0000fc4f8f8f8f8f8fc0ffffff0000fc3f8f8f8f8f8fc0ffffff0000fc2f8f8f8f8f8 else (if i < 32 then 0xfcffffffffffffcff8f8f8f8f8fcfff00fffffffdffdfdfdfdfdfcf00fffffffffeffbfbfbfbfbfcf0000fffffffcf7979797979fcf0000ffffffa8a2929292929fcf0000ffffff5455151515151fccffffffff00fddfdfdfdfdfdfccffffffff00fccf9f9f9f9f9fccffffffff00fccf8f8f8f8f8fc3ffffff00fffc3f9f9f9f9f9fc3ffffff00fffc3f8f8f8f8f8fc3ffffff00fffc2f8f8f8f8f8 else 0xff3ff00ff00ff5405050505050ff300ffff00ffaa22a2a2a2a2aff30000ff00ff0000000000000ff0ffffff0000ff0fefefefefeff0ffffff0000fe0fafafafafaff0ffffff0000fd0fcfcfcfcfcff0ffffff0000fc0f8f8f8f8f8ff0ffffff0000ab0aeaeaeaeaeff0ffffff0000570d6d6d6d6d6ff0ff00ff00005505454545454ff000ffff0000aa02a2a2a2a2afcffffffffffffcff9f9f9f9f9)) else (if i < 34 then 0xff3ffffff00fffe2fafafafafaff3ffffff00fffd1fcfcfcfcfcff3ffffff00fffc0f8f8f8f8f8ff3ffffff00fffc07878787878ff3ffffff00ffbb3bebebebebeff3ffffff00ffb913c3c3c3c3cff3ffffff00ff773dededededeff3ffffff00ff7625a5a5a5a5aff3ffffff00ff3339e9e9e9e9eff3ffffff00ff3331e1e1e1e1eff3ffffff00ff3009898989898ff3ff00ff00ff5515454545454 else (if i < 35 then 0xffcffffffff00d7cf6f6f6f6f6ffcffffffff00d687272727272ffcffffffff00c3ce6e6e6e6e6ffcffffffff00c3c6666666666ffcffffffff00c00e0e0e0e0e0ffcffffffff00774dededededeffcff00ffff005545454545454ffc00ffffff00aa82a2a2a2a2affc0000ffff000000000000000ff3ffffff00ffffbfefefefefeff3ffffff00ffff3fefefefefeff3ffffff00ffff37e7e7e7e7e else 0xfff0000ffffff0000101010101ffcffffffff00ffefefefefefeffcffffffff00ffcfefefefefeffcffffffff00ffc7e7e7e7e7effcffffffff00ff4fefefefefeffcffffffff00fe8fafafafafaffcffffffff00fd4fcfcfcfcfcffcffffffff00fc0f8f8f8f8f8ffcffffffff00fc07878787878ffcffffffff00f7cfefefefefeffcffffffff00ebceeeeeeeeeeffcffffffff00e946c6c6c6c6c)))) else (if i < 42 then (if i < 39 then (if i < 37 then 0xfff00ffffffff2220b0b0b0b0bfff00ffffffff2220a0a0a0a0afff00ffffffff2000909090909fff00ffffffff0200303030303fff00ffffffff0000101010101fff0000fffffffff7f7f7f7f7ffff0000ffffffccc6161616161fff0000ffffff3c31919191919fff0000ffffff03f0707070707fff0000ffffff02a0303030303fff0000ffffff0150505050505fff0000ffffff0008181818181 else (if i < 38 then 0xfff00ffffffffa802929292929fff00ffffffffa802828282828fff00ffffffffa2a2b2b2b2b2bfff00ffffffffa2a2a2a2a2a2afff00ffffffffa222b2b2b2b2bfff00ffffffffa002929292929fff00ffffffff82a2323232323fff00ffffffff8282323232323fff00ffffffff8282222222222fff00ffffffff8002121212121fff00ffffffff2a20b0b0b0b0bfff00ffffffff22a0b0b0b0b0b else 0xfff00ffffffffaea2b2b2b2b2bfff00ffffffffabf2f2f2f2f2ffff00ffffffffabe2f2f2f2f2ffff00ffffffffabb2f2f2f2f2ffff00ffffffffaaaabababababfff00ffffffffaaa2b2b2b2b2bfff00ffffffffaaa2a2a2a2a2afff00ffffffffaa82b2b2b2b2bfff00ffffffffaa82a2a2a2a2afff00ffffffffaa22b2b2b2b2bfff00ffffffffaa22a2a2a2a2afff00ffffffffaa02b2b2b2b2b)) else (if i < 40 then 0xfffff00ffffff4144545454545fffff00ffffff4144444444444fffff00ffffff4004141414141fffff00ffffff1151515151515fffff00ffffff1111515151515fffff00ffffff1111414141414fffff00ffffff1001111111111fffff00ffffff0100505050505fffff00ffffff0000101010101fff00fffffffffef7b7b7b7b7bfff00ffffffffeee6b6b6b6b6bfff00ffffffffbeb3b3b3b3b3b else (if i < 41 then 0xfffff00ffffff5555454545454fffff00ffffff5545555555555fffff00ffffff5545454545454fffff00ffffff5515555555555fffff00ffffff5515454545454fffff00ffffff5505555555555fffff00ffffff5405151515151fffff00ffffff5405050505050fffff00ffffff5155555555555fffff00ffffff5155454545454fffff00ffffff5005151515151fffff00ffffff4154545454545 else 0xfffffffffffff3009999999999fffffffffffff0308787878787fffff00fffffffdf7d7d7d7d7dfffff00ffffffdddf5f5f5f5f5fffff00ffffffddd7575757575fffff00ffffff7d75d5d5d5d5dfffff00ffffff5d55555555555fffff00ffffff57f5757575757fffff00ffffff57d5757575757fffff00ffffff5775757575757fffff00ffffff555d5d5d5d5d5fffff00ffffff5555555555555))) else (if i < 45 then (if i < 43 then 0xfffffffffffff7775f5f5f5f5ffffffffffffff762dbdbdbdbdbfffffffffffff755ddddddddddfffffffffffff7555d5d5d5d5dfffffffffffff636cfcfcfcfcffffffffffffff575d7d7d7d7d7fffffffffffff5755757575757fffffffffffff555d5d5d5d5d5fffffffffffff5555555555555fffffffffffff3339f9f9f9f9ffffffffffffff3339e9e9e9e9efffffffffffff3331f1f1f1f1f else (if i < 44 then 0xfffffffffffffbbbbebebebebefffffffffffffbbb3f3f3f3f3ffffffffffffffbaabbbbbbbbbbfffffffffffffbaa3b3b3b3b3bfffffffffffffabaafafafafaffffffffffffffaba2f2f2f2f2ffffffffffffffaaaabababababfffffffffffffaaa2b2b2b2b2bfffffffffffff7f7dfdfdfdfdffffffffffffff77fdfdfdfdfdffffffffffffff777dfdfdfdfdffffffffffffff777dedededede else 0xfffffffffffffe3eefefefefeffffffffffffffd7ff7f7f7f7f7fffffffffffffd7df7f7f7f7f7fffffffffffffd7df6f6f6f6f6fffffffffffffd7d7777777777fffffffffffffd557575757575fffffffffffffc3ce7e7e7e7e7fffffffffffffc3ce6e6e6e6e6fffffffffffffc3c6767676767fffffffffffffc00e1e1e1e1e1fffffffffffffbbfbfbfbfbfbffffffffffffffbbbbfbfbfbfbf)) else (if i < 47 then (if i < 46 then 0xffffffffffffffaafbfbfbfbfbffffffffffffff7fffffffffffffffffffffffff7ffefefefefeffffffffffffff7f7f7f7f7f7fffffffffffffff77ffffffffffffffffffffffff55fdfdfdfdfdffffffffffffff3ffffffffffffffffffffffffebfefefefefeffffffffffffffebeefefefefeffffffffffffffebeeeeeeeeeeefffffffffffffebe6f6f6f6f6ffffffffffffffeaa6b6b6b6b6b else 0xffffffffffffffeafafafafafaffffffffffffffea7b7b7b7b7bffffffffffffffe2fbfbfbfbfbffffffffffffffd5fdfdfdfdfdffffffffffffffd5fcfcfcfcfcffffffffffffffd57d7d7d7d7dffffffffffffffc0f9f9f9f9f9ffffffffffffffc0f8f8f8f8f8ffffffffffffffc07979797979ffffffffffffffbfffffffffffffffffffffffffbffefefefefeffffffffffffffbf7f7f7f7f7f) else (if i < 48 then 0xfffffffffffffffdfefefefefefffffffffffffffd7f7f7f7f7ffffffffffffffffcfffffffffffffffffffffffffbfefefefefefffffffffffffffb7f7f7f7f7ffffffffffffffffafffffffffffffffffffffffff7fffffffffffffffffffffffff7fefefefefefffffffffffffff77f7f7f7f7ffffffffffffffff5fffffffffffffffffffffffff3ffffffffffffffffffffffffeafbfbfbfbfb else 0xfffffffffffffffffefefefefeffffffffffffffff7f7f7f7f7ffffffffffffffffefefefefefefffffffffffffffe7f7f7f7f7f))))))

private def wireData (i : Nat) : Nat := unpack wireDataPacked 104 12 i

private def readSig (i : Nat) : Sig :=
  let a := wireData i
  (BitVec.ofNat 52 (a >>> 52), BitVec.ofNat 52 a)

private def sigHash (s : Sig) : Nat :=
  let h := (s.1.toNat * 0x517cc1b727220a95) ^^^ (s.2.toNat * 0x9e3779b97f4a7c15)
  let g := (h ^^^ (h >>> 57)) * 0xbf58476d1ce4e5b9
  (g ^^^ (g >>> 49)) &&& 0xffffffffffffffff

private def stateHash (s : SearchState) : Nat :=
  s.2.foldl (fun acc x => acc + sigHash x) (s.1 * 0x94d049bb133111eb)


private def decodeWires (code : Nat) : Nat → List Sig
  | 0 => []
  | n+1 => readSig (code &&& 1023) :: decodeWires (code >>> 10) n


private def st2Packed (i : Nat) : Nat := (if i < 1 then 0x7b1bf0a0c3d8e205061ec7342830f63146a987a5ce0a0c3d8ce0fc61ce630d530f5b9c14187adcd0a0c3c8e705061ec7182830f639214187b1ba0a0c3bce705061ec72c2830ed39c1418789ce0a0c3d8a5a4e61ce52d2a30f3b9c1418 else 0xe733a3f18)

private def st2 (i : Nat) : Nat := unpack st2Packed 37 20 i

private def adj2Packed (_i : Nat) : Nat := 0x40181203

private def adj2 (i : Nat) : Nat := unpack adj2Packed 3 80 i

private def loc2Packed (_i : Nat) : Nat := 0x1401e4944c0100e0281207000d000730028b001808000a

private def loc2 (i : Nat) : Nat := unpack loc2Packed 5 80 i

private def st3Packed (i : Nat) : Nat := (if i < 6 then (if i < 3 then (if i < 1 then 0x7394f4a83940ed39cb287281ec735650e503d8e735a3f20879ec7382840fcbd8e718281af594ef241035eb29ac4ba07b1cd4fc2840f4b9cb287281ec710f01a903d6e69e03520001ec7342832d7aca7790681af590f0259044af639c1420001eb7382832fb3d8b2a4e81af530f0259035eb29bc4ba0 else (if i < 2 then 0x7b1ba5943940f639a608d481d7518f025d035eb29c24b206dd4a3c09740d7ac87810081af568f020d039cce8f814207b1c95943940f5b9c608d481eb738f01a903c4e71e03520791ce3c06a40f638c780d481eb738c125d03b2a31e03ba07b1cd3042840f63886092e81eb734c125d03c8e71824ba0 else 0x6bd6538c9740f638cb287281eb738c10e503d8e69e014206bd653bc9640f639a4b85081eb738970a1035ea89b64ba07b18a3382840f3b9cb287281ce630d30a10470f639c14207b1cd66428410c3d8e705081b7594f01f103d8dfaca1ca06bd4e3c09740f639ad685081eb739ad0a10408f639c1420)) else (if i < 4 then 0x779ce5943940f639cbf87281af594e823d03d8a324e14208a5ec7382840f139cb287281ce5292a0a103d6e72ca1ca07b1c45943940f639ce685082437adce0a103d6e727e14207adce594284117bd8e705081ec7351c0e503d6e72381ca07b15549c3940ec2ca9387281eb739990a10370b2a541ca0 else (if i < 5 then 0x6bd653809740d7aba7811081e9738c125d035eb21c24ba06bd6439897411fbd8e705081af5953425d035eb29e044206bd653a49640d7ac87492e81ec739654ad036eb29a64ba07b1cd3043940d7aca7812c81eb738390a103d2e71e035206bd653c08d40d7abc7812c81af590f02250486f639a1420 else 0x7b1ce67c974107bd8e705081af594d825d035eb21e042207b1ce664d540f139c6092e80007adce0a0c35eb29c84b206bd943c0974119bd8e705081af548ef25d03d8ce0ee14207616533877411e3d8e705081af594d725903d8e69e035207b1cd1a83940f628c6f8ee81af590e425d0482f639c1420))) else (if i < 9 then (if i < 7 then 0x6bd593c09640d7ac87792c81af594e6259035eb21c64ba06bd653bc8840d7ac86e12e81af558f0259035ea69de4ba06bd643bc9740f5b9c3507281af5913f0e503d8e735040207adce3c02840d7aca9a92c81af648f01a903d8e729a9aa075d653c07740f639cc69e081af6b4c025d03d8aa99c3ba0 else (if i < 8 then 0x6bd643c08d40d7aca7810281ec7396516503d8e687214206bd6536c9640f5b9c6085081ec718c125d03d8e732a6ba06bd903c06a40d7ac89a92e81af590f023d0486f639c14206bd643a09740d7aca7812481af594ef1fd035eb29de47206bd643c08e40d7aca9787281af594db25d035eb29ac4b20 else 0x6bd5a3bc9740d7b42b292c82127399d25d035eaf1de4ba075d653389740d7ac87812e81af594ef21103eee731878207b1ce6848c40d7aca9887281ec7393f18d035ec72ca78206bd643c08c40d7aca7811681af594ef231035eb29e043206bd573c09640d7aca7812881af574ef25d035ea89e04ba0)) else (if i < 11 then (if i < 10 then 0x6bda23049740d7b486092e81af594e525d035eb29e03fa06bd5b3c09640d7b507792e81f77b18a3c1035eb21ae4ba07b1ce5652d40d7aca961e081af69cf025d03d8f5b9c14206bda83c09640d7aca7811e81af590e525d035eb29de40206bd583c09740d7b1eb21e081af590f022d0370b29a63e20 else 0x6bd8f594ef40003d8e685061af564ef25d035eb29ca46a07b1cb5943940d7ab67792e81af594e825d035eca9e04b206bd653bc9740d7aca9f07281af6b0c125d035ed0ac84ba07394f34c7c40d7aa47812c81af560ef25d03d8e6aca14206bd653809640d7b32780d281af6b4c1259035eb29b84b20) else (if i < 12 then 0x851ec7386a40d7b2a7792e81af558e025d035eab1e04ba06bd653ac9740f639a3505081af590f024103d8e69824ba06bd513c09640d7aca7692e81af5912d3c1035eb29de44a06bda05949740f639cc79c882127b19c25d035eae9e04ba06bd4d3c09640d7a987812e81af5952d3bd035ecc1e03520 else 0x1af664ef1a903d6e70d414206bd5a3c09740d7ac47812e81f6739654a90458f639c1ca0791ce5943940d7aca9f87081af594f020d03d8e72969fa06bd603c09740f5b9ab287281af55cef25d035eaa1e04ba0))))

private def st3 (i : Nat) : Nat := unpack st3Packed 47 20 i

private def adj3Packed (i : Nat) : Nat := (if i < 1 then 0x28003084436040062043101c410c600086101c022080188020380640000000001004040d80211028204c100c050184008800 else 0x2484e808080)

private def adj3 (i : Nat) : Nat := unpack adj3Packed 5 80 i

private def loc3Packed (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0x2b008237d9de0000007fa2004d590000844cc3f32d6e791304691900423cb0f463c667003f0000000ec53502b3d600003818af5d72ced700b8dde2b9f7000197004b179b50ed3900e17060bc480000 else 0x86fc1f001500005f470000626f564f00952af9d8ad746c009e000032005443bf004671000b3300307a0000856436d3ea000000f508fbdfae00006b2900d40000007b00e826008c99a9b152ab44e51151) else (if i < 3 then 0x1b000f4958b70073254eeb000040f600211200e606d57e006d00f000b6008b00783400759a2e0000c700db8307003d280057008900000000ef81a827000000fa66cd009100ccca0000006100090000a1 else (if i < 4 then 0x8a870088a45abbb5f85c1d0000a500005b7d005e000c056aec00001c3b0016ac00771e00c13e9c4adc0045ee0a239f000000000041a09300d1c2000000002200b200c89000c400d0539de000c9e9cf55 else 0xaa80a67600000000921a00ba24140000e38f00f1963a20b40094fde400d27ccb10680000038e000dc00000a70065e72ca331f28d000000980000be00bdda2f)))

private def loc3 (i : Nat) : Nat := unpack loc3Packed 8 80 i

private def st4Packed (i : Nat) : Nat := (if i < 26 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then 0x7b1ce5951425d4000f639a780d484007adce3c06a42003d8e69824ba1001eb738c125d0b5ea51e05e92ea1ec739653c09b50f639cb29e84ba87b1ce594da25d439cd7a947312ea1ec71d653909750f639cb51e04ba87b1ca548f025d43d8e72ca7892ea1ec7396549c285000486f639c1420001af5910e3c10800b29de4b85a84006bd6543cf042003d8e72ca8ea1 else (if i < 2 then 0x7b1ce5b0f525d43d8e72ca7092ea1ec6ed6c3c097500035ead1e04ba17b1ce594f027143d8e72ca78132a2426bd653909750f639cbb92e1ca87b1ce420f025d43d8e72caa0872a1ec739643c09650f639cba9e04ba87b1ce594f01c143d8e72ca9f8c8a1e2739653c09750f639cb2a6e14287b1ce53cdc25d43d8e72c27812ea1ec7393f4209750f639ca79e03e28 else 0x6bdad590f025d43ecf639cb2a7ea1ed739643c09750d7aca9f9de4ba8001653c0970b10bd8e72ca7912ea1af590f025c1f50f639cba1e04ba8875af594f022143d8e72ca6b8e8a1ec739653a097500035eb21e04ba07b1ce594e02594486f639c6092ea1ec71d654fc3950f639cb29ea4ba87b1ce5b0f025d43e6ddaca7812ea1af5953e3c09750d7aca6712e1aa8)) else (if i < 4 then 0x7b1ce3c0af25d43d8d7aca7292ea1ec739693c097500035eb29e041a1001af574f025d0b5eb29de5a12ea1ec7396525c4b50f639cb29e64ba8001af594e825d0b5eb29e04b002a1af594ef25c015121360b29e04ba86bd6543cf02594000d7ac87812c85fe7396534c7c50d7ac87812e2aa87b1ce594f02e5435eb29e06712ca1ec739653c098500035eb29e04421 else (if i < 5 then 0x6bd643c097005435eb2a1c7812ca1ec739ad3909750d7aca7812e44286bd65438ef25d435eb221c7812ea1ec6bd653c08850d7aca781664b286bd653bcb325d435eb21e05992ea0007b1cd5943942d7aca7792e16a86bd653c0970b143cae72ca78118a1af594ef25c2650f639cb299c21a86bd643c09709943d8e72147812ea1ec7396e3c09750f639cb29e038a8 else 0x739af56cd325d43c0e72ca7812ea1ec739653709750f639cb29a621a87b1ce594f029d435eb29e069910a1ec73965414ab50f5b9c9f9e03528861ec739650e543d8e72ca78088a1df739653c09650e3a947812e2a286bd653bc97151435eb21e04b8a8a1db6ed653c097500035eb29de4ba1761ce594f025d439cd7aca78106a1ec7396525c4850f639cb29e020a8))) else (if i < 9 then (if i < 7 then 0x7b1ce595041a943d8e7332b2894a1ec739654089750f639cb28f82528771ce594f025d43d8e735ab2886a1ec739654009750f639cb2a0821a877dce594ef25d4000d7aca7812c8400590f025c2d42f639cb2a0856287b1ce594ab1294432d7aca7792ea1ec739653a497510abd8e72ca96a88a5ec738c125d435ea31e05f12ea1ec735653c06a50f639cab9e03ba8 else (if i < 8 then 0x1eb739650e50bd8e72ca7d108a1ec7395b3e89750d7aca7812c0fa87b1ce5c8e625d43d8e3ae47812ea2406bd653c09750f2a8c7812e2a287b1ce549333c1435eb29de4b83ea1ce6bd523c07c50f639eb29e04b28001af594e025d0452f639c780d4a1ec739654fc5a50f639cb28a61ca87b1ce594f010d43d8e72ca55872a1ec739653c08a50f639cb29e055a8 else 0x6bd513c0971dd4000d82ca7812e85ec6ed653a49750f6388b29e04ba8785ce594f025d43d8e6a387812ea1eb7391c3c09750f639cb29e048a87b1bb594e125d43d6e6aca7812ea1e3739633c09750f639cb29904ba87b1ce588f025d43d8d7b14780d4a1ec7399a3c06a50f639cd412e1ca87b1ce594dc28543d8ddaca78142a1ec739953c06a50f639eb21e04ba8)) else (if i < 11 then (if i < 10 then 0x87daf590f025d43d8e732678050a1ec519273049750e7294951824ba8895ec738c125d4000f639a6092e82437b1cd3049750f639ce69824ba87adce4fcc125d4448d7aca7812ea1ec735653049750f5b9cb29824ba88cdec738c125d43e0e3aca7812ea22f7b1ce3049750e735eb29a640287b1cd3c0c125d4484d7b5a6092ea1ec739655083950f1b9cb2a7e1ca8 else 0x7b1ce5951d0e54000d7aac7812e81fc7394a3c09750f6370b29e0422890dec738f01a9435eb21e04b872a2437b1ce1a82850f639cd192e14287b1cd3c0971a943d8a324e780d4a1ce5292a3c06a50f639ce69e0352890deb738f01a943d6e72ca780d4a2337b1ce3c06a50f5b9c7812e35287b1ce424f025d43d8e72c67812ea1ec7399c25c2850f639cab9c23ba8) else (if i < 12 then 0x7b1c6594f025d43d8e72ca78126a1ec739654e83950f6390b29e04ba875dce594f025d43d8dbaca7812ea1af594ef25c38500035eb29de4b217b1ce590f025d43d8e72e47811ca1ec7adce3c06a50f6b9cb29e04b287b1ce594e122543d8ddb32780d4a1ec739553c08950ec39cb29e044a87b1ce554e125d4486f639cb2872a22f7b1ce3c06a50f639ca31e04828 else 0x7b1ce594df25d43d8e72aa6712ea1d873965338975121bd8e69e035287b1ce6a4970a143f8e72ca6992ea1ec705653c09750f639ca79a64ba87b1b8594d325d43d8ddaca999e0a1ec739954d49750f639cd41c84ba87b1c5548f025d43d8e72aa7812ea1eb739995943950f639cb29dc4ba87b1ce56cdc25d43d8e72ca78134a1ec739463c08c50f6376c7aca7828)))) else (if i < 19 then (if i < 16 then (if i < 14 then 0x77dbb594f025d439cc62ca69872a1ec7359959439510f3d8e72ca1ca87b1c7594dc25d439cceaca3e072a1ec739654c43950f639cb29b83e287b1ce5952a0e5435eb21e04b8d4a1ec739963c02850f6376c9aca78287f1ce594f01f1441ef639cb2872a1af594f02582d5121bd8e735a14287b1cd6b5650e54464d7aca7812ea2387b1ce5943950f639cd512e1428 else (if i < 15 then 0x6bd654fcf025943d6e72ca78072a2437b1ce1a83950f639caba7e1ca86bd5d3c0d325d43b6e72ca9f872a1ec739654cc395121bd8e712e14287adce594970e543d8e72b69f872a1ec739ad6642850f639ccc99c14287b1c7590f025d43d8e6a7e780d4a1ec6296533839511e3d8e72ca1ca8795d2594f025d43d8e72ce7812ea1ec7399934c2850f6380b29a64ba8 else 0x7b1c7548f025d43d8e72ca99072a2426bd643c09750f639cb1a7e1ca87b1ce53d3f0e54000f5b9c6092e81ec6e1654fc3950ff39cb2a541ca86bd643c0cc25d43d8e72ca97072a22f7b1ce5943950f639cb0a7e1ca87b1c55953f0e543d8e72ca99850a2437b1ce3043950d7aca7812c132877dce5953f0e543d8e02ca9f872a1ec739654d83950f6370b29b84ba8)) else (if i < 17 then 0x7b5ce594ef25d43d8e72ca95050a2437b1ce0e42850f639ca527e1428001ec735650e50486f639ab2872a1d8739653c07750f639ce6aca1ca8001eb739650e503d8ddaa46e12ea1af5954a3bc9750f63d6e72ca1ca8001af590ef25d0bd8e6aca9f872a1eb739654fc3950e735ea69e03e287b1ce5553f0e543d8e72c86e12ea1ec739653c08c50ec39cb2a7e1ca8 else (if i < 18 then 0x7b1ca594ec25d43d8ce1824b8eea1ec6ed653b09750f6376b2a5a7828001af594f02350bd8ddaca7392ea1ec739533c09750f639cae1e04ba87b1ce594e725d43b6e72ca6e12ea0006bd653809742f639ca327e14287b1ce595040e543d8b2a8c93872a2297b1ce5943950f2b9cb2a7e1ca8895ec739650e543d8e72ca9f86ca2437b1ce59428500035e7812e2aa1 else 0x7b1ce5953c0e543d8e72a47312ea1ec7394d3c07750f5b9c781824ba87b1bb584f025d43d8dc29e7812ea1ec739654fc4a50f639ca91e048287b1ce63d523c143d8ddaca78120a1ec739523a49750f6376b29e047287b1bb594e625d43d8e3aca7812ca2426bd653c08950f639ca89e04b286edaf594f01f143d8e72a47612ea1ec739643c08f50f639eb29de4ba8))) else (if i < 22 then (if i < 20 then 0x7b1ce548f021143d8e6a7e6092ea1af594db25c7750f6376b29e042287b1ce53cf025d4406d7aca7812ca1ec739a163d6550f639ca91b84ba87b1ce580f025d435ec92ca7812ea1ec73993594dc50f639cb29e047a87b1af574f025d43d8e73565f92ea1ec739654d82850f638ab29b84ba87b1ce5944a10143d8e72c26e12ea23f7b1ce5943950f6380b29f44ba8 else (if i < 21 then 0x811ec739650e5441cd7aca7012ea1ec6ed523c07c50f639cb59e04ba87b1ce50ce425d43d8e72ae6e12ea1ec739573bc975105bd8b299c3ba87b1ce6b4bf25d43d8e731eb29e0a1ec739a83049750f639cb2a666e286bd653bc971a943d8e72ca6e112a1ec6ed5e3c09750f4b9cb29e04ba8795ce594f025d43d8e72a07812ea1ec739653749750f639cb29b84228 else 0x841af594f02594414d7aca7812ea1ec739643a09750f639ca927e1ca87b1ce66cc125d43d8e72b47792ea1ec739993706a50f639cc89e035287b1ce558f025943d8d7a9a780eea1ce6bd653707c50f639cc51e0352877dce594ce25d43d8e72a46e0f8a1ec6ed573c09750d7ac87812e34a86bd643c0971f143b6e72a47812ea1ec739523c08950f6380b2a6e4ba8)) else (if i < 24 then (if i < 23 then 0x7b1ce594e625943d8ddaca9f872a2087b1653c097500035ea89e04ba17b1ce595390e54476d7aca7812ea1ec739654c03950f639ccb9cc4ba8835ec518f01dd43d8e3b2e7812ea1af5954a3a09750f639cb29d84ba87b1c0594ef25d435ecc2ca7812ea1ec6ed6536c9750f638ab29e04ba86bd463c07c1a9439cd7aca95072a1ec6ed5b3c09750f5b9cd6aca1ca8 else 0x761ce594e125d435ea519c6092ea1ec6bd653bc9650edb5eb29e03ba87b1c0548f025d43d8e729a6b92ea1ec739653c09650f639cab1e03ba87b1af578ce25d4000d7aca7792c81ec739513c07c5120bd8e71824ba8909af6856525d43f6e72ca7812ea1ec739653c09550f635eb29d04ba87b1ce578f025d43d8e72ca9b908a1ec7395b4dc9750f239cb29e04ba8) else (if i < 25 then 0x7b1ce5952f0e543d8ddaca7a92ea1ce6bd653bc9750f639ccb9e014287b1ce594f021d4486f639c78050a21c6bd653c0975121bd8e727e14287b1ce554f01dd43d8e72ca9b872a0006bd653c08d4120bd8e71e035288adaf590f025d4466f639cb2872a2097b1653c07750f639cd0aca4ba87b1ce594df1dd43b2e72ca780eea1ec7395e4fc3950f639ccb9e03528 else 0x7b1ce590f024143bee72a47812ea1ce6bd9d3049750f639cb21cc4ba87e5ec739653c14460d7aca7792ea1ec7395136c9750f6386b29e04ba87b1ce590e525d43d8e72ca6d92ea1ec7394b3c09750f639cb29b04ba87b1ce564cc25d43d8ce2ca3b872a1ec739653c08550f639cb29c23ba86bd65590ef25d43d8f5b9c6092ea1ec739653388950f639cc61e01428))))) else (if i < 39 then (if i < 32 then (if i < 29 then (if i < 27 then 0x7b1ce5951e3c14484d7aca78118a1ec7395e3bc9750efb9cb21e04ba87b1ce574f025d435eab1e04b8f8a1ec701643c09750f639ab29e04ba87b1ce4fcf02b9441cd7aac7812ea1ec739653bc9050f639caca7e4ba87b1ce5953f0dd43d8e72c87792ea1ec7395d3bc9750f635eb299c40287b1ce594ef20d43d8e72b67792ea1ec7396534c8450f639cb2a701ca8 else (if i < 28 then 0x795ce594f02594000d79e04b0a885ec7395b3c09650f6380b29e04ba88b1ec738f025d435eb29e03b86aa1ec739653c08d50f639cce92e14287b1ce594771294468d7ac87812ea1ec739643c08d500035eb29664b217b1ce6b4c025d4000d7ac85992e85ec739ac3049750f639cd69824ba87b1ce594dc25943d8e72ca7791ca1ec739653bc8950f639cb21e044a8 else 0x7b1ce660f01a943d8e72ca780fca0006bd563c09742f639cab9e04b2876dce594f025943d8e72ca7012ea1db739653bc9750f639cb21c24ba876dce590f025d43d8e72ca78110a1ec739523bc9750f6376b29de4ba890deb738c125d435eb29de4b8f8a0007b1cd3c06a40f6376b21e04ba876dce594e11dd43d8ddaa47812ea1ec701653c09650f639cb29e041a8)) else (if i < 30 then 0x7b1ce590e925d43d8d7aca7012ea1ec7396511c4350f639ca71e04ba86bd6534cbd25d43d8e7326a91e0a1ec7395e3c09650f639cb2a7e1c287b1ce5953e0e543d8e7332780d4a1ec739654fc3950f639cb29e04ba8859af594f025d439cd7ac87792ea2426bd654d49750f639cb29de4ba87b1ce558f025d439cd7ac87812ca1af594ce1f03950f635eb21e04ba8 else (if i < 31 then 0x909af590ef25d435eb21e07792ea1ec739ad1f02850edaca871e03ba87b1ce590f0239435ed22ca7812ea1ec739523649750f635eb21e04b287b1ce5dcf025d435eb29de6012ea1ec6bd643bc9750efb9cb29b84ba8739af594ef259435eb2a627812ea1e5739653709750e72caa52541ca87b1ce5952d30543d8e72ca6d92ca2097b16533897511935eb29e047a8 else 0x7b1af518e425d43d8e3aca7812ea1df739653c08050d7aca7812c1c28739af528e425d439cd7aca6d92ea1ec739884fc2850d7aca7812c34a8909af594ef259435eb29e07792ca0006bd643c096410fb5eb29e04b286bd65590f0259435eb21e04b92ca1ec739654fc285109b5eb29de4ba8909af594f025943d8e735c6092ea1e56ed653c097500035eb21de4ba0))) else (if i < 35 then (if i < 33 then 0x909af594e625d439cd7aca7811ea1ce6bd653a09750f639cb29c84628739af528f023943d8d7aca93872a1ce6bd653c09650f639cb29b84728001af5950e3bd0b5eb2a947812ca2056bd653c09650f639ca69e04ba8909af594f02394000d7ac87812e85dd739653c097500035eb29e047a18c1af594f02594000d7aca5a12e85ec739523c096511835eb21e04ba8 else (if i < 34 then 0x909af594e925d43d8e72ca7312ea2346bd653bc9750d7acaa31e046a87b1ce5953f10d43d8e72ca78084a0006bd653c08f40f6376a89e04ba8001af594e825d03d8d7aac7812ea2326bd653a09750f339cb29e04ba8795ce548f025d435eb21e06992ea1af594f03a097511935eb21e04ba87b1ce5952d3c143cae72ca7792ea1af5954a3c08f510cb5eb29e04b28 else 0x7b1ce5a0f025d4000d79de4b8a886176bd653bc9750d7aca779984ba87b1bb594d725d435eb2ac87812ea1ec739a84b4f050f639cac9e04ba87b1c7594f0231435eccac87812ea2346bd653c09650f639cb2a521ca86bd653c0972354416f62ca93872a1ec6bd463a49750f639c7815c4ba86bd65518f025943fad7aca7812ea1ec6bd6536c9750efb5eb299c4ba8)) else (if i < 37 then (if i < 36 then 0x739af528f0231439cd7aca78110a2426bd643c09650edb9cb29e04ba87e1af594f025943d8e731478050a1db739653c07750d7aca7812c2a287b1af518f0241435eccaca7812ca1ec739ad1dc285116b5eb29de4ba87b1ce694970a14456d7aca7812ea1ce6bd6535c7c50f639cb2a761ca88ddaf594f025d43d6e72ca7812ea22e6bd653c09750f639cb2a501ca8 else 0x7b1ce578dc25d435ed6aca7792ea1ec739463909750d7acaa31de4ba87b1bd594f025d43d8e72947212ea1af6b5653c09650f638eb29de4ba8795ce518f025d43d8e732278050a2426bd653c08051093d8e735a4ba87b1ce594ef221439cd7aca7292ea1ec739653c09050f635eb29c23ba87b1ce664ef1a943d8e72ca7811ca1ec6edad3049750f635ea31e04628) else (if i < 38 then 0x76dce55cf01dd435eb29e04b072a1ec7394d4fcf050f639c7815c3ba87b1b9548f025d445ad7ac87812ea2426bd5b3c09750003d8e72ca32217b1ce594d71dd43cae72c87812ea1d8739553c09750f6378b29e04ba87b1ce594db1f1445cd7ac87812ea2426bd8f594f050f639cad9e04ba88b5ec739a125d43d8e728678118a2286bd653c097511735eb29ca4ba8 else 0x7b1ce6b4c1259439cd7ab47812ea1af5914a3c09750d7aca781de4ba8909af578f025d43d8e52ca6e12ea0006bd653c08840f2b5ea31e04ba8875af574f025d43d8e731e78182a1af5955d3c09750e735eae9e04ba8001af594ef25d045ad7aca7812ca2426bd653c08450f639caf9e04ba877dc0594f025d435eb29e07292ea2437adce5943950f635ea89e04ba8)))) else (if i < 46 then (if i < 42 then (if i < 40 then 0x7b1ce594f625d435ea31a66092ea1af5952f3c09750d7aca7812c35286bd6450cf025d43d8d7aca7811ea0006bd5a3c097410bb5ead1e04ba885daf594f025d435eb29e067106a1af568f03389750f639ccc9e046287b1af594f020d4484d7b2a7812ea2156bd653c09650e735eb29a642287b1af594ce225440ad7ac87812ea1af590f03389750d7aca7812e34a8 else (if i < 41 then 0x7b1ce548f525d435eb29e06d92ea1ec6bd593389750d7acaad1e04ba890dec7391c0e54380d7aca6992ea2156bd653bc97500035eb29b64ba0855af590f025d435eb2a8c7292ea1ec739953c03950f639cb2a6a352884daf594f025d43d8e72ca7492ca21d6bd653c09750d7aca7799c4ba8739af594e025d443ed7aca7792ea1af594ce2f897512135ed41e04ba8 else 0x909af594f0241435eb29e06992ca1ec7396534c80500035eb29e041a07b1af594f025943d8e72b26712ea1ec7395934c9750f639cb299840287b1c0564f025d435eb21e04b85aa1ec6bd653bc9750f639cb29e044a87e9af590f025d43bee72ca7812ea1ec739593c08050f639cca9e046287b1ce594f021143d8ddaca7812ca1ec739653bc9650d7b44b29e04ba8)) else (if i < 44 then (if i < 43 then 0x7b1ce53cf021143d8e02ca78100a1ec731653c09750d7a94780ee35287b1bb570f025d4000d7aca6d92e8400594f02582d42f539cb29e04ba87b1ce698bf25d435ea31e04b8d0a1f86bd653c09750d7b58b29e04ba88f9af594f025d439cd7aca7811aa1ec7396d3c09750d7ac8781804ba8909af5952d3c143d8e72ca77908a2196bd643c09750f639cb299c4028 else 0x7b1ce594dc241440ad7aca7792ea2417b1ce5943950f639cb29d44ba8875af594ef25d43d8e72a47812ea1ce6bd5934c9750f639cc81e035286bd653c0c125943d8e72ca6a92ea1af594ef3049750f639cb292e25286bd643c0c125d43eef639ccc9e0a1ec739573c09750d7aca781804ba8909af594ef25d43d8e735ab2900a1ec739ad5649750f639cd69e04628) else (if i < 45 then 0x7b1bb594dc25d4484d7aca6e12ea1ec739653c08050e735ec61e035286bd653bcd325d435eb29e04b906a2426bd593c09750f639cb2a4e1ca86bd653c0961dd43d8e729a780e8a1ec739643bc9650f639cb298e4ba87a1ce594f025d4484d7aca7812ea1e5739653909750f639cc49e035287b1ce6b4970a143d8e7332b29aea1ec7396538077500035eb29e04b20 else 0x6bd65544f025d43d8d7aae780eea1ec739654109750e3b5ea51e04ba8909af55cf025d441cd7aca7812ea1ec7396539097510835eb21e04ba87b1bb594dc1f143d8e72ca98050a1af594e025c7c50e735eab1e04ba87b1ce6b53f0a1445cd7aca7811aa1ec739543c09750f639ca89e04ba8002437b1ce0a10bd8ddaca78112a22d7b1ce63cf050f639cb2a5a1ca8))) else (if i < 49 then (if i < 47 then 0x6bd644fcf025d435eb29de4b8eea2006bd653c09750f639cb29b24ba87b1ce548e125d43f4d7aca7812ca1fa6bd653bc9750efb9cac9e04ba87b19c3c0771a943d8e72ca4b892a2257b1ce3c06a50f639cc79e03528795c7594f025d435eb29a64b868a1af594f025c9650f639cd0ab24ba890dec739990a14406d7aca6d92ea0006bd6539497420035ea89e04ba0 else (if i < 48 then 0x7b1b8594f01f1435eb29e04b0e8a1ec7398f534f050d7aca698ee1ca87b1ce6a0f025d435eb29e06612ca2176bd653c08350d7ac8a31e04ba876dce534f025d4428f639cb292ea1ec7398b3c06a50e735eb21e04ba87b1bb594f025d43d8e72ca7813aa1ec6bd6535c7750f639cca9e04ba86bd653c07c19d4420d7aca7792ea1ce6bd513c097512135ea69e04ba8 else 0x7b1ce5953520143d8e72c878108a1fa7b1ce5953550f639cb29ca4ba87b1cd594f00e5435eccaca7792ea1af594ef25c7450f639cb2a6a4ba87b1ce664f01a5435eb21e04b8e8a0006bd5d3c097410abd8e73504ba87e9ec739953c143d8e73426092ea1ec7394d3c07c512135eb29c24ba87b1bb594f01f143d8e72ca969aea1af594f02587c50ecb9cb29e04ba8)) else (if i < 51 then (if i < 50 then 0x7b1ce678c125d43d8e3a947812ea2426bd993c06a50f6394b29e04ba87b1ce548f023943d8e72ca93072a1ec739654903950f639ccc9c84ba87b1ce664f00a143d8e72ca6492ea1ec7394a3c08c50f635eb29e046a87b1c0594dc25d43d8e72ca6b92ea1ec739654b4dc510735eb29e04b287b1ce6653f0a1435eb29e04b870a1ec6ed4d3c09750f639cb29e054a8 else 0x6bd6550cef25d43d8e72ca78104a1ec709653c097500035eb29ca4ba06bd653c0771a14484d7aa47812ea20c6bd653c09750d7aca7792e4b287b1ce595250e5435ea51e04b8cea1af595563c09750f639cb2a7a1ca87b1ce684971a943b6e72ca6b92ea2036bd653c09750d7aca7792e1ca87b1ce5b0dc25d43d8df2ca7812ea2437b1ce3046a5101b5ea89e04ba8) else (if i < 52 then 0x7b1ce614f025d435eb21e04b8eea1ec739644fc395121bd8e718214287b1ce594d71f143d8e72ca7092ca1ec739973c08e512135eb29ae4ba87b1ce595350e543d8e6aca4b872a1ec739753c03950f1b9cb29e04ba87b1b8594f025d435ec82ca7812ea1ec739654fcd75104bd8a31e04ba87b1ce5952125d435eb29e07012ea1ec739ab3049750f639cb29c44ba8 else 0x7b1af568f025d435eb2a867812ca1ec73965304ab50f639ccca9a78287b1ce5953f20143d8e734c6092ea1bb5950e3c07c50f639cad1e04ba86bd653c07c0d14000f5b9c780d481ec6bd9c3049750f638ab09e04ba87b1ce548f028543d8dcaca7812ea2426bd654fc3950d7aca7812e47a8))))))

private def st4 (i : Nat) : Nat := unpack st4Packed 57 20 i

private def adj4Packed (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0x1401100c41146221c080040008007300620042001cc63802008c04108400086229023200030800b01c042bc403141008043 else 0x15221204019c020003101544310000810201803330000080060400026a67190b084c501c440140030020104830800129062) else (if i < 3 then 0x10c600c8a502420300201042480027215400940e0902000cc23042020c2010000000a00048100020188205d807214260840d else (if i < 4 then 0xc2500c6201c04004241280a014c1701a1104e000020080030080218420008ab0040510805480810880400c020084062065 else 0x40118c0301021004230084102c001014001400)))

private def adj4 (i : Nat) : Nat := unpack adj4Packed 5 80 i

private def loc4Packed (i : Nat) : Nat := (if i < 10 then (if i < 5 then (if i < 2 then (if i < 1 then 0x778b794b30820a60097a0b000000000000003bd2438a2d8008003f156c0000900013e881e7000554e417300049adccd402845a000001611aa771a70002b828440a3550e4f1cc8005882b000213786000a2b50000a0000000242b6c5a24762c618842070010340022a00062c2c000 else 0x82b07db79f22ce001bd9c27a4000e5aa76c67b9093800008ad2026564610d8ab247ac001110000b2000000aa698001dc1bf7ee00000209000000001d92bc00000060000c0ce90833624a00333b0000c4c88f3000e9800000000b40b4ae272c171da2b1000c5d9abc4181008e9a4f) else (if i < 3 then 0x1d2e7d248000007bc068ca170244000007840000eaee018000003e3000bf8d20fb53c0000032c5ac0000000063a95d318000002c00000b0000600000019ede54ba7e35901d5d800136000002210dc0015f0003bc0000005341c604003320000000000003e00022089000000d7238 else (if i < 4 then 0x6d4968e80170002f0d3b1f26a001d732e000318100e3488059aa0df76215c128005f8db0003f02da58c2280060ea800000047e250ac800186000000da09e8a5c6b7610e000002110a28699d0007d0001498002ca978001ed1ec2657791e0000000041e19287ca78000025c1181ec else 0x590000cf2854be970000000ac05120aea000fa8000e6000000f10d300094400158174000782ad0006ac3a3e14ce8b9a991a51e01c000004505e1d1284000d69b883065a001ea8000000ec000003c27114e87a25a0008727d7600017d8000003fd648001904408980023af753909a))) else (if i < 7 then (if i < 6 then 0x75486c00311000001c41185c08340028300000000000000c9a0400031a4544f313000521333e90f6f2c00000624ca0170000fa00000000000d640015a3fcc94ea99281466c0009c60ad58248af000000b11d12ec0012c800000dc00035e084e754e0f70325b86b80076c001a224a else 0x11f000144000002e8794ab8088005bed1c0004c1664e0483a0532000de2880000000000000000000000438a44000000cc698000004b600014ac505e000f8aab000db4000841c2f60003f8000eac003b5000b91270d400078c002317740018f0003f4e48e600069000000000) else (if i < 8 then 0x64c80b425614e4c0df3eb11e0001d3653660017194d5f20016100022e001cd1794de63c938bb0004dc000cd408f3c453fc0000000012e00089103340001024000000009e0959207bd0455432f0964d8003f41a0001df1f7288000000db000729848542de65800000382f9c000e7 else (if i < 9 then 0x140000b3000654000572f50000007f0004f507400372000c28ed381390000f48000000000013433f068000006ce000000003bebe862b9500009d08000716c6c000004e8000000007e489d1db69000390a71b052a640988000000008a3c136e000f511661c5add63cc001049fda16 else 0x875028f849827400000000001b72e907e61400000000630003332f5061d78220008089901e718000001746c07d0208000005f8000007460008680000075c9d18a0ba9b8358040008bc0026859ea2c000a9000d0dcc2453b0000c200059800000157078000759e66fe001d480f)))) else (if i < 15 then (if i < 12 then (if i < 11 then 0x65600111800000000003c72eeae01600071e000003382c0000003a10001b400000530001b093b634d45982e7150000001ff0ca0012e88d0000e06c30635a000003180008b0392ec1d8128399756fa0003188868c000823f308c19001907000444be0dd0000002400074a50c87800 else 0x7b46a80040c7ca000cc83e364f7c000000366095aa73000efca300042ab44382525e8e9c002f10003480019a780dd000000296d71edbcd386ecd452537d8670000004960003500078c01400000602bf54305539ab68d7bee64eacdad8e8000000a99dd6c4edc3484000000015000) else (if i < 13 then 0x47223800000254c41ac008000000000cc0ec0004b0000000000027c53e0000037767e0011b00067a4f9c13f5001001002a9000c10000356f0b04000001fa000f43fa00057c00000000000002192246e10ba8c6f4001280f4000002078002840000017f5ecbc1198000000009e800 else (if i < 14 then 0x2086880015665081000214ff80041b38a000de933000000001ba000878e38000003090500029873e0980019624800000712b1c0000030e214000c76321e4000006f8d152300006c054000001f8000379406280006b1220002dd3db42020725988003d64b0ae8007b2541e4800 else 0xa3400097116cdd51800000254002640a00016a9932920007700082800000000232820000005584e4001f0000b2d12b6870c2c800000182000001093f305c00000346b198e1950000000015604c000d2b7e7080002399800000000000692ee5cdb0f0000014a3f614600062261))) else (if i < 17 then (if i < 16 then 0x59cae876c063429fc0000009c00000101000ce5a0b2973c5a8003e070e001f10e023e001fc8006940014da6d0006a40018e1c4084002420b40015c8f12c8dae023ad000000070000566edc2a010001f0faa7024aec87c813248000002a200000000000000135de80000000000218 else 0x148add768006aa00000000776cf1411a00ee185800b9728001ebb4b218cf8003225c2000000001307d82f0000e23940014100046c00334000000003d04b08f05e9fd07ae700020c2e6af1e98000eac31d21ce24c0d00005f0a4d354830b072370e33c8000a39352bf32e00016a0f) else (if i < 18 then 0xfc0002a42d8002dd2a2001530006ea001591d400090cce800000fbc56aa56049e5e29f37fa0005f15b2169d40d00019c0000023a00023081a92000554b8ad47261f8001b54ee000003910d0b28001292950705300082cac2008005a4000c1b5f20000179172000000001a2 else (if i < 19 then 0x1521fc5b80017ba763ce0012a800046550bd8000009b07a8000b68d12a1d60001b10a33671c00172ab40006201b8000127ec002a14e200000000000c3400260000a04000b56cc8c96bbed6ba200003d4000bfd6cabd1e4000db3e4000d5c0032155e419d42375f0001cb800 else 0x670c4001601473722c5ee3837cc09000000126bce082d800100de88783c098a0c8004060006ca3d7fe3e935800000b0c919e51bc1fc9fa260003a800289066001a79e4000b3569c0b10d03975b64312028e011c2fa070528000006d05fb523b6a68000000009a602800)))))

private def loc4 (i : Nat) : Nat := unpack loc4Packed 11 80 i

private def st5Packed (i : Nat) : Nat := (if i < 37 then (if i < 18 then (if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then 0x1ec73952438f052003d8ddaca871e0a4007b1ce548b325d4800f6376b29664ba9001ec739652c89752003d8e72d87812ea4007b1ce594b525d4800f62ca7812e13a9001ec7397c5953f52f639cb29e05992ec1ec739653c0970998000e72ca871660fa9001ce438f01501f52003d8e72ca871e0a400739653c09707d4800e71664b8a80fa9001ec739652cc9752003d8e71e04b8a8a4007b1ce438b31514800f621c780a81329 else 0x7b1ce631653c039610bb9cd7aca7812ec2057b1ce594ef25d83d8e72ca7815a4bb0909ec739653c09660f639cb7aca7812ec000909af5950e3c14800f639cac9e04ba97b1ce65cf0304976000000d7aca7812c8800001af594ef25d10000035eb21e04ba2001ec73965438ef52003d8e72ca5992ca4007b1ce590b325d4800f62ca7792e1329001ec590f025c2652003d8e72ca879e0a4007b1ce594b425d4800f639cb2a1c6e29) else (if i < 3 then 0x1ec7390425c5452f639ccc9e035072c0007b1ce3c0971494bd8e72ca7812e0eb0001ec700f025c5452003d8e71e04b8a2a4007b1ce3c0ab1514800f639c8292e23a9001ec738f01504352f639cb29b86992ec0007b1ce3c0961514800f639c7792e2a29001ec748f025c4e52f639cb29e04b862c1ec739b3594f025d8000f639cb2a6e1ca97b1ce594f02ec9760003d8e71e04b8aca5ec739653c09716183d8e72f0b29e04bb0 else 0x909af595463c09760f639cb29e04b8aec1ec739654fcf023983d8e72ca7812e00b0001ec71cf025c545321bd8e6aca7812ec0007b1ce384971514800e02ca7812e0fa97b1ce594f02c49761183d8e72a47812ec000739653c09607d4800e72ca7792e0fa9001ce590f025c1f52003d8e727e2a072a5ec71d653c0971dd8000edb9c7812e2a29001ec738f025c5053213d8d7ac87812ec0007b1bb3c0971514800f639c7812e27a9)) else (if i < 6 then (if i < 5 then 0x7b1ce594f025c6560003d6e72ca7812ea5ec739653c0970198000f1b9cb29e04ba97b1ce594f025c6160f639ccdaca7812ec000739654fc3907d4c2af635eb299c4bb07b1ce5c8f025c6a600039cb29c24b83ea5ec739653c0d025d8000e72bc7812e0fa980dec739653c097600039cad9e04b83ea40073d653c0970794bd8e72ca7812e06b0001ec739653c08950003bee71e04b8a8a5ec739653c0970ed83d8e72ca7812e0230 else 0x1ec739654a83952003d8e733278050a5ec739653c0841dd8000f639cb29e042297b1ce594e13389760003d8e72ca99872a4007b1ce594e125d4800f639cb2a601ca9815ec739523709760f639cdb2ca7812ec1ec739523c09715983d8ddaca7812e3e307b1ce594f025c0a60003d8e72aa7812ea5ec739653c09717983d8e735a780ee35307b1ce599653c09760f639cb29e04b8b8c1ec739654fd0e0e5800121bd8e71824ba9) else (if i < 7 then 0x7b1ce65d653c06a6102bd8e72d87812ec1ec739654d4971dd8000f639cb29ae4ba97b1ce594dc2d49760003d8ddaca6e12ea5ec739653c0b525d840af639cb29e04b30001ec715653c09752fd3d8e72ca780eec1ec739654ccf01dd83d8e72ca7812e13b07b1ce594c525c3960f639cb29e06512ec1ec739654fcb30e583d8e72ca781744bb07b1ce594f025c6f60f639cbdaca7812ec1f57b1ce594f025d83d8e72f8b2a7e1cb0 else (if i < 8 then 0x1ec739653c09052003b6e72ca780eea4007b1ce594f02594bd8e72fcb29e04bb08e5ec739653b09760f639cb2a307812ec1ec739653c0970c183d8e72ca7812e0730001ec739633c09752003d8e72ca7792ca400761ce594f025d440af9b9cb29e04bb07b1ce594dc2cc9760f6376b29e05992ec2077b1ce594f025d83d8e72ca9f9824bb07b1ce594dc25c2660003d8e72d87812ea1ec7396c3c09703583d8e72d8b29e04bb0 else 0x7b1ce594f02d09760f639cb29c24b872c0007b1ce3c0ac1014bd8e72ca7812e2ab07b1d5739653c09760f639cb29e05d0eec1ec739653c0971b983bee72ca781a64bb07b1ce594f02e09760f639cb29e04b85ec1ec739653c09e25d83d8e72ca7818c4bb07b1ce590f03bc9760f639cb2a2c7812ec1ec73965434f025d83d8e72ca889e04bb07d1ec739653c0976101bd8e72ca6d92ec0007b1ce65cf01a94bd8ddaca871e04bb0)))) else (if i < 13 then (if i < 11 then (if i < 10 then 0x909af594f02cc9760f639cb2a1c7812cc1ec739653c0b325983d8e72ca7792e133073965528f025c4d60f639cb21e04b84cc2426bd653c09709983d8e72f2b29e04bb07b1ce594ef25c6a61213dae72ca7812ec0007b1ce6b4970a14bd8e72ca7f1e04bb0001ec739653b09750f639cb29e04b002c1ec739653bc9700583d8e72ca879e04b30001ec739643c09653213bee72ca7812ec00090dec739650e54000f639cb21de4ba9 else 0x1ec71d653c09752f639cb29e04b8bac000795ce594f025d4800d7a94a31e04ba90022e6bd653c09752f639cd92ca7812ec0007b1ce3c0901514c84d7aca7812e00b07b1ce594f035c9760f639ca79e04b872c000909af594f025948000035eb29de4ba1001af594f03bc9753173d8d7aca7812ec000001af590f025d0800f6376a91e04ba9001af595643c09752003d8d7aca7792ea400739af594ef25d48012135eb29de4ba9) else (if i < 12 then 0x7b5ec739653c09760f639cb2a847812ec1ec739653c0970318000f639cb2a6a4ba97b1ce594f025c1060f639cb29e04b8c4c1fe7b1ce594d325d8432f639cb29e04bb0001ec7394d3c09752003b6e72ca7812ea40080daf594f025d4bd8e72ca6d92e3bb0001ec739654b4f052003d8e73507812ea5ec739653c0770d583d8e72ca7812e04b00021d6bd653c09752f639cb2a0c7812ec1ec739653c09716d8000f639cb29e04629 else 0x7b1ce594f025c0760f639cd8aca7812ec1ec739653c0d425d83d8e72ca859e04bb0909af5950e3c097612135eb2a947812ec1ec755af594f025d83e6e735eb29e04bb0001ec6bd653bc9750f639cb29e05812ec1ec739653c0970ad83d8e7368b29e04bb07b1ce5953f3709760f63a8d7aca7812ec1ec739653ecf025d83d8e72ca949e04bb07b1ce5cd653c09760f639cb29e04b84ac2426bd653c0970b580012135e7812e2a29)) else (if i < 15 then (if i < 14 then 0x7b1ce594f02ac9760f63a2e72ca7812ec1ef7b1ce594f025d83d8e72ca7e1e04bb07b1ce594f01504360003d8e72ca78112a6347b1463c0971518472f639cb29e04bb07b165518f025c4e60f639cb29d24b8a8c2347b1d2594f025d83d8e72ca7812e27307c1ec739653c09760f638eb29e04b8a8c1ec739653c09713583d8e72ca7812e2630909af594f025c5460f63a4d7aca7812ec1f0739af594f025d83d8e72c87812e2a30 else 0x7b1ce595043c09760f63a0e72ca7812ec1ee7b1ce594f025d83d8e72ca7818a4bb07b1ce5950425c5461213d8e72ca7812ec1ec739652b09712983d8e72ca7812e25307c5ec739653c09760f639cb2a0a7812ec1ec739ad5950525d83d8e72ca7812e23b07b1ce595053389760f639cb29fa7812ec1ec739653c09714983d8e72ca7812e22b07b1ce594f01d03960f639cad9e04b8a8c1ec739653c08407d83d8e72ca7815623b0) else (if i < 16 then 0x7b1ce55cf025c5460edb9cb29e04b8a8c1ec739a1594f025d83d8e72ca7812e2830002326bd653c09752f639cb29e0560f8c1ec739653c0970f98000f635eb29e04b297b1ce594f02989760003d8e72a4780f8a5ec739653709715183bee72ca7812e2a307b1ce594f025c0360f6376b29e04b8a8c1ec739653c09713d8000f639cb2a084ba8001ec739653c09050003d8b2a7e1c84ca5ec7396541097101843ef639ca91e04bb0 else (if i < 17 then 0x1ec701653c09750f639cb29e020072c1ec7396525c470e583d8e735eb29b84bb07b1ce594f025c3360f639cb2a7e78158c0007b1ce53cf025d43d8e72ca7812e0a307b1ce5953f4149761213d8e72ca7312ec1ec739653c09714d846af639cb29e04bb07b1ce594f025c6060f639cb2a807812ec1ec739653c06a10183d8e72ca781584bb0002437b1ce3c06a53033d8e72ca7812ec1ec739653c0ac1dd83d8e72ca7092e2a30 else 0x90dec7393f3c06a60f639cb29e04b836c1ec739653c0a025d83d8e72ca7c9e04bb0875af594f034c9760f639cb2a0a6992ec1ec739723c09706d83d8e72ca781844bb07b1ce595483c097612135eb29e04b83ec1ec739653c09607d8432f639cb29b84bb07b1ce590f025c1f60f639ccb9e04b8d4c0007b1ce594ec25d4bd8e7aca7812e0f307b1ce594f033c9760001e04b8a81303ea5ec7396551cf025d840af639cb29e044b0))))) else (if i < 27 then (if i < 22 then (if i < 20 then (if i < 19 then 0x77dce594f025c1f60f639cb29e03e068c2197b1ce594fa25d8460f639cb21e04bb07b1c0594f025c1f60f639cb29e04b830c1ec73971594f025d83d8e72ca7d12e0c307b1ce594f025c3a60f639cb29e06892ec000739653c0a10554c0af638ab29e04bb07b1ce5c9463c09760f639cb2a927812ec1ec7394a3c09706d83d8e72a47812e3e307b1ce594f02381f60f639cb2a9e7812ec2307b1ce5c8f025d8000f6376b29e04ba9 else 0x7b1ce594f025c1360f639cb29e04b838c1ec73d653c0971dd83d8e72ca7812e20307b1ce594f025c5660f639cab9e04b83ec1ec739653c07c05583d8e72ca781424bb07b1ce594dc25c1f60f639cb29e04b82ac1ec73970594f025d83d8e735ab29e04bb0001ce5c8f025c1b52003d8e72ca4b894a5ec739ad3049707d83d8e72ca7812e0b307b1ce6b9653c09760f639cb29f46712ec0007b1ce594e11dd4bd8e72ca7819a4bb0) else (if i < 21 then 0x7b1d3739653c09760f5b9cb2a7e7812ec0007b1ce58cf025d4454f639cb19e04bb07b1ce620f025c6a60f639cb2ac67812ec0007b1b8594f025d4bd8e7322a91e04bb0001e3739653c09750f639cb1a7e7812ec0006bd653c0972594bd8e92ca7812e27308a1ec739653c09760f639eb29e06712ec1ec739654fc3907d83d8e72ca7d12e1cb07b1ce595153c09760fd3d8ddaca7812ec1ec739653c0a11a983cae72ca7812e2a30 else 0x7b1ce56d3f3c09760f639cb2a6c7812ec1ec5954649cf025d83d8e72ca8c9e04bb08a5ec739653c09760f2b9cb2a7e7812ec22d7b1ce6b4f025d83d8e72948e1e04bb0001ec739653909750e72caa52547812ec1ec73965468f025d844af639cb29e04bb07b1c75953f3c09760f639cb2a707812ec1ec739653c0901dd83d8e72ca9f9e035307b1ce5950e370976102bd8ddaca6e12ec2227b1ce594f025d83d8e72e4781824bb0)) else (if i < 24 then (if i < 23 then 0x7b1ce595463c0966121bd8e72ca6092ec000739af594ef25d439cd7aca780f8353090a1f6bd653c09760f639cb29e04b86ac1ec739ad4fcc125d8486f639c781824bb08c1f0739653c09760f639cb29e04b810c1ec739654fcf01cd83d8e735a8e1e04bb07b1ce5953f3c08960f639caf27e7812ec1df739654fcf025d83d8e72ca9b9e04bb07b1ce594f025c6d60f639cb2a7e78108c0007b1ce584f025d4bd8e72c8871e04bb0 else 0x7b1ce548f02cc9760f639cccaca7812ec1ec739654fcc11a983d8e72949f9e035307b1ce594ce1f03960f639cb29e06192ec00090dec738f01a94486f639cb29e035307b1ce594fa3c09760f639cb2a54780d4c2437b1ce594f025d83d8e72ca809e04bb07b1ce595333c09760f639cd5aca6e12ec1ec73982594f025d83d8e72ca9f98214307b1ce5193f3049760f639cb29de5a12ec2057b1bb594f025d83d8e72ca7812e1230) else (if i < 25 then 0x7b1ce594f025c1260f639cb29e06912ec1fc7b1ce594f025d83d8e7286781824bb07b1ce620f025c2860f639cc0aca7812ec2427b1af594f025983d8e7310b2a7e1cb0001ec73965390975305bd8e72ca78112c0007b1523c0970994c16f639cb29c24bb000165438f00981f5305bb0e72ca7812ec1ec739553c0970e583b0e72ca7812e1cb0829ec739653c097600042ed7aca7812ea5ec7396543cf025d83d8e7370b29e04bb0 else (if i < 26 then 0x7b1ce518f025c2860f639ee72ca7812ec1ec73952514f025d83d8e7308b29e04bb07b1ce594f02b04060f639cb29e048072c00090dec738c125d43d8e72ca7492e1cb07b1ce594971504a60f2b9cb29e04b872c000739653c08407d4bd8e72ca7812e1bb08e9ec739653c09760f639cd1aca4b872c1ec739654fccb25d83d8e72ca7811c1cb090a106bd653c09760f639cb29cc4b872c1ec739653c0970d9846cf639cb29e04bb0 else 0x7b1ce6653f3049760f639cb299c4b86ac0007b1ce594e125d43d8e72ca780ee39b07b1ce595333c03960f639cb29e04b8b4c1df739653c0970e583d8e72ca981a61cb07b1ce5953025c3960f639cb29a64b850c1ec761ce594f025d83d8e7352b292e1cb0815ec739653d497611cbd8e72a47812ec1ec739653c0970f183d8e72b67812e1cb07b1c0594f025c3960f639cb22947812ec1ec739654fc3909983d8e734ab292e1cb0)))) else (if i < 32 then (if i < 29 then (if i < 28 then 0x7f9ec739653c07c60003d8e72ca78108a2427b1cf594f025d83d8e72ca781081cb0909ec739653bc9760f639cb2a6c4b872c1ec73965480f00e583d8e72caa91e03e307b1ce6b4c125c3960f639cb29e0480a8c1ec73965544f025d8000ec39cb29e04ba97b1ce5f5653c09760f939cd7aca7812ec1ec739ad594970a183d8e735a7812e14307b1ce594f025c7860f639cb2a6667072c1ec739654cc970e58416f639cb299c4bb0 else 0x1ec739993c02850f639cbb2ca7812ec2427b1c7594f025d83d8e736ab29e04bb0839af594f025c7c60f639cccaca78050c1ec7398a594f00e583d8e72ca9f8ee1cb07b1ce71d653c09760f639cb29e04b8d6c1ec6bd9c594f025d83d8e72c29f9e04bb076dce594f025c3960f639cb2a7e2f872c0007b1ce595270e54000f639cb2a6c1ca87b1ce595361f03960f639cb29e05512ec1ec739653bcb325d80012135eb21e04ba9) else (if i < 30 then 0x7b1ce594f036c976000484b29e04b85aa5ec739653c0970f583d8b2a1a7812e3bb07b1ce6b4971a83960f639cb2a464b872c1ec739653c0970a183d8e735accaca1cb07b1ce594f03709760f639cb29ea7812ec1ec73999594ce0e58420f62ca871e03bb0865ec739654dc9760f639cb29e04b87ec1ec73999594d30e583d8eb39cb29e04bb07b1ce548f02fc9760003d8e72ca78156a4007b1ce594dc25d4bd8e02ca9f9e04bb0 else (if i < 31 then 0x1ec739654a83951073d8e72ca7812cc1ec739af594e125d83d8e72ca9f8d41cb07b1ce6b5654fc3960f639cb2a7e67072c21f7b1ce5953f0e583d8e72b67812e0fb07b1ce5953f3c028610abd8e72ca6612ec2437b1ce594f00e583d8e72ca939e01cb07b1ce5952a3c03960f639cb29e05912ec1ec739653c0c425d83d8e72ca9f8f81cb07b1ce595103c09760f639cb2a7e4b850c1ec73965564f025d8486f639cb292e1cb0 else 0x7b1ce594e125c776119bd8e72ca7812ec2437b1ce5953f0e58416f639cb2a7e1cb07b1ce594f025c8c60f639cb2a727812ec1ec739654d4f025d8000e735a6092e0fa97b1ce601653c09760f639cb29e04483ec0006bd653c0970054800f639ca79e04ba97b1ce5953f49c3960f639cb2a0a4b88ec22a7b1ce5953f0e58432f6376b29e04bb08c1ec739653709760003d8e6aca7812ea5ec739653c0970e583fcf639cb2a7e1cb0))) else (if i < 34 then (if i < 33 then 0x1ec739654109752f6376b2a8a7812ec1ec739643c09715583d8e735eb29e04bb07b1ce595464fc3960f6380b29e04b8a8c000739653a49707d4bd8e72ca871de4bb07b1ce665653c0396101b9cd7aca7812ec2347b1ce5953f0e58460f639cb2a7e1cb07b1ce659653c03960f6376b29e04b84cc1ec739653c09707983d8e72ca9f8721430001af594d33389752003d8e72ca98072a00076d653c0971dd4bd8e72ca939824bb0 else 0x7b1ce6ed523c09760f639cb29e04b8d4c1ec739a6594f025d83d8e72ca7492e0fb07b1bb595523c09760f639cb2a827812ec1ec739653c0ec25d83d8e72ca7812e0bb07b1ce594f025c1a60003d8e52ca7812ea2397b1ca594f025d8000f639cb29b83e297b1ce729653c09760f639cd6aca7812cc2397b1bb594f025d83d8e72c87812e3e307b1bb594f03349760f639cb29cc4b83ec21b7b1bb594f025d83d8e72ca698f81cb0) else (if i < 35 then 0x815ec73993594f060f639ca928c7812ec0007b1bb594f01f14bd8e72caa29e04bb0815ec739653c090610abd8e72ca6992ec000739653e8970614c68f639cb29e04b307b1ce594f0258546113bd8e72ca7812ec2347b1bb594f025d83d8ddacaa51e04bb0841ec739643c0976102b9cb2a1c780f8c1db739654fcf025d83d8e7376b29e04bb0815ec71d653c09761183d8ddaca7812ec1ec739a6548f025d8402f639ca91e04bb0 else (if i < 36 then 0x909af595643c09760ff3d8e72ca6e12ec1ec73965370ce25d8000f639ca91b84ba87b1ce6ed653709761133d8e72ca6e12ec1ec7395b3c0971dd8420f639cb29e04b307b1ce664f01a85460f6376b29e06e12ec1fa7b1ce594f025d844cf639cb09e04bb0001ec715653c09750f639cccaca78158c1ec739653c077089844cf638ab29e04bb07b1ce594f025c3460003d6e72ca7812ea2427b1af594ef25d83d8e7294780ee3530 else 0x85dec6bd653c09760f6376d6aca7812ec1ec739653c0841f18404f639cb29e04bb087dec6ed653c09760f639ca91e06992ec2057b1ce594f02118000f639c4b8a82529815ec739654ccf060f639cb29e07212ec2197b1ce548f025d83fcf639cb29e04bb07b1ce595303709760f639cb2a8c6e12ec1e5739653c09707d83d8e72ae9f9e04bb0001ec73964438f052003d8e6aca7812ea1ec73965370bf25d83d8e72caaa9e04bb0)))))) else (if i < 55 then (if i < 46 then (if i < 41 then (if i < 39 then (if i < 38 then 0x7b1ce594f02582660f639ca51e04b8cec2107b1bb594f025d840aedb9cb29e04bb0001ec739523c07c50f639cb2a947812ec1ec739af590f025d840af639ca91e03e307b1ce594f0284396102bbee72ca7812ec1ff7b1ce594f025d8000f6376b29e03e28815ec6ed653c07c60f639cb29b86092ec1ec739523c0971dd83d8e72a4781824bb07b1ce679653c0976111bd8e72ca7812ec0007b1ce63d653c14bd8e735aa91e04bb0 else 0x1ec6bd643c09750f639cb29e06992ec0007b1ce544f025d4406f639ca89e04bb07b1ce595443c097611735eb2a8c7812ec1ec739653c0a325d8000f639ca91b84ba990dec738f025c6a60f639cb2ac87792ec1ec73965370970e583d8ddaca9f9e04bb07b1ce548f025c6a60f639cb2a7c7812ec1ec739653c0971ed83d8e72ca7812e05b07b1ce665653709760f6376ccaca7812ec2107b1ce594dc25d8484f639ca91e04bb0) else (if i < 40 then 0x7b1ce595373049760f639cb2a6e78112c1ec739655293f0e583d8e733ab292e1cb08c9ec739643c09760f639ccba8c7812ec1ec739653c0a825d845cf639cb29e04bb07b1ce629653c09760f639cb29e04b92cc1ec73990594f025d8412f639cb29e04bb07b1ce5494a3c09760f639cb29e0470eec1ec73965398971dd8000ddaca7812e0fa97b1ce594f025c5460fd3d8e7332b29e0c1ec739973c09719d83d8e72ca9f9c24bb0 else 0x8d1ec739523c09760f639ccc9e03b8d4c1ec739654d4971d183d8e72a47812e13307b1e5739653c09760f639cb29b84b8f8c1ec7396546cf025d83d8e738ab29e04bb0899ec739653c09760f638ed7aca7812ec1fe7b1b8594f025d8484fd35eb29e04bb08b5ce6bd4a3c0976100bd8e72ca7812ec0007b1ce594f525d43d8e72ca7812e3eb07b1ce61d653c09761213d8e72c87812cc1ec73965370cd25d83d8e72ca9b92e1a30)) else (if i < 43 then (if i < 42 then 0x6bd653c0964301bd8e72ca780f8c0007b1ce594f025943d8edb9cb29e03bb07b1ce594f027c9760003d8e72ca708eea1ec739995953f0e58484d7aca781a64bb0001bb594f025c7c52f639cb2a3e7812ec1ec739653c09704583d8e72ca7817e4bb0001c7594f025c1f52f639cb2a4e7812ec1ec739523c0970e580012135eb29e04b287b1ce578f025c7760f639cb29a64b868c1ec739af594f020183d8e72ca979e04bb0 else 0x835ec739653c07760f639cb29e0480d4c2057b1ce6b4c125d83ecf639cb29e04bb0001ec739a15949752f639cb29e04b8cec1ec739653c0972418420f639cb29c23bb0001ec739643c09650f639cb29e0708eec00077dce594f025d4bd8e735ab292e1cb0001ec739573c07750003d8e72ca4b894a0007b1ce594f010d4bd8e72caab9e03bb0001db739653c07751083b6e72ca780eec1ec6ed653c0971a983d8e72ca780f833b0) else (if i < 44 then 0x8d1ec739653709760f635eb29e04b83cc1ec6ed653c0970e583d8e72ca9fa2a4bb07b1ce664f01a81f60f639cd6aca6e12ec1ec73999470f025d83d8e72ca7a92e06b07b1ce594f025c8060f639cb29e05112ec1ec6ed65518f025d83d8e72ca7812e44b0001ce664f01a81f52003d8e72ca7792ca1ec739654dcf01a983d8e72ca781484bb07b1ce518f01dc6a60f639cb29cc4b8a8c1ec739973c0771a98484d7aca7819c4bb0 else (if i < 45 then 0x855ec701653c09760f639ccbaca78072c2427b1ce594f02418486f639c8e1e04bb085dec739653bc9760f639cb29fe7812ec242795ce594f025d83d8e72ca7812e02b08b9ec739643c0976120bd8e72ca7812ec1ec739653c0c125983d8e728c8e1e04bb07b1ce594f025c7760f6380b29e04b8eec1ec739653c09708983d8e72ca9b8ee1cb07b1ce64d653c03960f639cb2a0a78086c1ec739653c0770a18416f639cb29e03bb0 else 0x6bd65528f025c7760f639cb29b84b8eec2197b1ce594ef25d8000f639cb29e021a8909ec701653c097610bbd8e72ca7812ec0007b1ce594f02014bd8e72ca7792e1c307b1ce595463bc97611a3d8e72ca7792ec22a7b1ce594f025d8460f639cb29de4bb0001ec739654b4f05102bd8e72ae7812ec1e3739654fcf025d8484f639cb21de4bb07b1ce594f03389760e735eb29e03e072c0007b1ce3c0891514bd8e72c8a31e04bb0)))) else (if i < 50 then (if i < 48 then (if i < 47 then 0x909ec739ad30497612135eb29e04b8d4c00085daf594f025d43d8e72ca781804bb07b1ce6b5653bc976102bd8e72ca78142c1ec739ac594f025d83d8e72ca7799c4bb0909ec7395e3c097610ebd8e72ca7812ec1ec739653c0b625d83d8e72c87819c4bb0909ec739653c08960003d8e72ca78156a1ec739653c0960e183d8e72ca7812e0cb087dec739653bc9760f639cb29de6992ec2427b1ce594f02118000e72ca781120fa9 else 0x1ec701653c09752f639cb29e06992cc2197b1ce594f025983d8e72ca7812e07b0739af529463c09760ff3d8e729e7812ec1ec739653bcc025d83d8e72caa51e04b308c1ec739653c096610cbd8e72c87812ec1ec73991594f00e58000f639cab9e03ba97b1ce595303c09760f639cd7aca78118c2427b1ce594ef25983d8e72ca781de4b307b1ce594f025c7c600035eb29e04b92ca1ec739653bc972598000f639cb29b64ba8) else (if i < 49 then 0x7b1ce594f02401f60f639cb21e04b802c1ec739653c0972118420f639cb29de4bb07b1ce594f01f02860f639ab2a7e7812ec2427b1ce594e125d83d8e72ca780ee34307b1ce590f025c6a60f639cb2a4e780d4c20e7b1ce594f025d83d8e72ca7792e3e30001ce6bd643c09752f639cd7b2a7812ec1ec739af55cf025d83d8f5b9cb29e04bb07b1ce669653c09761213d8e72ca6e12ec1ec6ed653c0ce25d8484f6376b29e04bb0 else 0x2426bd652cc9752f639cddaca780f8c1ec6ed653c0c125d8462f639cb29e04bb0909ec739993c06a60f639cb29e0558a8c1ec739ad594770e583d8e72ca7812e34b07b1ce665653c09660f639cccaca7792ec1ec739653c097145800121bd8e72ca1ca97b1ce665643c09760f639cb29de4b8eec1ec739653c0bc25d8484f639cab9e04bb0865ec739654fc3960f639cb2a7e35050c1ec739643c0971dd83d8e732a7812e3a30)) else (if i < 52 then (if i < 51 then 0x7b1ce6b53f3c06a612135eb29e04b8e8c1ce6bd653c0ef25d83d8e7338b292e1cb0909ce6bd643c09760003d8d7ac87812ea5ec739653e8c125d83d8e735eb29de4bb0001ce6bd653c09652f9bd8e72ca7812ec1ec739ad304971dd843ef639cb29e04bb0001ec739953c097530fbd8e72c87812ec1ec739654fce925d83d8e72ca7819c4b307b1ce590f025c39600039cb29b84b83ea5ce6bd6534cce25d83d8e72c89f9e04bb0 else 0x1ce55cf025c1f52f639cb21e04b92cc000001af594ef25d03d8e72caa91b84bb0909af5953f3c097600035eb29e07792ea000001af590f025d0000f639c7312e2a298e5ec73965370976102bd8e7332780d4c000909af590f025d4000f635eb29e04b28001ec594dc25c2652f635eb29e07792ec000739af594f02594484e735eb29e04b307b1ce55cf025c7760f639cb2a1c7812ec1ec73965370971a9839cd7aca7812e4b30) else (if i < 53 then 0x7b1ce594f025c0060003d85992e2a04ca630739af528f025d83d8e72cab09e04bb07b1ce6bd653a49761193d8d7aca7812ec1ec739af594f023983eef639cb29e04bb07b1ce5c9653c09760f639cb29e04b072c2157b1ce5953f25d83d8e72ca7812e3ab0001ec7394d3c09750f639cb29e06092ec2428c1af594f025d83d8e72ca9b92e1cb07b1ce594cc304976000000d7aca7812c81ec739654fcd30e5839cd7aca7812e12b0 else (if i < 54 then 0x7b1e3739653c09760003d8e72ca9f850a5ec73965430f025d84851a35eb29e04bb08bdec739653c09760d7aca781a64b8eec2307b1ce65cf025d8000e72ca7811c0fa9815ec739643c09761073d8e72ca780eec1ec739653c0891518000f6376a91e04ba87b1ce594ef3049761003d8e72ca7812ec1ec739654c0f00e5835eb2a947819c4bb08c9af5954a3c09760f2b9cb2a947812ec232739af594f025d83d8e3aca7812e0fb0 else 0x7b1ce5953f3043960003e0e71e04b89aa4006bd4a518f025d43d8d7a94a31e04bb07b1ce6bd523c09760f638eb2a8c7812ec0008b9af594f025d43d8e735eac9e04bb07b1ce594f02586a610eb9cd7aca7812ec1ec7396544cf025d83d8e72ca9f9cc4bb07b1ce5952725c3961133d8ddaca7812ec2427b1ce594e925d8000d7aca780f83ba9841ec739523c09760f639cb2a867812ec0007b1ce65cf01a94000f639c7492e2a29))))) else (if i < 64 then (if i < 59 then (if i < 57 then (if i < 56 then 0x8b5ec7394a3c09760f6376b29e06992ec1ec739653c0971198484d7aca7812e1cb07b1ce5953f470396116bcae72ca7812ec1ec7398f594f025d8460f639cb29e04bb07b1ce664f025c28610fbd8d7aca6712ec20b7b1ce554f025d83d8e035eb29e04bb07b1ce6b4c125c5460f639cb2a6e6712ec219739af594d325d83d8e72ca7b92e1cb08b5ec6bd463c09760f639cb29e04b804c2107b1ce5953f0e58484d7aca7812e3e30 else 0x7b1ce63d6550cf060f635eb29e03e0eec1ec739643c0d325d83d8e7342b2a864bb07b1ce5953f4a83960f639cd7b1eb29e0c0007b1653c0960994c5af639cb29e046307b1ce6bda159497612135eb2a867812ec2057b1ce594dc25d8442f639cb29e04bb0855ce6bd6534c9760f639cb2a7e78120c1ec739af594f025983d8d7aca939e04bb0001ec594f025c265316bd8e728c7812ec2427b1ce5953f0e5839cd7acab21e04bb0) else (if i < 58 then 0x815ec739653c08e60003d8e52ca7812ea5ec739af578f025d83d8e72ca781c24bb07b1ce6bd653c08960f6376b29e04b83ec22d7b1ce594e425d83d8e72f4b29e04bb07b1ce594f023854610ebd8d7aca7812ec2057b1bb548f025d8000f639cb29b84ba8841ec739573c07760f639cd7aca78108c1ec739653c0970b583d8e72caa31e04bb07b1ce594f03707c6121432d7aca7812ec1af5954a518f025d8484d7aca781824bb0 else 0x7b1ce620f03049760f639cb29e04b83ec1db739653c0971dd83d8e72ca7812e10307b1ce548f03389760f639cd7a9a7812ec1ec739523c097151835eb2a8c781a64bb07b1ce548f03709760002ca5992e1303ea5ec739523c09707d83d8e732a7812e3bb090dec7393f3049760f639cb29e06612ec1af595463c0971f183d8e72ca6612e1cb0795ce6bd653c09761213d8e72ca7811cc0007b1bb594f025d4000e72ca781200fa9)) else (if i < 61 then (if i < 60 then 0x90dec739ad594396102bd8e72c27812ec000795ce594f025d4000f639cb29b83e287b1ce6ad653c097600035eb2ac87812ea1ec739993c0c10e583d8e72bc7812e0fb07b1cf595463c0976102bd8e72ca7612ec1ec73997594f024183d8e72ca781964bb07b1ce701653c097612135eb29e04b8eec1ec715654fcf025d835eb29e06999c4bb0001e5738f025c54532135ed6aca7812ec1ec701653c0ce25d80011935eb29e04ba8 else 0x855ec739653c08060f639cd7aca7312ec1ce6bd653c0be25d83d8e72ca781423bb07b1ce5493f3c09760f639cb29e04b85cc1ec739653c0971b183d8e7306b29e04bb0855ec739653389760f639cd7b507812ec1ec739af6b4c125d83d8e72cab21e04b30815ec701653c09760f639cb29de4b8a8c1fd7b1ce594f025d8000e72ca7312e0fa990a2d6bd653c0976116bd8e3aca7812ec00077dce594f025d43d8e72ca7816e4bb0) else (if i < 62 then 0x7b1ce55cf025c3960f639cb29de4b872c1ec739654b4f025d83d8e7330b29e04bb07b1ce6bd654b4f060003d8e731eb29e0a0007b1ce590ef25d43d8e72ca7812e19300020e6bd653c09752e735eb29a64b872c1ec739653709703583f4f639cb29e03a307b1ce595373c039600043ad7aca7812ea1ec739523c09703583f4f639cb29ae4bb0001ec738f023854532135eb29e06612ec0007b1ce595370e543d8e72ca7812e3b30 else (if i < 63 then 0x739af528f03049761093d8e72ca7812ec1ec739aa594970e583d8e72ca7812e3cb0855df739653c09760003d8e72ca9a92ea0007b1ce564f025d4486f5b9cb29e04bb080daf594f025c7760f639cb2a7e1c86ac21f7b1ce594dc25d83d8e72ca7814a4bb07b1ce6b5651f03960f93d8e72ca7812ec000739af590f025d4436f639cb29e04bb0815ec739523c09760fd39cd7aca780f8c000909af594ef25d43d8e72ca969e06630 else 0x1ec739653c08c50f635eb2ac87812ec1ec6bd65338c125d83d8e72a27812e3bb07b1ce6bd993c06a60edb9cb29e04b8f8c0007b1ce6b4970a1439cd7b18b29e04bb07b1ce6bd5b3c09760f639cb29e04b0eec0006bd653c07c1dd445af639ccc9e04bb0815ec739653c097611ebd8e72ca7812ec1ec739653c0a105583d8e72ca9f9e05d307b1af594f025c6760efb9cd7aca7812ec21d7b1ce594ef25d83d8d7a8c781824bb0)))) else (if i < 69 then (if i < 66 then (if i < 65 then 0x839ec6bd653c09760e735ea51e04b8d4c0007b1ce6a0f025d4406f635eb29e04bb07b1ce594f025c726102bd8e72ca7492ec00076dce594f025d40010735eb29e04ba87e9ec739653c07c60f639cb2a0e7812ec1ec739653c0970a98000f639c6e12e2a29909db739653c09760f639cb2a544b872c205739af594f01f183d8e72ca6712e14307b1ce595203c097611a3d8e72c87812ec1ce6bd653c0970d583d8e72ca919e04bb0 else 0x7b1ce64d653c07760fd3d8d7aca780eec1ec739653c09e0e583e0e72ca7812e26b0815ec739653989760f635eb29e04b868c0007b1ce594f525d4bd8e72ca819e04bb07b1ce594f025c2160f639cd7aca78120c1ec77dce594f025d83d8e72ca9f8721a307b1ce594f01d06a60d7aca7812e3e0eec1fa76dce594f025d83d8e72ca6092e23b07b1ce5490e3c09761083d8d7aca780eec00080daf594f025d4486f639cccaca1cb0) else (if i < 67 then 0x7b1ce595243c09760f639cb29e04b8ccc1ec7395e3c0970e58434f639cb29e04bb08c9ec739653c09760003d8e72ca6b92ea1ec739433c0971a98000f639cd0aca4ba890a056bd653c09760f639cc5aca7812ec0007b1ce595330e543d8e72caa51de4bb07b1ce6bd6535c9760f639cb29e037872c1ec739653c0890e583d8e72ca9f9e04bb0001ec739654fc2850f639cb2a7e2a072c1ec739643c0971a583d8e72caa51b84bb0 else (if i < 68 then 0x6bd653c0ce25c7c610abd8e72b27812ec0007b1ce544f025d4bd8d7aca780ee3530001ec739953c097510abd8e735ab292ec1ec739653c0971cd83d8e732ab29e04bb07b1ce665523c0976102bd8e52ca7812ec1ec739653849707d83d8ddaca7812e3bb0815ec7395e3c09760f639cb29e04b8f4c1ec739654fcf02598000f639cb29e040287b1ce6bd654fc3960efb9cb29e04b8eec2107b1ce594f025d8484d7aca781de4bb0 else 0x909ec7395b3c09760f639ca527e6092ec2057b1ce594e125d8484d7aca7812e4b30001ec739654d83952f639ca51e04b850c1ec6edaf594f025d83d8e735a4b87214307b1ce590f03009760e735eb2a547812ec1ec73989594f025d83d8e72ca951824bb076dce594f025c1f60003d8e72ca2f872a5ec7396534c9706183d8e939cb29e04bb07b1ce594f025c2960f639cd41e06612ec1ec6e1653c0970e58484d7b32b29e04bb0))) else (if i < 71 then (if i < 70 then 0x1ec739553c09750003d8e71e0420a8a6037b1ce594f025983d8e739ab29e04bb07b1ce594f025c2360f639cc8aca7812ec1ec6bd463c0971a98000f6370b29e04ba87b1ce6bd653909760003d8ddaca6e12ea0007b1c7594f025d4460e72947812e2a307b1ce6a1653c09761103d8e72ca7812ec0007b1ce3c0971554c0af639cad9e04bb07b1af629653c097611a3d8d7a8c7812ec1ec739653c0961a583d8e72ca9b1e01cb0 else 0x899ec739523c09760fd3d8e72ca9f9e0c1ec7396545cf025d83d8e72ca7c1e04bb07b1ce5953f3bc9760f635eb299c4b872c1ec739643c0b325d83d8ddaca7812e13b07b1ce664f00e42860f639cb29e04b870c1e5739653c0971dd840af2b9cb29e04bb07b1ce594f02587c60ff3d8e72ca78108c1ce6bd653c0971a183d8e72bc7812e2a308b9ce6bd653c0976102bd8e72ca9f872c1ec73965338770e5841ce735eb29e04bb0) else (if i < 72 then 0x8a9e3739653c09760f639cb2a447812ec1ec6ed653c09703583d8e72ca781082a307b1ce619653c09760e735eb29a66092ec242739af594ef25d843ef639cb29e04b307b1ce6b5643c09760f639cb29d24b8eec1ec6bd653c0bd25d8448f639cb29e04bb07b1ce6bd654d497600039ca91e04b83ea5ec739464fcf01a9842ed7aca7819c4bb0001ec7396536c975301bd8ddaca7812ec2347b1ce594f025d8462f6376b29e04bb0 else (if i < 73 then 0x7b1af594f01dc3960f639ccca7e780d4c1ec6bd6534cce25d83f4f639ca69e04bb0001af594d33389750003d8e72ca93872a5ec739653c0971d183d8e72c8781824bb0001ec739613c09750edb9cd7aca7812ec1ec6bd653c097259840af639cb29b83e30739af594f01f07761133d8e72ca9f872c242855af594f025d83d8e72ca7792e0fb07b19c594f025c776116bd8e72867812ec1ec739653c09710d83d8e3aca7812e1cb0 else 0xe735eceaca7812ec1ec73965534f025d83d8e72ca781123bb07b1ce594d31dc3960f63b6e72ca7812ec2117b1ce594f025d8484f639cb21e04bb0)))))))

private def st5 (i : Nat) : Nat := unpack st5Packed 67 20 i

private def adj5Packed (i : Nat) : Nat := (if i < 3 then (if i < 1 then 0x800c200c0021062c11470420c000a3010400450800020040830002440031000010080020890400043400001402c03c12000400000010482801001c2 else (if i < 2 then 0x30008305200b0850c008318004000308000000130708214e0000010023411000c010304208400e0c11404090860800000001010011c008200800d000 else 0x20008000e0411020420811000c324d0c504b0c60011c301410c10900200110a4c61010001c000000000600024310408000a0000c00c43c10050010d1)) else (if i < 5 then (if i < 4 then 0x10001c10020010460011402c400400018520a24220405200420214414019b0000090810402430410411c00c008024308000010004300c045102140 else 0x401800c40400000442401c60420030c30000021c02050cb18100800b2c41403c00430400001c10410060056800073c029308100028200a04204100c) else (if i < 6 then 0x1004d0032001830012c700438200010714530000a0032c00830422000001820c004600300100000400b0020c2005080387281001040002ac1080000 else 0x8082081080340241)))

private def adj5 (i : Nat) : Nat := unpack adj5Packed 6 80 i

private def loc5Packed (i : Nat) : Nat := (if i < 14 then (if i < 7 then (if i < 3 then (if i < 1 then 0x1299d18007e11b8ed869001568000000006a0df80046eb289e00000058a83000992fa93000000000298800000ca5e5d1e9a2420000f32c8eb800000240c704ed009d50369abcd536ff502142000000002270000000059286b6b256af3000d188f2f0a280015100003217898000 else (if i < 2 then 0x86cf9c340007600e400094000001ed0000007f0648004a2cd4002a555eb940000035d354001c31c232000000904000834d20011a478800222c749c0000013180000051ce15ac9220004601a0002b6256ad85177f3748aaaba7a001b04b773c00154c791795d00f00038e000391b5 else 0x8680c0000003282e0002660000000000000000017c633de00108b1a3e744d59caa46abf8004ee000108004d70000000033e6760000991c70c9e19700002eed400587000c8c004951360027b0002885edd68008627a46980022e00165d29ac0ad4000e399c9010bd21000769bdbd4)) else (if i < 5 then (if i < 4 then 0x7db178a1800714db80051200000069000af2b66738000000003f0ce84a911e405098665e88000b3936ec2037000002160fa00095276800000e9c00160606fe049444ad09b68c800a93230000000005140003a0006c5839ec19f390cf80000099e9c99d000c3e1d0601020018acf4 else 0x3f2eedfc95d7be00095da70006628d8007e6002559a27683ac6b80079c0013784d0000019c2cc00000178c0625e000a94ac00028c004142002307f257a5c000000e857250400000b48000b2a49758972b3800158000002070000000021a9167fc0032aa6473400445a0aab21224f) else (if i < 6 then 0x7c6000f855e22c000000008ee001a830b0012355880060a16ecbae0000000000278b400000488000d91150008e1679bf2630000000000054000071000532e0dbbac11968345728daa67d6570000000ca1705f686b5a528458a03126289c00162143358000c3210000000aa9ce8fb else 0xaff57473800b5ab71d28002f2002579a46c558687afc3b200132d3b1eb131de1b826e002118004aa392a345faf8024091b37b8000003ff001158005760000015f8b9a4a00149cff0cc068972619ef084e0d2832a678f3800000000002be00000287550000000000002f8c5c23b30))) else (if i < 10 then (if i < 8 then 0x4eeedc000003e40007c00043cc89b594846600000000000000e78000000001980082d55e268002e8411292842d8dc0004e3000ab5740009f6a01840000012d4000fc1640000048544c00000000a685fc06b794fc0000018ab516515d8dc000d5cd5b9b0aa294f712300000248000 else (if i < 9 then 0xa560000c34b5292fc7bd730009e80040b12ce6a96212a10865bb21d7ba000004579361b000000000a09e8800ae2000a63ba770ebd45daf8f6000ebc2f520df1b4800a04002dd09796297c000007167e8000006ab2440022b000cfcea955822001ed97828e5793fbd60000003713b else 0x6a4000002d100127888348001684004e20000017486a0fa00193c8a4ea002d847f1d8e4400000ade0028ab562fb198c5804000406c180009e0006f5b43383c00041e001470002481daa8c004e19616e4609817620014fa461276240014a00070000000000e4815bd562818c00151)) else (if i < 12 then (if i < 11 then 0x11d00083247c6c93600022400559372bd8000088b7004c90000000000015f0512d8cb0a9001032311d166d5480033d000684398000015d6888c55cc000b68677840fa6b17165aa283f800001399d10009ea001eb81b00000029b190a80024a000304d1d7e8000003a80010e else 0x97ab5c00102160000002cd8b2002353164a6448794c7000d7a7600036e9a223825000e66270003120c5b54c400000000000198c98000110000001c00066e0000016717e0f1bd59982e00000213000fdc00000000664005b316b655a985d9a62edf60003a0000f08e04625a5e3800) else (if i < 13 then 0xa820009f80085466e0824c000001c38d44720021c3329f40000015c001281b409827c0008d9e80008200005aaa80001a9e0684001941b67f601c0058634d4c04580016654e4b000a86001460be92e49100a6c9f0b14004520006aa9b4da000002a2446000000f200000000139800 else 0x4b09f59647c0001f2c510b37d63800166458000c6d0d0012a400279a304159241c001535d53f2a2f40400404ad407d8d800000001cc0000000026048e3e2000000000009d935a9e82703adb52d5804a00008e0013f40047e3ba0000000044a081104de2155f400000000e7e41d24)))) else (if i < 21 then (if i < 17 then (if i < 15 then 0x1680002943377223c119c92720000058f37674e0d80041627e4c5690003fd4e96a9f80004f00036085400340001022289d400133d7d82d49b595218002f54f164b395c400188c76436559d90d10000000053f000001ff40a0000017a437018a62d598f77a0018518725219400000 else (if i < 16 then 0x346000860000015980002c000e50002c2340af62526459e8ec00000000001a70001fb1b4000002ea000510004144cd7bbbe000001ce3e26c2a1cf5b319013a6148000000003d2eb0aea847cab48d8b2002bf46fe8b850800000b74002d50006d000312000f600034a3a5380003fc else 0x80b6300000065e002a8a817088d9a0d818a75de2e000000f10ef800b540000043f3db06025021000e040000005c328d91861755ac000ad64073a20800a16b78a700091e0010b0003222a91a000000000004df000002c10000e0104003336e800190a88406e30f18005d40025f4c8)) else (if i < 19 then (if i < 18 then 0x9720000024727ade0000a6000002cd3e5000001d99d8391098a68006306bc2b00071e216010000000017c9808b0fd400000afc6f2511c218e000e6000001156cf80a0002691900017b12d3d80007e000a49bdb6a002142280f60000012154d1bc00193b2306841b886e6e026a000 else 0x2650005fe000000b1970f900044800079a2a000000160ab8000006a5b90006c6615873c08e7640003a80015ec000d60000000030987cd14000002322112d00062095ad4800a851f5f704400021d14c0f000091b88006d92d08ed33a4c130005b154f1e99280069324907800) else (if i < 20 then 0x1860000032b000b500050aae0819cab67812000000003bd4680708d9e4b129b8610f2f800049d1220f4001c5886000002db9d01c4968008c8000e32ef0009065e0902340000000052e6315953a00000000000000fade55a20015380035a678989e080000151e950c04e2be800504 else 0x1e28000008600055526a360000000007d0fc49a1500000051600141d3a0001dc0025d00056c8f60180058e000eb00094600233ceb8e4928849ac6be6b6bc2b0000be000412001218004749e2000d3a6900021800200000e580035d1ab3bc003901404ca498000da00025c9c))) else (if i < 24 then (if i < 22 then 0x7da002050e80569f0000013f80017729629c002c60015582700079249c6e8b7000002ae45d0b2d444000069f61437cd02b4002a64dc32000000393460000001340001e0a7dae4b25656856349c0069152f000586728a400000081800b70000fe80080ec3571a9200000000000 else (if i < 23 then 0xcead2b6558768c4401671cc1886800b65194002ae42164c004cb00000117bc68e2000000f6876000e5d64000000000005120015c596000001f784620e5b80023e574fa035ba11cc0023aada03b5b2308000000013e4a101e000002b77a6000001e24e00000025e96400000049 else 0xb82e10174e000000443480003d93100008a4494443a4004a752288e4380652d13e59800ac4000d2c815ce0006fa38000000000ef8d0001f0800448000150002fc001bad580008fd7a8ab000562a5bd0000b4a6c3975e510a66800000000dd0000000d8000b6000fa432000)) else (if i < 26 then (if i < 25 then 0x19a0000000024a000000625b04e9801844dc0000e2a4000c0947800ae45014e000000fd800026704d9acc0002260018f8000760002016b7f4001e78db83e001db47863d101e9002a3e55254489052b91060009336340000052b57ebd37d000000083c3756e9169800254229014f0 else 0x14d21447800215ba6a9f49e7c800000002421c4add69942bde872000000002ded52c58e5b368250717600000e1e80083a0500034c0000000043c000000b40820000000000024c0002e000a1800000000a470883b1e500000098800001292661504b6dbdd0000000002a2800) else (if i < 27 then 0x865306a5000132001c698e2580025dace000369542ec7527aa359fb5da5c922cf328c87000000090000000c2b6e00021aee000909f32bc4a034189b343b93640007721f180000007e340cff000a3a92dada833940026107530600000000001426168006dac1000272001520003cc else 0x7a25d3340024f800000001c4da045a00057800b3a00180c274d55b60ab4d0010c2a0163001601a235c43e5cc0000018c7dc000000440016f800)))))

private def loc5 (i : Nat) : Nat := unpack loc5Packed 11 80 i

private def st6Packed (i : Nat) : Nat := (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then 0x1ec594f025c390998800f639cb2a7e5992ec400001ce5950e3c01f520039cb2a1c7812e0fb100000739652cc9707d4800e72ca781664b83ec400001ce3c0971501f520039cb29e04b8a80fb100000594f025c2607d4800f639cb29e04b83ec4007b1ce5950e3c01f62003d8e72ca5992e0fb1001ec738f025c5407d8800f639c871e04b8a8c4007b1ce3c097150266200000e72ca871e00faa00000739652cc9707d50000039c7812e2a03ea800001653c0970981f5400000f639cb29e04baa else (if i < 2 then 0x1ec739463c0971518801183d8e71e04b8a8c4007b1ce594f025c4e62003e0f639cb29e04bb1001ec739af5950e3c18800f635eb29e04b84cc400909ec739652cc9762003d8e72ca7812e00b1000007b1ce594f02595000003d8e72ca7792ea800001ec739643c09754003d8e72ca5992e3bb1002057b1ce594b325d880102bd8b29e04b84cc4007b1ce594f025c0d6200000f61e04b8a8132a000007b1ce594dc25d5000003d8e72a47812ea8007b1ce5950e3c03962003d8e72ca5992e1cb1 else 0x219739653c09707d8bd8e72ca781664b83ee0007b1ce594f025c1862003d8e72ca7d1e04bb100230739653c09707d8800f639cb29e04b83cc4007b1ce595053c09760003d8e727e7812e2a31001ec739653c0970b58800f639c7812e3e0a8c40087dec738f025c5462003d8e71e06992e2a31002197b1ce3c0971518800f639cd79e04b8a8c4007b1d2738f025c54620040af639ca91e04bb1001ec738f025c541358800f83d8e71e04b8a8c5ec73965438f025c5470003d8e72ca7812e2031)) else (if i < 4 then 0x1ec739654fcc125d8801083d8e72ca780eec0007b1ce3c0ac25c5462f639cb29e06712e0fb8000007b1ce594f025d4000e72ca7812e3503ec400739653c0971dc1f6200420e72ca7812e0fb1001ce6b5653c09707d8800e72ca7819c4b83ec400739653e8f025c1f620039cb29e04b83e0db1001cf739653c09707d8800f639cb29e05092ec1ec739653c0970981f700039cb29e04b8f80fb1001ec73dce594f025d880102b9cb29e04b83ec4007b1ce594f028497620039cb29e06992e0fb1 else (if i < 5 then 0x1ec739654dcf025d8800f639cb29e04b8cec6057b1ce5950e3c0977102bd8e72ca7812e1338000007b1ce594dc25d480102bd8e72ca6e12ec5ec739653c0971f01f70003d8e72ca781b84bb1001ec738f025c541018800003d8e72a47812ea400815ec6ed653c09762003d8e7376b29e04bb1001ce594f025c1f0618bd8e72ca9fa1c7812ee000001ec739654fc3952003d8e72ca780f81cb1001ec73965338970e58800f639cb29a64b872c4007f9ec739653c09762f639cb2a7e7812e1338 else 0x842057b1ce594f025dc000f635eb29e06712ec6057b1ce665653c09770000012135eb29e04ba9001ce594f025c2607d8c84f639cb29e05992ee0007b1ce594f025c0160f639cb29e04b8721338002427b1ce594f02598800003d8e72ca7792ea400909ec739653bc976200484f639cb21e04bb1001ec73965590f025d8bd8e72ca7812e3b84ce24287dec739653c09770f639cb2a247812e3bb8001ec739653c0771a988012139cb29e04b83ec400841ec594f025c7762003d8e72ca780f83bb1))) else (if i < 9 then (if i < 7 then 0x7b1d2739653c097151c00102b9cb29e04b8f8c4007b1ce594d325c3960003d8e72ca7812e27307b1ce594f025c54139c000f639cb29e04b89ac0007c1ec739653c09760f639cd7aca871e04bb87b1ce6bd653c0b325dc001083d8e72ca780eec61f7b1ce594f025c1f70003d8e72ca7812e16b07b1ce6bd653c0970b5c000003d8e72c87812ea4007b1ce6b4f025c5462003d8e72ca9fa1c78317b1ce6bd653c097099c000e735eb2a947812ec4007e9ec739653c09762003d8e71e04b8a82731 else (if i < 8 then 0x1ec739653c09707983d8e72ca7812e0f83ce1ec739653c0971dc547000472f639cb29e04bb18d2057b1ce594f025dc3d8e7332b2a7e7812ee000739653c09707c1562f639cb29e04b8d42a387b1ce594f025c7c151c00105bd8e72ca7812ec4007b1ce594f025c1f6102bd8e72ca7812e2a38001ec739653c09710183d8e72ca7812e2a080e1ec739653c0ac25c5470f639cd6aca7812e2a387b1ce594f034c97151c000f639cb29e04b88ec5ec739653c09715047700039cd7aca781a64bb1 else 0x22a7b1ce594f025d83d8e7332b29e04b83ee0007b1ce594f025c1560003d8e71e04b8a823b17b1ce594f02849707dc432f639cb29e04b83ee1ec739653c0ce25c3970f639cb29f47812e0fb87b1ce595463c09707dc420f639cb29e04b8a8e000909ec739653bc9760003d8e72e4b29e04bb0001ec739653c09706d83d8e72e4b29e04b83ee0007b1654fcf025c2663213d8e72ca7812e0fb8815ec739653c0dc25dc000f639cb29e04b8e8c5ec73965414f025c5470f639cb2a7e7812e2a38)) else (if i < 11 then (if i < 10 then 0x7b1ce5953f3c0b325dc000f639cb2a7e6092ec1ec739653c0b325c7770003d8e72ca7812e2a3187dec739654fcf025dc420f639cb29e04b83ee000855ec739653c097630cbd8e72ca9f9e04bb88c1ec739654fcf025dc000f639cb2a387812ec1ec739654fd1c3c0977000486f639cb29e04bb000242739af594f025d8801213d8e71e04b8a8c5ec73965528f025c7770003d8e72ca7812e0ab18a9ec739654fcf025dc44cf639cb2a7e7812ee1ec739654fcf025c1f70003d8e7310b29e04bb1 else 0x8c1ec739653c0970e5c000f639cb29e03b872c5ec739655193f3c09770003d8e7310b29e04bb07b1ce621653c0970e5c000f639cb29e04b86ac5ec739653c0970e4347000416f639cb29e04bb0001ce594f03049707d8bd8e735eb29e06992ee1ec739653c0970e43570003fcf639cb29e04bb07b1ce594f0338971ddc3fcf639cb29e04b872e1ec739655293f3c0977102bd8e72ca7812e06b8815ec739654fcf025dc3d8e72ca9f9e04b8d4e2107b1ce5953f3c09770f639cb2a7e7812e3e38) else (if i < 12 then 0x1ec739653c07c0e583d8e72ca871e04b8eee1ec739653c0971f03970003d8e72e4b29e04bb17b1ce594f0304970e5c3d8e735ab29e04b872e0007b1ce594ce25c39600045af639cb29e04bb1001ec73965448f025d8000f639cb29e04b868c40073972594f025c1f630fbd8e72ca7812e1cb87b1ce594f034c970e5c432f639cb29e04b872e0007b1af594f025c7760f639cb2a8c7812e1cb8001ce6bd653c0971f18c84f639cb29e07792ee2347b1ce594f025c39700039cb2a8c7812e0fb1 else 0x1ec73999594f00e58c84f639cb29e04b802e242841ec739653c09770003d8e7332b29e01cb07b1ce6bd653c097151c3d8e72caa51e04b872e2347b1ce594f025c5470003d8e72ca7812e2fb1001ec739af594b325d8800f639ccbaca7812ec4007b1ce5953f3c06a62003d8e72ca7812e06b07b1ce5953f3c0970e5c3e0f639cb29e04b8a8e0007b1ce595123c09762f639cd6aca9f9e04bb8815ec739653c0b325dc000f635eb2a8c7812ec5ec73999594f025c3970003d8e71e06092e2a31)))) else (if i < 19 then (if i < 16 then (if i < 14 then 0x1ec739653c0970a18800e735eb29e04b8f8c2427b1ce594f025c96711840af639cb29e04bb8000007b1ce548f025d43d8e735eb29e04b8f8e000815ec739523c0976000472f639cb29e04bb0000007b0f025c5409948010fb9cb29e04b83ec400001ec7390e3c054520040af6376b29e04bb0001ec739993c0971518800f639cddaca7812ec1ec739653c0c125c1f7000000f639cb2a7e1ca8002037b1ce594f025d8800003d8e71664b8a8a9ec739653c0971504d710fbd8e72ca7812e2a38 else (if i < 15 then 0x7b1ce5953f49cf025dc40af639cb29e04b8d4e1ec739af595433c09771213d8e72caa51e04bb880dec739653c0971ddc40af639cb29e04b8eee00073999594f025c1f620040af639cb29e03e30001ce5954a3c09707d8c0af639cb29e04b8f8e000909ec73965438f0631a3d8e72ca7812e3bb8000007b1bb594f025d5000f639cb29e04b8a8c1ec739af594f033897711cc0af639cb29e04bb8001ec739652cc971518bd8e72ca781a64b8eee1ec739653c0c125c77711340af639cb29e04bb8 else 0x7b1ce5953f3c0971ddc000f639cb29e03b8d4c2057b1ce594f03389770f639cccaca7812e3bb87b1cf739653c09707dc3d8e735eb29e06092ee1ec739653c0971f077710fbd8e72ca7812e3bb8865ec739653c0971ddc484f639cb29e06992ee0007b1ce594f025c3460003d8e72ca7812e4b31001ec739654dcf025d83d8e72ca9b9e04b8eee1ec73965518f025c7770003d8e72caa19e04bb1001ec6bd653c0971dd8bd8e72ca7812e3b8cee219815ec739653c097700040af639cb29b84bb0)) else (if i < 17 then 0x7b1ce594ef25d4000f639cd6aca4b872c4007b1ce594f03bc9761213d8e72caa31e04bb87b1ce5953f3c09717dc4851a3d8e72ca7812ee1ec739af594f025c1f70003d8e939cb29e04bb190a307b1ce594f025dc000003d8e72c87812ea000909ec739643c09760003d8e72cab21e04bb0001ec739653c0770e58001133d8e72ca7812ec6057b1ce6ed653c09770003d8e72ca939e04bb0909ec739653c097099c000f639cb29e04b850c000001ec738b325c54520039cb2a7e7812e0fb1 else (if i < 18 then 0x909ec73999594f025dc3d8e72ca7812e3b8d4e242815ec739653c09770003d8e72ca7d1e04bb0001ec7394a3c0971518800003d8ddaca7812ea5ec739654fcf0304977102bd8e72ca781a64bb8002427b1ce594f025983d8e72ca7812e35072e1ec739ad594f025c1f71213d8e72ca781824bb8001ec73965438f01518800f639cb29e04b830c1ec739af6b5653c09770003d8e72ca781b84bb08c1ec739653c09707dc4850cbd8e72ca7812ee2427b1ce595643c09770003d8e71e06712e2a31 else 0x7b1ce594f025c770d1c00000484d7aca7812ea000739af5954a3c09760f639cb29e04b8ee1cb88c1ec739653c0971ddc000f639c829e04b8a8c5ec7397c594f025c397000484f635eb29e04bb17b1ce594f025c3907dc432f639cd7aca7812ee0007b1cf739653c09760003d8e72ca7812e2fb0001ec594f025c2607d8800f639cb2a4e7812ec400815ec73965438f063213d8e72ca7812e1cb8000007b1ce594dc25d4000f639cb29e05612ec4007b1ce5953f25c396200420f639c7812e2a31))) else (if i < 22 then (if i < 20 then 0x7b1ce594f025c1f06dc3d8e72ca7812e3b8e8e1ec739af665653c09770003d8d7acaa31e04bb0001ec73965414f025d8bd8e72ca7812e0f830e2107b1ce6bd653c097700039cd7aca7812e0fb17b1ce6bd65518f025dc000f62ca7812e3b84cc6427b1ce5950e3c097711a3d8e735eb29e04bb8865ec739653c097151c000f639c7812e2a072c5ec739af5953f3c09770003d8e72ca781984bb100242739af594f025d8000f639cb2a387812ec5ec739af5954a3c0977102bd8e735ab29e04bb8 else (if i < 21 then 0x7b1ce594f034c9707dc000f639cb2aa47812ec4007b1ce5f1653c09762003d8e72ca9f9e01cb17b1ce594f025c6a07dc3d8e72ca7819c4b8a8e21f7b1ce6bd653c097700039cd7aca781a64bb07b1ce594f02cc970e5c00102bd8e71e04b8a8c4007b1ce595433c09760003d8e71e04b8d42a3190dec739654fcf025dc45af639cd7aca7812ee0007b1ce5952a3c09762003d8e71e05992e2a31000007b1ce594f025d4c84f639cb29e04b8d4e2427b1ce6b5653c09770000012135eb29e04baa else 0x1ec739653c0971d18000003d8ddaca7812ea00090dec739653c0976200000f639cb29e04b2982dec739653c0970e5c000f639cb29e05612ec000855ec739653c0976102bd8e72ca7812e1cb8001ec739654a8f025d83d8e72ca871e04b83ee2347b1ce5953f3c09770f639cb2a1c7812e1cb8001ec6bd653c0ce25d840af639cb2a947812ee1ec739653c09715026700045af639cb29e04bb0002347b1ce3c0971518c60f639cb29e04b8a8e0007b1ce594f025c6760f639cb2a8c7812e2a38)) else (if i < 24 then (if i < 23 then 0x7b1ce6bd653c0971ddc484f639cb29e04b8a8e2427b1ce594f025c7c70f639cb2a7e951e04bb8002427b1653c0970998800f639cb29e03e0eec1ec739653c0c125c5470003d8e72caa91e04bb0002057b1ce594f01f18800fd3d8e72ca7812ec2427b1ce594f033897711a3d8e72ca7812e0fb8001ec739ad594970e583d8e72caa51e04b83ee1ec73999594f025c547000484f635eb29e04bb0815ec739af594f025dc3d8e72ca7812e0f82ae0007b1ce594f03309760f639cd7aca781984bb8 else 0x1ec73997594f025d8484f639cd7aca7812ee1ec73997594f025c7770f639cd7aca7812e3a3800234739653c09707d8c60f639cd7aca7812ee0007b1ce594f025c47600039cb29e04b83e0f317b1ce5953f3c0d325dc3d8e72ca7812e2a072e0007b1ce594f025c3560fd3d8e735eb29e04bb8909ec739654fcf025dc000f639cb2a7e4b872c000899ec739653c09760003d8e72ca7812e26b1855ec739af594f025dc000f639cb29e04b836c6057b1ce595463c09770003d8e939cb29e04bb0) else (if i < 25 then 0x7b1ce6bd653c0970e5c3d8e735ab29e04b8eee0007b1ce5953f3c06a60f639cb2a947812e2a380022a7b1ce594f025d8800003d8e72ca7812ca000001ec7390e3c05454f639cb29e05992e2a38000007b1ce5953f0e55000f639cb2a7e78072c0007b1ce594f025c9660003d8e72ca781de4bb1001ec594f025c540998bd8e72ca7812e2a03ee2107b1ce594f025c77700039cb29e04b8720fb1001ce594f02849707d8c0af639cb29e06092ee2427b1ce594f025c7770f639cd7aca7812e3538 else 0xf639c7812e3b8a8c4007b1ce5f1653c0976102bd8e72ca7812e0fb87b1ce5953f3c0ce25dc3d8e72ca7812e3b83ee0007b1ce5950e3c0776200406f639cb29e04bb087e057b1ce594f025dc40af639cb2aa47812ee1ec739653c0970e42871083d8e72ca7812e1cb8)))))

private def st6 (i : Nat) : Nat := unpack st6Packed 77 20 i

private def adj6Packed (i : Nat) : Nat := (if i < 1 then 0x8086800008080020486701da231093088000816001023394a010c0d101e0a0062000c0681060882348026200004002621005 else (if i < 2 then 0xb844018001014003802a205201144f4180a19c00018a020ea511b01110a3110a058080000243142818da019c0208460700a0 else 0x84091a01009c80))

private def adj6 (i : Nat) : Nat := unpack adj6Packed 5 80 i

private def loc6Packed (i : Nat) : Nat := (if i < 5 then (if i < 2 then (if i < 1 then 0x8584c0176ebedd80005483000ce1d802e0b6cb800012ac130aa3dc004c664003e803e000002929e002600315d21a0013111e28000000300014ab1007341da84672cb6d5000013400778000195efe900e00ba000b900c0000b473 else 0x24284628f004388600bf375a6000078000009a001c609e48000000007d00191b7801617500210013a00002ba39007fab872b892401857dd5de4008d991ca850caf332a60000000ac004dbce000000001e8006e9e6ecf51ef7abb) else (if i < 3 then 0x4709d2c0030b7266d62b7e4012d9c15000bf8980001de90002a5ab00195fd1d8a7579075001c400748f88929092313e200000318008d006340000003b45af0d36aac7fa73000000000000ec296bc377edb00135f8d80065b73bc else (if i < 4 then 0xd80a0038f6780001e6838028cae0f2a3191a00504cd2807808897300550004e55d345c1c00000117fb25affaf4a18fc00cb0000000df4cd1ef83ad894c01980038094005c000a0004047bb7a0000000000000030c0600003f000 else 0x16002c20040f840069dc498fc82003780077183d8423c7adb1680000001dc0000001fff100001860017fb36777000007bf78b8027600c2003060d7c1bd20ea2380000c8003066000b541b590301d4c0000000025d42828003000))) else (if i < 7 then (if i < 6 then 0x5f70401b5eb0946e00bd0021055006b914000000215c2001b40166d3802b3c40000167390014bb15bd6d790c36005140000001ead200bc0002b0145bae32d40053000000004bbabd4489000b513000367c001b26e970026f6400 else 0x5ed9242003a2b15a500af36b9002c8bc00a4cf76c00b2ed000f7e8d5b1000001c000d90062c00350000028fa43803980000541b5ce90801c467ca31eaa000033401eb9e4d58ab751528b09ff700252e11000001a20000016a7) else (if i < 8 then 0x3a6fd37001c832cf800f040d0c480123002ab47870d3a401a968eec2291007902000f4d8a8000af9e48b1c2f8038ecc788024f02bc874d522b68025600738021fcff19ad7572b70000000f107c00570000001c30041000c4 else (if i < 9 then 0x4ac60d05100002590c0b003e78e118033c00a27180000df4fe2bfcd2803b3930000000938b00000d00000001fb41c94c6afbe800007ff6fd47c0400003cbda97d8097814e800019a002700a41cefd8013e000cc54000018801ca else 0x5d000011000007433800ea7000059a459c00000002b5f4b0000125680bfbd94006964800387ca7800a3a76255a00c87c80000004900000))))

private def loc6 (i : Nat) : Nat := unpack loc6Packed 9 80 i

private def st7Packed (i : Nat) : Nat := (if i < 1 then 0x909ec739653c09760f639cb29e04b83ec9ec739af594f025d8c0af639cb29e04bb07b1ce594f025c3960f639cb29e04b872c4007b1ce3c0971515bd8e72ca9f9e04bb0001ce594f025c1f55213d8e72ca7812ec800739653c09707d5c0af639cb29e04bb17b1ce5953f3c09764f639cb2a7e7812ec400739653c09707d4bd8e72ca7812e0fb1815ec739653c09764f639cb29e04b872c8007b1ce3c09715153d8e72ca7812e2a32 else 0x2427b1ce594f025d8bd8e72ca7812e2a317b1ce6bd653c09760f639cb29e04b8eec9ec739653c09707d83d8e735eb29e04bb2001ec738f025c5452f639cb29e04b8a8c1ec739653c0971dd8bd8e72ca7812e3bb0)

private def st7 (i : Nat) : Nat := unpack st7Packed 67 20 i

private def adj7Packed (_i : Nat) : Nat := 0x9b0b0405

private def adj7 (i : Nat) : Nat := unpack adj7Packed 3 80 i

private def loc7Packed (_i : Nat) : Nat := 0x22532f800601782680d0015eb41641c00981ead8192c80207000400062

private def loc7 (i : Nat) : Nat := unpack loc7Packed 5 80 i

private def certCount : Nat → Nat
  | 2 => 21
  | 3 => 254
  | 4 => 1056
  | 5 => 1467
  | 6 => 511
  | 7 => 30
  | _ => 0

private def certSizes : Nat → Nat × Nat
  | 2 => (11,37)
  | 3 => (89,383)
  | 4 => (353,1597)
  | 5 => (491,2203)
  | 6 => (173,769)
  | 7 => (11,47)
  | _ => (1,2)

private def stData : Nat → Nat → Nat
  | 2 => st2
  | 3 => st3
  | 4 => st4
  | 5 => st5
  | 6 => st6
  | 7 => st7
  | _ => fun _ => 0

private def adjData : Nat → Nat → Nat
  | 2 => adj2
  | 3 => adj3
  | 4 => adj4
  | 5 => adj5
  | 6 => adj6
  | 7 => adj7
  | _ => fun _ => 0

private def locData : Nat → Nat → Nat
  | 2 => loc2
  | 3 => loc3
  | 4 => loc4
  | 5 => loc5
  | 6 => loc6
  | 7 => loc7
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
private lemma cert2_0 : checkCert 2 0 21 = true := by decide +kernel

private lemma certLayer2 : checkCert 2 0 (certCount 2) = true :=
  cert2_0

set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert3_0 : checkCert 3 0 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert3_32 : checkCert 3 32 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert3_64 : checkCert 3 64 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert3_96 : checkCert 3 96 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert3_128 : checkCert 3 128 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert3_160 : checkCert 3 160 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert3_192 : checkCert 3 192 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert3_224 : checkCert 3 224 30 = true := by decide +kernel

private lemma certLayer3 : checkCert 3 0 (certCount 3) = true :=
  (joinCert 3 0 128 126 (joinCert 3 0 64 64 (joinCert 3 0 32 32 cert3_0 cert3_32) (joinCert 3 64 32 32 cert3_64 cert3_96)) (joinCert 3 128 64 62 (joinCert 3 128 32 32 cert3_128 cert3_160) (joinCert 3 192 32 30 cert3_192 cert3_224)))

set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_0 : checkCert 4 0 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_32 : checkCert 4 32 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_64 : checkCert 4 64 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_96 : checkCert 4 96 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_128 : checkCert 4 128 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_160 : checkCert 4 160 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_192 : checkCert 4 192 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_224 : checkCert 4 224 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_256 : checkCert 4 256 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_288 : checkCert 4 288 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_320 : checkCert 4 320 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_352 : checkCert 4 352 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_384 : checkCert 4 384 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_416 : checkCert 4 416 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_448 : checkCert 4 448 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_480 : checkCert 4 480 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_512 : checkCert 4 512 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_544 : checkCert 4 544 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_576 : checkCert 4 576 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_608 : checkCert 4 608 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_640 : checkCert 4 640 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_672 : checkCert 4 672 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_704 : checkCert 4 704 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_736 : checkCert 4 736 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_768 : checkCert 4 768 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_800 : checkCert 4 800 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_832 : checkCert 4 832 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_864 : checkCert 4 864 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_896 : checkCert 4 896 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_928 : checkCert 4 928 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_960 : checkCert 4 960 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_992 : checkCert 4 992 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_1024 : checkCert 4 1024 32 = true := by decide +kernel

private lemma certLayer4 : checkCert 4 0 (certCount 4) = true :=
  (joinCert 4 0 512 544 (joinCert 4 0 256 256 (joinCert 4 0 128 128 (joinCert 4 0 64 64 (joinCert 4 0 32 32 cert4_0 cert4_32) (joinCert 4 64 32 32 cert4_64 cert4_96)) (joinCert 4 128 64 64 (joinCert 4 128 32 32 cert4_128 cert4_160) (joinCert 4 192 32 32 cert4_192 cert4_224))) (joinCert 4 256 128 128 (joinCert 4 256 64 64 (joinCert 4 256 32 32 cert4_256 cert4_288) (joinCert 4 320 32 32 cert4_320 cert4_352)) (joinCert 4 384 64 64 (joinCert 4 384 32 32 cert4_384 cert4_416) (joinCert 4 448 32 32 cert4_448 cert4_480)))) (joinCert 4 512 256 288 (joinCert 4 512 128 128 (joinCert 4 512 64 64 (joinCert 4 512 32 32 cert4_512 cert4_544) (joinCert 4 576 32 32 cert4_576 cert4_608)) (joinCert 4 640 64 64 (joinCert 4 640 32 32 cert4_640 cert4_672) (joinCert 4 704 32 32 cert4_704 cert4_736))) (joinCert 4 768 128 160 (joinCert 4 768 64 64 (joinCert 4 768 32 32 cert4_768 cert4_800) (joinCert 4 832 32 32 cert4_832 cert4_864)) (joinCert 4 896 64 96 (joinCert 4 896 32 32 cert4_896 cert4_928) (joinCert 4 960 32 64 cert4_960 (joinCert 4 992 32 32 cert4_992 cert4_1024))))))

set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_0 : checkCert 5 0 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_32 : checkCert 5 32 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_64 : checkCert 5 64 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_96 : checkCert 5 96 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_128 : checkCert 5 128 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_160 : checkCert 5 160 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_192 : checkCert 5 192 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_224 : checkCert 5 224 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_256 : checkCert 5 256 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_288 : checkCert 5 288 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_320 : checkCert 5 320 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_352 : checkCert 5 352 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_384 : checkCert 5 384 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_416 : checkCert 5 416 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_448 : checkCert 5 448 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_480 : checkCert 5 480 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_512 : checkCert 5 512 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_544 : checkCert 5 544 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_576 : checkCert 5 576 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_608 : checkCert 5 608 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_640 : checkCert 5 640 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_672 : checkCert 5 672 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_704 : checkCert 5 704 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_736 : checkCert 5 736 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_768 : checkCert 5 768 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_800 : checkCert 5 800 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_832 : checkCert 5 832 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_864 : checkCert 5 864 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_896 : checkCert 5 896 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_928 : checkCert 5 928 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_960 : checkCert 5 960 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_992 : checkCert 5 992 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_1024 : checkCert 5 1024 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_1056 : checkCert 5 1056 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_1088 : checkCert 5 1088 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_1120 : checkCert 5 1120 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_1152 : checkCert 5 1152 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_1184 : checkCert 5 1184 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_1216 : checkCert 5 1216 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_1248 : checkCert 5 1248 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_1280 : checkCert 5 1280 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_1312 : checkCert 5 1312 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_1344 : checkCert 5 1344 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_1376 : checkCert 5 1376 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_1408 : checkCert 5 1408 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_1440 : checkCert 5 1440 27 = true := by decide +kernel

private lemma certLayer5 : checkCert 5 0 (certCount 5) = true :=
  (joinCert 5 0 736 731 (joinCert 5 0 352 384 (joinCert 5 0 160 192 (joinCert 5 0 64 96 (joinCert 5 0 32 32 cert5_0 cert5_32) (joinCert 5 64 32 64 cert5_64 (joinCert 5 96 32 32 cert5_96 cert5_128))) (joinCert 5 160 96 96 (joinCert 5 160 32 64 cert5_160 (joinCert 5 192 32 32 cert5_192 cert5_224)) (joinCert 5 256 32 64 cert5_256 (joinCert 5 288 32 32 cert5_288 cert5_320)))) (joinCert 5 352 192 192 (joinCert 5 352 96 96 (joinCert 5 352 32 64 cert5_352 (joinCert 5 384 32 32 cert5_384 cert5_416)) (joinCert 5 448 32 64 cert5_448 (joinCert 5 480 32 32 cert5_480 cert5_512))) (joinCert 5 544 96 96 (joinCert 5 544 32 64 cert5_544 (joinCert 5 576 32 32 cert5_576 cert5_608)) (joinCert 5 640 32 64 cert5_640 (joinCert 5 672 32 32 cert5_672 cert5_704))))) (joinCert 5 736 352 379 (joinCert 5 736 160 192 (joinCert 5 736 64 96 (joinCert 5 736 32 32 cert5_736 cert5_768) (joinCert 5 800 32 64 cert5_800 (joinCert 5 832 32 32 cert5_832 cert5_864))) (joinCert 5 896 96 96 (joinCert 5 896 32 64 cert5_896 (joinCert 5 928 32 32 cert5_928 cert5_960)) (joinCert 5 992 32 64 cert5_992 (joinCert 5 1024 32 32 cert5_1024 cert5_1056)))) (joinCert 5 1088 192 187 (joinCert 5 1088 96 96 (joinCert 5 1088 32 64 cert5_1088 (joinCert 5 1120 32 32 cert5_1120 cert5_1152)) (joinCert 5 1184 32 64 cert5_1184 (joinCert 5 1216 32 32 cert5_1216 cert5_1248))) (joinCert 5 1280 96 91 (joinCert 5 1280 32 64 cert5_1280 (joinCert 5 1312 32 32 cert5_1312 cert5_1344)) (joinCert 5 1376 32 59 cert5_1376 (joinCert 5 1408 32 27 cert5_1408 cert5_1440))))))

set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_0 : checkCert 6 0 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_32 : checkCert 6 32 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_64 : checkCert 6 64 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_96 : checkCert 6 96 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_128 : checkCert 6 128 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_160 : checkCert 6 160 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_192 : checkCert 6 192 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_224 : checkCert 6 224 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_256 : checkCert 6 256 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_288 : checkCert 6 288 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_320 : checkCert 6 320 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_352 : checkCert 6 352 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_384 : checkCert 6 384 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_416 : checkCert 6 416 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_448 : checkCert 6 448 32 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_480 : checkCert 6 480 31 = true := by decide +kernel

private lemma certLayer6 : checkCert 6 0 (certCount 6) = true :=
  (joinCert 6 0 256 255 (joinCert 6 0 128 128 (joinCert 6 0 64 64 (joinCert 6 0 32 32 cert6_0 cert6_32) (joinCert 6 64 32 32 cert6_64 cert6_96)) (joinCert 6 128 64 64 (joinCert 6 128 32 32 cert6_128 cert6_160) (joinCert 6 192 32 32 cert6_192 cert6_224))) (joinCert 6 256 128 127 (joinCert 6 256 64 64 (joinCert 6 256 32 32 cert6_256 cert6_288) (joinCert 6 320 32 32 cert6_320 cert6_352)) (joinCert 6 384 64 63 (joinCert 6 384 32 32 cert6_384 cert6_416) (joinCert 6 448 32 31 cert6_448 cert6_480))))

set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert7_0 : checkCert 7 0 30 = true := by decide +kernel

private lemma certLayer7 : checkCert 7 0 (certCount 7) = true :=
  cert7_0


private lemma allChecked (k : Nat) (hk : k ≤ 7) (i : Nat) (hi : i < certCount k) :
    runCheck certCount certState certLocate k i = true := by
  have h : checkCert k 0 (certCount k) = true := by
    have hc : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rfl
    · rfl
    · exact certLayer2
    · exact certLayer3
    · exact certLayer4
    · exact certLayer5
    · exact certLayer6
    · exact certLayer7
  exact checkBatch_at h i (Nat.zero_le i) (by simpa only [Nat.zero_add] using hi)

private lemma noLiveAt7 (r : SearchState)
    (h : checkLink certCount certState certLocate 7 r = true) :
    ∀ m ≤ 7, ¬ Live m r.1 r.2.toFinset := by
  intro m hm hl
  simp only [checkLink, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨hi,ht⟩,hw⟩ := h
  have he := sameWires_sound hw
  rw [ht,he] at hl
  exact runCheck_complete (allChecked) 7 (by decide) _ hi m hm hl

set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma tableLinks0 :
    frontier0_1.all (checkLink certCount certState certLocate 7) = true := by decide +kernel

private lemma excluded0 : ∀ k ≤ 8, ¬ Live k 0 rawLow.toFinset := by
  intro k hk
  have rest : ∀ r ∈ frontier0_1, ∀ m ≤ 7, ¬ Live m r.1 r.2.toFinset := by
    intro r hr
    exact noLiveAt7 r (List.all_eq_true.mp tableLinks0 r hr)
  exact (noLive_layer layer0_1 (by decide +kernel) rest) (0,rawLow)
    (by simp [roots0]) k hk

set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma tableLinks1 :
    frontier1_1.all (checkLink certCount certState certLocate 7) = true := by decide +kernel

private lemma excluded1 : ∀ k ≤ 8, ¬ Live k 1 rawLow.toFinset := by
  intro k hk
  have rest : ∀ r ∈ frontier1_1, ∀ m ≤ 7, ¬ Live m r.1 r.2.toFinset := by
    intro r hr
    exact noLiveAt7 r (List.all_eq_true.mp tableLinks1 r hr)
  exact (noLive_layer layer1_1 (by decide +kernel) rest) (1,rawLow)
    (by simp [roots1]) k hk

set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma tableLinks2 :
    frontier2_1.all (checkLink certCount certState certLocate 7) = true := by decide +kernel

private lemma excluded2 : ∀ k ≤ 8, ¬ Live k 2 rawLow.toFinset := by
  intro k hk
  have rest : ∀ r ∈ frontier2_1, ∀ m ≤ 7, ¬ Live m r.1 r.2.toFinset := by
    intro r hr
    exact noLiveAt7 r (List.all_eq_true.mp tableLinks2 r hr)
  exact (noLive_layer layer2_1 (by decide +kernel) rest) (2,rawLow)
    (by simp [roots2]) k hk

set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma tableLinks3 :
    frontier3_1.all (checkLink certCount certState certLocate 7) = true := by decide +kernel

private lemma excluded3 : ∀ k ≤ 8, ¬ Live k 3 rawLow.toFinset := by
  intro k hk
  have rest : ∀ r ∈ frontier3_1, ∀ m ≤ 7, ¬ Live m r.1 r.2.toFinset := by
    intro r hr
    exact noLiveAt7 r (List.all_eq_true.mp tableLinks3 r hr)
  exact (noLive_layer layer3_1 (by decide +kernel) rest) (3,rawLow)
    (by simp [roots3]) k hk

set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma tableLinks4 :
    frontier4_1.all (checkLink certCount certState certLocate 7) = true := by decide +kernel

private lemma excluded4 : ∀ k ≤ 8, ¬ Live k 4 rawLow.toFinset := by
  intro k hk
  have rest : ∀ r ∈ frontier4_1, ∀ m ≤ 7, ¬ Live m r.1 r.2.toFinset := by
    intro r hr
    exact noLiveAt7 r (List.all_eq_true.mp tableLinks4 r hr)
  exact (noLive_layer layer4_1 (by decide +kernel) rest) (4,rawLow)
    (by simp [roots4]) k hk


theorem lowImpossible {k t : Nat} (hk : k ≤ 8) (ht : t ≤ 4) :
    ¬ Live k t rawLow.toFinset := by
  have ht' : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 := by omega
  rcases ht' with rfl | rfl | rfl | rfl | rfl
  · exact excluded0 k hk
  · exact excluded1 k hk
  · exact excluded2 k hk
  · exact excluded3 k hk
  · exact excluded4 k hk

theorem lower (b : Bool) (s : ℕ) (h : HasCircuitSize 5 (graph b) s) : 9 ≤ s := by
  obtain ⟨C, legal, cap, correct⟩ := h
  by_contra! hsmall
  have rid : List.ofFn (fun j : Fin 5 => (raw b).getD j zero) = raw b := by
    cases b <;> decide +kernel
  obtain ⟨k,t,S,hk,hc,hbin,hl,hsub⟩ :=
    extract C.gates (raw b) legal (circuit_target b (raw b) rid (sampleCorrect b) C legal correct)
  have eq := necessary (raw b) (by cases b <;> decide +kernel) hl hsub
  have sc : S.card = 5 := by
    rw [←eq]
    cases b <;> decide +kernel
  have hs := (live_size hl).2
  change C.gates.length ≤ s at cap
  have hk8 : k ≤ 8 := by omega
  have ht4 : t ≤ 4 := by omega
  rw [←eq] at hl
  cases b
  · exact lowImpossible hk8 ht4 hl
  · have h2 := live_dual hl
    rw [raw_dual] at h2
    exact lowImpossible hk8 ht4 h2

def big (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4276676840 * 2 ^ 32 + 3907577984) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem pinEq : ∀ (i : Fin 6), i.val < 3 → ∀ b : Bool,
    (fun y : Fin 5 → Bool => big (Fin.insertNth i b y)) = graph b := by
  decide +kernel

theorem cofactorLower (i : Fin 6) (hi : i.val < 3) (b : Bool) (s : ℕ)
    (h : HasCircuitSize 5 (fun y : Fin 5 → Bool => big (Fin.insertNth i b y)) s) : 9 ≤ s := by
  rw [pinEq i hi b] at h
  exact lower b s h

end PEqualNP.Outside.L_meta_12302.Core

namespace PEqualNP.Outside.L_meta_12302

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or,[0,2]⟩, ⟨.or,[4,5]⟩, ⟨.or,[3,7]⟩, ⟨.and,[6,8]⟩,
    ⟨.or,[1,9]⟩, ⟨.and,[4,5]⟩, ⟨.and,[3,11]⟩, ⟨.and,[1,9]⟩,
    ⟨.and,[0,2]⟩, ⟨.or,[12,14]⟩, ⟨.and,[10,15]⟩, ⟨.or,[13,16]⟩], 17⟩

lemma mono : Monotone2 witness := by simp [witness, Monotone2]

set_option maxHeartbeats 0 in
lemma witnessCorrect : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = FirstGate.f x := by
  decide +kernel

end PEqualNP.Outside.L_meta_12302

open PEqualNP.Outside.L_meta_12302 in
theorem PEqualNP.Outside.L_meta_12302 :
∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676840 * 2 ^ 32 + 3907577984) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676840 * 2 ^ 32 + 3907577984) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  change ∀ s, PEqualNP.MetaComplexity.HasCircuitSize 6 FirstGate.f s → _
  intro s h
  have hl := FirstGate.structural Core.cofactorLower s h
  exact ⟨witness, mono, (show witness.size = 12 by decide) ▸ hl, witnessCorrect⟩
