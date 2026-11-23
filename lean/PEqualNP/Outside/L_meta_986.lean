import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_986

open PEqualNP.CircuitLowerBounds

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

private theorem foldl_step_length (G : List Gate) (w : List Bool) :
    (G.foldl step w).length = w.length + G.length := by
  induction G generalizing w with
  | nil => simp
  | cons g G ih => rw [List.foldl_cons, ih]; simp [step]; omega

private theorem getD_append_lt (l l' : List Bool) (i : ℕ) (hi : i < l.length) :
    (l ++ l').getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private theorem getD_of_length_le (l : List Bool) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

private theorem foldl_step_getD (G : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (G.foldl step w).getD i false = w.getD i false := by
  induction G generalizing w with
  | nil => rfl
  | cons g G ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    exact getD_append_lt _ _ _ hi

private theorem foldl_step_getD_gate (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl step w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i => ((G.take t).foldl step w).getD i false) := by
  have hsplit : G = G.take t ++ G[t] :: G.drop (t + 1) := by
    simp [List.take_append_drop]
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  rw [foldl_step_getD _ _ _ (by simp only [step, List.length_append, List.length_singleton, foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp only [step]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp only [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp [foldl_step_length, Nat.min_eq_left ht.le]

private theorem foldl_take_getD (G : List Gate) (w : List Bool) (t i : ℕ)
    (hi : i < ((G.take t).foldl step w).length) :
    (G.foldl step w).getD i false = ((G.take t).foldl step w).getD i false := by
  conv_lhs => rw [← List.take_append_drop t G, List.foldl_append]
  exact foldl_step_getD _ _ _ hi

private theorem gate_value (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl step w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i =>
        if i < w.length + t then (G.foldl step w).getD i false else false) := by
  rw [foldl_step_getD_gate G w t ht]
  congr 1
  apply List.map_congr_left
  intro i _
  have hlen : ((G.take t).foldl step w).length = w.length + t := by
    rw [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]
  split_ifs with h
  · exact (foldl_take_getD G w t i (by rw [hlen]; exact h)).symm
  · exact getD_of_length_le _ _ (by rw [hlen]; omega)

private def val (C : Circuit) (n : ℕ) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

private theorem val_input (C : Circuit) (n : ℕ) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val C n x w = x ⟨w, hw⟩ := by
  unfold val
  rw [wires_eq, foldl_step_getD _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

private theorem val_none (C : Circuit) (n : ℕ) (x : Fin n → Bool) (j : ℕ)
    (hg : C.gates[j]? = none) : val C n x (n + j) = false := by
  unfold val
  apply getD_of_length_le
  rw [wires_eq, foldl_step_length]
  have := List.getElem?_eq_none_iff.mp hg
  simp only [List.length_ofFn]
  omega

private theorem val_gate (C : Circuit) (n : ℕ) (x : Fin n → Bool) (j : ℕ) (h : Gate)
    (hg : C.gates[j]? = some h) :
    val C n x (n + j) =
      h.op.eval (h.inputs.map fun i => if i < n + j then val C n x i else false) := by
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hg
  have := gate_value C.gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at this
  exact this

private theorem val_or (C : Circuit) (n : ℕ) (x : Fin n → Bool) (j : ℕ) (h : Gate)
    (hg : C.gates[j]? = some h) (hop : h.op = GateOp.or) :
    val C n x (n + j) = true ↔ ∃ w ∈ h.inputs, w < n + j ∧ val C n x w = true := by
  rw [val_gate C n x j h hg, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
  constructor
  · rintro ⟨w, hw, hv⟩
    by_cases hlt : w < n + j
    · exact ⟨w, hw, hlt, by simpa [hlt] using hv⟩
    · simp [hlt] at hv
  · rintro ⟨w, hw, hlt, hv⟩
    exact ⟨w, hw, by simpa [hlt] using hv⟩

private theorem val_and (C : Circuit) (n : ℕ) (x : Fin n → Bool) (j : ℕ) (h : Gate)
    (hg : C.gates[j]? = some h) (hop : h.op = GateOp.and) :
    val C n x (n + j) = true ↔ ∀ w ∈ h.inputs, w < n + j ∧ val C n x w = true := by
  rw [val_gate C n x j h hg, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id]
  constructor
  · intro hall w hw
    have hv := hall w hw
    by_cases hlt : w < n + j
    · exact ⟨hlt, by simpa [hlt] using hv⟩
    · simp [hlt] at hv
  · intro hall w hw
    obtain ⟨hlt, hv⟩ := hall w hw
    simpa [hlt] using hv

private def bits {n : ℕ} (s : Finset (Fin n)) : Fin n → Bool :=
  fun i => decide (i ∈ s)

private lemma val_mono (C : Circuit) {n : ℕ} (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (i : ℕ) : val C n x i = true → val C n y i = true := by
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hx
    by_cases hin : i < n
    · rw [val_input C n x i hin] at hx
      rw [val_input C n y i hin]
      exact hxy _ hx
    · obtain ⟨j, rfl⟩ : ∃ j, i = n + j := ⟨i - n, by omega⟩
      cases hg : C.gates[j]? with
      | none => rw [val_none C n x j hg] at hx; contradiction
      | some g =>
        rcases hC g (List.mem_of_getElem? hg) with ha | ho
        · rw [val_and C n x j g hg ha] at hx
          rw [val_and C n y j g hg ha]
          intro w hw
          obtain ⟨hlt, hv⟩ := hx w hw
          exact ⟨hlt, ih w hlt hv⟩
        · rw [val_or C n x j g hg ho] at hx
          rw [val_or C n y j g hg ho]
          obtain ⟨w, hw, hlt, hv⟩ := hx
          exact ⟨w, hw, hlt, ih w hlt hv⟩

private def replaceNot (g : Gate) : Gate :=
  match g.op with
  | .not => ⟨.and, []⟩
  | _ => g

private def forced (C : Circuit) : Circuit :=
  ⟨C.gates.map replaceNot, C.output⟩

private theorem forced_get (C : Circuit) (j : ℕ) (g : Gate) (h : C.gates[j]? = some g) :
    (forced C).gates[j]? = some (replaceNot g) := by
  simp [forced, List.getElem?_map, h]

private theorem forced_none (C : Circuit) (j : ℕ) (h : C.gates[j]? = none) :
    (forced C).gates[j]? = none := by
  simp [forced, List.getElem?_map, h]

private theorem replace_not_true (C : Circuit) {n : ℕ} (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (h : C.gates[j]? = some g) (hn : g.op = .not) :
    val (forced C) n x (n+j) = true := by
  rw [val_gate _ _ _ _ _ (forced_get C j g h)]
  simp [replaceNot, hn, GateOp.eval]

private theorem same_at (C : Circuit) {n : ℕ} (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (h : C.gates[j]? = some g) (hn : g.op ≠ .not)
    (his : ∀ i < n+j, val C n x i = val (forced C) n x i) :
    val C n x (n+j) = val (forced C) n x (n+j) := by
  have he : replaceNot g = g := by
    unfold replaceNot
    split <;> simp_all
  have ht := forced_get C j g h
  rw [he] at ht
  rw [val_gate _ _ _ _ _ h, val_gate _ _ _ _ _ ht]
  congr 1
  apply List.map_congr_left
  intro i _
  split_ifs with hi
  · exact his i hi
  · rfl

private theorem forced_ge (C : Circuit) {n : ℕ} (x : Fin n → Bool)
    (hG : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or ∨ g.op = .not)
    (w : ℕ) : val C n x w = true → val (forced C) n x w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hx
    by_cases hn : w < n
    · simpa [val_input C n x w hn, val_input (forced C) n x w hn] using hx
    obtain ⟨j, rfl⟩ : ∃ j, w = n+j := ⟨w-n, by omega⟩
    cases hg : C.gates[j]? with
    | none => rw [val_none _ _ _ _ hg] at hx; contradiction
    | some g =>
      have hget := forced_get C j g hg
      rcases hG g (List.mem_of_getElem? hg) with ha | ho | hn
      · have he : replaceNot g = g := by simp [replaceNot, ha]
        rw [he] at hget
        rw [val_and _ _ _ _ _ hget ha]
        intro i hi
        obtain ⟨hi', hv⟩ := (val_and _ _ _ _ _ hg ha).mp hx i hi
        exact ⟨hi', ih i hi' hv⟩
      · have he : replaceNot g = g := by simp [replaceNot, ho]
        rw [he] at hget
        obtain ⟨i, hi, hi', hv⟩ := (val_or _ _ _ _ _ hg ho).mp hx
        exact (val_or _ _ _ _ _ hget ho).mpr ⟨i,hi,hi',ih i hi' hv⟩
      · exact replace_not_true C x j g hg hn

private theorem forced_eq (C : Circuit) {n : ℕ} (x : Fin n → Bool)
    (i0 : Fin C.gates.length) (hw : ℕ)
    (onlyNot : ∀ q : Fin C.gates.length, (C.gates.get q).op = .not → q = i0)
    (hhead : (C.gates.get i0).inputs.head? = some hw) (hprev : hw < n+i0.val)
    (hzero : val C n x hw = false) (w : ℕ) :
    val C n x w = val (forced C) n x w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hinput : w < n
    · rw [val_input _ _ _ _ hinput, val_input _ _ _ _ hinput]
    obtain ⟨j, rfl⟩ : ∃ j, w = n+j := ⟨w-n, by omega⟩
    cases hg : C.gates[j]? with
    | none => rw [val_none _ _ _ _ hg, val_none _ _ _ _ (forced_none C j hg)]
    | some g =>
      by_cases hn : g.op = .not
      · obtain ⟨hj, hget⟩ := List.getElem?_eq_some_iff.mp hg
        have he := onlyNot ⟨j,hj⟩ (by simpa [hget] using hn)
        have hj0 : j = i0.val := congrArg Fin.val he
        have hfirst : g.inputs.head? = some hw := by
          rw [← hget]
          change (C.gates.get ⟨j,hj⟩).inputs.head? = some hw
          rw [he]
          exact hhead
        rw [replace_not_true C x j g hg hn, val_gate C n x j g hg, hn]
        cases hs : g.inputs with
        | nil => simp [hs] at hfirst
        | cons t ts =>
          simp [hs] at hfirst
          subst t
          simp [GateOp.eval, hzero, hj0, hprev]
      · exact same_at C x j g hg hn (fun i hi => ih i hi)

open Finset

private theorem trace {α : Type*} [DecidableEq α] (alive : ℕ → Finset α)
    (low : ℕ → Prop)
    (split : ∀ i, low i → 2 ≤ (alive i).card →
      ∃ kids : Finset ℕ, kids.card ≤ 2 ∧
        (∀ j ∈ kids, j < i ∧ low j) ∧ alive i ⊆ kids.biUnion alive)
    (k : ℕ) (ob : Finset ℕ) (hbound : ∀ i ∈ ob, i < k ∧ low i) :
    ∃ charged : Finset ℕ,
      (∀ i ∈ charged, i < k ∧ low i ∧ 2 ≤ (alive i).card) ∧
      (ob.biUnion alive).card ≤ ob.card + charged.card := by
  classical
  induction k generalizing ob with
  | zero =>
    have he : ob = ∅ := Finset.eq_empty_iff_forall_notMem.mpr
      (fun i hi => Nat.not_lt_zero i (hbound i hi).1)
    subst ob
    exact ⟨∅, by simp, by simp⟩
  | succ k ih =>
    by_cases hk : k ∈ ob
    · let rest := ob.erase k
      have hrest : ∀ i ∈ rest, i < k ∧ low i := by
        intro i hi
        obtain ⟨hne,hmem⟩ := Finset.mem_erase.mp hi
        obtain ⟨hlt,hlow⟩ := hbound i hmem
        exact ⟨by omega, hlow⟩
      have hc : rest.card + 1 = ob.card := Finset.card_erase_add_one hk
      have hob : insert k rest = ob := Finset.insert_erase hk
      by_cases hr : 2 ≤ (alive k).card
      · obtain ⟨kids, hkcard, hkids, hcover⟩ := split k (hbound k hk).2 hr
        let newOb := rest ∪ kids
        have hnew : ∀ i ∈ newOb, i < k ∧ low i := by
          intro i hi
          rcases Finset.mem_union.mp hi with hi | hi
          · exact hrest i hi
          · exact hkids i hi
        obtain ⟨ch, hch, hlen⟩ := ih newOb hnew
        have hn : k ∉ ch := fun h => Nat.lt_irrefl _ (hch k h).1
        refine ⟨insert k ch, ?_, ?_⟩
        · intro i hi
          rcases Finset.mem_insert.mp hi with he | hi
          · subst i
            exact ⟨Nat.lt_succ_self k, (hbound k hk).2, hr⟩
          · exact ⟨Nat.lt_succ_of_lt (hch i hi).1, (hch i hi).2⟩
        · have hle : (ob.biUnion alive).card ≤ (newOb.biUnion alive).card := by
            apply Finset.card_le_card
            intro x hx
            obtain ⟨i, hi, hx⟩ := Finset.mem_biUnion.mp hx
            by_cases h : i = k
            · subst i
              obtain ⟨j, hj, hx'⟩ := Finset.mem_biUnion.mp (hcover hx)
              exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_union_right _ hj, hx'⟩
            · exact Finset.mem_biUnion.mpr
                ⟨i, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hi⟩), hx⟩
          have hnewCard : newOb.card ≤ rest.card + kids.card := Finset.card_union_le _ _
          rw [Finset.card_insert_of_notMem hn]
          omega
      · obtain ⟨ch, hch, hlen⟩ := ih rest hrest
        refine ⟨ch, fun i hi => ⟨Nat.lt_succ_of_lt (hch i hi).1, (hch i hi).2⟩, ?_⟩
        conv_lhs => rw [← hob, Finset.biUnion_insert]
        have hUnion := Finset.card_union_le (alive k) (rest.biUnion alive)
        omega
    · have hsmall : ∀ i ∈ ob, i < k ∧ low i := by
        intro i hi
        obtain ⟨hlt,hlow⟩ := hbound i hi
        have hne : i ≠ k := fun h => hk (h ▸ hi)
        exact ⟨by omega, hlow⟩
      obtain ⟨ch, hch, hlen⟩ := ih ob hsmall
      exact ⟨ch, fun i hi => ⟨Nat.lt_succ_of_lt (hch i hi).1, (hch i hi).2⟩, hlen⟩


private def alive {n : ℕ} (C : Circuit) (A : Finset (Fin n)) (w : ℕ) :
    Finset (Fin n) :=
  A.filter (fun p => val C n (bits {p}) w = true)

private theorem rich_gate {n : ℕ} (C : Circuit) (A : Finset (Fin n)) (w : ℕ)
    (hr : 2 ≤ (alive C A w).card) : n ≤ w ∧ w < n + C.gates.length := by
  constructor
  · by_contra! h
    have sub : alive C A w ⊆ {⟨w,h⟩} := by
      intro p hp
      have hp' := (Finset.mem_filter.mp hp).2
      rw [val_input _ _ _ _ h] at hp'
      simpa [bits, eq_comm] using hp'
    have hc := Finset.card_le_card sub
    simp at hc
    omega
  · by_contra! h
    let j := w-n
    have he : w = n+j := by dsimp [j]; omega
    have hnone : C.gates[j]? = none := List.getElem?_eq_none_iff.mpr (by omega)
    have he' : alive C A w = ∅ := by
      ext p
      simp [alive, he, val_none C n _ j hnone]
    simp [he'] at hr

private theorem splitLow {n : ℕ} (C : Circuit) (A : Finset (Fin n)) (x : Fin n → Bool)
    (hG : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (w : ℕ) (hLow : val C n x w = false) (hRich : 2 ≤ (alive C A w).card) :
    ∃ kids : Finset ℕ, kids.card ≤ 2 ∧
      (∀ i ∈ kids, i < w ∧ val C n x i = false) ∧
      alive C A w ⊆ kids.biUnion (alive C A) := by
  obtain ⟨hlo,hhi⟩ := rich_gate C A w hRich
  obtain ⟨j,rfl⟩ : ∃ j, w = n+j := ⟨w-n,by omega⟩
  have hj : j < C.gates.length := by omega
  let g := C.gates[j]
  have hget : C.gates[j]? = some g := List.getElem?_eq_some_iff.mpr ⟨hj,rfl⟩
  obtain ⟨hop,hfan⟩ := hG g (List.mem_of_getElem? hget)
  rcases hop with hand | hor
  · have hp := Finset.card_pos.mp (show 0 < (alive C A (n+j)).card by omega)
    obtain ⟨p,hp⟩ := hp
    have hAll := (val_and C n _ j g hget hand).mp (Finset.mem_filter.mp hp).2
    have existsFalse : ∃ i ∈ g.inputs, val C n x i = false := by
      by_contra! he
      apply Bool.false_ne_true
      rw [← hLow]
      apply (val_and C n x j g hget hand).mpr
      intro i hi
      exact ⟨(hAll i hi).1, by simpa using he i hi⟩
    obtain ⟨i,hi,hfalse⟩ := existsFalse
    refine ⟨{i}, by simp, ?_, ?_⟩
    · intro k hk
      have he := Finset.mem_singleton.mp hk
      subst k
      exact ⟨(hAll i hi).1,hfalse⟩
    · intro q hq
      have hq' := Finset.mem_filter.mp hq
      exact Finset.mem_biUnion.mpr ⟨i, by simp,
        Finset.mem_filter.mpr ⟨hq'.1,((val_and C n _ j g hget hand).mp hq'.2 i hi).2⟩⟩
  · let kids := g.inputs.toFinset.filter (· < n+j)
    refine ⟨kids, (Finset.card_filter_le _ _).trans ((List.toFinset_card_le _).trans hfan), ?_, ?_⟩
    · intro i hi
      obtain ⟨hi,hil⟩ := Finset.mem_filter.mp hi
      refine ⟨hil, ?_⟩
      by_cases hiTrue : val C n x i = true
      · have ht := (val_or C n x j g hget hor).mpr ⟨i,List.mem_toFinset.mp hi,hil,hiTrue⟩
        simp [hLow] at ht
      · simpa using hiTrue
    · intro p hp
      obtain ⟨hp,hv⟩ := Finset.mem_filter.mp hp
      obtain ⟨i,hi,hil,htrue⟩ := (val_or C n _ j g hget hor).mp hv
      exact Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hi, hil⟩, Finset.mem_filter.mpr ⟨hp,htrue⟩⟩

open scoped BigOperators

private lemma removed_membership_accounting {m n : ℕ}
    (D : Finset (Fin n)) (S : Fin m → Finset (Fin n)) :
    1 + (∑ i, ((S i).card - 1)) ≤
      (1 + ∑ i, ((S i \ D).card - 1)) +
        ∑ u ∈ D, (Finset.univ.filter (fun i => u ∈ S i)).card := by
  classical
  have hcount : (∑ i, (S i ∩ D).card) =
      ∑ u ∈ D, (Finset.univ.filter (fun i => u ∈ S i)).card := by
    calc
      (∑ i, (S i ∩ D).card) =
          ∑ i, ∑ u ∈ D, if u ∈ S i then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_boole]
        congr 1
        ext u
        simp [and_comm]
      _ = ∑ u ∈ D, (Finset.univ.filter (fun i => u ∈ S i)).card := by
        rw [Finset.sum_comm]
        simp [Finset.sum_boole]
  have hsum : (∑ i, ((S i).card - 1)) ≤
      (∑ i, ((S i \ D).card - 1)) + ∑ i, (S i ∩ D).card := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have h := Finset.card_sdiff_add_card_inter (S i) D
    omega
  rw [← hcount]
  omega

private theorem bound {n m : ℕ}
    (S : Fin m → Finset (Fin n)) (C : Circuit) (out : Fin m → ℕ)
    (i0 : Fin C.gates.length) (hw : ℕ) (T : Finset (Fin n)) (t0 : Fin n)
    (pairwiseS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hG : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (onlyNot : ∀ q : Fin C.gates.length, (C.gates.get q).op = .not → q = i0)
    (isNot : (C.gates.get i0).op = .not)
    (hhead : (C.gates.get i0).inputs.head? = some hw) (hprev : hw < n+i0.val)
    (hOut : ∀ (w : Fin m) (x : Fin n → Bool),
      val C n x (out w) = decide (∃ v ∈ S w, x v = true))
    (hClause : ∀ y : Fin n → Bool, (∀ t ∈ T, y t = false) → val C n y hw = false)
    (ht0 : t0 ∈ T) : 1 + (∑ s : Fin m, ((S s).card - 1)) ≤
      C.gates.length + ∑ u ∈ T.erase t0, (Finset.univ.filter (fun c : Fin m => u ∈ S c)).card := by
  classical
  let D := T.erase t0
  let F := forced C
  let R (w : Fin m) := S w \ D
  let A (w : Fin m) : Finset (Fin n) :=
    if t0 ∈ S w then Finset.univ \ D else Finset.univ \ T
  have hSF : ∀ w, S w ∩ A w = R w := by
    intro w
    ext p
    by_cases h : t0 ∈ S w
    · simp [A,R,h]
    · by_cases he : p = t0
      · subst p
        simp [A,R,h]
      · simp [A,R,D,h,he]
  have fixed (w : Fin m) (Y : Finset (Fin n)) (hY : Y ⊆ A w) :
      val F n (bits Y) (out w) = true ↔ ∃ p ∈ R w, p ∈ Y := by
    have hpred : (∃ p ∈ S w, bits Y p = true) ↔ ∃ p ∈ R w, p ∈ Y := by
      rw [← hSF w]
      simp only [bits, decide_eq_true_eq, Finset.mem_inter]
      exact ⟨fun ⟨p,hp,hy⟩ => ⟨p,⟨hp,hY hy⟩,hy⟩, fun ⟨p,hp,hy⟩ => ⟨p,hp.1,hy⟩⟩
    by_cases ht : t0 ∈ Y
    · have hs : t0 ∈ S w := by
        by_contra hn
        have ha := hY ht
        simp [A,hn,ht0] at ha
      have ho : val C n (bits Y) (out w) = true := by
        rw [hOut]
        exact decide_eq_true ⟨t0,hs,by simp [bits,ht]⟩
      have htF : val F n (bits Y) (out w) = true :=
        forced_ge C _ (fun g hg => (hG g hg).1) _ ho
      simp only [htF, true_iff]
      exact hpred.mp ⟨t0,hs,by simp [bits,ht]⟩
    · have hz : ∀ p ∈ T, bits Y p = false := by
        intro p hp
        by_cases he : p = t0
        · subst p
          simp [bits,ht]
        · have hn : p ∉ Y := by
            intro hy
            have ha := hY hy
            by_cases hs : t0 ∈ S w <;> simp [A,D,hs,he,hp] at ha
          simp [bits,hn]
      have he := forced_eq C (bits Y) i0 hw onlyNot hhead hprev (hClause _ hz) (out w)
      rw [← he, hOut, decide_eq_true_eq]
      exact hpred
  have hFG : ∀ g ∈ F.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨o,ho,rfl⟩ := List.mem_map.mp hg
    obtain ⟨hop, hsize⟩ := hG o ho
    rcases hop with h | h | h <;> simp [replaceNot,h,hsize]
  let gateIds := (Finset.Ico n (n+C.gates.length)).erase (n+i0.val)
  let G (w : Fin m) := gateIds.filter (fun j => alive F (A w) j ⊆ R w ∧ 2 ≤ (alive F (A w) j).card)
  have hc (w : Fin m) : (R w).card - 1 ≤ (G w).card := by
    by_cases hsmall : (R w).card ≤ 1
    · omega
    have hs : alive F (A w) (out w) = R w := by
      ext p
      constructor
      · intro hp
        obtain ⟨ha, hv⟩ := Finset.mem_filter.mp hp
        obtain ⟨a,hr,he⟩ := (fixed w {p} (by simpa)).mp hv
        simpa using (Finset.mem_singleton.mp he) ▸ hr
      · intro hp
        have ha : p ∈ A w := (Finset.mem_inter.mp (show p ∈ S w ∩ A w by simpa [hSF] using hp)).2
        exact Finset.mem_filter.mpr ⟨ha, (fixed w {p} (by simpa)).mpr ⟨p,hp,by simp⟩⟩
    have hlow : val F n (bits (A w \ R w)) (out w) = false := by
      have h := fixed w (A w \ R w) Finset.sdiff_subset
      by_cases he : val F n (bits (A w \ R w)) (out w) = true
      · obtain ⟨p,hp,hn⟩ := h.mp he
        exact ((Finset.mem_sdiff.mp hn).2 hp).elim
      · simpa using he
    have hgate := rich_gate F (A w) (out w) (by rw [hs]; omega)
    obtain ⟨charged,hchg,hl⟩ := trace (alive F (A w))
      (fun j => val F n (bits (A w \ R w)) j = false)
      (fun j => splitLow F (A w) (bits (A w \ R w)) hFG j)
      (n+F.gates.length) {out w} (by simpa using And.intro hgate.2 hlow)
    have hsub : charged ⊆ G w := by
      intro j hj
      obtain ⟨_,hlo,hr⟩ := hchg j hj
      have ⟨hlower,hupper⟩ := rich_gate F (A w) j hr
      have hne : j ≠ n+i0.val := by
        intro he
        subst j
        have hi : C.gates[i0.val]? = some (C.gates.get i0) :=
          List.getElem?_eq_some_iff.mpr ⟨i0.isLt,rfl⟩
        rw [replace_not_true C _ _ _ hi isNot] at hlo
        contradiction
      refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr
        ⟨hne, Finset.mem_Ico.mpr ⟨hlower, by simpa [F,forced] using hupper⟩⟩, ?_, hr⟩
      intro p hp
      obtain ⟨ha,hp⟩ := Finset.mem_filter.mp hp
      by_contra hR
      have hp' : p ∈ A w \ R w := Finset.mem_sdiff.mpr ⟨ha,hR⟩
      have hTrue := val_mono F (bits {p}) (bits (A w \ R w))
        (by intro i hi; have he : i = p := by simpa [bits] using hi
            subst i
            simp [bits,hp'])
        (fun g hg => (hFG g hg).1) j hp
      simp [hlo] at hTrue
    have hle := Finset.card_le_card hsub
    have hEnds : ({out w} : Finset ℕ).biUnion (alive F (A w)) = R w := by
      rw [← hs]
      ext p
      simp [Finset.mem_biUnion]
    rw [hEnds, Finset.card_singleton] at hl
    omega
  have hA (i j : Fin m) : A i ⊆ A j ∨ A j ⊆ A i := by
    have hd : Finset.univ \ T ⊆ (Finset.univ \ D : Finset (Fin n)) :=
      Finset.sdiff_subset_sdiff Finset.Subset.rfl (Finset.erase_subset _ _)
    by_cases hi : t0 ∈ S i <;> by_cases hj : t0 ∈ S j <;> simp [A,hi,hj,hd]
  have disj : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint G := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro g hgi hgj
    obtain ⟨_, hsubi, hci⟩ := Finset.mem_filter.mp hgi
    obtain ⟨_, hsubj, hcj⟩ := Finset.mem_filter.mp hgj
    have impossible (i j : Fin m) (hne : i ≠ j) (h : A i ⊆ A j)
        (hi : alive F (A i) g ⊆ R i) (hj : alive F (A j) g ⊆ R j)
        (hc : 2 ≤ (alive F (A i) g).card) : False := by
      have hx : alive F (A i) g ⊆ S i ∩ S j := by
        intro p hp
        obtain ⟨ha,hp'⟩ := Finset.mem_filter.mp hp
        exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp (hi hp)).1,
          (Finset.mem_sdiff.mp (hj (Finset.mem_filter.mpr ⟨h ha,hp'⟩))).1⟩
      have h := Finset.card_le_card hx
      have hl := pairwiseS i j hne
      omega
    rcases hA i j with h | h
    · exact impossible i j hij h hsubi hsubj hci
    · exact impossible j i hij.symm h hsubj hsubi hcj
  have ht : (n+i0.val) ∈ Finset.Ico n (n+C.gates.length) :=
    Finset.mem_Ico.mpr ⟨by omega, by have := i0.isLt; omega⟩
  have hcap : gateIds.card + 1 = C.gates.length := by
    simpa [gateIds] using Finset.card_erase_add_one ht
  have hcounts : (∑ w, ((R w).card - 1)) ≤ gateIds.card := calc
    _ ≤ ∑ w, (G w).card := Finset.sum_le_sum (fun w _ => hc w)
    _ = (Finset.univ.biUnion G).card := (Finset.card_biUnion disj).symm
    _ ≤ gateIds.card := Finset.card_le_card (by
      intro j hj
      obtain ⟨w,_,hw⟩ := Finset.mem_biUnion.mp hj
      exact (Finset.mem_filter.mp hw).1)
  have htotal := removed_membership_accounting D S
  change 1 + (∑ i, ((S i).card - 1)) ≤
      (1 + ∑ i, ((R i).card - 1)) + ∑ u ∈ D, (Finset.univ.filter (fun i => u ∈ S i)).card at htotal
  change 1 + (∑ i, ((S i).card - 1)) ≤
      C.gates.length + ∑ u ∈ D, (Finset.univ.filter (fun i => u ∈ S i)).card
  omega

end PEqualNP.Outside.L_meta_986

theorem PEqualNP.Outside.L_meta_986 :
    ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (i0 : Fin gates.length) (hw : ℕ) (T : Finset (Fin n)) (t0 : Fin n), (∀ i : Fin m, 2 ≤ (S i).card) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ q : Fin gates.length, (gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.not → q = i0) → (gates.get i0).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get i0).inputs.head? = some hw → hw < n + i0.val → (∀ (o : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true)) → (∀ y : Fin n → Bool, (∀ t ∈ T, y t = false) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, hw⟩ (List.ofFn y) = false) → t0 ∈ T → (∀ t ∈ T, (Finset.univ.filter (fun a : Fin m => t ∈ S a)).card ≤ (Finset.univ.filter (fun b : Fin m => t0 ∈ S b)).card) → 1 + ∑ s : Fin m, ((S s).card - 1) ≤ gates.length + ∑ u ∈ T.erase t0, (Finset.univ.filter (fun c : Fin m => u ∈ S c)).card
    := by
  intro n m S gates out i0 hw T t0 _ hsets hG onlyNot isNot hhead hprev hOut hClause ht0 _
  exact PEqualNP.Outside.L_meta_986.bound S ⟨gates,0⟩ out i0 hw T t0 hsets hG
    onlyNot isNot hhead hprev hOut hClause ht0
