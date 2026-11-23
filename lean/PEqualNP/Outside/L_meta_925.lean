import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_925

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

private def Specific {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (w : Fin m) (i : ℕ) : Prop :=
  val C n (bits (S w)) i = true ∧ ∀ v, v ≠ w → val C n (bits (S v)) i = false

private def Charge {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (w : Fin m) (i : ℕ) : Prop :=
  Specific S C w i ∧ n ≤ i ∧
    ∃ g, C.gates[i - n]? = some g ∧ g.op = GateOp.and

private def Terminal {n m : ℕ} (S : Fin m → Finset (Fin n)) (w : Fin m)
    (a : Finset (Fin n)) : Prop :=
  (∃ v, v ≠ w ∧ a = S v) ∨ ∃ p ∈ S w, a = {p}

private lemma trace {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : Fin m) (k : ℕ) (ob : Finset ℕ)
    (hbound : ∀ i ∈ ob, i < k)
    (htrue : ∀ i ∈ ob, val C n (bits (S w)) i = true) :
    ∃ (terms : List (Finset (Fin n))) (charged : Finset ℕ),
      (∀ a ∈ terms, Terminal S w a) ∧
      (∀ i ∈ charged, i < k ∧ Charge S C w i) ∧
      terms.length ≤ ob.card + charged.card ∧
      ∀ x : Fin n → Bool, (∀ a ∈ terms, ∀ p ∈ a, x p = true) →
        ∀ i ∈ ob, val C n x i = true := by
  classical
  induction k generalizing ob with
  | zero =>
    refine ⟨[], ∅, by simp, by simp, by simp, ?_⟩
    intro x hx i hi
    exact (Nat.not_lt_zero i (hbound i hi)).elim
  | succ k ih =>
    by_cases hk : k ∈ ob
    · let rest := ob.erase k
      have hrest : ∀ i ∈ rest, i < k := by
        intro i hi
        obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hi
        have := hbound i hmem
        omega
      have hrestTrue : ∀ i ∈ rest, val C n (bits (S w)) i = true :=
        fun i h => htrue i (Finset.mem_erase.mp h).2
      have hcard : rest.card + 1 = ob.card := by
        change (ob.erase k).card + 1 = ob.card
        rw [Finset.card_erase_of_mem hk]
        have := Finset.card_pos.mpr ⟨k, hk⟩
        omega
      have traceDrop (a : Finset (Fin n)) (ha : Terminal S w a)
          (hdrop : ∀ x : Fin n → Bool, (∀ p ∈ a, x p = true) → val C n x k = true) :
          ∃ (terms : List (Finset (Fin n))) (charged : Finset ℕ),
            (∀ a ∈ terms, Terminal S w a) ∧
            (∀ i ∈ charged, i < k + 1 ∧ Charge S C w i) ∧
            terms.length ≤ ob.card + charged.card ∧
            ∀ x : Fin n → Bool, (∀ a ∈ terms, ∀ p ∈ a, x p = true) →
              ∀ i ∈ ob, val C n x i = true := by
        obtain ⟨ts, ch, hts, hch, hlen, hval⟩ := ih rest hrest hrestTrue
        refine ⟨a :: ts, ch, ?_, ?_, ?_, ?_⟩
        · intro s hs
          rcases List.mem_cons.mp hs with rfl | hs
          · exact ha
          · exact hts s hs
        · intro i hi
          exact ⟨Nat.lt_succ_of_lt (hch i hi).1, (hch i hi).2⟩
        · simp only [List.length_cons]
          omega
        · intro x hx i hi
          by_cases h : i = k
          · subst i
            exact hdrop x (hx a (by simp))
          · exact hval x (fun s hs => hx s (List.mem_cons_of_mem a hs)) i
              (Finset.mem_erase.mpr ⟨h, hi⟩)
      by_cases hspec : Specific S C w k
      · by_cases hin : k < n
        · let p : Fin n := ⟨k, hin⟩
          have hp : p ∈ S w := by
            have hv := hspec.1
            rw [val_input C n _ _ hin] at hv
            simpa [bits, p] using hv
          apply traceDrop {p} (Or.inr ⟨p, hp, rfl⟩)
          intro x hx
          rw [val_input C n x k hin]
          exact hx p (by simp)
        · obtain ⟨j, rfl⟩ : ∃ j, k = n + j := ⟨k - n, by omega⟩
          cases hg : C.gates[j]? with
          | none =>
            have hv := hspec.1
            rw [val_none C n _ j hg] at hv
            contradiction
          | some g =>
            obtain ⟨hop, hfan⟩ := hC g (List.mem_of_getElem? hg)
            rcases hop with ha | ho
            · have kids := (val_and C n _ j g hg ha).mp hspec.1
              let newOb := rest ∪ g.inputs.toFinset
              have hnew : ∀ i ∈ newOb, i < n + j := by
                intro i hi
                rcases Finset.mem_union.mp hi with hi | hi
                · exact hrest i hi
                · exact (kids i (List.mem_toFinset.mp hi)).1
              have hnewTrue : ∀ i ∈ newOb, val C n (bits (S w)) i = true := by
                intro i hi
                rcases Finset.mem_union.mp hi with hi | hi
                · exact hrestTrue i hi
                · exact (kids i (List.mem_toFinset.mp hi)).2
              obtain ⟨ts, ch, hts, hch, hlen, hval⟩ := ih newOb hnew hnewTrue
              have hf : g.inputs.toFinset.card ≤ 2 :=
                le_trans (List.toFinset_card_le _) hfan
              have hunion : newOb.card ≤ rest.card + g.inputs.toFinset.card :=
                Finset.card_union_le _ _
              have hnot : n + j ∉ ch := fun h => (Nat.lt_irrefl _ (hch _ h).1)
              refine ⟨ts, insert (n+j) ch, hts, ?_, ?_, ?_⟩
              · intro i hi
                rcases Finset.mem_insert.mp hi with rfl | hi
                · exact ⟨by omega, hspec, by omega, g, by simpa using hg, ha⟩
                · exact ⟨Nat.lt_succ_of_lt (hch i hi).1, (hch i hi).2⟩
              · rw [Finset.card_insert_of_notMem hnot]
                omega
              · intro x hx i hi
                by_cases h : i = n + j
                · subst i
                  apply (val_and C n x j g hg ha).mpr
                  intro r hr
                  exact ⟨(kids r hr).1, hval x hx r
                    (Finset.mem_union_right _ (List.mem_toFinset.mpr hr))⟩
                · exact hval x hx i (Finset.mem_union_left _
                    (Finset.mem_erase.mpr ⟨h, hi⟩))
            · obtain ⟨child, hm, hlt, hchild⟩ := (val_or C n _ j g hg ho).mp hspec.1
              let newOb := insert child rest
              have hnew : ∀ i ∈ newOb, i < n + j := by
                intro i hi
                rcases Finset.mem_insert.mp hi with rfl | hi
                · exact hlt
                · exact hrest i hi
              have hnewTrue : ∀ i ∈ newOb, val C n (bits (S w)) i = true := by
                intro i hi
                rcases Finset.mem_insert.mp hi with rfl | hi
                · exact hchild
                · exact hrestTrue i hi
              obtain ⟨ts, ch, hts, hch, hlen, hval⟩ := ih newOb hnew hnewTrue
              have hc : newOb.card ≤ rest.card + 1 := Finset.card_insert_le _ _
              refine ⟨ts, ch, hts, ?_, by omega, ?_⟩
              · intro i hi
                exact ⟨Nat.lt_succ_of_lt (hch i hi).1, (hch i hi).2⟩
              · intro x hx i hi
                by_cases h : i = n + j
                · subst i
                  exact (val_or C n x j g hg ho).mpr
                    ⟨child, hm, hlt, hval x hx child (Finset.mem_insert_self _ _)⟩
                · exact hval x hx i (Finset.mem_insert_of_mem
                    (Finset.mem_erase.mpr ⟨h, hi⟩))
      · have hother : ∃ v, v ≠ w ∧ val C n (bits (S v)) k = true := by
          by_contra hn
          apply hspec
          refine ⟨htrue k hk, fun v hv => ?_⟩
          cases hv' : val C n (bits (S v)) k
          · rfl
          · exact (hn ⟨v,hv,hv'⟩).elim
        obtain ⟨v,hvw,hv⟩ := hother
        apply traceDrop (S v) (Or.inl ⟨v, hvw, rfl⟩)
        intro x hx
        apply val_mono C (bits (S v)) x _ (fun g hg => (hC g hg).1) k hv
        intro i hi
        exact hx i (by simpa [bits] using hi)
    · have hbound' : ∀ i ∈ ob, i < k := by
        intro i hi
        have h := hbound i hi
        have hn : i ≠ k := fun e => hk (e ▸ hi)
        omega
      obtain ⟨ts, ch, hts, hch, hlen, hval⟩ := ih ob hbound' htrue
      exact ⟨ts, ch, hts, fun i hi => ⟨Nat.lt_succ_of_lt (hch i hi).1, (hch i hi).2⟩, hlen, hval⟩

private lemma union_card_small {α : Type*} [DecidableEq α]
    (terms : List (Finset α)) (hsize : ∀ X ∈ terms, X.card ≤ 1) :
    (terms.toFinset.biUnion id).card ≤ terms.length := by
  induction terms with
  | nil => simp
  | cons X rest ih =>
    have hX := hsize X List.mem_cons_self
    have hr := ih (fun Y hY => hsize Y (List.mem_cons_of_mem _ hY))
    have hU := Finset.card_union_le X (rest.toFinset.biUnion id)
    simp only [List.toFinset_cons, Finset.biUnion_insert, id_eq, List.length_cons]
    omega

private lemma union_card_terms {α : Type*} [DecidableEq α] (q : ℕ) (hq : 1 ≤ q)
    (terms : List (Finset α))
    (hsize : ∀ X ∈ terms, X.card ≤ 1 ∨ X.card = q + 1)
    (hmeet : ∀ X ∈ terms, ∀ Y ∈ terms, X.card = q + 1 → Y.card = q + 1 →
      (X ∩ Y).Nonempty) :
    (terms.toFinset.biUnion id).card ≤ q * terms.length + 1 := by
  induction terms with
  | nil => simp
  | cons X rest ih =>
    let U := rest.toFinset.biUnion id
    have htail := ih (fun Y hY => hsize Y (List.mem_cons_of_mem _ hY))
      (fun Y hY Z hZ => hmeet Y (List.mem_cons_of_mem _ hY) Z (List.mem_cons_of_mem _ hZ))
    change U.card ≤ q * rest.length + 1 at htail
    simp only [List.toFinset_cons, Finset.biUnion_insert, id_eq, List.length_cons, Nat.mul_succ]
    change (X ∪ U).card ≤ q * rest.length + q + 1
    have hUnion := Finset.card_union_add_card_inter X U
    rcases hsize X List.mem_cons_self with hX | hX
    · omega
    · by_cases h : ∃ Y ∈ rest, Y.card = q + 1
      · obtain ⟨Y, hY, hYcard⟩ := h
        obtain ⟨a, ha⟩ := hmeet X List.mem_cons_self Y (List.mem_cons_of_mem _ hY) hX hYcard
        have haU : a ∈ U := Finset.mem_biUnion.mpr ⟨Y, List.mem_toFinset.mpr hY,
          (Finset.mem_inter.mp ha).2⟩
        have hone := Finset.card_pos.mpr (show (X ∩ U).Nonempty from
          ⟨a, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp ha).1, haU⟩⟩)
        omega
      · have small : U.card ≤ rest.length :=
          union_card_small rest fun Y hY =>
            (hsize Y (List.mem_cons_of_mem _ hY)).resolve_right (fun hy => h ⟨Y, hY, hy⟩)
        have hprod : rest.length ≤ q * rest.length := by
          simpa using Nat.mul_le_mul_right rest.length hq
        omega

private lemma union_inter_card_terms {α : Type*} [DecidableEq α]
    (terms : List (Finset α)) (S : Finset α)
    (hsize : ∀ X ∈ terms, (X ∩ S).card ≤ 1) :
    ((terms.toFinset.biUnion id) ∩ S).card ≤ terms.length := by
  induction terms with
  | nil => simp
  | cons X rest ih =>
    have hX := hsize X List.mem_cons_self
    have hr := ih (fun Y hY => hsize Y (List.mem_cons_of_mem _ hY))
    have hU := Finset.card_union_le (X ∩ S) (rest.toFinset.biUnion id ∩ S)
    simp only [List.toFinset_cons, Finset.biUnion_insert, id_eq,
      Finset.union_inter_distrib_right, List.length_cons]
    omega

private lemma finish (q n m K : ℕ) (S : Fin m → Finset (Fin n))
    (hsize : ∀ i, (S i).card = q+1)
    (gates : List Gate) (out : Fin m → ℕ)
    (hC : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcomp : ∀ (w : Fin m) (x : Fin n → Bool),
      (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ K →
      (⟨gates, out w⟩ : Circuit).eval (List.ofFn x) = decide (∀ v ∈ S w, x v = true))
    (hu : ∀ w (ts : List (Finset (Fin n))), (∀ a ∈ ts, Terminal S w a) →
      (ts.toFinset.biUnion id).card ≤ q * ts.length + 1 ∧
      ((ts.toFinset.biUnion id) ∩ S w).card ≤ ts.length)
    (c : ℕ) (hcq : c ≤ q) (hcK : c*q < K) : m*c ≤ gates.length := by
  classical
  by_cases hc : c = 0
  · simp [hc]
  let C : Circuit := ⟨gates,0⟩
  let allCharges (w : Fin m) := (Finset.range (n+gates.length)).filter (Charge S C w)
  have hcount (w : Fin m) : c ≤ (allCharges w).card := by
    have hq : q ≤ c*q := by
      simpa using Nat.mul_le_mul_right q (show 1 ≤ c by omega)
    have hinK : (S w).card ≤ K := by rw [hsize]; omega
    have compBits (a : Finset (Fin n)) (ha : a.card ≤ K) :
        val C n (bits a) (out w) = decide (S w ⊆ a) := by
      have ht : (Finset.univ.filter (fun i : Fin n => bits a i = true)) = a := by
        ext i; simp [bits]
      have hv := hcomp w (bits a) (by simpa only [ht] using ha)
      apply Bool.eq_iff_iff.mpr
      rw [decide_eq_true_eq]
      change (⟨gates, out w⟩ : Circuit).eval (List.ofFn (bits a)) = true ↔ S w ⊆ a
      rw [hv, decide_eq_true_eq]
      simp only [bits, decide_eq_true_eq]
      exact ⟨fun h _ hi => h _ hi, fun h _ hi => h hi⟩
    have hw : val C n (bits (S w)) (out w) = true := by
      rw [compBits (S w) hinK]
      simp
    have ho : out w < n + gates.length := by
      by_contra h
      have hlen : (C.wires (List.ofFn (bits (S w)))).length = n + gates.length := by
        rw [wires_eq, foldl_step_length]
        simp [C]
      have hfalse := getD_of_length_le (C.wires (List.ofFn (bits (S w)))) (out w)
        (by rw [hlen]; omega)
      exact Bool.false_ne_true (hfalse.symm.trans hw)
    obtain ⟨ts, ch, ht, hch, hlen, hval⟩ :=
      trace S C hC w (n+gates.length) {out w}
        (by simpa) (by simpa)
    have hsub : ch ⊆ allCharges w := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hch i hi).1, (hch i hi).2⟩
    apply le_trans _ (Finset.card_le_card hsub)
    by_contra hsmall
    let U := ts.toFinset.biUnion id
    have htlen : ts.length ≤ c := by simpa using (show ts.length ≤ c by simp at hlen; omega)
    have hcard : U.card ≤ K := by
      have hmul := Nat.mul_le_mul_left q htlen
      have := (hu w ts ht).1
      dsimp [U]
      rw [Nat.mul_comm q c] at hmul
      omega
    have hv : val C n (bits U) (out w) = true := by
      apply hval
      · intro a ha p hp
        have hpu : p ∈ U := Finset.mem_biUnion.mpr ⟨a, List.mem_toFinset.mpr ha, hp⟩
        exact decide_eq_true hpu
      · simp
    have hs : S w ⊆ U := by
      rw [compBits U hcard] at hv
      exact of_decide_eq_true hv
    have hcard' : (S w).card ≤ (U ∩ S w).card :=
      Finset.card_le_card (fun i hi => Finset.mem_inter.mpr ⟨hs hi, hi⟩)
    have hsmall' := (hu w ts ht).2
    rw [hsize] at hcard'
    change (U ∩ S w).card ≤ ts.length at hsmall'
    omega
  have hdisj : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint allCharges := by
    intro v _ w _ hvw
    apply Finset.disjoint_left.mpr
    intro i hv hw
    have hvc := (Finset.mem_filter.mp hv).2.1
    have hwc := (Finset.mem_filter.mp hw).2.1
    exact Bool.false_ne_true ((hvc.2 w hvw.symm).symm.trans hwc.1)
  calc
    m*c = ∑ _w : Fin m, c := by simp
    _ ≤ ∑ w : Fin m, (allCharges w).card := Finset.sum_le_sum (fun w _ => hcount w)
    _ = (Finset.univ.biUnion allCharges).card := (Finset.card_biUnion hdisj).symm
    _ ≤ (Finset.Ico n (n+gates.length)).card := by
      apply Finset.card_le_card
      intro i hi
      obtain ⟨w, _, hw⟩ := Finset.mem_biUnion.mp hi
      obtain ⟨hlo, hhi⟩ := Finset.mem_filter.mp hw
      exact Finset.mem_Ico.mpr ⟨hhi.2.1, Finset.mem_range.mp hlo⟩
    _ = gates.length := by simp

end PEqualNP.Outside.L_meta_925

theorem PEqualNP.Outside.L_meta_925 :
    ∀ (q n m K : ℕ) (S : Fin m → Finset (Fin n)), 2 ≤ q → (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ K → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∀ v ∈ S w, x v = true)) → ∀ c : ℕ, c ≤ q → c * q < K → m * c ≤ gates.length := by
  intro q n m K S hq hs hm gates out hC hcomp c hc hcK
  apply PEqualNP.Outside.L_meta_925.finish q n m K S hs gates out hC hcomp _ c hc hcK
  intro w ts ht
  constructor
  · apply PEqualNP.Outside.L_meta_925.union_card_terms q (by omega) ts
    · intro X hX
      rcases ht X hX with ⟨v, _, rfl⟩ | ⟨p, _, rfl⟩
      · exact Or.inr (hs v)
      · simp
    · intro X hX Y hY hXc hYc
      rcases ht X hX with ⟨v, _, rfl⟩ | ⟨p, _, rfl⟩
      · rcases ht Y hY with ⟨v', _, rfl⟩ | ⟨p, _, rfl⟩
        · apply Finset.card_pos.mp
          by_cases he : v = v'
          · subst v'
            simp [hs]
          · rw [hm v v' he]
            omega
        · simp at hYc
          omega
      · simp at hXc
        omega
  · apply PEqualNP.Outside.L_meta_925.union_inter_card_terms ts (S w)
    intro X hX
    rcases ht X hX with ⟨v, hv, rfl⟩ | ⟨p, _, rfl⟩
    · rw [hm v w hv]
    · exact (Finset.card_le_card (Finset.inter_subset_left : {p} ∩ S w ⊆ {p})).trans (by simp)
