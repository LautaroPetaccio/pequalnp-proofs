import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_716

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def shifted (n i : ℕ) : ℕ := if i < n then i else i + 1
private def move (n : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (shifted n)⟩
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma lookup (a b : List Bool) (z : Bool) (i : ℕ) :
    (a ++ z :: b).getD (shifted a.length i) false = (a ++ b).getD i false := by
  simp only [shifted, List.getD_eq_getElem?_getD]
  split
  next h => rw [List.getElem?_append_left h, List.getElem?_append_left h]
  next h =>
    rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
    have hi : i + 1 - a.length = (i - a.length) + 1 := by omega
    rw [hi]
    rfl

private lemma moved (a b : List Bool) (z : Bool) (gs : List Gate) :
    ∃ tail,
      gs.foldl step (a ++ b) = a ++ tail ∧
      (gs.map (move a.length)).foldl step (a ++ z :: b) = a ++ z :: tail := by
  induction gs generalizing b with
  | nil => exact ⟨b, rfl, rfl⟩
  | cons g gs ih =>
    let v := g.op.eval (g.inputs.map fun i => (a ++ b).getD i false)
    have hv : (move a.length g).op.eval
        ((move a.length g).inputs.map fun i => (a ++ z :: b).getD i false) = v := by
      simp only [move, v, List.map_map, Function.comp_def, lookup]
    simp only [List.foldl_cons, List.map_cons, step, hv]
    simpa only [List.append_assoc, List.cons_append] using ih (b ++ [v])

private lemma snoc (n : ℕ) (x : Fin (n + 1) → Bool) :
    List.ofFn x = List.ofFn (fun i : Fin n => x i.castSucc) ++ [x (Fin.last n)] := by
  simpa [List.concat_eq_append] using List.ofFn_succ' x

private def extra (neg : Bool) (z g k : ℕ) : List Gate :=
  if neg then
    [⟨.and, [z,g]⟩, ⟨.or, [z,g]⟩, ⟨.not, [k+1]⟩, ⟨.or, [k,k+2]⟩]
  else
    [⟨.or, [z,g]⟩, ⟨.and, [z,g]⟩, ⟨.not, [k+1]⟩, ⟨.and, [k,k+2]⟩]

private lemma getD_prefix (a b : List Bool) (i : ℕ) (hi : i < a.length) :
    (a ++ b).getD i false = a.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma extra_eval (neg : Bool) (w : List Bool) (z g : ℕ)
    (hz : z < w.length) (hg : g < w.length ∨ w.length + 4 ≤ g) :
    ((extra neg z g w.length).foldl step w).getD (w.length+3) false =
      xor (w.getD z false) (if neg then !(w.getD g false) else w.getD g false) := by
  have hz' (l : List Bool) : (w ++ l).getD z false = w.getD z false :=
    getD_prefix w l z hz
  have hg' (l : List Bool) (hl : l.length ≤ 4) :
      (w ++ l).getD g false = w.getD g false := by
    rcases hg with h | h
    · exact getD_prefix w l g h
    · have h' : (w ++ l).length ≤ g := by simp; omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h',
        List.getElem?_eq_none (show w.length ≤ g by omega)]
  have hg1 (a : Bool) := hg' [a] (by simp)
  have h1 (a b : Bool) (l : List Bool) :
      (w ++ a :: b :: l).getD (w.length+1) false = b := by
    simp [List.getD_eq_getElem?_getD]
  have h0 (a : Bool) (l : List Bool) :
      (w ++ a :: l).getD w.length false = a := by
    simp [List.getD_eq_getElem?_getD]
  have h2 (a b c : Bool) (l : List Bool) :
      (w ++ a :: b :: c :: l).getD (w.length+2) false = c := by
    simp [List.getD_eq_getElem?_getD]
  have h3 (a b c d : Bool) :
      (w ++ [a,b,c,d]).getD (w.length+3) false = d := by
    simp [List.getD_eq_getElem?_getD]
  cases neg <;>
    simp only [extra, Bool.false_eq_true, ite_false, ite_true, List.foldl_cons, List.foldl_nil,
      step, GateOp.eval, List.map_cons, List.map_nil, List.append_assoc, List.cons_append,
      List.nil_append, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq,
      Bool.and_true, Bool.or_false, List.headD_cons, hz', hg1, h0, h1, h2, h3]
  all_goals cases w.getD z false <;> cases w.getD g false <;> rfl


private lemma len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [step, ih]; omega

private lemma savedIndex (n i : ℕ) (b : List Bool) (a : List Bool)
    (ha : a.length = n) (z : Bool) (k : ℕ) (hk : k = (a ++ z :: b).length) :
    (a ++ z :: b).getD (if i < (a ++ b).length then shifted n i else k+4) false =
      (a ++ b).getD i false := by
  split
  next h => subst n; exact lookup a b z i
  next h =>
    simp [List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (show (a ++ b).length ≤ i by omega),
      List.getElem?_eq_none (show (a ++ z :: b).length ≤ k+4 by omega)]

private lemma readZ (a b : List Bool) (z : Bool) :
    (a ++ z :: b).getD a.length false = z := by
  simp [List.getD_eq_getElem?_getD]

private lemma build (n s : ℕ) (g : (Fin n → Bool) → Bool) (neg : Bool)
    (h : HasCircuitSize n (fun y => if neg then !(g y) else g y) s) :
    HasCircuitSize (n+1) (fun x => xor (x (Fin.last n)) (g fun i => x i.castSucc)) (s+4) := by
  obtain ⟨C, hfan, hsize, heval⟩ := h
  let k := n+1+C.size
  let j := if C.output < n+C.size then shifted n C.output else k+4
  refine ⟨⟨C.gates.map (move n) ++ extra neg n j k,k+3⟩, ?_, ?_, ?_⟩
  · intro gate hgate
    rcases List.mem_append.mp hgate with hgate | hgate
    · obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hgate
      simpa [move] using hfan old hold
    · cases neg <;> simp [extra] at hgate <;>
        rcases hgate with rfl | rfl | rfl | rfl <;> simp
  · cases neg <;> simpa [Circuit.size, extra] using Nat.add_le_add_right hsize 4
  · intro x
    let a := List.ofFn (fun i : Fin n => x i.castSucc)
    let z := x (Fin.last n)
    have ha : a.length = n := by simp [a]
    have hn : List.ofFn x = a ++ [z] := snoc n x
    obtain ⟨tail, ht, hmove⟩ := moved a [] z C.gates
    rw [ha] at hmove
    simp only [List.append_nil] at ht
    have hlength : (a ++ tail).length = n+C.size := by
      rw [← ht, len, ha]
      rfl
    have hlength' : (a ++ z :: tail).length = k := by
      simp [List.length_append, List.length_cons, ha] at hlength ⊢
      dsimp [k]
      omega
    have hj : j < (a ++ z :: tail).length ∨ (a ++ z :: tail).length + 4 ≤ j := by
      rw [hlength']
      unfold j shifted
      split <;> simp [k] at *
      next hj =>
        left
        split <;> omega
    have hz : n < (a ++ z :: tail).length := by rw [hlength']; dsimp [k]; omega
    have ho : (a ++ z :: tail).getD j false = C.eval a := by
      have w : C.wires a = a ++ tail := ht
      rw [Circuit.eval, w]
      simpa [j, hlength] using savedIndex n C.output tail a ha z k hlength'.symm
    change (((C.gates.map (move n) ++ extra neg n j k).foldl step (List.ofFn x)).getD (k+3) false) = _
    rw [List.foldl_append, hn, hmove]
    have he := extra_eval neg _ _ _ hz hj
    rw [hlength'] at he
    rw [he, ho]
    have hnew : (a ++ z :: tail).getD n false = z := by rw [← ha, readZ]
    rw [hnew]
    have ev := heval (fun i : Fin n => x i.castSucc)
    change C.eval a = _ at ev
    rw [ev]
    cases neg <;> simp [z]

end PEqualNP.Outside.L_meta_716

theorem PEqualNP.Outside.L_meta_716 :
    ∀ (n s : ℕ) (g : (Fin n → Bool) → Bool), (PEqualNP.MetaComplexity.HasCircuitSize n g s → PEqualNP.MetaComplexity.HasCircuitSize (n + 1) (fun x : Fin (n + 1) → Bool => xor (x (Fin.last n)) (g (fun i : Fin n => x i.castSucc))) (s + 4)) ∧ (PEqualNP.MetaComplexity.HasCircuitSize n (fun y : Fin n → Bool => !(g y)) s → PEqualNP.MetaComplexity.HasCircuitSize (n + 1) (fun x : Fin (n + 1) → Bool => xor (x (Fin.last n)) (g (fun i : Fin n => x i.castSucc))) (s + 4)) := by
  intro n s g
  exact ⟨PEqualNP.Outside.L_meta_716.build n s g false,
    PEqualNP.Outside.L_meta_716.build n s g true⟩
