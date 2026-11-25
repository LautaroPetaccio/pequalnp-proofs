import PEqualNP.Defs
-- The live-wire checker is adapted from ljste's PR 2918 and jfsantoropereira's L-meta-1007.
-- Adapted from the signed live-wire certificate in L_meta_8721. Apache-2.0.
namespace PEqualNP.Outside.L_meta_11090

abbrev B := BitVec 54
abbrev Sig := B × B
def top : B := BitVec.allOnes 54
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
  by_cases hi : i < 54
  · cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases ht : decide (0<t) <;>
      simp only [sep,neg,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 54 ≤ i)] at h

private lemma sep_binary (t d : Bool) (a b : Sig) (i : Nat)
    (h : (sep t (bin d a b)).getLsbD i = true) :
    (sep t a).getLsbD i = true ∨ (sep t b).getLsbD i = true := by
  by_cases hi : i < 54
  · cases t <;> cases d <;>
      cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases hu : b.1.getLsbD i <;> cases hv : b.2.getLsbD i <;>
      simp only [sep,bin,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,hu,hv] at h ⊢ <;> first | contradiction | decide
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 54 ≤ i)] at h

private lemma sep_weaken (t : Nat) (a : Sig) (i : Nat) (hi : i < 54)
    (h : (sep (decide (0<t)) a).getLsbD i = true) : (sep true a).getLsbD i = true := by
  cases ht : decide (0<t) <;> cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
    simp only [sep,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide

private lemma live_sep {k t S} (h : Live k t S) (i : Nat) (hi : i < 54) :
    ∃ a ∈ S, (sep (decide (0<t)) a).getLsbD i = true := by
  induction h using liveInd with
  | stop =>
    refine ⟨target,by simp,?_⟩
    change (BitVec.allOnes 54 &&& ~~~(0 : B)).getLsbD i = true
    rw [BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_allOnes (v := 54)]
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

def bit (side : Bool) (i : Fin 54) (a : Sig) : Bool :=
  (if side then a.1 else a.2).getLsbD i.val

private lemma bit_zero (s i) : bit s i zero = false := by cases s <;> simp [bit,zero]
private lemma bit_one (s i) : bit s i one = true := by
  cases s <;> change (BitVec.allOnes 54).getLsbD i.val = true <;> rw [BitVec.getLsbD_allOnes] <;> simp
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


def graph (x : Fin 7 → Bool) : Bool :=
  decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2,
    (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧
    (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)
def sample (raw : List Sig) (s : Bool) (i : Fin 54) (j : Fin 7) := bit s i (raw.getD j.val zero)
private lemma sample_list (raw : List Sig) (raw_id : List.ofFn (fun j : Fin 7 => raw.getD j.val zero) = raw) (s i) : List.ofFn (sample raw s i) = raw.map (bit s i) := by
  calc
    _ = (List.ofFn (fun j : Fin 7 => raw.getD j.val zero)).map (bit s i) := by rw [List.map_ofFn]; rfl
    _ = _ := by rw [raw_id]

private lemma circuit_target (raw : List Sig) (raw_id : List.ofFn (fun j : Fin 7 => raw.getD j.val zero) = raw)
    (sample_ok : ∀ s i, graph (sample raw s i) = s) (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = graph x) : target ∈ execute C.gates raw := by
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

private abbrev bitCount : Nat := 54

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

private def checkOrbit (syms : List BitPerm) (reps : List SearchState)
    (c : SearchState) (key : Nat × Nat) : Bool :=
  match syms[key.1]?, reps[key.2]? with
  | some p, some r =>
    c.1 == r.1 && decide ((c.2.toFinset.map (permSignal p).toEmbedding) = r.2.toFinset)
  | _, _ => false

private theorem checkOrbit_ok {syms : List BitPerm} {reps : List SearchState}
    {c : SearchState} {key : Nat × Nat} (h : checkOrbit syms reps c key = true) :
    ∃ (p : BitPerm) (r : SearchState), r ∈ reps ∧ c.1 = r.1 ∧
      c.2.toFinset.map (permSignal p).toEmbedding = r.2.toFinset := by
  unfold checkOrbit at h
  split at h
  · rename_i p r hp hr
    exact ⟨p,r,List.mem_of_getElem? hr,by simpa only [Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] using h⟩
  · contradiction

private def checkOrbits (syms : List BitPerm) (reps : List SearchState) :
    List SearchState → List (Nat × Nat) → Bool
  | [], [] => true
  | c::cs, key::keys => checkOrbit syms reps c key && checkOrbits syms reps cs keys
  | _, _ => false

private theorem checkOrbits_ok {syms : List BitPerm} {reps : List SearchState}
    {cs : List SearchState} {keys : List (Nat × Nat)}
    (h : checkOrbits syms reps cs keys = true) {c : SearchState} (hc : c ∈ cs) :
    ∃ (p : BitPerm) (r : SearchState), r ∈ reps ∧ c.1 = r.1 ∧
      c.2.toFinset.map (permSignal p).toEmbedding = r.2.toFinset := by
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

private theorem noLive_of_orbits {k t : Nat} {v : List Sig}
    (hv : v.Nodup) (hn : v ≠ [target])
    (syms : List BitPerm) (reps : List SearchState) (keys : List (Nat × Nat))
    (cover : checkOrbits syms reps (kids k (t,v)) keys = true)
    (excluded : ∀ r ∈ reps, r.2.Nodup ∧ search k r.1 r.2 = false) :
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
  obtain ⟨p,r,hr,he,himage⟩ := checkOrbits_ok cover hc
  obtain ⟨l,hk,hl⟩ : ∃ l ≤ k, Live l c.1 c.2.toFinset := of_decide_eq_true ht
  have h2 := live_permSignal p hl
  rw [he,himage] at h2
  have ⟨nd,ex⟩ := excluded r hr
  exact Bool.false_ne_true (ex.symm.trans (search_complete h2 k hk r.2 nd rfl))


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The rows pair edges with independent sets, and include a sensitivity
-- witness for each input by pairing an edge with one of its endpoints.
def raw : List Sig := [(0xf003f27ff, 0x23081120d1),
  (0x0, 0x0),
  (0x600f03f30f830, 0x202721b3068b4),
  (0x81f00c7c0c03f, 0x47404140ca2e),
  (0x31e000f800ffc0, 0x10e400e0849708),
  (0x3e0000ffff0000, 0x3e9008b6ae0400),
  (0x3fffff00000000, 0x2d188c04080000)]
def active : List Sig := raw.filter (fun a => a != zero)


set_option maxRecDepth 24000 in
set_option maxHeartbeats 2000000 in
lemma sample_correct : ∀ s i, graph (sample raw s i) = s := by decide +kernel


-- Only the first pin of a NOT gate affects its output.
private def readsWireOne (g : Gate) : Bool :=
  if isNot g.op then g.inputs.head? == some 1 else g.inputs.contains 1

private lemma represented_append {w : List Sig} {z : Sig} {k t S} (h : Live k t S)
    (hz : represented w z) (sub : ∀ a ∈ S, a ∈ w ++ [z]) : ∀ a ∈ S, a ∈ w := by
  intro a ha
  rcases List.mem_append.mp (sub a ha) with hm | hm
  · exact hm
  · have eq : a = z := List.mem_singleton.mp hm
    subst a
    exact hz.resolve_right (fun hc => hc (live_proper h z ha))

private lemma collapse_read (w : List Sig) (g : Gate) (atOne : w.getD 1 zero = zero)
    (legal : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (reads : readsWireOne g = true) : represented w (gv w g) := by
  obtain ⟨op, args⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at legal
  have flat0 : represented w zero := Or.inr (fun hp => hp.1 rfl)
  have flat1 : represented w one := Or.inr (fun hp => hp.2 rfl)
  cases args with
  | nil => rcases legal.1 with rfl | rfl | rfl <;> simp [readsWireOne, isNot] at reads
  | cons a args =>
    cases args with
    | nil =>
      rcases legal.1 with rfl | rfl | rfl
      · simpa only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
          (bin_laws _).1] using get_rep w a
      · simpa only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
          (bin_laws _).2.1] using get_rep w a
      · have ha : a = 1 := by simpa [readsWireOne, isNot] using reads
        subst a
        change represented w (neg (w.getD 1 zero))
        rw [atOne, neg_laws.1]
        exact flat1
    | cons b args =>
      cases args with
      | cons => simp at legal
      | nil =>
        rcases legal.1 with rfl | rfl | rfl
        · have inds : 1 = a ∨ 1 = b := by simpa [readsWireOne, isNot] using reads
          rcases inds with rfl | rfl
          · change represented w (bin false (w.getD 1 zero) (bin false (w.getD b zero) one))
            rw [(bin_laws _).1, atOne, bin_comm false zero, (bin_laws _).2.2.1]
            exact flat0
          · change represented w (bin false (w.getD a zero) (bin false (w.getD 1 zero) one))
            rw [(bin_laws _).1, atOne, (bin_laws _).2.2.1]
            exact flat0
        · have inds : 1 = a ∨ 1 = b := by simpa [readsWireOne, isNot] using reads
          rcases inds with rfl | rfl
          · change represented w (bin true (w.getD 1 zero) (bin true (w.getD b zero) zero))
            rw [(bin_laws _).2.1, atOne, bin_comm true zero, (bin_laws _).2.1]
            exact get_rep w b
          · change represented w (bin true (w.getD a zero) (bin true (w.getD 1 zero) zero))
            rw [(bin_laws _).2.1, atOne, (bin_laws _).2.1]
            exact get_rep w a
        · have ha : a = 1 := by simpa [readsWireOne, isNot] using reads
          subst a
          change represented w (neg (w.getD 1 zero))
          rw [atOne, neg_laws.1]
          exact flat1

private def Agree (w v : List Bool) : Prop :=
  w.length = v.length ∧ ∀ i : ℕ, i ≠ 1 → w.getD i false = v.getD i false

private lemma ignore_read {w v : List Bool} (eq : Agree w v) (g : Gate)
    (legal : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp))
    (hn : readsWireOne g = false) :
    g.op.eval (g.inputs.map (fun i => w.getD i false)) =
      g.op.eval (g.inputs.map (fun i => v.getD i false)) := by
  obtain ⟨op,args⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at legal
  rcases legal with rfl | rfl | rfl
  · have same : args.map (fun i => w.getD i false) = args.map (fun i => v.getD i false) := by
      apply List.map_congr_left
      intro i hi
      refine eq.2 i (fun h => ?_)
      subst i
      simp [readsWireOne, isNot, hi] at hn
    rw [same]
  · have same : args.map (fun i => w.getD i false) = args.map (fun i => v.getD i false) := by
      apply List.map_congr_left
      intro i hi
      refine eq.2 i (fun h => ?_)
      subst i
      simp [readsWireOne, isNot, hi] at hn
    rw [same]
  · cases args with
    | nil => rfl
    | cons i l =>
      have h : i ≠ 1 := by simpa [readsWireOne, isNot] using hn
      change (!(w.getD i false)) = (!(v.getD i false))
      rw [eq.2 i h]

private lemma agree_append {w v : List Bool} (h : Agree w v) (b : Bool) :
    Agree (w ++ [b]) (v ++ [b]) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i hi
  by_cases hw : i < w.length
  · have hv : i < v.length := h.1 ▸ hw
    rw [List.getD_append _ _ _ _ hw, List.getD_append _ _ _ _ hv, h.2 i hi]
  · have hw' : w.length ≤ i := by omega
    have hv' : v.length ≤ i := h.1 ▸ hw'
    rw [List.getD_append_right _ _ _ _ hw', List.getD_append_right _ _ _ _ hv', h.1]

private def executeBool (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun l g => l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)]) w

private lemma ignores (gs : List Gate) (w v : List Bool) (eq : Agree w v)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp))
    (none : gs.any readsWireOne = false) : Agree (executeBool gs w) (executeBool gs v) := by
  induction gs generalizing w v with
  | nil => exact eq
  | cons g gs ih =>
    simp only [List.any_cons, Bool.or_eq_false_iff] at none
    obtain ⟨head, tail⟩ := none
    have hs := ignore_read eq g (legal g (by simp)) head
    simp only [executeBool, List.foldl_cons]
    rw [hs]
    exact ih _ _ (agree_append eq _) (fun a ha => legal a (by simp [ha])) tail

private lemma early_read (gs : List Gate) (w : List Bool) (h : 1 < w.length) :
    (executeBool gs w).getD 1 false = w.getD 1 false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [executeBool, List.foldl_cons]
    rw [show gs.foldl _ _ = executeBool gs
        (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) from rfl]
    rw [ih _ (by simp; omega), List.getD_append _ _ _ _ h]

-- The edge 1--4 forces the original circuit to read wire 1.
private lemma reads_pivotal (C : Circuit) (legal : FanInTwo C)
    (correct : ∀ x, C.eval (List.ofFn x) = graph x) : C.gates.any readsWireOne = true := by
  by_contra hn
  have none : C.gates.any readsWireOne = false := Bool.eq_false_of_not_eq_true hn
  let a : Fin 7 → Bool := fun i => decide (i.val = 4)
  let b : Fin 7 → Bool := fun i => decide (i.val = 1 ∨ i.val = 4)
  let c : Fin 7 → Bool := fun i => decide (i.val = 1)
  have noOut : C.output ≠ 1 := by
    intro h
    have solve := correct c
    change (executeBool C.gates (List.ofFn c)).getD C.output false = graph c at solve
    rw [h, early_read _ _ (by decide)] at solve
    exact Bool.noConfusion solve
  have hAgree : Agree (List.ofFn a) (List.ofFn b) := by
    refine ⟨rfl, ?_⟩
    intro i hi
    by_cases h : i < 7
    · have casesI : i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
      rcases casesI with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · rw [List.getD_eq_default _ _ (show (List.ofFn a).length ≤ i by simpa using Nat.le_of_not_gt h),
        List.getD_eq_default _ _ (show (List.ofFn b).length ≤ i by simpa using Nat.le_of_not_gt h)]
  have eq := (ignores C.gates _ _ hAgree (fun g hg => (legal g hg).1) none).2 _ noOut
  change C.eval (List.ofFn a) = C.eval (List.ofFn b) at eq
  rw [correct a, correct b] at eq
  exact Bool.false_ne_true eq

private def readsWireOneBinary (g : Gate) : Bool :=
  !isNot g.op && g.inputs.contains 1

private def OrderedApart (w v : List Bool) : Prop :=
  w.length = v.length ∧ 1 < w.length ∧ w.getD 1 false = true ∧ v.getD 1 false = false ∧
    ∀ i : Nat, i ≠ 1 → w.getD i false ≤ v.getD i false

private lemma orderedAppend {w v : List Bool} (h : OrderedApart w v)
    {p q : Bool} (hpq : p ≤ q) : OrderedApart (w ++ [p]) (v ++ [q]) := by
  obtain ⟨size,wide,ow,ov,rest⟩ := h
  have wide' : 1 < v.length := size ▸ wide
  refine ⟨by simp [size],by simp; omega,by rwa [List.getD_append _ _ _ _ wide],
    by rwa [List.getD_append _ _ _ _ wide'],?_⟩
  intro i hi
  by_cases hw : i < w.length
  · have hv : i < v.length := size ▸ hw
    rw [List.getD_append _ _ _ _ hw, List.getD_append _ _ _ _ hv]
    exact rest i hi
  · have nw : w.length ≤ i := Nat.le_of_not_gt hw
    have nv : v.length ≤ i := size ▸ nw
    rw [List.getD_append_right _ _ _ _ nw,List.getD_append_right _ _ _ _ nv, size]
    by_cases eq : i = v.length
    · simp [eq, hpq]
    · have h : 1 ≤ i - v.length := by omega
      rw [List.getD_eq_default _ _ (by simpa using h),
        List.getD_eq_default _ _ (by simpa using h)]

private lemma orderedFold (d : Bool) {w v : List Bool} (h : OrderedApart w v)
    (qs : List Nat) (no1 : ∀ j ∈ qs, j ≠ 1) :
    (if d then (qs.map (fun j => w.getD j false)).any id else (qs.map (fun j => w.getD j false)).all id) ≤
      (if d then (qs.map (fun j => v.getD j false)).any id else (qs.map (fun j => v.getD j false)).all id) := by
  induction qs with
  | nil => cases d <;> simp
  | cons a qs ih =>
    have e := h.2.2.2.2 a (no1 a (by simp))
    have f := ih (fun j hj => no1 j (by simp [hj]))
    have both (p q r s : Bool) (hp : p ≤ r) (hq : q ≤ s) :
        (if d then p || q else p && q) ≤ (if d then r || s else r && s) := by
      cases d <;> cases p <;> cases q <;> cases r <;> cases s <;> simp_all
    cases d <;> simpa using both _ _ _ _ e f

private lemma orderedGate {w v : List Bool} (h : OrderedApart w v) (g : Gate)
    (legal : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp))
    (noBinary : readsWireOneBinary g = false)
    (notPin : g.op = GateOp.not → g.inputs.head? = some 1) :
    g.op.eval (g.inputs.map (fun i => w.getD i false)) ≤
      g.op.eval (g.inputs.map (fun i => v.getD i false)) := by
  obtain ⟨op,args⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at legal
  rcases legal with rfl | rfl | rfl
  · have np : 1 ∉ args := by simpa [readsWireOneBinary,isNot] using noBinary
    exact orderedFold false h args (fun j hj e => np (e ▸ hj))
  · have np : 1 ∉ args := by simpa [readsWireOneBinary,isNot] using noBinary
    exact orderedFold true h args (fun j hj e => np (e ▸ hj))
  · cases args with
    | nil => simp at notPin
    | cons i l =>
      have e : i = 1 := by simpa using notPin rfl
      subst i
      change (!(w.getD 1 false)) ≤ (!(v.getD 1 false))
      rw [h.2.2.1, h.2.2.2.1]
      decide

private lemma orderedRun (gs : List Gate) {w v : List Bool} (h : OrderedApart w v)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp))
    (none : gs.any readsWireOneBinary = false)
    (notPin : ∀ g ∈ gs, g.op = GateOp.not → g.inputs.head? = some 1) :
    OrderedApart (executeBool gs w) (executeBool gs v) := by
  induction gs generalizing w v with
  | nil => exact h
  | cons g gs ih =>
    obtain ⟨first,other⟩ := Bool.or_eq_false_iff.mp none
    have gate := orderedGate h g (legal g (by simp)) first (notPin g (by simp))
    exact ih (orderedAppend h gate) (fun g hg => legal g (by simp [hg])) other
      (fun g hg => notPin g (by simp [hg]))

private lemma readBinaryPivotal (C : Circuit) (legal : FanInTwo C)
    (unique : ∀ i j : Fin C.gates.length, (C.gates.get i).op = GateOp.not →
      (C.gates.get j).op = GateOp.not → i = j)
    (correct : ∀ x, C.eval (List.ofFn x) = graph x) :
    C.gates.any readsWireOneBinary = true := by
  by_contra hh
  have hn : C.gates.any readsWireOneBinary = false := Bool.eq_false_of_not_eq_true hh
  obtain ⟨g,hg,hread⟩ := List.any_eq_true.mp (reads_pivotal C legal correct)
  have gnot : g.op = GateOp.not := by
    by_contra h
    have no : isNot g.op = false := by cases e : g.op <;> simp_all [isNot]
    have q : readsWireOneBinary g = true := by simpa [readsWireOneBinary, readsWireOne, no] using hread
    exact Bool.false_ne_true (hn.symm.trans (List.any_eq_true.mpr ⟨g,hg,q⟩))
  have pin : g.inputs.head? = some 1 := by simpa [readsWireOne,isNot,gnot] using hread
  have allNotPin (q : Gate) (hq : q ∈ C.gates) (qo : q.op = GateOp.not) : q.inputs.head? = some 1 := by
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hg
    obtain ⟨j,hj⟩ := List.mem_iff_get.mp hq
    have ij := unique i j (hi.symm ▸ gnot) (hj.symm ▸ qo)
    rw [← hj, ← ij, hi, pin]
  let a : Fin 7 → Bool := fun i => decide (i.val = 1 ∨ i.val = 4)
  let b : Fin 7 → Bool := fun i => decide (i.val = 4)
  let c : Fin 7 → Bool := fun i => decide (i.val = 1)
  have noOut : C.output ≠ 1 := by
    intro h
    have solve := correct c
    change (executeBool C.gates (List.ofFn c)).getD C.output false = graph c at solve
    rw [h, early_read _ _ (by decide)] at solve
    exact Bool.noConfusion solve
  have seed : OrderedApart (List.ofFn a) (List.ofFn b) := by
    refine ⟨rfl,by decide,by decide,by decide,?_⟩
    intro i hi
    by_cases h : i < 7
    · have casesI : i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
      rcases casesI with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · rw [List.getD_eq_default _ _ (show (List.ofFn a).length ≤ i by simpa using Nat.le_of_not_gt h),
        List.getD_eq_default _ _ (show (List.ofFn b).length ≤ i by simpa using Nat.le_of_not_gt h)]
  have eq := (orderedRun C.gates seed (fun g hg => (legal g hg).1) hn allNotPin).2.2.2.2 _ noOut
  change C.eval (List.ofFn a) ≤ C.eval (List.ofFn b) at eq
  rw [correct a, correct b] at eq
  exact (show ¬graph a ≤ graph b by decide) eq

private lemma extractBinaryCut (gs : List Gate) (w : List Sig) (wide : 1 < w.length)
    (atOne : w.getD 1 zero = zero)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2)
    (hout : target ∈ execute gs w) :
    ∃ k t S, k + gs.countP (fun g => isNot g.op) + (gs.any readsWireOneBinary).toNat ≤ gs.length + t ∧
      t ≤ gs.countP (fun g => isNot g.op) ∧ Live k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0, 0, {target}, by simp, by simp, Live.stop, by simpa [execute] using hout⟩
  | cons g gs ih =>
    have hg := legal g (by simp)
    obtain ⟨k,t,S,hk,hcount,ht,hs⟩ :=
      ih (w ++ [gv w g]) (by simp; omega)
        (by simpa only [List.getD_append _ _ _ _ wide] using atOne)
        (fun a ha => legal a (by simp [ha])) hout
    have same : readsWireOneBinary g = (!isNot g.op && readsWireOne g) := by
      cases q : isNot g.op <;> simp [readsWireOneBinary,readsWireOne,q]
    cases hr : readsWireOne g with
    | true =>
      refine ⟨k, t, S, ?_, ?_, ht, represented_append ht (collapse_read w g atOne hg hr) hs⟩
      · cases h : gs.any readsWireOneBinary <;> cases hf : isNot g.op <;>
          simp [List.any_cons,same,hr,hf,h] at hk ⊢ <;> omega
      · cases h : isNot g.op <;> simp [h] at hcount ⊢ <;> omega
    | false =>
      obtain ⟨l,u,T,_,hc,hl,hu,hT⟩ := pull_gate ht (gate_rep w g hg) hs
      refine ⟨l,u,T,?_,?_,hu,hT⟩
      · cases hf : isNot g.op <;> simp [List.any_cons,same,hr,hf] at hl ⊢ <;> omega
      · cases hf : isNot g.op <;> simp [hf] at hc ⊢ <;> omega

private lemma countNot {gs : List Gate}
    (unique : ∀ i j : Fin gs.length, (gs.get i).op = GateOp.not →
      (gs.get j).op = GateOp.not → i = j) :
    gs.countP (fun g => isNot g.op) ≤ 1 := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have uniqueTail (i j : Fin gs.length) (hi : (gs.get i).op = GateOp.not)
        (hj : (gs.get j).op = GateOp.not) : i = j := by
      have h := unique i.succ j.succ hi hj
      exact Fin.succ_inj.mp h
    have bound := ih uniqueTail
    cases hr : isNot g.op with
    | false => simpa [hr] using bound
    | true =>
      have head : g.op = GateOp.not := by cases e : g.op <;> simp [e, isNot] at hr ⊢
      have none : ∀ a ∈ gs, isNot a.op = false := by
        intro a ha
        obtain ⟨i, eq⟩ := List.mem_iff_get.mp ha
        by_contra hn
        have op : a.op = GateOp.not := by cases e : a.op <;> simp [e, isNot] at hn ⊢
        have pos := unique 0 i.succ head (eq.symm ▸ op)
        exact (Fin.succ_ne_zero i) pos.symm
      have hz : gs.countP (fun g => isNot g.op) = 0 := List.countP_eq_zero.mpr (fun a ha => by rw [none a ha]; decide)
      simp [hr, hz]

private def reverseIndex (i : Fin bitCount) : Fin bitCount :=
  ⟨(([48, 45, 47, 46, 53, 52, 43, 44, 40, 42, 41, 23, 22, 51, 31, 30, 39, 36, 38, 37, 50, 49, 12, 11, 29, 28, 27, 26, 25, 24, 15, 14, 34, 35, 32, 33, 17, 19, 18, 16, 8, 10, 9, 6, 7, 1, 3, 2, 0, 21, 20, 13, 5, 4] : List Nat).getD i.val 0) % bitCount, Nat.mod_lt _ (by decide)⟩

private def reversePermutation : BitPerm :=
  ⟨reverseIndex, reverseIndex, by decide, by decide⟩

private def automorphisms : List BitPerm := [Equiv.refl _, reversePermutation]

private def reps0 : List SearchState := [(0, [(0x302030, 0x2208102090), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]),
  (0, [(0xf003f27ff, 0x23081120d1), (0x600ff3f3fffff, 0x202731b3168f5), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]),
  (0, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x600ff3f3fffff, 0x202731b3168f5), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]),
  (0, [(0x3f, 0x0), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]),
  (0, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x81f0fc7ffe7ff, 0x47634951eaff), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]),
  (0, [(0x27c0, 0x0), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]),
  (0, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x31e00ff83fffff, 0x10e423e895b7d9), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]),
  (0, [(0x3f0000, 0x0), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]),
  (0, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3e000fffff27ff, 0x3e902bbebf24d1), (0x3fffff00000000, 0x2d188c04080000)]),
  (0, [(0xf00000000, 0x0), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]),
  (0, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000), (0x3fffff003f27ff, 0x2d18af0c1920d1)]),
  (0, [(0x700c030, 0x24001004824), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]),
  (0, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0xe1ff0fff0f83f, 0x247725b70eabe), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]),
  (0, [(0x3800f800, 0x0), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]),
  (0, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x37e0f0ff30fff0, 0x12e672fbb4ffbc), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]),
  (0, [(0xf003f27ff, 0x23081120d1), (0x600003f300000, 0x2000012200000), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]),
  (0, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3e00f0fffff830, 0x3e927abfbe6cb4), (0x3fffff00000000, 0x2d188c04080000)]),
  (0, [(0xc000c000, 0x440040008208), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]),
  (0, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x39ff00ffc0ffff, 0x10e740e1c4df2e), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)])]

private def permutationKeys0 : List (Nat × Nat) := [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (0, 15), (0, 16), (1, 7), (1, 8), (0, 17), (0, 18), (1, 13), (1, 14), (1, 5), (1, 6), (1, 11), (1, 12), (1, 3), (1, 4), (1, 0), (1, 1), (1, 2)]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma coverOrbits0 : checkOrbits automorphisms reps0 (kids 7 (0, active)) permutationKeys0 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma done0_0 :
    ((0, [(0x302030, 0x2208102090), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2.Nodup ∧ search 7 ((0, [(0x302030, 0x2208102090), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).1 ((0, [(0x302030, 0x2208102090), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma done0_1 :
    ((0, [(0xf003f27ff, 0x23081120d1), (0x600ff3f3fffff, 0x202731b3168f5), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2.Nodup ∧ search 7 ((0, [(0xf003f27ff, 0x23081120d1), (0x600ff3f3fffff, 0x202731b3168f5), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).1 ((0, [(0xf003f27ff, 0x23081120d1), (0x600ff3f3fffff, 0x202731b3168f5), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma done0_2 :
    ((0, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x600ff3f3fffff, 0x202731b3168f5), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2.Nodup ∧ search 7 ((0, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x600ff3f3fffff, 0x202731b3168f5), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).1 ((0, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x600ff3f3fffff, 0x202731b3168f5), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma done0_3 :
    ((0, [(0x3f, 0x0), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2.Nodup ∧ search 7 ((0, [(0x3f, 0x0), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).1 ((0, [(0x3f, 0x0), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma done0_4 :
    ((0, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x81f0fc7ffe7ff, 0x47634951eaff), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2.Nodup ∧ search 7 ((0, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x81f0fc7ffe7ff, 0x47634951eaff), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).1 ((0, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x81f0fc7ffe7ff, 0x47634951eaff), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma done0_5 :
    ((0, [(0x27c0, 0x0), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2.Nodup ∧ search 7 ((0, [(0x27c0, 0x0), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).1 ((0, [(0x27c0, 0x0), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma done0_6 :
    ((0, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x31e00ff83fffff, 0x10e423e895b7d9), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2.Nodup ∧ search 7 ((0, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x31e00ff83fffff, 0x10e423e895b7d9), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).1 ((0, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x31e00ff83fffff, 0x10e423e895b7d9), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma done0_7 :
    ((0, [(0x3f0000, 0x0), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2.Nodup ∧ search 7 ((0, [(0x3f0000, 0x0), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).1 ((0, [(0x3f0000, 0x0), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma done0_8 :
    ((0, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3e000fffff27ff, 0x3e902bbebf24d1), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2.Nodup ∧ search 7 ((0, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3e000fffff27ff, 0x3e902bbebf24d1), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).1 ((0, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3e000fffff27ff, 0x3e902bbebf24d1), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma done0_9 :
    ((0, [(0xf00000000, 0x0), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2.Nodup ∧ search 7 ((0, [(0xf00000000, 0x0), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).1 ((0, [(0xf00000000, 0x0), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma done0_10 :
    ((0, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000), (0x3fffff003f27ff, 0x2d18af0c1920d1)]) : SearchState).2.Nodup ∧ search 7 ((0, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000), (0x3fffff003f27ff, 0x2d18af0c1920d1)]) : SearchState).1 ((0, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000), (0x3fffff003f27ff, 0x2d18af0c1920d1)]) : SearchState).2 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma done0_11 :
    ((0, [(0x700c030, 0x24001004824), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2.Nodup ∧ search 7 ((0, [(0x700c030, 0x24001004824), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).1 ((0, [(0x700c030, 0x24001004824), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma done0_12 :
    ((0, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0xe1ff0fff0f83f, 0x247725b70eabe), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2.Nodup ∧ search 7 ((0, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0xe1ff0fff0f83f, 0x247725b70eabe), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).1 ((0, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0xe1ff0fff0f83f, 0x247725b70eabe), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma done0_13 :
    ((0, [(0x3800f800, 0x0), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2.Nodup ∧ search 7 ((0, [(0x3800f800, 0x0), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).1 ((0, [(0x3800f800, 0x0), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma done0_14 :
    ((0, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x37e0f0ff30fff0, 0x12e672fbb4ffbc), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2.Nodup ∧ search 7 ((0, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x37e0f0ff30fff0, 0x12e672fbb4ffbc), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).1 ((0, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x37e0f0ff30fff0, 0x12e672fbb4ffbc), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma done0_15 :
    ((0, [(0xf003f27ff, 0x23081120d1), (0x600003f300000, 0x2000012200000), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2.Nodup ∧ search 7 ((0, [(0xf003f27ff, 0x23081120d1), (0x600003f300000, 0x2000012200000), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).1 ((0, [(0xf003f27ff, 0x23081120d1), (0x600003f300000, 0x2000012200000), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma done0_16 :
    ((0, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3e00f0fffff830, 0x3e927abfbe6cb4), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2.Nodup ∧ search 7 ((0, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3e00f0fffff830, 0x3e927abfbe6cb4), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).1 ((0, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3e00f0fffff830, 0x3e927abfbe6cb4), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma done0_17 :
    ((0, [(0xc000c000, 0x440040008208), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2.Nodup ∧ search 7 ((0, [(0xc000c000, 0x440040008208), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).1 ((0, [(0xc000c000, 0x440040008208), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma done0_18 :
    ((0, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x39ff00ffc0ffff, 0x10e740e1c4df2e), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2.Nodup ∧ search 7 ((0, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x39ff00ffc0ffff, 0x10e740e1c4df2e), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).1 ((0, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x39ff00ffc0ffff, 0x10e740e1c4df2e), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2 = false := by decide +kernel

private lemma excluded0 : ∀ r ∈ reps0, r.2.Nodup ∧ search 7 r.1 r.2 = false := by
  intro r mem
  simp only [reps0, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact done0_0
  · exact done0_1
  · exact done0_2
  · exact done0_3
  · exact done0_4
  · exact done0_5
  · exact done0_6
  · exact done0_7
  · exact done0_8
  · exact done0_9
  · exact done0_10
  · exact done0_11
  · exact done0_12
  · exact done0_13
  · exact done0_14
  · exact done0_15
  · exact done0_16
  · exact done0_17
  · exact done0_18

private def reps1 : List SearchState := [(0, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3ffff0ffc0d800, 0x3fffdcf7eedf2e), (0x3fffff00000000, 0x2d188c04080000)]),
  (0, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x39ff0fc0cf07cf, 0x3dfd8de4cf974b), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]),
  (0, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x37e0ff383f3fc0, 0x3fb8bfbebf35d1), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]),
  (1, [(0x302030, 0x2208102090), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]),
  (1, [(0xf003f27ff, 0x23081120d1), (0x600ff3f3fffff, 0x202731b3168f5), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]),
  (1, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x600ff3f3fffff, 0x202731b3168f5), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]),
  (1, [(0x3f, 0x0), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]),
  (1, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x81f0fc7ffe7ff, 0x47634951eaff), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]),
  (1, [(0x27c0, 0x0), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]),
  (1, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x31e00ff83fffff, 0x10e423e895b7d9), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]),
  (1, [(0x3f0000, 0x0), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]),
  (1, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3e000fffff27ff, 0x3e902bbebf24d1), (0x3fffff00000000, 0x2d188c04080000)]),
  (1, [(0xf00000000, 0x0), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]),
  (1, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000), (0x3fffff003f27ff, 0x2d18af0c1920d1)]),
  (1, [(0x700c030, 0x24001004824), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]),
  (1, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0xe1ff0fff0f83f, 0x247725b70eabe), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]),
  (1, [(0x3800f800, 0x0), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]),
  (1, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x37e0f0ff30fff0, 0x12e672fbb4ffbc), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]),
  (1, [(0xf003f27ff, 0x23081120d1), (0x600003f300000, 0x2000012200000), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]),
  (1, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3e00f0fffff830, 0x3e927abfbe6cb4), (0x3fffff00000000, 0x2d188c04080000)]),
  (1, [(0xc000c000, 0x440040008208), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]),
  (1, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x39ff00ffc0ffff, 0x10e740e1c4df2e), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)])]

private def permutationKeys1 : List (Nat × Nat) := [(0, 0), (0, 1), (0, 2), (1, 2), (1, 1), (1, 0), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (0, 15), (0, 16), (0, 17), (0, 18), (0, 19), (1, 10), (1, 11), (0, 20), (0, 21), (1, 16), (1, 17), (1, 8), (1, 9), (1, 14), (1, 15), (1, 6), (1, 7), (1, 3), (1, 4), (1, 5)]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma coverOrbits1 : checkOrbits automorphisms reps1 (kids 8 (1, active)) permutationKeys1 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma done1_0 :
    ((0, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3ffff0ffc0d800, 0x3fffdcf7eedf2e), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2.Nodup ∧ search 8 ((0, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3ffff0ffc0d800, 0x3fffdcf7eedf2e), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).1 ((0, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3ffff0ffc0d800, 0x3fffdcf7eedf2e), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma done1_1 :
    ((0, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x39ff0fc0cf07cf, 0x3dfd8de4cf974b), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2.Nodup ∧ search 8 ((0, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x39ff0fc0cf07cf, 0x3dfd8de4cf974b), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).1 ((0, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x39ff0fc0cf07cf, 0x3dfd8de4cf974b), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma done1_2 :
    ((0, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x37e0ff383f3fc0, 0x3fb8bfbebf35d1), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2.Nodup ∧ search 8 ((0, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x37e0ff383f3fc0, 0x3fb8bfbebf35d1), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).1 ((0, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x37e0ff383f3fc0, 0x3fb8bfbebf35d1), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma done1_3 :
    ((1, [(0x302030, 0x2208102090), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2.Nodup ∧ search 8 ((1, [(0x302030, 0x2208102090), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).1 ((1, [(0x302030, 0x2208102090), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma done1_4 :
    ((1, [(0xf003f27ff, 0x23081120d1), (0x600ff3f3fffff, 0x202731b3168f5), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2.Nodup ∧ search 8 ((1, [(0xf003f27ff, 0x23081120d1), (0x600ff3f3fffff, 0x202731b3168f5), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).1 ((1, [(0xf003f27ff, 0x23081120d1), (0x600ff3f3fffff, 0x202731b3168f5), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma done1_5 :
    ((1, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x600ff3f3fffff, 0x202731b3168f5), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2.Nodup ∧ search 8 ((1, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x600ff3f3fffff, 0x202731b3168f5), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).1 ((1, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x600ff3f3fffff, 0x202731b3168f5), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma done1_6 :
    ((1, [(0x3f, 0x0), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2.Nodup ∧ search 8 ((1, [(0x3f, 0x0), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).1 ((1, [(0x3f, 0x0), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma done1_7 :
    ((1, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x81f0fc7ffe7ff, 0x47634951eaff), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2.Nodup ∧ search 8 ((1, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x81f0fc7ffe7ff, 0x47634951eaff), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).1 ((1, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x81f0fc7ffe7ff, 0x47634951eaff), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma done1_8 :
    ((1, [(0x27c0, 0x0), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2.Nodup ∧ search 8 ((1, [(0x27c0, 0x0), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).1 ((1, [(0x27c0, 0x0), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma done1_9 :
    ((1, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x31e00ff83fffff, 0x10e423e895b7d9), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2.Nodup ∧ search 8 ((1, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x31e00ff83fffff, 0x10e423e895b7d9), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).1 ((1, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x31e00ff83fffff, 0x10e423e895b7d9), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma done1_10 :
    ((1, [(0x3f0000, 0x0), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2.Nodup ∧ search 8 ((1, [(0x3f0000, 0x0), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).1 ((1, [(0x3f0000, 0x0), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma done1_11 :
    ((1, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3e000fffff27ff, 0x3e902bbebf24d1), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2.Nodup ∧ search 8 ((1, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3e000fffff27ff, 0x3e902bbebf24d1), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).1 ((1, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3e000fffff27ff, 0x3e902bbebf24d1), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma done1_12 :
    ((1, [(0xf00000000, 0x0), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2.Nodup ∧ search 8 ((1, [(0xf00000000, 0x0), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).1 ((1, [(0xf00000000, 0x0), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma done1_13 :
    ((1, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000), (0x3fffff003f27ff, 0x2d18af0c1920d1)]) : SearchState).2.Nodup ∧ search 8 ((1, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000), (0x3fffff003f27ff, 0x2d18af0c1920d1)]) : SearchState).1 ((1, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000), (0x3fffff003f27ff, 0x2d18af0c1920d1)]) : SearchState).2 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma done1_14 :
    ((1, [(0x700c030, 0x24001004824), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2.Nodup ∧ search 8 ((1, [(0x700c030, 0x24001004824), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).1 ((1, [(0x700c030, 0x24001004824), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma done1_15 :
    ((1, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0xe1ff0fff0f83f, 0x247725b70eabe), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2.Nodup ∧ search 8 ((1, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0xe1ff0fff0f83f, 0x247725b70eabe), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).1 ((1, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0xe1ff0fff0f83f, 0x247725b70eabe), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma done1_16 :
    ((1, [(0x3800f800, 0x0), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2.Nodup ∧ search 8 ((1, [(0x3800f800, 0x0), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).1 ((1, [(0x3800f800, 0x0), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma done1_17 :
    ((1, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x37e0f0ff30fff0, 0x12e672fbb4ffbc), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2.Nodup ∧ search 8 ((1, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x37e0f0ff30fff0, 0x12e672fbb4ffbc), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).1 ((1, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x37e0f0ff30fff0, 0x12e672fbb4ffbc), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma done1_18 :
    ((1, [(0xf003f27ff, 0x23081120d1), (0x600003f300000, 0x2000012200000), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2.Nodup ∧ search 8 ((1, [(0xf003f27ff, 0x23081120d1), (0x600003f300000, 0x2000012200000), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).1 ((1, [(0xf003f27ff, 0x23081120d1), (0x600003f300000, 0x2000012200000), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma done1_19 :
    ((1, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3e00f0fffff830, 0x3e927abfbe6cb4), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2.Nodup ∧ search 8 ((1, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3e00f0fffff830, 0x3e927abfbe6cb4), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).1 ((1, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3e00f0fffff830, 0x3e927abfbe6cb4), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma done1_20 :
    ((1, [(0xc000c000, 0x440040008208), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2.Nodup ∧ search 8 ((1, [(0xc000c000, 0x440040008208), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).1 ((1, [(0xc000c000, 0x440040008208), (0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma done1_21 :
    ((1, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x39ff00ffc0ffff, 0x10e740e1c4df2e), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2.Nodup ∧ search 8 ((1, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x39ff00ffc0ffff, 0x10e740e1c4df2e), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).1 ((1, [(0xf003f27ff, 0x23081120d1), (0x600f03f30f830, 0x202721b3068b4), (0x81f00c7c0c03f, 0x47404140ca2e), (0x31e000f800ffc0, 0x10e400e0849708), (0x39ff00ffc0ffff, 0x10e740e1c4df2e), (0x3e0000ffff0000, 0x3e9008b6ae0400), (0x3fffff00000000, 0x2d188c04080000)]) : SearchState).2 = false := by decide +kernel

private lemma excluded1 : ∀ r ∈ reps1, r.2.Nodup ∧ search 8 r.1 r.2 = false := by
  intro r mem
  simp only [reps1, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact done1_0
  · exact done1_1
  · exact done1_2
  · exact done1_3
  · exact done1_4
  · exact done1_5
  · exact done1_6
  · exact done1_7
  · exact done1_8
  · exact done1_9
  · exact done1_10
  · exact done1_11
  · exact done1_12
  · exact done1_13
  · exact done1_14
  · exact done1_15
  · exact done1_16
  · exact done1_17
  · exact done1_18
  · exact done1_19
  · exact done1_20
  · exact done1_21

set_option maxRecDepth 24000 in
lemma lowerBound (C : Circuit) (legal : FanInTwo C)
    (unique : ∀ i j : Fin C.gates.length, (C.gates.get i).op = GateOp.not →
      (C.gates.get j).op = GateOp.not → i = j)
    (hasNot : ∃ g ∈ C.gates, g.op = GateOp.not)
    (correct : ∀ x, C.eval (List.ofFn x) = graph x) : 11 ≤ C.size := by
  by_contra small
  obtain ⟨k,t,S,hk,hcount,live,sub⟩ :=
    extractBinaryCut C.gates raw (by decide) (by decide) legal
      (circuit_target raw rfl sample_correct C legal correct)
  have read := readBinaryPivotal C legal unique correct
  simp only [read, Bool.toNat_true] at hk
  have sub' (a) (ha : a ∈ S) : a ∈ active := by
    have hh := (live_proper live a ha).1
    simpa [active, hh] using sub a ha
  have nd : active.Nodup := by decide +kernel
  have eq := necessary active (by decide +kernel) live sub'
  change ¬ 11 ≤ C.gates.length at small
  have tb := hcount.trans (countNot unique)
  have posNot : 0 < C.gates.countP (fun g => isNot g.op) := by
    obtain ⟨g,hg,hn⟩ := hasNot
    by_contra! bad
    have eq : C.gates.countP (fun g => isNot g.op) = 0 := by omega
    have forbid := List.countP_eq_zero.mp eq g hg
    simp [hn,isNot] at forbid
  have casesT : t = 0 ∨ t = 1 := by omega
  rcases casesT with rfl | rfl
  · exact noLive_of_orbits nd (by decide) automorphisms reps0 permutationKeys0 coverOrbits0 excluded0 k (by omega)
      (eq.symm ▸ live)
  · exact noLive_of_orbits nd (by decide) automorphisms reps1 permutationKeys1 coverOrbits1 excluded1 k (by omega)
      (eq.symm ▸ live)

def monotoneCircuit : Circuit :=
  ⟨[⟨.or, [0,1]⟩, ⟨.or, [7,2]⟩, ⟨.or, [7,3]⟩, ⟨.or, [7,6]⟩,
    ⟨.or, [3,4]⟩, ⟨.or, [4,6]⟩, ⟨.and, [5,9]⟩, ⟨.and, [8,12]⟩,
    ⟨.and, [11,10]⟩, ⟨.or, [13,14]⟩, ⟨.or, [16,15]⟩], 17⟩

lemma witness_mono :
    ∀ g ∈ monotoneCircuit.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      g.inputs.length ≤ 2 := by
  intro g hg
  simp only [monotoneCircuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2000000 in
lemma witness_eval : ∀ x : Fin 7 → Bool, monotoneCircuit.eval (List.ofFn x) = graph x := by
  decide +kernel

end PEqualNP.Outside.L_meta_11090

open PEqualNP.Outside.L_meta_11090 in
theorem PEqualNP.Outside.L_meta_11090 :
∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal unique correct
  have valid : PEqualNP.MetaComplexity.FanInTwo ⟨gates, o⟩ := by
    intro g hg
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using legal g hg
  by_cases hasNot : ∃ g ∈ gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · have lower := lowerBound ⟨gates, o⟩ valid unique hasNot correct
    exact ⟨monotoneCircuit.gates, monotoneCircuit.output, witness_mono, lower, witness_eval⟩
  · refine ⟨gates, o, ?_, le_rfl, correct⟩
    intro g hg
    obtain ⟨ops, width⟩ := legal g hg
    exact ⟨ops.imp_right (fun p => p.resolve_right (fun hn => hasNot ⟨g,hg,hn⟩)), width⟩
