import PEqualNP.Defs
-- The live-wire checker is adapted from ljste's PR 2918 and jfsantoropereira's L-meta-1007.
-- Adapted from the signed live-wire certificate in L_meta_8721. Apache-2.0.
namespace PEqualNP.Outside.L_meta_12398

abbrev B := BitVec 60
abbrev Sig := B × B
def top : B := BitVec.allOnes 60
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
  by_cases hi : i < 60
  · cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases ht : decide (0<t) <;>
      simp only [sep,neg,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 60 ≤ i)] at h

private lemma sep_binary (t d : Bool) (a b : Sig) (i : Nat)
    (h : (sep t (bin d a b)).getLsbD i = true) :
    (sep t a).getLsbD i = true ∨ (sep t b).getLsbD i = true := by
  by_cases hi : i < 60
  · cases t <;> cases d <;>
      cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases hu : b.1.getLsbD i <;> cases hv : b.2.getLsbD i <;>
      simp only [sep,bin,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,hu,hv] at h ⊢ <;> first | contradiction | decide
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 60 ≤ i)] at h

private lemma sep_weaken (t : Nat) (a : Sig) (i : Nat) (hi : i < 60)
    (h : (sep (decide (0<t)) a).getLsbD i = true) : (sep true a).getLsbD i = true := by
  cases ht : decide (0<t) <;> cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
    simp only [sep,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide

private lemma live_sep {k t S} (h : Live k t S) (i : Nat) (hi : i < 60) :
    ∃ a ∈ S, (sep (decide (0<t)) a).getLsbD i = true := by
  induction h using liveInd with
  | stop =>
    refine ⟨target,by simp,?_⟩
    change (BitVec.allOnes 60 &&& ~~~(0 : B)).getLsbD i = true
    rw [BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_allOnes (v := 60)]
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

def bit (side : Bool) (i : Fin 60) (a : Sig) : Bool :=
  (if side then a.1 else a.2).getLsbD i.val

private lemma bit_zero (s i) : bit s i zero = false := by cases s <;> simp [bit,zero]
private lemma bit_one (s i) : bit s i one = true := by
  cases s <;> change (BitVec.allOnes 60).getLsbD i.val = true <;> rw [BitVec.getLsbD_allOnes] <;> simp
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


def graph (x : Fin 6 → Bool) : Bool := Nat.testBit (4278124160 * 2 ^ 32 + 4269834368) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def sample (raw : List Sig) (s : Bool) (i : Fin 60) (j : Fin 6) := bit s i (raw.getD j.val zero)
private lemma sample_list (raw : List Sig) (raw_id : List.ofFn (fun j : Fin 6 => raw.getD j.val zero) = raw) (s i) : List.ofFn (sample raw s i) = raw.map (bit s i) := by
  calc
    _ = (List.ofFn (fun j : Fin 6 => raw.getD j.val zero)).map (bit s i) := by rw [List.map_ofFn]; rfl
    _ = _ := by rw [raw_id]

private lemma circuit_target (raw : List Sig) (raw_id : List.ofFn (fun j : Fin 6 => raw.getD j.val zero) = raw)
    (sample_ok : ∀ s i, graph (sample raw s i) = s) (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = graph x) : target ∈ execute C.gates raw := by
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

def raw : List Sig := [(172012848559525887, 27893262286163382), (397410814694388223, 109145253063287149), (719454404293296639, 141867717656051931), (1008810714460061240, 1008809260339649080), (1152917106577113024, 1105268670664718272), (1152921504590069760, 1057621724557737984)]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma sample_correct : ∀ s i, graph (sample raw s i) = s := by decide +kernel

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

private def wireDataPacked (i : Nat) : Nat := (if i < 60 then (if i < 30 then (if i < 15 then (if i < 7 then (if i < 3 then (if i < 1 then 0x3800002a520a94838000000000000007000000000000007000000000000000e0424084802120000000000000000011080000044204100000000000000008841108100000100000000000000005010000014048200000000000000002808501200000200000000000000000290000000a50400000000000000000148029400000400000000000000000002210088400900000000000000000000a020280812000000000000000000000520014824 else (if i < 2 then 0x7000000800100027200000000000000e00000100020021e000000000000001ff15292a520fdedff0000000000001c715290000054a5c70000000000001c71500000005400c30000000000001c710280000040a1450000000000001c70421000001085860000000000001c015290000054a5c000000000000003f00002a520a9483f00000000000003f00002a000a8001b00000000000003f00002050081402d00000000000003f000008420210836 else 0x318e38000008420210830000000000300e00040108020300c920000000003001ff0400080003000920000000000e00000100020000e120000000000001ffc715290052057ffe700000000001fe3f00292a520abff3f00000000001fe0000290052003ff2400000000001fe0000290000002b70000000000001fe00000000520035a2000000000001f00000280050001e124000000000018e00002100420018d240000000000181ff002000400018124)) else (if i < 5 then (if i < 4 then 0xc1f038000020500814028000000000c07000100820100c06049000000000c001ff100020000c000490000000003ffe0005290a5203fffb60000000003e0fc715290a0207ebfd70000000003e0e3f05012a520bf5ebf0000000003e0e0005010a0203e1e920000000003e0e000501000001616800000000003e0e0000000a0202a1a100000000003e000005000a0003c0092000000000318fff042108420318db6000000000318fc0042100000108580 else 0xfe01c01500000005400c0000000000fe003800002a000a80018000000000f1ffff142928520f1edff000000000cffe00112922520cfff6d000000000ce71c7152922100def7cf000000000ce703f11082a520ef7a7f000000000ce7000110822100ce7249000000000ce7000110800000463240000000000ce70000000221008a5208000000000ce0000110022000cc0049000000000c1f1ff102820500c1e16d000000000c1f1c010280000040a140) else (if i < 6 then 0xffffff15290842077bff6000000000ffffff15002a520ff5afb000000000ffffff10282a520ebfb7d000000000ffffff04212a520bbdfbe000000000fffff815292a520fffff8000000000ffffc015290000056b7c0000000000fffe3800002a520ab5a38000000000fffe00000000000021200000000000fff1ff15282a500fde1ff000000000ff8fff15212a420fd8dff000000000fe7e0015092a120fe7edb000000000fe01ff15002a000fc00db else 0x70001ff1fbdbf7b7fdedff0000000070001ff0000000000000000000000070001c71fbd9529754a5c700000000700003f0a94bf7b7a9483f0000000070000070a94952970000070000000070000070a80150030000030000000070000070814102850000050000000070000070210842160000060000000070000000a9495297000000000000000ffffff15292a520ffffff000000000ffffff15292a000feb7db000000000ffffff152920500d7f7ed))) else (if i < 11 then (if i < 9 then (if i < 8 then 0x7f801fe00003d80ffc03ff240000007f800003f0014aaffca9483f0000007f8000000001480ffc0148240000007f8000000001480adc0000000000007f8000000000000d680148200000007c000000000140078401402400000063800000000108063401082400000060700003f0010006040100240000006000180380000004000100200000001c00000000004009c8004000000000038000000000080878000800000000007ffffff1fbdbf7b7ffffff else 0xf83800000000000a86828081000000f80000000002800f00228001200000c63f318fff06318c636318db600000c63f00003f02108c63621083600000c63f00000002108421600000000000c63800003800000842021083000000c03800000002008c03220081200000c00700003f02000c00220001200000c0003000380000080002000100000038000000000080038480800000000007ff0000070a9495fff0148270000007f8ffffff153daaffcffffff) else (if i < 10 then 0x307c70000000814102850000000000307c00000380000205008140280000301c000000008043018180400900003000700003f080030001800009000030000c0003800002000080000800000fff800000002948fffe29483600000f83f0000070a949faff28081700000f838ffffff17a9afd7affffff00000f8383e0e0007818f87a3e1e9200000f83800003f0280afd7aa9483f00000f83800000002808f87a28081200000f83800000002808585a000000 else 0x3c7ff00003f0a14bc7b7a1483f000033ff80000000894b3ffd89482d0000339c70000070a94b7bdf88400f0000339c0ffffff1dad3bde9ffffff0000339c0ce7000198c339c9ce72490000339c000003f08843bde9a9483f0000339c00000000884339c98840090000339c00000000884118c90000000000339c00000000000229488840080000338000000000880330018800090000307c7c1f1ff183c30785c1e16d0000307c700003f08143078581402d)) else (if i < 13 then (if i < 12 then 0x3ffff0000000a9495adf00000000003fff8fffe3800002ad68ab5a3800003fff8fffe0000000084802120000003fff800003800002ad68a9483800003fff800000000000084800000000003ffc700003f0a943f787a9403f00003fe3f00003f0a90bf637a9083f00003f9f80000000a84bf9fba8481b00003f807fe01ff1f803f003fc00db00003f80700003f0a803f003a8001b00003f8070000000a801500300000000003f80000003800002a000a80018 else 0x3ffffce703f1b9cbffffef7a7f00003ffff3e0e3f0f95bffffbf5ebf00003ffff01fe3f0abdbffffabff3f00003ffff0001ff1fbdbfffffdedff00003ffff00003f0a94bffffa9483f00003ffff00003f0a94bfadfa8001b00003ffff00003f0a94b5fdf81402d00003ffff00003f0a949deff21083600003ffff00003f0a803fd6ba9483b00003ffff00003f08143afeda9483d00003ffff00003f0210aef7ea9483e00003ffff0000380a94bffffa94838) else (if i < 14 then 0x3000607ffffff15392a724ffffff003000607c1f1ff103820704c1e16d003000607318fff043108624318db60030006070181ff0030006040181240030006070000000010002040000000030006000180000030006040181240030000070001c70030002040081040030000000181c0002000000008100000e00000000000004e400800020000001c00000000000043c001000040000003ffffffffff1fbdbffffffffff00003ffffffffc01fbd95adf56b7c0 else 0x3fc00070000070affd529700a507003fc0000ffffff157fea7b4ffffff003fc000001fe00007fc07b403ff24003fc00000001c7157fc029454a5c7003fc0000000000007fc029400a504003fc0000000000006b4000000a500003fc00000000000056c0294000000003e00000000000003c0028400a1040031c000000000000318021400850400303ffff0181ff0ab4bffffa9c93f0030307c70181ff08343078581c12d00300c63f0181ff02308c636218936)))) else (if i < 22 then (if i < 18 then (if i < 16 then 0x6000c63f3001ff06108c6363108b606000c007ffffff17292e522ffffff06000c007fe01ff17002e002fc00db06000c007318fff06210c422318db606000c0073001ff06000c00230009206000c00700000002000400200000006000c00030000006000c0023000920600000070001c70600040021000820600000003001c004000000010008001c00000000000001c241000040000003ffffff00003f0afffffffa9ed3f003fc07f8000000007fc0ffc01ed24 else (if i < 17 then 0x7c0000000000000780050021400820631cc63f0001ff06318c636318db60631cc0073001ff06318c2163085960631c06070181ff0631846161185a60631c0007318fff06318c636318db60631c00070001c70631842161085860631c00070000000210842160000000631c00000001c004210000010858006300c6073181ff06300c6063181b60601c000000000006018401210048206003ffff3001ff0e94bffffb948bf06003f8073001ff0e803f003b8009b else 0x1800000070001c7180010001400041180000000c001c010000000040004007ffc000000000007ffc529614a58607c1fffff00003f0fd7fffffbd4cbf07c1cf83800000007c3cf87a3c0c9207c1c00070000070fd7d529714048707c1c0000ffffff17ebef532ffffff07c1c00003e0e0007c3cf0323e1e9207c1c00000001c717ebc501254a5c707c1c000000000007c3c501214048207c1c000000000005434000014048007c1c000000000002c2c5012000000)) else (if i < 20 then (if i < 19 then 0x183e000000001c010280000040a140183030607c181ff183030605c1816d180e00000000000180c1008140204118003ffffc001ff1a94bffffe9487f18003f807c001ff1a803f003e8005b1800307c7c001ff181430785c1406d180030007ffffff1d293a521ffffff180030007fe01ff1d003a001fc00db180030007c1f1ff182830501c1e16d180030007c001ff180030001c00049180030007000000080010001000000180030000c00000180030001c00049 else 0x19ce00000ce700019ce73181ce724919ce000000001c71def5108154a5c719ce0000000000019ce5108144204119ce00000000000114a4000044204019ce0000000000008c65108100000019c000000000000198011001440041183e307c70001ff183c30785c1e16d183e30007c001ff183c30285c0a14d183e006070181ff183c1068541a165183e00007c1f1ff183c30785c1e16d183e000070001c7183c1028540a145183e00007000000081410285000000) else (if i < 21 then 0x1fc00c0073001ff1f801d0037400d31fc000007fe01ff1f803f003fc00db1fc0000070001c71f80150035400c31fc0000070000000a80150030000001fc0000000001c01500000005400c01e3fc00070001c71e3d9429750a5c71e003c007f001ff1e003c003f000db19ffc000000000019ffd129544a54519ce3ffff00003f1bdefffffed687f19ce339c000000019ce739c9cc604919ce000070000071bded529744204719ce00000ffffff1def7b5a1ffffff else 0x1fffc00070001c70ef7d52971085861fffc00070001c01fffd529754a5c01fffc00070000000ad6d52970000001fffc0000ffffc0156b4000056b7c01fffc0000fffe000042400000212001fffc00000001c0156b4000054a5c01fffc00000000000042400000000001ffe000070001c71fbc1528754a1c71ff1c00070001c71fb1952175485c71fcfc00000000001fcfd50935424c31fc03f8070001ff1f803f003fc00db1fc030007c001ff1f8035003d400cb))) else (if i < 26 then (if i < 24 then (if i < 23 then 0x1fffc0007ffffff1fffff7b7ffffff1fffc0007fffe380ad6ff7b7ab5a381fffc0007ce71c71ffff7397def7cf1fffc00073e0fc71fffdf2b77ebfd71fffc000701ffc71fffd57b757ffe71fffc00070001ff1fffff7b7fdedff1fffc00070001c71fffd529754a5c71fffc00070001c71feb5500354a5c31fffc00070001c71fd6d52975400c31fffc00070001c71d7f5028554a5c51fffc00070001c71afed529740a1451fffc00070001c7177bc421654a5c6 else 0x200000000318e000000000000000001ffffffffffffff1ffffffffffffff1ffffffff0001ff1fffffffffdedff1ffffffff0000000ad6d5adf0000001fffffff80001f8156b6ad68fdedf81fffffff80000000042408480000001ffff39c70001c71ffff7bdfdce5cf1ffff0007c001ff1ffff5297d4a5cf1fffcf83f0001c71fffdfaff7cadd71fffcc0073001ff1fffdd29774a5d71fffc07ff0001c71fffd5fff55ede71fffc06070181ff1fffd569755a5e7) else (if i < 25 then 0x20003ffff318e3f0a94bffffa9483f20003fff8fffe3800002ad68ab5a3820003fff8318e3800002ad68a9483820000c63f318e3f02108c63621083620000c638ffffff15292a520ffffff20000c638fffe3800002a520ab5a3820000c638318fff042108420318db620000c638318e3800000842021083020000c63800000000000000000000020000c038300e00000008020200810200000638018e00000000420010820200000038000e00e00000868021a00 else 0x20300c63f318fff0030086242189342001fffff000e3fead7fffffab5e3f2001cf838000e00e2c3cf87a2a1e122001c07f8000e00e057c0ffc035e242001c003f000fff000180030000c002001c0038fffffff56bead78ffffff2001c00383e0e00e543ca8783e1e922001c003801fe00e06bc0d7803ff242001c0038000e00e043c0878021e002001c0038000e00000180030000c002001c0038000000e042c08580000002001c0000000e00e04340000021600)) else (if i < 28 then (if i < 27 then 0x203fc0038000e00e07fc0afc02bf042031cc63f318fff06318c636318db62031cc63f318fff003188634218d342031cc63f018fff02318c636218d362031cc63f018e3f02318c636218d362031cc638318e38003188634218d342031c063f318fff043188634318db62031c063f018fff003180634018d242031c0638318fff043188634318db62031c0638018e00003180634018d242031c06380000000010802140000002031c0000018e00002100000008500 else 0x2601cc63f318fff06318c636318db62601cc63f318fff06018c432310cb22601cc63f300fff06118c636310cb62601cc63f300e3f06118c636310cb62601cc638318e3806018c432310cb22601cc03f318fff06218c432318db62601cc03f300fff06018c032300c922601cc038318fff06218c432318db62601cc038300e0006018c032300c922601cc0380000000200840120000002601c0000300e0004010000010048026000c63f318fff06000c4223108b2) else (if i < 29 then 0x2631c063f318fff06318c636318db62631c063f318fff043180634118da42631c063f018fff063184636118da62631c063f018fc7063184636118da62631c0638318fc0043180634118da42631c0607318fff0431006041185a42631c0007318fc70631842161085862631c0000ffffff15292a520ffffff2631c0000ffffc015290000056b7c02631c0000318fff042108420318db62631c0000318fc00421000001085802631c0000000000000000000000000 else 0x2631cc63f0181ff0230846160181242631cc63f0001c70631842161085862631cc63f00003f02108c6362108362631cc63f0000000210842160000002631cc638318ff8042108420318db02631cc638318e0006318c636318db62631cc03f318fff06318c636318db62631cc03f318fff06218c032308d922631cc03f300fff06318c236308d962631cc03f300fc706318c236308d962631cc038318fc006218c032308d922631cc007318fff06210c002308592))))) else (if i < 45 then (if i < 37 then (if i < 33 then (if i < 31 then 0x2631cc63f318fff06108c6363108b22631cc63f318fff043108624318db42631cc63f318fff02308c6362189342631cc63f318fc00631842161085802631cc63f318e3802108c6362108302631cc63f300fff06318c636318db62631cc63f300fff06118c236300c922631cc63f300e0006118c236300c922631cc63f3001ff06108c2163000922631cc63f018fff06318c636318db62631cc63f018fff023184636018d242631cc63f018e00023184636018d24 else (if i < 32 then 0x2631cc63f318fff0eb59d6b7318db72631cc63f318fff07318c636358db62631cc63f318fff06b18d636318db62631cc63f318fff06398c63631adb62631cc63f318fff06358c6b6318db62631cc63f318fff0631ae736b9cdbf2631cc63f318fff06318e636398db62631cc63f318fff06318c73631cdb62631cc63f318fff06318c636318db62631cc63f318fff06318c2163085922631cc63f318fff0631846161185a42631cc63f318fff06210c422318db2 else 0x2631cc63fffffff1739ae736ffffff2631cc63fffffff17398c63677bff62631cc63fffffff0631ae736bbdfbe2631cc63fff8fff1731ae636fd8dff2631cc63ff1ffff1639ac736f1edff2631cc63fce70001318a6316ce72492631cc63f3f8fff07318e6363f9fb62631cc63f3f8fff07318e6363d8db62631cc63f31ffff06398c73633ffb62631cc63f31ffff06398c73631edb62631cc63f318fffe673cce7e339fb62631cc63f318fff17398c63675adf7)) else (if i < 35 then (if i < 34 then 0x2631fffff318fff0eb5bffffb9cdbf2631fffff318fff0eb59deff318db62631fffff318fff0631aef7eb9cdbe2631fffff00003f0a94bffffa9483f2631fffff0000000a9495adf0000002631ffe3f318fff0eb1bf637b98dbf2631fc7ff318fff0e35bc7b7b1cdbf2631f39c0318fc00ca5339c998c5892631cfe3f318fff06b18fe7e398db62631cfe3f318fff06b18f636398db62631cc7ff318fff06358cffe31cdb62631cc7ff318fff06358c7b631cdb6 else 0x3fffc0000318fc0156b4000054a5c03ff1cc63f318fff1fb19d637758df73e3fcc63f318fff1e3d9c6b771adf73e31fc63ff18fff1e31bc637f18dff39ce0c638318e3819ce594a16528713801f003fc00ffff843f0879c21e4927f1cc63f318fff07f3cd636358db627f1cc63f318fff07b18d636358db627c1c0038000e00e7c3c587a161e82263fcc63f318fff067fcc6b631adb6263fcc63f318fff063d8c6b631adb62631fffffffffff1fbdbffffffffff) else (if i < 36 then 0x400000000c1f0000000000000000003ffffffff318fff1fffffffffdedff3ffffffff0000000ad6d5adf0000003fffcc63fffffff1fffff7b7ffffff3fffcc63f318fff1fffdd6b775adf73fffcc63f318fff177bcc63675adf63fffcc63f318fff0ef7dd6b7318db63fffcc63f0001c71fffd529754a5c73fffcc63f0000000ad6d52970000003fffc003f000fc7ffffd5aff56bfc73fffc0007318fc71fffd529754a5c73fffc0000ffffc0156b4000056b7c0 else 0x40003ffffc1f03f0a94bffffa9483f40003fff8fffe3800002ad68ab5a3840003fff8c1f03800002ad68a948384000307c7c1f03f08143078581402d4000307c0ffffff15292a520ffffff4000307c0fffe3800002a520ab5a384000307c0c1f1ff102820500c1e16d4000307c0c1f0380000205008140284000307c00000000000000000000004000301c0c070000000201008040084000007c001f0000000005000140204000001c0007000e00000948025200))) else (if i < 41 then (if i < 39 then (if i < 38 then 0x4030307c7c1f1ff00302070481c12c400e3ffff00703feadefffffab7a3f400e339c0007000e8ce739c98a7209400e007f8007000e05ec0ffc037a24400e001c70071ff000c00180006000400e001c0fffffff56f6ade8ffffff400e001c0ce7000f14e629c8ce7249400e001c001fe00e06f40de803ff24400e001c0007000e04e409c8027200400e001c0007000000c00180006000400e001c0000000e046408c8000000400e00000007000e04a40000023200 else 0x403fc01c0007000e07fc0bdc02f704403e307c7c1f1ff183c30785c1e16d403e307c7c1f1ff003c2078481e12c403e307c701f1ff083c3078581e12d403e307c701f03f083c3078581e12d403e307c0c1f038003c2078481e12c403e007c7c1f1ff103c20784c1e16d403e007c701f1ff003c0078401e124403e007c0c1f1ff103c20784c1e16d403e007c001f000003c0078401e124403e007c0000000001400284000000403e0000001f00000280000000a100) else (if i < 40 then 0x580e307c7c071ff181c30785c1606d580e307c7c0703f181c30785c1606d580e307c0c1f038180c30581c16069580e301c7c1f1ff182c30581c1e16d580e301c7c071ff180c30181c06049580e301c0c1f1ff182c30581c1e16d580e301c0c07000180c30181c06049580e301c0000000080410081000000580e00000c070001008000004020405800307c7c1f1ff180030501c1406947c1f07c0c1f03807c3e55129544aa460e0c1c73071ffe64e4c9ca327292 else 0x583e007c701f1ff183c1078541e165583e007c701f1c7183c1078541e165583e007c0c1f1c0103c0078441e164583e00607c1f1ff10380060441a164583e00007c1f1c7183c1028540a145583e00000ffffff15292a520ffffff583e00000ffffc015290000056b7c0583e00000c1f1ff102820500c1e16d583e00000c1f1c010280000040a140583e00000000000000000000000000580e307c7c1f1ff183c30785c1e16d580e307c7c1f1ff180c30581c16069)) else (if i < 43 then (if i < 42 then 0x583e307c7000000081410285000000583e307c0c1f1f8102820500c1e168583e307c0c1f000183c30785c1e16d583e301c7c1f1ff183c30785c1e16d583e301c7c1f1ff182c30181c0e149583e301c7c071ff183c30385c0e14d583e301c7c071c7183c30385c0e14d583e301c0c1f1c0182c30181c0e149583e30007c1f1ff182830001c0a149583e0f838c1f1c012a88f87a68a952583e007c7c1f1ff183c30785c1e16d583e007c7c1f1ff103c0078441e164 else 0x583e307c7c1f038081430785814028583e307c7c071ff183c30785c1e16d583e307c7c071ff181c30385c06049583e307c7c07000181c30385c06049583e307c7c001ff181430285c00049583e307c73e0e000d151a2a53e1e92583e307c701f1ff183c30785c1e16d583e307c701f1ff083c1078501e124583e307c701f000083c1078501e124583e307c70181ff083410685018124583e307c70001c7183c1028540a145583e307c700003f08143078581402d) else (if i < 44 then 0x583e307c7c1f1ff183cb0795c1e16d583e307c7c1f1ff183c3a7a5e9e97f583e307c7c1f1ff183c32785c9e16d583e307c7c1f1ff183c307a5c1e96d583e307c7c1f1ff183c30785c1e16d583e307c7c1f1ff183c30285c0a149583e307c7c1f1ff183c1068541a164583e307c7c1f1ff182830501c1e169583e307c7c1f1ff181430785c14069583e307c7c1f1ff103820704c1e16c583e307c7c1f1ff08343078581c12c583e307c7c1f1c0183c1028540a140 else 0x583e307c7fff1ff1d3c3a785fde1ff583e307c7f1ffff1c3d387a5f1edff583e307c7cff1ff193c32785cff36d583e307c7cff1ff193c32785cde16d583e307c7c1ffff183d307a5c3ff6d583e307c7c1ffff183d307a5c1ed6d583e307c7c1f1fff87e70fcdc3f36d583e307c7c1f1ff1d3d30785d5e5ef583e307c7c1f1ff1abcb5797c1e16f583e307c7c1f1ff193c30785c5e16d583e307c7c1f1ff18bc31785c1e16d583e307c7c1f1ff183d30785c1e56d)))) else (if i < 52 then (if i < 48 then (if i < 46 then 0x583e3ffffc1f1ff183c3afede9e97d583e3ffff00003f0a94bffffa9483f583e3ffff0000000a9495adf000000583e3ffc7c1f1ff1abc3f787e9e17f583e3c7ffc1f1ff1a3cbc7b7e1e97f583e33fc7c1f1ff18bc33fcdc9e16d583e33fc7c1f1ff18bc33785c9e16d583e307ffc1f1ff183cb0ffdc1e96d583e307ffc1f1ff183cb07b5c1e96d583e307c7ffffff1d3d3a7a5ffffff583e307c7ffffff1d3d30785d7f7ed583e307c7ffffff183c3a7a5ebfb7d else (if i < 47 then 0x5fffc0000c1f1c0156b4000054a5c05ffe307c7c1f1ff1fbc35787d5e1ef5e3ff07c7c1f1ff1e3db4797d1e5ef5e3e3c7c7f1f1ff1e3c3c787f1e1ff59fe307c7c1f1ff19fe71785c5e16d59fe307c7c1f1ff19bc31785c5e16d59ce001c0007000f9ce519c9467241583ff07c7c1f1ff187ff0795c1e56d583ff07c7c1f1ff183db0795c1e56d583e3ffffffffff1fbdbffffffffff583e3ffffc1f1ff1abcbffffe9e97f583e3ffffc1f1ff1abcb5fdfc1e16d else 0x60000000001fe00e000000000212005ffffffffc1f1ff1fffffffffdedff5ffffffff0000000ad6d5adf0000005ffff07c7ffffff1fffff7b7ffffff5ffff07c7c1f1ff1ffff5797d5e5ef5ffff07c7c1f1ff1d7f70785d5e5ed5ffff07c7c1f1ff1afef5797c1e16d5ffff07c70001c71fffd529754a5c75ffff07c70000000ad6d52970000005fffc01c70071c7ffffd5bdf56f7c75fffc0007c1f1c71fffd529754a5c75fffc0000ffffc0156b4000056b7c0)) else (if i < 50 then (if i < 49 then 0x603fc0000000000e04240000000000603e007f801fe00e03c00fec03fb246031c07f801fe00e03180f7c03df24600fc01f8007e00e04fc09f8027e0060003fff8fffe38e0002ad68ab5a3860003fff801fe38e0002ad68ab5a3860003c7f8f1fe38000028520a148386000307f8c1fe38e00020d68835a2860000c7f831fe38e00008d68235a306000007f8fffe38e0002ad68ab5a386000007f801fe00e00000d68035a206000007f8000000e00000848000000 else 0x603fc07f801fe00e07fc0ffc03ff24603fc07f801fe00e07fc0adc02b700603fc07f801fe00e06b40d6803ff20603fc07f801fe00e056c0ffc035a20603fc07f801fe00003d807b401ed24603fc07f801f000e07ec0fdc01e124603fc07f8018e00e077c0efc018d24603fc07f8000000e056c0adc000000603fc07c001fe00e07f4078403f724603fc063801fe00e07bc063403bf24603fc0000ffffc0f56b4000056b7c0603fc000001fe00e06b4000002b700) else (if i < 51 then 0x603ff07f8c1fe38e07fe0ffc83ff2c603fcfff801fe00e2ffcfffe2bff36603fcc7f831fe38e07fc8ffc23ff34603fc07ff01ffffe07fc0ffc03ff24603fc07ff01ffff003d807b401ed24603fc07ff01fe07eaffd5fff03ff27603fc07f8fffffff57feaffcffffff603fc07f8fe01fff556eaadcfc00db603fc07f8cffe00f17fe2ffccfff6d603fc07f83ffe00e57fcaffc3fffb6603fc07f801ffc7f57fc0ffc57ffe7603fc07f801fe3fe07feaffcabff3f else 0x663fc07f831ffc0e47fc0ffc13ffa4663fc000031ffc0e46b4000012b7806631fc7fff1ffff0631ac736b1cdbe6631fc7ff318fff06318c636318db66631cc7ff31ffffe6318cf7e33dfb66631cc7ff31ffff06318c73631cdb66631cc63ff1ffff06318c636318db6603fffffffffffffffffffffffffff603ffffff01fe3feafffffffabff3f603ffffff000000ead6d5adf000000603fff80701fe3feaeb7f003aab71b603ff3ff801fe00e8fff3ffd8bff2d))) else (if i < 56 then (if i < 54 then (if i < 53 then 0x783e307c7f1ffff183c30785c1e16d67ffc07f801fe00e7ffc5ffe17ffa6663ffffff31ffffeefffffffbbffbf663fcc7fffffffff77feeffeffffff663fcc7ff31ffffe67fccffe33ffb6663fcc7ff31ffff063d8c7b631edb6663fcc7ff318fffe677ccefe318db6663fcc7ff318fff06358c6b6318db6663fcc7ff01fe00e27fc4ffe03ff24663fcc7ff000000e256c4ade000000663fcc63f31ffffe67bcc63633bfb6663fcc63f31ffff06398c63631adb6 else 0x783ff07ffc1f1fff87ef0fddc1e16d783ff07ffc1f1ff183cb0795c1e16d783ff07ff01fe00e87fd0ffd03ff24783ff07ff000000e856d0add000000783ff07c7c1fffff87f70785c3f76d783ff07c7c1ffff183d30785c1e56d783fc07f8c1ffc0f07fc0ffc43ff64783fc0000c1ffc0f06b4000042b740783e3c7fff1ffff183c387a5e1e97d783e3c7ffc1f1ff183c30785c1e16d783e307ffc1fffff83c30fedc3fb6d783e307ffc1ffff183c307a5c1e96d) else (if i < 55 then 0x7e3ffc7ff0000000a14942970000007e3ff07c7f1ffff1c3d30785d1e5ed7e3ff07c7c1f1ff183c30785c1e16d7e3fcc63ff1ffff16398c63671adf67e3fcc63f318fff06318c636318db67e3fc0000f1ffc014290000050a5c07e0ffc1f8f07e001e0dbc1b3f06cdb79ffc07f801fe00f9ffd1ffd47ff65783ffffffc1fffffafffffffebff7f783ff07fffffffffd7ffaffdffffff783ff07ffc1fffff87ff0ffdc3ff6d783ff07ffc1ffff183db07b5c1ed6d else 0x7fffc07fffffffffffffffffffffff7fffc07ff01ffc7ffffd5fff57ffe77fffc07ff000000ead6d5adf0000007fffc0000ffffc0f56b4000056b7c07fffc000001ffc0f56b4000056b7c07fc0007ff01ffc7ff8015d6b575ae37e3fffffff1ffff1ebdbfffff9edff7e3ffc7ffffffff1f3dbe7b7ffffff7e3ffc7fff1fffffe7ffcffff3ffff7e3ffc7fff1ffff1e3dbc7b7f1edff7e3ffc7ffc1f1ff1a3cb4797c1e16d7e3ffc7ff318fff0e359c6b7318db6)) else (if i < 58 then (if i < 57 then 0x80003f800fe01ff15002a000fc00db80003f800fe003800002a000a8001880003f800000000000000000000000800033800ce000000002200088000880000f8003e000000000a0002800108000038000e0000e000028480a1200800000000fe00000000000000000007ffffffff01fffffffffffffffffff7ffffffff000000ead6d5adf0000007ffffc7fff1ffff1ffffd7b7f5edff7ffff07ffc1fffffffff5fffd7ffef7fffcc7ff31ffffffffddfff77fff7 else 0x81c0038003e0e00e5c34b8683e1e9281c0038000e0000e1c2438480e120081c0038000e00000180030000c000081c003800000000e0c24184800000081c0000000e0000e14240000061200803fff800fe0038007fea294a8a51c80003fffffe003f0a94bffffa9483f80003fff8fffe3800002ad68ab5a3880003fff8fe003800002ad68a9483880003f807fe003f0a803f003a8001b80003f800ffffff15292a520ffffff80003f800fffe3800002a520ab5a38) else (if i < 59 then 0x87c00f800fe01ff17802f002fc00db87c00f8003e000007800f0023c009287c00f80000000002800500200000087c0000003e000005000000014008086003f807fe01ff06002e002b8009a81f003e070f81ffe1f243e4c0f932481c03ffff0e003febd6fffffaf5a3f81c0339c00e0000e9c6739c98e520981c00f8380e0000e3c2cf87a2e1a1281c0038070e01ff0180030000c000081c003800fffffff5eb6bd68ffffff81c003800ce7000f1ca63948ce7249 else 0x99c033800ce0000198033001cc004999c03380000000008801100100000099c000000ce000011000000044004098003f807fe01ff18003a001e8005987c1c38000e0000e7c3c785a1e168287c03f807fe01ff1f803f003fc00db87c03f807fe01ff07802f002bc009a87c03f8073e01ff0f803f003bc009b87c03f8073e003f0f803f003bc009b87c03f800fe003807802f002bc009a87c00f807fe01ff17802f002fc00db87c00f8073e01ff07800f0023c0092)))))) else (if i < 90 then (if i < 75 then (if i < 67 then (if i < 63 then (if i < 61 then 0x9fc000000fe01ff15002a000fc00db9fc000000fe01c01500000005400c09fc00000000000000000000000000099ce038000e0000f9ce538c94e324199c03f807fe01ff1f803f003fc00db99c03f807fe01ff19803b001ec005999c03f807ce01ff1b803f003ec005b99c03f807ce003f1b803f003ec005b99c03f800fe003819803b001ec005999c033807fe01ff1d803b001fc00db99c033807ce01ff198033001cc004999c033800fe01ff1d803b001fc00db else (if i < 62 then 0x9fc033800fe01c01d8033001dc00c99fc030007fe01ff1d0030001d400c99fc00f807fe01ff1f803f003fc00db9fc00f807fe01ff17800f0027c00d29fc00f8073e01ff1f801f0037c00d39fc00f8073e01c71f801f0037c00d39fc00f800fe01c017800f0027c00d29fc00c007fe01ff17000c0027400d29fc0007f8fe01c0151480ffc5548e49fc000007fe01c71f80150035400c39fc000000ffffff15292a520ffffff9fc000000ffffc015290000056b7c0 else 0x9fc03f8073e00000f801f0033c00929fc03f8073001ff0e801d0033000929fc03f80701fe000aa91552303ff249fc03f8070001c71f80150035400c39fc03f80700003f0a803f003a8001b9fc03f8070000000a80150030000009fc03f800fe01f815002a000fc00d89fc03f800fe00001f803f003fc00db9fc033807fe01ff1f803f003fc00db9fc033807fe01ff1d8033001dc00c99fc033807ce01ff1f8037003dc00cb9fc033807ce01c71f8037003dc00cb)) else (if i < 65 then (if i < 64 then 0x9fc03f807fe01ff1d003a001fc00d99fc03f807fe01ff1a803f003e800599fc03f807fe01ff17002e002fc00da9fc03f807fe01ff0e803f003b8009a9fc03f807fe01c01f80150035400c09fc03f807fe00380a803f003a800189fc03f807ce01ff1f803f003fc00db9fc03f807ce01ff1b8037003cc00499fc03f807ce00001b8037003cc00499fc03f807c001ff1a8035003c000499fc03f8073e01ff1f803f003fc00db9fc03f8073e01ff0f801f0033c0092 else 0x9fc03f807fe01ff1fa93f003fca5df9fc03f807fe01ff1f94bf297fc00df9fc03f807fe01ff1f883f003fc20db9fc03f807fe01ff1f843f083fc00db9fc03f807fe01ff1f813f003fc04db9fc03f807fe01ff1f80bf013fc00db9fc03f807fe01ff1f803f523fd48ff9fc03f807fe01ff1f803f103fc40db9fc03f807fe01ff1f803f023fc08db9fc03f807fe01ff1f803f003fc00db9fc03f807fe01ff1f8035003d400c99fc03f807fe01ff1f801d0037400d2) else (if i < 66 then 0x9fc03f83ffe01ff1f80bf87bfc08db9fc03f83ffe01ff1f80bf033fc08db9fc03f807ffffff1fa93f523ffffff9fc03f807ffffff1fa93f003feb7db9fc03f807ffffff1f803f523ff5afb9fc03f807fff1ff1fa83f503fde1ff9fc03f807ff8fff1fa13f423fd8dff9fc03f807fe71ff1f883f103fe72db9fc03f807fe71ff1f883f103fc60db9fc03f807fe0fff1f813f023fe1edb9fc03f807fe0fff1f813f023fc0cdb9fc03f807fe01ffffc27f84bfe12db else 0x9fc1ff807fe01ff1fc3ff013fc04db9fc1ff807fe01ff1f81bf013fc04db9fc03ffffffffff1fbdbffffffffff9fc03fffffe01ff1f94bfffffd48ff9fc03fffffe01ff1f94bfadffc00db9fc03fffffe01ff1f803fd6bfd48fb9fc03ffff00003f0a94bffffa9483f9fc03ffff0000000a9495adf0000009fc03ffc7fe01ff1f943f787fd40ff9fc03fe3ffe01ff1f90bf637fd08ff9fc03f9c7fe01ff1f843f9cbfc40db9fc03f9c7fe01ff1f843f183fc40db))) else (if i < 71 then (if i < 69 then (if i < 68 then 0x9fffff807fe01ff1fd6ff297fc00db9fffff8070001c71fffd529754a5c79fffff8070000000ad6d52970000009fffc38070e01c7ffffd7adf5eb7c79fffc0007fe01c71fffd529754a5c79fffc0000ffffc0156b4000056b7c09fffc0000fe01c0156b4000054a5c09ffe3f807fe01ff1fbc3f287fca1df9ff1ff807fe01ff1fb1bf217fc85df9ff03fe07ff81ff1fb03f607fd81ff9fce3f807fe01ff1fce7f083fc20db9fce3f807fe01ff1f8c3f083fc20db else 0xa0003fe38ff8e3800002a420a90838a0003f838fe0e38e0002a868aa1a18a0000fe383f8e38e0000ac682b1a30a0000f838fffe38e0002ad68ab5a38a0000f8383e0e00e0000a8682a1a10a0000f838000000e00000848000000a000000003e0e00e000000000212009fffffffffe01ff1fffffffffdedff9ffffffff0000000ad6d5adf0000009fffff807ffffff1fffff7b7ffffff9fffff807fe01ff1fffff297fca5df9fffff807fe01ff1feb7f003fca5db) else (if i < 70 then 0xa7c1c00003e0e00e54340000161680a7c1c0000000000e04240000000000a7c00f8383e0e00e7800f86a3e1a92a631ffe3fff8fff0631ae636b98dbea631ffe3f318fff06318c636318db6a631cfe3f3f8fffe6318ee7e3b9fb6a631cfe3f3f8fff06318e636398db6a631cc63fff8fff06318c636318db6a601cf8383e0e00e6018e87a3a1e92a1c1c38380e0e00e1c3c38780e1e00a0003fff8fffe38e0002ad68ab5a38a0003fff83e0e38e0002ad68ab5a38 else 0xa7c1cf8383e0e3fe7c3efd7abf5ebfa7c1cf8383e0e00e7c3cf87a3e1e92a7c1cf8383e0e00e7c3c585a161680a7c1cf8383e0e00e5434a8683e1e90a7c1cf8383e0e00e2c2cf87a2a1a10a7c1cf8383e0e0007818f0323c0c92a7c1cf8383e0000e7c2cf85a3c0092a7c1cf838300e00e6c3cd87a300c92a7c1cf838000000e2c2c585a000000a7c1cf8003e0e00e7c34f0023e1692a7c1cc0383e0e00e743cc032361e92a7c1c0000ffffc0f56b4000056b7c0)) else (if i < 73 then (if i < 72 then 0xa7c1ff838fe0e38e7c3ef87abe1e9aa7c1f07c73e0e3fed57707859756ada7c1cfff83e0e00e7d7cfffe3f5eb6a7c1cfe383f8e38e7c3cfc7a3f1eb2a7c1cf83f3e0fffe7c3cf87a3e1e92a7c1cf83f3e0fff07818f0323c0c92a7c1cf83f3e0e07efd7dfaff3e1e97a7c1cf838fffffff7ebefd7affffffa7c1cf838fe7e00f7cbef97afe7edba7c1cf838c1f1fff2eae5d5ac1e16da7c1cf8383ffe00e7ebcfd7a3fffb6a7c1cf8383e0fc7f7ebcf87a7ebfd7 else 0xa7f1cfe3f3e0e00e7d3cfa7e3e1e92a7f1cfe3f318fffe6f3cde7e318db6a7f1cfe3f318fff06b18d636318db6a7f1cfe3f000000e2d2c5a5e000000a7f1cf8383f8fc0e7e3cf87a3e9f92a7f1cc63f3f8fffe773cc636379fb6a7f1cc63f3f8fff07318c636358db6a7f1c00003f8fc0e56340000169780a7c1ffffffffffffffffffffffffffa7c1fffff3e0e3fefd7fffffbf5ebfa7c1fffff000000ead6d5adf000000a7c1ff9f83e0e00efc7ff9fbbe5e9b) else (if i < 74 then 0xbfc03fe3fff8fff1f803f423fd08fbbfc03fe3ffe01ff1f803f003fc00dbbfc03f83ffe0fffff803f86bfe1adbbfc03f83ffe0fff1f803f023fc08dbbfc03f807ff8fff1f803f003fc00dbb9f1f3e38cf8e0019b1b3635cd8d6db83e0f83f3e0fc7f83c1aaed6abb55a7ffcf8383e0e00e7ffcfafe3ebf96a7f1fffff3f8fffeff7fffffbfdfbfa7f1cfe3ffffffff7fbeff7effffffa7f1cfe3f3f8fffe7f3cfe7e3f9fb6a7f1cfe3f3f8fff07b18f6363d8db6 else 0xbfc1ffffffe0fffffd7fffffff5effbfc1ff83fffffffffebffd7bffffffbfc1ff83ffe0fffffc3ff87bfe1edbbfc1ff83ffe0fff1f81bf033fc0cdbbfc1ff83ffe01ffffc2ff85bfc00dbbfc1ff83ffe01ff1f80bf013fc00dbbfc1ff83f3e0e00efc3df87b3e1e92bfc1ff83f000000eac2d585b000000bfc1ff807fe0fffffc37f003fe16dbbfc1ff807fe0fff1f813f003fc04dbbfc1cf838fe0fc0f7c3cf87a7e1ed2bfc1c0000fe0fc0f543400005616c0)))) else (if i < 82 then (if i < 78 then (if i < 76 then 0xbff1ffe3fffffff1fb9bf737ffffffbff1ffe3fff8ffffff3ffe7fff9fffbff1ffe3fff8fff1fb1bf637fd8dffbff1ffe3ffe01ff1f90bf217fc00dbbff1ffe3f318fff0eb19d637318db6bff1ffe3f0000000a9095217000000bff1ff807ff8fff1fa13f003fc85dbbff1ff807fe01ff1f803f003fc00dbbff1cc63fff8fff17318c636758df6bff1cc63f318fff06318c636318db6bff1c0000ff8fc01521000005485c0bfcfcf8383e0e00ffcfdf8fb7e3ed3 else (if i < 77 then 0xc00000000ce7000e00000000021200bffffffff3e0ffffffffffffffffffbffffffff000000ead6d5adf000000bfffffe3fff8fff1fffff6b7fdadffbfffff83ffe0fffffffffafffebfdfbfffcfe3f3f8fffffffdfeff7fbff7bfffcf83ffffffffffffffffffffffbfffcf83f3e0fc7ffffdfaff7ebfd7bfffcf83f000000ead6d5adf000000bfffc0000ffffc0f56b4000056b7c0bfffc00003e0fc0f56b4000056b7c0bff1fffffff8fff1fb5bfffffdcdff else 0xd80e339c0ce7000f80c329c9ca7249c7fe0ffc03ff00007bc0f7863de1b6c631f39c7ce71c7e631a6b5e9ad78ec1ce039c00e7000e1ce439c80e7200c0003fff8fffe38e0002ad68ab5a38c0003fff8ce7038e0002ad68ab5a38c0003ffc0fff03800002a500a94038c0003f9c0fe7038e0002a948aa5218c00033fc0cff038e00022d488b5228c000339c0fffe38e0002ad68ab5a38c000339c0ce7000e000229488a5208c000339c0000000e00000848000000)) else (if i < 80 then (if i < 79 then 0xd9ce33800ce7000f9ca73001ce3249d9ce301c0ce7000f94e70181c67249d9ce0c63fce703ff35acc636673a76d9ce00000ffffc0f56b4000056b7c0d9ce00000ce7000f14a40000463240d9ce00000000000e04240000000000d9c0339c0ce7000f98033949ce5249d83e3ffc7fff1ff183c3a785e9e17dd83e3ffc7c1f1ff183c30785c1e16dd83e33fc7cff1fff83c32fcdcbf36dd83e33fc7cff1ff183c32785c9e16dd83e307c7fff1ff183c30785c1e16d else 0xd9ce339c0cffe00f9ef73de9cfff6dd9ce339c0ce71c7fdef739c9def7cfd9ce339c0ce703ff9ce7bde9ef7a7fd9ce339c0ce7000f9ce739c9ce7249d9ce339c0ce7000f9ce518c9463240d9ce339c0ce7000f14a62948ce7248d9ce339c0ce7000e8c6739c98a5208d9ce339c0ce7000198c33181cc6049d9ce339c0ce0000f9c6738c9cc0049d9ce339c0c07000f8ce719c9c06049d9ce339c0318fffece759ce9318db6d9ce339c0000000e8c6518c9000000) else (if i < 81 then 0xd9ce3fffffffffffffffffffffffffd9ce3ffffce703ffbdefffffef7a7fd9ce3ffff000000ead6d5adf000000d9ce3f9f8ce7000fbceff9fbee7a5bd9ce3f9c0fe7038f9ce7b9c9ee7259d9ce33ff8ce7000f9def3ffdcf7a6dd9ce33fc0cff038f9ce73dc9cf7269d9ce339c7ce71fff9ce739c9ce7249d9ce339c7ce71ff198c33181cc6049d9ce339c7ce7007fbdef7bdfce724fd9ce339c0fffffffdef7bde9ffffffd9ce339c0fe7e00fdcf7b9e9fe7edb else 0xd9fe3ffffcff1fffbfefffffeffb7fd9fe33fc7fffffffdff7bfedffffffd9fe33fc7cff1fff9fe73fcdcff36dd9fe33fc7cff1ff19bc33785cde16dd9fe33fc7ce7000f9de73bcdce7249d9fe33fc7c1f1fff8fe71fcdc1e16dd9fe33fc7c1f1ff18bc31785c1e16dd9fe33fc7000000e8d651acd000000d9fe339c0cff1c0f9ee739c9cef349d9fe307c7cff1fff97e70785c7f36dd9fe307c7cff1ff193c30785c5e16dd9fe00000cff1c0f16a4000046b340))) else (if i < 86 then (if i < 84 then (if i < 83 then 0xdfce3f9c7ce7000fbce779cbce7249dfce3f9c7000000eac6558cb000000dfce3f807fe71ffffca7f003fe32dbdfce3f807fe71ff1f883f003fc20dbdfce339c0fe71c0fdce739c9de72c9dfce00000fe71c0f54a400005632c0dfc03ffc7fff1ff1f803f503fd40fbdfc03ffc7fe01ff1f803f003fc00dbdfc03f9c7fe71ffff803f94bfe52dbdfc03f9c7fe71ff1f803f103fc40dbdfc03f807fff1ff1f803f003fc00dbd9fff39c0ce7000f9fff3bddcef74d else 0xdffe3f807fff1ff1fa83f003fca1dbdffe3f807fe01ff1f803f003fc00dbdffe307c7fff1ff1d3c30785d5e1eddffe307c7c1f1ff183c30785c1e16ddffe00000fff1c015280000054a1c0dfcff39c0ce7000ffcff79dbde76cbdfce3fffffe71ffffdefffffff7affdfce3f9c7ffffffffef7fdebffffffdfce3f9c7fe71ffffce7f9cbfe72dbdfce3f9c7fe71ff1f8c3f183fc60dbdfce3f9c7fe01ffffc67f8cbfc00dbdfce3f9c7fe01ff1f843f083fc00db) else (if i < 85 then 0xdffff39c7fffffffffffffffffffffdffff39c7ce71c7fffff7bdfdef7cfdffff39c7000000ead6d5adf000000dfffc0000ffffc0f56b4000056b7c0dfffc0000ce71c0f56b4000056b7c0dffe3fffffff1ff1fbcbfffffde9ffdffe3ffc7ffffff1fbd3f7a7ffffffdffe3ffc7fff1fffffe7ffcffff3ffdffe3ffc7fff1ff1fbc3f787fde1ffdffe3ffc7fe01ff1f943f287fc00dbdffe3ffc7c1f1ff1abc35787c1e16ddffe3ffc70000000a9415287000000 else 0xe000007f8fffe00e00000d68035a20e00000007fffe07ea9495297021207e00000000fffffff5292a520ffffffe00000000ffffc0f5290000056b7c0e00000000fffe38e0002a520ab5a38e00000000fffe00e00000000021200e00000000000000e00000000000000dffffffffce71fffffffffffffffffdffffffff000000ead6d5adf000000dffffffc7fff1ff1fffff797fde5ffdfffff9c7fe71ffffffffbdffef7dfdffff3fc7cff1fffffff7fdfdff7ef)) else (if i < 88 then (if i < 87 then 0xe0003fff801fe00e00000d68035a20e0003fff80001c7f5290084854a5c7e0003fff8000038e0002ad68a94838e0003fff8000000e00000848000000e0003f9f8fe7e00e0002a968aa5a18e0003f800fffe38e0002a000aa1218e00033ff8cffe00e00022d688b5a28e000339c0fffe00e000229488a5208e000307c0fffe38e00020500835228e0000fff83ffe00e0000ad682b5a30e0000f838fffe00e0000a8682a1a10e0000c638fffe38e00008420231a30 else 0xe0003fff8fffe38e00008c68231a30e0003fff8fffe3800002a520a94838e0003fff8fffe00e0002ad68ab5a38e0003fff8fffe00e000229488a5208e0003fff8fffe00e0000a8682a1a10e0003fff8fffe00e00000d68035a20e0003fff8fffe00e00000848021200e0003fff8fe0038e0002a848a80018e0003fff8ce7000e000229488a5208e0003fff8c1f038e00020d48814028e0003fff83e0e00e0000a8682a1a10e0003fff8318e38e00008c68210830) else (if i < 89 then 0xe0003fff8fffe38e8843bde9ab5a39e0003fff8fffe38e5012ad68bf5ebae0003fff8fffe38e280afd7aab5a3ae0003fff8fffe38e0426ad68ab5a38e0003fff8fffe38e0292ad68abff3ce0003fff8fffe38e014aaffcab5a3ce0003fff8fffe38e0002ad68ab5a3ce0003fff8fffe38e0002ad68ab5a3ae0003fff8fffe38e0002ad68ab5a39e0003fff8fffe38e0002ad68ab5a38e0003fff8fffe38e0002a848aa1218e0003fff8fffe38e00020d48835228 else 0xe0003ffff00003fea94bffffa9483fe0003ffff000000ea9495adf000000e0003fff8fffffff5292ad68ffffffe0003fff8fffffff5002ad68ff5afbe0003fff8fffffff0282ad68ebfb7de0003fff8ffffffe4212ad68bbdfbee0003fff8fffff8f5292ad68fffff8e0003fff8fffe3fe0002ad68ab5a3fe0003fff8fffe3fe0002ad68ab5a3ee0003fff8fffe3fe0002ad68ab5a3de0003fff8fffe3fe0002ad68ab5a3be0003fff8fffe38f1082ad68ef7a79))))) else (if i < 105 then (if i < 97 then (if i < 93 then (if i < 91 then 0xe03e3fff8fffe38e03c2afecabfb3ce031ffff8fffe38e031aaf7cabdf3ce0303ffffffffffe0302af6cabdb3ce00e3fff8fffe38e04e6ade8ab7a38e001ffff8fffe38e043ead78ab5e38e0003ffffffffffffbdbffffffffffe0003ffffffffffe0002ad68ab5a38e0003fffffffe3fea94bffffab5a3fe0003fffffffe3fea803fd6bab5a3be0003fffffffe3fe8143afedab5a3de0003fffffffe3fe210aef7eab5a3ee0003fffffffe38ea94bffffab5a38 else (if i < 92 then 0xe1ffc3ff80ffe00e1ffc3ffc0fff24e1c03fff8fffe38e1c26bd68af5a38e03fffffffffe3feafffffffabff3fe03fffff8fffffff57feaffcffffffe03fffff8fffe38e07feaffcabff3ce03fffff8fffe38e06b6ad68abff38e03fffff8fffe38e056eaffcab5a38e03fffff8fffe38e0426ad68ab5a38e03fffff801fe00e07fc0ffc03ff24e03fffff8000000e056c0adc000000e03fc07f8fffe00e07fc0ffc03ff24e03fc0000fffe00e06b4000002b700 else 0xe631ffffffffffff739aef7effffffe631fffffffffffeeb5bffffbbdfbfe631fffffffffffe631aef7ebbdfbee631ffffffffe38e210aef7eab5a38e631fffff318fffe6318ce7e318db6e631fffff000000e21084a5e000000e631ffff8fffff8e4212ad68bbdfb8e631ffff8fffe38e0002ad68ab5a38e631cc63fffffffe6318c636339fb6e631c0000ffffc0e42100000129780e601ffff8fffe38e601aed7abb5ebae6003ffffffffffe6002ed6abb5aba)) else (if i < 95 then (if i < 94 then 0xe7c1ffffffffe3fefd7fffffbf5ebfe7c1ffff8fffffff7ebefd7affffffe7c1ffff8fffe38e7c3efd7abf5ebae7c1ffff8fffe38e5436ad68bf5eb8e7c1ffff8fffe38e2c2efd7aab5a38e7c1ffff8fffe38e0426ad68ab5a38e7c1ffff83e0e00e7c3cf87a3e1e92e7c1ffff8000000e2c2c585a000000e7c1cf838fffe00e7c3cf87a3e1e92e7c1c0000fffe00e54340000161680e7c03fff8fffe38e7802fd6abf5abae63ffffffffffffe67feeffebbffbe else 0xf80e3fff8fffe38f80c3ade9eb7a79f8003fffffffffff8003ad69eb5a79e7fffffff3ffe3feffffffffbfffbfe7ffffff8fffe38e7ffefffebfffbee7ffcffff3fffffe7ffcfffe3fffb6e7ffcffff3fffff07bd8f7b63dedb6e7ffcfff8fffffff7ffefffeffffffe7ffcfff83ffe00e7ffcfffe3fffb6e7ffcfff8000000e2d6c5ade000000e7ffc00003ffe00e56b4000016b780e7f1fffffffffffe7f3eff7ebfdfbee7cfcf9f83e7e00e7cfcf9fa3e7e92) else (if i < 96 then 0xf9c03fff8fffe38f9803bd69ef5a79f83fffffffffffff87ffaffdebff7df83e3fffffffffffd3d3afedfffffff83e3fffffffffffabcbffffebfb7ff83e3fffffffffff83c3afedebfb7df83e3fffffffe38e8143afedab5a38f83e3ffffc1f1fff83c30fcdc1e16df83e3ffff000000e81410acd000000f83e3fff8fffff8f0282ad68ebfb78f83e3fff8fffe38e0002ad68ab5a38f83e307c7fffffff83c30785c3f36df83e00000ffffc0f0280000042b340 else 0xf9fe3fffffffffff9fe7bfedeffb7df9cff39f8ce7e00f9cff39f9ce7e49f9ce3fffffffe3ffbdefffffef7a7ff9ce3fff8fffffffdef7bde9fffffff9ce3fff8fffe38f9ce7bde9ef7a79f9ce3fff8fffe38f14a6ad68ef7a78f9ce3fff8fffe38e8c67bde9ab5a38f9ce3fff8fffe38e0426ad68ab5a38f9ce3fff8ce7000f9ce739c9ce7249f9ce3fff8000000e8c6518c9000000f9ce339c0fffe00f9ce739c9ce7249f9ce00000fffe00f14a40000463240))) else (if i < 101 then (if i < 99 then (if i < 98 then 0xffc03fff8fffe38e0002ad68ab5a38ffc03f807ffffffff803f003fe12dbffc000000ffffc0f500000005612c0fe3fffffffffffffe3dbeffffbfffff9fffffffcffe3ffbfffffffefff7ff9ffffff8fffe38f9fffbffdefff7df9fff3fffcffffff9fff3ffdcfff6df9fff3fffcfffff19bdb37b5cded6df9fff3ff8fffffffdfffbffdfffffff9fff3ff8cffe00f9fff3ffdcfff6df9fff3ff8000000e8d6d1add000000f9ffc0000cffe00f16b4000046b740 else 0xffcfff9f8fe7e00ffcfff9fbfe7edbffcfff9f8000000eac6d58db000000ffcfc0000fe7e00f54b400005636c0ffce3ffffffffffffce7fdebff7afbffc1fffffffffffffc3ffd7bff5efbffc03ffffffffffffa93fd6bffffffffc03ffffffffffff94bffffff5affffc03ffffffffffff803fd6bff5afbffc03fffffffe38ea803fd6bab5a38ffc03fffffe01ffff803f84bfc00dbffc03ffff000000ea801584b000000ffc03fff8fffff8f5002ad68ff5af8) else (if i < 100 then 0xffffc0000318fc0e46340000108580ffffc000001fe00e06b4000002b700ffffc00000001c0f56b4000054a5c0ffffc000000003fe0426a520a9483fffffc0000000000e04240000000000fffe3ffffffffffffbc3ffeffffbfffff1fffffffffffffb1bff7fffdfffffcfffffffe7e3fffdffffffff7effffcfffff8fffe38ffcfffdfbff7efbffcfff9fffe7fffffcfff9fbfe7edbffcfff9fffe7fff1f8dbf1b3fc6cdbffcfff9f8ffffffffefffdfbffffff else 0xffffc0000ffffc0f06a4000042b340ffffc0000ffffc0e46340000129780ffffc0000ffffc015290000054a5c0ffffc0000fffe00f56b4000056b7c0ffffc0000fffe00f14a40000463240ffffc0000fffe00e54340000161680ffffc0000fffe00e06b4000002b700ffffc0000fffe00e04240000021200ffffc0000fe01c0f542400005400c0ffffc0000ce7000f14a40000463240ffffc0000c1f1c0f06a4000040a140ffffc00003e0e00e54340000161680)) else (if i < 103 then (if i < 102 then 0xffffc0000ffffc0fdef5108156b7c1ffffc0000ffffc0f7ebc501256b7c2ffffc0000ffffc0f57fc029456b7c4ffffc0000ffffc0f56b62100def7c9ffffc0000ffffc0f56b4a0207ebfd2ffffc0000ffffc0f56b4084856b7c0ffffc0000ffffc0f56b4052057ffe4ffffc0000ffffc0f56b4000056b7c4ffffc0000ffffc0f56b4000056b7c2ffffc0000ffffc0f56b4000056b7c1ffffc0000ffffc0f56b4000056b7c0ffffc0000ffffc0f542400005612c0 else 0xffffc0007ffffc0ffffd529756b7c0ffffc00070001c7ffffd529754a5c7ffffc0007000000ead6d5297000000ffffc0000fffffff56b6a520ffffffffffc0000fffffff56b6a000feb7dbffffc0000fffffff56b60500d7f7edffffc0000fffffff56b4842077bff6ffffc0000fffff8f56b6a520fffff8ffffc0000ffffc7f56b4000056b7c7ffffc0000ffffc7f56b4000056b7c6ffffc0000ffffc7f56b4000056b7c5ffffc0000ffffc7f56b4000056b7c3) else (if i < 104 then 0xffffc07f8000000e056c0adc000000ffffc07c0ffffc0f57f4078457f7e4ffffc0638ffffc0f57bc063457bfe4ffffc0607fffffff57b4060457b7e4ffffc01c0ffffc0f56f409c856f7c0ffffc0038ffffc0f56bc087856bfc0ffffc0007ffffffffffff7b7ffffffffffc0007fffffff56b4000056b7c0ffffc0007ffffc7ffffd529756b7c7ffffc0007ffffc7ffeb5500356b7c3ffffc0007ffffc7fd7f5028556b7c5ffffc0007ffffc7f77bc421656b7c6 else 0xffffcc638fffff8f56b4842077bff0ffffcc638ffffc0f56b4000056b7c0ffffcc038ffffc0f76bcc03276bfd2ffffcc007fffffff76b4c00276b7d2ffffc3800ffffc0f5eb438485eb7c0ffffc07ffffffc7ffffd5fff57ffe7ffffc07f8fffffff57feaffcffffffffffc07f8ffffc0f57fc0ffc57ffe4ffffc07f8ffffc0f57fc0adc56b7c0ffffc07f8ffffc0f56b40d6857ffe0ffffc07f8ffffc0f56b4084856b7c0ffffc07f801fe00e07fc0ffc03ff24)))) else (if i < 113 then (if i < 109 then (if i < 107 then (if i < 106 then 0xffffcf838ffffc0f56b4a8687ebfd0ffffcf838ffffc0f56b4084856b7c0ffffcf8383e0e00e7c3cf87a3e1e92ffffcf838000000e2c2c585a000000ffffcf800ffffc0f7eb4f0027eb7d2ffffcc7fffffffff77fccffe77fff6ffffcc63fffffffffffdd6b777bff7ffffcc63ffffffff77bee736ffffffffffcc63ffffffff77bcc63677bff6ffffcc63fffffc0f77bc421656b7c0ffffcc63f318fffe673cc636318db6ffffcc63f000000e252c4216000000 else 0xfffff07c7000000e85650285000000fffff07c0fffff8f56b60500d7f7e8fffff07c0ffffc0f56b4000056b7c0fffff01c0ffffc0fd6f70181d6f7c9fffff0007fffffffd6b70001d6b7c9ffffcffff3fffc7ffffdffff7ffff7ffffcfff8ffffc0f7ffcfffe7ffff6ffffcfe3ffffffff7fbcfe7e7fbff6ffffcf83fffffc7ffffdfaff7ebfd7ffffcf838fffffff7ebefd7affffffffffcf838ffffc0f7ebcf87a7ebfd2ffffcf838ffffc0f7ebc585a56b7c0) else (if i < 108 then 0xfffff39c0ffffc0fdef518c956b7c0fffff39c0ffffc0f56b62948def7c8fffff39c0ffffc0f56b4084856b7c0fffff39c0ce7000f9ce739c9ce7249fffff39c0000000e8c6518c9000000fffff3800ffffc0fdeb73001deb7c9fffff07fffffffffd7ff0ffdd7ffedfffff07c7fffffffffff5797d7f7effffff07c7fffffffd7f7a7a5fffffffffff07c7fffffffd7f70785d7f7edfffff07c7ffffc0fd7f5028556b7c0fffff07c7c1f1fff87e70785c1e16d else 0xffffff807ffffc0ffeb5500356b7c0ffffff807fe01ffffc27f003fc00dbffffff807000000eac255003000000ffffff800fffff8f56b6a000feb7d8ffffff800ffffc0f56b4000056b7c0fffffc7ffffffffff7ffc7b7f7fffffffff3fffcfffc7fffff7fffdfffeffffff3ff8ffffc0fdfff3ffddfffedfffff3fc7fffffffdff73fcddff7edfffff39c7ffffc7fffff7bdfdef7cffffff39c0fffffffdef7bde9fffffffffff39c0ffffc0fdef739c9def7c9)) else (if i < 111 then (if i < 110 then 0xffffffff8000000e2c2c585a000000ffffffff8000000e056c0adc000000ffffffff8000000e04240848000000fffffffc7ffffffffff7f787fff7ffffffffe3ffffffffffbff637ffbfffffffff9fffe7fc7ffffffbfffeffdfffffff9f8ffffc0ffefff9fbfeffdbffffff9c7ffffffffef7f9cbfef7dbffffff83fffffffffebff87bfebfdbffffff807ffffffffffff297feb7dfffffff807ffffffffeb7f523ffffffffffff807ffffffffeb7f003feb7db else 0xffffffff8fffff8fdef7bde9fffff9ffffffff8fffff8f7ebefd7afffffaffffffff8fffff8f57feaffcfffffcffffffff8fffff8f56b6ad68fffff8ffffffff8ffffc7f56b4084856b7c7ffffffff8ffffc0f56b4084856b7c0ffffffff8fffe3fe0426ad68ab5a3fffffffff8fffe38e0426ad68ab5a38ffffffff8fffe00fffffffffffffffffffffff8fffe00e04240848021200ffffffff8000000ead6d5adf000000ffffffff8000000e8c6518c9000000) else (if i < 112 then 0xfffffffff000000ead6dfaff280812fffffffff000000ead6d5fff014824fffffffff000000ead6d5adf021200fffffffff000000ead6d5adf000004fffffffff000000ead6d5adf000002fffffffff000000ead6d5adf000001fffffffff000000ead6d5adf000000fffffffff000000eac25584b000000fffffffff000000e85650acd000000fffffffff000000e252c4a5e000000fffffffff0000000a9495297000000ffffffff8fffffff56b6ad68ffffff else 0xfffffffff00003fead6ffadfa8001bfffffffff00003fead6f5fdf81402dfffffffff00003fead6ddeff210836fffffffff000038ead6fffffa94838fffffffff000007ead6d5adf000007fffffffff000007ead6d5adf000006fffffffff000007ead6d5adf000005fffffffff000007ead6d5adf000003fffffffff000000fbded5adf442041fffffffff000000efd7d5adf140482fffffffff000000eaffd5adf00a504fffffffff000000ead6f7bdf884009))) else (if i < 117 then (if i < 115 then (if i < 114 then 0xfffffffff018e00eaf7d5eff018d24fffffffff0181ffeaf6d5edf018124fffffffff007000eaded5bdf027200fffffffff000e00ead7d5aff021e00fffffffff0001ffffffffffffdedfffffffffff0001ffead6d5adf000000fffffffff0001c7ffffd5adf54a5c7fffffffff0001c7ffd6d5adf5400c3fffffffff0001c7fafed5adf40a145fffffffff0001c7eef7d5adf108586fffffffff0001c0ffffd5adf54a5c0fffffffff00003fead6fffffa9483f else 0xfffffffff318e38ead6ddeff210830fffffffff318e00ead6d5adf000000fffffffff300e00eed7ddaff300c92fffffffff3001ffeed6ddadf300092fffffffff0e0000ebd6d7adf0e1200fffffffff01ffc7ffffd5fff57ffe7fffffffff01fe3feafffffffabff3ffffffffff01fe00eaffd5fff03ff24fffffffff01fe00eaffd5adf02b700fffffffff01fe00ead6d5fff035a20fffffffff01fe00ead6d5adf021200fffffffff01f000eafed5fdf01e124) else (if i < 116 then 0xfffffffff3e0fc7ffffdfaff7ebfd7fffffffff3e0e3fefd7fffffbf5ebffffffffff3e0e00efd7dfaff3e1e92fffffffff3e0e00efd7d5adf161680fffffffff3e0e00ead6dfaff2a1a10fffffffff3e0e00ead6d5adf021200fffffffff3e0000efd6dfadf3c0092fffffffff31ffffeeffddfff33ffb6fffffffff318fffffffddeff75adf7fffffffff318fffeef7fffffb9cdbffffffffff318fffeef7ddeff318db6fffffffff318fc0eef7d5adf108580 else 0xfffffffffce0000fbd6f7adfcc0049fffffffffc1fffffafff5fffc3ff6dfffffffffc1f1fffffff5fdfd5e5effffffffffc1f1fffafefffffe9e97ffffffffffc1f1fffafef5fdfc1e16dfffffffffc1f1c0fafed5adf40a140fffffffffc1f038ead6f5fdf814028fffffffffc1f000ead6d5adf000000fffffffffc07000fadef5bdfc06049fffffffffc001fffad6f5adfc00049fffffffff3ffe00efffdffff3fffb6fffffffff3f8fffeff7dfeff3f9fb6)) else (if i < 119 then (if i < 118 then 0xffffffffffe01c0ffd6d5adf5400c0ffffffffffe0038ead6ffadfa80018ffffffffffe0000ead6d5adf000000ffffffffff1fffffefffdffff1edfffffffffffcffe00fbfff7fffcfff6dfffffffffcff1fffbfef7fdfcff36dfffffffffce71c7fffff7bdfdef7cffffffffffce703ffbdefffffef7a7ffffffffffce7000fbdef7bdfce7249fffffffffce7000fbded5adf463240fffffffffce7000ead6f7bdf8a5208fffffffffce7000ead6d5adf021200 else 0xffffffffffffe38eafffffffabff3cffffffffffffe38ead6fffffab5a38ffffffffffffe07ead6d5adf021207ffffffffffffe00ead6d5adf021200ffffffffffff1fffffefffdffde1fffffffffffff8ffffff7ffefffd8dffffffffffffe7e00ffdfffbfffe7edbffffffffffe71ffffdeffbdffe72dbffffffffffe0fffffd7ffafffe1edbffffffffffe01ffffffffadffca5dfffffffffffe01ffffd6ffffffd48ffffffffffffe01ffffd6ffadffc00db) else (if i < 120 then 0xffffffffffffffff77beef7efffffefffffffffffffffeef7fffffbbdfbefffffffffffffff1fbdbf7b7fdedffffffffffffffff8ffffffffffffff8fffffffffffffc7ffffd5adf56b7c7fffffffffffffc0fffff7bdfdef7c9fffffffffffffc0ffffdfaff7ebfd2fffffffffffffc0ffffd5fff57ffe4fffffffffffffc0ffffd5adf56b7c0ffffffffffffe3fead6fffffab5a3fffffffffffffe38fbdefffffef7a79ffffffffffffe38efd7fffffbf5eba else 0xfffffffffffffffffffffadffeb7dbffffffffffffffffffff5fdfd7f7edfffffffffffffffffffddeff77bff6fffffffffffffffffeb7fd6bfffffbfffffffffffffffffd6fffffff5afbffffffffffffffffd7f7afedfffffdffffffffffffffffafefffffebfb7d)))))))
private def wireData (i : Nat) : Nat := unpack wireDataPacked 120 12 i
private def readSig (i : Nat) : Sig :=
  let a := wireData i
  (BitVec.ofNat 60 (a >>> 60), BitVec.ofNat 60 a)

private def sigHash (s : Sig) : Nat :=
  let h := (s.1.toNat * 0x517cc1b727220a95) ^^^ (s.2.toNat * 0x9e3779b97f4a7c15)
  let g := (h ^^^ (h >>> 57)) * 0xbf58476d1ce4e5b9
  (g ^^^ (g >>> 49)) &&& 0xffffffffffffffff

private def stateHash (s : SearchState) : Nat :=
  s.2.foldl (fun acc x => acc + sigHash x) (s.1 * 0x94d049bb133111eb)

private def decodeWires (code : Nat) : Nat → List Sig
  | 0 => []
  | n+1 => readSig (code &&& 2047) :: decodeWires (code >>> 11) n

private def st3Packed (_i : Nat) : Nat := 0x52a60482cbba0
private def st3 (i : Nat) : Nat := unpack st3Packed 51 20 i
private def adj3Packed (_i : Nat) : Nat := 0x0
private def adj3 (i : Nat) : Nat := unpack adj3Packed 1 80 i
private def loc3Packed (_i : Nat) : Nat := 0x0
private def loc3 (i : Nat) : Nat := unpack loc3Packed 1 80 i
private def st4Packed (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0xa54c092ba0b2eea2953024165dc2528a4ac0905977080a29ccbd844fcc99a8a54c090597723aa2c83024165dc8da8804c0905977234a2953024165dc89a8a5cc0905977224a2953024165dc8728a54c090597721aa2083024165dc81a8832c0905977202a2953024165dc2a28a54c09059770a6a2ced3997b0882928a54c09059770a2a2953024165dc2828a54c090597709ea29ccbd8dd0886d28 else 0xb214958120b2eea29552560482cbba8a552f58120b2eea2974b460482cbba8a552d18120b2eea292cb460482cbba8a552ad8120b2eea29542260482cbba8a590658120b2eea29541960482cbba8a4b0658120b2eea25a41960482cbba89590658120b2eea255c1960482cbba89690498120b2eea29541060482cbba89690418120b2eea292c0660482cbba8a550098120b2eea292c0260482cbba8) else (if i < 3 then 0xb214d18120b2eea2c8d3060482cbba8b214c18120b2eea2c952f60482cbba8b2d4b98120b2eea2c952e60482cbba8b214b98120b2eea2cbd2d60482cbba8b374b18120b2eea2cbd2c60482cbba8b214b18120b2eea29752c60482cbba8b2f4a98120b2eea2c952a60482cbba8b214a98120b2eea29cd2a60482cbba8a614a98120b2eea29752a60482cbba8a594a98120b2eea00052a60482cbba0 else (if i < 4 then 0x14a92ba0b2ee84003024165dc29a1a732f652c22148a2953024165dc07a8a732f6112ba52ca2953024165dc0aa8a54c0905977028a2953024165dc4ea8a58c0905977138a2953024165dc4c28a54c090597712ea255b024165dc46a8968c0905977116a29ccbd844c092fa8a732f61135a416a29ccbd844e34e1a8a732f648422176a29ccbd844f0cbba8a54ef18120b2eea29535260482cbba8 else 0x52a778c0905a10014a9a93022ee840052a60482cbba1)))
private def st4 (i : Nat) : Nat := unpack st4Packed 62 20 i
private def adj4Packed (_i : Nat) : Nat := 0x130c0600000281200210018d08d082f1a405
private def adj4 (i : Nat) : Nat := unpack adj4Packed 5 80 i
private def loc4Packed (i : Nat) : Nat := (if i < 1 then 0xb1a000000300572e2304e0864a2ed8510002c0335e4df0074000450104d008f3c04d7e028d070898c0005401600224800108f876aa0180a439026006000000c82940045200 else 0x484ce0000e00008c0000004c808c3dca9360000d0085ead3c0000078124006e9572a010c0000131d9d)
private def loc4 (i : Nat) : Nat := unpack loc4Packed 7 80 i
private def st5Packed (i : Nat) : Nat := (if i < 15 then (if i < 7 then (if i < 3 then (if i < 1 then 0xb250418120b2ee4118590844c0905977204c29cc1960482cbb9026165e113024165dc80b0a4b0098120b2ee151853997b089812960a4c29ccbd844e3505852614e65ec227e65dc2930b2f4b18120b2ee1458592a5cc09059770a0c2c853060482cbb84f61496013024165dc27b0a732f6113024ec369853997b089b620b1b4c29ccbd844f50bb8da614e65ec227705dc6d30a732f6113a62ee369859da732f6111771b4c29ccbd844fccbb8da614e65ec227cc5dc6d30 else (if i < 2 then 0xa732f5d2b02416491853997b1658120b248c2c853060482cbb91d61496013024165dc8eb097b0898120b2ee4718530804c0905977238c29cc0260482cbb91b6164a973024165dc89b09690418120b2ee44d84bd820c0905977224c255c1960482cbb90e61642983024165dc86b0b254b98120b2ee4358597a58c090597721ac255c1960482cbb90d612d2083024165dc86b0a4b0098120b2ee435852e844c090597720ac25ec1960482cbb905614e6113024165dc8230 else 0xb2f4b18120b2ee12984ab832c0905977094c25a41060482cbb84a61496013024165dc2530a734b18120b2ee1098525844c0905977084c29cd2e60482cbb841614965eb024165dc20b0a734c18120b2ee101853997b0898120b282c29ccbd844c0905942614e65ec2260482ca030a732f6113024164f5853997b089f9b02278c29ccbd844c094b13c614e65ec22604a209e30a732f6113024164f1853997b089811ca278c29ccbd844c08e613a614e65eb024165dc9530)) else (if i < 5 then (if i < 4 then 0xa732f611302416585853997b0898120b2c0c29ccbd844c090595f614e65ec2260482cadb0a732f611302416569853997b0898120b2b2c29cc22762c0905951614e677c2260482ca8b0a732f61130241653d853997b0898120b29cc29ccbd844c090594d614e65ec2260482ca530a732f61138d416525853997b089c020b292c29ccbd844c0905949614e65ec2258482ca4b0a732f6113f3416525853997b0896220b28ec2c853060482cbb84a6164a973024165dc2530 else 0xa732f6113023a05dd853997b089811cd2eec29ccbd844c08e6177614e65eb024166e8bbb0a732f5b8b023685dd853997b1ed811b42eec25ec2260482cd6977614e611302416690bbb0a732f6113f333c5dd853997b0898120b2ecc29ccbd844c0905975614e65ec2260482cba30a732f6113024165cd853997b0898120b2e4c29ccbd844c090596e614e65ec2260482cb6b0a732f6113024165a5853997b0898120b2d4c25ec2276ac0905964615965ec2260482cb230) else (if i < 6 then 0xa732f6113023e45dd8539a0d089811ee2eec29ccbd844c08f6177614e65ec226047b4bbb0a732f6113023d65dd8539844d79811e32eec29cd06844c08f1977614e65ec22604784bbb0a732f6113023c05dd853997b089811df2eec29ccbd844c08ee177614e65ec2271a76cbbb0a732f6113023b65dd853997b089679db2eec29ccbd844fcced977614e65ec227cc76cbbb0a732f6112d13b25dd853997b1ed811d52eec29ccbd844c08e9177614e65ec22604744bbb0 else 0xa732f6113ee4165dd853997b089f320b2eec29ccbd844f9105977614e65ec227c082cbbb0a732f6113dc4165dd853997b089ed20b2eec29ccbd844f6505977614e65ec22604828bbb0a732f6113024125dd853997b089812082eec29ccbd844c0903977614e65ec22604808bbb0a732f6113024025dd857797b089811fe2eec29ccbd844c08fe177614e65ec226047f4bbb097b089ab3023ee5dd857797b089811f72eec29ccbd844c08fa177614e65ec226047ccbbb0))) else (if i < 11 then (if i < 9 then (if i < 8 then 0xa732f6112c84165dd853997b08962a0b2eec29ccbd844b1105977614e65ec9c56482cbbb0a732f5812b04165dd853997b2715520b2eec25ec22604a8d05977614e61130253882cbbb0a732f55529a4165dd8539844b6932a0b2eec25ec225dc9710597761642983024ae82cbbb0b254b9812574165dd8597a58c092ba0b2eec255c1960495d05977612d2083024ae82cbbb0a4b009812574165dd853997ac0923a0b2eec25ec226048f505977614e61130246882cbbb0 else 0xa732f6112f84165dd853997b0897a20b2eec29ccbd844bd505977616225ec225e282cbbb0b112f6112ee4165dd853997b08975a0b2eec29ccbd844ba905977614e65ec225d282cbbb0a732f6112e54165dd853997b0897220b2eec29ccbd844b8d05977614e68e4225be82cbbb0a73472112da4165dd853997b0896ba0b2eec29ccbd844b5905977614e65ec225aa82cbbb0a732f6112d24165dd853997b08968a0b2eec29ccbd844b2505977614e65ec2259482cbbb0) else (if i < 10 then 0xa734d2013024165dd8590a610098120b2eec2a3d30804c0905977614e69840260482cbbb0a734ba013024165dd8539a590098120b2eec29cd25804c0905977614c292c0260482cbbb0001496013024165dd452597b0098120b2eec292c22804c0905977612ae0840260482cbbb097b089ffb024165dd8539844fe18120b2eec29ccbd844c0505977614e65ec2260082cbbb0a732f6112ff4165dd853997b0897f20b2eec29ccbd844bf505977614e65ec225f282cbbb0 else 0xa992f60cb024165dd853997b0658120b2eec2cbcab832c0905977614e655c1960482cbbb097b2ae0cb024165dd80009570658120b2eea255c22832c09059776164a5ec1260482cbbb0b254ba083024165dd85929970418120b2eec2cb4bd820c09059776164a5ec1060482cbbb0b212f6083024165dd852c97b0418120b2eec2c94b4820c0905977614e65a41060482cbbb097b2d2083024165dd80009690418120b2eea25a422820c0905977614e69840660482cbbb0)) else (if i < 13 then (if i < 12 then 0xb212d2113024165dd85519690898120b2eec29ccb4844c09059776165e5642260482cbbb0b372ae113024165dd85979570898120b2eec2c84ab844c0905977614ba55c2260482cbbb0a732f610b024165dd853997b0818120b2eec29ccbd83ec0905977614e65ec1d60482cbbb0a732f60e3024165dd853997b06d8120b2eec29ccbd834c0905977614e69841960482cbbb0a734ba0cb024165dd85399a10658120b2eec2c94bd832c0905977616425ec1960482cbbb0 else 0xa792f6113024165dd853b97b0898120b2eec29d4bd844c0905977614e65ec2260482cbbb0a712f6113024165dd853797b0898120b2eec29b4bd844c0905977614a65ec2260482cbbb0a512f6113024165dd852797b0898120b2eec2934bd844c0905977614965ec2260482cbbb0a732f2113024165dd85399770898120b2eec29ccba844c0905977614e65c42260482cbbb0a732de113024165dd853996d0898120b2eec29ccb5844c09059776165e5a42260482cbbb0) else (if i < 14 then 0xa73322113024165dd85399730898120b2eec29ccc2844c0905977614e66042260482cbbb0a732fe113024165dd853997d0898120b2eec2c84bd844c0905977616165ec2260482cbbb0af92f6113024165dd857497b0898120b2eec2b54bd844c09059776158a5ec2260482cbbb0ab32f6113024165dd855297b0898120b2eec2a3cbd844c09059776151a5ec2260482cbbb0a8b2f6113024165dd854497b0898120b2eec29acbd844c0905977614f65ec2260482cbbb0 else 0xa732f611b024165dd8590a610898120b2eec2c952e844c0905977615329742260482cbbb0a734ba113024165dd8597a590898120b2eec2cbd25844c0905977614ba92c2260482cbbb0a7345e113024165dd8539a1b0898120b2eec29cd01844c0905977614e67b42260482cbbb0a733aa113024165dd85399c30898120b2eec29ccd8844c0905977614966bc2260482cbbb0b21342113024165dd85399970898120b2eec29ccca844c0905977614e664c2260482cbbb0)))) else (if i < 22 then (if i < 18 then (if i < 16 then 0xa732f64bb024165dd853997b2118120b2eec29ccbd8ecc0905977614e65ec6260482cbbb0a732f62a3024165dd853997b1218120b2eec29ccbd87ac0905977614e69743c60482cbbb0a4b2f61e3024165dd859097b0d58120b2eec29ccb486ac0905977614e65ec3060482cbbb0b2f2ae183024165dd853997b0bd8120b2eec29ccbd85cc0905977614e65ec2d60482cbbb0a732f60f3024165dd853997b0a18120b2eec29ccbd84ac0905977614e65ec2460482cbbb0 else (if i < 17 then 0x97b08999b024165dd8539844ca98120b2eec2cbd92a60c090597760002c853060482cbba8b214e6983024165dd8000b254b98120b2eea2c9539a5cc090597760002cbd2c60482cbba8b2f4e6963024165dd8539a5935d8120b2eec2c853097ac09059776164a974bd60482cbbb0b2f4b25eb024165dd8551a592f58120b2eec29cd2c97ac09059776164a92cbd60482cbbb0a594965eb024165dd8539a612d18120b2eec29cd2c968c09059776165e964ab60482cbbb0 else 0xa732f6113074165dd853997b0898320b2eec29ccbd844c1105977614e65ec2260682cbbb0b214c1de3024165dd8592a5cef18120b2eec2cbd2c778c0905977612ae0cbbc60482cbbb0969041de3024165dd8525804ef18120b2eec29ccbd746c0905977612f61139960482cbbb0a73089c93024165dd8590a60d498120b2eec2c952e6a4c09059776165e9635260482cbbb0957065a93024165dd84b4820d498120b2eec292c026a4c0905977614e65eb3d60482cbbb0)) else (if i < 20 then (if i < 19 then 0xa732f6113024205dd853997b0898120f2eec29ccbd844c0906977614e65ec22604830bbb0a732f6113884165dd853997b089c020b2eec29ccbd844df905977614e65ec226f482cbbb0a732f6113764165dd853997b089ba20b2eec29ccbd844dcd05977614e65ec2264882cbbb0a732f6113224165dd853997b0898c20b2eec29ccbd844c5905977614e65ec2261e82cbbb0a732f61130d4165dd853997b0897e20b2eec29ccbd844c2505977614e65ec2261082cbbb0 else 0xa732f6113d45a25dd853997b089f9ad12eec29ccbd844b454b177614e65ec22604a44bbb0a732f6113025105dd853997b089812862eec29ccbd844c0941177614e65ec226049f8bbb0a732f6113024f85dd853997b0898127b2eec29ccbd844c0917177614e65ec226048acbbb0a732f6113024425dd853997b0898121f2eec29ccbd844c090c177614e65ec22604858bbb0a732f61130240c5dd853997b089812052eec29ccbd844c0909177614e65ec22604844bbb0) else (if i < 21 then 0xacb2f611302416619853997b0898120b308c29ccbd844c0905982614e65ec2260482cb8b0a732f6113024165f9853997b0898120b2fac29ccbd844c090597c614e65ec2260482cbdb0a732f6113024165e5853997b0898120b2f0c29ccbd844f9dea177614e65ec227ccf54bbb0a732f6113f37885dd853997b089ea3022eec29ccbd844f4581177614e65ec2279ac08bbb0a732f6113ab6045dd853997b089d4b022eec29ccbd844ea181177614e65ec227d8c08bbb0 else 0xa732f6113024d482d853997b08981269416c29ccbd844e35059d4614e65ec2271ac08e630a732f61130252c731853997b08981276398c29ccbd844c09440bb614e65ec2271a82c5db0a732f6113804162ed853997b089b920b176c29ccbd844db1058bb614e65ec2269c82c5db0b3b4e65ec224162ed853997b089ea177176c29ccbd8b2c090599f614e65ec2260482cce30a732f61130241666585399df0898120b320c29ccbd844c090598e614e65ec2260482cc630))) else (if i < 26 then (if i < 24 then (if i < 23 then 0xb252f58120b2ee22d853997b089812964c0c29ccbd844e05b620b614e65ec22700db505b0a732f61138d6b682d853997b089c3302416c29ccbd844db18120b614e65ec226d2c0905b0a732f61136560482d853997b089a1b02416c29ccbd844d058120b614e65ec22680c0905b0a732f61138d58882d853997b089b62c4416c29ccbd844b114b20b614e65ec22604a3d05b0a732f6113024ec82d853997b08981274416c29ccbd844c093820b614e65ec226049b105b0 else 0xa732f6113025129d9853997b089812884eec2c952e60482cbb814612d2083024165dc0a30b2f4b18120b2ee27584ab832c090597713ac255c2260482cbb89c612d2083024165dc4c30b214c18120b2ee25d8592a5cc090597712ec2cbd2c60482cbb897612ae0cb024165dc4bb09690418120b2ee25d8525804c090597712ec2964bd60482cbb88f612d2113024165dc47b0a732f58120b2ee2398597956c090597711cc2c84bd60482cbb88c614e65a3024165dc4630) else (if i < 25 then 0x12d18120b2ee44d480097ac0905977224a4004ab60482cbb90e52002013024165dc2a290016769ccbd8441494800b2ec09059770a2a40059260482cbb85052002c83024165dc27a9b3b4e65ec22604291853997b08981296148c29ccbd844c09468a4614e65ec22604a205230a732f6113024ec291853997b08981253148c29ccbd844e01058a4614e65ec227cc5dc5230b2f4b18120b2ee03d84ab832c090597701ec29ccbd844c095f29661642983024165dc0ab0 else 0x14aa013024165dd4800a4b0098120b2eea4004bd844bc505977520029cc225be82cbba90014e65eab24165dd4800a732f54d20b2eea40053984499505977520025ec224b882cbba9001642982574165dd4800b254b92ba0b2eea400597a5895d059775200255c194ae82cbba90012d2082574165dd4800a4b0092ba0b2eea4004bd844c08ff177520029cc226047b8bba90014e65eb023aa5dd4800a732f61119e2eea40052560482cbb91d520029cb024165dc8da9)) else (if i < 28 then (if i < 27 then 0x14b2953024165dd48000014a98120b2ee8400590a4ac0905977520029552560482cbba90014aa5eb024165dd4800a5d2d18120b2eea40052a968c09059775200292cb460482cbba90014aa55b024165dd4800a550898120b2eea4004ac844c0905977520029641960482cbba90014aa0cb024165dd4800a4b0658120b2eea4004b4832c09059775200255c1960482cbba90012f6093024165dd4800a550418120b2eea4004b4820c0905977520029cc0660482cbba9 else 0x14e61135e6045dd480097b089ab3022eea400590a60d498117752002c952e6a4c08bba900165e963526045dd4800957065a93022eea4004b4820d49811775200292c026a4c08bba9001642983024165dd4800b254b98120b2eea400590a5cc090597752002cbd2c60482cbba9001642963024165dd4800a5d4b18120b2eea400597a54c090597752002c952a60482cbba9001642953024165dd4800a734a98120b2eea400530a54c0905977520029752a60482cbba9) else (if i < 29 then 0x14b98120b2ee0514800832c090597713aa40042260482cbb89c52002083024165dc4c290014e65ec226e482d4800b214c1de302416a400592a5cef18120b52002cbd2c778c0905a90012ae0cbbc60482d4800969041de302416a400525804ef18120b520025ec2276ac0905a90014e6113b160482d4800a732f5d2b02416a40053997b089059d4520029ccbd60482ccfa90014e611302416641480097b0898120b30ca40053997b089d3177520029ccbd6e2c08bba9 else 0x52a60482cbba20014b18120b2ee03d4800a732f61130257ca40053997b0898128d52002983024165dc0aa9)))))
private def st5 (i : Nat) : Nat := unpack st5Packed 73 20 i
private def adj5Packed (i : Nat) : Nat := (if i < 1 then 0xc031848530803080070800100c2348c0160403180810146201805020040806000422090013bc001804000020110e00c060 else (if i < 2 then 0x8182180a449c038a0820942c20420300a41000001c841a44639400215ad3162038087000600ac212a5a21a1400002208025 else 0x608443095011002108003288401184100c264804000000))
private def adj5 (i : Nat) : Nat := unpack adj5Packed 5 80 i
private def loc5Packed (i : Nat) : Nat := (if i < 6 then (if i < 3 then (if i < 1 then 0x218001083340055590001c700000248f4041cd001860b400174006b4d3002398e1af001b000103000ff3d5f0000007ac00001f7048ef8b40025d114dc007196b68400354f00012a000000000000000745ef000791a6220013431c0033a3a001968f60e else (if i < 2 then 0x66893000af001a20000500000914000007f6220d00248408873c50d105422ac00364008480036e2900000001227a1fe825a90002514e253417400000000000020f6302828c00000001bc005880037d3c0000027172000002e863002214e4c5000be6e800 else 0x5ec005210f20591000d7001c100099278161500076a027b5e164c00002360006c58c004d8840004767d0e03578328985d58e00031771e955c000184359143269c2001b4390002080000116349d3490355fc0090800000004cc0030c003622a4ed5b3806b)) else (if i < 4 then 0x8c82109c1d0bc77804006791f511d4000008f800000dc43000002432c0005580053d008b1010014c0a800001b100000280670000044d19000b845154000ad764fa00000875a679c000005a571ab501f800219000007991c579c4000330000091d4a00204 else (if i < 5 then 0x298bf000111f05b828e31580000000398001c44e7f40004cb4099534bc00000005b16842dca0213a00000179e2740005a4700f1f33855000078919f6780ec0015a8a12c6809d001d70b000474503740f61d7d001aa195980017001cda0009f0018a000bd else 0xde2a1bd000007391e636248b9188c400000000c85700117000f33a5c8064002300080d2b5bc00000005cc96000000004f101ac4b80000000001921f5b9000a44193865449000000020b85c001f800000687a9261e8000013d350b1469100898f051a7))) else (if i < 9 then (if i < 7 then 0x3940032167000187d4000001b7c400595cf81c9b5652d4fc000006a001d6000b6000aa60c0059800486355b4008982e5e6140000066cc02554d0000053a16001f45740000000000003de13761db1ca11145510021f3c9dd00000285616d9f2010cb else (if i < 8 then 0x240c40018189c001cd7e0023f7b1940000000000001ff11000715858d14900000238e84d60070c00000766f000795fb0000000000000000f92851c0058066624005c60c0000049c6d0015f235a58ec00001a82ece2115fa164003aa2b3e57a548ed00009 else 0x1cc0000022cc93f838748894483f18402304f63b8000000a154005dc1f86c0042400308621319d171460010a000002dc00000000003d3193e00132818006f999000008f0004141c2b83b00000002202444b791f9000002c80000000609c00e41500000)) else (if i < 10 then 0x2b03a0000016000181a40007b41d301b80029c4d002339121c004000018b6fc008c000001b500029031ae78dde294860008f17ccc1490445400000f8000bc0000020cb90021a000420022333cd600064000fb7f1764a56a0d14b68d1b000fc34446201cb else (if i < 11 then 0x2140e0000b6e075821d512837220006dc746c9bb61030001255623777c1a0000012000000b32a5ee2501700197854008bc245b9319019c48d410ac00000000000000023000035f0eb87945001c928980078e70024108000815200008a2d5b3840003f436 else 0x0))))
private def loc5 (i : Nat) : Nat := unpack loc5Packed 10 80 i
private def st6Packed (i : Nat) : Nat := (if i < 48 then (if i < 24 then (if i < 12 then (if i < 6 then (if i < 3 then (if i < 1 then 0xa732f6113024165dc38b8a732f6113024165dc3838a732f6113024165dc37b8a732f6113024165dc3738a732f6113024165dc35b8a732f6113024165dc36b8a7341a113023c65dc36b8a732f6113024165dc3638a732f6113024165dc3538a732f6113024165dc0cb8a732f6113024165dc0438a732f6113024165dc0238a732f6113024165dc00b8a732f6113024165dc03b8a732f6113024165dc01b8a732f6113024165dc0138a732f6113024165dc0338a732f6113024165dc0038a732f6113024165dc02b8a732f6113024165dc04b8 else (if i < 2 then 0xa732f6113f37785dc6d38a732f6113f36a45dc6d38a732f6113f36045dc6d38a732f61130252c5dc6d38a732f6113f34ae5dc6d38a732f61138d4165dc6d38a732f6113024165dc6d38a732f6112cf4165dc6d38a732f6112c24165dc6d38a732f6113f34165dc6d38a732f6113023b25dc6d38a732f6113023945dc6d380014e65ec227e65dc6d30a732f6364227e65dc6d38a732f6113f32ee4bc6d38a732f6113f32ee4346d38a732f6113024165dc6cb8a732f6113024165dc6c38a732f6113024165dc6bb8a732f6113024165dc6b38 else 0xa732f6113024165dc56b8a732f6113024165dc3938a732f6113024165dc74b8a732f6113024165dc7438a732f6113024165dc73b8a732f6113024165dc7338a732f6113024765dc72b8a732f6113024165dc72b8a732f6113023685dc72b8a732f6113024165dc7238a732f6113024165dc71b8a732f6113024165dc5638a732f6113024165dc7138a732f6113024165dc70b8a732f6113024165dc7038a732f6113024165dc6fb8a732f6113024165dc6f38a732f6113024165dc6eb8a732f6113024165dc6e38a732f6113024165dc6db8)) else (if i < 4 then 0xa732f6113024165dc79b8a732f6113024165dc7938a732f6113024165dc78b8a732f6113024165dc7838a732f6113024165dc77b8a732f6113024165dc7738a732f6113024165dc7638a732f6113024165dc75b8a732f6113024165dc76b8a732f62cb0241649076b8a732f6113024165dc7538a732f6113024165dc5ab8a732f6113024165dc5a38a732f6113024165dc59b8a732f6113024165dc5938a732f6113024165dc58b8a732f6113024165dc5838a732f6113024165dc57b8a732f64e2aa4165dc57b8a732f6113024165dc5738 else (if i < 5 then 0xa732f6113023ee5dc18b8a732f6113024165dc1838a732f6113024165dc17b8a732f6113024165dc0d38a732f6113024165dc1738a732f6113024165dc16b8a732f6113024165dc2938a734b25eb024165dc28b8a732f6113024165dc28b8a734ba113024165dc2838a732f6113024165dc2838a732f6113024165dc2638a8f2f6113024165dc27b8a732f6113024165dc27b8a4b2f6113024165dc27b8a734c2013024165dc27b8a732f6113024165dc2738a732f6113024165dc26b8a732f6113024165dc25b8a732f6113024165dc7a38 else 0xa732f6113024165dc1c38a732f6113024165dc7b38a732f6113024165dc1bb8a732f6113024165dc1b38a732f6113024165dc1ab8acb2f6113024165901ab8a732f6113024165dc1a38a732f6113024165dc19b8a732f6113024165dc7ab8a732f6113024165dc1938a732f6113024165dc2a38a4b2f6113024165dc2a38a732f6113024165dc0fb8a732f6113024165dc0f38a732f6113024165dc0eb8b112f6112ee4165dc0eb8a732f6113024165dc0e38a732f6113024165dc0db8a732f61130243c5dc18b8a732f6113024165dc18b8))) else (if i < 9 then (if i < 7 then 0xa732f6113024165dc8238a7308a083024165dc8238a730898120b2ee44c8238b2f4e6113024165dc8138a7335e113024165dc8138a732f6113024165dc8138a7308a013024165dc8138a732f6113024165dc80b8a732f6113024165dc8038a732f6113024165dc7fb8a732f6113024165dc7f38a732f6113024165dc7eb8a732f6113024165dc7e38a732f6113024165dc7db8a732f6113024165dc7d38a732f6113314165dc7cb8a732f6113024165dc7cb8a732f6112aa4165dc7cb8a732f6113024165dc7c38a732f6113024165dc7bb8 else (if i < 8 then 0xb112f6112ee4165dc86b8a73472112da4165dc86b8a732f64e2aa4165dc86b8aef2f6113023ee5dc86b8a7341a113023c65dc86b8a732f63db023685dc86b8acb2f61130241659086b8a733be1130241654486b8a732f62cb0241649086b8a732f6113024165dc8638a732f6113024165dc85b8a732f6113024165dc8538a732f6113024165dc84b8a732f6113024165dc8438a732f6113024165dc8338b2f2f6113024165dc82b8aa32f6113024165dc82b8a732f6113024165dc82b897b08a083024165dc82b80014e6113024165dc8230 else 0xa732f6113024165dc8a38a734ba113024165dc89b8a732f6113024165dc89b8b252f6083024165dc89b8a732f6113024165dc88b8a732f6113024165dc8838a732f6113024165dc87b8a732f6113024165dc8738a732f60cb024165dc8738a732f6113024165dc83b8a734b25eb024165dc86b8a734ba113024165dc86b8b212f6113024165dc86b8a732f6113024165dc86b8a4b2f6113024165dc86b8a732d2113024165dc86b8b2f2ae113024165dc86b8a732f60cb024165dc86b8b252f6083024165dc86b8a734c2013024165dc86b8)) else (if i < 10 then 0xa732f62cb024165dc9238a732f6113024165dc9238a732f6113024165dc91b8a732f6113024165dc9138a732f6113024165dc90b8a732f6113024165dc9038a732f6113024165dc8fb8a732f6113024165dc8f38b212f6113024165dc8eb8a732f6113024165dc8eb8a734c2013024165dc8eb8a732f6113024165dc8e380012f6113024165dc8e3097b08a013024165dc8e3897b0898120b2ee4748e38a732f6113024165dc8cb8a732f6113024165dc8c38a732f6113024165dc8bb8a732f6113024165dc8b38a732f6113024165dc8ab8 else (if i < 11 then 0xa732f6113024165dc9938a732f6113024165dc98b8a732f6113024165dc9838a732f6113024165dc9738a732f6113024165dc97b8a732f6113024165dc96b8a732f6113024165dc9638a732f6113024165dc95b8a732f6113024165dc94b8a732f6113024165dc9438a732f6113024165dc93b8a732f6113024165dc9338a732f6113024165dc92b8a732f62cbbc60482c9238a732f62cb5260482c92380014e65ec5960482c9230a732f62cc2260482c9238a732f62cbfa60482c9238a732f62cb024ae82c9238a732f5ceb024165dc9238 else 0xa732f6113024165dc1db8a732f6113024165dc1d38a732f6113024165dc1cb8a732f6113024165dca1b8a732f6113024165dc9fb8a732f6113024165dc9f380014e65ec2260482c9e30a732f61130251282c9e38a732f6113024ae82c9e38a732f6113024165dc9e38a732f6113024165dc9db8a732f6113024ee82c9d38a732f6113025105dc9d38a732f6113024165dc9d38a732f6113024165dc9cb8a732f6113024165dc9c38a732f6113024165dc9bb8a732f6113024165dc9b38a732f6113024165dc9ab8a732f6113024165dc9a38)))) else (if i < 18 then (if i < 15 then (if i < 13 then 0xa732f6113024165dc23b8a732f6113024165dc2338a732f6113024165dc22b8a732f6113024165dc2238a732f6113024165dc21b8a734c2113024165dc2138a73342113024165dc2138a732f6113024165dc2138a732ae113024165dc2138a734c25eb024165dc20b8a732f61ab024165dc20b8a732f6113024165dc20b8a732f6083024165dc20b8a732f6113024165dc2038a732f6113024165dc1fb8a732f6113024165dc1f38a732f6113024165dc1eb8a732f6113154165dc1e38a732f6113024165dc1e38a732f6112ee4165dc1e38 else (if i < 14 then 0xb212f6113024165dc2538a732f6113024165dc2538a4b2f6113024165dc2538a732d2113024165dc2538b2f2ae113024165dc2538a732f60cb024165dc2538b252f6083024165dc2538a734c2013024165dc2538b112f6112ee4165dc2538a73472112da4165dc2538a732f64e2aa4165dc2538aef2f6113023ee5dc2538a7341a113023c65dc2538a732f63db023685dc2538acb2f6113024165902538a733be113024165442538a732f62cb024164902538a732f6113f32ee3682538a732f6113024165dc24b8a732f6113024165dc2438 else 0xa733be113024165dca8b8a732f6113024165dca8b8a732f6113024165dca838a732f6113024165dca638a732f6113024165dca5b8a732f61138160482ca4b8a732f61135260482ca4b80014e65ec2260482ca4b0a732f6113024165dca4b8a732f6113024165dca438a732f61136d60482ca3b8a732f6113804165dca3b8a732f6113024165dca3b8a732f6113024165dca338a732f6113024165dca2b8a732f6113024165dca238a732f61130252c2902538a732f61138d4162ec2538a734b25eb024165dc2538a734ba113024165dc2538)) else (if i < 16 then 0xa732f6113024165dcb238a732f6113024165dcb1b8a732f6113024165dcb138a732f6113024165dcaf38a732f6113024165dcaeb8a732f6113024165dcae38a732f6113024165dcac38a732f6113024165dcabb8a732f6113024165dcab38a732f6113024165dcaab8a732f6113024165dcaa38a732f6113024165dca9b8a732f6113024165dca938a733be113ca60482ca8b8a733be113bc60482ca8b8a733be1135260482ca8b80014e677c2260482ca8b0a733be5ec2260482ca8b8a733be113024ae82ca8b8a73089d7b024165dca8b8 else (if i < 17 then 0xa732f6113024165fcbbb8a732f6113024165e8bbb8a732f611302416600bbb8a732f611302416604bbb8a732f6113024165dcb838a732f6113024165dcb7b8a732f6113024165dcb638a732f6113024165dcb5b8a732f6113024165dcb438a732f6113024165dcb3b8a732f6113024165dcb338a732f6113024165dcb2b8acb2f6113c160482cb238acb2f6113bc60482cb238acb2f61135260482cb2380015965ec2260482cb230acb4e65ec2260482cb238acb2f6113024ae82cb23897b089da3024165dcb238acb2f6113024165dcb238 else 0xa732f611302416674bbb8a732f61130241666cbbb8a732f611302416668bbb8a732f611302416660bbb8a732f61130241665cbbb8a732f611302416658bbb8a732f611302416654bbb8a732f611302416650bbb8a732f61130241664cbbb8a732f611302416648bbb8a732f611302416644bbb8a732f61130241663cbbb8a732f611302416634bbb8a732f611302416624bbb8a732f61130241662cbbb8a732f611302416628bbb8a732f611302416620bbb8a732f61130241661cbbb8a732f611302416614bbb8a732f61130241660cbbb8))) else (if i < 21 then (if i < 19 then 0xa732f63db024166d0bbb8a732f6113024166d0bbb8a732f6113024166ccbbb8a732f6113024166c8bbb8a732f6113024166c4bbb8a732f6113024166c0bbb8a732f6113024166bcbbb8a732f6113024166b8bbb8a732f6113024166b0bbb8a732f6113024166a4bbb8a732f6113024166acbbb8a732f6113024166a8bbb8a732f6113024166a0bbb8a732f61130241669cbbb8a732f611302416698bbb8a732f611302416694bbb8a732f61130241668cbbb8a732f611302416688bbb8a732f611302416684bbb8a732f611302416680bbb8 else (if i < 20 then 0xa732f611302416708bbb8a732f611302416704bbb8a732f611302416700bbb8a732f6113024166f8bbb8a732f6113024166fcbbb8a732f6113024166f4bbb8a732f6113024166f0bbb8a732f6113024166ecbbb8a732f6113024166e4bbb8a732f6113024166e0bbb8a732f6113024166dcbbb8a732f6113024166d8bbb8a732f6113024166d4bbb8a732f63dbbc6046d0bbb8a732f63db946046d0bbb8a732f63db526046d0bbb80014e65ec7b6046d0bbb0a732f63dc226046d0bbb8a732f63db024ae6d0bbb8a732f59bb024166d0bbb8 else 0xa732f6113e6416764bbb8a732f611302416760bbb8a732f61130241675cbbb8a732f611302416758bbb8a732f61130241674cbbb8a732f61130241673cbbb8a732f611302416738bbb80014e65ec22604730bbb0a732f6113024ee730bbb8a732f6113024ae730bbb8a732f611302416730bbb8a732f61130241672cbbb8a732f611302512728bbb8a732f611302416728bbb8a732f611302416724bbb8a732f611302416720bbb8a732f61130241671cbbb8a732f611302416718bbb8a732f611302416714bbb8a732f611302416710bbb8)) else (if i < 22 then 0xa732f611302416790bbb8a7341a113bc60478cbbb8a7341a1136260478cbbb8a7341a1135260478cbbb80014e68342260478cbbb0a7341a5ec2260478cbbb8a7341a113024ae78cbbb8a73089a3b0241678cbbb8a7341a1130241678cbbb8a732f61130241678cbbb8a732f611302416788bbb8a732f611302416778bbb8a732f611302416774bbb8a732f6113bc60476cbbb80014e65ec2260476cbbb0a732f6113e760476cbbb8a732f61130241676cbbb8a732f611302416768bbb8a732f6113d5604764bbb8a732f611302416764bbb8 else (if i < 23 then 0xaef2f6113bc6047dcbbb8aef2f6113586047dcbbb8aef2f6113526047dcbbb80015de5ec226047dcbbb0aef4e65ec226047dcbbb8aef2f6113024ae7dcbbb897b089a5b024167dcbbb8aef2f6113024167dcbbb8a732f6113024167dcbbb8a732f6113024167d8bbb8a732f6113024167d4bbb8a732f6113024167c4bbb8a732f6113024167c0bbb8a732f6113024167bcbbb8a732f6113024167a8bbb8a732f6113024167a4bbb8a732f6113024167a0bbb8a732f61130241679cbbb8a732f611302416798bbb8a732f611302416794bbb8 else 0xa732f61130243a82cbbb8a732f61130243882cbbb8a732f61130243682cbbb8a732f61130243482cbbb8a732f61130243282cbbb8a732f61130242e82cbbb8a732f61130242882cbbb8a732f61130242682cbbb8a732f61130242a82cbbb8a732f61130241c82cbbb80014e65ec227cc82cbbb0a732f6113f37ce82cbbb8a732f611302416810bbb8a732f61130241680cbbb8a732f611302416800bbb8a732f6113024167fcbbb8a732f6113024167ecbbb8a732f6113024167e8bbb8a732f6113024167e4bbb8a732f6113024167e0bbb8))))) else (if i < 36 then (if i < 30 then (if i < 27 then (if i < 25 then 0xa732f61130246c82cbbb8a732f61130246a82cbbb8a732f61130246682cbbb8a732f61130246482cbbb8a732f61130246282cbbb8a732f61130246082cbbb8a732f61130245e82cbbb8a732f61130245a82cbbb8a732f61130245882cbbb8a732f61130245482cbbb8a732f61130245282cbbb8a732f61130245082cbbb8a732f61130244e82cbbb8a732f61130244c82cbbb8a732f61130244a82cbbb8a732f61130244882cbbb8a732f61130244682cbbb8a732f61130244482cbbb8a732f61130244082cbbb8a732f61130243c82cbbb8 else (if i < 26 then 0xa732f61130249482cbbb8a732f61130249282cbbb8a732f61130249082cbbb8a732f61130248c82cbbb8a732f61130248a82cbbb8a732f61130248882cbbb8a732f61130248682cbbb8a732f61130248482cbbb8a732f625b0248282cbbb8a732f61130248282cbbb8a732f5812aa48282cbbb8a732f61130248082cbbb8a732f61130247e82cbbb8a732f61130247c82cbbb8a732f61130247882cbbb8a732f61130247682cbbb8a732f61130247482cbbb8a732f61130247282cbbb8a732f61130247082cbbb8a732f61130246e82cbbb8 else 0xb252f6083024ae82cbbb8a734c2013024ae82cbbb8b112f6112ee4ae82cbbb8a73472112da4ae82cbbb8a732f64e2aa4ae82cbbb8a732f6113024ac82cbbb8a732f6113024aa82cbbb8a732f6113024a882cbbb8a732f6113024a482cbbb8a732f6113024a282cbbb8ab92f6113024a082cbbb8a732f6113024a082cbbb897b089812ee4a082cbbb8a732f61130249e82cbbb8a732f61130249c82cbbb8a732f61130249a82cbbb8a733921130249882cbbb8a732f61130249882cbbb8a73089812da49882cbbb8a732f61130249682cbbb8)) else (if i < 28 then 0xa732f6113024c682cbbb8a732f6113024c482cbbb8a732f6113024c282cbbb8a732f6113024c082cbbb8a732f6113024bc82cbbb8a732f6113024ba82cbbb8b112f6112ee4ba82cbbb8a732f6113024b682cbbb8a732f6113024b482cbbb8a732f6113024b282cbbb8a732f6113024b082cbbb8a732f6113024a682cbbb8a734b25eb024ae82cbbb8a734ba113024ae82cbbb8b212f6113024ae82cbbb8a732f6113024ae82cbbb8a4b2f6113024ae82cbbb8a732d2113024ae82cbbb8b2f2ae113024ae82cbbb8a732f60cb024ae82cbbb8 else (if i < 29 then 0xa732f6113024fe82cbbb8a732f6113024fa82cbbb8a732f6113024f482cbbb8a732f6113024f282cbbb8a732f6113024f082cbbb8a732f6113024ec82cbbb8a732f6113024ee82cbbb8a732f6113024ea82cbbb8a732f6113024e682cbbb8a732f6113024e482cbbb8a732f6113024e282cbbb8a732f6113024de82cbbb8a732f6113024dc82cbbb8a732f6113024da82cbbb8a732f6113024d682cbbb8a732f6113024d082cbbb8a732f6113024ce82cbbb8a73472112da4ce82cbbb8a732f6113024cc82cbbb8a732f6113024c882cbbb8 else 0xa732f61130253082cbbb8a732f61130252c82cbbb8a732f61130252e82cbbb8a732f61130252a82cbbb8a732f61130252882cbbb8a732f61130252682cbbb8a732f61130252482cbbb8a732f61130252082cbbb8a732f61130251c82cbbb8a732f61130251882cbbb8a732f61130251682cbbb8a732f61130251482cbbb8a732f61130251282cbbb8a732f61130251082cbbb8a732f61130250e82cbbb8a732f61130250a82cbbb8a732f61130250882cbbb8a732f61130250682cbbb8a732f61130250282cbbb8a732f61130250082cbbb8))) else (if i < 33 then (if i < 31 then 0xa732f64e35255482cbbb8a732f64e30255482cbbb8a732f61130255482cbbb80014e65ec9c55482cbbb0a732f64e42255482cbbb8a732f61130255282cbbb8a732f61130255082cbbb8a732f61130254e82cbbb8a732f61130254c82cbbb8a732f61130254a82cbbb8a732f61130254882cbbb8a732f61130254482cbbb8a732f61130254282cbbb8a732f61130254082cbbb8a732f61130253e82cbbb8a732f61130253c82cbbb8a732f64e2aa53c82cbbb8a732f61130253a82cbbb8a732f61130253682cbbb8a732f61130253282cbbb8 else (if i < 32 then 0xa732f61130258282cbbb8a732f61130258082cbbb8a732f61130257e82cbbb8a732f61130257a82cbbb8a732f61130257882cbbb8a732f61130257682cbbb8a732f61130257282cbbb8a732f61130257082cbbb8a732f61130256e82cbbb8a732f61130256a82cbbb8a732f61130256c82cbbb8a732f61130256882cbbb8a732f61130256682cbbb8a732f61130256282cbbb8a732f61130255e82cbbb8a732f61130255c82cbbb8a732f61130255a82cbbb8a732f61130255882cbbb8a732f61130255682cbbb8a732f64e3bc55482cbbb8 else 0xa732f6113d55a282cbbb8a732f6113bc5a282cbbb8a732f6113025a282cbbb80014e65ec225a282cbbb0a732f6113025a082cbbb8a732f61130259e82cbbb8a732f6113e759e82cbbb8a732f61130259c82cbbb8a732f61130259a82cbbb8a732f61130259882cbbb8a732f61130259682cbbb8a732f61130258e82cbbb8a732f61130258c82cbbb8a732f61136d58882cbbb8a732f61135258882cbbb8a732f61130258882cbbb80014e65ec2258882cbbb0a732f61130258682cbbb8a732f61138158482cbbb8a732f61130258482cbbb8)) else (if i < 34 then 0xa732f6113025d082cbbb8a732f6113025ce82cbbb8a732f6113025cc82cbbb8a732f6113025c482cbbb8a732f6113025c282cbbb8a732f6113025c082cbbb8a732f6113025bc82cbbb8a732f6113025ba82cbbb8a732f6113025b882cbbb8a732f6113025b682cbbb8a73472113bc5b482cbbb8a73472113525b482cbbb8a73472113025b482cbbb8a732f6113025b482cbbb80014e68e4225b482cbbb0a734725ec225b482cbbb8a732f6113025b282cbbb8a732f6113025b082cbbb8a732f6113025a882cbbb8a732f6113025a682cbbb8 else (if i < 35 then 0xa732f6113df60482cbbb8a732f6113de60482cbbb8a732f6113dd60482cbbb8a732f6113db60482cbbb8a732f6113025f682cbbb8a732f6113025f482cbbb8a732f6113025ee82cbbb8a732f6113025ec82cbbb8a732f6113025e682cbbb8a732f6113025e482cbbb8a732f6113025e082cbbb8a732f6113025de82cbbb8b112f6113bc5dc82cbbb8b112f6113525dc82cbbb8b112f6113025dc82cbbb8a732f6113025dc82cbbb80016225ec225dc82cbbb0b114e65ec225dc82cbbb8a732f6113025da82cbbb8a732f6113025d882cbbb8 else 0xa732f6113f760482cbbb8a732f6113f660482cbbb8a732f6113f560482cbbb8a732f6113f360482cbbb8a732f6113f460482cbbb8a732f6113f260482cbbb8a732f6113f160482cbbb8a732f6113f060482cbbb8a732f6113ef60482cbbb8a732f6113ed60482cbbb8a732f6113eb60482cbbb8a732f6113ea60482cbbb8a732f6113e960482cbbb8a732f6113e860482cbbb8a732f6113e660482cbbb8a732f6113e760482cbbb8a732f6113e560482cbbb8a732f6113e360482cbbb8a732f6113e260482cbbb8a732f6113e160482cbbb8)))) else (if i < 42 then (if i < 39 then (if i < 37 then 0xa732f61140560482cbbb8a732f61140460482cbbb8a732f61140360482cbbb80014e69840260482cbbb0a734c25ec0260482cbbb8a732f61ac0260482cbbb8a734c21140260482cbbb8a733421140260482cbbb8b212f61140260482cbbb8a732f61140260482cbbb8a732ae1140260482cbbb8a732f60840260482cbbb8a732f61140160482cbbb8a732f61140060482cbbb8a732f6113fe60482cbbb8a732f6113fd60482cbbb8a732f6113fc60482cbbb8a732f6113fb60482cbbb8a732f6113fa60482cbbb8a732f6113f960482cbbb8 else (if i < 38 then 0xa732f61141460482cbbb8a732f61141360482cbbb8a732f61141160482cbbb800164a5ec1060482cbbb0b254e65ec1060482cbbb8a732f61e41060482cbbb8a734ba1141060482cbbb8b252f61141060482cbbb8a992f61141060482cbbb8a732f61141060482cbbb897b2ae1141060482cbbb8a732f61140f60482cbbb8a732f61140e60482cbbb8a732f61140d60482cbbb8a732f61140c60482cbbb8a732f61140b60482cbbb8a732f61140a60482cbbb8a732f61140960482cbbb8a732f61140860482cbbb8a732f61140760482cbbb8 else 0xa732f61b42260482cbbb8a732f61ac2260482cbbb8a732f61a42260482cbbb8a732f619c2260482cbbb8a732f61942260482cbbb8a732f618c2260482cbbb8a732f61842260482cbbb8a732f61642260482cbbb8a732f615c2260482cbbb8a732f61542260482cbbb8a732f614c2260482cbbb8a732f613c2260482cbbb8a732f61342260482cbbb8b2f4e65ec1960482cbbb80014e65ec1960482cbbb0a732f61141960482cbbb8a732f61141860482cbbb8a732f61141760482cbbb8a732f61141660482cbbb8a732f61141560482cbbb8)) else (if i < 40 then 0xa732f62642260482cbbb8a732f625c2260482cbbb8a732f62542260482cbbb8a732f624c2260482cbbb8a732f623c2260482cbbb8a732f62342260482cbbb8a732f622c2260482cbbb8a732f62242260482cbbb8a732f621c2260482cbbb8a732f62142260482cbbb8a732f620c2260482cbbb8a732f62042260482cbbb8a732f61fc2260482cbbb8a732f61f42260482cbbb8a732f61e42260482cbbb8a732f61dc2260482cbbb8a732f61d42260482cbbb8a732f61cc2260482cbbb8a732f61c42260482cbbb8a732f61bc2260482cbbb8 else (if i < 41 then 0xa732f630c2260482cbbb8a732f63042260482cbbb8a732f62fc2260482cbbb8a732f62f42260482cbbb8a732f62ec2260482cbbb8a732f62e42260482cbbb8a732f62dc2260482cbbb8a732f62d42260482cbbb8a732f62cc2260482cbbb8a732f62c42260482cbbb8a732f62bc2260482cbbb8a732f62b42260482cbbb8a732f62ac2260482cbbb8a732f629c2260482cbbb8a732f62942260482cbbb8a732f628c2260482cbbb8a732f62842260482cbbb8a732f627c2260482cbbb8a732f62742260482cbbb8a732f626c2260482cbbb8 else 0xa732f63c42260482cbbb8a732f63bc2260482cbbb8a732f63ac2260482cbbb8a732f63a42260482cbbb8a732f639c2260482cbbb8a732f63942260482cbbb8a732f638c2260482cbbb8a732f63842260482cbbb8a732f637c2260482cbbb8a732f636c2260482cbbb8a732f63642260482cbbb8a732f635c2260482cbbb8a732f63542260482cbbb8a732f634c2260482cbbb8a732f63442260482cbbb8a732f633c2260482cbbb8a732f63342260482cbbb8a732f632c2260482cbbb8a732f63242260482cbbb8a732f631c2260482cbbb8))) else (if i < 45 then (if i < 43 then 0xa732f646c2260482cbbb8a732f64642260482cbbb8a732f645c2260482cbbb8a732f64542260482cbbb8a732f644c2260482cbbb8a732f64442260482cbbb8a732f643c2260482cbbb8a732f64342260482cbbb8a732f642c2260482cbbb8a732f641c2260482cbbb8a732f64142260482cbbb8a732f640c2260482cbbb8a732f64042260482cbbb8a732f63fc2260482cbbb8a732f63f42260482cbbb8a732f63ec2260482cbbb8a732f63e42260482cbbb8a732f63dc2260482cbbb8a732f63d42260482cbbb8a732f63cc2260482cbbb8 else (if i < 44 then 0xa732f651c2260482cbbb8a732f65142260482cbbb8a732f650c2260482cbbb8a732f65042260482cbbb8a732f64fc2260482cbbb8a732f64f42260482cbbb8a732f64ec2260482cbbb8a732f64e42260482cbbb8a732f64dc2260482cbbb8a732f64d42260482cbbb8a732f64cc2260482cbbb8a732f64c42260482cbbb8a732f64b42260482cbbb8a732f64ac2260482cbbb8a732f64a42260482cbbb8a732f649c2260482cbbb8a732f64942260482cbbb8a732f648c2260482cbbb8a732f647c2260482cbbb8a732f64742260482cbbb8 else 0xa732f65a42260482cbbb8a732f659c2260482cbbb8a732f65942260482cbbb8a732f658c2260482cbbb8a732f65842260482cbbb8a732f657c2260482cbbb8a732f65742260482cbbb8a732f656c2260482cbbb800165e55c2260482cbbb0b2f4e655c2260482cbbb8a7335e55c2260482cbbb8b2f2f655c2260482cbbb8aa32f655c2260482cbbb8a732f655c2260482cbbb8a732f65542260482cbbb8a732f654c2260482cbbb8a732f65442260482cbbb8a732f653c2260482cbbb8a732f65342260482cbbb8a732f65242260482cbbb8)) else (if i < 46 then 0xa7335a5ec2260482cbbb8a733565ec2260482cbbb8a733525ec2260482cbbb8a7334e5ec2260482cbbb8a7334a5ec2260482cbbb8a733465ec2260482cbbb8a733425ec2260482cbbb8a7333e5ec2260482cbbb8a7333a5ec2260482cbbb8a733365ec2260482cbbb8a733325ec2260482cbbb8a7332e5ec2260482cbbb8a7331e5ec2260482cbbb8a7331a5ec2260482cbbb8a733165ec2260482cbbb8a733125ec2260482cbbb8a7330e5ec2260482cbbb8a733065ec2260482cbbb8b254e65a42260482cbbb80014e65a42260482cbbb0 else (if i < 47 then 0xa733b65ec2260482cbbb8a733b25ec2260482cbbb8a733ae5ec2260482cbbb8a733a65ec2260482cbbb8a733a25ec2260482cbbb8a7339e5ec2260482cbbb8a7339a5ec2260482cbbb8a733965ec2260482cbbb8a733925ec2260482cbbb8a7338e5ec2260482cbbb8a7338a5ec2260482cbbb8a733825ec2260482cbbb8a7337e5ec2260482cbbb8a7337a5ec2260482cbbb8a733765ec2260482cbbb8a733725ec2260482cbbb8a7336e5ec2260482cbbb8a7336a5ec2260482cbbb8a733665ec2260482cbbb8a7335e5ec2260482cbbb8 else 0xa7340e5ec2260482cbbb8a7340a5ec2260482cbbb8a734025ec2260482cbbb8a733fe5ec2260482cbbb8a733fa5ec2260482cbbb8a733f65ec2260482cbbb8a733f25ec2260482cbbb8a733ee5ec2260482cbbb8a733ea5ec2260482cbbb8a733e65ec2260482cbbb8a733e25ec2260482cbbb8a733de5ec2260482cbbb8a733d65ec2260482cbbb8a733d25ec2260482cbbb8a733ce5ec2260482cbbb8a733ca5ec2260482cbbb8a733c65ec2260482cbbb8a733c25ec2260482cbbb8a733be5ec2260482cbbb8a733ba5ec2260482cbbb8)))))) else (if i < 72 then (if i < 60 then (if i < 54 then (if i < 51 then (if i < 49 then 0xa734665ec2260482cbbb8a734625ec2260482cbbb8a7345a5ec2260482cbbb8a734565ec2260482cbbb8a734525ec2260482cbbb8a7344e5ec2260482cbbb8a7344a5ec2260482cbbb8a734465ec2260482cbbb8a734425ec2260482cbbb8a7343e5ec2260482cbbb8a7343a5ec2260482cbbb8a734325ec2260482cbbb8a7342e5ec2260482cbbb8a7342a5ec2260482cbbb8a734265ec2260482cbbb8a734225ec2260482cbbb8a7341e5ec2260482cbbb8a7341a5ec2260482cbbb8a734165ec2260482cbbb8a734125ec2260482cbbb8 else (if i < 50 then 0xa734c65ec2260482cbbb8a8f4c25ec2260482cbbb8a734c25ec2260482cbbb8a734ba5ec2260482cbbb8a734b25ec2260482cbbb8a734ae5ec2260482cbbb8a734965ec2260482cbbb8a614965ec2260482cbbb80014965ec2260482cbbb0a734925ec2260482cbbb8a7348e5ec2260482cbbb8a7348a5ec2260482cbbb8a734865ec2260482cbbb8a734825ec2260482cbbb8a7347e5ec2260482cbbb8a7347a5ec2260482cbbb8a734765ec2260482cbbb8a734725ec2260482cbbb8a7346e5ec2260482cbbb8a7346a5ec2260482cbbb8 else 0xaa34e65ec2260482cbbb8aa14e65ec2260482cbbb8a9f4e65ec2260482cbbb8a9d4e65ec2260482cbbb8a9b4e65ec2260482cbbb8a994e65ec2260482cbbb8a974e65ec2260482cbbb8a954e65ec2260482cbbb8a934e65ec2260482cbbb8a914e65ec2260482cbbb8a8f4e65ec2260482cbbb8a874e65ec2260482cbbb8a854e65ec2260482cbbb8a834e65ec2260482cbbb8a814e65ec2260482cbbb8a7f4e65ec2260482cbbb8a7d4e65ec2260482cbbb8a734d25ec2260482cbbb8a734ce5ec2260482cbbb8a734ca5ec2260482cbbb8)) else (if i < 52 then 0xad14e65ec2260482cbbb8acf4e65ec2260482cbbb8acd4e65ec2260482cbbb8acb4e65ec2260482cbbb8ac94e65ec2260482cbbb8ac74e65ec2260482cbbb8ac34e65ec2260482cbbb8ac14e65ec2260482cbbb8abf4e65ec2260482cbbb8abd4e65ec2260482cbbb8abb4e65ec2260482cbbb8ab94e65ec2260482cbbb8ab74e65ec2260482cbbb8ab54e65ec2260482cbbb8ab14e65ec2260482cbbb8aaf4e65ec2260482cbbb8aad4e65ec2260482cbbb8aab4e65ec2260482cbbb8aa94e65ec2260482cbbb8aa74e65ec2260482cbbb8 else (if i < 53 then 0xaff4e65ec2260482cbbb8afd4e65ec2260482cbbb8afb4e65ec2260482cbbb8af74e65ec2260482cbbb8af54e65ec2260482cbbb8af34e65ec2260482cbbb8af14e65ec2260482cbbb8aef4e65ec2260482cbbb8aed4e65ec2260482cbbb8aeb4e65ec2260482cbbb8ae74e65ec2260482cbbb8ae54e65ec2260482cbbb8ae34e65ec2260482cbbb8ae14e65ec2260482cbbb8adf4e65ec2260482cbbb8add4e65ec2260482cbbb8adb4e65ec2260482cbbb8ad94e65ec2260482cbbb8ad74e65ec2260482cbbb8ad34e65ec2260482cbbb8 else 0xb2b4e65ec2260482cbbb8b294e65ec2260482cbbb8b274e65ec2260482cbbb8b254e65ec2260482cbbb8b214e65ec2260482cbbb8b1f4e65ec2260482cbbb8b1d4e65ec2260482cbbb8b1b4e65ec2260482cbbb8b194e65ec2260482cbbb8b174e65ec2260482cbbb8b154e65ec2260482cbbb8b134e65ec2260482cbbb8b114e65ec2260482cbbb8b0f4e65ec2260482cbbb8b0d4e65ec2260482cbbb8b094e65ec2260482cbbb8b074e65ec2260482cbbb8b054e65ec2260482cbbb8b034e65ec2260482cbbb8b014e65ec2260482cbbb8))) else (if i < 57 then (if i < 55 then 0xb255465ec2260482cbbb8b2f5325ec2260482cbbb800151e5ec2260482cbbb0b3b4e65ec2260482cbbb8b4d4e65ec2260482cbbb8b4b4e65ec2260482cbbb8b494e65ec2260482cbbb8b474e65ec2260482cbbb8b454e65ec2260482cbbb8b434e65ec2260482cbbb8b414e65ec2260482cbbb8b3f4e65ec2260482cbbb8b3d4e65ec2260482cbbb8b394e65ec2260482cbbb8b374e65ec2260482cbbb8b354e65ec2260482cbbb8b334e65ec2260482cbbb8b314e65ec2260482cbbb8b2f4e65ec2260482cbbb8b2d4e65ec2260482cbbb8 else (if i < 56 then 0xa732f643c5960482cbbb8a732f64e44b60482cbbb8a734c25ec3c60482cbbb8b254e65ec3560482cbbb8b2f4e65ec3060482cbbb80014e65ec3060482cbbb0b2f4e69842260482cbbb80014e69742260482cbbb0a7341a7cc2260482cbbb8a7344277c2260482cbbb8a734727242260482cbbb8a734c26bc2260482cbbb8b2f4e66842260482cbbb8b254e665c2260482cbbb80014e665c2260482cbbb0b2f64a5ec2260482cbbb80016425ec2260482cbbb0aef5b65ec2260482cbbb8aff5965ec2260482cbbb8b115725ec2260482cbbb8 else 0xa732f61131c60482cbbb8a732f61131b60482cbbb8a732f61131a60482cbbb8a732f61131960482cbbb8a732f61131760482cbbb8a732f61131560482cbbb8a732f61131460482cbbb8a732f61131360482cbbb8a732f61131260482cbbb8a732f61131160482cbbb8a732f61131060482cbbb8a732f61130e60482cbbb8a732f61130b60482cbbb8a732f61130a60482cbbb8a732f61130560482cbbb8a732f61130c60482cbbb8b254e6984bd60482cbbb80014e6964bd60482cbbb0a734b25ecab60482cbbb8a732f63dc6560482cbbb8)) else (if i < 58 then 0xa732f61133460482cbbb8a732f61133260482cbbb8a732f61133160482cbbb8a732f61133060482cbbb8a732f61132f60482cbbb8a732f61132e60482cbbb8a732f61132d60482cbbb8a732f61132c60482cbbb8a732f61132b60482cbbb8a732f61132960482cbbb8a732f61132860482cbbb8a732f61132760482cbbb8a732f61132660482cbbb8a732f61132560482cbbb8a732f61132360482cbbb8a732f61132160482cbbb8a732f61132060482cbbb8a732f61131f60482cbbb8a732f61131e60482cbbb8a732f61131d60482cbbb8 else (if i < 59 then 0xa732f61134a60482cbbb8a732f61134960482cbbb8a732f61134860482cbbb8a733e61134760482cbbb8a732f61134760482cbbb8a732f61134660482cbbb8a732f61134560482cbbb8a732f61134460482cbbb8a732f61134260482cbbb8a732f61133f60482cbbb8a732f61133e60482cbbb8a732f61133c60482cbbb8a732f61133b60482cbbb8a732f61133a60482cbbb8a732f61133960482cbbb8a732f61133860482cbbb8a732f632b3760482cbbb8a732f61133760482cbbb8a732f61133660482cbbb8a732f61133560482cbbb8 else 0xa732f61135460482cbbb8a732f61135360482cbbb8a732f61134e60482cbbb8a734b25eb5260482cbbb8a734ba1135260482cbbb8b212f61135260482cbbb8a732f61135260482cbbb8a4b2f61135260482cbbb8a732d21135260482cbbb8b2f2ae1135260482cbbb8a732f60cb5260482cbbb8b252f60835260482cbbb8a734c20135260482cbbb8a732f61135160482cbbb8a732f61135060482cbbb8a732f61134f60482cbbb8a732f61134d60482cbbb8a732f61134c60482cbbb8adb2f61134b60482cbbb8a732f61134b60482cbbb8)))) else (if i < 66 then (if i < 63 then (if i < 61 then 0xa732f61136c60482cbbb8a732f61136d60482cbbb8a732f61136b60482cbbb8a732f61136a60482cbbb8a732f61136860482cbbb8a732f61136760482cbbb8a732f61136660482cbbb8a732f61136460482cbbb8a732f61136360482cbbb8a732f61136260482cbbb8a732f61136160482cbbb8a732f61136060482cbbb8a732f61135f60482cbbb8a732f61135d60482cbbb8a732f61135c60482cbbb8a732f61135b60482cbbb8a732f61135960482cbbb8a732f61135860482cbbb8a732f61135760482cbbb8a732f61135560482cbbb8 else (if i < 62 then 0xa732f61138a60482cbbb8a732f61138960482cbbb8a732f61138760482cbbb8a732f61138560482cbbb8a732f61138460482cbbb8a732f61138360482cbbb8a732f61138260482cbbb8a732f61138060482cbbb8a732f61138160482cbbb8a732f61137f60482cbbb8a732f61137d60482cbbb8a732f61137c60482cbbb8a732f61137b60482cbbb8a732f61137960482cbbb8a732f61137860482cbbb8a732f61137760482cbbb8a732f61137560482cbbb8a732f61137060482cbbb8a732f61136f60482cbbb8a732f61136e60482cbbb8 else 0xa732f61139f60482cbbb8a732f61139e60482cbbb8a732f643b9d60482cbbb8a732f61139d60482cbbb8a732f61139c60482cbbb8a732f61139b60482cbbb8a732f61139a60482cbbb8a732f61139860482cbbb8a732f61139760482cbbb8a732f61139660482cbbb8a732f61139560482cbbb8a732f61139460482cbbb8a732f61139360482cbbb8a732f61139160482cbbb8a732f61139060482cbbb8a732f61138f60482cbbb8a732f61138d60482cbbb8a732f61138e60482cbbb8a732f61138c60482cbbb8a732f61138b60482cbbb8)) else (if i < 64 then 0xa732f6113ba60482cbbb8a732f6113b960482cbbb8a732f6113b760482cbbb8a732f6113b660482cbbb8aff2f6113b460482cbbb8a732f6113b460482cbbb8a732f6113b360482cbbb8a732f6113b260482cbbb8a732f6113b060482cbbb8a73442113af60482cbbb8a732f6113af60482cbbb8a732f6113ae60482cbbb8a732f6113ad60482cbbb8a732f6113ac60482cbbb8a732f6113aa60482cbbb8a732f6113a760482cbbb8a732f6113a460482cbbb8a732f6113a260482cbbb8a732f6113a160482cbbb8a732f6113a060482cbbb8 else (if i < 65 then 0xa732f6113c560482cbbb8a732f6113c460482cbbb8a732f6113c260482cbbb8a732f6113c160482cbbb8a732f6113c060482cbbb8a732f6113bf60482cbbb8a732f6113be60482cbbb8a732f6113bd60482cbbb8a732f6113b860482cbbb8a734b25ebbc60482cbbb8a734ba113bc60482cbbb8b212f6113bc60482cbbb8a732f6113bc60482cbbb8a4b2f6113bc60482cbbb8a732d2113bc60482cbbb8b2f2ae113bc60482cbbb8a732f60cbbc60482cbbb8b252f6083bc60482cbbb8a734c2013bc60482cbbb8a732f6113bb60482cbbb8 else 0xa732f64e42266282cbbb8a734725ec2264082cbbb8b114e65ec2262a82cbbb8a732f6113d860482cbbb8a732f6113d760482cbbb8a732f6113d660482cbbb8a732f6113d460482cbbb8a732f6113d560482cbbb8a732f6113d360482cbbb8a732f6113d260482cbbb8a732f6113d060482cbbb8a732f6113cf60482cbbb8a732f6113ce60482cbbb8a732f6113cc60482cbbb8a732f6113cb60482cbbb8a732f6113ca60482cbbb8a732f6113c960482cbbb8a732f6113c860482cbbb8a732f6113c760482cbbb8a732f6113c660482cbbb8))) else (if i < 69 then (if i < 67 then 0xa733be5ec2260482ccbb8acb4e65ec2260482cc5b80014e65ec227a8c08bbb0a732f6113f37aac08bbb8a732f6113d4778c08bbb8a732f6113d4604b3cbbb8a732f6113d5604a58bbb8a732f6113f3604a24bbb8a732f61130252ca24bbb80014e65ec22604a20bbb0a732f61130251095cbbb8a732f63dc226048ecbbb8a7341a5ec226048a4bbb8aef4e65ec22604878bbb8a732f6113e677882cbbb8a732f6113e771a82cbbb80014e65ec2270082cbbb0a732f61138d70282cbbb8a732f6113f370282cbbb8a732f6113806a482cbbb8 else (if i < 68 then 0xa732f61130252c82c5db8a732f61138d4ae82c5db8a732f61138d4166fc5db8a732f61138d4165dc5db8a732f6113024165dc5db8a732f6112cf4165dc5db8a732f6112c24165dc5db8a732f6113f34165dc5db8a732f61130241651c5db8a732f6113024164e85db8a732f61138d4164345db8a732f6113024165dc5d38a732f6113024165dc5cb8a732f6113024165dc5c38a732f6113024165dc5bb8a732f6113024165dc2cb8a732f6113024165dc2c38a732f6113024165dc2bb8a732f6113024165dc4fb8a732f6113024165dc3138 else 0xa732f6113024165dc6438a732f6113024165dc63b8a732f6113024166ac6338a732f6113024165dc6338a732f6113024164906338a732f6113024165dc62b8a732f6113024165dc6238a732f6113024165dc61b8a732f6113024165dc6138a732f6113024165dc60b8a732f6113024165dc6038a732f6113024165dc5fb8a732f6113024165dc5f38a732f6113024165dc5eb8a732f6113024165dc5e38a732f6113bc71a82c5db80014e65ec2271a82c5db0a732f64742271a82c5db8a732f61138d6a482c5db8a732f61138d60482c5db8)) else (if i < 70 then 0xa732f6113023c65dc3c38a732f6113024165dc3bb8a732f6113024165dc3b38a732f6113024165dc2d38a732f6113024165dc3ab8a732f6113024165dc3a38a732f6113024165dc39b8a732f61130241662c12b8a732f6113024165dc12b8a732f61130241659012b8a732f6113024165dc1238a732f6113024165dc11b8a732f6113024165dc1138a732f6113024165dc10b8a732f6113024165dc4f38a732f6113024ec82ce538a732f62cc2260482cd5b8a732f6113024165dc0bb8a732f6113024165dc6538a732f6113024165dc64b8 else (if i < 71 then 0xa732f6113024165dc6938a732f6113024165dc68b8a732f6113024165dc6838a732f6113024165dc67b8a732f6113024165dc6738a732f63db023685dc6738a732f6113024165dc66b8a732f6113024165dc6638a732f6113024165dc65b8a732f6113024165dc30b8a732f6113024165dc3038a732f6113024165dc2fb8a732f6113024165dc2f38a732f6113024165dc2db8a732f6113024165dc2eb8a73472112da4165dc2eb8a732f6113024165dc2e38a732f6113024165dc3cb8a732f6113024525dc3c38a732f6113024165dc3c38 else 0xa732f61136c604b0905b8a732f61136d604a5905b80014e65ec226049d905b0a732f61138d6049dd05b8a732f61130252c9dd05b8a732f6113024ec95d05b8a732f6113024165dc6ab8a732f6113024165dc0b38a732f6113024165dc4138a732f6113024165dc40b8a732f6113024165dc4038a732f6113024165dc3fb8a732f6113024165dc3f38a732f6113024165dc3eb8a733be113024165443eb8a732f6113024165dc3e38a732f6113024165dc3db8a732f6113024165dc3d38a732f6113024165dc6a38a732f6113024165dc69b8))))) else (if i < 84 then (if i < 78 then (if i < 75 then (if i < 73 then 0xa732f6113024165dc44b8a732f6113024165dc4438a732f6113024165dc43b8a732f6113204165dc4338a732f6113024165dc4338a732f6112da4165dc4338a732f6113024165dc42b8a732f6113024165dc4238a732f6113024165dc1638a732f6113024165dc41b8a732f6113024165dc15b8a732f6113024165dc1538a732f6113024165dc13b8a732f6113024165dc14b8aef2f6113023ee5dc14b8a732f6113024165dc1438a732f6113024165dc13380014e65ec226d8c0905b0a732f61138d6dac0905b8a732f61136c6a4c0905b8 else (if i < 74 then 0xa732f6113024165dc4b38a732f6113024165dc4ab8a732f6113024165dc4a38a732f6113024165dc49b8a732f6113024165dc4938a732f6113024165dc4838b252f6113024165dc47b8a992f6113024165dc47b8a732f6113024165dc47b897b2ae113024165dc47b8a732f58120b2ee27447380014e65eb024165dc4730a732f655b024165dc4738a732f6113024165dc4738b254e65eb024165dc4638a732f61e3024165dc4638a732f6113024165dc4638a732f6013024165dc4638a732f6113024165dc45b8a732f6113024165dc4538 else 0xa734b25eb024165dc4bb8a734ba113024165dc4bb8b212f6113024165dc4bb8a732f6113024165dc4bb8a4b2f6113024165dc4bb8a732d2113024165dc4bb8b2f2ae113024165dc4bb8a732f60cb024165dc4bb8b252f6083024165dc4bb8a734c2013024165dc4bb8b112f6112ee4165dc4bb8a73472112da4165dc4bb8a732f64e2aa4165dc4bb8aef2f6113023ee5dc4bb8a7341a113023c65dc4bb8a732f63db023685dc4bb8acb2f6113024165904bb8a733be113024165444bb8a732f62cb024164904bb8a732f6113f32ee3684bb8)) else (if i < 76 then 0xa732f6113024165dc0ab8a7332e113024165dc0a38a732f6113024165dc0a38a732d2113024165dc0a38b252f6083024165dc0a38a732f6113024165dc09b8a732f6113024165dc0938a732f6113024165dc08b8a732f6113024165dc0838a734b25eb024165dc4eb8a732f6113024165dc4eb8b2f2ae113024165dc4eb8a732f6113024165dc4db8a732f6113024165dc4d38a732f6113024165dc4cb8a732f6113024165dc4c38a732d2113024165dc4c38a732f6113024165dc48b8a732f61130252c2904bb8a732f61138d4162ec4bb8 else (if i < 77 then 0xa732f61130252c4345238a732f6113024165dc51b8a732f6113024165dc5138a732f6113024165dc50b8a732f6113024165dc5038a732f6113024165dc32b8a732f6113024165dc3238a732f6113024165dc31b8a732f6113024165dc5b38a732f6113024165dc2b38a732f6113024165dc0538a732f6113024165dc0638a732f6183024165dc07b8a732f6113024165dc07b8b2f2ae113024165dc07b8a732f60cb024165dc07b8a732f6113024165dc0738a732f6113024165dc06b8a732f6113024165dc05b8b212f6113024165dc0ab8 else 0xa732f6113024165dc54b8a732f6113024165dc5438a732f6113024165dc53b8a732f6113024165dc5338a732f6113024165dc52b8a732f6113bc604a585238a732f611352604a5852380014e65ec22604a585230a732f651c22604a585238a732f61130256ca585238a732f61130252c95c5238a732f61138d60482c5238a732f61130252c82c5238a732f6113f36045dc5238a732f61130252c5dc5238a732f6113024165dc5238a732f6113023b25dc5238a732f6113023945dc5238a732f61130241651c5238a732f6113024164e85238))) else (if i < 81 then (if i < 79 then 0x14e6013024165dc27b10014e65eb0241649076b10014e65eaaa4165dc57b10014e65eb024765dc72b10014e65ec227e6ef06d310016769ccbd8445dc6d310014e65ec222ee4bc6d310014e65ebf32ee4346d310014e6113023c65dc36b1a732f6113024165dc0c38a732f6113024165dc2ab8a732f6113024165dc1038a732f6113024165dc55b8a732f6113024165dc34b8a732f61130241665c3438a732f6113024165dc3438a732f6113024165443438a732f6113024165dc33b8a732f6113024165dc3338a732f6113024165dc5538 else (if i < 80 then 0x16225eaee4165dc86b10014e68e2da4165dc86b10015de5eb023ee5dc86b10014e6833023c65dc86b10015965eb0241659086b10014e677b0241654486b10014e65eb024165dc83310015465eb024165dc82b10014e6113024165dc82310014e66bb024165dc81310014e65eb314165dc7cb10012f6113024165901ab10012f6113024165dc2a310012f6112ee4165dc0eb10012f61130243c5dc18b10014e65ec22604a5829310014e65ec2271a82c29310014e65ec227e65dc29310014e65eb024165dc28b10014e6113024165dc2831 else 0x12f61ab024165dc20b10012f6113154165dc1e310014e65ec2260482c9e310014e65ec224ae82c9e310014e65ec224ee82c9d310014e65ec596a4c0892310014e65ec594ae82c92310014e6983024165dc8eb10012f6113024165dc8e3100164a5eb024165dc89b10014e65eb024165dc87310014e65ebbc6a4c0886b10014e65ebbc4ae82c86b10014e65eb524ae5dc86b10014e6973024165dc86b10016425eb024165dc86b10014e65eb024165dc86b10014965eb024165dc86b10014e65a3024165dc86b100165e55b024165dc86b1)) else (if i < 82 then 0x12f61138d4162ec25310012f6113524ae5dc25310014b25eb024165dc25310014ba113024165dc25310012f6113024165dc25310012d2113024165dc25310012f60cb024165dc25310014c2013024165dc2531001472112da4165dc25310012f64e2aa4165dc253100141a113023c65dc25310012f63db023685dc25310013be1130241654425310012f62cb0241649025310012f5de30241643425310012f5a93022ee43425310012f52ba0b2ee43425310012f6113f32ee36825310012f6113024165dc21b1001342113024165dc2131 else (if i < 83 then 0x14e65ec6c844fccbbb10014e65ec2260482cbb310014e65ec2260482cbab10014e65ec2260482cba310014e65ec2260482cb9b10014e65ec2260482cb9310015965ec226a4c08b2310015965ec224ae82cb2310014e677c226a4c08a8b10014e677c224ae82ca8b10014e65ec226a4c08a4b10014e65ec2260482ca4b10014e65ec226dac08a3b10012f61130252c29025310012f6113bc6a4c082531001089de30241625c2531001089a93022ee25c25310010892ba0b2ee25c2531000c090597721a25c25310012f6113bc4ae82c2531 else 0x164a5ec104ae82cbbb10014e6984024ae82cbbb10015725ec224a082cbbb10014e67242249882cbbb10014e65ec4b48282cbbb10014e65ec227dc82cbbb10014e65ec227cc82cbbb10014e65ec227b882cbbb10014e65ec227b282cbbb10014e65ec22604828bbb10014e65ec22604824bbb10014e65ec22604820bbb10014e65ec2260481cbbb10015de5ec224ae7dcbbb10014e6834224ae78cbbb10014e65ec2260476cbbb10014e65ec22604730bbb10014e65ec224ae730bbb10014e65ec22512728bbb10014e65ec7b4ae6d0bbb1)))) else (if i < 90 then (if i < 87 then (if i < 85 then 0x14961140260482cbbb10012ae0840260482cbbb10014e65ec2260282cbbb10014e65ec2260082cbbb10014e65ec225fe82cbbb10014e65ec225fc82cbbb10014e65ec225fa82cbbb10014e65ec225a282cbbb10014e65ec2258882cbbb10014e65ec9c53c82cbbb10014e68e4224ce82cbbb10016225ec224ba82cbbb10014e6964bd4ae82cbbb10014e6974224ae82cbbb10016425ec224ae82cbbb10014e65ec224ae82cbbb10014965ec224ae82cbbb10014e65a4224ae82cbbb100165e55c224ae82cbbb10014e65ec194ae82cbbb1 else (if i < 86 then 0x14e655c1960482cbbb10012f655c1960482cbbb100000255c1960482cbba90012ae1141960482cbbb100164a9741060482cbbb10016425ec1060482cbbb10014b25ec1060482cbbb100164a5a41060482cbbb10014e65a41060482cbbb10012f65a41060482cbbb10000025a41060482cbba90012d21141060482cbbb10012f61140560482cbbb10016429840260482cbbb10014e69740260482cbbb10014e69640260482cbbb10014e692c0260482cbbb10014c292c0260482cbbb100000292c0260482cbba90014965ec0260482cbbb1 else 0x14da5ec2260482cbbb10014965ec2260482cbbb10014e65e42260482cbbb10014e65dc2260482cbbb10014e65d42260482cbbb100165e5a42260482cbbb10016425a42260482cbbb10014e65a42260482cbbb100164255c2260482cbbb10014ba55c2260482cbbb10014e61bc2260482cbbb10014e65ec2160482cbbb10014e65ec2060482cbbb10014e65ec1f60482cbbb10014e69841960482cbbb10014e69741960482cbbb100164a5ec1960482cbbb10016425ec1960482cbbb10014e65ec1960482cbbb100165e55c1960482cbbb1)) else (if i < 88 then 0x164a9742260482cbbb10014e69742260482cbbb100165e9642260482cbbb100165e92c2260482cbbb10014ba92c2260482cbbb10014e68bc2260482cbbb10014e680c2260482cbbb10014e67542260482cbbb10014e66c42260482cbbb10014e665c2260482cbbb10014e65cc2260482cbbb10016425ec2260482cbbb10016165ec2260482cbbb10015d25ec2260482cbbb100158a5ec2260482cbbb100154a5ec2260482cbbb100151e5ec2260482cbbb10014d65ec2260482cbbb10014e25ec2260482cbbb10014de5ec2260482cbbb1 else (if i < 89 then 0x164a9cd2e60482cbbb1000002cbd2c60482cbba900165e9cd2c60482cbbb1001642984bd60482cbbb100164a974bd60482cbbb100165e964bd60482cbbb10014e6964bd60482cbbb100164a92cbd60482cbbb10014b292cbd60482cbbb10014e6694bd60482cbbb10014e6984b460482cbbb10014e6964b460482cbbb100165e964ab60482cbbb10014e65ec9760482cbbb10014e65ec7660482cbbb10014e65ec5460482cbbb10014e65ec3d60482cbbb10014e65ec3060482cbbb10014e65ec1e60482cbbb10016429842260482cbbb1 else 0x14e68e4226a4b68bbb10014e65ec226a4b10bbb10014e65ec22702b08bbb10014e65ec9c6a4aa8bbb10014e65ec22604a44bbb10014e65ec22604a20bbb10014e65ec226049f8bbb10014e65ec226049ecbbb10014e65ec2251095cbbb10014e65ec22604818bbb10014e65ec22604814bbb10014e65ec2271082cbbb10014e65ec2270082cbbb10014e65ec226ec82cbbb10014e65ec226e682cbbb10014e65ec225f882cbbb100165ec953060482cbbb1000002c853060482cbba90016429cd3060482cbbb1000002c952e60482cbba9))) else (if i < 93 then (if i < 91 then 0x14e65ec22756c08bbb10014e65ec22750c08bbb10014e65ec7b728c08bbb10014e6834226c4c08bbb10015de5ec226b0c08bbb10014e6964bd6a4c08bbb10014e6974226a4c08bbb10016425ec226a4c08bbb10014e65ec226a4c08bbb10014965ec226a4c08bbb10014e65a4226a4c08bbb100165e55c226a4c08bbb10014e65ec196a4c08bbb100164a5ec106a4c08bbb10014e6984026a4c08bbb10015b65ec22696c08bbb10014e67cc2268ec08bbb10014e65ec6566ec08bbb10014e65ec227d8c08bbb10016225ec226a4bb8bbb1 else (if i < 92 then 0x14e65ec226049a505b10014e65ec224ec95d05b10015de5ec22778c08fbb10014e683422778c08f1b10014e65ec22778c08edb10014e65ec227aac08ecb10014e6113024165443eb10014e65eb023685dc67310014e6112da4165dc2eb10014e6113024525dc3c310012f61130241662c12b10014e65ec7b778c08da310014e65eb024166ac63310014e65ec2271ad485db10016769ccbd84482c5db10014e65ec224166fc5db10014e65eb8d4164345db10014e65ec2260482cb8b10014e65ec22700d48bbb10014e65ec227a8c08bbb1 else 0x165e55c22778c0905b10014e65ec19778c0905b100164a5ec10778c0905b10014e698402778c0905b10015fe5ec22768c0905b10014e68842275ec0905b10014e65ec8773ac0905b10014e65ec2270cc0905b10014e65ec226d8c0905b10014e65ec22686c0905b10014e65ec22680c0905b10014e65ec597f4c0905b10016225ec22778bb905b10014e68e422778b6905b10014e65ec22778b4505b10014e65ec227ceb3d05b10014e65ec9c778aa905b10014e65ec22604a3d05b10014e65ec226049d905b10014e65ec226049b105b1)) else (if i < 94 then 0x14e5a93022ee4344bb10014e52ba0b2ee4344bb10014e6113f32ee3684bb10014e6113024165dc4831001532113024165dc47b10014e65eb024165dc47310014e61e3024165dc46310014e6113204165dc43310014e65ec22778d492bb10012f6113023ee5dc14b10014e65ec227ccef105b10014e65ec8e844e3505b10014e677c22794c0905b10015965ec22782c0905b10014e6964bd778c0905b10014e697422778c0905b10016425ec22778c0905b10014e65ec22778c0905b10014965ec22778c0905b10014e65a422778c0905b1 else (if i < 95 then 0x165e113024165dc4eb10014e6113024165dc4c310014e61130252c2904bb10014e6113bc6a4c084bb10014e6113bc4ae82c4bb10014e61138d4162ec4bb10014e6113524ae5dc4bb10014e6963024165dc4bb1001642113024165dc4bb10014e6113024165dc4bb1001496113024165dc4bb10014e60cb024165dc4bb100164a083024165dc4bb1001622112ee4165dc4bb10014e64e2aa4165dc4bb10015de113023ee5dc4bb10014e63db023685dc4bb1001596113024165904bb10014e62cb024164904bb10014e5de3024164344bb1 else 0x2c853060482cbbaa000002c952e60482cbbaa000002cbd2c60482cbbaa00000255c1960482cbbaa0000025a41060482cbbaa00000292c0260482cbbaa0014e61130241665c34310016769ccbd844c0852310014e65ec22604ad852310014e65ec2252c95c52310014e65eb0252c43452310014e65ec227a8ef181310014e65ec226d8d4981310012ae113024165dc07b10014e65eca3844c094b310012f6113024165dc0ab10012f6083024165dc0a31)))))))
private def st6 (i : Nat) : Nat := unpack st6Packed 84 20 i
private def adj6Packed (i : Nat) : Nat := (if i < 4 then (if i < 2 then (if i < 1 then 0x14144000000104404298410150d10aa412820dc3c20020000c01c21411020800834c40032c20421400421000c000d0412070021450022800020c6180 else 0x304110714100604014614004000c08104104d0c00000816400440c500c0430031013032800410001440101c32000400451c00cd08a0401c1180340) else (if i < 3 then 0xc16860001c60000030800080010020852461454c10811400c30091070000040410000010810040473072c0100500000003081047040045040085000 else 0x420071411000c220000010200300808300e04800200304508500d0810850c000500600108404014000000124e0801040020400810400c10cc4c1080)) else (if i < 6 then (if i < 5 then 0x90000822c444504e04114c10000004100a64700204210308114010110200000000304008204b04120000009b0011c009b1c004e000041085040090 else 0x10c02080420420810805c20010570011c034a1c114714504004b05c0020400430ce00d0000c00400051001810430810803c0002000045380002040) else (if i < 7 then 0x1010490832c00861000c300e6cc2413453420810010400002402053411400001830010450040001040000451cd2010000040c10430800010400c9044 else (if i < 8 then 0x10830c230004014001f2860040010c130508018504100a0020840045c900300300b0010891932851c60810891420021010820000020c010100000a else 0x0))))
private def adj6 (i : Nat) : Nat := unpack adj6Packed 6 80 i
private def loc6Packed (i : Nat) : Nat := (if i < 18 then (if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then 0x18c04c6804a32280045dc48558005720009a5a816a11a039f06b1e167cf3b000949555f69c96d8a27620000015a8003088086208e462d78f1c760ee7649d7ae9e70010c00038f06603ed18006ff915d8800000000d7000000f0800000000001848e4000a980059d4aa2ea7e000 else 0x1c966ebec0036c9cecc39780025b09d707062d00000000000000097cd197400063079ee09391f2f791e000000ec800144ee9756d809f31b2180046258974000000ebda40eb001bb96ee77b14423b91191d4e800043d9cc002c251e00000078b650cca54000000012cc00000) else (if i < 3 then 0x3fc0013842b0006679eeddb674b632a6c0013410bc00000000002dbb6e7ac00765001be42b89078d3299b4dfbd2003a50003160000000082c7e3200000fa0000d022ae7b405809100000329a3d0000d86a464191b50000000000003cb9e001356c1761000001abd9e0008a73f000 else 0x8e94ff59dfdc853d40272891c00000442290cd19fc97001c15078000000035fe290006d80000082e4e43180079b859657129e6c7273eae18680d8d80044c4b5c771714a1b352e93b3025d207354258980024e001759d0800b7fa0657d46000f2c005c00002900055f828000003e2)) else (if i < 6 then (if i < 5 then 0xd0368e2e1710be49c221420000016e878e232a764c3423ab680031412400766bbd6eb09403001320e528c001d3b8569a000e980000000000235346000000aa5375d20000000047872c003be001ac38c000001326ead10001d3791800001b240005f2fce6e4c8009eece400000 else 0xb6c000fb551000c2c007022fe0021080067c003adbef001bf5c841d2ba8d70170d0740f9ed000220ad13f000001dc77c16d07800035dc2c9dd788c4374c6000001950a1a3c0010f001b9091143000214005c6a4bdf17c800000454000001807ee76b73ee0864c7b5470800308800) else (if i < 7 then 0x70a000048586e2f28c3c5c0f07d432901c82000a9d7c61f2f4002c2000eb79bb0ed120000047e2b3820fbc45e12451a48d5001a85a90a70000000000084ed5b8b000de400000000a86000d9d7099e0038d0fc0004480000076c00357d5d001ae23c800e41234734d8001d5a89011 else (if i < 8 then 0xdaed880063e000000000430017cc000007489e06fa7dcb2001be3b3a884d564000000ebb47000cf600328ec857474eb18006d6af40002974e001712cf88e002848002c8000000004c2e5800268b4e424000fbc511340032229a00224ca0001af774a110009747385a0001d876cb4 else 0x4da00168800edd598960000002a000117589c1c005c32064d8af2bf1a200054e0de4e001068008ec0009780058b4bc0a86744e000fa4a60009ad4e8000deda40056e65a8d80053d7e4002ab3430000015ba018b60b800000000000000000000014233a416c00d5dd100139400000)))) else (if i < 13 then (if i < 11 then (if i < 10 then 0xbd0674000007316b53e3fb5ff95c003167a0002942c0001ab4001576dc003a6000a94000a900024f913a10000000027100019f3144921ecfb7a9c1deb0e40c8dc3c1d400000068700cde2ee664000880000003a807b01a7a45a001538836a6002b5800a30000000000006d40047d else 0x8aa000df80000136800160e680017e928d6ad38068003e5b2f559b478904a5ac5600000186800d441054f925a6a3e7334ea0003c8cd47a5f6001bad675c17300051c00004f24000813500006d36525a239b050019c80000076eff8d562d000788004570017f09502532423000000) else (if i < 12 then 0xd39cafa8262b80054f12a003b3d74000f6c003514840011228800064e83ba2435c5400482000000b2800bcc000000891946df07800ac2e729f745b44a90c88000013e9f49ffe632e5dd9c74209e6cc9210003a563f516b6b18001efa592d90213a729766348a3ee6abc00000 else 0xa851fc6cf54d4c003027328460024a8c4a07934250003aeb99c380000070b75800c980005a6e20000010e0000000014c00029ef7cf4cc0128fd86928f000ab951cd9a8a003958543614a733d83aa90fa5f4b85f8001161df4c8001fa800a97b34006b400000000000000f8d41bb0)) else (if i < 15 then (if i < 14 then 0xe2048bb0000003457c80000014a0000000056585c00000741bee3e1f085c79171ca10180000039843a0000015f186c31b6a7ff60b2c78400000946f480a0030005272380000164981559000003975db001dbda200050b6140039d642bc80000016d43c00271714b2400000 else 0x2877bcff400000882000ed0000fcbd115800000e54004a50008ec000008ee2c836ec381c101010fd0017b9fc75a78a0018a00000000080000e200000052600065c003aa000506700002664f85580000044c001bd00000000000bfcfe82f1e8b13bc10d8a0e88002c61e3) else (if i < 16 then 0x6d1d2c005dfe52000002e713e003bc8bdc723dc94a978c6c496bc4400124319af0ad09240040c000a180032c3e188066d31001b3fbb00000041cb652e5633ed3b1cc5400000029c830001818000000029215b44278000000b269b8000000000000000020d9a9ec76ca2f74a59000 else (if i < 17 then 0x5c21580072a6be001bcbcc76a0026ba730000025132f0d4ded268001a1004000000580af8180000e00000301cf05c0cb6db000cd6fce7f0018db71ace40182ac38008b0001110000000000002d000003b699c9280000044f0000000000090f23000000a22fe5b5000084bcc0f800 else 0xcca3728280e000bae5b000002ca00b0015d61400020400000617000000f235d000003230700360017b1dd1738dc77ecab0dae80000041d2a1141d60015dc98000867580005da984002a9491000a5acd45ac45b04000000015277400000000000576000d36ebaadd360030a8f0))))) else (if i < 27 then (if i < 22 then (if i < 20 then (if i < 19 then 0x7199bbe508a93ce6800046000df45eccb5bc298001b000000081000002d70006c73b228d0eab60028ceb9304003b12c1000002f924aaf458c0073bca4001664c4e74000101a8000002a80001c1c201eaa50c4000fcecc74749f18800640001a1496001a615400048312397aa1 else 0x5e000ac07a8334c8000000010a4a38002aa0e400215000f700071d0000036100000022dfe41a000000006960016714a0007120006700095c001d5800000002bf22eb7a6178daf10620003bdaa90102ae418daaf66ec6ca7246ea45e2628730c80063b0000026382a70d40000000) else (if i < 21 then 0x961a402e800b68003b5701682b58499cf000002e800080c27363d200a3b02f60005531a1c6edc000b8d9c0000014eb058000016932e239000030007110005c8450000017d754981c599c6261500015f40e08200057f89e2f001d0dcb80000000335ce43f4d980025a9fa0016e74f else 0xe44002f380034a00256347000e7e6e3f3ac4394dd000000d2912a2f8e40000062a00000212ccc4b20000000017e00000000afe00268ad44d57342363a000000f60f60000011f14b000d2cee0748f04b80000000000199800ab8e6a9a000978704003b4001b9a30d7b0000033e515)) else (if i < 24 then (if i < 23 then 0x4add1c0e800c280022f800a198157be500014200000015e4f442138eb3044e8800288d90000000005000032e70374e10000136cc000000000824003939626880024763f86c0011aa0400000000000491240000d0518000002ef680000000d21c54f00091031c000008b200221db9 else 0x6df1d49a1c0c33c94cc0000013cb802380015a4002332f20000000046400244d0db4a000932d87cc0a15c8008800024f000a9bce000000ec793c562efabc001480000019ce430e8d0400000415cb01851830c001784b7800000000e2d3c00000198df0ba89700000000067d72e4b) else (if i < 25 then 0x4198fd930000b38c800553b42000000000019bc0028e623cf8220007d8e32bccbbac8002385b51bc0000028ad385c5b6800c7a0034896b0f6002dc49f00042c00000b1c000005a90714868d800b5fd20000c200000000539487974006868c1a2e91e9419695d952071babba25000 else (if i < 26 then 0x6145f3518000000021c000d4eee3128bb75095379800499bb49e0b51013e400000e48d6000223cbe6a6c46e7000008002d50015047a452c42ae0f890c0017d20e0e2c3d72dff9840010fc0000504f4ae8f800000001042672cc0006d800772b0e5f94e0011b000408b0044400740 else 0xc38000d21bc79c0033828b10dbc65480083f33a89800298003830000005cc000dc000000004de8552ac0058f9df78c003829f08140027400005faa8000000016900000000082b7d001304002ac000001ea0000019d3754d30000ef93000c000016580081a001aa801000a6de0000)))) else (if i < 31 then (if i < 29 then (if i < 28 then 0x848740fee62000000000fad186c800064eea000003ee16ef74000000017940071f13cb9342800d6e65000000000efc00167da5a0f8ccf1049d415af78dfe43bac42cea4e9770dc9000d640062b3cc001f8800a3400202e637e80000027f0016ec0034cb952876ff579879a576b27 else 0xd8a440f8002a44cd42c9173c80011ecf00046bb23aa8bb1d500000000000a60001eb65a0017e0001e5000c9227214b62c55153d35660037b8000b600000000ebf5c4bc4ddd77d7271800b160480050a4f6fa8004db0600d4005a6b9ea0000000000d80533c30016a00031a) else (if i < 30 then 0x3040000084c000c74715be7780054713526d3300034f41039c816c3dde6a0e100000069e23be3d18004fee1d4515b660a02000000003d581d8c8000013aea70003599d400610236a88004cbb0384c000000eb0d8c8000000c8dde20a0a484f9e41b000000006559e9da691656 else 0x1dac00291555cb558000b560010f800ab5dec006e5001b546651d3876c0006f40010d4006d6b3e000000be000000ec42dd8a0001bc1e0006b6df00086811c00000430001bbb1093a0011d2500c000000277001a5c6b9690016f3ba66cc0c000000007d17e80061d0006ee1db5c)) else (if i < 33 then (if i < 32 then 0x4e42591a0009359a0000001fe8de8b258a6756026bc9954720f6800000bf8006a8d8c0026b23f0004374217d67a00000000bc00000000000000071b8b0000038647b000682e75900009789fa93257384bd09d000002830003b600345000306dd3563d7759248003d167694c4c800 else 0x2c0035915151a7f000635167b780000018b71274920c3f8258380023b1988ff7a262a055e000a6d02d762ebd102b5b38001920038f53800178b5f00048d20c0037e001211fb800d2a000006fe000b4c00000df9ad858800b8a220825fb00008400000626a6a0859559a06400000) else (if i < 34 then 0x6560018337a0016b00054c0006bc000003720016d736000dd8000000000009dcba04c001b8000bbb11b256fa524040cd80096edc80071ce580022a6ce0002a8000fe0000027b206e285eddece828a13132b5aad8fad55800cf4bd4000000018d000000e436c992f53c7860000189 else (if i < 35 then 0x7e0000000004c0003a480022d23c0046d733417073280aaf5656b188de0010e84b00134843a4bc02000000088960006b6f60003183fe99d3a1ba2853b6bc3d56cb9121400000000d48000ae0003420031c000ed00281fc0fd3e0018f48b862c12bc5ff001008b080000000000485 else 0x34f0005bca64cf000000001f3800d24be0005974a4000001eedea003878007b269b3693269f7b400137dd919c0073f9dc0031380079f92537800dde56800000930e00004f0000002f200062e74800000e08000007335640000052a8a60028580057600000000df7a346d31d))))))
private def loc6 (i : Nat) : Nat := unpack loc6Packed 11 80 i
private def st7Packed (i : Nat) : Nat := (if i < 26 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then 0xb114e65ec2260482cbb81d800029ccbd844c090597703ae00053997b0898120b2ee0c5c53997b0898120b2ee12818c00014e65ec2260482cbb84f714e6984bd844c090597709f000053997b0898120b2ee3b5c53997b166113024165dc76c00014e65ec2260482cbb8af714e65ec9c844c090597715f000053997b0898120b2ee395c53997b0898120b2ee43472c0a732f6113bc60482cbb8da814e65ec226a4c09059771b5000053997b0898120b2ee369c53997b1b2113024165dc6d40a732f6113024ae82cbb8da814e65ec2260482cbb90d1b5000053997b0898120b2ee1b5c539a0d2f6113024165dc36c0 else (if i < 2 then 0xa732f6113025b482cbb90d814e65ec22604aa90597721b029ccbd844c094b20b2ee436053997b089812574165dc86c0a732f61130247682cbb90d814e65ec2260482cfb97721b029ccbd844c09059e32ee436053997b0898120b3685dc86c0a732f6113024166acbb90d814e65ec2260482cbb96421b029ccbd844c09059772a2436053997b0898120b2ee49086c00014e65ec2260482cbb905714e65ec2260482cbb90d20b000053997b0898120b2ee409c53997b0898120b2ee43481400014e65ec2260482cbb8f9714e65ec2260482cbb90d1f302b2d3997b0898120b2ee0d60000a732f6113024165dc1ab8 else 0xb2f4e65ec2260482cbb90d8164a9ccbd844c090597721b02c453997b0898120b2ee4360577a732f6113024165dc86c0acb4e65ec2260482cbb90d815469ccbd844c090597721b000053997b0898120b2ee435c539a612f6113024165dc86c0a734725ec2260482cbb90d814e6834bd844c090597721b029ccef97b0898120b2ee43605399af2f6113024165dc86c0a732f655c2260482cbb90d814e65ec9c844c090597721b029ccbd8f70898120b2ee436053997b166113024165dc86c0a732f61141060482cbb90d814e65ec22804c090597721b029ccbd844fcd8120b2ee436053997b089812ee4165dc86c0)) else (if i < 4 then 0xa732f6113024165dc25041800029ccbd844c0905977078e29ccbd844c09059770940f20000a732f6113024165dc9d38a732f6113024ae82cbb93a800029ccbd844c090597725ee29ccbd844fcd8120b2ee4be053997b089de3024165dc9240a732f61135260482cbb924800029ccbd844c0905977248e29ccbd844fe98120b2ee492053997b089812574165dc92400014e65ec2260482cbb91d714e65ec22804c090597723b000053997b0898120b2ee44dc53997b08a083024165dc89c0a732f6113bc60482cbb90d814e65ec2271ac090597721b029ccbd844d498120b2ee436053997b08998b024165dc86c0 else (if i < 5 then 0xa732f61140260482cbb84a814e65ec227e6c0905977095029ccbd844c097720b2ee12a053997b089812da4165dc2540a732f61130255482cbb84a814e65ec22604a5905977095029ccbd844c092ba0b2ee12a053997b0898121e4165dc2540a732f6113024167dcbb84a814e65ec2260482cf1977095029ccbd844c09059b42ee12a053997b0898120b3165dc2540a732f6113024165dcb204a814e65ec2260482cbb951095029ccbd844c090597724812a053997b0898120b2ee4342540a732f6113024165dc6d04a800029ccbd844c0905977084e29ccbd844c090597709410a0000a732f6113024165dc20b8 else 0xa732f61138d60482cbb84a814e65ec226a4c0905977095029ccbd844c558120b2ee12a0597a732f6113024165dc2540b254e65ec2260482cbb84a816229ccbd844c090597709502bbd3997b0898120b2ee12a0565a732f6113024165dc25400014e65ec2260482cbb84a714e6984bd844c0905977095029cd1c97b0898120b2ee12a0539a0d2f6113024165dc2540a733be5ec2260482cbb84a814e6684bd844c0905977095029ccbd9570898120b2ee12a053997b272113024165dc2540a732f63dc2260482cbb84a814e65ec59844c0905977095029ccbd86b0898120b2ee12a053997b08a083024165dc2540))) else (if i < 9 then (if i < 7 then 0xa732f6113024ae82cda177800029ccbd844c09059ab2eee00053997b0898120b32e5ddc000a732f61130241662cbbb8a732f6113c160482cbb964814e65ec22778c09059772c9029ccbd844d498120b2ee5920000a732f6113024165dcb238a732f6113024ae82cbb964814e65ec22794c09059772a3029ccbd844ef18120b2ee546053997b089a93024165dca8c00014e65ec2260482cbb951714e65ec2260495d059772a3029ccbd844d498120b2ee51e0000a732f6113024165dca3b8a732f6113024165dc5204a814e65ec2260482cbb897095029ccbd844c090597717612a053997b089de3024165dc2540 else (if i < 8 then 0xa732f6113bc60482cfb977814e65ec226b0c09059f72ef029ccbd844d498120b3ee5de0000a732f6113024167dcbbb8a732f6113024ae82cfb977814e65ec22778c09059e32ef029ccbd844d898120b3c65de053997b089a930241678cbbc00014e65ec2260482cf1977714e65ec2260495d059e32ef029ccbd844ef18120b3b25de0000a732f611302416764bbb80014e65ec2260482ce5177714e65ec2260495d059ca2ef029ccbd844e358120b37e5de0000a732f6113024166fcbbb8a732f6113bc60482cda177814e65ec22728c09059b42ef029ccbd844d498120b3685de0000a732f6113024166d0bbb8 else 0xa732f62cc2260495d05977814e65ec4b844c092ba0b2ef029ccbd845041812574165de053997b08a013024ae82cbbc0a732f6113f360495d05977814e65ec22604bb92ba0b2ef029ccbd844c096d2574165de053997b089812aa4ae82cbbc0a732f61130252c95d05977814e65ec22604a252ba0b2ef029ccbd844c093ba574165de0000a732f6113024a082cbbb8a732f6113024ae94105977800029ccbd844c092620b2eee29ccbd844c092ba4c4165de0000a732f61130248282cbbb8a732f6113024ae90505977800029ccbd844c091da0b2eee00053997b089812294165ddc000a732f61130243c82cbbb8)) else (if i < 11 then (if i < 10 then 0x14e65ec2260497505977714e65ec22604bb92ea0b2ef029ccbd844ef1812574165de053997b089c6b024ae82cbbc0a732f61135260495d059778165e9ccbd844c092ba0b2ef02c953997b089812574165de0588a732f6113024ae82cbbc0aef4e65ec2260495d05977815969ccbd844c092ba0b2ef02ae53997b089812574165de0000a732f6113024ae82cbbb8a734c25ec2260495d05977814e68e4bd844c092ba0b2ef029cd0697b089812574165de05399df2f6113024ae82cbbc0a733925ec2260495d05977814e65ecab844c092ba0b2ef029ccbd939089812574165de053997b1ee113024ae82cbbc0 else 0xa732f611352604b6905977800029ccbd844c096d20b2eee29ccbd844ef1812cf4165de0000a732f61130259e82cbbb8a732f611352604b0905977800029ccbd844c096120b2eee00053997b089812b64165ddc53997b089de30255482cbbc0a732f611352604aa905977800029ccbd844c095520b2eee00053997b0898129e4165ddc53997b089812aa53c82cbbc0a732f6113bc604a5905977814e65ec226a4c094b20b2ef000053997b089812964165ddc53997b089812b652c82cbbc00014e65ec22604a2505977700029ccbd844c093ba0b2eee00053997b089812674165ddc53997b089812da4ce82cbbc0) else (if i < 12 then 0x14e65eca3844c0905977700029ccbd9390898120b2eee00053997b23a113024165ddc000a732f643c2260482cbbb80014e65ec7b844c0905977700029ccbd8d90898120b2eee00053997b196113024165ddc000a732f62cc2260482cbbb80014e65ec4b844c0905977700029ccbd8790898120b2eee00053997b0d6113024165ddc000a732f61141060482cbbb80014e65ec22804c0905977700029ccbd844fe98120b2eee00053997b089f9b024165ddc000a732f6113e760482cbbb8a732f6113bc604bb905977814e65ec226a4c097720b2ef000053997b089812ee4165ddc53997b089de3025b482cbbc0 else 0x164a9ccbd844c090597770002c453997b0898120b2eee00057fa732f6113024165ddc000aef4e65ec2260482cbbb80015b69ccbd844c090597770002b2d3997b0898120b2eee00055ca732f6113024165ddc000aa34e65ec2260482cbbb80015329ccbd844c0905977700000053997b0898120b2eec000539a612f6113024165ddc000a734725ec2260482cbbb80014e6884bd844c0905977700029cd0697b0898120b2eee0005399f32f6113024165ddc000a733be5ec2260482cbbb80014e6724bd844c0905977700029ccd797b0898120b2eee0005399a12f6113024165ddc000a732f655c2260482cbbb8)))) else (if i < 19 then (if i < 16 then (if i < 14 then 0xa733e65ec226a4c0905977814e677cbd844d498120b2ef029ccbd957089a93024165de053997b2721135260482cbbc0a732f63dc226a4c0905977814e65ec65844d498120b2ef029ccbd8b3089a93024165de053997b08a0835260482cbbc0a732f6114026a4c0905977814e65ec227e6d498120b2ef029ccbd844d49a5b024165de0000a732f61134b60482cbbb8a732f61135268ec0905977800029ccbd844d1d8120b2eee29ccbd844d499bb024165de0000a732f61133760482cbbb80014e65ec22662c0905977700029ccbd844c818120b2eee00053997b0898ab024165ddc000b2f4e65ec2260482cbbb8 else (if i < 15 then 0xa732f6113bc71ac0905977800029ccbd844e358120b2eee00053997b089c0b024165ddc000a732f61136d60482cbbb80014e65ec226c4c0905977700029ccbd844d618120b2eee29ccbd844ef1a93024165de053997b089c6b5260482cbbc0a732f6113816a4c0905977814e65ec226dad498120b2ef02cbd3997b089a93024165de0592a732f61135260482cbbc0b114e65ec226a4c0905977815de9ccbd844d498120b2ef02b6d3997b089a93024165de0565a732f61135260482cbbc00014e65ec226a4c0905977714e6984bd844d498120b2ef029cd1c97b089a93024165de0539a0d2f61135260482cbbc0 else 0xa734725ec22778c0905977814e6884bd844ef18120b2ef029cd0697b089de3024165de05399df2f6113bc60482cbbc0a732f655c22778c0905977814e65ec9c844ef18120b2ef029ccbd90f089de3024165de053997b1ee113bc60482cbbc0a732f62cc22778c0905977814e65ec22820ef18120b2ef029ccbd845009de3024165de053997b089f9bbc60482cbbc0a732f6113e7778c0905977814e65ec22778ed18120b2ef000053997b089da3024165ddc53997b089de3af60482cbbc00014e65ec2275ec0905977714e65ec22778e758120b2ef000053997b089ceb024165ddc000a732f61139460482cbbb8)) else (if i < 17 then 0x14e65ec2260482cbb8c6714e65ec2260482cbb90d18d029ccbd844ef18120b2ee2ee053997b089a93024165dc5dc00014e65ec2260482cbb8bb714e65ec8e844c0905977177029ccbd844c092ba0b2ee2ee053997b0898120b2ee4345dc00014e65ec227aac0905977700029ccbd844f298120b2eee00053997b089e0b024165ddc53997b089eabbc60482cbbc0b2f4e65ec22778c09059778164a9ccbd844ef18120b2ef02c453997b089de3024165de057fa732f6113bc60482cbbc0aef4e65ec22778c0905977815969ccbd844ef18120b2ef000053997b089de3024165ddc539a612f6113bc60482cbbc0 else (if i < 18 then 0xa732f6113024165dc86897814e65ec2260482cbb8da12f029ccbd844c090597712e23e0000a732f6113024165dc47b8a732f6113024165dc4b88c800029ccbd844c0905977118e29ccbd844c090597712e21a0000a732f6113024165dc4338aef4e65ec2260482cbb829800029ccbd844c0905977052e00053997b0898120b2ee1f5c5399df2f6113024165dc3ec00014e65ec2260482cbb8ce714e65ec7b844c090597719d000053997b0898120b2ee175c539a392f6113024165dc2ec0a732f6113024165dc4b878800029ccbd844c09059770f0e00053997b0898120b2ee095c53997b0898120b2ee12812c0 else 0xa732f64e42260482cbb897814e65ec7b844c090597712f029ccbd8b30898120b2ee25e053997b0f2113024165dc4bc0a732f61141060482cbb897814e65ec22804c090597712f029ccbd844fcd8120b2ee25e053997b089812ee4165dc4bc0a732f6113025b482cbb897814e65ec22604aa90597712f029ccbd844c094b20b2ee25e053997b089812574165dc4bc0a732f61130245282cbb897814e65ec2260482cfb97712f029ccbd844c09059e32ee25e053997b0898120b3685dc4bc0a732f61130241665cbb897814e65ec2260482cbb96412f029ccbd844c09059772a225e053997b0898120b2ee4904bc0))) else (if i < 22 then (if i < 20 then 0x14e65ec2260482cbb89d714e65ecab844c090597713b029ccbd844c090597714825e053997b0898120b2ee2ec4bc0a732f6113bc60482cbb897814e65ec2271ac090597712f029ccbd844d498120b2ee25e053997b089903024165dc4bc0b2f4e65ec2260482cbb8978164a9ccbd844c090597712f02c453997b0898120b2ee25e0577a732f6113024165dc4bc0acb4e65ec2260482cbb897815329ccbd844c090597712f000053997b0898120b2ee25dc539a612f6113024165dc4bc0a734725ec2260482cbb897814e6834bd844c090597712f029ccef97b0898120b2ee25e053997b2ae113024165dc4bc0 else (if i < 21 then 0x14e65ec2271a82cbb8da720029ccbd84495d059771b4e40053997b089f9a0b2ee369c8000014e65ec227e65dc6d310014e65eb024165dc868da720029ccbd844c09059771b2e40053997b0898120b2ee359c800a732f6113024165dc36b9a732f6113024165dc4b868800029ccbd844c09059770d0e29ccbd844ef18120b2ee292053997b089a93024165dc52400014e65ec2260482cbb8a4714e65eca3844c0905977149029ccbd844c092ba0b2ee292053997b0898120b2ee4345240b2f4e65ec2260482cbb80f800029ccbd844c090597701ee2c953997b0898120b2ee0520000a732f6113024165dc0a38 else 0x14e65ec2260482cbb902720029ccbd60482cbb90d204e40053997b0898120b2ee3e5c800a732f58120b2ee4347cb90014e65ec2260482cbb835720029ccbd844c09059771eae40053997b0898120b2ee075c800a732f6113024165dc18b90012f6113024165dc25031720029ccbd844c09059770a4e40053997b0898120b2ee13dc800a732f6113024165dc76b90014e65ec2260482cbb8af720029ccbd844c09059771cae40053997ac090597721a395c800a732f6113024165dc71390014e65ec22778c09058da720029ccbd844d49811771b4e40053997b089f9b022ee369c800a732f61130252c5dc6d39)) else (if i < 24 then (if i < 23 then 0x14e65ec1060482cbb90d720029ccbd804c090597721ae40053997afcd8120b2ee435c800a732f5812ee4165dc86b90014e65eb025b482cbb90d720029ccbd604aa90597721ae40053997ac094b20b2ee435c800a732f5812574165dc86b90000029ccbd4ae82cbb90d620029ccbd84495d0597721ae40053997ac091da0b2ee435c800a732f58120b3ee5dc86b90014e65eb0241678cbb90d720029ccbd60482cda17721ae40053997ac09059ab2ee435c800a732f58120b2ee59086b90014e65eb024165dca890d720029ccbd60482cbb92421ae40053997b0898120b2ee415c800a732f58120b2ee43482b9 else 0x14e65ebbc60482cbb90d720029ccbd71ac090597721ae40053997ad498120b2ee435c800a732f598b024165dc86b900165e9ccbd60482cbb90d72002c953997ac090597721ae400588a732f58120b2ee435c800aef4e65eb024165dc86b90015969ccbd60482cbb90d72002a8d3997ac090597721ae400539a612f58120b2ee435c800a734725eb024165dc86b90014e6834bd60482cbb90d720029ccef97ac090597721ae4005399af2f58120b2ee435c800a732f655b024165dc86b90014e65ec9c60482cbb90d720029ccbd8f6c090597721ae40053997b1658120b2ee435c800a732f6113024165dc86b9) else (if i < 25 then 0x14e65ec2260482cbb83c720025ec2260482cbb84a078e40053997b0898120b2ee4e9c800a732f6112574165dc9d390014e65ec2260482cbb937720029ccbd844c090597725ee40053997b089de302416491c8000014e65ec5960482c92310014e65ec59844c0905924720029ccbd844d4981177248e40053997b1658120b2ee491c800a732f6112574165dc92390014e65ec2260482cbb923720029ccbd844c090597723ee40053997b0898120b2ee475c800a732f6113024165dc89b90000029ccbd778c090590d620029ccbd844ef18120b21ae400000a732f5a93022ee4358800a732f6113526045dc86b9 else 0x12f61130252c82cbb84a720025ec2260495d05977094e40053997b0892ba0b2ee129c8000012f6112574165dc25310012f61130243c82cbb84a720025ec2260482cfb977094e4004bd844c09059e32ee129c80097b0898120b3685dc25390012f61130241662cbb84a720025ec2260482cbb964094e4004bd844c09059772a2129c80097b0898120b2ee49025390014e65eb024165dc8684a72000004bd60482cbb90d094c4004bd844c090597721a129c80097b0898120b2ee36825390014e65ec2260482cbb842720025ec2260482cbb84a084e40053997b0898120b2ee105c80097b0898120b2ee12820b9))))) else (if i < 39 then (if i < 32 then (if i < 29 then (if i < 27 then 0x16225ec2260482cbb84a72002bbcbd844c0905977094e40056597b0898120b2ee129c800a732f6113024165dc25390014c25ec2260482cbb84a720028e4bd844c0905977094e40050697b0898120b2ee129c8009df2f6113024165dc25390013425ec2260482cbb84a720025ecab844c0905977094e4004bd9390898120b2ee129c80097b1ee113024165dc25390012f62cc2260482cbb84a720025ec35844c0905977094e4004bd8450418120b2ee129c80097b08a013024165dc25390012f6113f360482cbb84a720025ec22604bb905977094e4004bd844c096d20b2ee129c80097b089812aa4165dc2539 else (if i < 28 then 0x14e65ec224ae82cbb951720029ccbd844c09059772a0e40053997b089a93022ee51dc800a732f6113024165dca3b90014e65ec2260482cbb944720025ec2260482cbb8a4094e400539844c090597712e129c80097b0898120b2ee25c2539000002113024165dc4b84a620029ccbd844ef18120b094e40000097b089de302416129880097b0898120b2ee2ec25390014e65ec226a4c08bb84a72000004bd844d4981177094c4004bd844ef18120b2ee129c80097b089c6b024165dc25390012f61135260482cbb84a720025ec2262ac0905977094e40059797b0898120b2ee129c800b252f6113024165dc2539 else 0x14e65ec2260482ccb977720029ccbd844c090598b2eee40053997b0898120b2ee5c1c800a732f6113024165dcb7b90014e65ec2260482cbb96b720029ccbd844c09059772cee40053997b089de302416591c8000015965ec2260482cb2310015969ccbd844c0905964720029ccbd844d49811772c8e40056597b0898120b2ee591c800a732f6112574165dcb2390014e65ec2260482cbb963720029ccbd844c09059772b8e40053997b0898120b2ee559c800a732f6113bc60482ca8b90000029ccef844c0905951620029ccef97b0898120b2a2e40053997b089a93022ee545c800a733be113024165dca8b9)) else (if i < 30 then 0x29cd06844c08f1977620029cd0697b089811e32eee400539a0d0898120b3c65ddc800a732f61125741678cbbb90014e65ec2260482cf1177720029ccbd844c09059d92eee40053997b0898120b3ac5ddc800a732f611302416728bbb90014e65ec224ae82ce5177720029ccbd844c09059c72eee40053997b0898120b37e5ddc800a732f6113526046d0bbb90000029ccbd8f6c08da177620029ccbd8f7089811b42eee40053997b1ed8120b3685ddc800a732f6112574166d0bbb90014e65ec2260482cd9977720029ccbd844c09059af2eee40053997b0898120b3565ddc800a732f611302416680bbb9 else (if i < 31 then 0x14e65ec2260491505977720029ccbd844c0920a0b2eee40053997b0892ba414165ddc800a732f61130247682cbbb90014e65ec226048c105977720029ccbd844c0914a0b2eee40053997b0898121e4165ddc800a732f611302416810bbb90014e65ec2260482d01977720029ccbd844c09059ff2eee40053997b0898120b3f45ddc800a732f6113526047dcbbb9000002bbcbd844c08fb97762002bbd3997b089811f72eee40057797b0898120b3ee5ddc800a732f6112574167dcbbb90014e65ec2260482cfb177720029ccbd844c09059ef2eee40053997b0898120b3d05ddc800a732f61135260478cbbb9 else 0x15de9ccbd84495d0597772002b2d3997b0892ba0b2eee40055ca732f6112574165ddc800a734c25ec224ae82cbbb90014e68e4bd84495d05977720029cd0697b0892ba0b2eee4005399df2f6112574165ddc800a733925ec224ae82cbbb90014e65ecab84495d05977720029ccbd9390892ba0b2eee40053997b1ee112574165ddc800a732f62cc224ae82cbbb90014e65ec4b84495d05977720029ccbd8450412ba0b2eee40053997b08a012574165ddc800a732f6113f34ae82cbbb90014e65ec2260494105977720029ccbd84495d2820b2eee40053997b0898124c4165ddc800a732f61125749882cbbb9))) else (if i < 35 then (if i < 33 then 0x14e65ec22604a3905977720029ccbd844c0944a0b2eee40053997b0898127f4165ddc800a732f6113024ee82cbbb90014e65ec226049b505977720029ccbd844c0933a0b2eee40053997b0898125d4165ddc800a732f6113bc4ae82cbbb90014e65ec2271a95d05977720029ccbd844d492ba0b2eee40053997b089812574165ddc800a732f6112ee4ae82cbbb90014e65ec225b495d05977720029ccbd844aa92ba0b2eee40053997b0894b2574165ddc800a732f6112894ae82cbbb90014e65ec224ee95d0597772002cbd3997b0892ba0b2eee400592a732f6112574165ddc800b114e65ec224ae82cbbb9 else (if i < 34 then 0x14e68e422604b69059777200000539a390896d20b2eec400539a392f6112da4165ddc800a732f6113025b282cbbb90014e65ec22604b3d05977720029ccbd844c096620b2eee40053997b089812c24165ddc800a732f61130257e82cbbb90014e65ec22604ad905977720029ccbd938c095520b2eee400000a732f64e2aa4165dd8800a732f64e42255482cbbb90014e65ec22604aa505977720029ccbd844c0952a0b2eee40053997b0898129e4165ddc800a732f61130252a82cbbb90014e65ec22604a5105977720029ccbd844c0949a0b2eee40053997b089812924165ddc800a732f61130252082cbbb9 else 0x14e65ec22802c0905977720029ccbd844fe98120b2eee40053997b089f93024165ddc800a732f6113f160482cbbb90014e65ec227e0c0905977720029ccbd844fbd8120b2eee40053997b089f6b024165ddc800a732f6113eb60482cbbb90014e65ec227cec0905977720029ccbd844f758120b2eee40053997b089812fb4165ddc800a732f6113025f482cbbb90014e65ec22604bd905977720029ccbd844c097920b2eee40058897b089812ee4165ddc8000016225ec225dc82cbbb10016229ccbd844bb905977720029ccbd844c0976a0b2eee40053997b089812e64165ddc800a732f6113025c082cbbb9)) else (if i < 37 then (if i < 36 then 0x165e9ccbd832c0905977720000053997b0658120b2eec40053997b08a0cb024165ddc800a732f61141860482cbbb90014e65ec2282cc0905977720029ccbd8450518120b2eee400000b252f6083024165dd8800b254e65ec1060482cbbb90014e697422820c090597772002c94bd8450418120b2eee4004bd95708a083024165ddc800a732f61140e60482cbbb90014e65ec22816c0905977720029ccbd8450218120b2eee400000a734c2013024165dd8800a734c25ec0260482cbbb90014e698422804c090597772002c84bd8450098120b2eee40053995708a013024165ddc800a732f60840260482cbbb9 else 0x14e65ec7a844c0905977720029ccbd8f30898120b2eee40053997b1e2113024165ddc800a732f63bc2260482cbbb90014e65ec75844c0905977720029ccbd8e90898120b2eee40053997b1ca113024165ddc800a732f63642260482cbbb90014e65ec65844c0905977720029ccbd8b10898120b2eee40053997b15e113024165ddc800a732f62b42260482cbbb90014e65ec55844c0905977720029ccbd8a70898120b2eee40053997b14a113024165ddc800a732f62842260482cbbb90014e65ec4b844c0905977720029ccbd8830898120b2eee40053997b0f2113024165ddc800a732f61ac2260482cbbb9) else (if i < 38 then 0x29ccb4844c0905977620029ccbd9690898120b2eee40053997b2ce113024165ddc800a732f658c2260482cbbb90014e65ecaf844c090597772000005979570898120b2eec400597a732ae113024165ddc800b2f2f655c2260482cbbb90014e65ecaa844c0905977720029ccbd9530898120b2eee40053997b28e113024165ddc800a732f64dc2260482cbbb90014e65ec9a844c0905977720029ccbd9330898120b2eee40053997b262113024165ddc800a732f64b42260482cbbb90014e65ec95844c0905977720029ccbd9290898120b2eee40053997b23a113024165ddc800a732f643c2260482cbbb9 else 0x14e68ccbd844c0905977720029cd1897b0898120b2eee400539a2d2f6113024165ddc800a734425ec2260482cbbb90014e682cbd844c0905977720029cd0497b0898120b2eee400539a072f6113024165ddc800a7340a5ec2260482cbbb90014e67fcbd844c0905977720029ccf997b0898120b2eee4005399dd2f6113024165ddc800a733b65ec2260482cbbb90014e6764bd844c0905977720029cceb97b0898120b2eee4005399d12f6113024165ddc800a733925ec2260482cbbb90014e66e4bd844c0905977720029ccd797b0898120b2eee4005399a12f6113024165ddc800b254e65a42260482cbbb9)))) else (if i < 46 then (if i < 42 then (if i < 40 then 0x15d69ccbd844c090597772002b953997b0898120b2eee40056da732f6113024165ddc800ac94e65ec2260482cbbb900158e9ccbd844c090597772002b053997b0898120b2eee40055ca732f6113024165ddc800aad4e65ec2260482cbbb90015469ccbd844c090597772002a653997b0898120b2eee400000a732f6113024165dd8800a734ba5ec2260482cbbb90014e6964bd844c0905977720029cd2597b0898120b2eee400530a4b2f6113024165ddc8000014965ec2260482cbbb10014e6924bd844c0905977720029cd2397b0898120b2eee400539a372f6113024165ddc800a7346a5ec2260482cbbb9 else (if i < 41 then 0x2c84bd844c090597762002ced3997b0898120b2eee4005a6a732f6113024165ddc800b4b4e65ec2260482cbbb90016929ccbd844c090597772002d1d3997b0898120b2eee4005a2a732f6113024165ddc800b434e65ec2260482cbbb90016829ccbd844c090597772002cfd3997b0898120b2eee40059ea732f6113024165ddc800b394e65ec2260482cbbb90016429ccbd844c090597772002c7d3997b0898120b2eee40058ea732f6113024165ddc800b0f4e65ec2260482cbbb900161a9ccbd844c090597772002c253997b0898120b2eee40057fa732f6113024165ddc800aed4e65ec2260482cbbb9 else 0x14e65ec226eec0905977720029ccbd844db58120b2eee40053997b089b13024165ddc800a732f61135860482cbbb90014e65ec226a4c0905977720029ccbd844d2d8120b2eee40053997b089a3b024165ddc800a732f61134460482cbbb90014e65ec22676c0905977720029ccbd844cdd8120b2eee40053997b08998b024165ddc800a732f61132660482cbbb90014e65ec22640c0905977720029ccbd844c558120b2eee400592a734c25eb024165ddc8000014e6964bd60482cbbb10014e6964bd956c090597772002cbd39a610898120b2eee400000a734ba113024165dd8800b2f64a5ec2260482cbbb9)) else (if i < 44 then (if i < 43 then 0x14e65ec226a4c094b177720000053997b089a92572eec40053997b089a93024ae5ddc800a732f6113d560482cbbb90014e65ec22794c0905977720029ccbd844f058120b2eee40053997b089de3024165ddc800a732f6113b460482cbbb90014e65ec2275ec0905977720029ccbd844eb18120b2eee40053997b089d0b024165ddc800a732f61139d60482cbbb90014e65ec22728c0905977720029ccbd844e318120b2eee40053997b089c5b024165ddc800a732f61138a60482cbbb90014e65ec22712c0905977720029ccbd844e1d8120b2eee40053997b089c2b024165ddc800a732f61138160482cbbb9 else 0x14e6984bd844d4981177720029cd1c97b089a93022eee400539a0d2f6113526045ddc800a733e65ec226a4c08bbb90014e677cbd844d4981177720029ccbd957089a93022eee40053997b272113526045ddc800a732f63dc226a4c08bbb90014e65ec65844d4981177720029ccbd8b3089a93022eee40053997b08a083526045ddc800a732f6114026a4c08bbb90014e65ec227e6d4981177720029ccbd844d49a5b022eee40053997b089a93476045ddc800a732f61135266ec08bbb90014e65ec226a4c0977177720029ccbd844d49812da2eee40053997b089a93025845ddc800a732f611352604aa8bbb9) else (if i < 45 then 0x14e65ec2271ac09058bb720029ccbd844c094b20b176e40053997b089a93022ee2edc800a732f61138d4165dc5db90014e65ec224ae82cbb8bb720029ccbd844fcd05977176e40053997ac090597721a2edc800a732f6113024165dc5d390014e65ec2260482cbb8b7720029ccbd844c09059770aee40053997b089de3526045ddc800a732f61138d6a4c08bbb90014e65ec22702d4981177720029ccbd844db5a93022eee400597a732f6113526045ddc800b254e65ec226a4c08bbb90016229ccbd844d498117772002bbd3997b089a93022eee40056da732f6113526045ddc800acb4e65ec226a4c08bbb9 else 0x14e65ec22778c094b20b720000053997b089de257416c40053997b089de3024ae82dc800a732f6113bc60482cfbb90014e65ec22778c09059e3720029ccbd844ef18120b3b2e40053997b0898120b2ee1f5c800a732f6113024165dc67390014e65ec2260482cbb85d720029cc2260482cbb8970f0e40053997b0898120b2ee1e1c800a732f6113024165dc39b90014e65ec2260482cbb825720025ec2260482cbb84a04ae40053997b089de3024166d1c800a732f6113024165dc63390014e65eb024165dc868c6720029ccbd844c0905977186e400000a732f61138d4162ed8800a732f6113bc60482c5db9))) else (if i < 49 then (if i < 47 then 0x14e6834bd844ef18120b720029ccef97b089de302416e40053997b2ae113bc60482dc800a732f64e422778c0905b90014e65ec87844ef18120b720029ccbd8f7089de302416e40053997b166113bc60482dc800a732f611410778c0905b90014e65ec22804ef18120b720029ccbd844fcdde302416e40053997b089f3bbc60482dc800a732f6113bc768c0905b90014e65ec22778ebd8120b720029ccbd844ef1ceb02416e40053997b089de38d60482dc800a732f6113bc6a4c0905b90014e65ec22778c097720b720029ccbd844ef1812da416e40053997b089de30259e82dc800a732f6113bc604aa905b9 else (if i < 48 then 0x14e65eb024165dc86897720029cc2260482cbb90d12ee400539844c09059771b425dc800a730898120b2ee25c47b90014e65ec2260482cbb88f720029cc2260482cbb897118e40053997b0898120b2ee231c800a730898120b2ee25c43390014e65ec2260482cbb886720029ccbd844c0905977052e40053997b089eabbc60482dc800b2f4e65ec22778c0905b900164a9ccbd844ef18120b72002c453997b089de302416e40057fa732f6113bc60482dc800aef4e65ec22778c0905b90015969ccbd844ef18120b720029cd3097b089de302416e400539a392f6113bc60482dc800a734425ec22778c0905b9 else 0x14e61e42260482cbb897720029cc22820c090597712ee4005398450098120b2ee25dc800a73089f9b024165dc4bb90014e6113025dc82cbb897720029cc22604b690597712ee400539844c095520b2ee25dc800a73089812964165dc4bb90014e6113024ae82cbb897720000053984495d0597712ec40053997b0892ba0b2ee25dc800a73089812294165dc4bb90014e6113024167dcbb897720029cc2260482cf197712ee400539844c09059b42ee25dc800a730898120b32e5dc4bb90014e6113024165dcb2097720029cc2260482cbb95112ee400539844c090597724825dc8000014e58120b2ee4344bb1)) else (if i < 51 then (if i < 50 then 0x14e65ec226a4c08bb897720029cc22778c090597712ee400539844e358120b2ee25dc800a73089a93024165dc4bb90014e61132060482cbb89772002cbd39844c090597712ee400592a730898120b2ee25dc800b114e6113024165dc4bb90015de9cc2260482cbb89772002b2d39844c090597712ee40054ca730898120b2ee25dc800a734c2113024165dc4bb90014e68e42260482cbb897720029cd06844c090597712ee4005399df0898120b2ee25dc800a732f6113024165dc4bb90014e655c2260482cbb897720029cc9c844c090597712ee4005398f70898120b2ee25dc800a73166113024165dc4bb9 else 0x14e65ec22778c09058a4720029ccbd844e358120b148e40053997b08981296416291c800a732f6113526045dc52390014e65ec227e6c08bb8a4720029ccbd844c094b177148e40053997b0892ba0b2ee291c800a732f58120b2ee43452390014e65ec2260482cbb8a3720029ccbd844c0905977140e40053997b0898120b2ee18dc8000014e65ec22778d4981310014e65ec2260482cbb80f720029ccbd844c0905977028e40053997b0898120b2ee275c800a730898120b2ee2904bb90000029cc22778c0905897620029ccbd844ef18120b12ee400539844c090597717625dc8000014e6113526045dc4bb1) else (if i < 52 then 0x29cd1c844b6905977640000053997b2715520b2eec800000aef2f6113023ee5dd90000014e68342260478cbbb20000029ccbd8f6c08da177640000056597b0898120b2c8c800000a733be1130241654590000010898120b2ee25c25320000025ec22778c090584a64000004bd844d4981177094c80000097b0892ba0b2ee12990000012f58120b2ee43425320000029ccbd8b2c0905924640000053997aef18120b21ac800000a732f5a93022ee43590000014e65ea574165dc86b20000029ccbd844fccbb8da640029cc2260482cbb8970d0e40053997b0898120b2ee1a1c8000014e65ec22604a585231 else 0x29ccbd844c094b0a4640000053997b089de352604c800000a73089de30241625d90000014e6113526045dc4bb20000029cc224ae82cbb897640000053960482cbb90d12ec800000a732f6113bc4ae82d90000014e65ec2271a82c5db20000029ccbd844d492b9776400000539a592f58120b2eec800000a734ba113024165dd90000016425ec2260482cbbb20000029ccbd844c0905977640000052597b0898120b2eec800000a732d2113024165dd900000165e55c2260482cbbb20000029ccbd832c0905977640000059297b0418120b2eec800000a734c2013024165dd90000016225ec225dc82cbbb2))))))
private def st7 (i : Nat) : Nat := unpack st7Packed 95 20 i
private def adj7Packed (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0x851000002400003000080c20400410400c12000402091c000710001610110104218004a1430000440460830c42cb04000000000300b0471c1 else 0x10061c00c215200328104108040d0c62830001c20010400000020400c30800c00030420011000800090000461c21000c1381002084000102041082) else (if i < 3 then 0x1430c08050860430cc0010000000083002c03400c204004a10d0c20020001430430433090800031c30480030044830c200204008100008b142080001 else (if i < 4 then 0x8e0000c51021010020011c000100000110408a0c000d1420401025000c008000614918204714004e0010020010000c0040000082240006008000140 else 0x851000c034c10000b101085181000143388186007284002106204082)))
private def adj7 (i : Nat) : Nat := unpack adj7Packed 6 80 i
private def loc7Packed (i : Nat) : Nat := (if i < 10 then (if i < 5 then (if i < 2 then (if i < 1 then 0x3f0f78643c43885d400417508565dc80774c000371820008fd61000566000003e80e4c6800060664944bb8006ba89c002500004c4debbe000994002e6000001a90003820a0b98000000007b2b60000005139b64cd0cee3ed0000010e80000090800be16c4cbd380ee7245517697c else 0x45200008106816dc9983190002f5bcbf14ae00000000000f4c0000069c1506328a82ab34001170001d5788004920005f0004720010402d3662dc00000000d12048b1744000001aa3e89f97c0de6f88711c23b000000000f15dc4b0c4b6d0424003884b000001ed8fe662e2de0000) else (if i < 3 then 0x34a000e18000947802ca7f000001a680d0006c211000000539b99f3000118001c946800000082626f1d479af00007585a04070f3c8594a3a00000038506a000001f10009c800000698000000fd000000f2000000fdce0000000858000e6180000000000b00005611f0000014f37a else (if i < 4 then 0xeac7927a58ae68f6b5e000001ab0000000005e0001f400126aa6646bd0001cc36800000423562dbcb53ac0002b922bdc040404003dd7b25804e3f41ea000002e717600000247290c84520d11cee840020c0000ac0001b3eec9089b15732910001e3000000003ad06800000381 else 0x798515460005b87f80000055aac0851282de00169bf6000dfca625e000f085c8007264bdec3972c8a001ba466921a419800000001649ae0009c400000000dc41f8797a0efd0aafb000d2d839620004f8cb3b4100c38000c2000001ad00007600050388236000be80050c62c00232))) else (if i < 7 then (if i < 6 then 0x5b0000001a0636dd1b8000000000000000000000018700000000351000cd000091000001b029f0d0000ea8002bae340000060c08c00000666c49cb122000411640cd54a0000014258637c12acc0007b1f01c734e000682170000000019e0009bcfb2ae1a80000029107a6102186f else 0x25a4e04d236000db0dd8006c2230de000828000003a40303800018d0b800009a596b2000cfc01000261119100001dd02ba3568b8d458495ee0000033e0000017e8007fe2fdc741928e000452962524719b00031e3cdc8809000c140caa208e9b8000440000020e80000104800231) else (if i < 8 then 0xe930135424001129f9000a50472330002943d919000000dc1801263a4000000009b0002980f40000000000099dd9a48720052098006a6568e400001e0008680079c001ff364000e780000071400179bf97520a8000923025f80005b6d4a20000b221c374f13c30cc33def800 else (if i < 9 then 0x890a300020e0006b0a1000901aa0000006a00000045c000cab505400012e403708648ed00074a054ef9585f21d048000000fec001a108a5e0902ca22c0019396e038801868005d40003e800794001a2800224c5dde8007d4c04020555029f1d942027600040ae2000000eb029 else 0x171034b92a47eade1a12e50c2000001516ecb6a020422e000000276000928f421440200000297412218649b7018e3dc621f000ec00020640ebbc28c1c278a36108624ccfe8a4abf000000003e654e9680fa284d01489ca6a4e8c0000369000ff5f1b1c0d83bc001851ee00026c0c)))) else (if i < 15 then (if i < 12 then (if i < 11 then 0x761658000008f9070af83e000002870000006c800706000fd8006ce000b5c166ee000000671ae045fe000330aa8000b6656ca1c300000049d6b9d72ec3fc728534982a1d5221062c76073bb160c21be800552001b58005fe76c002c43e0001482d2001001a0a6d00034800000 else 0x65d01b5f74e000d5800000f140000069ed2800322000ec4002d9000001068007dc354000002560000007c014000003f879a00157a3c3f47fc002bc0000020d1186b60000000000028c0033b00000000000474584d31b10000001f1c500029d418004eee7c001432c6a8d3ea22) else (if i < 13 then 0x83ddb20a000fb081000000bc9ce0005c87380020b384e758880028000000407572000d48004a6748a80006520000000000000174000000475970003dc8400000000080887800000d1da012304ea4c002a8000b595904127a6880000059e794000004a46fcb40001103ac00000 else (if i < 14 then 0xc8d5c672ab288fac000500000009b3980000b0653ef33405c0014f000168e58005f8a648d338830e810d22a000000000e259c000002266cca851b96d00c001088e43e47f0000360ac4fc001be5bf07800000000ebde8ac06780016380055886c3f800000da0e540a4826318b032 else 0x8f4000001b88ad178006b05580006a1d40004a191000224a98003a80000027800093d30800314954002ec0f0274660001f2001c4a4b3c2cb4000005e0549b2b95000ca95c03c440000b32f57c841400125000e094d33900034c42000328258000aa7ac000e899c4ac55e080ab))) else (if i < 17 then (if i < 16 then 0x70000000000000d70478b31d8000001c6000b545a0c5000ef0003f0210001bab2c000e500016722a000000000002e9e0a430000000031f15a988ba219000478002c149c1c07695e00a570000000000000000033a4cc001a3822ee9f98a639a0002f80080a6b58a12a640f20003e5 else 0x64a991182de30c000000000fc9607e0872aa000dd1e975c0004bb0962030dd4000000000001ac2d80012e800604d206214b13c8b568000000a089914d7707bc9b800282cdc0002239e099ed0003b3020000007ae000980000005e8c400046aad4369d30bcc3c00000000b752f95f) else (if i < 18 then 0xc6000d20b50167983b3041e0000bd8081b4058c7000000000000e3000db8000241f025454a85430001f93355d2f2dbd86b106d5417800000000001b6000215db80005c000002631f696c0000052a000279695f4ed575a6967e0000041b2fe0c207a9b25c27d688d880400007000 else (if i < 19 then 0xe6000002fe372bd82e926000fa4003c967a001631fd3ceb6c81800000000638030246d5ea1710007ad5f0005c00012a0cb000000000000009ec0011157a0000030a116000001906300695d1994264241cb0c0003849a000080d19eabe70001389d09932612149000000f198f165 else 0xf5121000000328000003a1398c111a0000000043c778000005760782b800000df94e8020007d54489b00000181a6b5a9019c38001e8f8800000000000ee80000056ccd800306d8cbc924000ce95b90c51c130000000000013c8db4ea000d93d2228b851629c)))))
private def loc7 (i : Nat) : Nat := unpack loc7Packed 11 80 i
private def st8Packed (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0xa732f6113024ae82cbbb90014e65ec224ae82cbbb1a732f6113024167dcbbb9a732f61130241678cbbb9a732f6113024166d0bbb9a732f6113024165dcb239a732f6113024165dca8b9a732f6113024165dc25390012f6113024165dc2531a732f6113024165dc92390014e65eb024165dc86b1a732f6113024165dc86b9a732f6113024165dc6d39a732f6113024165dc4bb8a732f6113bc60482cbbb8a732f61135260482cbbb80014e65ec2260482cbbb0a732f6113024ae82cbbb8a732f6113024165dc2538a732f6113024165dc86b8 else 0xb2f4e65ec2260482cbbb9b254e65ec2260482cbbb9b114e65ec2260482cbbb9aef4e65ec2260482cbbb9acb4e65ec2260482cbbb9a734c25ec2260482cbbb9a734725ec2260482cbbb9a7341a5ec2260482cbbb9a733be5ec2260482cbbb9a732f655c2260482cbbb9a732f64e42260482cbbb9a732f63dc2260482cbbb9a732f62cc2260482cbbb9a732f61141060482cbbb9a732f61140260482cbbb9a732f6113f360482cbbb9a732f6113025dc82cbbb9a732f6113025b482cbbb9a732f61130255482cbbb9a732f61130252c82cbbb9) else (if i < 3 then 0xa732f6113024167dcbbbaa732f61130241678cbbbaa732f6113024166d0bbbaa732f6113024165dcb23aa732f6113024165dca8baa732f6113024165dc253a0012f6113024165dc2532a732f6113024165dc923a0014e65eb024165dc86b2a732f6113024165dc86baa732f6113024165dc6d3aa732f6113024165dc52390014e6113024165dc4bb1a732f6113024165dc4bb90014e65ec22778c0905b1a732f6113024165dc5db90014e65ec226a4c08bbb1a732f6113bc60482cbbb9a732f61138d60482cbbb9a732f61135260482cbbb9 else (if i < 4 then 0xb114e65ec2260482cbbbaaef4e65ec2260482cbbbaacb4e65ec2260482cbbbaa734c25ec2260482cbbbaa734725ec2260482cbbbaa7341a5ec2260482cbbbaa733be5ec2260482cbbbaa732f655c2260482cbbbaa732f64e42260482cbbbaa732f63dc2260482cbbbaa732f62cc2260482cbbbaa732f61141060482cbbbaa732f61140260482cbbbaa732f6113f360482cbbbaa732f6113025dc82cbbbaa732f6113025b482cbbbaa732f61130255482cbbbaa732f61130252c82cbbbaa732f6113024ae82cbbba0014e65ec224ae82cbbb2 else 0x14e6113024165dc4bb30014e65ec22778c0905b30014e65ec226a4c08bbb30014e65ec224ae82cbbb30012f6113024165dc25330014e65eb024165dc86b3a732f6113024165dc523a0014e6113024165dc4bb2a732f6113024165dc4bba0014e65ec22778c0905b2a732f6113024165dc5dba0014e65ec226a4c08bbb2a732f6113bc60482cbbbaa732f61138d60482cbbbaa732f61135260482cbbbab2f4e65ec2260482cbbbab254e65ec2260482cbbba)))
private def st8 (i : Nat) : Nat := unpack st8Packed 84 20 i
private def adj8Packed (_i : Nat) : Nat := 0x800184030080300c034809008c2101c602988800060
private def adj8 (i : Nat) : Nat := unpack adj8Packed 5 80 i
private def loc8Packed (i : Nat) : Nat := (if i < 1 then 0x94000511a3ed80b800041007d5807cb40114b117805c000001541cc300580470ec0000509c05366d0d46960304000d801400f45a10116bd448018dd780030338021553248000 else 0x7e000003c6d300544cc009b2004f0125b8008b01000031c00008c04e1016c560000ab22f30800bc3913a0000080b200000b4d4480a4a5d803b7d000)
private def loc8 (i : Nat) : Nat := unpack loc8Packed 7 80 i
private def st9Packed (_i : Nat) : Nat := 0xa732f6113024165dda53997b0898120b2eece9ccbd844c0905977654e65ec2260482cbbb1
private def st9 (i : Nat) : Nat := unpack st9Packed 73 20 i
private def adj9Packed (_i : Nat) : Nat := 0x0
private def adj9 (i : Nat) : Nat := unpack adj9Packed 1 80 i
private def loc9Packed (_i : Nat) : Nat := 0xc000200004000000000000000000000
private def loc9 (i : Nat) : Nat := unpack loc9Packed 2 80 i
private def certCount : Nat → Nat
  | 3 => 1
  | 4 => 83
  | 5 => 585
  | 6 => 1917
  | 7 => 1060
  | 8 => 97
  | 9 => 4
  | _ => 0
private def certSizes : Nat → Nat × Nat
  | 3 => (3,67)
  | 4 => (29,127)
  | 5 => (197,881)
  | 6 => (641,2879)
  | 7 => (359,1597)
  | 8 => (37,149)
  | 9 => (3,67)
  | _ => (1,2)
private def stData : Nat → Nat → Nat
  | 3 => st3
  | 4 => st4
  | 5 => st5
  | 6 => st6
  | 7 => st7
  | 8 => st8
  | 9 => st9
  | _ => fun _ => 0
private def adjData : Nat → Nat → Nat
  | 3 => adj3
  | 4 => adj4
  | 5 => adj5
  | 6 => adj6
  | 7 => adj7
  | 8 => adj8
  | 9 => adj9
  | _ => fun _ => 0
private def locData : Nat → Nat → Nat
  | 3 => loc3
  | 4 => loc4
  | 5 => loc5
  | 6 => loc6
  | 7 => loc7
  | 8 => loc8
  | 9 => loc9
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
private lemma cert3_0 : checkCert 3 0 1 = true := by decide +kernel

private lemma certLayer3 : checkCert 3 0 (certCount 3) = true :=
  cert3_0

set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_0 : checkCert 4 0 83 = true := by decide +kernel

private lemma certLayer4 : checkCert 4 0 (certCount 4) = true :=
  cert4_0

set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_0 : checkCert 5 0 96 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_96 : checkCert 5 96 96 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_192 : checkCert 5 192 96 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_288 : checkCert 5 288 96 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_384 : checkCert 5 384 96 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_480 : checkCert 5 480 96 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_576 : checkCert 5 576 9 = true := by decide +kernel

private lemma certLayer5 : checkCert 5 0 (certCount 5) = true :=
  (joinCert 5 0 288 297 (joinCert 5 0 96 192 cert5_0 (joinCert 5 96 96 96 cert5_96 cert5_192)) (joinCert 5 288 192 105 (joinCert 5 288 96 96 cert5_288 cert5_384) (joinCert 5 480 96 9 cert5_480 cert5_576)))

set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_0 : checkCert 6 0 96 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_96 : checkCert 6 96 96 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_192 : checkCert 6 192 96 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_288 : checkCert 6 288 96 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_384 : checkCert 6 384 96 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_480 : checkCert 6 480 96 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_576 : checkCert 6 576 96 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_672 : checkCert 6 672 96 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_768 : checkCert 6 768 96 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_864 : checkCert 6 864 96 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_960 : checkCert 6 960 96 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_1056 : checkCert 6 1056 96 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_1152 : checkCert 6 1152 96 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_1248 : checkCert 6 1248 96 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_1344 : checkCert 6 1344 96 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_1440 : checkCert 6 1440 96 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_1536 : checkCert 6 1536 96 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_1632 : checkCert 6 1632 96 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_1728 : checkCert 6 1728 96 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_1824 : checkCert 6 1824 93 = true := by decide +kernel

private lemma certLayer6 : checkCert 6 0 (certCount 6) = true :=
  (joinCert 6 0 960 957 (joinCert 6 0 480 480 (joinCert 6 0 192 288 (joinCert 6 0 96 96 cert6_0 cert6_96) (joinCert 6 192 96 192 cert6_192 (joinCert 6 288 96 96 cert6_288 cert6_384))) (joinCert 6 480 192 288 (joinCert 6 480 96 96 cert6_480 cert6_576) (joinCert 6 672 96 192 cert6_672 (joinCert 6 768 96 96 cert6_768 cert6_864)))) (joinCert 6 960 480 477 (joinCert 6 960 192 288 (joinCert 6 960 96 96 cert6_960 cert6_1056) (joinCert 6 1152 96 192 cert6_1152 (joinCert 6 1248 96 96 cert6_1248 cert6_1344))) (joinCert 6 1440 192 285 (joinCert 6 1440 96 96 cert6_1440 cert6_1536) (joinCert 6 1632 96 189 cert6_1632 (joinCert 6 1728 96 93 cert6_1728 cert6_1824)))))

set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert7_0 : checkCert 7 0 96 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert7_96 : checkCert 7 96 96 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert7_192 : checkCert 7 192 96 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert7_288 : checkCert 7 288 96 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert7_384 : checkCert 7 384 96 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert7_480 : checkCert 7 480 96 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert7_576 : checkCert 7 576 96 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert7_672 : checkCert 7 672 96 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert7_768 : checkCert 7 768 96 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert7_864 : checkCert 7 864 96 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert7_960 : checkCert 7 960 96 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert7_1056 : checkCert 7 1056 4 = true := by decide +kernel

private lemma certLayer7 : checkCert 7 0 (certCount 7) = true :=
  (joinCert 7 0 576 484 (joinCert 7 0 288 288 (joinCert 7 0 96 192 cert7_0 (joinCert 7 96 96 96 cert7_96 cert7_192)) (joinCert 7 288 96 192 cert7_288 (joinCert 7 384 96 96 cert7_384 cert7_480))) (joinCert 7 576 288 196 (joinCert 7 576 96 192 cert7_576 (joinCert 7 672 96 96 cert7_672 cert7_768)) (joinCert 7 864 96 100 cert7_864 (joinCert 7 960 96 4 cert7_960 cert7_1056))))

set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert8_0 : checkCert 8 0 96 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert8_96 : checkCert 8 96 1 = true := by decide +kernel

private lemma certLayer8 : checkCert 8 0 (certCount 8) = true :=
  (joinCert 8 0 96 1 cert8_0 cert8_96)

set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert9_0 : checkCert 9 0 4 = true := by decide +kernel

private lemma certLayer9 : checkCert 9 0 (certCount 9) = true :=
  cert9_0


private lemma allChecked (k : Nat) (hk : k ≤ 9) (i : Nat) (hi : i < certCount k) :
    runCheck certCount certState certLocate k i = true := by
  have h : checkCert k 0 (certCount k) = true := by
    have hc : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rfl
    · rfl
    · rfl
    · exact certLayer3
    · exact certLayer4
    · exact certLayer5
    · exact certLayer6
    · exact certLayer7
    · exact certLayer8
    · exact certLayer9
  exact checkBatch_at h i (Nat.zero_le i) (by simpa only [Nat.zero_add] using hi)

private lemma noLiveAt (k : Nat) (hk : k ≤ 9) (r : SearchState)
    (h : checkLink certCount certState certLocate k r = true) :
    ∀ m ≤ k, ¬ Live m r.1 r.2.toFinset := by
  intro m hm hl
  simp only [checkLink, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨hi,ht⟩,hw⟩ := h
  have he := sameWires_sound hw
  rw [ht,he] at hl
  exact runCheck_complete allChecked k hk _ hi m hm hl
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
lemma lowerBound (C : Circuit) (legal : FanInTwo C)
    (hasNot : ∃ g ∈ C.gates, g.op = .not)
    (correct : ∀ x, C.eval (List.ofFn x) = graph x) : 10 ≤ C.size := by
  by_contra small
  obtain ⟨k,t,S,hk,hc,hbin,live,sub⟩ :=
    extract C.gates raw legal (circuit_target raw rfl sample_correct C legal correct)
  have eq := necessary raw (by decide +kernel) live sub
  have sc : S.card = 6 := by rw [←eq]; decide
  have hs := (live_size live).2
  change ¬ 10 ≤ C.gates.length at small
  have notPositive : 0 < C.gates.countP (fun g => isNot g.op) := by
    obtain ⟨g, hg, hnot⟩ := hasNot
    by_contra! h
    have hz : C.gates.countP (fun g => isNot g.op) = 0 := by omega
    have hn := List.countP_eq_zero.mp hz g hg
    simp [hnot, isNot] at hn
  have tc : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 := by omega
  rcases tc with rfl | rfl | rfl | rfl | rfl
  · exact noLiveAt 8 (by decide) (0,raw) (by decide +kernel) k (by omega) (eq.symm ▸ live)
  · exact noLiveAt 9 (by decide) (1,raw) (by decide +kernel) k (by omega) (eq.symm ▸ live)
  · exact noLiveAt 9 (by decide) (2,raw) (by decide +kernel) k (by omega) (eq.symm ▸ live)
  · exact noLiveAt 9 (by decide) (3,raw) (by decide +kernel) k (by omega) (eq.symm ▸ live)
  · exact noLiveAt 9 (by decide) (4,raw) (by decide +kernel) k (by omega) (eq.symm ▸ live)

def monotoneCircuit : Circuit := ⟨[⟨.and, [3,5]⟩, ⟨.and, [1,2]⟩, ⟨.or, [4,6]⟩, ⟨.or, [3,5]⟩, ⟨.and, [8,9]⟩, ⟨.or, [1,2]⟩, ⟨.and, [0,7]⟩, ⟨.or, [0,11]⟩, ⟨.and, [10,13]⟩, ⟨.or, [12,14]⟩], 15⟩

lemma witness_mono : Monotone2 monotoneCircuit := by
  simp [monotoneCircuit, Monotone2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma witness_eval : ∀ x : Fin 6 → Bool, monotoneCircuit.eval (List.ofFn x) = graph x := by
  decide +kernel

end PEqualNP.Outside.L_meta_12398

open PEqualNP.Outside.L_meta_12398 in
theorem PEqualNP.Outside.L_meta_12398 :
∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124160 * 2 ^ 32 + 4269834368) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124160 * 2 ^ 32 + 4269834368) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  change ∀ s, PEqualNP.MetaComplexity.HasCircuitSize 6 graph s → _
  intro s hs
  obtain ⟨C, hlegal, hsize, heval⟩ := hs
  by_cases hn : ∃ g ∈ C.gates, g.op = .not
  · exact ⟨monotoneCircuit, witness_mono, (lowerBound C hlegal hn heval).trans hsize, witness_eval⟩
  · refine ⟨C, ?_, hsize, heval⟩
    intro g hg
    obtain ⟨hop, harity⟩ := hlegal g hg
    have hnot : g.op ≠ .not := fun he => hn ⟨g, hg, he⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    exact ⟨hop.elim Or.inl (fun h => Or.inr (h.resolve_right hnot)), harity⟩
