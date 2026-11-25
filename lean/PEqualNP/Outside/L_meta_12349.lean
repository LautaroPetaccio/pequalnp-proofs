import PEqualNP.Defs
-- The live-wire checker is adapted from ljste's PR 2918 and jfsantoropereira's L-meta-1007.
-- Adapted from the signed live-wire certificate in L_meta_8721. Apache-2.0.
namespace PEqualNP.Outside.L_meta_12349

abbrev B := BitVec 56
abbrev Sig := B × B
def top : B := BitVec.allOnes 56
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
  by_cases hi : i < 56
  · cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases ht : decide (0<t) <;>
      simp only [sep,neg,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 56 ≤ i)] at h

private lemma sep_binary (t d : Bool) (a b : Sig) (i : Nat)
    (h : (sep t (bin d a b)).getLsbD i = true) :
    (sep t a).getLsbD i = true ∨ (sep t b).getLsbD i = true := by
  by_cases hi : i < 56
  · cases t <;> cases d <;>
      cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases hu : b.1.getLsbD i <;> cases hv : b.2.getLsbD i <;>
      simp only [sep,bin,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,hu,hv] at h ⊢ <;> first | contradiction | decide
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 56 ≤ i)] at h

private lemma sep_weaken (t : Nat) (a : Sig) (i : Nat) (hi : i < 56)
    (h : (sep (decide (0<t)) a).getLsbD i = true) : (sep true a).getLsbD i = true := by
  cases ht : decide (0<t) <;> cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
    simp only [sep,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide

private lemma live_sep {k t S} (h : Live k t S) (i : Nat) (hi : i < 56) :
    ∃ a ∈ S, (sep (decide (0<t)) a).getLsbD i = true := by
  induction h using liveInd with
  | stop =>
    refine ⟨target,by simp,?_⟩
    change (BitVec.allOnes 56 &&& ~~~(0 : B)).getLsbD i = true
    rw [BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_allOnes (v := 56)]
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

def bit (side : Bool) (i : Fin 56) (a : Sig) : Bool :=
  (if side then a.1 else a.2).getLsbD i.val

private lemma bit_zero (s i) : bit s i zero = false := by cases s <;> simp [bit,zero]
private lemma bit_one (s i) : bit s i one = true := by
  cases s <;> change (BitVec.allOnes 56).getLsbD i.val = true <;> rw [BitVec.getLsbD_allOnes] <;> simp
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


def graph (x : Fin 6 → Bool) : Bool := Nat.testBit (4278124032 * 2 ^ 32 + 4261445632) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def sample (raw : List Sig) (s : Bool) (i : Fin 56) (j : Fin 6) := bit s i (raw.getD j.val zero)
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

def raw : List Sig := [(0x398c798c798c7f, 0x198c698c698c6e), (0x5e0f8e0f8e0f8f, 0x1e0f0e0f0e0f0d), (0x9ff00ff00ff00f, 0x1fe00fe00fe00b), (0xe0000fffffffff, 0xe000055ad55ad7), (0xfffff0000ffff0, 0xf55ad0000ab5b0), (0xfffffffff00000, 0xeab5bab5b00000)]

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

private def wireDataPacked (i : Nat) : Nat := (if i < 67 then (if i < 33 then (if i < 16 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0xa050a05000008000000000000000884288420000800000000000000044200000221000000000000000002210221000000000000000000000140400000a0200000000000000000a020a020000000000000000000000a4000000520000000000000000005200520000000000000000000000004420442010000000000000000000140414042000000000000000000000a400a440000000000000000000000000008 else 0xf0000040a040a0d0000000000000f0000010841084e00000000000000e0109010901090000000000000001fef6aa52aa52800000000000000154a40000aa52800000000000000154a40000aa52000000000000000154000000aa00800000000000000140a00000a05080000000000000011084000088428000000000000000aa52aa5200008000000000000000aa52aa5200000000000000000000aa00aa0000008) else (if i < 3 then 0xff0000a400a401ff400000000000ff0000a40000015b000000000000ff00000000a401ad400000000000f80000a000a000f0400000000000c7000084008400c64000000000003800002000200139000000000000070000040004010f00000000000000f154a454a4fef6f0000000000000f0aa52fef654a4f0000000000000f0000054a454a4f0000000000000f0000054a454a470000000000000f0000054005400b else 0x60380040204020603010000000001fff0014a414a41fff60000000001f07f0140454a45faff0000000001f070154a41404bf5fa0000000001f0700140414041f0f20000000001f0700140400000b0b00000000001f070000001404150d20000000001f0000140014001e0020000000001807001004100418062000000000070000040004000709000000000000fff000a454a455fff00000000000ff0154a400a4abffc)) else (if i < 6 then (if i < 5 then 0x98c7f0000010841084600000000098c70110840000884200000000009800f1100010009800a00000000080c0f10080008080c0c0000000007f3f00542454247f3f300000000067ff0044a444a467ff50000000006738f0442054a477bdf00000000067380154a44420ef7b90000000006738004420442067391000000000673800442000002319000000000067380000004420452910000000006700004400440066001 else 0xffff000000000001090000000000fff8f154a054a0fef0f000000000ffc7f154845484fec6f000000000ff00f154005400fe00b000000000ff00f00000540054003000000000ff000154000000aa000000000000f8fff150a450a4f8f6f000000000e0f8f140a040a0e0f0d000000000e0f8f0000040a040a05000000000e0f80140a00000a0500000000000e000f140004000e000900000000098c7f11084108498c6e) else (if i < 7 then 0x70000000002010f00040000000000fffff1fef6fef6fffff000000000fffff154a454a4fffff000000000fffff154a454a4ffff7000000000fffff154a45400ff5bb000000000fffff154a440a0ebfbd000000000fffff154a41084bbdfe000000000fffff1540054a4ffadf000000000fffff140a054a4f5fdf000000000fffff1108454a4ddeff000000000fffff0000054a455ad7000000000ffff0154a40000ab5b0 else 0x1807000000080218061004200000070000000002000709040000000000fffffff154f655fffffff0000000ff00ff0000f601ff01ff40000000ff0000f0005255ff54a4f0000000ff000000aa52abff00a4c0000000ff000000005201ff00a440000000ff0000000052015b000000000000ff000000000001ad00a440000000f8000000005000f000a040000000c7000000004200c6008440000000380000000010013900200))) else (if i < 12 then (if i < 10 then (if i < 9 then 0x6738000000000045294420100000670000000022006600440010000060380000002010603040201000001fff0000000a521fff14a46000001f07fffff15ea65faffffff000001f071f07001e061f0f1f0f2000001f070000f00a025faf54a4f000001f07000000aa52bf5f1404a000001f070000000a021f0f14042000001f070000000a020b0b00000000001f070000000000150d14042000001f000000000a001e0014002 else 0x98009800f000001000100020000098000000f0880098001000a0000080c080c0f000000080008040000080c00000f0804080c00080c000007f3f0000002a127f3f542430000067ff000000225267ff44a45000006738fffff176b477bdfffff00000673867380066306739673910000067380000f0221077bd54a4f000006738000000aa52ef7b4420900000673800000022106739442010000067380000002210231900000) else (if i < 11 then 0xff00000000aa00aa000000000000f8ff0000f0a852f8f650a4f00000e0f8e0f8f1e0f0e0f0e0f0d00000e0f80000f0a050e0f040a0d00000e0f80000f0000040a040a0500000e0f8000000a050a0500000000000e000e000f0000040004000100000e0000000f0a000e000400090000098c798c7f198c698c698c6e0000098c70000f0884298c61084e0000098c70000f000001084108460000098c70000008842884200000 else 0xffff0000f0aa52bbdf1084e00000ffff0000f0aa00ffad54a4f00000ffff0000f0a050f5fd54a4f00000ffff0000f08842ddef54a4f00000ffff0000f0000055ad54a4700000ffff000000aa52ab5b0000000000ffff000000000001090000000000fff80000f0aa50fef054a0f00000ffc70000f0aa42fec65484f00000ff00ff00f1fe00fe00fe00b00000ff000000f0aa00fe005400b00000ff000000f00000540054003)) else (if i < 14 then (if i < 13 then 0x70000000000010f00020002000000fffffffff1fef6fffffffff00000fffffffff0000055ad55ad700000ffffffff01fef6ab5bab5b000000ffff6738f0ee72ffff77bdf00000ffff1f07f0be56ffff5faff00000ffff00fff0aaf6ffff55fff00000ffff0000f1fef6fffffef6f00000ffff0000f0aa52ffff54a4f00000ffff0000f0aa52ffff54a4700000ffff0000f0aa52ff5b5400b00000ffff0000f0aa52ebfb40a0d else 0xff00ff00000001ff01ff00f64000ff0000fffff155ff54f6fffff000ff000000ff0001ff00f601ff4000ff000000000155ff0052aa528000ff0000000000abffaa5200528000ff000000000001ff005200520000ff000000000001ad000000520000ff0000000000015b005200000000f8000000000000f0005000500000c7000000000000c6004200420000c000c000c00000c000c000c040003800000000000139001000100) else (if i < 15 then 0x1f070000fffff15faf5ea6fffff01f0700001f07001f0f1e061f0f201f0700000000015faf0a02aa52801f070000000000bf5faa520a02801f0700000000001f0f0a020a02001f070000000000150d00000a02001f0700000000000b0b0a020000001f0000000000001e000a000a000018070000000000180608020802001800180018000018001800180020070000000000000709020002000000ffffff0000f0abffffff54f6f else 0x67380000673800673966306739106738000000000177bd2210aa528067380000000000ef7baa522210806738000000000067392210221000673800000000004529000022100067380000000000231922100000006700000000000066002200220000603800000000006030201020100060006000600000600060006000101fff00000000001fff0a520a52001f07ffff0000f0bf5fffff5ea6f01f071f070000001f0f1f0f1e062)))) else (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then 0x180c080c0e0f8f1c0e0c0e0e0f0d180c080c098c7f190c490c498c6e180c080c080c0f180c080c080c0c180c080c00000008040804000000180c0000080c0010080000080400180c0000000000180c08040804081800080008000f1800080008000807f3f00000000007f3f2a122a120067ff000000000067ff22522252006738ffff0000f0ef7bffff76b4f0673867380000006739673966301067380000fffff177bd76b4fffff else 0x1980098c79800f1984298c69884e198009800fffff1dca4dca4fffff198009800ff00f1dc00dc00fe00b19800980098c7f19884988498c6e1980098009800f1980098009800a198009800000000880088000000019800000098000110000000880001980000000000019800880088008180c0ffff80c0f1aad2ffffd4e4f180c0e0f880c0f1a0d0e0f0c0e0d180c098c780c0f188c298c690c4e180c080c0fffff1d4e4d4e4fffff) else (if i < 19 then 0x1e0000000e0000140000000a00001e0000000000001e000a000a0008198c798c70000f198c698c698c6e198c798009800f198c698429842a198c780c080c0f198c688c288c2c198c7000098c7f198c698c698c6e198c7000000000198c6884288428198c700000000011084000088420198c700000000008842884200000198c098c098c0f198c098c098c0e19800ffff9800f1ba52ffffdca4f19800ff009800f1ba00fe00dc00b else 0x1e0f80000000001e0f0a050a05081e0f8000000000140a00000a05001e0f80000000000a050a050000001e0c0e0c0e0c0f1e0c0e0c0e0c0d1e000ffffe000f1ea52fffff4a4f1e000ff00e000f1ea00fe00f400b1e000e0f8e000f1e050e0f0e0a0d1e000e000fffff1f4a4f4a4fffff1e000e000ff00f1f400f400fe00b1e000e000e0f8f1e0a0e0a0e0f0d1e000e000e000f1e000e000e00091e000e000000000a000a00000000)) else (if i < 22 then (if i < 21 then 0x1ff00e000e000f1fe00ea00ea0091ff0098009800f1fe00ba00ba00a1ff000000ff00f1fe00fe00fe00b1ff000000000001fe00aa00aa0081ff00000000000154000000aa0001ff000000000000aa00aa00000001f8ff0000000001f8f6a852a85281f800f800f800f1f800f800f800b1e0f8e0f80000f1e0f0e0f0e0f0d1e0f8e000e000f1e0f0e050e05091e0f880c080c0f1e0f0a0d0a0d0c1e0f80000e0f8f1e0f0e0f0e0f0d else 0x1ffff0000000001ffadaa00aa5281ffff0000000001ff5baa52aa0081ffff0000000001f5fda050aa5281ffff0000000001ebfbaa52a05081ffff0000000001ddef8842aa5281ffff0000000001bbdfaa52884281ffff000000000155ad0000aa5201ffff0000000000ab5baa52000001ffff000000000001090000000001fff80000000001fef0aa50aa5081ffc70000000001fec6aa42aa4281ff00ff000000f1fe00fe00fe00b) else (if i < 23 then 0x1ffff6738000001ffffef7bee7291ffff1f07000001ffffbf5fbe56a1ffff00ff000001ffffabffaaf6c1ffff0000fffff1fffffef6fffff1ffff0000fffff0ab5bfef655ad71ffff0000ffff0155ad0000ab5b01ffff0000673801ffffee72ef7b91ffff00001f0701ffffbe56bf5fa1ffff000000ff01ffffaaf6abffc1ffff00000000f1fffffef6fef6f1ffff0000000001ffffaa52aa5281ffff0000000001ffffaa52aa520 else 0x2000098c7000000000000000000020000180718070000001004100422000000c700c700000000840084420000000700070e0000010d010d020000000098c70000000000000001fffffffffffff1fffffffffffff1ffffffff0000f1fffffffffef6f1ffffffff0000f155ad55adfef671ffffffff000000ab5bab5b000001ffffe000e000f1ffffea52ea5291ffff98009800f1ffffba52ba52a1ffff80c080c0f1ffffaad2aad2c))) else (if i < 28 then (if i < 26 then (if i < 25 then 0x20007000700070e010f010f010f0200070007000700000600060006020007000700000e010b010b0000020007000000070e010d0000010b020000fffffffff0000055ad55ad720000ffff98c7f0aa52ffff54a4f20000ffff98c7f0000055ad54a472000098c7fffff154a454a4fffff2000098c7fffff0000054a455ad72000098c798c7f11084108498c6e2000098c798c7f0884298c61084e2000098c798c7f00000108410846 else 0x200c700c700c70000c600c600c64200c700c70000000042004200000200c7000000c700008400000042020007ffff0007feab5fffff55aff2000798c798c7f000061086108662000798c70007f0884698c61086e200071f0700070e0b0f1f0f150f22000700ff00070e015f01ff01af4200070007ffffff55af55affffff20007000798c7f11086108698c6e2000700071f070e150f150f1f0f220007000700ff0e01af01af01ff4) else (if i < 27 then 0x2180700001807001004000008020200ff000700070e01ff015f015f0200c798c798c7f198c698c698c6e200c798c798c7f110c610c698c6e200c798c798c7f088c698c610c6e200c798c798c7f000c610c610c66200c798c798c7f00084108410c66200c798c798c7f0004210c610846200c798c700c7f088c698c610c6e200c780c780c7f000c600c600c64200c700c798c7f110c610c698c6e200c700c700c7f000c610c610c6e else 0x2180798c798c7f198c698c698c6e2180798c798c7f11886188698c6e2180798c798c7f0984698c61886e2180798c798c7f018061886188662180798c798c7f010041084188662180798c798c7f008021886108462180798c71807f0984698c61886e2180798079807f0180618061806221807180798c7f11886188698c6e2180718071807f0180618861886e21807180718070018061806180622180718070000000802080200000)) else (if i < 30 then (if i < 29 then 0x380c798c798c7f180c690c690c6e380c798c780c7f188c698c690c6e380c780c798c7f190c690c698c6e380c780c780c7f180c680c680c6c380c098c798c7f180c090c490c4e3800780078007f180068006800682673898c798c7f0673932943294621f07000700070e1f0f0b0f0b0f0218c798c798c7f018c618c618c66218c798c718c7f098c698c618c6e218c718c798c7f118c618c698c6e218c718c718c70018c618c618c66 else 0x398c700c700c70198c688c688c6c398c70000fffff154a454a4fffff398c70000ffff0154a40000ab5b0398c7000098c7f11084108498c6e398c7000098c70198c6884288428398c7000098c7011084000088420398c7000000000000000000000003980798c798c7f1980698869886e3980798c79807f1984698c69886e39807980798c7f19886988698c6e3980798079807f1980698069806a3980098c798c7f1980098849884e) else (if i < 31 then 0x398c7980098c7f1988498009842a398c780c798c7f190c680c688c6c398c780c780c7f198c688c688c6c398c780c098c7f190c480c088c2c398c7673898c70132946739cc621398c7180798c7f198c698c698c6e398c7180798c7f11886188698c6e398c7180798c7011886180698462398c7180718070198c698469846a398c700c798c7f198c698c698c6e398c700c798c7f110c610c698c6e398c700c798c70110c600c688c64 else (if i < 32 then 0x398c798c7673800cc62cc6267391398c798c71807f198c698c698c6e398c798c71807f0984698c61886e398c798c71807009846984618062398c798c700c7f198c698c698c6e398c798c700c7f088c698c610c6e398c798c700c70088c688c600c64398c798c70000f0884298c61084e398c798c700000198c6884288428398c798c70000008842884200000398c7980798c7f1988698069846a398c798079807f198c698469846a else 0x398c798c798c7f11084108498c6e398c798c798c7f11084108498c66398c798c798c7f0984698c618866398c798c798c7f088c698c610c66398c798c798c7f0884298c61084e398c798c798c7f0884298c610846398c798c798c7f00000108410846398c798c798c70198c6884288420398c798c79807f1984698469806a398c798c79800f1984298429800a398c798c780c7f188c688c680c6c398c798c780c0f188c288c280c0c)))))) else (if i < 50 then (if i < 41 then (if i < 37 then (if i < 35 then (if i < 34 then 0x398c798c798c7f198c69cc69cc6e398c798c798c7f198c698e698e6e398c798c798c7f198c698c698c6e398c798c798c7f198c698c698c66398c798c798c7f198c698429842a398c798c798c7f198c688c288c2c398c798c798c7f19884988498c6e398c798c798c7f1984298c69884e398c798c798c7f190c490c498c6e398c798c798c7f188c298c690c4e398c798c798c7f11886188698c66398c798c798c7f110c610c698c66 else 0x398c798c798c7f1fef6bad6bad6e398c798c798c7f1dce698c6bad6e398c798c798c7f1dcc698c6bac6e398c798c798c7f1d8e698c6b8d6e398c798c798c7f1bad6bad698c6e398c798c798c7f1bac6bac698c6e398c798c798c7f1b8d6b8d698c6e398c798c798c7f19cc698c69ac6e398c798c798c7f19ac69ac698c6e398c798c798c7f198e698c698d6e398c798c798c7f198d698d698c6e398c798c798c7f198c6dce6dce6f) else (if i < 36 then 0x398c798c7fffff1dce6dce6fffff398c798c7fffff1dce698c6bbdfe398c798c7fffff198c6dce6ddeff398c798c7ffc7f1dcc6dcc6fec6f398c798c7ffc7f1dcc698c6bac6e398c798c7f8fff1d8e6d8e6f8f6f398c798c7f8fff1d8e698c6b8d6e398c798c79fc7f19cc69cc69fcfe398c798c79fc7f19cc69cc69ec6e398c798c798fff198e698e699ffe398c798c798fff198e698e698f6e398c798c798c7ff99cf99cf99cfe else 0x398c7ffff98c7f1bad6bbdf98c6e398c7ffff98c7f198c6ddefdce6f398c7ffff0000f0aa52ffff54a4f398c7ffff000000aa52ab5b00000398c7ffc798c7f1bac6fec6dcc6f398c7ffc798c7f1bac6bac698c6e398c7f8ff98c7f1b8d6f8f6d8e6f398c7f8ff98c7f1b8d6b8d698c6e398c79fc798c7f19ac69fcf9cc6e398c79fc798c7f19ac69ec69cc6e398c798ff98c7f198d699ff98e6e398c798ff98c7f198d698f698e6e)) else (if i < 39 then (if i < 38 then 0x3f8ff98c798c7f1b8d6b8d698c6e3f8c7f8c7f8c7f1f8c6f8c6f8c6f3f8c7f8c798c7f1b8c6b8c698c6e3f8c798c7f8c7f1d8c698c6b8c6e3f8c798c798c7f1f8c6b8c6b8c6e3e007e007e007ffe10fe10fe10f939fc798c798c7f19fcf9ac69ac6e39fc798c798c7f19ec69ac69ac6e398ff98c798c7f199ff98d698d6e398ff98c798c7f198f698d698d6e398c7fffffffff1fef6fffffffff398c7ffff98c7f1bad6ffffdce6f else 0x3ffff98c798c7f1bbdfbad698c6e3ffff98c7000001ffffaa52aa5283ffff98c7000000ab5baa52000003ffff000700070fffffab5fab5f83ffff0000ffff0155ad0000ab5b03ffff000098c701ffffaa52aa5283ffff000098c70155ad0000aa5203ffc798c798c7f1fec6bac6bac6e3ffc798c798c7f1dcc698c6bac6e3ffc798c798c7f1bac6bac698c6e3f8ff98c798c7f1f8f6b8d6b8d6e3f8ff98c798c7f1d8e698c6b8d6e) else (if i < 40 then 0x40000e0f8e0f8f0000040a040a0540000e0f8000000000000000000040000603860380000004020402014000000f800f800000000a000a0440000003800380e0000012901290400000000e0f80000000000000003ffffffff98c7f1fffffffffef6f3ffffffff000000ab5bab5b000003ffff98c7fffff1fffffef6fffff3ffff98c798c7f1ffffbad6bad6e3ffff98c798c7f1fef6bad6bad6e3ffff98c798c7f1ddef98c6bad6e else 0x40038003800ff0e01bd01bd01ff440038003800380e0139013901390400380038003800003000300030040038003800000e011901190000040038000000380e012900000119040000fffffffff0000055ad55ad740000ffffe0f8f0aa52ffff54a4f40000ffffe0f8f0000055ad54a4740000e0f8fffff154a454a4fffff40000e0f8fffff0000054a455ad740000e0f8e0f8f140a040a0e0f0d40000e0f8e0f8f0a050e0f040a0d))) else (if i < 45 then (if i < 43 then (if i < 42 then 0x400f800f800f8f000f040f040f0d400f800f800f80000f000f000f04400f800f80000000050005000000400f8000000f80000a000000050040038ffff0038feab7bffff55bdf40038e0f8e0f8f0003040b040b0540038e0f80038f0a070e0f040b0d40038673800380e23396739453914003800ff00380e017b01ff01bd4400380038ffffff55bd55bdfffff400380038e0f8f140b040b0e0f0d40038003867380e4539453967391 else 0x460380000603800402000002010041f07e0f8e0f8f01f0f4aa24aa25400ff003800380e01ff017b017b0400f8e0f8e0f8f1e0f0e0f0e0f0d400f8e0f8e0f8f140f040f0e0f0d400f8e0f8e0f8f0a0f0e0f040f0d400f8e0f8e0f8f000f040f040f05400f8e0f8e0f8f000a040a040f05400f8e0f8e0f8f0005040f040a05400f8e0f800f8f0a0f0e0f040f0d400f880f880f8f000f000f000f04400f800f8e0f8f140f040f0e0f0d) else (if i < 44 then 0x46038e0f8e0f8f1e0f0e0f0e0f0d46038e0f8e0f8f160b060b0e0f0d46038e0f8e0f8f0e070e0f060b0d46038e0f8e0f8f0603060b060b0546038e0f8e0f8f0402040a060b0546038e0f8e0f8f0201060b040a0546038e0f86038f0e070e0f060b0d46038e038e038f06030603060301460386038e0f8f160b060b0e0f0d4603860386038f0603060b060b0d46038603860380060306030603014603860380000002010201000000 else 0x5983898389838ff993999399939a580f8e0f8e0f8f180f0c0f0c0f0d580f8e0f880f8f1a0f0e0f0c0f0d580f880f8e0f8f1c0f0c0f0e0f0d580f880f880f8f180f080f080f0c580c0e0f8e0f8f180c0c0e0c0e0d5803880388038f1803080308030846738003800380e6739233923390460f8e0f8e0f8f060f060f060f05460f8e0f860f8f0e0f0e0f060f0d460f860f8e0f8f160f060f0e0f0d460f860f860f80060f060f060f05)) else (if i < 47 then (if i < 46 then 0x5e0f800f800f801e0f0a0f0a0f0c5e0f80000fffff154a454a4fffff5e0f80000ffff0154a40000ab5b05e0f80000e0f8f140a040a0e0f0d5e0f80000e0f801e0f0a050a05085e0f80000e0f80140a00000a05005e0f8000000000000000000000005e038e0f8e0f8f1e030e0b0e0b0d5e038e0f8e038f1e070e0f0e0b0d5e038e038e0f8f1e0b0e0b0e0f0d5e038e038e038f1e030e030e03095e000e0f8e0f8f1e000e0a0e0a0d else 0x5e0f8e000e0f8f1e0a0e000e05095e0f880f8e0f8f1c0f080f0a0f0c5e0f880f880f8f1e0f0a0f0a0f0c5e0f880c0e0f8f1c0e080c0a0d0c5e0f86038e0f8f1e0f0e0f0e0f0d5e0f86038e0f8f160b060b0e0f0d5e0f86038e0f80160b06030e07015e0f86038603801e0f0e070e07095e0f81f07e0f8014aa21f0fb45425e0f800f8e0f8f1e0f0e0f0e0f0d5e0f800f8e0f8f140f040f0e0f0d5e0f800f8e0f80140f000f0a0f04) else (if i < 48 then 0x5e0f8e0f86038f1e0f0e0f0e0f0d5e0f8e0f86038f0e070e0f060b0d5e0f8e0f8603800e070e070603015e0f8e0f81f0700b454b4541f0f25e0f8e0f800f8f1e0f0e0f0e0f0d5e0f8e0f800f8f0a0f0e0f040f0d5e0f8e0f800f800a0f0a0f000f045e0f8e0f80000f0a050e0f040a0d5e0f8e0f8000001e0f0a050a05085e0f8e0f8000000a050a050000005e0f8e038e0f8f1e0b0e030e07095e0f8e038e038f1e0f0e070e0709 else (if i < 49 then 0x5e0f8e0f8e0f8f140a040a0e0f0d5e0f8e0f8e0f8f140a040a0e0f055e0f8e0f8e0f8f0e070e0f060b055e0f8e0f8e0f8f0a0f0e0f040f055e0f8e0f8e0f8f0a050e0f040a0d5e0f8e0f8e0f8f0a050e0f040a055e0f8e0f8e0f8f0000040a040a055e0f8e0f8e0f801e0f0a050a05005e0f8e0f8e038f1e070e070e03095e0f8e0f8e000f1e050e050e00095e0f8e0f880f8f1a0f0a0f080f0c5e0f8e0f880c0f1a0d0a0d080c0c else 0x5e0f8e0f8e0f8f1e0f0e4f0e4f0d5e0f8e0f8e0f8f1e0f0e0f4e0f4d5e0f8e0f8e0f8f1e0f0e0f0e0f0d5e0f8e0f8e0f8f1e0f0e0f0e0f055e0f8e0f8e0f8f1e0f0e050e05095e0f8e0f8e0f8f1e0f0a0d0a0d0c5e0f8e0f8e0f8f1e0a0e0a0e0f0d5e0f8e0f8e0f8f1e050e0f0e0a0d5e0f8e0f8e0f8f1c0e0c0e0e0f0d5e0f8e0f8e0f8f1a0d0e0f0c0e0d5e0f8e0f8e0f8f160b060b0e0f055e0f8e0f8e0f8f140f040f0e0f05))))) else (if i < 58 then (if i < 54 then (if i < 52 then (if i < 51 then 0x5e0f8e0f8e0f8f1fef6eaf2eaf2d5e0f8e0f8e0f8f1f4f4e0f0eaf2d5e0f8e0f8e0f8f1f4f0e0f0eaf0d5e0f8e0f8e0f8f1f0f4e0f0e8f2d5e0f8e0f8e0f8f1eaf2eaf2e0f0d5e0f8e0f8e0f8f1eaf0eaf0e0f0d5e0f8e0f8e0f8f1e8f2e8f2e0f0d5e0f8e0f8e0f8f1e4f0e0f0e2f0d5e0f8e0f8e0f8f1e2f0e2f0e0f0d5e0f8e0f8e0f8f1e0f4e0f0e0f2d5e0f8e0f8e0f8f1e0f2e0f2e0f0d5e0f8e0f8e0f8f1e0f0f4f4f4f4f else 0x5e0f8e0f8fffff1f4f4f4f4fffff5e0f8e0f8fffff1f4f4e0f0ebfbd5e0f8e0f8fffff1e0f0f4f4f5fdf5e0f8e0f8fff8f1f4f0f4f0fef0f5e0f8e0f8fff8f1f4f0e0f0eaf0d5e0f8e0f8f8fff1f0f4f0f4f8f6f5e0f8e0f8f8fff1f0f4e0f0e8f2d5e0f8e0f8e7f8f1e4f0e4f0e7f9d5e0f8e0f8e7f8f1e4f0e4f0e6f0d5e0f8e0f8e0fff1e0f4e0f4e1ffd5e0f8e0f8e0fff1e0f4e0f4e0f6d5e0f8e0f8e0f8ffe1f9e1f9e1f9d) else (if i < 53 then 0x5e0f8ffffe0f8f1eaf2ebfbe0f0d5e0f8ffffe0f8f1e0f0f5fdf4f4f5e0f8ffff0000f0aa52ffff54a4f5e0f8ffff000000aa52ab5b000005e0f8fff8e0f8f1eaf0fef0f4f0f5e0f8fff8e0f8f1eaf0eaf0e0f0d5e0f8f8ffe0f8f1e8f2f8f6f0f4f5e0f8f8ffe0f8f1e8f2e8f2e0f0d5e0f8e7f8e0f8f1e2f0e7f9e4f0d5e0f8e7f8e0f8f1e2f0e6f0e4f0d5e0f8e0ffe0f8f1e0f2e1ffe0f4d5e0f8e0ffe0f8f1e0f2e0f6e0f4d else 0x5f8ffe0f8e0f8f1f0f4e0f0e8f2d5f8ffe0f8e0f8f1e8f2e8f2e0f0d5f8f8f8f8f8f8f1f8f0f8f0f8f0f5f8f8f8f8e0f8f1e8f0e8f0e0f0d5f8f8e0f8f8f8f1f0f0e0f0e8f0d5f8f8e0f8e0f8f1f8f0e8f0e8f0d5e7f8e0f8e0f8f1e7f9e2f0e2f0d5e7f8e0f8e0f8f1e6f0e2f0e2f0d5e0ffe0f8e0f8f1e1ffe0f2e0f2d5e0ffe0f8e0f8f1e0f6e0f2e0f2d5e0f8fffffffff1fef6fffffffff5e0f8ffffe0f8f1eaf2fffff4f4f)) else (if i < 56 then (if i < 55 then 0x5ffffe0f8e0f8f1f5fde0f0eaf2d5ffffe0f8e0f8f1ebfbeaf2e0f0d5ffffe0f8000001ffffaa52aa5285ffffe0f8000000ab5baa52000005ffff003800380fffffab7bab7b85ffff0000ffff0155ad0000ab5b05ffff0000e0f801ffffaa52aa5285ffff0000e0f80155ad0000aa5205fff8e0f8e0f8f1fef0eaf0eaf0d5fff8e0f8e0f8f1f4f0e0f0eaf0d5fff8e0f8e0f8f1eaf0eaf0e0f0d5f8ffe0f8e0f8f1f8f6e8f2e8f2d else 0x60000f8fff8fff0000050a450a4760000e0ffe0fffe000041ad41ad56000098ff98fffe000011ad11ad66000000fffffffe000055ad55ad76000000ff00ff0e000001ad01ad46000000ff00000e000001090000060000000000ff0e00000000010905ffffffffe0f8f1fffffffffef6f5ffffffff000000ab5bab5b000005ffffe0f8fffff1fffffef6fffff5ffffe0f8e0f8f1ffffeaf2eaf2d5ffffe0f8e0f8f1fef6eaf2eaf2d) else (if i < 57 then 0x600ff00ff00c70e01df01df00c64600ff00ff00000e015b015b00000600ff00f800ff0e01fd00f001fb4600ff00c700ff0e01ef00c601df4600ff0000ffff0f55ad0000ab5b0600ff000000ff0e01ad0000015b0600ff000000000e0109000000000600f800ff00ff0e00f001fd01fd4600c700ff00ff0e00c601ef01ef46003f003f003f0e013f013f013f060000fffffffffe000055ad55ad760000ffff00fffe000055ad55ad7 else 0x600ff00ffff00ff555b555bfe00b600ff00ff67ff0e45ff45ff67ff5600ff00ff1fff0e15ff15ff1fff6600ff00ff00fffe01ff55ff55fff600ff00ff00ff0f55ff01ffabffc600ff00ff00ff0eabffabff01ffc600ff00ff00ff0e01ff01ff01ff4600ff00ff00ff0e01ff015b015b0600ff00ff00ff0e01ad01ad01ff4600ff00ff00ff0e015b01ff01ad4600ff00ff00ff0000f600f600f64600ff00ff00f80e01fb01fb00f04))) else (if i < 62 then (if i < 60 then (if i < 59 then 0x6783f783f783f007836783678363667ff00ff00ff0e67ff23ff23ff461fff00ff00ff0e1fff0bff0bff4600fffffffffffffffffffffffff600ffffff00fffeabffffff55fff600ffffff00000eab5bab5b00000600ffff0000fffeabadfe00555bb600ffe0ffe0fffe01ff41ff41ff5600ff98ff98fffe01ff11ff11ff6600ff67ff00ff0e23ff67ff45ff5600ff1fff00ff0e0bff1fff15ff6600ff00ffffffff55ff55fffffff else 0x798ff98ff00000e895b895b00000798ff98c798ffff99ef98c699dfe798ff98c798fff198e698c698d6e798ff00ff98ff0f11ff01ff89ff4798ff000098ff0f11ad0000895b0798c7f8fff8fff198c6d8e6d8e6f798c7f8ff98c7f198c698c698c6e798c798ff98ffff98c699ef99efe798c798ff98fff198c698e698e6e798c798c7f8fff198c698c698c6e780ff80ff80ffff81ff81ff81ffc780ff80ff80fff180f680f680f6c) else (if i < 61 then 0x7e0f8f8fff8fff1e0f0f0f4f0f4f7e0f8f8ffe0f8f1e0f0e0f0e0f0d7e0f8e0ffe0ffffe0f0e1fde1fdd7e0f8e0ffe0fff1e0f0e0f4e0f4d7e0f8e0f8f8fff1e0f0e0f0e0f0d798ffffff98ffffbbffffffddfff798ff98ffffffffddffddfffffff798ff98ff98ffff99ff99ff99ffe798ff98ff98fff198f698f698f6e798ff98ff98c7ff99df99df98c6e798ff98ff98c7f198d698d698c6e798ff98ff00ff0e89ff89ff01ff4 else 0x7e0ffffffe0ffffebfffffff5fff7e0ffe0fffffffff5fff5fffffff7e0ffe0ffe0ffffe1ffe1ffe1ffd7e0ffe0ffe0fff1e0f6e0f6e0f6d7e0ffe0ffe0f8ffe1fbe1fbe0f0d7e0ffe0ffe0f8f1e0f2e0f2e0f0d7e0ffe0ff00ff0ea1ffa1ff01ff47e0ffe0ff00000ea15ba15b000007e0ffe0f8e0ffffe1fde0f0e1fbd7e0ffe0f8e0fff1e0f4e0f0e0f2d7e0ff00ffe0ff0f41ff01ffa1ff47e0ff0000e0ff0f41ad0000a15b0)) else (if i < 64 then (if i < 63 then 0x7f8fff8ff000000a852a852000007f8ffe0fff8fff1f0f6e0f6e8f6d7f8ffe0ffe0fff1f8f6e8f6e8f6d7f8ffe0f8f8fff1f8f6e8f2e8f2d7f8ffe0f8f8fff1f0f4e0f0e8f2d7f8ffe0f8e0f8f1e0f0e0f0e0f0d7f8ff98fff8fff1d8f698f6b8f6e7f8ff98ff98fff1f8f6b8f6b8f6e7f8ff98c7f8fff1f8f6b8d6b8d6e7f8ff98c7f8fff1d8e698c6b8d6e7f8ff98c798c7f198c698c698c6e7f8ff0000f8ff0150a40000a8520 else 0x7f8fffffff8fff1faf6fffffcf6f7f8fff8fffffff1fcf6fcf6fffff7f8fff8fff8fffff9fff9fff9fff7f8fff8fff8fff1f8f6f8f6f8f6f7f8fff8fff8fff1f8f6e8f2e8f2d7f8fff8fff8fff1f8f6b8d6b8d6e7f8fff8ffe0fff1e8f6e8f6e0f6d7f8fff8ffe0f8f1f8f6e8f2e8f2d7f8fff8ffe0f8f1e8f2e8f2e0f0d7f8fff8ff98fff1b8f6b8f698f6e7f8fff8ff98c7f1f8f6b8d6b8d6e7f8fff8ff98c7f1b8d6b8d698c6e) else (if i < 65 then 0x800000000ff000000000000000007ffffffff00fffffffffffffffff7ffffffff00000eab5bab5b000007fffff8fff8fff1fffffaf6faf6f7ffffe0ffe0ffffffffebffebffd7ffff98ff98ffffffffbbffbbffe7ffff00fffffffffffffffffffff7ffff00ff00ff0fffffabffabffc7ffff00ff00000eab5bab5b000007ffff0000ffff0f55ad0000ab5b07ffff000000ff0f55ad0000ab5b07ff0000ff00ff0ffe00abadabadc else (if i < 66 then 0x80000fffffffff0000055ad55ad780000ffffff00f0aa52ffff54a4f80000ffffff00f0000055ad54a4780000ff00fffff154a454a4fffff80000ff00fffff0000054a455ad780000ff00ff00f154005400fe00b80000ff00ff00f0aa00fe005400b80000ff00ff00f0000054005400380000ff0000000000000000000008000067006700000000440044001800001f001f0000000014001400280000070007000e0000050905090 else 0x80700ff000700f0ae00fe005600b80700673807000e2719673947291807001f0707000e0f0b1f0f170d2807000700ffffff57ad57adfffff807000700ff00f156005600fe00b80700070067380e47294729673918070007001f070e170d170d1f0f280700070007000e0709070907090807000700070000060006000600080700070000000e030903090000080700000007000e0509000003090800ffff00ff00f001ff545254523))))))) else (if i < 100 then (if i < 83 then (if i < 75 then (if i < 71 then (if i < 69 then (if i < 68 then 0x81f00ff00ff00f01e005e005e00381f00ff00ff00f0140054005e00381f00ff00ff00f00a005e005400381f00ff001f00f0be00fe005e00b81f009f009f00f01e001e001e00281f001f00ff00f15e005e00fe00b81f001f001f00f01e005e005e00b81f001f001f00001e001e001e00281f001f000000000a000a000000081f0000001f0000140000000a00080700ffff0700feaf5bffff57adf80700ff00ff00f00600560056003 else 0x86700ff00ff00f0220076005400386700ff006700f0ee00fe007600b86700e700e700f06600660066001867006700ff00f176007600fe00b8670067006700f0660076007600b86700670067000066006600660018670067000000002200220000000867000000670000440000002200081f07070007000e1f0f0f0b0f0b081f00ff00ff00f1fe00fe00fe00b81f00ff00ff00f15e005e00fe00b81f00ff00ff00f0be00fe005e00b) else (if i < 70 then 0x987c087c087c0ff87c987c987c9c9870087008700f1860086008600887f00ff00ff00f07e007e007e00387f00ff007f00f0fe00fe007e00b87f007f00ff00f17e007e00fe00b87f007f007f00007e007e007e00386738070007000e673927192719086700ff00ff00f1fe00fe00fe00b86700ff00ff00f176007600fe00b86700ff00ff00f0ee00fe007600b86700ff00ff00f0660076007600386700ff00ff00f04400540076003 else 0x9ff000000ff000154000000aa0009ff00000000000000000000000009e700ff00ff00f1e600f600f600b9e700ff00e700f1ee00fe00f600b9e700e700ff00f1f600f600fe00b9e700e700e700f1e600e600e60099e000ff00ff00f1e000f400f400b99f00ff00ff00f19e00de00de00b99f00ff009f00f1be00fe00de00b99f009f00ff00f1de00de00fe00b99f009f009f00f19e009e009e00a99800ff00ff00f19800dc00dc00b)) else (if i < 73 then (if i < 72 then 0x9ff006700ff00f176007600fe00b9ff006700ff000176006600ee0019ff006700670001fe00ee00ee0099ff001f00ff00f1fe00fe00fe00b9ff001f00ff00f15e005e00fe00b9ff001f00ff00015e001e00be0029ff001f001f0001fe00be00be00a9ff0000ffff0001545201ffaaa449ff000000fffff154a454a4fffff9ff000000ffff0154a40000ab5b09ff000000ff00f154005400fe00b9ff000000ff0001fe00aa00aa008 else 0x9ff00ff001f0000be00be001e0029ff00ff0000ff00aaa4aaa401ff49ff00ff000000f0aa00fe005400b9ff00ff00000001fe00aa00aa0089ff00ff00000000aa00aa00000009ff00e700ff00f1f600e600ee0099ff00e700e700f1fe00ee00ee0099ff00e000ff00f1f400e000ea0099ff009f00ff00f1de009e00be00a9ff009f009f00f1fe00be00be00a9ff009800ff00f1dc009800ba00a9ff006700ff00f1fe00fe00fe00b) else (if i < 74 then 0x9ff00ff00ff00f0aa00fe00540039ff00ff00ff00f000005400540039ff00ff00ff0001fe00aa00aa0009ff00ff00e700f1ee00ee00e60099ff00ff00e000f1ea00ea00e00099ff00ff009f00f1be00be009e00a9ff00ff009800f1ba00ba009800a9ff00ff006700f1fe00fe00fe00b9ff00ff006700f0ee00fe007600b9ff00ff00670000ee00ee00660019ff00ff001f00f1fe00fe00fe00b9ff00ff001f00f0be00fe005e00b else 0x9ff00ff00ff00f1fe00ba00ba00a9ff00ff00ff00f1f400f400fe00b9ff00ff00ff00f1ea00fe00f400b9ff00ff00ff00f1dc00dc00fe00b9ff00ff00ff00f1ba00fe00dc00b9ff00ff00ff00f176007600fe0039ff00ff00ff00f15e005e00fe0039ff00ff00ff00f154005400fe00b9ff00ff00ff00f154005400fe0039ff00ff00ff00f0ee00fe00760039ff00ff00ff00f0be00fe005e0039ff00ff00ff00f0aa00fe005400b))) else (if i < 79 then (if i < 77 then (if i < 76 then 0x9ff00ff00ff00f1fe50fe50fe00b9ff00ff00ff00f1fe42fe42fe00b9ff00ff00ff00f1fe20fe00fe10b9ff00ff00ff00f1fe10fe10fe00b9ff00ff00ff00f1fe04fe00fe02b9ff00ff00ff00f1fe02fe02fe00b9ff00ff00ff00f1fe00fea4fea4f9ff00ff00ff00f1fe00fe20fe20b9ff00ff00ff00f1fe00fe04fe04b9ff00ff00ff00f1fe00fe00fe00b9ff00ff00ff00f1fe00fe00fe0039ff00ff00ff00f1fe00ea00ea009 else 0x9ff00ff00ffc7f1fe84fe84fec6f9ff00ff00ffc7f1fe84fe00fe42b9ff00ff00ff38f1fe20fe20ff39b9ff00ff00ff38f1fe20fe20fe30b9ff00ff00ff07f1fe04fe04ff0fb9ff00ff00ff07f1fe04fe04fe06b9ff00ff00ff00ffff09ff09ff09b9ff00ff00ff00f1fef6fe52fe52b9ff00ff00ff00f1fea4fe00fe52b9ff00ff00ff00f1fea0fe00fe50b9ff00ff00ff00f1fe84fe00fe42b9ff00ff00ff00f1fe52fe52fe00b) else (if i < 78 then 0x9ff00fff8ff00f1fe50fe50fe00b9ff00ffc7ff00f1fe42fec6fe84f9ff00ffc7ff00f1fe42fe42fe00b9ff00ff38ff00f1fe10ff39fe20b9ff00ff38ff00f1fe10fe30fe20b9ff00ff07ff00f1fe02ff0ffe04b9ff00ff07ff00f1fe02fe06fe04b9ff00ff00fffff1fea4fea4fffff9ff00ff00fffff1fea4fe00ff5bb9ff00ff00fffff1fe00fea4ffadf9ff00ff00fff8f1fea0fea0fef0f9ff00ff00fff8f1fea0fe00fe50b else 0x9ffc0ff00ff00f1fec0fe40fe40b9ff38ff00ff00f1ff39fe10fe10b9ff38ff00ff00f1fe30fe10fe10b9ff07ff00ff00f1ff0ffe02fe02b9ff07ff00ff00f1fe06fe02fe02b9ff00fffffffff1fef6fffffffff9ff00ffffff00f1fe52fffffea4f9ff00ffffff00f1fe52ff5bfe00b9ff00ffffff00f1fe00ffadfea4f9ff00ffff0000f0aa52ffff54a4f9ff00ffff000000aa52ab5b000009ff00fff8ff00f1fe50fef0fea0f)) else (if i < 81 then (if i < 80 then 0x9ffff0000ffff0155ad0000ab5b09ffff0000ff0001ffffaa52aa5289ffff0000ff000155ad0000aa5209fff8ff00ff00f1fef0fe50fe50b9fff8ff00ff00f1fea0fe00fe50b9fff8ff00ff00f1fe50fe50fe00b9ffc7ff00ff00f1fec6fe42fe42b9ffc7ff00ff00f1fe84fe00fe42b9ffc7ff00ff00f1fe42fe42fe00b9ffc0ffc0ffc0f1fec0fec0fec0f9ffc0ffc0ff00f1fe40fe40fe00b9ffc0ff00ffc0f1fe80fe00fe40b else 0xa00001f0700000e0000010900000a000000001f070e00000000010909ffffffffff00f1fffffffffef6f9ffffffff000000ab5bab5b000009ffffff00fffff1fffffef6fffff9ffffff00ff00f1fffffe52fe52b9ffffff00ff00f1ffadfe00fe52b9ffffff00ff00f1ff5bfe52fe00b9ffffff00ff00f1fef6fe52fe52b9ffffff00000001ffffaa52aa5289ffffff00000000ab5baa52000009ffff070007000fffffaf5baf5b8) else (if i < 82 then 0xa1f0700001f070e150d00000b0b0a1f07000000000e0109000000000a1f001f071f070e1e001f0d1f0d2a18071f071f070e18061d0f1d0f2a0707070707070e070f070f070f0a0000fffffffffe000055ad55ad7a0000ffff1f07fe000055ad55ad7a0000ffc7ffc7f00000548454847a0000ff07ff07fe0000550d550d3a00009fc79fc7fe0000158d158d6a00001f07fffffe000055ad55ad7a00001f071f070e0000150d150d2 else 0xa1f071f071f070ebf5fbf5f1f0faa1f071f071f070e1f0f1f0f1f0f2a1f071f071f070e1f0f0b0b0b0b0a1f071f071f070e150d150d1f0f2a1f071f071f070e0b0b1f0f150d2a1f071f071f07001e061e061e062a1f071f071f000e1f0b1f0b1e002a1f071f0718070e1b0f1b0f18062a1f071f0700000e0b0b0b0b00000a1f071f001f070e1f0d1e001f0b2a1f0718071f070e1d0f18061b0f2a1f070000ffff0f55ad0000ab5b0)))) else (if i < 91 then (if i < 87 then (if i < 85 then (if i < 84 then 0xa1f07ffff00000eab5bab5b00000a1f07ff07ff07fe1f0f5f0f5f0f3a1f07e0f81f07feb55de0f04babda1f079fc79fc7fe1f0f1f8f1f8f6a1f077f3f1f070e3f1f7f3f5f2f3a1f071fff1f070e1f5f1fff1faf6a1f071f07ffffff5faf5faffffffa1f071f07e0f8ff4bab4babe0f0da1f071f077f3f0e5f2f5f2f7f3f3a1f071f071fff0e1faf1faf1fff6a1f071f071f07fe1f0f5faf5faffa1f071f071f070f5faf1f0fbf5fa else 0xb9f079f079f07ff9f0f9f0f9f0fab9f079f079f07f19e069e069e06ab98c7ffc7ffc7f198c6dcc6dcc6fb98c7ffc798c7f198c698c698c6eb98c79fc79fc7ff98c69dcf9dcfeb98c79fc79fc7f198c69cc69cc6eb98c798c7ffc7f198c698c698c6ea7f3f1f071f070e7f3f3f1f3f1f2a67c767c767c70066c666c666c65a1fff1f071f070e1fff1f5f1f5f2a1f07fffffffffffffffffffffffa1f07ffff1f07febf5fffff5faff) else (if i < 86 then 0xb9fc7ffff9fc7ffbfdfffffdfeffb9fc79fc7ffffffdfefdfeffffffb9fc79fc79fc7ff9fcf9fcf9fcfeb9fc79fc79fc7f19ec69ec69ec6eb9fc79fc798c7ff9bcf9bcf98c6eb9fc79fc798c7f19ac69ac698c6eb9fc79fc71f070e9f4f9f4f1f0f2b9fc79fc700000e8b4b8b4b00000b9fc798c79fc7ff9dcf98c69bcfeb9fc798c79fc7f19cc698c69ac6eb9fc71f079fc70f1f8f1f0f9f4f2b9fc700009fc70f158d00008b4b0 else 0xbff07ff071f070ebf0fbf0f1f0f2bff07ff0700000eab0bab0b00000bff07ff00ff07ffff0dfe00ff0bbbff07ff00ff07f1fe04fe00fe02bbff071f07ff070f5f0f1f0fbf0f2bff070000ff070f550d0000ab0b0bff00ffc7ffc7f1fe00fe84fe84fbff00ffc7ff00f1fe00fe00fe00bbff00ff07ff07fffe00ff0dff0dbbff00ff07ff07f1fe00fe04fe04bbff00ff00ffc7f1fe00fe00fe00bbe0f81f071f070fe0f0b55db55da)) else (if i < 89 then (if i < 88 then 0xbffc79fc7ffc7f1dec69ec6bec6ebffc79fc79fc7f1fec6bec6bec6ebffc798c7ffc7f1fec6bac6bac6ebffc798c7ffc7f1dcc698c6bac6ebffc798c798c7f198c698c698c6ebffc70000ffc70154840000aa420bff07ffffff07ffff5fffffffaffbff07ff07ffffffffafffaffffffbff07ff07ff07ffff0fff0fff0fbbff07ff07ff07f1fe06fe06fe06bbff07ff07ff00ffff0bff0bfe00bbff07ff07ff00f1fe02fe02fe00b else 0xbffc7ffc7ff07f1fe46fe46fe06bbffc7ffc7ff00f1fec6fe42fe42bbffc7ffc7ff00f1fe42fe42fe00bbffc7ffc79fc7f1bec6bec69ec6ebffc7ffc798c7f1fec6bac6bac6ebffc7ffc798c7f1bac6bac698c6ebffc7ffc7000000aa42aa4200000bffc7ff07ffc7f1fe86fe06fe46bbffc7ff07ff07f1fec6fe46fe46bbffc7ff00ffc7f1fec6fe42fe42bbffc7ff00ffc7f1fe84fe00fe42bbffc7ff00ff00f1fe00fe00fe00b) else (if i < 90 then 0xbffff9fc79fc7ffffffbfdfbfdfebffff1f07fffffffffffffffffffbffff1f071f070fffffbf5fbf5fabffff1f0700000eab5bab5b00000bffff0000ffff0f55ad0000ab5b0bffff00001f070f55ad0000ab5b0bffc7ffffffc7f1fed6fffffee6fbffc7ffc7fffff1fee6fee6fffffbffc7ffc7ffc7ffffcfffcfffcffbffc7ffc7ffc7f1fec6fec6fec6fbffc7ffc7ffc7f1fec6fe42fe42bbffc7ffc7ffc7f1fec6bac6bac6e else 0xc0000ffff6738fe000055ad55ad7c0000fff8fff8f0000054a054a07c0000ff38ff38fe0000552955293c0000e7f8e7f8fe000045a945a95c00006738fffffe000055ad55ad7c0000673867380e0000452945291c0000673800000e0000010900000c0000000067380e0000000001090bffffffff1f07fffffffffffffffbffffffff00000eab5bab5b00000bffffffc7ffc7f1fffffed6fed6fbffffff07ff07ffffffff5fff5fb))) else (if i < 95 then (if i < 93 then (if i < 92 then 0xc6738673860380e6339633960301c6738673800000e2319231900000c6738670067380e6729660067191c6738603867380e6539603063391c67380000ffff0f55ad0000ab5b0c6738000067380e4529000023190c6738000000000e0109000000000c6700673867380e6600672967291c6038673867380e6030653965391c1ff81ff81ff8001ef01ef01ef06c0738073807380e0739073907390c0000fffffffffe000055ad55ad7 else 0xc6738673898c7ff339d339d98c6ec673867387f3f0e773d773d7f3f3c6738673867ff0e67bd67bd67ff5c673867386738fe673977bd77bdfc6738673867380f77bd6739ef7b9c6738673867380eef7bef7b67399c6738673867380e6739673967391c6738673867380e6739231923190c6738673867380e4529452967391c6738673867380e2319673945291c673867386738006630663066301c6738673867000e6719671966001) else (if i < 94 then 0xd98c7673867380f98c6cd6bcd6b9c7f3f673867380e7f3f6f3b6f3b1c67ff673867380e67ff677b677b1c6738fffffffffffffffffffffffc6738ffff6738feef7bffff77bdfc6738ffff00000eab5bab5b00000c6738ff38ff38fe6739773977393c6738e7f8e7f8fe673967b967b95c673898c76738fecd6b98c6339dec67387f3f67380e6f3b7f3f773d3c673867ff67380e677b67ff67bd5c67386738ffffff77bd77bdfffff else 0xde7f8e7f800000ea359a35900000de7f8e0f8e7f8ffe5f9e0f0e3f9dde7f8e0f8e7f8f1e4f0e0f0e2f0dde7f86738e7f80f67b96739e7791de7f80000e7f80f45a90000a3590de738e738e738ffe739e739e7399de738e738e738f1e630e630e6309de0f8fff8fff8f1e0f0f4f0f4f0fde0f8fff8e0f8f1e0f0e0f0e0f0dde0f8e7f8e7f8ffe0f0e5f9e5f9dde0f8e7f8e7f8f1e0f0e4f0e4f0dde0f8e0f8fff8f1e0f0e0f0e0f0d)) else (if i < 97 then (if i < 96 then 0xdff00fff8fff8f1fe00fea0fea0fdff00fff8ff00f1fe00fe00fe00bdff00ff38ff38fffe00ff29ff29bdff00ff38ff38f1fe00fe20fe20bdff00ff00fff8f1fe00fe00fe00bde7f8ffffe7f8ffeffbfffff7fdfde7f8e7f8fffffff7fdf7fdfffffde7f8e7f8e7f8ffe7f9e7f9e7f9dde7f8e7f8e7f8f1e6f0e6f0e6f0dde7f8e7f8e0f8ffe3f9e3f9e0f0dde7f8e7f8e0f8f1e2f0e2f0e0f0dde7f8e7f867380ee779e77967391 else 0xdff38ffffff38ffff7bffffffbdfdff38ff38ffffffffbdffbdfffffdff38ff38ff38ffff39ff39ff39bdff38ff38ff38f1fe30fe30fe30bdff38ff38ff00ffff19ff19fe00bdff38ff38ff00f1fe10fe10fe00bdff38ff3867380eef39ef3967391dff38ff3800000eab19ab1900000dff38ff00ff38ffff29fe00ff19bdff38ff00ff38f1fe20fe00fe10bdff386738ff380f77396739ef391dff380000ff380f55290000ab190) else (if i < 98 then 0xdfff8fff8000000aa50aa5000000dfff8ff38fff8f1feb0fe30fe70bdfff8ff38ff38f1fef0fe70fe70bdfff8ff00fff8f1fef0fe50fe50bdfff8ff00fff8f1fea0fe00fe50bdfff8ff00ff00f1fe00fe00fe00bdfff8e7f8fff8f1f6f0e6f0eef0ddfff8e7f8e7f8f1fef0eef0eef0ddfff8e0f8fff8f1fef0eaf0eaf0ddfff8e0f8fff8f1f4f0e0f0eaf0ddfff8e0f8e0f8f1e0f0e0f0e0f0ddfff80000fff80154a00000aa500 else (if i < 99 then 0xdfff8fffffff8f1fef2fffffef4fdfff8fff8fffff1fef4fef4fffffdfff8fff8fff8fffff9fff9fff9fdfff8fff8fff8f1fef0fef0fef0fdfff8fff8fff8f1fef0fe50fe50bdfff8fff8fff8f1fef0eaf0eaf0ddfff8fff8ff38f1fe70fe70fe30bdfff8fff8ff00f1fef0fe50fe50bdfff8fff8ff00f1fe50fe50fe00bdfff8fff8e7f8f1eef0eef0e6f0ddfff8fff8e0f8f1fef0eaf0eaf0ddfff8fff8e0f8f1eaf0eaf0e0f0d else 0xe00000000ffff0e0000000001090e0000000000000e0000000000000dffffffff6738fffffffffffffffdffffffff00000eab5bab5b00000dfffffff8fff8f1fffffef2fef2fdffffff38ff38ffffffff7bff7bbdffffe7f8e7f8ffffffeffbeffbddffff6738fffffffffffffffffffdffff673867380fffffef7bef7b9dffff673800000eab5bab5b00000dffff0000ffff0f55ad0000ab5b0dffff000067380f55ad0000ab5b0)))))) else (if i < 117 then (if i < 108 then (if i < 104 then (if i < 102 then (if i < 101 then 0xe0000e0f8fffffe000040a041a95e000098c7fffffe00001084118d6e00007f3f7f3f0e0000552d552d3e000067ff67ff0e000045ad45ad5e00006738ffff0e0000452945291e00001fff1fff0e000015ad15ad6e00001f07ffff0e0000150d150d2e000000ffffff0e000001ad01ad4e00000000ffffff54a454a4fffffe00000000fffffe000054a455ad7e00000000ffff0f54a40000ab5b0e00000000ffff0eaa52aa5201098 else 0xe0000ffffff00fe0000550954003e0000ffffe0f8fe000041a940a05e0000ffff98c7fe0000118d10846e0000ffff67380e0000452945291e0000ffff1f070e0000150d150d2e0000ffff00ff0e000001ad01ad4e0000ffff0000feaa52ffff54a4fe0000ffff0000fe000055ad54a47e0000ffff00000f54a40109aa528e0000ffff00000eaa52ab5b00000e0000ffff00000e0000010900000e0000ff00fffffe0000540055093) else (if i < 103 then 0xe0000fffffffffe140455ad5faf7e0000fffffffffe0a025faf55ad7e0000fffffffffe010955ad55ad7e0000fffffffffe00a455ad55ff7e0000fffffffffe005255ff55ad7e0000fffffffffe000055ad55adfe0000fffffffffe000055ad55ad7e0000fffffffffe0000550955093e0000fffffffffe000041a941a95e0000fffffffffe0000118d118d6e0000fffffffff0000054a454a47e0000ffffffff0e0000010901090 else 0xe0000ffffffffff54a455adfffffe0000ffffffffff54a455adffff7e0000ffffffffff540055adffadfe0000ffffffffff40a055adf5fdfe0000ffffffffff108455adddeffe0000fffffffffeaa52ffff55adfe0000fffffffffeaa52ffff55ad7e0000fffffffffeaa00ffad55adfe0000fffffffffea050f5fd55adfe0000fffffffffe8842ddef55adfe0000fffffffffe442055ad77bd7e0000fffffffffe221077bd55ad7)) else (if i < 106 then (if i < 105 then 0xe00fffffffffffe01ad55ad55ff7e00fffffffffffe015b55ff55ad7e00fffffffffffe010955ad55ad7e00ffffff00ff0e01ff01ff01ff4e00ffffff00000e015b015b00000e00ff00ffffff0e01ff01ff01ff4e00ff0000ffff0e01ad0000015b0e00f8fffffffffe00f055fd55fd7e00c7fffffffffe00c655ef55ef7e0038fffffffffe013955bd55bd7e0007fffffffffe010f55af55af7e0000fffffffffffef6fffffffff else 0xe1f07fffffffffe010955ad55ad7e1f07ffff1f070e1f0f1f0f1f0f2e1f07ffff00000e0b0b0b0b00000e1f071f07ffff0e1f0f1f0f1f0f2e1f070000ffff0e150d00000b0b0e1f00fffffffffe1e005fad5fad7e1807fffffffffe18065daf5daf7e07ff07ff07ff0e07ff07ff07ff4e0700fffffffffe070957ad57ad7e00ffffffffffff55ff55fffffffe00fffffffffffeabffffff55fffe00fffffffffffe01ff55ff55ff7) else (if i < 107 then 0xe1ffffffffffffe1fff5fff5fff7e1fffffff1ffffebfffffff5ffffe1fff1fffffffff5fff5ffffffffe1fff1fff1fff0e1fff1fff1fff6e1fff1fff00000e0b5b0b5b00000e1fff00001fff0e15ad00000b5b0e1f3f1f3f1f3f0e1f3f1f3f1f3f2e1f07ffffffffff5faf5faffffffe1f07fffffffffebf5fffff5faffe1f07fffffffffe1f0f5faf5faf7e1f07fffffffffe150d55ad5faf7e1f07fffffffffe0b0b5faf55ad7 else 0xe6738ffffffffff77bd77bdfffffe6738fffffffffeef7bffff77bdfe6738fffffffffe673977bd77bd7e6738fffffffffe452955ad77bd7e6738fffffffffe231977bd55ad7e6738fffffffffe010955ad55ad7e6738ffff67380e6739673967391e6738ffff00000e2319231900000e67386738ffff0e6739673967391e67380000ffff0e4529000023190e6700fffffffffe660077ad77ad7e6038fffffffffe603075bd75bd7))) else (if i < 112 then (if i < 110 then (if i < 109 then 0xe7f3fffff7f3ffeff7fffff7fbffe7f3f7f3fffffff7fbf7fbffffffe7f3f7f3f7f3f0e7f3f7f3f7f3f3e7f3f7f3f00000e2b1b2b1b00000e7f3f00007f3f0e552d00002b1b0e67fffffffffffe67ff77ff77ff7e67ffffff67fffeefffffff77fffe67ff67ffffffff77ff77fffffffe67ff67ff67ff0e67ff67ff67ff5e67ff67ff00000e235b235b00000e67ff000067ff0e45ad0000235b0e673f673f673f0e673f673f673f1 else 0xf98c7ffffffffff98c6ddefddefff98c7ffffffffff108455adddef7f98c7fffffffffe8842ddef55ad7f98c7fffffffffe000055ad55ad7f98c7ffff98c7ff98c699cf98c6ef98c7ffff00000e8842894b00000f98c798c7ffffff98c698c699cfef98c70000ffff0f10840000894b0f9800ffffffffff9800ddadddadff80c0ffffffffff80c0d5edd5edfe7fff7fff7fff0e7fff7fff7fff7e7f3ffffffffffe7f3f7fbf7fbf7) else (if i < 111 then 0xfe0f8fffffffffe000055ad55ad7fe0f8ffffe0f8ffe0f0e1f9e0f0dfe0f8ffff00000ea050a15900000fe0f8e0f8ffffffe0f0e0f0e1f9dfe0f80000ffff0f40a00000a1590fe000ffffffffffe000f5adf5adff9fff9fff9fffff9fff9fff9fffef9fff9fff9ffff19ef69ef69ef6ef9fc7ffffffffff9fcfdfefdfefff98ffffffffffff99ffddffddffff98c7ffffffffffdce6ddefffffff98c7ffffffffffbad6ffffddeff else 0xfff00ff00fffffffe00fe00ff09bfff000000ffff0f54000000ab090ff8fffffffffffff8f6fdfffdffffe7ffe7ffe7ffffe7ffe7ffe7ffdfe7ffe7ffe7fff1e6f6e6f6e6f6dfe7f8ffffffffffe7f9f7fdf7fdffe0ffffffffffffe1fff5fff5ffffe0f8fffffffffff4f4f5fdffffffe0f8ffffffffffeaf2fffff5fdffe0f8ffffffffffe0f0f5fdf5fdffe0f8ffffffffff40a055adf5fd7fe0f8fffffffffea050f5fd55ad7)) else (if i < 114 then (if i < 113 then 0xfff3fff3fff3fffff3fff3fff3fbfff3fff3fff3ff1fe36fe36fe36bfff38ffffffffffff39ffbdffbdffff07ffffffffffff0fffafffafffff00fffffffffffea4ffadffffffff00fffffffffffe52ffffffadffff00fffffffffffe00ffadffadffff00ffffffffff540055adffad7fff00fffffffffeaa00ffad55ad7fff00fffffffffe000055ad55ad7fff00ffffff00fffe00ff09fe00bfff00ffff00000eaa00ab0900000 else 0xfffff0000e0f80f41a90000a0500fffff000098c70f118d000088420fffff000067380e4529000023190fffff00001f070e150d00000b0b0fffff000000ff0e01ad0000015b0fffff00000000fe010954a454a4ffffff000000000fffffaa52aa528fffff000000000f55ad0000aa520fffff000000000eab5baa5200000fffff000000000e0109000000000ffff8fffffffffffef0fffdfffdffffc7fffffffffffec6ffefffeff) else (if i < 115 then 0xfffff0000ffff0f55ad00a4abff4fffff0000ffff0f55ad0000ab5b8fffff0000ffff0f55ad0000ab5b0fffff0000ffff0f55090000ab090fffff0000ffff0f41a90000a1590fffff0000ffff0f118d0000894b0fffff0000ffff0e4529000023190fffff0000ffff0e150d00000b0b0fffff0000ffff0e01ad0000015b0fffff0000ffff0e0109000001090fffff0000ffff0154a40000aa520fffff0000ff000f55090000aa000 else (if i < 116 then 0xfffff0000ffffff55ad1084bbdfefffff0000ffff0fffffaa52ab5b8fffff0000ffff0fffffaa52ab5b0fffff0000ffff0fffadaa00ab5b8fffff0000ffff0ff5fda050ab5b8fffff0000ffff0fddef8842ab5b8fffff0000ffff0f77bd2210ab5b0fffff0000ffff0f5faf0a02ab5b0fffff0000ffff0f55ff0052ab5b0fffff0000ffff0f55ad4420ef7b1fffff0000ffff0f55ad1404bf5f2fffff0000ffff0f55ad0109ab5b0 else 0xfffff00ffffff0f55ad0109ab5b0fffff00ff00ff0e01ff01ff01ff4fffff00ff00000e015b015b00000fffff00f8ffff0f55fd00f0abfb4fffff00c7ffff0f55ef00c6abdf4fffff0038ffff0f55bd0139ab7b0fffff0007ffff0f55af010fab5f0fffff0000fffffffffffef6ffffffffff0000ffffff55ad54a4ffffffffff0000ffffff55ad54a4ffff7fffff0000ffffff55ad5400ff5bbfffff0000ffffff55ad40a0ebfbd))))) else (if i < 125 then (if i < 121 then (if i < 119 then (if i < 118 then 0xfffff1f07ffff0f55ad150dbf5f2fffff1f07ffff0f55ad0109ab5b0fffff1f071f070e1f0f1f0f1f0f2fffff1f0700000e0b0b0b0b00000fffff1f00ffff0f5fad1e00bf5b2fffff1807ffff0f5daf1806bb5f2fffff0700ffff0f57ad0709af5b0fffff00ffffffff55ff55ffffffffffff00ffffff0fffffabffabffcfffff00ffffff0f55ff01ffabff4fffff00ffffff0f55ff015bab5b0fffff00ffffff0f55ad01adabff4 else 0xfffff6738ffff0f55ad4529ef7b1fffff6738ffff0f55ad0109ab5b0fffff673867380e6739673967391fffff673800000e2319231900000fffff6700ffff0f77ad6600ef5b1fffff6038ffff0f75bd6030eb7b1fffff1fffffff0f5fff1fffbfff6fffff1fff1fff0fffffbfffbfffefffff1f07ffffff5faf5fafffffffffff1f07ffff0fffffbf5fbf5fafffff1f07ffff0f5faf1f0fbf5f2fffff1f07ffff0f5faf0b0bab5b0) else (if i < 120 then 0xfffff98c798c7ff99cf98c698c6efffff98c700000e894b884200000fffff9800ffffffddad9800bb5bafffff80c0ffffffd5ed80c0abdbcfffff7f3fffff0f7fbf7f3fff7f3fffff7f3f7f3f0fffffff7fff7fbfffff67ffffff0f77ff67ffefff5fffff67ff67ff0fffffefffefffdfffff6738ffffff77bd77bdffffffffff6738ffff0fffffef7bef7b9fffff6738ffff0f77bd6739ef7b1fffff6738ffff0f77bd2319ab5b0 else 0xfffffe0f8e0f8ffe1f9e0f0e0f0dfffffe0f800000ea159a05000000fffffe000fffffff5ade000eb5b9fffff9fc7ffffffdfef9fcfbfdfefffff98ffffffffddff99ffbbffefffff98c7ffffffffffbad6bbdfefffff98c7ffffffddefdce6ffffffffff98c7ffffffddef98c6bbdfefffff98c7ffffff55ad1084bbdf6fffff98c7fffff1dce698c6bad6efffff98c7ffff0fddef8842ab5b0fffff98c7ffff0f55ad0000ab5b0)) else (if i < 123 then (if i < 122 then 0xfffffff00ff00ffff09fe00fe00bfffffff0000000eab09aa0000000ffffff8fffffffffdfff8f6fbffffffffe7f8fffffff7fde7f9effbdfffffe0fffffffff5ffe1ffebffdfffffe0f8ffffffffffeaf2ebfbdfffffe0f8fffffff5fdf4f4ffffffffffe0f8fffffff5fde0f0ebfbdfffffe0f8ffffff55ad40a0ebfb5fffffe0f8fffff1f4f4e0f0eaf2dfffffe0f8ffff0ff5fda050ab5b0fffffe0f8ffff0f55ad0000ab5b0 else 0xfffffffff000000aa52aa5200000ffffffff8fffffffffdfef0fffbffffffffc7ffffffffeffec6ffdfffffffff38ffffffffbdff39ff7bbfffffff07ffffffffafff0fff5fbfffffff00fffffffffffe52ff5bbfffffff00ffffffffadfea4ffffffffffff00ffffffffadfe00ff5bbfffffff00ffffff55ad5400ff5b3fffffff00fffff1fea4fe00fe52bfffffff00ffff0fffadaa00ab5b0fffffff00ffff0f55ad0000ab5b0) else (if i < 124 then 0xfffffffff00000eab5bbf5f14042fffffffff00000eab5babff00a44fffffffff00000eab5bab5b01090fffffffff00000eab5bab5b00008fffffffff00000eab5bab5b00000fffffffff00000eab09ab0900000fffffffff00000ea159a15900000fffffffff00000e894b894b00000fffffffff00000e2319231900000fffffffff00000e0b0b0b0b00000fffffffff00000e015b015b00000fffffffff00000e0109010900000 else 0xfffffffff0000feab5bff5b5400bfffffffff0000feab5bebfb40a0dfffffffff0000feab5bbbdf1084efffffffff00000fffffab5baa528fffffffff00000fffffab5baa520fffffffff00000fff5bab5baa008fffffffff00000febfbab5ba0508fffffffff00000fbbdfab5b88428fffffffff00000eef7bab5b22100fffffffff00000ebf5fab5b0a020fffffffff00000eabffab5b00520fffffffff00000eab5bef7b44201))) else (if i < 129 then (if i < 127 then (if i < 126 then 0xfffffffff00ff0fffffabffabffcfffffffff00ff0eabffabff01ff4fffffffff00ff0eabffab5b015b0fffffffff00ff0eab5babff01ad4fffffffff00ff0eab5bab5b01090fffffffff00f80eabfbabfb00f04fffffffff00c70eabdfabdf00c64fffffffff00380eab7bab7b01390fffffffff00070eab5fab5f010f0fffffffff0000fffffffffffef6ffffffffff0000feab5bffff54a4ffffffffff0000feab5bffff54a47 else 0xfffffffff60380eeb7beb7b60301fffffffff1fff0ebfffbfff1fff6fffffffff1f07febf5fffff5fafffffffffff1f070fffffbf5fbf5fafffffffff1f070ebf5fbf5f1f0f2fffffffff1f070ebf5fab5b0b0b0fffffffff1f070eab5bbf5f150d2fffffffff1f070eab5bab5b01090fffffffff1f000ebf5bbf5b1e002fffffffff18070ebb5fbb5f18062fffffffff07000eaf5baf5b07090fffffffff00fffeabffffff55fff) else (if i < 128 then 0xfffffffff98c70eab5bab5b00000fffffffff9800ffbb5bbb5b9800afffffffff80c0ffabdbabdb80c0cfffffffff7f3f0eff7fff7f7f3f3fffffffff67ff0eefffefff67ff5fffffffff6738feef7bffff77bdffffffffff67380fffffef7bef7b9fffffffff67380eef7bef7b67391fffffffff67380eef7bab5b23190fffffffff67380eab5bef7b45291fffffffff67380eab5bab5b01090fffffffff67000eef5bef5b66001 else 0xfffffffffe0f8f1eaf2eaf2e0f0dfffffffffe0f80febfbab5ba0500fffffffffe0f80eab5bab5b00000fffffffffe000ffeb5beb5be0009fffffffff9fc7ffbfdfbfdf9fcfefffffffff98ffffbbffbbff99ffefffffffff98c7ffffffbbdfbad6efffffffff98c7ffbbdfffffdce6ffffffffff98c7ffbbdfbbdf98c6efffffffff98c7feab5bbbdf10846fffffffff98c7f1bad6bad698c6efffffffff98c70fbbdfab5b88420)) else (if i < 131 then (if i < 130 then 0xfffffffffff00ffff5bff5bfe00bfffffffffff00feab5bff5b54003fffffffffff00f1fe52fe52fe00bfffffffffff000fff5bab5baa000fffffffffff000eab5bab5b00000ffffffffff8fffffbfffbfff8f6ffffffffffe7f8ffeffbeffbe7f9dfffffffffe0ffffebffebffe1ffdfffffffffe0f8ffffffebfbeaf2dfffffffffe0f8ffebfbfffff4f4ffffffffffe0f8ffebfbebfbe0f0dfffffffffe0f8feab5bebfb40a05 else 0xfffffffffffff0fffffab5bab5b0fffffffffffff0f55ad0109ab5b8fffffffffffff0f55ad0109ab5b0fffffffffffff0eab5bab5b01098fffffffffffff0eab5bab5b01090fffffffffffff0e0109010901090ffffffffffff8fffffbfffbfef0ffffffffffffc7ffffdfffdffec6ffffffffffff38ffff7bff7bff39bfffffffffff07ffff5fff5fff0fbfffffffffff00ffffffff5bfe52bfffffffffff00ffff5bfffffea4f) else (if i < 132 then 0xfffffffffffffff55ad55adffff7ffffffffffffffeef7bffff77bd7ffffffffffffffebf5fffff5faf7ffffffffffffffeabffffff55ff7ffffffffffffffeab5bffff55adfffffffffffffffeab5bffff55ad7ffffffffffffffe010955ad55ad7ffffffffffffff1fef6fef6fef6ffffffffffffff0fffffef7bef7b1fffffffffffff0fffffbf5fbf5f2fffffffffffff0fffffabffabff4fffffffffffff0fffffab5bab5b8 else (if i < 133 then 0xfffffffffffffffffffebfbebfbdfffffffffffffffffffbbdfbbdfefffffffffffffffffadffadffffffffffffffffffffff5bffffffadfffffffffffffffff5fdf5fdffffffffffffffffffffebfbfffff5fdffffffffffffffffddefddefffffffffffffffffffffbbdfffffddefffffffffffffffff77bd77bdffff7fffffffffffffff5faf5fafffff7fffffffffffffff55ff55ffffff7fffffffffffffff55ad55adfffff else 0xfffffffffffffffffffffffffff7fffffffffffffffffffff5bff5bb))))))))
private def wireData (i : Nat) : Nat := unpack wireDataPacked 112 12 i
private def readSig (i : Nat) : Sig :=
  let a := wireData i
  (BitVec.ofNat 56 (a >>> 56), BitVec.ofNat 56 a)

private def sigHash (s : Sig) : Nat :=
  let h := (s.1.toNat * 0x517cc1b727220a95) ^^^ (s.2.toNat * 0x9e3779b97f4a7c15)
  let g := (h ^^^ (h >>> 57)) * 0xbf58476d1ce4e5b9
  (g ^^^ (g >>> 49)) &&& 0xffffffffffffffff

private def stateHash (s : SearchState) : Nat :=
  s.2.foldl (fun acc x => acc + sigHash x) (s.1 * 0x94d049bb133111eb)

private def decodeWires (code : Nat) : Nat → List Sig
  | 0 => []
  | n+1 => readSig (code &&& 2047) :: decodeWires (code >>> 11) n

private def st3Packed (_i : Nat) : Nat := 0x61e6f6954caa0c3cddd2a99541879bb25532a830f386494655061e70c918caa0c3ce192299541879c3255314830f3864aa615061e70c954c320
private def st3 (i : Nat) : Nat := unpack st3Packed 51 20 i
private def adj3Packed (_i : Nat) : Nat := 0xc
private def adj3 (i : Nat) : Nat := unpack adj3Packed 2 80 i
private def loc3Packed (_i : Nat) : Nat := 0x50000300000000007000000400000060000002001000000080000000000
private def loc3 (i : Nat) : Nat := unpack loc3Packed 4 80 i
private def st4Packed (i : Nat) : Nat := (if i < 1 then 0xc55879c325532aa314e1e70c954caa8c3d335c325532aa314cc870c954caa8c5f87dbda5532aa2e24af6f6954caa8c55885bba5532aa2ad4bd6ee954caa8c5388dbb25532aa317e1f70c928caa8b892bdc324a32aa31562170c918caa8ab52f5c324632aa314e2370c914caa8c5f87dc3255314a2e24af70c954c528c5388dc325530aa31562170c954c328ab52f5c325530ca2e5d6199b280ab28 else (if i < 2 then 0xb9758666c2e42aa314e2370c954d1a8c55885c3255344a317e1f70c954cfa8b9758666c6d32aa314e2370c98ccaa8c55885c326232aa317e1f70c97ccaa8c5388dca25532aa315621726954caa8c5f87dc825532aa314e2470c954caa8c5388dc325532aa31562270c954caa8c55885c325532aa314e2170c954caa8c5f881c325532aa317e1f70c954caa8c5387dc325532aa317e1e70c954caa8 else 0x61e6f6954caa1001879bba5532a840061e6ec954caa1001879c324a32a840061e70c918caa1001879c324532a840061e70c954c521001879c325530a840061e70c954c321c3ee192a995230a310b864aa65487a8b97586964cd1caa2e5d61a7733469a8c52e192a995130a2e5d61a9533464a8c5172eb0ccd18aa2e5d6199ad197e28b9758666b86588a2e5d6199afe92aa8))
private def st4 (i : Nat) : Nat := unpack st4Packed 62 20 i
private def adj4Packed (_i : Nat) : Nat := 0x632391174023100015101
private def adj4 (i : Nat) : Nat := unpack adj4Packed 4 80 i
private def loc4Packed (i : Nat) : Nat := (if i < 1 then 0x40004eb000968939c82014803000600021000c76d33a6f000038b4d25158bba3e9d0002157c6dce01c680000981005000790b192a2480a80d4f else 0x270300075c031b)
private def loc4 (i : Nat) : Nat := unpack loc4Packed 6 80 i
private def st5Packed (i : Nat) : Nat := (if i < 24 then (if i < 12 then (if i < 6 then (if i < 3 then (if i < 1 then 0xb9758666b865c856185cbac3335c32552b0c2e5d6199ae18fb158618bf0fb864aa6540e30c55885c325532a06d8629c46e192a995034c2e5d61a4ee192a955618a711b864aa65428b0c55885c325532a145862fc3ee192a9950a2c310dcb70c954ca84961712b0b864aa65424b0c5372dc325532a12185c499ae192a995090c317dcb70c954ca8476172eb0ccd84c9542230b9758666c9832a1118629c46e192a995028c31562170c954ca813618bf0fb864aa6540730 else (if i < 2 then 0xb9769266b865de58985cbb4933610a552c4c2e5da499ae192a9626172ed1ccd70c954b130b973362fb864aa58985cbb493359d2552c4c2e5da499ae19049626172eb0ccd70c954b030b9758666b864aa57d85cbac3335c32552bcc2e5d6199b2812a95d6172eb0ccd85c954aeb0b9758666c164aa57585cbac3335c32552bac2e5d6199aca12a95d6172eb0ccd70c954adb0b9758666b864aa56985cbac3335c32552b2c2e5d6199b281c31586172eb0ccd70cbf0ac30 else 0xb9758666b864aa5ed85cbac3335c32552f4c301d6199ae197b9766180eb0ccd852954bb30c0758666b864aa5d98602ac3335c32552ecc2b0ccd8b6e192a9766180eb0ccd670954bb30c0758666b8640e5d985cbac3335c32552eac2e5d6199ae192a9746172eb0ccd85c954b9b0b9758666b864aa5c985cbac3335c32552e2c2e5d6199ae197e1706172ed24cd70c954b7b0b9758666b864aa5b985cbac3335c32552dac2e5d6199ae192a96a6172eb0ccd70c954b4b0)) else (if i < 4 then 0xc5372eb0b864aa61585cbac3335c325530ac2e5d6199ae192a9896172eb0ccd70c954c430b9758666b864aa61d85cbac3335c326230cc2e5d6199ae4d2a9866172eb14cd70c954c330b9758666b864aa61985cbab5335c325530cc31556197ae192a9866172eb0ccd6ee954c330b9758666b8648c61985cbac3335c3255306c2e5d6199b0b92a9826172eb0ccd70c954c0b0b9758666b865f86018603ac3335c32552fec2e5d6199ae192a97e6172eb0ccd70c954beb0 else (if i < 5 then 0xb97335c325539e65585cbac3336501c232ac2e5d6199ae192a9946172eb0ccd70c954c9b0b9758666b864aa64985cbac3335c3255322c2e5d6199ae192a9906172eb0ccd70c954c7b0b9758666b864aa63985cbac3335c325531ac2e5d6199ae192a98c6172eb0ccd70c954c5b0b9758666b864be62985cbac3335c8255314c2e656199ae192a98a6172eb0ccd70c954c530b8958666b864aa629862fb972bdc3255314c2e5d6199aded2a98a6172eb0ccd70c928c530 else 0xb976f266b533f465585cbac3335c31f932ac2e5d6199ae18fc1956185eb0ccd6ce7e0cab0b9758666b863ee65585cbac3335c31f232ac2e5d6199ae18f89956172eb0ccd70c7b4cab0b97585c32553cc65585cbac33364d9df32ac2e5d6199b24cef9956172eb0ccd91077ccab0b9758666bbc3be65585cbac34d9c31df32ac2e5d61a6ae18ef9956172eb0d3470c77ccab0b97586823863be65585cbac3391c31df32ac2e5d61810e18ef9956158666b864aa760cab0))) else (if i < 9 then (if i < 7 then 0xb9758666b8641865585cbac33359ea0c32ac2e5d6199ae19059956172eb0ccd842824cab0b9758666b8641265585cbac33359d20932ac2e5d6199ae19041956172eb0ccd85281ccab0b9758666b8640e65585cbac33359c20732ac2e5d6199ae19031956172eb0ccd69c814cab0b975869b38640465585cbac3335c320032ac2e5d6199ae18ff9956172eb0ccd70c7eccab0b9758666b863fc65585cbac3335c31fd32ac2e5d6199ae18fe1956172eb0ccd70c7e8cab0 else (if i < 8 then 0xb976c266b2c44465585cbac3335c322032ac2e5d6199ae190f9956172eb0ccd70c878cab0b9758666ca043a65585cbac33364421d32ac2e5d6199b0b90e9956172eb0ccd70c874cab0b9758666b3643a65585cbac3335c321a32ac2e5d6199ae190c9956172eb0ccd70c860cab0b9758666b8642e65585cbac3335c321332ac2e5d6199ae19091956172eb0ccd70c844cab0b9758666b8641e65585cbac3335c320e32ac2e5d6199ae19051956172eb0ccd70c834cab0 else 0xb9758666b86474655860dac33364da3632ac306d6199ae191b19561832b0ccd70c8d8cab0ac3335f438646c655860dac33359523632ac2e5d6199ae191a9956172eb0ccd70c8d0cab0b9758666ca046665585cbac3335c323232ac2e5d6199ae19189956172eb0ccd70c8bccab0b9758666b8645c65585cbb61335c322b32ac2e5d6199ae19151956172eb0ccd70c8a4cab0b976c266c9344465585cbb61335c322232ac2e5daf99ae19111956172e66bed70c888cab0)) else (if i < 10 then 0xc5f72e57b8649465585cbac3335bda4a32ac2e5d6199ae19249956172eb0ccd70c920cab0b9758666b8648e65585cbac3335c9a4632ac2e5d6299ae19231956172eb0ccd70c918cab0b9756a66b8648c655862aac32f5c324632ac2e5d6199addd23195618a6e5d6170c914cab0b9758666b8648a65585cbac3335c324332ac2e5d6199b281211956172eb0ccd70c904cab0b9758666b8647e65585cbac3335c323e32ac306d6199ae191e1956172eb0ccd70c8eccab0 else (if i < 11 then 0xc5388dc32b14aa655862ac42e1958a5532ac317e1f70cac52a9956172eb0b86542954cab0ac3335c32974aa65585cb99ae194725532ac2e5d6199ae192a1956172eb0ccd70c94ccab0b9758666b864a465585cbac3335c325132ac2e5d6199ae19281956172eb0ccd70c93ccab0b9758666b8649c65585cbac3335c324d32ac2e5d6199ae19261956172eb0ccd70c92ccab0b9758666b9049465585ccac3335c324a32ac2e5d6199ae192519561712b0ccd70c928cab0 else 0xb9758666b2d4aa65585cbac33359625532ac2e5d6199acad2a9956172eb0ccd654954cab0b9758666b294aa65585cbac33359225532ac2e5d6199ac8d2a9956172eb0ccd63e954cab0b97586a2b184aa65585cbac2e198ba5532ac2e5d61a8ac412a9956172eb0d44620954cab0b97586a1b104aa65585cbac34158825532ac2e5d619e4c412a9956158666b86612954cab0b97335c33024aa65585cbac2c418025532ac2e5ccd6a6af52a9956158666b6756e954cab0)))) else (if i < 18 then (if i < 15 then (if i < 13 then 0xb9758666b4a4aa65585cbac3335a4a5532ac2e5d6199ad152a9956172eb0ccd688954cab0b9758666b434aa65585cbac3335a025532ac2e5d6199acfd2a9956172eb0ccd676954cab0b9758666b3e4aa65585cbac33359ea5532ac2e5d6199acf12a9956172eb0ccd674954cab0b9758666b394aa65585cbac33359c25532ac2e5d6199acdd2a9956172eb0ccd664954cab0b9758666b314aa65585cbac333597a5532ac2e5d6199acb92a9956172eb0ccd660954cab0 else (if i < 14 then 0xc2f58666b6a4aa6558617ac3335b3a5532ac30b56199ad9d2a9956172eb0ccd6cc954cab0b9758666b654aa65585cbac3335b1a5532ac2e5d6199ad892a9956172eb0ccd6c0954cab0b9758666b5f4aa65585cbac3335ae25532ac2e5d6199ad6d2a9956172ede4cd6b0954cab0b976f266b534aa65585cbb77335a9a5532ac2e5d6199ad452a9956172eb0ccd6a0954cab0b9758666b4f4aa65585cbac3335a725532ac2e5d6199ad312a9956172eb0ccd696954cab0 else 0xb9758666b7c4aa65585ccac3335bda5532ac2e5d6199aded2a99561712b0ccd6f6954cab0c5f72e57b7b4aa65585cbac3335bd25532ac2e5d6199ade52a9956172eb0ccd6f0954cab0b9758a66b774aa65585cbac3335bba5532ac2e5d5a99addd2a995618aab0cbd6ee954cab0c5372eb0b764aa65585cbac3335bb25532ac2e5d6199add12a9956172eb0ccd6e4954cab0b9758666b704aa65585cbac3335b7a5532ac2e5d6199adb52a9956172eb0ccd6d8954cab0)) else (if i < 16 then 0xc558862ab864aa655862fc3f155c325532ac2e5d61888e192a9956158666c3a70c954cab0b9733619b864aa6558629c46f89c325532ac3156217c4e192a995618bf0fbe270c954cab0b97585e93864aa655856199af21c325532ac2e5ccd77ee192a9956172eb0ccd70a954cab0b9758666b844aa65585cbac3335c1a5532ac2e5d6199ae092a9956172eb0ccd702954cab0b9758666b804aa65585cbac3335bfa5532ac2e5d6199adf92a9956172eb0ccd6fa954cab0 else (if i < 17 then 0xc5f72e643864aa655862aac3321c325532ac2a74cd990e192a995618aab0cbf70c954cab0c558865eb864aa655862aac52f5c325532ac31556197ae192a995618a6b0cbd70c954cab0c5556a5eb864aa655855a99b2f5c325532ac317dcb960e192a995618bf0fcaf70c954cab0c5f73257b864aa655862fb972bdc325532ac314dcb95ee192a995618bee24af70c954cab0b8933657b864aa655856199b2b1c325532ac2e5ccd94ae192a995618a711c5570c954cab0 else 0xb9758266b864aa65585cbabf335c325532ac2e5d5e99ae192a9956172eaeccd70c954cab0b9757266b864aa65585cbab7335c325532ac311d5a99ae192a9956187ead4cd70c954cab0bb156a66b864aa65585cbab5335c325532ac2e5d5999ae192a9956188ea94cd70c954cab0c4953a66b864aa6558623a9d335c325532ac310d4e99ae192a9956187ea74cd70c954cab0b97586663864aa65585cbac332dc325532ac2e5d61994e192a9956172eb0cc970c954cab0))) else (if i < 21 then (if i < 19 then 0xb9759266b864aa65585cbac5335c325532ac30fd6199ae192a9956184eb0ccd70c954cab0c1358666b864aa65585ffac3335c325532ac2fad6199ae192a995617b2b0ccd70c954cab0bc758666b864aa65585cdac3335c325532ac2e656199ae192a9956172eb0ccd70c954cab0b9558666b864aa65585c9ac3335c325532ac2e456199ae192a9956171eb0ccd70c954cab0b8d58666b864aa65585c5ac3335c325532ac2e256199ae192a9956170eb0ccd70c954cab0 else (if i < 20 then 0xb97586923864aa65585cbac3429c325532ac2e5d619eee192a9956172eb0ce970c954cab0b9758668b864aa6558629c47335c325532ac31562199ae192a995618bf0fccd70c954cab0c4377666b864aa6558621b97335c325532ac311dc499ae192a99561886e24cd70c954cab0b976e266b864aa65585cbb59335c325532ac2e5da099ae192a9956172ec94cd70c954cab0b9761a66b864aa65585cbaf7335c325532ac30fd7399ae192a99561712b74cd70c954cab0 else 0xc5f8ab11b864aa6558000c5388dc325532aa00062ac42e192a9955000317e1f70c954caa8c5388ee5b864aa655862ac4372dc325532ac317e1fb96e192a995618a6e5d6e70c954cab0c5388eb0b864aa655862ac43585c325532ac317e1fac2e192a995618a6ec56170c954cab0c5372eb0b864aa655862ab89585c325532ac314dc4ac2e192a995618bee5d5a70c954cab0c5372ead3864aa6558629c47539c325532ac2e5d61a84e192a9956172eb0d3370c954cab0)) else (if i < 22 then 0xc5372eb0b944aa65585cbac3335ca25532ac2e5d6299ae4d2a9956172eb0ccd726954cab0b9756a66b934aa655862aac32f5c9a5532ac2e5d6199ae492a9956172eb0ccd722954cab0b9958666b904aa65585cbac3335c825532ac2e256199ae412a995618bee5caf720954cab0b9758666b8f4aa65585cbac3335c725532ac2e5d6199ae352a9956172eb0ccd718954cab0b9758666b8b4aa65585cbac3335c525532ac2e5d6199ae212a9956172eb0ccd70e954cab0 else (if i < 23 then 0xb9758666bc34aa65585cbac3335de25532ac2e5d6199aeed2a9956172eb0ccd774954cab0b9758666bb94aa65585cbac3335dc25532ac2e5d6199aedd2a9956172eb0ccd76a954cab0b9758666bb44aa65585cbac3335d9a5532ac2e5d6199aec52a9956172eb0ccd75e954cab0b9758666ba74aa65585cbac3335d2a5532ac2e5d6199ae8d2a9956172eb0ccd742954cab0b9758666b9c4aa65585cbac3335cd25532ac2e5d6199ae612a9956172eb0ccd72c954cab0 else 0xb9758666c7e4aa65585cbac33363e25532ac2e5d6199b1ed2a9956172eb0ccd85a954cab0b9758666c2b4aa65585cbac33361525532ac2e5d6199b0a52a9956185eb0ccd84a954cab0b9758666c244aa65585cbac333611a5532ac2e5d6199b0892a9956172eb0ccd842954cab0b9758666c204aa65585cbb793360d25532ac2e5d6199b0592a9956172eb0ccd828954cab0b9758666c104aa65585cbac33360625532ac2e5d6199b0292a9956172eb0ccd812954cab0))))) else (if i < 36 then (if i < 30 then (if i < 27 then (if i < 25 then 0xb9758666b864b465585cbac3335c325932ac2e5d6199ae192b9956172eb0ccd70c958cab0c2b72eb0ccd4aa65585cbb7558666a5532ac2e5d6199b27d2a9956172eb0ccd93a954cab0b9758666c9c4aa65585cbac33364da5532ac30bd6199b25d2a9956172eb0ccd92c954cab0b9758666c954aa65585cbac33364a25532ac2e5d6199b24d2a9956172eb0ccd924954cab0b976f266c8c4aa65585cbac33364425532ac2e5d6199b2192a9956172eb0ccd904954cab0 else (if i < 26 then 0xc5372eb0b864c665585cbac3335c326332ac2e5d6199ae4d311956172eb14cd70c988cab0b9758666b864c465585cbab5335c326232ac31556197ae19311956172eb0ccd6ee988cab0b9758666b864c265585cbac3335c326032ac2e5d6199ae412f99561732b0ccd70c97ccab0b9758666b864be65585c4ac3335c325f32ac317dcb95ee192f9956172eb0ccd6f697ccab0b9758666b864bc65585cbac3335c325d32ac2e5d6199ae192e1956172eb0ccd70c96ccab0 else 0xb9758666b1051665585cbac3335c328a32ac2e5d6199ae19449956172eb0ccd772a20cab0b9758666b8651065585cbac3335c328732ac2e5d6199ae19431956172eb0ccd70ca10cab0b9758666b8650665585cbac3335c328232ac2e5d6199ae19401956172eb0ccd70c9f8cab0b9758666b864ec65585cbac3335c327432ac2e5d6199ae19391956172eb0ccd70c9c0cab0b9758666b864d665585cbac3335c326932ac2e5d6199ae19339956172eb0ccd70c994cab0)) else (if i < 28 then 0xb9758666b865e465585cbac3335c32f132ac2e5d6199ae19781956172eb0ccd842bbccab0b9758666b865de65585cbac33359d2ef32ac2e5d6199ae19771956172ed84cd70cba0cab0b9758666b865c865585cbac3335c32e232ac2e5d6199ae196f1956172eb0ccd70cb68cab0b9758666b865b065585cbac3335c32d732ac2e5d6199b26d4a9956172eb0ccd926a54cab0b9758666bbc52a65585cbac3335c329432ac2e5d6199af19459956172eb0ccd70ca2ccab0 else (if i < 29 then 0xb9758666c6b70c65585cbac333634b8632ac2e5d6199b1a1c31956172eb0ccd940dcccab0c2f58666c986ce65585cbac33365036432ac2e5dbc99b239a99956172eb0ccd940d38cab0b9758666c7769c65585cbac33364c31032ac2e5d6199b239881956172eb0ccd8eec40cab0b9758666b4e5f865585cbac3335c32fb32ac2e5d6199ae197c9956172eb0ccd70cbe0cab0b9758666c295ee65585cbac3335c32f732ac2e5d6199ace17b99561836b0ccd70cbcccab0 else 0xb9758666c888f065585cbac33365046e32ac2e5d6199b261e31956172eb0ccd91cf18cab0c1772eb0ccd70c65585cbb5d58666b8632ac2e5d6199b279c31956172eb0ccd934e18cab0b9758666c9970c65585cbac33364c38632ac306d6199b25dc31956172eb0ccd922e18cab0b9758666c9070c65585cbac333647b8632ac2e5d6199b239c31956172eb0ccd91ae18cab0b976c266c8c70c65585cbac33363bb8632ac2e5d6199b1d5c31956172eb0ccd8e2e18cab0))) else (if i < 33 then (if i < 31 then 0xb9758666b8649467d85cbac3335c325533cc2e5d6199ae192a99d6172eb0ccd70c954ce30b9758666b864aa66d85cbac3335c3255334c2e5d6199ae192a9996172eb0ccd70c954cbb0b9758666b864aa6598608b9758666ca032ac2e5da9ac33365019561836e5d6199b26ccab0c2f72eb0ccd93065585cbb6158666c9332ac2e5dbcac33364719561836e5d6199b220cab0b976c2b0ccd9106558617b9758666c7732ac2e5dbcac33363b9956172eb0ccd9131dccab0 else (if i < 32 then 0xb9758666b864aa6958629b97585c3255346c2e5d6199ae192a9a36172eb0ccd70c988d130b9758666b934aa68985cbac5335c3255344c2e5d6199ae192a9a26172ead4cd70c954d130c555865eb864aa68985cbac3335bba55344c2e5d6199ae19231a26172eb0ccd70c954d0b0b9758666b864aa68185cbac3335c325f33ec2e5d6199ae412a99f61732b0ccd70c954cfb0b9758666b864aa67d85c4ac3335c325533ec317dcb95ee192a99f6172eb0ccd6f6954cfb0 else 0xb9758666b864aa72d85cbac3335c3255394c2e5d6199ae194a9c96172eb0ccd778954e4b0b9758666b864aa72585cbac3335c31df392c2e5d6199ae192a9c86172eb0ccd70c954e3b0b9758666b864aa71585cbac3335c3255388c2e5d6199ae192a9c36172eb0ccd70c954e030b9758666b864aa6f985cbac3335c325536cc2e5d6199ae192a9b46172eb0ccd70c954d930b9758666b864aa6c185cbac3335c3255356c2e5d6199ae192a9a96172eb0ccd70c954d3b0)) else (if i < 34 then 0xb9758666c2e4aa86d85cbac33361738642ec2e5d6199ae197e2176172eb0ccd70cb4d0bb0b9758666c1c70c7e985cbac3336133863f0c2e5d6199ae197a1df6172eb0ccd70cba8efb0b9758666b865a677d85cbac3335c32f73acc2e5d6199ae19779d66172eb0ccd70ca20eb30b9758666c294aa75985cbac333610a553acc2e5d6199aee52a9d66172eb0ccd70c954eab0b9758666b8651673185cbac3335e3255398c2e5d6199ae192a9cc6172eb0ccd620954e630 else (if i < 35 then 0xb9758666b2a5e89558603ac3335c32f34aac2e5d6199ae1976a556172eb0ccd70cbb12ab0b9758666b865d695585cbac333649aea4aac2e5d6199ae19752556172eb0ccd658ba92ab0b9758666b865d295585cbb49335c32e84aac2e5d6199ae1969a556172eb0ccd70cb452ab0b9758666b8659a95585cbac3335c32c94aac2e5d6199ae1963a556172eb0ccd70cb192ab0b9758666b865f8901860dac3335c32f446cc2e5d6199ae197e2306172ed84cd70cba91130 else 0xb9758666c0270c95585cbac3335ff3864aac2e5d6199afe1c32556172eb0ccd7ece192ab0b9758666bf570c95585cbac3336173714aac30bd6199b099b3a556172eb0ccd85cd852ab0b976f266c1c6a695585cbac3336173494aac2e5d6199b011a4a556172eb0ccd84cc412ab0b9758666c1c62095585cbac3336023104aac2e5d6199ad257e2556172eb0ccd70cbe92ab0b9758666b865ec95585cbac3335c32f54aac2e5d6199b26d7a2556172eb0ccd70cbd12ab0)))) else (if i < 42 then (if i < 39 then (if i < 37 then 0xb976f2b0ccd80895585cbac33360bc044aac2e5d6199b05a02a556172eb0ccd85cfed2ab0b9758666c2678c95585cbac33360e3c64aac300dcbac3335c32556172ed156199ae192ab0b9758666c2c70c95585cbac3336143864aac2e5d6199b09dc32556172eb0ccd84ce192ab0c0758666c2570c95585cbac33360fb864aac2e5d6199b079c32556172eb0ccd83ae192ab0b9758666c1c70c95585cbac33360db864aac2e5da499b069c32556172eb0ccd808e192ab0 else (if i < 38 then 0xc0772eb0ccd70cb9185cbb4958666b865c8c2e5d6199ae197e0756172eb0ccd70cbf03a30c1b72eb0ccd70cb4d85cbb6158666b865a6c2e5d6199ae1972ad36172eb0ccd70cb916a30b9758666b865f8b1585cbac3335c32f452ac2e5d6199ae1975295617fae5d6199b0b92ab0b97676b0ccd85c9558603b9758666c294aac30bdcbac3336132556172ed256199b0852ab0b976f2b0ccd8389558603b9758666c164aac2e5da4ac33360b2556185ee5d6199b0112ab0 else 0xb9758666c294aa0f185cbac333617255072c2e5d6199ae19750806172eb0ccd9266544030b9758666ca032a1f585cbac3336501950f8c2e5d6199ae197e0386172eb0ccd931099c330b9758666c8e838e1985cbac3335c32ef0f4c2e5d6199b0852a87a6172eb0ccd85c9543bb0b9758666c2e4aa1d985fdb9758666b865f8c2e5d9cac3335c32fc6172eb0ccd70cd1d7e30c0772eb0ccd70cbdd860db9758666b865e8c2e5da4ac3335c32ef6172ed856199ae197530)) else (if i < 40 then 0xc5f87dc325532a24d861fac2e192a995116c2e5d5a70c954ca88b618a6b0b864aa6544530ab5335c325532a229862aac2e192a995112c2e5d6199b0712a8856172eb0ccd91c65442b0c5172eb0ccd70c32585cbac3335c32fc192c2e5d6199ae19720c96172eb0ccd70cb4c64b0b9758666b8658632585cbac3335c32ad192c2e5d6199b0592a8c96172eb0ccd91065464b0b9758666b865f831585cbac33361725518ac2e5d6199b280ca8c56172eb0ccd70cbdc1e30 else (if i < 41 then 0xb9758666c8832a39585cbac33363b9951cac2e5d6199b144ca8e56172eb0ccd88c65472b0b9758666c2e4aa38185cbac3335c32fc1bec2e5d6199ae19720d3618a2e5d6199a95469b0b9758666c2e4aa34d85cbac33360b2551a6c2e5d6199b0112a8d36172eb0ccd7e695469b0b9758666bde4aa34d85cbac33363b9951a6c314e2370c954ca89a6172eb0b864aa6544cb0c47539c325532a265854e99ae192a995130c314e2370c954ca893618ab10b864aa65449b0 else 0xb9758666c2e4aa45585cbac3335c32fc228c31562170c954ca910615865eb864aa65487b0b97335c325532a439862a97ae192a99521cc314e2370c954ca909618ab10b864aa65484b0c5f87dc325532a425861f99ae192a995202c310ccd70c954ca9006188e66b864aa6547fb0b9758666ca032a3ed85cbac3336172551f4c2e5d6199b280ca8f26172eb0ccd70cbf078b0b9758666b865a639585cbac3336022551cac3145cbac3334ca8e56172eb0ccd94065472b0))) else (if i < 45 then (if i < 43 then 0xb97585c325532a49d85cbac3335c32f7240c2e5d6199ae19779206172eb0ccd70cb909030b9758666b8651048185cbac333614a55240c2e5d6199b0852a9206172eb0ccd82c9549030b9758666bb94aa48185cbac349dc3255240c2e5d61a4ce192a9206172eb0d2570c9549030b9758678b864aa48185cbac338dc3255240c2e5d618cee192a920618bf0fb864aa6548cb0b972bdc325532a461856199ae192a99522ec317caf70c954ca9176172eb0ccd9406548b30 else (if i < 44 then 0xb9758666b864aa50585cbac3335c3255280c2e5d6199ae192a93c6172eb0ccd70c9549fb0b9758666b864aa4f985cbac3335c31fd27cc2e5d6199b239c313b6172eb0ccd70c9549db0b976f266b534aa4ed85cbac3335c31fa276c2e5d6199ae192a93a6172eb0ccd930e189cb0b9758666b864aa4e58617ac3335b3a55272c2e5d6199ae18fc1396172eb0ccd70c9549c30b9758666b8642e4dd85cbac3335c3255266c2e5d6199ae192a9326172eb0ccd70c9549730 else 0xb9758666b864aa53185cbac333597a55298c2e5d6199ae192a94b6172eb0ccd70c954a6b0b9758666b864aa52985cbac333649a55292c2e5d6199ae192a9496172eb0ccd658954a4b0b976c266b8644452585cbac3335c3255290c2e5d6199b26d2a9476172eb0ccd70c954a3b0b9758666b2a4aa51d860dac3335c323628ec2e5d6199ae192a9466172eb0ccd692954a2b0b9758666b865e810185cbac33364d995080c2e5d6199b280ca83d6172eb0ccd70c9549eb0)) else (if i < 47 then (if i < 46 then 0x172eb0ccd3846554800c5f87dc3255314a4005c495ee192a98a5200314e2370c954c2a90018ab10b864aa6194800ab52f5c325530ca40056199ae192a97f52002e5ccd70c954b7a90018bdc325532a0714800c54e192a995036a40062970c954ca81a52002e5d6170c954aaa900188dc325532a0514800c42e192a995026a40061f70c954ca80e5372eb0ccd70c954a9b0b9758666b864aa54985cbac3335c32552a2c2e5d6199ae192a94f6172eb0ccd70c954a730 else 0x18ab10b774aa6554800ab52f5bba5532aa400629c46dd92a99552002b0ccd6d4954caa900172e66b584aa6554800b975858c25532aa4005cbac2c012a99552002e5ccd57a954caa900158666ab74aa6554800c5388d58a5532aa40062ac42ac52a9955200317e1f562954caa90018bf0fb864946554800b892bdc324a32aa40062ac42e192319552002ad4bd70c918caa90018a711b8648a6554800ac3335c323c32aa4005cb99ae191599552002e5d6170c808caa9) else (if i < 48 then 0x172e66bed70c6554800ac3335f438632aa400629c46f89c319552003156217c4e18caa90018bf0fbe270c6554800c5388dc325532aa40062ac42e192a9955200314e2170c954caa90018bf0fb864aa6554800c5387dc325532aa40062fc3ce192a995520031561e70c954caa90018a70f3864aa6554800c3d335c325532aa40055299ae192a9955200314cc870c954caa90015865fb864aa6554800b972c1c325532aa40062fc3eded2a99552002e24af6f6954caa9 else 0x172dc325532a4614800ac2e192a99521ea4004cd70c954ca89852003145cbac333462a900172eb0ccd70cd1d4800b9758666b86586a4005cbac3335f9a5552002e5d618cee192aa900172e66c5f70c9554800ac33362db864aaa400629c47155c325552003156218aae192aa90018bf0fc5570c9554800b9758666a55436a4005cbac33362319552002e5d61810e18caa9))))))
private def st5 (i : Nat) : Nat := unpack st5Packed 73 20 i
private def adj5Packed (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0x400052440420010030064830001000060053c22800801c00000000803cf1960851810430000411013c10000020040000c3006081040002000080240 else 0x2400000810004486c00010400c60000800020831051000421c00c208804010601300e0001841001c000000a0000401411010010812c3044001181) else (if i < 3 then 0x15e00300e08200708100118f15e00218900208210105010200200104014200100200200008608b0021406c108000000a503001042094011004840006 else (if i < 4 then 0x2450052460040821c80840014c200800130000308000104600104038201a18100100904405110504000000118a18048008f00100100200604300b140 else 0x40107205)))
private def adj5 (i : Nat) : Nat := unpack adj5Packed 6 80 i
private def loc5Packed (i : Nat) : Nat := (if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then 0xe80220021ee2ec824e40000001b575e880000249000008e4be994000000000000541dfc796edf28f001880035adec0b001ed475e2000fb2d67472a849c400b3800ea1b7f208c06800ea596002298f9eac38f0000e6c74cc52c000012900015002ef67dfa else 0x4cc00000d954800d1c0000000d6400e6184000006f8420016cac6461a40100014a4628cc0bbb8c0089c004dbb77d8000b60d003bd345da0eecf0006f01ab8001ef2608f001cf001e076148ad2be6ca776d4000022d003110009a002f8e1c000008738b64) else (if i < 3 then 0x3bb920012b3e80070fb30012de6899baa530007f3600000061d3ac200000003022fc004c000000004a000000411ec0030c00efa2500000000eb002667c0003cfa30000075f6acbf9b001c600241d55810015d9fb81eb80000222f2800000000610375310 else 0x1c06e307cb91f33537b600000f0c000c800032d467180f26eb00208cdb310010b00067a3618d18c8000000003a40b130011009b8a00386dbda35ac550000093c9052a2ce7a1c3f6101104a85569001f74fb766b0003737a6563200000003cfa1d7c002f6)) else (if i < 6 then (if i < 5 then 0x3824aa8b9656e2b0025795000001fbb98726fc2c4e851bb400eac00002ec0000035c00d2800a9ec00000076caac5c008f67c32f0beec005abb50028eba4341d305aac29000715c2200400000000c11a63c5c900353000002a729000b15f400736b0002f3 else 0x2933bc00ebc750280000000981ba2d92c06f3863211c00fe00000c4b5f6a7b87f800cec0000288d940000000002de0000088775b8b3e35454001aa0000000000a9a43000009a896003c159c00504009200009e38ec00099356454c000337ae9313e521) else (if i < 7 then 0x8d4000005893a9e04c0e0039100049003610acea6aeaaadfce0006c426630003e2cda4a487700000b0c2e00000e01640019300301d4800f362f12c432080000178000001212e00104001a0000000001d16e1d0028600189000009350c94370bc537001c4 else (if i < 8 then 0xc9cf2d80009540000000000002acac0000032460be800e2644a2b71003aa00206000009ac0083800a85ee6ef0d34bc079000000000000031e94d413f00000001260036b45ed1c9488744000032c2953578c00a8e5c000006bc0022ce4b5bcc7175bd4400 else 0xcea01d22a06e613de4de0031446a3f23556384398cd8b003630000000395f10dd002457380000309000c49ba5199c007cc000a8c6418000005ac9000a92d0ad40070546275f2ee80000011460e9b6cf55bc00000000000048ead22800001dc6cd8e28c00)))) else (if i < 14 then (if i < 11 then (if i < 10 then 0x1546355e00000b2800bf24cd2c00250005d05658c7898400001c80009b000007adbc3e000001a729f9d11c00114b4571ddb2555000009bc00000005fec71a14500176b4db80de5a0023000147db0126c00000050204d6d065d9f73c6a2c659b0f0c400 else 0xcb4000000063c0059400000009a40036f320000d758640002146c00e30005ea9858b783b13239e80675612880047afed89e1002bd61c0000000dff770031b002857b37ea940700000d249c86ad85fac464b22000007a2195b40066c00e4eb233e041e400) else (if i < 12 then 0xaec00cd799d7800001820d40f0f55317400eb400c70005cd91c30006bb5d09400732763a00000200285f96d345000000029b0000092c001000000023bf6d54f00000252ec80000334000857563cd9e621948900000b6800c2bb165c00002e700000 else (if i < 13 then 0xb9400b767f18d7700000000005c40018800438e58b8006679ce9400e3c00eb11c7fe5f6d846000005619483fa6428cad0c00a0c0001400685799e8d47a400e7c361adb134c28b05f42a34c29adc00000851430000081c00c59442de6800000a300038cf4 else 0xab0809e65b001254e61b71d9055f19d5101001bdf15490020b0fe8b9eca4003720026d0031f1995a000a000224e149f00151701e513000da2732780000000002900e2f521800bb88e001fdbde952f6cb00000c68030083c0023bb866cbe4d0b7c001732e))) else (if i < 16 then (if i < 15 then 0x85800afc8313c53000007c78e420000000088eb3ef234080af003b41f74f1fb830037d2b85e14800bfec517c00314000032a0034d3080056637002f415c0400000d001f0033fca00000000003204440000000a04b20010d000b840000369249c17bd9800 else 0xc18009e18300000003a100000db5720030844800b6476414df000330bc00a753db3400e200000114a7c0058138489341cc00d604e00000ae59a2c00000258000003f14c1eba4001a53dc00d0abc00000338004a9de064adcae5e00009e0b846b40061816) else (if i < 17 then 0x14f0007cbc830a6408000000030700000db80074c0087e0ab80008d800c9800001d00010f002170001e001d2a5f23e9ccd80fc27e35c00259e438d3b4000020c0011341f69000970029c0000000000a0aae0019e0012f7f024c5400001f5e5296001d9 else (if i < 18 then 0x2d2b3000bee0500000aa65668800000ff2e459a68006611f8e8000013b002f000289c84ba000f6b9119ee400212af48000b5c0072fbfd5c002562a0000013400001e6ba2020009200226848000000079fc700000000bcdd1279d46a00397dcf44c0d68 else 0x18a00185ce5420014ef191600000824008c41790800002a8c60919c94070ab600000cf55f07000)))))
private def loc5 (i : Nat) : Nat := unpack loc5Packed 10 80 i
private def st6Packed (i : Nat) : Nat := (if i < 63 then (if i < 31 then (if i < 15 then (if i < 7 then (if i < 3 then (if i < 1 then 0xb9758666b864aa65403b8b9758666b864aa67c0738b9758666b864be6540738b9758666b904aa6540738b9958666b864aa6540738b9758666b864aa6540738b8958666b864aa6540738c5f72e57b864aa6540738b9758666b7b4aa6540738b9758666b864946540738b9758666b864aa6280738b9758666b864aa65406b8b9758666b864aa6540638b9758666b864aa65405b8b9758666b864aa6540538b9758666b864aa65401b8b9758666b864aa6540338b9758666b864aa65400b8b9758666b864aa65404b8b9758666b864aa65402b8 else (if i < 2 then 0xb9758666b864aa6540a38b9758666b864aa6540038b9758666b864aa6540ab8b9758666b864aa68809b8b9758666b864c465409b8b9758666b934aa65409b8b9758a66b864aa65409b8b9758666b864aa65409b8b9756a66b864aa65409b8c555865eb864aa65409b8b9758666b774aa65409b8b9758666b8648c65409b8b9758666b864aa61809b8b9758666b864aa6540938b9758666b864aa6540438b9758666b864aa65408b8b9758666b864aa6540838b9758666b864aa6540238b9758666b864aa6540138b9758666b864aa65407b8 else 0xc5f72eb0b864aa65424b8b975866fb864aa65424b8b9758666b864aa65424b8b975865eb864aa65424b8c5f72e66b864aa6542438b975ce66b864aa6542438b9758666b864aa6542438b9753a66b864aa6542438b9758666b864aa65423b8b9758666b864aa6542338b9758666b864aa65422b8b9758666ca04aa6542238b9758666c2e4aa6542238b9758666ba04aa6542238b9758666b864aa6542238b9758666b674aa6542238b9758666b864aa65421b8b9758666b864aa6542138b9758666b864aa65420b8c5372eb0b864aa6540a38)) else (if i < 5 then (if i < 4 then 0xb9758666b774aa65428b8c2f58666b674aa65428b8b976f266b534aa65428b8b97586a2b104aa65428b8b9758666b8649465428b8b9758666b8648c65428b8c1b58666b8646c65428b8b976c266b8644465428b8b975869b3863be65428b8b9758666b864aa62828b8b9758666b864aa61828b8c0758666b864aa5d828b8b9769266b864aa58828b8b9758666b864aa6542838b9758666b864aa65427b8b9758666b864aa6542738b9758666b864aa65426b8b9758666b864aa6542638b9758666b864aa65425b8b9758666b864aa6542538 else 0xb9758666b865e895428b8b9758666b865d495428b8b9758666c9870c65428b8b9758666c8e70c65428b8b9758666b865ee65428b8b9758666b865de65428b8b9758666c9b4aa65428b8b9758666c934aa65428b8b9758666c294aa65428b8b9758666c214aa65428b8c5372eb0b864aa65428b8c4372e66b864aa65428b8c3f58666b864aa65428b8b9758666b864aa65428b8b8958666b864aa65428b8b9756a66b864aa65428b8c4753a66b864aa65428b8c555865eb864aa65428b8c5f72e57b864aa65428b8b9758666b7b4aa65428b8) else (if i < 6 then 0xb9758666b864aa6544f38b9758666b864aa6544eb8b9758666b864aa6541738b9758666b864aa65416b8b9758666b864aa6541638b9758666b864aa65414b8b9758666b864aa65415b8c1b58666b8646c65415b8b9758666b864aa6541538b9758666b864aa6541438b9758666b864aa65454b8b9758666b864aa6540eb8b9758666b864aa6542938b8958666b864aa6542938b9758693b864aa48028b8b9758666ca032a39428b8b9758666c2e4aa34c28b8b9758666b865f832428b8b9758666c2670c95428b8b9758666c1c70c95428b8 else 0x172eb0ccd70c954aeb0b9758666c1770c954aeb8b9758666be270c954aeb8b9758666b864aa654aeb8b9758666b864aa654ae3800172eb0ccd70c954ac30b9758666b865ca954ac38b9758666b86562954ac38b9758666b864aa654ac38b9758666b864aa654abb8c3f58666b864aa6540e38b9758666b864aa6540e38b9758666b864aa6540b38c4372e66b864aa6540db8b9758666b864aa6540db8b9758666b864aa6540d38c4753a66b864aa6540d38b9758666b864aa6540cb8b9758666b864aa6540c38b9758666b864aa6540bb8))) else (if i < 11 then (if i < 9 then (if i < 8 then 0xb9758666b864aa654b3b8b9758666b864aa654b338b9758666b864aa654b2b8b9758666b864aa654b238b9758666b864aa654b1b800172ed24cd70c954b130b97692b0ccd70c954b138b9769266c6370c954b138b9769266c5570c954b138b9769266be270c954b138b9769266b86562954b138b9758666b864aa758b138b9758666b865de654b138b9758666c214aa654b138b9769266b864aa654b138b9758666b864aa654b138b97336253864aa654b138b9758666b3a4aa654b138b9758666b86412654b138b9758666b864aa654b0b8 else 0xb9758666b864aa654bbb800180eb0ccd70c954bb30c0772eb0ccd70c954bb38c0758666c5c70c954bb38c0758666c5570c954bb38c0758666be270c954bb38c0758666b86562954bb38b9758666b864aa758bb38b9758666b865ee654bb38b9758666c294aa654bb38c0758666b864aa654bb38b9758666b864aa654bb38ac3336273864aa654bb38b9758666b384aa654bb38b9758666b8640e654bb38b9758666b864aa654b9b8b9758666b864aa654b838b9758666b864aa654b638b9758666b864aa654b5b8b9758666b864aa654b438) else (if i < 10 then 0xc5f72eb0ccd70c954c53800172eb0ccd70c954c530b9758666c5670c954c538b9758666c5570c954c538b9758666be270c954c538b9758666b86562954c538b9758666b864aa654c538c5572eb0ccd70c954c33800172eb0ccd70c954c330b9758666c5770c954c338b9758666c5570c954c338b9758666be270c954c338b9758666b86562954c338b9758666b864aa654c338b9758666b864aa654c238b9758666b864aa654c138b9758666b864aa654c038b9758666b864aa654be38b9758666b864aa654bcb8b9758666b864aa654bc38 else 0xb9758666b864aa6f0cab8b9758666b864aa6eccab8b9758666b864aa6e8cab8b9758666b864aa6e4cab8b9758666b864aa6e0cab8b9758666b864aa6dccab8b9758666b864aa6d4cab8b9758666b864aa6cccab8b9758666b864aa6c4cab8b9758666b864aa6bccab8b9758666b864aa6b8cab8b9758666b864aa6b4cab8b9758666b864aa6b0cab8b9758666b864aa6a8cab8b9758666b864aa6a0cab8b9758666b864aa698cab8b9758666b864aa688cab8b9758666b864aa67ccab8b9758666b864aa660cab8b9758666b864aa690cab8)) else (if i < 13 then (if i < 12 then 0xb9758666b864aa774cab8b9758666b864aa770cab8b9758666b864aa76ccab8b9758666b864aa768cab8b9758666b864aa764cab8b9758666b864aa75ccab8b9758666b864aa758cab8b9758666b864aa750cab8b9758666b864aa74ccab8b9758666b864aa748cab8b9758666b864aa744cab8b9758666b864aa740cab8b9758666b864aa738cab8b9758666b864aa734cab8b9758666b864aa730cab8b9758666b864aa724cab8b9758666b864aa718cab8b9758666b864aa704cab8b9758666b864aa6fccab8b9758666b864aa6f4cab8 else 0xb9758666b864aa784cab8b9758666b864aa780cab800172eb0d3670c77ccab0b975869b4cd70c77ccab8b9758666ca070c77ccab8b975869b45570c77ccab8b975869b43570c77ccab8b975869b3e270c77ccab8b9758666b865f877ccab8b975869b38656277ccab8b9758666b864f877ccab8b9758666b864de77ccab8b975869b3864aa77ccab8b9758666b864aa77ccab8b97585e63864aa77ccab8b9758666b8646c77ccab8b9758666b8644477ccab8b9758666b8640a77ccab8b9758666b863ec77ccab8b9758666b864aa778cab8) else (if i < 14 then 0xb9758666b865ca7d8cab8b9758666b864aa7d8cab8b9758666b864aa7d4cab8b9758666b864aa7d0cab8b9758666b864aa7cccab8b9758666b864aa7c0cab8b9758666c214aa7bccab8b9758666b864aa7bccab8b9758666b864aa7b8cab8b9758666b864aa7b0cab8b9758666c294aa7accab8b9758666b864aa7accab8b9758666b864aa7a8cab8b9758666b864aa7a4cab8b9758666b864aa7a0cab8b9758666b864aa79ccab8b9758666b864aa794cab8b9758666b864aa790cab8b9758666b864aa78ccab8b9758666b864aa788cab8 else 0xb9758666c7870c814cab8b9758666c884aa814cab8b9758666b864aa814cab8b9758666b864aa810cab8b9758666b864aa80ccab8b9758666b864aa804cab800172eb0ccd70c7f4cab0b97586764cd70c7f4cab8b9758666b865627f4cab8b9758666b864aa7f4cab800172eb0ccd70c7e8cab0b9758666b866a67e8cab8b9758666b8657e7e8cab8b9758666b864aa7e8cab800172eb0ccd70c7e0cab0b9758666b866ce7e0cab8b9758666b865707e0cab8b9758666b864aa7e0cab8c1b72eb0ccd70c7d8cab8b976c2b0ccd70c7d8cab8)))) else (if i < 23 then (if i < 19 then (if i < 17 then (if i < 16 then 0xb9758666b864aa870cab800172eb0ccd70c85ccab0b9758666b865a885ccab8b9758666b8656285ccab8b9758666b864aa85ccab8b9758666b864aa858cab8b9758666b864aa850cab8b9758666b864aa840cab800172eb0ccd70c830cab0b9758686ccd70c830cab8b9758666c5570c830cab8b9758666b864aa830cab800172eb0ccd70c824cab0b9758666c6370c824cab8b9758666b864aa824cab800172eb0ccd70c81ccab0b9758666c5c70c81ccab8b9758666b864aa81ccab8c1b72eb0ccd70c814cab8b976c2b0ccd70c814cab8 else 0xb9758666b864aa894cab8b9758666b864aa890cab8b9758666b864aa88ccab800172ed84cd70c888cab0b976c2b0ccd70c888cab8b976c266c5570c888cab8b976c266bf070c888cab8b976c266be270c888cab8b976c266b86562888cab8b9758666b8652a888cab8b9758666c934aa888cab8b976c266b864aa888cab8b9758666b864aa888cab8b97335ebb864aa888cab8b9758666b2c4aa888cab8b9758666b864aa884cab800172eb0ccd70c874cab0b9758666c8970c874cab8b9758666c5570c874cab8b9758666b864aa874cab8) else (if i < 18 then 0xb9758666b864aa8dccab8001836b0ccd70c8d8cab0c1b72eb0ccd70c8d8cab8c1b58666c5570c8d8cab8c1b58666be970c8d8cab8c1b58666be270c8d8cab8c1b58666b865628d8cab8b9758666b8652a8d8cab8b9758666c9b4aa8d8cab8c1b58666b864aa8d8cab8b9758666b864aa8d8cab8ac3335edb864aa8d8cab8b9758666b2a4aa8d8cab8b9758666b864aa8cccab8b9758666b864aa8c0cab8b9758666b864aa8b4cab8b9758666b864aa8b0cab8b9758666b864aa8a0cab8b9758666b864aa89ccab8b9758666b864aa898cab8 else 0xc5f72eb0ccd70c928cab800172eb0ccd70c928cab0b9758666c5570c928cab8b9758666be370c928cab8b9758666be270c928cab8b9758666b86562928cab8b9758666b864aa928cab8c5572eb0ccd70c918cab800172eb0ccd70c918cab0b9758666c5570c918cab8b9758666be470c918cab8b9758666be270c918cab8b9758666b86562918cab8b9758666b864aa918cab8b9758666b864aa910cab8b9758666b864aa908cab8b9758666b864aa900cab8b9758666b864aa8f4cab8b9758666b864aa8e4cab8b9758666b864aa8e0cab8)) else (if i < 21 then (if i < 20 then 0xb9758666b864f8954cab8b9758666b864f6954cab8b9758666b864f4954cab8b9758666b864f2954cab8b9758666b864f0954cab8b9758666b864ee954cab8b9758666b864ea954cab8b9758666b864e6954cab8b9758666b864e2954cab8b9758666b864de954cab8b9758666b864dc954cab8b9758666b864da954cab8b9758666b864d8954cab8b9758666b864d4954cab8b9758666b864d0954cab8b9758666b864cc954cab8b9758666b864c4954cab8b9758666b864be954cab8b9758666b864b0954cab8b9758666b864c8954cab8 else 0xb9758666b86536954cab8b97585c3310536954cab8b9758666b86534954cab8b9758666b86532954cab8b9758666b86530954cab8b9758666b8652c954cab8b9758666b8652a954cab8b9758666b86526954cab8b9758666b86524954cab8b9758666b86522954cab8b9758666b86520954cab8b9758666b8651e954cab8b9758666b8651a954cab8b9758666b86518954cab8b9758666b86516954cab8b9758666b86510954cab8b9758666b8650a954cab8b9758666b86502954cab8b9758666b864fe954cab8b9758666b864fa954cab8) else (if i < 22 then 0xb9758666b86556954cab8bcd58666b86554954cab8b9758666b86554954cab8ac3335c3367554954cab8b9758666b86552954cab8b9758666b86550954cab8b9758666b8654e954cab8b975fa66b8654c954cab8b9758666b8654c954cab8b97335c335354c954cab8b9758666b8654a954cab8b9758666b86548954cab8b9758666b86546954cab8b9758666b86544954cab8b9758666b86540954cab8b9758666b8653e954cab8b9758666b8653c954cab8b9758666b8653a954cab8b9758666b86538954cab8b9758676386536954cab8 else 0xb9758666c21562954cab8c5372eb0b86562954cab8c4372e66b86562954cab8c3f58666b86562954cab8b9758666b86562954cab8b8958666b86562954cab8b9756a66b86562954cab8c4753a66b86562954cab8c555865eb86562954cab8c5f72e57b86562954cab8b9758666b7b562954cab8b9758666b77562954cab8c2f58666b67562954cab8b976f266b53562954cab8b97586a2b10562954cab8b9758666b86560954cab8b9758666b8655e954cab8b9758666b8655c954cab8b9758666b8655a954cab8b9758666b86558954cab8))) else (if i < 27 then (if i < 25 then (if i < 24 then 0xb9758666b86580954cab8b9758666b8657e954cab8b976f266b5357e954cab8b9758666b8657c954cab8b9758666b86578954cab8b9758666b86576954cab8b9758666b86574954cab8b9758666b86572954cab8b9758666b86570954cab8c2f58666b67570954cab8b9758666b8656c954cab8b9758666b8656a954cab8b9758666b86568954cab8b9758666b86566954cab8b9758666b77566954cab8b9758666b86564954cab8b9758666b7b564954cab8b9758666c9b562954cab8b9758666c93562954cab8b9758666c29562954cab8 else 0xb9758666b865be954cab8b9758666b865ba954cab8b9758666b865b8954cab8b9758666b865b6954cab8b9758666b865b2954cab8b9758666b865ac954cab8b9758666b865aa954cab8b9758666b865a6954cab8b9758666b865a8954cab8b9758666b865a4954cab8b9758666b865a0954cab8b9758666b8659e954cab8b9758666b8659c954cab8b9758666b86598954cab8b9758666b86596954cab8b9758666b86594954cab8b9758666b86590954cab8b9758666b8658a954cab8b9758666b86584954cab8b9758666b86582954cab8) else (if i < 26 then 0xb97586a2b10608954cab8b9758666b86606954cab8b9758666b86602954cab8b9758666b865fe954cab8b9758666b865fc954cab8b9758666b865f8954cab8b9758666b865fa954cab8b9758666b865ee954cab8b9758666b865e8954cab8b9758666b865e6954cab8b9758666b865de954cab8b9758666b865d4954cab8b9758666b865d0954cab8b9758666b865ce954cab8b9758666b865cc954cab8b9758666b865c8954cab8b9758666b865ca954cab8b9758666b865c6954cab8b9758666b865c2954cab8b9758666b865c0954cab8 else 0xb97586a2be2620954cab8b9758666bad620954cab8b9758666ba0620954cab8b97586a2b86620954cab8b9758666b86620954cab8b9758666b67620954cab8b9758666b53620954cab8b9758666b36620954cab8b9758666b28620954cab8b9758666b8661e954cab8b9758666b8661c954cab8b9758666b8661a954cab8b9758666b86618954cab8b9758666b86616954cab8b9758666b86614954cab8b9758666b86610954cab8b9758666b8660e954cab8b9758666b8660c954cab8b9758666b8660a954cab8b9758666b86608954cab8)) else (if i < 29 then (if i < 28 then 0xb9758666b86644954cab8b9758666b86642954cab8b9758666b86640954cab8b9758666b8663c954cab8b9758666b8663a954cab8b9758666b86638954cab8b9758666b86636954cab8b9758666b86634954cab8b9758666b86632954cab8b9758666b8662c954cab8b9758666b8662a954cab8b9758666b86628954cab8b9758666b86626954cab8b9758666b86624954cab8b9758666b86622954cab800172eb0d45620954cab0b97586a2ccd620954cab8b9758666ca0620954cab8b97586a2c55620954cab8b9758666c2e620954cab8 else 0xb9758666b8666a954cab8b9758666b86668954cab8b9758666b86666954cab800172eb0ccd65e954cab0b975867d4cd65e954cab8b9758666be265e954cab8b9758666b8665e954cab800172eb0ccd658954cab0b9758666bf0658954cab8b9758666b86658954cab800172eb0ccd654954cab0b9758666be9654954cab8b9758666b86654954cab8c2f72eb0ccd650954cab8b976f2b0ccd650954cab8b9758666c17650954cab8b9758666b86650954cab8b9758666b8664e954cab8b9758666b8664c954cab8b9758666b8664a954cab8) else (if i < 30 then 0xb9758666c05692954cab8b9758666be2692954cab8b9758666b86692954cab8b9758666b86690954cab8b9758666b86684954cab8b9758666b86682954cab800172eb0ccd67a954cab0b9758686ccd67a954cab8b9758666c5567a954cab8b9758666b8667a954cab800172eb0ccd674954cab0b9758666c63674954cab8b9758666b86674954cab800172eb0ccd670954cab0b9758666c5c670954cab8b9758666b86670954cab8c2f72eb0ccd66c954cab8b976f2b0ccd66c954cab8b9758666c8966c954cab8b9758666b8666c954cab8 else 0xb9758666b866b4954cab8b9758666b866b2954cab8b9758666b866ae954cab8b9758666b866ac954cab8b9758666b866aa954cab8b9758666b866a8954cab800172ede4cd6a6954cab0b976f2b0ccd6a6954cab8b976f266c556a6954cab8b976f266be26a6954cab8b9758666bc66a6954cab8b976f266b866a6954cab8b9758666b866a6954cab8b9758666b866a4954cab800172eb0ccd69c954cab0b9758666c7869c954cab8b9758666c5569c954cab8b9758666b8669c954cab8b9758666b8669a954cab800172eb0ccd692954cab0))))) else (if i < 47 then (if i < 39 then (if i < 35 then (if i < 33 then (if i < 32 then 0xb9758666be26ee954cab8b9758666b866ee954cab8b9758666b866ea954cab8b9758666b866e6954cab8b9758666b866e2954cab8b9758666b866dc954cab8b9758666b866d6954cab8b9758666b866d2954cab8b9758666b866d0954cab800185eb0ccd6ce954cab0c2f72eb0ccd6ce954cab8c2f58666c556ce954cab8c2f58666be26ce954cab8b9758666bc66ce954cab8c2f58666b866ce954cab8b9758666b866ce954cab8b9758666b866c8954cab8b9758666b866c2954cab8b9758666b866bc954cab8b9758666b866ba954cab8 else 0xb9758666ba270c954cab8b9758666ba070c954cab8b9758666b9f70c954cab8b9758666b9e70c954cab8b9758666b9d70c954cab8b9758666b9b70c954cab8b9758666b9970c954cab8b9758666b9770c954cab8b9758666b9370c954cab8b9758666b9070c954cab8b9758666b8970c954cab8b9758666b9570c954cab8c5f72eb0ccd6f6954cab800172eb0ccd6f6954cab0b9758666c556f6954cab8b9758666be26f6954cab8b9758666b866f6954cab8c5572eb0ccd6ee954cab800172eb0ccd6ee954cab0b9758666c556ee954cab8) else (if i < 34 then 0xb9758666bc470c954cab8b9758666bc270c954cab8b9758666bc170c954cab8b9758666bc070c954cab8b9758666bbe70c954cab8b9758666bbd70c954cab8b9758666bbc70c954cab8b9758666bb970c954cab8b9758666bb670c954cab8b9758666bb270c954cab8b9758666bb070c954cab8b9758666bae70c954cab8b9758666bad70c954cab8b9758666bac70c954cab8b9758666bab70c954cab8b9758666baa70c954cab8b9758666ba970c954cab8b9758666ba870c954cab8b9758666ba670c954cab8b9758666ba470c954cab8 else 0xb9758666bd870c954cab8b9762666bd770c954cab8b9758666bd770c954cab8b9758666bd670c954cab8b9758666bd570c954cab8b9758666bd470c954cab8b9758666bd370c954cab8b9758666bd170c954cab8b9758666bd070c954cab8b9758666bcf70c954cab8b9758666bce70c954cab8b9758666bcd70c954cab8b975867d3cc70c954cab8b9758666bcc70c954cab8b9758666bcb70c954cab8b9758666bca70c954cab8b9758666bc970c954cab8b9758666bc770c954cab8b9758666bc670c954cab8b9758666bc570c954cab8)) else (if i < 37 then (if i < 36 then 0xb9758666be370c954cab8c5372eb0be270c954cab8c4372e66be270c954cab8c3f58666be270c954cab8b9758666be270c954cab8b8958666be270c954cab8b9756a66be270c954cab8c4753a66be270c954cab8c555865ebe270c954cab8c5f72e57be270c954cab8b9758666be170c954cab8b9758666be070c954cab8b9758666bdf70c954cab8b9758666bde70c954cab8b9758666bdd70c954cab8b9758666bdc70c954cab8bdf58666bdb70c954cab8b9758666bdb70c954cab8b9758666bda70c954cab8b9758666bd970c954cab8 else 0xb9758666bff70c954cab8b9758666bfd70c954cab8b9758666bfc70c954cab8b9758666bfb70c954cab8b9758666bf970c954cab8b9758666bf770c954cab8b9758666bf470c954cab8b9758666bf270c954cab8b9758666bf170c954cab8b9758666bf070c954cab8b9758666bef70c954cab8b9758666bee70c954cab8b9758666bec70c954cab8b9758666beb70c954cab8b9758666bea70c954cab8b9758666be970c954cab8b9758666be770c954cab8b9758666be670c954cab8b9758666be570c954cab8b9758666be470c954cab8) else (if i < 38 then 0xb9758666c1a70c954cab8b9758666c1970c954cab8b9758666c1870c954cab8b9758666c1670c954cab8b9758666c1770c954cab8b9758666c1570c954cab8b9758666c1370c954cab8b9758666c1270c954cab8b9758666c1170c954cab8b9758666c0f70c954cab8b9758666c0e70c954cab8b9758666c0d70c954cab8b9758666c0b70c954cab8b9758666c0770c954cab8b9758666c0670c954cab8b9758666c0470c954cab8b9758666c0570c954cab8b9758666c0370c954cab8b9758666c0170c954cab8b9758666c0070c954cab8 else 0xb9758666c3e70c954cab8b9758666c3d70c954cab8b9758666c3c70c954cab8b9758666c3b70c954cab8b9758666c3970c954cab8b9758666c3870c954cab8b9758666c3770c954cab8b9758666c3670c954cab8b9758666c3570c954cab8b9758666c3470c954cab8b9758666c3270c954cab8b9758666c3170c954cab8b9758666c3070c954cab8b9758666c2e70c954cab8b9758666c2f70c954cab8b9758666c2970c954cab8b9758666c2670c954cab8b9758666c2570c954cab8b9758666c2170c954cab8b9758666c1c70c954cab8))) else (if i < 43 then (if i < 41 then (if i < 40 then 0xb9758666c5170c954cab8b9758666c5070c954cab8b9758666c4f70c954cab8bf158666c4e70c954cab8b9758666c4e70c954cab8b9758666c4d70c954cab8b9758666c4c70c954cab8b9758666c4b70c954cab8b9765666c4a70c954cab8b9758666c4a70c954cab8b9758666c4970c954cab8b9758666c4870c954cab8b9758666c4770c954cab8b9758666c4570c954cab8b9758666c4370c954cab8b9758666c4270c954cab8b9758666c4170c954cab8b9758666c4070c954cab8b9758666c3f70c954cab8b9758686c3e70c954cab8 else 0xb9758666c5e70c954cab8b9758666c5d70c954cab8b9758666c5c70c954cab8b9758666c5a70c954cab8b9758666c5970c954cab8b9758666c5870c954cab8b9758666c5770c954cab8b9758666c5670c954cab8c5372eb0c5570c954cab8c4372e66c5570c954cab8c3f58666c5570c954cab8b9758666c5570c954cab8b8958666c5570c954cab8b9756a66c5570c954cab8c4753a66c5570c954cab8c555865ec5570c954cab8c5f72e57c5570c954cab8b9758666c5470c954cab8b9758666c5370c954cab8b9758666c5270c954cab8) else (if i < 42 then 0xb9758666c7a70c954cab8b9758666c7970c954cab8b9758666c7770c954cab8b9758666c7870c954cab8b9758666c7670c954cab8b9758666c7470c954cab8b9758666c7370c954cab8b9758666c7270c954cab8b9758666c7070c954cab8b9758666c6f70c954cab8b9758666c6e70c954cab8b9758666c6c70c954cab8b9758666c6a70c954cab8b9758666c6670c954cab8b9758666c6570c954cab8b9758666c6470c954cab8b9758666c6370c954cab8b9758666c6270c954cab8b9758666c6170c954cab8b9758666c6070c954cab8 else 0xb9758666ca070c954cab8b9758666ca170c954cab8b9758666c9b70c954cab8b9758666c9870c954cab8b9758666c9770c954cab8b9758666c9370c954cab8b9758666c8e70c954cab8b9758666c8c70c954cab8b9758666c8b70c954cab8b9758666c8a70c954cab8b9758666c8870c954cab8b9758666c8970c954cab8b9758666c8770c954cab8b9758666c8570c954cab8b9758666c8470c954cab8b9758666c8370c954cab8b9758666c8170c954cab8b9758666c8070c954cab8b9758666c7f70c954cab8b9758666c7d70c954cab8)) else (if i < 45 then (if i < 44 then 0xb9758666cb270c954cab8b9758666cb170c954cab80018bee5caf70c954cab0c5f72eb0caf70c954cab8c5f72e66caf70c954cab8b975ce66caf70c954cab8c3f58666caf70c954cab8b9758666caf70c954cab8b9753a66caf70c954cab8b9758666cae70c954cab8b9758666cad70c954cab8b9758666cab70c954cab8b9758666caa70c954cab8b9758666ca970c954cab8b9758666ca870c954cab8b9758666ca770c954cab8b9758666ca670c954cab8b9758666ca470c954cab8b9758666ca370c954cab8b9758666ca270c954cab8 else 0xb9758666cc170c954cab8b9758666cc070c954cab8b9758666cbe70c954cab80018aab0cbd70c954cab0c5572eb0cbd70c954cab8c4372e66cbd70c954cab8c5558666cbd70c954cab8bbb58666cbd70c954cab8b9758666cbd70c954cab8ac353a66cbd70c954cab8b9758666cbc70c954cab8b9758666cbb70c954cab8b9758666cba70c954cab8b9758666cb970c954cab8b9758666cb870c954cab8b9758666cb770c954cab8b9758666cb670c954cab8b9758666cb570c954cab8b9758666cb470c954cab8b9758666cb370c954cab8) else (if i < 46 then 0xb975866dccd70c954cab8b975866d4cd70c954cab8b975866cccd70c954cab8b975866c4cd70c954cab8b975866bccd70c954cab8b975866b4cd70c954cab8b975866accd70c954cab8b975866a4cd70c954cab8b9758669ccd70c954cab8b97586694cd70c954cab8b97586684cd70c954cab8b9758667ccd70c954cab8b97586674cd70c954cab8b9758666cc870c954cab8b9758666cc770c954cab8b9758666cc670c954cab8b9758666cc570c954cab8b9758666cc470c954cab8b9758666cc370c954cab8b9758666cc270c954cab8 else 0xb97586784cd70c954cab8b9758677ccd70c954cab8b97586774cd70c954cab8b9758676ccd70c954cab8b97586764cd70c954cab8b9758675ccd70c954cab8b97586754cd70c954cab8b97586744cd70c954cab8b9758673ccd70c954cab8b97586734cd70c954cab8b9758672ccd70c954cab8b97586724cd70c954cab8b9758671ccd70c954cab8b97586714cd70c954cab8b9758670ccd70c954cab8b97586704cd70c954cab8b975866fccd70c954cab8b975866f4cd70c954cab8b975866eccd70c954cab8b975866e4cd70c954cab8)))) else (if i < 55 then (if i < 51 then (if i < 49 then (if i < 48 then 0xb9758682ccd70c954cab8b97586824cd70c954cab8b9758681ccd70c954cab8b97586814cd70c954cab8b9758680ccd70c954cab8b97586804cd70c954cab8b975867fccd70c954cab8b975867f4cd70c954cab8b975867eccd70c954cab8b975867e4cd70c954cab8b975867dccd70c954cab8b975867d4cd70c954cab8b975867cccd70c954cab8b975867c4cd70c954cab8b975867b4cd70c954cab8b975867accd70c954cab8b975867a4cd70c954cab8b9758679ccd70c954cab8b97586794cd70c954cab8b9758678ccd70c954cab8 else 0xb975868d4cd70c954cab8b975868cccd70c954cab8b975868c4cd70c954cab8b975868bccd70c954cab8b975868b4cd70c954cab8b975868accd70c954cab8b975868a4cd70c954cab8b9758689ccd70c954cab8b97586894cd70c954cab8b9758688ccd70c954cab8b97586884cd70c954cab8b9758687ccd70c954cab8b97586874cd70c954cab8b9758686ccd70c954cab8b97586864cd70c954cab8b9758685ccd70c954cab8b9758684ccd70c954cab8b97586844cd70c954cab8b9758683ccd70c954cab8b97586834cd70c954cab8) else (if i < 50 then 0xb97586984cd70c954cab8b9758697ccd70c954cab8b97586974cd70c954cab8b9758696ccd70c954cab8b9758695ccd70c954cab8b97586954cd70c954cab8b9758694ccd70c954cab8b97586944cd70c954cab8b9758693ccd70c954cab8b97586934cd70c954cab8b9758692ccd70c954cab8b9758691ccd70c954cab8b97586914cd70c954cab8b9758690ccd70c954cab8b97586904cd70c954cab8b975868fccd70c954cab8b975868f4cd70c954cab8b975868eccd70c954cab8b975868e4cd70c954cab8b975868dccd70c954cab8 else 0xb97586a3ccd70c954cab8b97586a34cd70c954cab8b97586a2ccd70c954cab8b97586a24cd70c954cab8b97586a1ccd70c954cab8b97586a0ccd70c954cab8b97586a04cd70c954cab8b975869fccd70c954cab8b975869f4cd70c954cab8b975869eccd70c954cab8b975869e4cd70c954cab8b975869d4cd70c954cab8b975869cccd70c954cab8b975869c4cd70c954cab8b975869bccd70c954cab8b975869b4cd70c954cab8b975869accd70c954cab8b975869a4cd70c954cab8b97586994cd70c954cab8b9758698ccd70c954cab8)) else (if i < 53 then (if i < 52 then 0xb97586ac4cd70c954cab8b97586abccd70c954cab8b97586ab4cd70c954cab8b97586aaccd70c954cab8b97586aa4cd70c954cab8b97586a9ccd70c954cab8b97586a8ccd70c954cab8b97586a84cd70c954cab8b97586a7ccd70c954cab800188ea74cd70c954cab0c4772ea74cd70c954cab8b975baa74cd70c954cab8c47586a74cd70c954cab8bb1586a74cd70c954cab8b97586a74cd70c954cab8b97586a6ccd70c954cab8b97586a64cd70c954cab8b97586a5ccd70c954cab8b97586a4ccd70c954cab8b97586a44cd70c954cab8 else 0xb975ceb0ccd70c954cab8b975cab0ccd70c954cab8b975c6b0ccd70c954cab8b975c2b0ccd70c954cab8b975beb0ccd70c954cab8b975bab0ccd70c954cab8b975b6b0ccd70c954cab8b975b2b0ccd70c954cab8b975aeb0ccd70c954cab8b975aab0ccd70c954cab8b975a6b0ccd70c954cab8b975a2b0ccd70c954cab8b9759eb0ccd70c954cab8b9759ab0ccd70c954cab8b97596b0ccd70c954cab8b9758eb0ccd70c954cab8b9758ab0ccd70c954cab8c5572ead4cd70c954cab800172ead4cd70c954cab0b97586ad4cd70c954cab8) else (if i < 54 then 0xb97626b0ccd70c954cab8b97622b0ccd70c954cab8b9761eb0ccd70c954cab8b97616b0ccd70c954cab8b97612b0ccd70c954cab8b9760eb0ccd70c954cab8b9760ab0ccd70c954cab8b97606b0ccd70c954cab8b97602b0ccd70c954cab8b975feb0ccd70c954cab8b975fab0ccd70c954cab8b975f6b0ccd70c954cab8b975f2b0ccd70c954cab8b975eab0ccd70c954cab8b975e6b0ccd70c954cab8b975e2b0ccd70c954cab8b975deb0ccd70c954cab8b975dab0ccd70c954cab8b975d6b0ccd70c954cab8b975d2b0ccd70c954cab8 else 0xb9767ab0ccd70c954cab8b97676b0ccd70c954cab8b97672b0ccd70c954cab8b9766eb0ccd70c954cab8b9766ab0ccd70c954cab8b97666b0ccd70c954cab8b97662b0ccd70c954cab8b9765eb0ccd70c954cab8b9765ab0ccd70c954cab8b97656b0ccd70c954cab8b97652b0ccd70c954cab8b9764eb0ccd70c954cab8b97646b0ccd70c954cab8b97642b0ccd70c954cab8b9763eb0ccd70c954cab8b9763ab0ccd70c954cab8b97636b0ccd70c954cab8b97632b0ccd70c954cab8b9762eb0ccd70c954cab8b9762ab0ccd70c954cab8))) else (if i < 59 then (if i < 57 then (if i < 56 then 0xb976dab0ccd70c954cab8b976d6b0ccd70c954cab8b976d2b0ccd70c954cab8b976ceb0ccd70c954cab8b976cab0ccd70c954cab8b976c6b0ccd70c954cab8b976c2b0ccd70c954cab8b976beb0ccd70c954cab8b976b6b0ccd70c954cab8b976aeb0ccd70c954cab8b976aab0ccd70c954cab8b976a6b0ccd70c954cab8b976a2b0ccd70c954cab8b9769eb0ccd70c954cab8b9769ab0ccd70c954cab8b97696b0ccd70c954cab8b97692b0ccd70c954cab8b9768eb0ccd70c954cab8b97686b0ccd70c954cab8b9767eb0ccd70c954cab8 else 0xba772eb0ccd70c954cab8ba572eb0ccd70c954cab8ba372eb0ccd70c954cab8ba172eb0ccd70c954cab8b9f72eb0ccd70c954cab8b9d72eb0ccd70c954cab8b9972eb0ccd70c954cab8c5f712b0ccd70c954cab8b97712b0ccd70c954cab8001712b0ccd70c954cab0b9770ab0ccd70c954cab8b97706b0ccd70c954cab8b97702b0ccd70c954cab8b976feb0ccd70c954cab8b976fab0ccd70c954cab8b976f6b0ccd70c954cab8b976f2b0ccd70c954cab8b976eeb0ccd70c954cab8b976e6b0ccd70c954cab8b976deb0ccd70c954cab8) else (if i < 58 then 0xbd172eb0ccd70c954cab8bcf72eb0ccd70c954cab8bcd72eb0ccd70c954cab8bcb72eb0ccd70c954cab8bc972eb0ccd70c954cab8bc572eb0ccd70c954cab8bc372eb0ccd70c954cab8bc172eb0ccd70c954cab8bbf72eb0ccd70c954cab8bbd72eb0ccd70c954cab8bbb72eb0ccd70c954cab8bb972eb0ccd70c954cab8bb772eb0ccd70c954cab8bb572eb0ccd70c954cab8bb372eb0ccd70c954cab8bb172eb0ccd70c954cab8baf72eb0ccd70c954cab8bad72eb0ccd70c954cab8bab72eb0ccd70c954cab8ba972eb0ccd70c954cab8 else 0xbfd72eb0ccd70c954cab8bfb72eb0ccd70c954cab8bf972eb0ccd70c954cab8bf772eb0ccd70c954cab8bf572eb0ccd70c954cab8bf372eb0ccd70c954cab8bf172eb0ccd70c954cab8bef72eb0ccd70c954cab8bed72eb0ccd70c954cab8be972eb0ccd70c954cab8be772eb0ccd70c954cab8be572eb0ccd70c954cab8be372eb0ccd70c954cab8be172eb0ccd70c954cab8bdf72eb0ccd70c954cab8bdd72eb0ccd70c954cab8bdb72eb0ccd70c954cab8bd772eb0ccd70c954cab8bd572eb0ccd70c954cab8bd372eb0ccd70c954cab8)) else (if i < 61 then (if i < 60 then 0xc3172eb0ccd70c954cab8c2f72eb0ccd70c954cab8c2d72eb0ccd70c954cab8c2972eb0ccd70c954cab8c2572eb0ccd70c954cab8c2372eb0ccd70c954cab8c2172eb0ccd70c954cab8c1f72eb0ccd70c954cab8c1d72eb0ccd70c954cab8c1b72eb0ccd70c954cab8c1972eb0ccd70c954cab8c1572eb0ccd70c954cab8c1172eb0ccd70c954cab8c0f72eb0ccd70c954cab8c0d72eb0ccd70c954cab8c0b72eb0ccd70c954cab8c0972eb0ccd70c954cab8c0772eb0ccd70c954cab8c0572eb0ccd70c954cab8c0172eb0ccd70c954cab8 else 0xc6172eb0ccd70c954cab8c5f72eb0ccd70c954cab8c5d72eb0ccd70c954cab8c5b72eb0ccd70c954cab8c5972eb0ccd70c954cab8c5772eb0ccd70c954cab8c5572eb0ccd70c954cab8c5372eb0ccd70c954cab8c4f72eb0ccd70c954cab8c4d72eb0ccd70c954cab8c4b72eb0ccd70c954cab8c4972eb0ccd70c954cab8c4772eb0ccd70c954cab8c4372eb0ccd70c954cab8c3f72eb0ccd70c954cab8c3b72eb0ccd70c954cab8c3972eb0ccd70c954cab8c3772eb0ccd70c954cab8c3572eb0ccd70c954cab8c3372eb0ccd70c954cab8) else (if i < 62 then 0xc1b7beb0ccd70c954cab8c2f79ab0ccd70c954cab8c47776b0ccd70c954cab8c55762b0ccd70c954cab8c5f732b0ccd70c954cab8001732b0ccd70c954cab0c5172eb0ccd70c954cab8c7b72eb0ccd70c954cab8c7972eb0ccd70c954cab8c7772eb0ccd70c954cab8c7572eb0ccd70c954cab8c7372eb0ccd70c954cab8c7172eb0ccd70c954cab8c6f72eb0ccd70c954cab8c6d72eb0ccd70c954cab8c6b72eb0ccd70c954cab8c6972eb0ccd70c954cab8c6772eb0ccd70c954cab8c6572eb0ccd70c954cab8c6372eb0ccd70c954cab8 else 0xc5f8aae5d6170c954cab80018a6e5d6170c954cab0c5372eb0d4e70c954cab8b9758693d0d70c954cab8b975869b4fa70c954cab8b97586a2cec70c954cab8c5572eb0cdf70c954cab8c5f72eb0cda70c954cab8c5f88ee5ccd70c954cab8001886e5ccd70c954cab0b97692caccd70c954cab8b976c2c4ccd70c954cab8b976f2bf4cd70c954cab8c4772eb9ccd70c954cab8c5f72eb74cd70c954cab8c5572eb14cd70c954cab800172eb14cd70c954cab0c5588eb0ccd70c954cab800187eb0ccd70c954cab0c077e2b0ccd70c954cab8)))))) else (if i < 95 then (if i < 79 then (if i < 71 then (if i < 67 then (if i < 65 then (if i < 64 then 0xb9758666ca082e954cab8b9758666c2e82e954cab8b9758666c937e0954cab8b9758666c9b7d2954cab8b9758666c9b7c4954cab8b9758666c937c4954cab8b9758666c297c4954cab8b9758666c217c4954cab8b9758666c167c4954cab8b97586a2ccd78c954cab8b9758666ca078c954cab8b9758666c2e78c954cab800172eb0ccd778954cab000172eb0ccd772954cab0b976f2b0ccd75a954cab8c2f72eb0ccd740954cab8c5572eb0ccd726954cab800172eb0ccd726954cab0c5f72eb0ccd720954cab800172eb0ccd720954cab0 else 0x172eb0ccd70c97ccab0c2f72eb0ccd940954cab8b976f2b0ccd940954cab800172eb0ccd936954cab000172eb0ccd926954cab000172eb0ccd910954cab0b9758666ca0912954cab8b9758666c9b8aa954cab8b9758666c938aa954cab8b9758666c888aa954cab8c2f72eb0ccd85c954cab8b976f2b0ccd85c954cab8b9758666c8985c954cab800172eb0ccd852954cab0b9758666c5c852954cab8b9758666c55852954cab800172eb0ccd842954cab0b9758666c63842954cab8b9758666c55842954cab800172eb0ccd82c954cab0) else (if i < 66 then 0x172eb0ccd70cb90cab0b9758666ca070cb94cab8b9758666b865f8b94cab8b9758666c8e70cafccab8b9758666c9870cae0cab8b9758666c9870cac4cab8b9758666c8e70cac4cab8b9758666b865eeac4cab8b9758666b865deac4cab8b9758666b865c8ac4cab8b975869b4cd70ca54cab8b9758666ca070ca54cab8b9758666b865f8a54cab800172eb0ccd70ca2ccab000172eb0ccd70ca20cab0b976c2b0ccd70c9f0cab8c1b72eb0ccd70c9bccab8c5572eb0ccd70c988cab800172eb0ccd70c988cab0c5f72eb0ccd70c97ccab8 else 0xb9758666c8e8aae18cab8b9758666c778aae18cab8b9758666c987c4e18cab8b9758666c8e7c4e18cab8b9758666c9870cd9ccab8b9758666c8e70cd4ccab8b9758666c7770ccd8cab8c1b72eb0ccd70cbf0cab8b976c2b0ccd70cbf0cab8b9758666c7870cbf0cab800172eb0ccd70cbdccab0b9758666c5c70cbdccab8b9758666c5570cbdccab8b9758666be270cbdccab8b9758666b8663abdccab800172eb0ccd70cbbccab0b9758666c6370cbbccab8b9758666c5570cbbccab8b9758666be270cbbccab8b9758666b86642bbccab8)) else (if i < 69 then (if i < 68 then 0xb97586a2b104aa6545138b9758666b864aa65451b8b9758666b864aa65450b8b9758666b864aa6545038b9758666b864aa6544fb8b9758666b864aa6545c38b9758666b864aa6545bb8b97692b0ccd70c954de38c0772eb0ccd70c954d7b8c5572eb0ccd70c954d13800172eb0ccd70c954d130c5f72eb0ccd70c954cfb800172eb0ccd70c954cfb0c1b72eb0ccd940e18cab8b976c2b0ccd940e18cab800172eb0ccd930e18cab000172eb0ccd91ce18cab000172eb0ccd8eee18cab0b9758666ca08f0e18cab8b9758666c988aae18cab8 else 0xb9758666b864aa6545d38b9758666b864aa6545eb8b9758693b864aa4805e38b9758666b864aa6545e38b9758666b864aa6545db8b9758666b864aa6545cb8b9758666b865a6954fb38b9758666c1c70c954f838b9758666c2670c954f638b9758693ccd70c954eb38b9758666c2e70c954eb38b9758666b865f8954eb3800172eb0ccd70c954e63000172eb0ccd70c954e4b0b9758666b864aa6545438b9758666b864aa65453b8b9758666b864aa6545338b9758666b864aa65452b8b9758666b864aa6545238b9758666b864aa6545138) else (if i < 70 then 0xb9758666c1c70cafd2ab8b9758666c2670cae12ab8b9758666c2670cac52ab8b9758666c1c70cac52ab8b9758666b865e8ac52ab8b9758666b865d4ac52ab8b9758666b865a6ac52ab8b9758666b865e89551b38b9758666b865d49551138b9758666b864aa6542b38b9758666b864aa65434b8b9758666b864aa6546238b9758666b864aa6542ab8b9758666b864aa6542f38b9758666b864aa65461b8b9758666b864aa6546138b9758666b864aa65460b8b9758666b864aa6546038b9758666b864aa6545fb8b9758666b864aa6545f38 else 0xb9758666c047c4e192ab8b9758666c2670cd9d2ab8b9758666c1c70cd4d2ab8b9758666c0470cca12ab8c0772eb0ccd70cbf12ab8b97692b0ccd70cbf12ab8b9758666c0570cbf12ab800172eb0ccd70cbd12ab0b9758666c5570cbd12ab8b9758666be970cbd12ab8b9758666be270cbd12ab8b9758666b8663cbd12ab800172eb0ccd70cba92ab0b9758666c5570cba92ab8b9758666bf070cba92ab8b9758666be270cba92ab8b9758666b86644ba92ab800172eb0ccd70cb4d2ab0b9758666c2e70cb512ab8b9758666b865f8b512ab8))) else (if i < 75 then (if i < 73 then (if i < 72 then 0xb9758666b864aa65435b8b9758666b864aa6543538b9758666b864aa6542eb8b9758666b864aa6542e38b9758666b864aa6542db8b9758666b864aa6542cb8b976f266b534aa6542cb8b9758666b864aa6542c38b9758666b864aa6542bb8b9758666b864aa6542d38c0772eb0ccd85ce192ab8b97692b0ccd85ce192ab800172eb0ccd84ce192ab0b9758666c5584ce192ab800172eb0ccd838e192ab0b9758666c55838e192ab800172eb0ccd808e192ab0b9758666c2e80ae192ab8b9758666c267c4e192ab8b9758666c1c7c4e192ab8 else 0xb9758666b864aa65410b8b9758666b864aa65411b8c2f58666b674aa65411b8b9758666b864aa6541138b9758666b864aa6541038b9758666b864aa65417b8b9758666b864aa6544e38b9758666b864aa6543ab8b9758666b864aa6543a38b9758666b864aa65439b8b9758666b864aa6540fb8b9758666b864aa6541338b9758666b864aa6543938b9758666b864aa65438b8b9758666b864aa6543838b9758666b864aa65437b8b9758666b864aa65436b8b9769266b864aa58836b8b9758666b864aa6543638b9758666b864aa6543738) else (if i < 74 then 0xb9758666b864aa6541a38b9758666b864aa65418b8b9758666b864aa65419b8c0758666b864aa5d819b8b9758666b864aa6541938b9758666b864aa65455b8b9758666b864aa6545538b9758666b864aa6541838b9758666b864aa6543db8b9758666b864aa6543cb8b9758666c2e70c9543d38b9758666b865f89543d38b9758666b864aa6f03d38b9758666b864aa6543d38b9758666b864aa5883d38b9758666b864aa6543c38b9758666b864aa65412b8b9758666b864aa6543bb8b9758666b864aa6543b38b9758666b864aa6541238 else 0xb9758666b864aa6543eb8b9758666b864aa6543e38b9758666b864aa6542a38b9758666b864aa6545b38b9758666b864aa6545ab8b9758666b864aa6545a38b9758666b864aa65459b8b9758666b864aa6545938b9758666b864aa65458b8b9758666b864aa65457b8b975869b3863be65457b8b9758666b864aa6545738b9758666b864aa6545838b9758666b864aa65456b8b9758666b864aa6545638b9758666b864aa6541c38b9758666b864aa6541bb8b9758666b864aa6544db8b9758666b864aa6541b38b9758666b864aa6541ab8)) else (if i < 77 then (if i < 76 then 0xb9758666b864aa6546338b9758666b864aa65462b8b9758666b864aa6544138b9758666b864aa6542fb8b9758666c2e70c9541e38b9758666b865f89541e38b9758666b864aa6bc1e38b9758666b864aa6541e38b9758666b864aa5d81e38b9758666b864aa6541db8b9758666b864aa6541d38b9758666b864aa6541cb8b9758666b864aa65440b8b9758666ca070c6544038b9758666b865f86544038b9758666b864f86544038b9758666b864aa6544038b9758666b864446544038b9758666b864aa6543fb8b9758666b864aa6543f38 else 0xb9758666b864aa65465b8b9758666b864aa6546538b9758666b864aa51464b8b9758666b864aa4dc64b8b9758666b865f842464b800172eb0ccd70cbf064b0b975868cccd70cbf064b8b9758666c5570cbf064b8b9758666be270cbf064b8b9758666b86638bf064b8b9758666b865f8ac464b8b9758666c2e70c95464b8b9758666b865f895464b8b9758666ca070c65464b8b9758666b865f865464b8b9758666b864aa65464b8b9758666b8640a65464b8b9758666b863ec65464b8b9758666b864aa6546438b9758666b864aa65463b8) else (if i < 78 then 0xb9758657b864aa65445b8c5558666b864aa6544538bbb58666b864aa6544538b9758666b864aa6544538ac353a66b864aa6544538b9758666b864aa65444b8b9758666b864aa6544438b9758666b864aa65443b8b9758666b864aa6544338b9758666ca04aa65442b8b9758666c2e4aa65442b8b9758666bad4aa65442b8b9758666b864aa65442b8b9758666b534aa65442b8b9758666b864aa6544238b9758666b864aa65441b8b9758666b864aa65467b8b9758666b864aa6546738b9758666b864aa65466b8b9758666b864aa6546638 else 0xb97586a2b104aa65449b8b9758666b8649465449b8b9758666b8648c65449b8c1b58666b8646c65449b8b976c266b8644465449b8b975869b3863be65449b8b9758666b864aa62849b8b9758666b864aa61849b8c0758666b864aa5d849b8b9769266b864aa58849b8b9758666b864aa6544938b9758666b864aa65448b8b9758666b864aa6544838b9758666b864aa65447b8b9758666b864aa6544738b9758666b864aa65446b8b9758666b864aa6544638c5572eb0b864aa65445b8b975866d3864aa65445b8b9758666b864aa65445b8)))) else (if i < 87 then (if i < 83 then (if i < 81 then (if i < 80 then 0xb9758666c8e70c65449b8b9758666b865ee65449b8b9758666b865de65449b8b9758666c9b4aa65449b8b9758666c934aa65449b8b9758666c294aa65449b8b9758666c214aa65449b8c5372eb0b864aa65449b8c4372e66b864aa65449b8c3f58666b864aa65449b8b9758666b864aa65449b8b8958666b864aa65449b8b9756a66b864aa65449b8c4753a66b864aa65449b8c555865eb864aa65449b8c5f72e57b864aa65449b8b9758666b7b4aa65449b8b9758666b774aa65449b8c2f58666b674aa65449b8b976f266b534aa65449b8 else 0xb9758666b864aa6544d38c4753a66b864aa6544d38b97585c325532a2684cb800172eb0b864aa6544cb0b97586a73864aa6544cb8b9758666b864aa6544cb8b9758666b864aa6544bb8b9758666b864aa6544b38b9758666b864aa6544ab8b9758666b864aa6544a38b9756a66b864aa6544a38b9758693b864aa48049b8b9758666ca032a39449b8b9758666c2e4aa34c49b8b9758666b865f832449b8b9758666c2670c95449b8b9758666c1c70c95449b8b9758666b865e895449b8b9758666b865d495449b8b9758666c9870c65449b8) else (if i < 82 then 0xb9758666b864aa51469b8b9758666b864aa4dc69b8b9758666c2e4aa42469b800172eb0ccd85c95469b0b9758689ccd85c95469b8b9758666c5585c95469b8b9758666c2e7c495469b8b9758666c2e70c95469b8b9758666b865f895469b8b9758666c2e56295469b8b9758666c2e4aa7a869b8b9758666ca04aa65469b8b9758666c2e4aa65469b8b9758666b864aa65469b8b9758666b364aa65469b8b9758666b284aa65469b8b9758666b864aa6546938b9758666b864aa65468b8b9758666b864aa6546838c5372eb0b864aa6544d38 else 0xb9758666b864aa6543038b9758666b864aa65429b8b9758666b864aa65470b8b9758666b864aa6547038b9758666b864aa6546fb8b9758666b864aa6546f38b9758666b864aa4806eb8b9758666b864aa7586eb8b9758666b865106546eb8b9758666bb94aa6546eb8b9758666b864aa6546eb8b9758666b864aa6546e38b9758666b864aa6546db8b9758666b864aa6546d38b9758666b864aa6546cb8b9758666b864aa6546c38b9758666b864aa6546bb8b9758666b864aa6546b38b9758666b864aa6546ab8b9758666b864aa6546a38)) else (if i < 85 then (if i < 84 then 0xb9758666b865f865472b8b9758666ca056265472b8b9758666ca04aa65472b8b9758666c2e4aa65472b8b9758666b864aa65472b8b9758666b364aa65472b8b9758666b284aa65472b8b9758666b8640a65472b8b9758666b863ec65472b8b9758666b864aa6547238b9758666b864aa65471b8b9758666b864aa6547138b9758666b864aa65433b8b9758666b864aa6543338b9758666b864aa65432b8b9758666b864aa65430b8b9758666b864aa6543238b9758666b864aa65431b8b976c266b8644465431b8b9758666b864aa6543138 else 0xb9758666b8652a65477b8b9758666bbc4aa65477b8b9758666b864aa65477b8b9758666b863be65477b8b9758666b864aa6547738b9758666b864aa65476b8b9758666b864aa6547638b9758666b864aa65475b8b9758666b864aa6547538b9758666b864aa65474b8b9758666b864aa6547438b9758666b864aa65473b8b9758666b864aa6547338b9758666ca032a4ac72b8b9758666ca032a42472b800172eb0ccd94065472b0b97586804cd94065472b8b9758666ca08aa65472b8b9758666ca07c465472b8b9758666ca070c65472b8) else (if i < 86 then 0xb9758666b864aa6547e38b9758666b864aa6547db8b9758666b864aa6547d38b9758666b864aa6547cb8b9758666b864aa7307c38b9758666b865166547c38b9758666bc64aa6547c38b9758666b864aa6547c38b9758666b104aa6547c38b9758666b864aa6547bb8b9758666b864aa6547b38b9758666b864aa6540f38b9758666b864aa6547ab8b9758666b864aa6547a38b9758666b864aa6543438b9758666b864aa65479b8b9758666b864aa6547938b9758666b864aa65478b8b9758666b864aa6547838b9758666b864aa72477b8 else 0xc0758666b864aa5d884b8b9769266b864aa58884b8b9758666b864aa6548438b9758666b864aa65483b8b9758666b864aa6548338b9758666b864aa65482b8b9758666b864aa6548238b9758666b864aa65481b8b9758666b864aa6548138c4772e66b864aa65480b8b975ba66b864aa65480b8b9758666b864aa65480b8b9733657b864aa65480b8c4758666b864aa6548038bb158666b864aa6548038b9758666b864aa6548038ac33365eb864aa6548038b9758666b864aa6547fb8b9758666b864aa6547f38b9758666b864aa6547eb8))) else (if i < 91 then (if i < 89 then (if i < 88 then 0xc4372e66b864aa65484b8c3f58666b864aa65484b8b9758666b864aa65484b8b8958666b864aa65484b8b9756a66b864aa65484b8c4753a66b864aa65484b8c555865eb864aa65484b8c5f72e57b864aa65484b8b9758666b7b4aa65484b8b9758666b774aa65484b8c2f58666b674aa65484b8b976f266b534aa65484b8b97586a2b104aa65484b8b9758666b8649465484b8b9758666b8648c65484b8c1b58666b8646c65484b8b976c266b8644465484b8b975869b3863be65484b8b9758666b864aa62884b8b9758666b864aa61884b8 else 0xb9758693b864aa48084b8b9758666c2670c95484b8b9758666c1c70c95484b8b9758666b865e895484b8b9758666b865d495484b8b9758666b864aa73084b8b9758666b864aa72484b8b9758666c9870c65484b8b9758666c8e70c65484b8b9758666b865ee65484b8b9758666b865de65484b8b9758666b8651665484b8b9758666b8651065484b8b9758666c9b4aa65484b8b9758666c934aa65484b8b9758666c294aa65484b8b9758666c214aa65484b8b9758666bbc4aa65484b8b9758666bb94aa65484b8c5372eb0b864aa65484b8) else (if i < 90 then 0xb9758666b864aa6548bb800158666b864aa6548bb0ac333657b864aa6548bb8b9758666b864aa6548b38b9758666b864aa6548ab8b9758666b864aa6548a38b9758666b864aa65489b8b9758666b864aa6548938b9758666b864aa65488b8c4372e66b864aa6548838b9758666b864aa6548838c555865eb864aa6548838b97335c325532a440873800172e66b864aa6548730b9758666b864aa6548738b973365eb864aa6548738b9758666b864aa65486b8b9758666b864aa6548638b9758666b864aa65485b8b9758666b864aa6548538 else 0xb9758666b865f89549038b9758693b865629549038b9758666b864aa6f09038b9758666b864aa6bc9038b9758693b864aa6549038b9758666b864aa6549038b975861f3864aa6549038b9758666b864aa5d89038b9758666b864aa5889038b9758666b864aa65490b8b9758666b864aa6548fb8b9758666b864aa6548f38b9758666b864aa6548eb8b9758666b864aa6548e38b9758666b864aa6548db8b9758666b864aa6548d38c3f58666b864aa6548cb8b9758666b864aa6548cb8c5f72e57b864aa6548cb8ac3335c325532a4648bb8)) else (if i < 93 then (if i < 92 then 0xb9758666b864aa65496b8b9758666c9b4aa6549638b9758666b864aa6549638b9758666b864aa65495b8b9758666b864aa6549538b9758666b864aa65494b8b9758666b864aa6549438b9758666b864aa6549338b9758666b864aa65492b8b9758666b864aa6549238b9758666b864aa65491b8b9758666b864aa6549138b9758666b864aa5149038b9758666b864aa4dc903800172eb0d2770c9549030b9758693ccd70c9549038b9758693ca770c9549038b9758693c5570c9549038b9758666c2e70c9549038b9758693be270c9549038 else 0xb9758666b8657e9549db8b9758666b864aa6549db800172eb0ccd70c9549cb0b9758666b866ce9549cb8b9758666b865709549cb8b9758666b864aa6549cb8c0772eb0ccd70c9549bb8b97692b0ccd70c9549bb8b9758666b865a89549bb8b9758666b865c86549bb8b9758666b864aa6549bb8b9758666b864aa6549b38b9758666b864aa6549ab8b9758666b864aa6549a38b9758666c8e70c65498b8b9758666b864aa65498b8b9758666c934aa6549838b9758666b864aa6549838b9758666b864aa65497b8b9758666c9870c65496b8) else (if i < 94 then 0xb9758666c0570c954a2b8b9758666c164aa654a2b8b9758666b864aa654a2b8b9758666b864aa654a238b9758666b864aa654a1b8b9758666ca070c6542038b9758666b865f86542038b9758666b864de6542038b9758666b864aa6542038b9758666b8646c6542038b9758666b864aa6541fb8b9758666b864aa6541f38b9758666b864aa6541eb8b9758666b864aa654a13800172eb0ccd70c9549f30b97586764cd70c9549f38b9758666b865629549f38b9758666b864aa6549f3800172eb0ccd70c9549db0b9758666b866a69549db8 else 0x172eb0b864aa6540a310015865eb864aa65409b100172e57b864aa6540731b9758666b864aa65413b8b9758666b864aa654aa38b9758666b864aa654a83800172eb0ccd70c954a630b975867d4cd70c954a638b9758666be270c954a638b9758666b864aa654a63800172eb0ccd70c954a4b0b9758666bf070c954a4b8b9758666b864aa888a4b8b9758666b864aa654a4b800172eb0ccd70c954a3b0b9758666be970c954a3b8b9758666b864aa8d8a3b8b9758666b864aa654a3b8c0772eb0ccd70c954a2b8b97692b0ccd70c954a2b8))))) else (if i < 111 then (if i < 103 then (if i < 99 then (if i < 97 then (if i < 96 then 0x18a6b0b864aa65428b100188666b864aa65428b100158666b864aa65428b100156a66b864aa65428b10018be57b864aa65428b100158666b7b4aa65428b100158666b774aa65428b10016f266b534aa65428b1001586a2b104aa65428b100158666b8649465428b100158666b8648c65428b10016c266b8644465428b10015869b3863be65428b100158666b864aa62828b100158666b864aa61828b100169266b864aa58828b100158666b864aa65428310015866fb864aa65424b10015ce66b864aa654243100158666ba04aa6542231 else 0xe192a99521224c28b10013362ab864aa24c28b1001335f138632a24c28b100133558a5532a24c28b100158666b865f832428b100158666c557c4e1828b100158666c2670c95428b100158666c1c70c95428b100158666b865e895428b100158666b865d495428b100158666c5556295428b100158666c9870c65428b100158666c8e70c65428b100158666b865ee65428b100158666b865de65428b100158666be256265428b100158666c9b4aa65428b100158666c934aa65428b100158666c294aa65428b100158666c214aa65428b1) else (if i < 98 then 0x172ed24cd7c4e18b13100172ed24cd70cbbcb13100172ed24cd842954b13100172ed1ccd70c954b13100172ed24cd562954b13100172eb0ccd7c4e18aeb100172eb0ccd70c954aeb100172eb0ccd70c954ac3100172eb0ccd562954ac3100158666b864aa6540e3100172e66b864aa6540db100153a66b864aa6540d3100158666b8646c65415b100158666b864aa654293100158693b864aa48028b10015862ab864aa42428b1001585f138632a42428b100158558a5532a42428b100158666ca032a39428b100158666c2e4aa34c28b1 else 0x172eb0ccd562954c53100172eb0ccd70c928c5310018a6e5d6170c954c2b100172eb0ccd70c954c2b100172eb0ccd7c4e18c33100172eb0ccd70c954c33100172ead4cd70c954c3310018aab0cbd70c954c33100172eb0ccd6ee954c33100172eb0ccd562954c33100172eb0ccd70c918c33100172eb0ccd85c954c13100172eb0ccd70cbf0c03100180eb0ccd7c4e18bb3100180eb0ccd70cbdcbb3100180eb0ccd852954bb3100180ab0ccd70c954bb3100180eb0ccd562954bb3100172eb0ccd85c954b9b100172eb0ccd70cbf0b831)) else (if i < 101 then (if i < 100 then 0x172eb0ccd5ca7d8cab100172eb0ccd4aa7bccab100172eb0ccd4aa7accab100172eb0ccd93677ccab100172eb0ccd92677ccab100172eb0d3570c77ccab100172eb0d3470c77ccab100172eb0d3656277ccab100172eb0ccd70c954ca3100172eb0ccd70c954c9b100172eb0ccd70c954c93100172eb0ccd70c954c8b100172eb0ccd70c954c83100172eb0ccd70c954c7b100172eb0ccd70c954c73100172eb0ccd7c4e18c53100172eb0ccd70c954c531001712b0ccd70c954c5310018bee5caf70c954c53100172eb0ccd6f6954c531 else 0x18a6e5d6170c914cab100172eb0ccd70c914cab100172eb0ccd940908cab1001836b0ccd9368d8cab1001832b0ccd70c8d8cab1001836b0ccd5628d8cab100172eb0ccd9408cccab100172ed84cd926888cab100172ed7ccd70c888cab100172ed84cd562888cab100172eb0ccd70c874cab100172eb0ccd70c85ccab100172eb0ccd56285ccab100172eb0ccd70c830cab100172eb0ccd70c824cab100172eb0ccd70c81ccab100172eb0ccd70c7f4cab100172eb0ccd5627f4cab100172eb0ccd70c7e8cab100172eb0ccd70c7e0cab1) else (if i < 102 then 0x179ab0ccd554954cab100172ebf4cd54c954cab100172eb0cec536954cab100172eb0ccd70c950cab100172eb0ccd70c94ccab100172eb0ccd70c948cab100172eb0ccd70c944cab100172eb0ccd70c940cab100172eb0ccd70c93ccab100172eb0ccd70c938cab100172eb0ccd70c928cab1001712b0ccd70c928cab10018bee5caf70c928cab100172eb0ccd6f6928cab100172eb0ccd562928cab100172eb0ccd70c918cab100172ead4cd70c918cab10018aab0cbd70c918cab100172eb0ccd6ee918cab100172eb0ccd562918cab1 else 0x172eb0d45608954cab100172eb0ccd5c2954cab100172eb0ccd5ba954cab100172eb0ccd5a0954cab100172eb0ccd598954cab100172ede4cd57e954cab100185eb0ccd570954cab100172eb0ccd566954cab100172eb0ccd564954cab10018a6e5d61562954cab1001886e5ccd562954cab100187eb0ccd562954cab100172eb0ccd562954cab1001712b0ccd562954cab100172ead4cd562954cab100188ea74cd562954cab10018aab0cbd562954cab10018bee5caf562954cab100172eb0ccd55e954cab100172eb0ccd55c954cab1))) else (if i < 107 then (if i < 105 then (if i < 104 then 0x172eb0ccd6f6954cab1001712b0ccd6f6954cab10018bee5caf6f6954cab100172eb0ccd6ee954cab100172ead4cd6ee954cab10018aab0cbd6ee954cab10018a6e5d616ec954cab100172eb0ccd6ec954cab100185ab0ccd6ce954cab100172eddccd6a6954cab100172eb0ccd69c954cab100172eb0ccd692954cab100172eb0ccd67a954cab100172eb0ccd674954cab100172eb0ccd670954cab100172eb0ccd65e954cab100172eb0ccd658954cab100172eb0ccd654954cab100172eb0d44620954cab100172eb0d43620954cab1 else 0x18bee5cc870c954cab10018aab0cc870c954cab100153a66cc870c954cab100172e66cc170c954cab10018ab10cbd70c954cab10018a6b0cbd70c954cab10018aaad4bd70c954cab100156a66cbd70c954cab100158666cb370c954cab10018bf0fcaf70c954cab10018a6e5caf70c954cab10018bee24af70c954cab100171266caf70c954cab100172eb0ccd70a954cab100172eb0ccd708954cab100172eb0ccd706954cab100172eb0ccd704954cab100172eb0ccd702954cab100172eb0ccd700954cab100172eb0ccd6fe954cab1) else (if i < 106 then 0x17feb0ccd70c954cab1001732b0ccd70c954cab100172ab0ccd70c954cab1001726b0ccd70c954cab1001722b0ccd70c954cab1001712b0ccd70c954cab100170eb0ccd70c954cab100172eb04cd70c954cab100172eafccd70c954cab100172eaf4cd70c954cab100188ead4cd70c954cab100187ead4cd70c954cab100172ead4cd70c954cab100172eacccd70c954cab1001886a74cd70c954cab100187ea74cd70c954cab100172eb0ccc70c954cab100172eb0ccb70c954cab100172eb0cca70c954cab100172eb0cc970c954cab1 else 0x18bee5d5a70c954cab10018a6e5d5a70c954cab100172eb0d5170c954cab10018a711d4e70c954cab100172eb0d4270c954cab100172eb0d3370c954cab100172eb0d2470c954cab10018a711ccd70c954cab10018ab10ccd70c954cab10018bf0fccd70c954cab1001886e5ccd70c954cab100188ee24cd70c954cab1001886e24cd70c954cab100172edc4cd70c954cab100172ed64cd70c954cab100172ed04cd70c954cab100172eb14cd70c954cab100187eb0ccd70c954cab100184eb0ccd70c954cab1001826b0ccd70c954cab1)) else (if i < 109 then (if i < 108 then 0x172eb0ccd812954cab100172eb0ccd778954cab100172eb0ccd772954cab100172eb0ccd76a954cab100172eb0ccd768954cab100172eb0ccd726954cab100172eb0ccd720954cab10018bf1562370c954cab100000314e2370c954caa90000031562170c954caa900000317e1f70c954caa90018a711dcb70c954cab10018ab10dcb70c954cab10018bf0fdcb70c954cab10018a711d6170c954cab10018ab10d6170c954cab10018bf0fd6170c954cab10018a6e5d6170c954cab10018aae256170c954cab10018a6e256170c954cab1 else 0x172eb0ccd70c97ccab1001856e5d6199a954cab100172edd56199a954cab100172eb0ccd93e954cab100172eb0ccd936954cab100185eb0ccd92e954cab100172eb0ccd926954cab100172eb0ccd924954cab100172ede4cd918954cab100172eb0ccd910954cab100172eb0ccd8fc954cab100172eb0ccd8f6954cab100172eb0ccd85a954cab100172eb0ccd852954cab100185eb0ccd84a954cab100172eb0ccd842954cab100172eb0ccd840954cab100172ede4cd834954cab100172eb0ccd82c954cab100172eb0ccd818954cab1) else (if i < 110 then 0x172eb0ccd852bdccab100172eb0ccd70cbdccab1001836b0ccd70cbcccab100172eb0ccd842bbccab100172eb0ccd70cbbccab100172eb0ccd70cbb8cab100172ed84cd70cba0cab100172eb0ccd70cb90cab100172eb0ccd70cb68cab100172eb0ccd70cb5ccab100172eb0ccd930ac4cab100172eb0ccd91cac4cab100172eb0ccd5eeac4cab100172eb0ccd5deac4cab100172eb0ccd5c8ac4cab100172eb0ccd70ca2ccab100172eb0ccd70ca20cab100172eb0ccd70ca10cab100172eb0ccd70ca0ccab100172eb0ccd70c988cab1 else 0x17beb0ccd7b6e18cab100172ec4ccd7aee18cab100172eb0cfa798e18cab100172eb0ccd7c4deccab100172eb0ccd7c4ddccab100172eb0ccd940dcccab100185eb0ccd930d9ccab100185eb0ccd7c4d9ccab100172eb0ccd940d90cab100172ede4cd91cd4ccab100172ede4cd7c4d4ccab100172eb0ccd7c4d24cab100172eb0ccd7c4cbccab100172eb0ccd82eca0cab100172eb0ccd70cc84cab100172eb0ccd70cc74cab100172eb0ccd930c40cab100172eb0ccd91cc40cab100172eb0d457c4c40cab100172eb0ccd70cbeccab1)))) else (if i < 119 then (if i < 115 then (if i < 113 then (if i < 112 then 0x172eb0d3686ae18cab100172eb0ccd826e18cab100172eb0ccd81ee18cab100172eb0ccd802e18cab100172eb0ccd7fae18cab100172ed84cd7e0e18cab1001836b0ccd7d2e18cab100172eb0ccd7c8e18cab100172eb0ccd7c6e18cab10018a6e5d617c4e18cab1001886e5ccd7c4e18cab100187eb0ccd7c4e18cab100172eb0ccd7c4e18cab1001712b0ccd7c4e18cab100172ead4cd7c4e18cab100188ea74cd7c4e18cab10018aab0cbd7c4e18cab10018bee5caf7c4e18cab100172eb0ccd7c0e18cab100172eb0ccd7bee18cab1 else 0x1836e5d6199b26ccab100185ee5d6199b260cab100172ed856199b24ccab100172ede56199b238cab100172eb0ccd936f88cab100172eb0ccd926f88cab100172eb0ccd852f88cab100172eb0ccd842f88cab100172eb0ccd82cf88cab100182ee5d6199ae18cab100172ed756199ae18cab100172eb0ccd93ce18cab100172eb0ccd930e18cab1001836b0ccd92ee18cab100172eb0ccd91ce18cab100172eb0ccd91ae18cab100172ed84cd918e18cab100172eb0ccd8eee18cab100172eb0ccd8d6e18cab100172eb0ccd8d0e18cab1) else (if i < 114 then 0x172ed84cd70cba9113100172eb0ccd8aae190eb100172eb0ccd8aae19063100172eb0ccd8f0e1902b100172eb0b864aa4805e3100172eb0ccd70c954f83100172eb0ccd70c954f63100172eb0d368aae18efb100172eb0ccd70cbd0efb100172eb0ccd70cba8efb100172eb0ccd70c954e63100172eb0ccd70c954e4b100172eb0ccd70c954e2b100172eb0ccd70c954e23100172eb0b104aa654513100172eb0ccd70c954d13100172eb0ccd70c954cfb1001822e5d6199b280cab100172ed4d6199b280cab100172eb0d0099b280cab1 else 0x180eb0ccd70cbcd2ab100172eb0ccd926ba92ab100172eb0ccd70cba92ab100172eb0ccd70cba52ab100172ed24cd70cba12ab100172eb0ccd70cb4d2ab100172eb0ccd70cb252ab100172eb0ccd70cb192ab100172eb0ccd84cac52ab100172eb0ccd838ac52ab100172eb0ccd5e8ac52ab100172eb0ccd5d4ac52ab100172eb0ccd5a6ac52ab100172eb0ccd8aae19253100172eb0ccd8aae19233100172eb0ccd70cbf12031001836b0ccd8aae191b31001836b0ccd70cbd11b3100172eb0ccd70cbf1183100172ed84cd8aae191131)) else (if i < 117 then (if i < 116 then 0x172eb0ccd7eae192ab100172eb0ccd8aaded2ab100172eb0ccd8aaddd2ab100172eb0ccd85cdc52ab100185eb0ccd8aad9d2ab100185eb0ccd84cd9d2ab100172eb0ccd85cd852ab100172ede4cd8aad4d2ab100172ede4cd838d4d2ab100172eb0ccd8aad392ab100172eb0ccd8aacf52ab100172eb0ccd912cd92ab100172eb0ccd70cc892ab100172eb0ccd70cc792ab100172eb0d458aac412ab100172eb0ccd84cc412ab100172eb0ccd838c412ab100172eb0ccd70cbe92ab100172eb0ccd936bd12ab100172eb0ccd70cbd12ab1 else 0x187eb0ccd8aae192ab100172eb0ccd8aae192ab1001712b0ccd8aae192ab100172ead4cd8aae192ab100188ea74cd8aae192ab10018aab0cbd8aae192ab10018bee5caf8aae192ab100172eb0ccd8a6e192ab100172eb0ccd8a4e192ab10017e2b0ccd89ce192ab100172ecaccd894e192ab100172eb0d0d87ce192ab100172eb0ccd858e192ab100172eb0ccd84ce192ab100180eb0ccd84ae192ab100172eb0ccd838e192ab100172eb0ccd836e192ab100172ed24cd834e192ab100172eb0ccd808e192ab100172eb0ccd7f0e192ab1) else (if i < 118 then 0x172eb0d1399b0b92ab100180ee5d6199b0a52ab100172eb0ccd8ab0a52ab100185ee5d6199b0992ab100172ed256199b0852ab100172eb0ccd8ab0852ab100172ede56199b0712ab1001806e5d6199ae192ab100172ed156199ae192ab100172eb0d2794ee192ab100172eb0ccd90ae192ab100172eb0ccd902e192ab100172eb0ccd8e8e192ab100172eb0ccd8e0e192ab100172ed24cd8c6e192ab100180eb0ccd8b8e192ab100172eb0ccd8aee192ab100172eb0ccd8ace192ab10018a6e5d618aae192ab1001886e5ccd8aae192ab1 else 0x17f6e5d6199ae197e3100172ece56199ae197e3100172eb0d1999ae197e3100180ee5d6199ae197bb100172eb0ccd8aae197bb1001836e5d6199ae197a3100172eb0ccd7c4e197a3100172ed256199ae1977b100172eb0ccd8aae1977b100172ed856199ae19753100172eb0ccd7c4e19753100172eb0ccd70cbf03ab100172e66b864aa58836b100172eb0ccd8aaf8958b100172e66b534aa6542cb100172eb0ccd9371552ab100172eb0ccd9271552ab100172eb0ccd9111552ab10017fae5d6199b0b92ab100172eced6199b0b92ab1))) else (if i < 123 then (if i < 121 then (if i < 120 then 0x172eb0ccd5f8ac464b100172eb0ccd70cbf062b100172eb0ccd85c95462b100172eb0ccd94065462b100158666b864aa6bc1e3100172e66b864f8654403100172eb0ccd9406543eb100172eb0b863be65457b100172eb0ccd931155c33100172eb0ccd91d155c33100172eb0ccd8ef155c33100172eb0ccd931099c33100172eb0ccd91d071c33100172eb0ccd84cf89c33100172eb0ccd838f89c33100172eb0ccd808f89c33100158666b864aa5d819b100172e66b864aa6f03d3100172eb0ccd85c9543bb100158666b674aa65411b1 else 0x171266b864aa65449b10018aa5eb864aa65449b100172e66b7b4aa65449b100172e66b774aa65449b100185e66b674aa65449b100172ea2b104aa65449b100172e66b8649465449b100172e66b8648c65449b100183666b8646c65449b100172e9b3863be65449b100172e66b864aa62849b100172e66b864aa61849b100180e66b864aa5d849b100172e66b864aa654493100172e6d3864aa65445b100177666b864aa654453100172e66bad4aa65442b100172eb0b865f842464b10018a2e5d6199ae1864b100172eb0ccd70cc7064b1) else (if i < 122 then 0x172e66c2e4aa34c49b100172e66b865f832449b100172e66c557c4e1849b100172e66c2670c95449b100172e66c1c70c95449b100172e66b865e895449b100172e66b865d495449b100172e66c5556295449b100172e66c9870c65449b100172e66c8e70c65449b100172e66b865ee65449b100172e66b865de65449b100172e66be256265449b100172e66c9b4aa65449b100172e66c934aa65449b100172e66c294aa65449b100172e66c214aa65449b10018a6e5b864aa65449b100187e66b864aa65449b100172e66b864aa65449b1 else 0x172eb0bc64aa6547c3100172eb0b8652a65477b100172eb0ccd32a4ac72b100172eb0ca032a42472b100172eb0ccd94115472b10018a2e5d6199a65472b100172e66b8644465431b100172eb0b864aa7586eb100172eb0c2e4aa42469b100172eb0ccd85cf8869b10018a2e5d6199a95469b100172eb0ccd4aa7a869b100188e66b864aa6544d3100172eb0b864aa6544cb100172e66b864aa6544a3100172e93b864aa48049b100172e2ab864aa42449b100172df138632a42449b100172d58a5532a42449b100172e66ca032a39449b1)) else (if i < 125 then (if i < 124 then 0x1886e5b864aa65484b100187eb0b864aa65484b100172eb0b864aa65484b1001712b0b864aa65484b100172ead3864aa65484b100188ea73864aa65484b100172eb0b7b4aa65484b100172eb0b774aa65484b100185eb0b674aa65484b100172ede3534aa65484b100172eb0b8649465484b100172eb0b8648c65484b1001836b0b8646c65484b100172ed838644465484b100172eb0b864aa62884b100172eb0b864aa61884b100180eb0b864aa5d884b100172ed23864aa58884b100172eb73864aa65480b1001762b0b864aa6548031 else 0x172eb0c2670c95484b100172eb0c1c70c95484b100172eb0b865e895484b100172eb0b865d495484b100172eb0c5556295484b100172eb0b864aa73084b100172eb0b864aa72484b100172eb0c9870c65484b100172eb0c8e70c65484b100172eb0b865ee65484b100172eb0b865de65484b100172eb0be256265484b100172eb0b8651665484b100172eb0b8651065484b100172eb0c9b4aa65484b100172eb0c934aa65484b100172eb0c294aa65484b100172eb0c214aa65484b100172eb0bbc4aa65484b100172eb0bb94aa65484b1) else (if i < 126 then 0x172eb0ccd70c9549db100172eb0ccd70c9549cb100172eb0ccd5a89549bb100172eb0ccd70c65498b100172eb0ccd4aa654983100172eb0ccd70c65496b100172eb0ccd4aa654963100172eb0d277c4e18903100172eb0ccd70cbdc903100172eb0ccd70cbbc903100172eb0ccd852954903100172eb0ccd842954903100172eb0d2670c954903100172eb0d2570c954903100172eb0d2756295490310018bee5b864aa6548cb100158666b864aa6548bb10018aab0b864aa654883100172e66b864aa654873100172eb0c557c4e1884b1 else 0x314e2370c954caaa0000031562170c954caaa00000317e1f70c954caaa00172eb0ccd7c4e18a63100172eb0ccd70c954a63100172eb0ccd70c954a4b100172eb0ccd70c954a3b100172eb0ccd80ae18a2b100158666b864de654203100172eb0ccd70c9549f3100172eb0ccd5629549f31)))))))
private def st6 (i : Nat) : Nat := unpack st6Packed 84 20 i
private def adj6Packed (i : Nat) : Nat := (if i < 5 then (if i < 2 then (if i < 1 then 0x1c20833020011404400000800002800800400810c20420042000010014820011000461020011010811800870d20403810430c200104000100004004c else 0x1801001470010400823c20802c30040c30090020030c73420420020010832c80001c024208300d0800000070000870074c120b2000000410c5000142) else (if i < 3 then 0x4822820020010070010401561080001401020000010000011890800003050053403c20813c60030070050000801850000040c21825c06c11c1002103 else (if i < 4 then 0x6011000430000000801001870410030c308a1020c00823c004010000710414200008804201624400b10208410114e04020a0830061800410851c0 else 0x614b00444220d1800410020430020010c11410800400880420c21803091801412400410400072401010c00461400801c004000148b040080004081))) else (if i < 8 then (if i < 6 then 0x400405c00400c10060801810402020000023cd1841401800c000004300134700204024000a0000c000c7000010430010c024000004020108200008e else (if i < 7 then 0x10010440410c14070010000410526871840020840c21040452400461820020842000820c90410810c204010a00300500211c0830011410008c3008 else 0x8200000430708b00118218a2471400c02010010090430420d200e1400000011c40860c21c01400050000020cd0000c3103000340084000005086040)) else (if i < 9 then 0xc01c304218014800304610b0020010001c50820801440c02c02000050024d00400471000c90070410c00410870400c2180282003000042041042201 else (if i < 10 then 0x84000042a0734100e1410030c00000c000038804000404c0420c358000610720600e1010020000440c02c00800020804420800000030400811060c0 else 0xb0010460803810432410c208708100028600000300020008100100200208118c000085103040140))))
private def adj6 (i : Nat) : Nat := unpack adj6Packed 6 80 i
private def loc6Packed (i : Nat) : Nat := (if i < 24 then (if i < 12 then (if i < 6 then (if i < 3 then (if i < 1 then 0x4130006d500000007571b00046e6db8d10196aa0b800034800040476f00048400000000020900000000040186f5954e70001fe40045224816a00099600069f97422b6559c100028b0003a367b50f0008b16b40003cd7ae0710001a209745e0000009876e25943590002741250003b789b7987d0000539000 else (if i < 2 then 0x5fa0000000002d68260000b02467b666a77c00081d2d365238c8780007f30006eb0430006935a60000f00ba3a000002f0001d690b0008876910000170000000005362b751f8da0005a55d81b65f60004038069c798a2c99e23f19bd00000004600000068800000058749681129021b4347a30002df5b4000 else 0x43600036d62d52c4284d54400f30002e191b8f317264f6160001a72382de6ea40709a5319ab0008ca28376956200242c00087b00060564d1223280300642d57260000e700040c42f0011451420827057ba4da6fc19900000048a47d5a36256c70000dd7c920471600033500019b0003d35bb1ee7d5)) else (if i < 4 then 0x5660892bc07e6ff3982200001820000006440002f31f12a08054ec3d700000000075e0000000004a31de8c908c2616470d808337725f7377b50008988f88c029a00052150686e53238e6f30009252247ee8321fd9773b90000000004950ed9423bb00046f88e0000005e569a2f73a63cc00035d000825 else (if i < 5 then 0x4d400081b65961a0810009a400071577f7044a66a30000444f70006c48ac26d2e400000000018792800069220b0000000000000000000003be00087a0000000000005513e40007f75f41b778176d5a14e917a00000090158a00035f00067e7ec1aa00000000073856000000000000082e000000 else 0x29d0007ed9957001c659c0002e60000004881c20004460104660005194170000000002da3da71115d0ae00074678a62b00000065100019438942a00000b0000a72fa00000d62c3f30003f803f0009260000990002a20006cc86a7e700046037d6e300081f6e100089f5ce8400005f980e8190004bf000000))) else (if i < 9 then (if i < 7 then 0x81a72094805100085900097967f8430000000000002b40083cf0000000000002568f568700000009385b0000000000002bf78424400000047516469b0002d00000c703b39d4ac2f10d139b9023046ad8902b290523a23793c00043f88c4214cf6b347f0000009ba5b90006c34c58090940005fc057000 else (if i < 8 then 0x3af3290008d749319d8a57e800066e0000003df1f34985160001104d96a40000005110675c82fb6787ce63b0c00000008eb0630000000000131842d80680000000000000002d736f4c81234256f20000000004d29a15861f257f77862443c0006665429277990000004bb8e3000000000992000783000000 else 0x47439c5e83fc0007766d31bb28014c7f400042d98b6d90005ac00000054d00060f66055200000050800000085f2810006676dc2797f200049a0007554f000022900059d6b04fd0007309ae00000000000088d5008fc82c23f00000000089283a00000092f00072416b0009b17647a91ce9b2000000000)) else (if i < 10 then 0x7cb00000020064a0007d30005234151cb7390006020003190e91270008306980008470000000000002aa00054b01f5739721928f46355a291300000086437e7829cf73693d6cf7090b304200000000024e11859b0007da00095326771900048d87592153a51200052800008f96c0000000000000d02848b0 else (if i < 11 then 0x2cc0008de4ff7415c049b6739c36b76d037000090614857b4646a056d96605c1b49945f080337b7cc95900088900035e24a54186997c9d182100050d94f8b80dc0000007b768b00000091851c0003c63db3c52cf73c0003150f100015e3907bf55c1be0000009d44b242900056300332517952000015760a else 0x8450000000000000003450529bb0006286ec18e78b3737434b83d45e00000000003171885500000000006309b30004e00005bd56e05316c5ad0003322be0b60009390008977d918b7958ec5030124670004020ac1800005e20006403ca0006e50002697580000c414e1e720819e64e000569000712000000)))) else (if i < 18 then (if i < 15 then (if i < 13 then 0x6fa95200058100041284a00027000044e0007c872a0004780001638833f588f8807918c67960002550000007736ee00024766224200079a6330000000004eb0003977070003630008274507af1e40000000a50000bc86b86c7ff5050004916146295430000004f60000003fe0005d67f081575d933 else (if i < 14 then 0x6bd89609066c57c0005d000067c5021700002b382000031c51e0006c074c40a2a893b8330f620c10900054f3513fd0000007e00273868e72490005e15290004cb6de1ab16d00003e6f86560007b91e68f08510002f600004f0003e78664a88f98186960002fc1f001b41f00000058c00000000072f10634a else 0x34b14a97f0000b70500a400026f8be4d163c1f99502ed6340003e09d60000006c65750ee5f50000009430000370397010006a20eb5720000003462e922e1132e050b11c0004510004be13e93600000036400030a0000005ec7cd95120e0f47270002300000006f50005fd1358dd4c30000e1685000)) else (if i < 16 then 0x63d1d82bd48e0451e193111d5370000007359712f81c70ce9171cd6680002277d60000000008d009b0002938ef0ec00000098300031e5ca0005250000006800009b81028bb2f47105ff00000087300000000060e34730121561c88559e0004ee2600003bc96130c0004a089417194d1a80009d500099e7b2 else (if i < 17 then 0x80c00000094500000041c0007e100054a0fe00027d1590008ce4381c80007631a367685a00004121135c4774f143290024f19336100000070b0000000798840000001d219644500002654e0ff23100079c86019f0009a72120001df1a91146380007893859c95a80005dd0006d600000000004c29c393000 else 0x11a0003e63182222871a42026190009708a700068f0007850c600084f1580000f80e500063948b2a68720004713cb00062e8ae94b4734941db3dc12a0000003a200058900049c20739a92d0000000000008740863de00092b0000000008913d200040b89c00000061176b59600047c0005140000000000d3))) else (if i < 21 then (if i < 19 then 0x76144d5150005332436328a855a0000007df34e42489a0007a067d70d0007a472b48502312110400e2164370000000000001ff56b5c32632539202f90001011280000008e200025700000000045b58e65c7217903806d70000000005900160000009c60001860000000001ad52f86700099f98c44f2ec8cf else (if i < 20 then 0x43d9104900b24e500049200023469c00000000000039f74b00053c4e28225300003246b22320000001320000003f974a30b47a0000002364f31f62ca7543278c40000003e825a3e20003a90001c300000000000033f80286368d55f7c26e60007b478f9b911264900000716e3e508b0001e265a8ba35793a else 0x9930000550002146f76ab2912850000000005709dc4c10000000000000008d873f20600023b7062a926e28801495633600038b0006ac3c066f0000007d70000004801542410f70000000000002582972e500022524d3ff22f00062f7507652233841d083573b0004628a06fe79d54c00080a80f02d0003dd)) else (if i < 22 then 0x95e97b63f00000070a00000007d94112d15600070f2c00000003080006bc4220007023c85c406170c4445772a723516800006d38f0004ef0003a128f0004c727c17f0210006705f31f59845b500000020a37f9bf92c3f209d94668c2b00000000fb1d50009cb88215b8b44cc1676df00092a0967450fd000 else (if i < 23 then 0x81279210c73d05498e4a406c00000058886500000005a0000005d96ed0000000040002ae2af00000012053e00082800084133a4761770000000002c20009a99769d70003887de33c44b00000000000065700064c4b055b0004790002770000006f01bf69d3060000004979150cf00018d00000057a0003d5 else 0x4b500077b5c111b7184d657d0000000929df61368200072e85671400055600045a2ce5040000008c300008a1ed5df98f7a70008427bc0008db9673f66f183f0003210009da4bc6c900026845f1380007c54e86060001dd0007e478c00007331d0c38b304e56496e0001812333ac0000000001da0000008f7))))) else (if i < 36 then (if i < 30 then (if i < 27 then (if i < 25 then 0x9240008a30656c80005cb4310002010a09aa84c00000000000026496800000010800000009c00084e6037d10000000006fd3140000003a800000054958b1ec00016f8b61e933856f15211f00071f8d50007b30006b686110700051a5820008b770e0956420001c00005c256a5ee00036c00000f73427e5d7 else (if i < 26 then 0x8cc0c81978e600004b0005b267468411e85297d8cd68a0004867ac3100fa0c18d429b65e0060001763091910008e97ef64399000002b83440900006e96f00000000000097e1c98c26bf7ad7970aa07626500068372346305d71e4a20000003a598d0004c90009973332d49381758d680087d0002fe82a18f else 0x21a8040001bc0352dc5c78072ea5130000000000006bb21e1308cb4060009858a949f59361549e0000007a29c200037500089341000003270888a0001f40365a005e00000000000034288100078e25d0560002e31c177a0003315bc4fa6630009de00082b5ef00037c4e65d121c0000007aa74d989)) else (if i < 28 then 0xcd2ab00030e00000018a0009e127f15f00063a0000009654ce0000000000e200074831a0001bd13b0009690000000002b67c60001850001290000200006ef0d25977b092389d0000004ad0e80000000003f021f5480000000000000ad0001170000002c79d355300057e2947a539100000073a19c10e6e0 else (if i < 29 then 0x20568902a0000000007a10004145278a400097a3550009e04186360007518aa0000000e422d0000000a14ea0000006a83208a24c62766729115557db34f4e31ba0be1342db0000004b69320003c90006010008ab6c20006790000380003370007a80000003bd0004de6410000000349733504ae90784b303 else 0x3d676e0001160000005b10007032e79c44c412682d0004ab00000042000000025b8dc4598fb01504d9573eb2520002ee6503b37729990003664d879f00000002500000000024c3825459d200000000029250a87902c0000000de00000063734d0006189a60000009640000fc0000007be0009220008ea))) else (if i < 33 then (if i < 31 then 0x2b900000052e0d61a60000000009b01d97298380004bd0bd8d953f1553ba6277dd28c07c00029f8460005bf00014f3b60005b800012e9a38551b38c81610002ac00000010a4162eb00047048c44200028a98839500041d0001e09583ce00026b15300051b0006694fc8e589e0002392e852b000000 else (if i < 32 then 0x3053a481e4af76059f0db0008951ea7770000007a61690000003fa00000000004a0d50000009632b50770d70000006d800000000000055900078d4f58105f862225e3005407427c140884d5cc3ed0007f100000015c0009801440005cf34945500047e46b55800075a91d7560002c36530005476e98b9000 else 0x9b700025955d0008530ea0000000003a70bf0007fc9cc77e07800013109833b5d37d46234680000005aa4ba5b30000ca0000008580007747c40000000000009441f86544e15eb06000000083d00027200060b27891452d90391f23c0000b400085c2184ca0002f50b50008e800001818953d1c50001e5584)) else (if i < 34 then 0x5a433d37a0006170000007bb8446f900000048100000016200093f0e68e117836b24b0008290001d14300007f603c0009080b90001600000000007e36610317d85d423e09e4f80003d91af0a947b00000099c5af00025100083700000000038d64b00074f09100057801a80b00086265d0000ef000000387 else (if i < 35 then 0x479bc42b17e4230c59868705240004aa18c5ed36e00a6a90004dd0000000000001d34b92c50000000000000005b685e0722b890a3539dd94e3d00000003e90000da00000007004000000048700000073195d32f5c50699ac0002d932e3740008ff40f5ea00077d28639400000000014d29836a1c4435 else 0x6082a53991ca19a0000005b700095b5d501d0000000004dc00033073e0002710cc0002197b191a0006a60000007444b400077500077069464621061d6ba00000091600051010f3f700c33e94786800019509f0000000000000000006e800000010345d2ad3ad5db5dc0009a041b136000780000)))) else (if i < 42 then (if i < 39 then (if i < 37 then 0x9a20000003b18f20d90000000000006006640000002260003236ca6cd20f9c50002952a38af95500000065f5170000000000001cf75f1fb0000000001b599876227b0000000004b17493fb5852c40000003d890e00000000000050c35600000000000014039600001c0000000000003444d700021d88807b else (if i < 38 then 0x4db6f44822406d28fa7f86753b40007135986c593e0000000000002e21650001ef76613f0000006b88ed02e4b796b2c194c00046530f00015a30d36096d4a99ce1e31159300007f917c3653722c890d7d24f90000cb7e98500000009ad0007cf6e70000004df8080004fe6fb7473c20096af6d18163ee000 else 0x6040007678e099d0000009cd50727a50999a0000000003583b03628b261f0003f482486d75b0003400002130000003ea6973540008ee66d0a200000012f1500000001a50001433bf0001dc3130000003078390007fa05b3b200013d19800017d00000000040e32a41146d0007590008bd0000000001a1173)) else (if i < 40 then 0x8716f600062613c00075262a6450001497fd4c22289094a15610a36e400000087e45687c3c338374e57405841a1338310000007dc0007940e006272592e00000055e91c00017401e5e729900000000003d76c2cd0006a775700039e81308871a3b884878661e65b43e00082390c08e00076a00000058f000 else (if i < 41 then 0x85491272c0c90006710000000007e22d15a700078714b0df1240008d302495481c68614700000078808000599b0000003438fe7795650000000008df6100000007ca00000031f8ad5ba4896995e400005f1b000000084931153b0000008fd43a0004580bb00053400058d9b48c17ea1eb6a1518 else 0x4a50005e60007b83690005f226a5380003ef9043e10004722ef8175791cc0005359827400000002620005835d200000046c71c66b0a80006ae0000003164cd0009be3920003812cb00008460700043b40500029e0005807fb4530000000000003ae82f04800000000000096200040d1fa0007e60ab95c))) else (if i < 45 then (if i < 43 then 0x5fe83e00046a0000007c75de00052a0000002bb8c77f500062075c6656c15fb00018332b1662c61b100000017b00011100088600012c0003ab2ff00083c9d80007c085d0004a700044c0003260009d900065807a0e30000007fe0000855f10af8f100091950100000068187600067a0000001413aa000 else (if i < 44 then 0x1a04f26770000000004837c300035a6ce9c00000003760292036310005465440009340000002b194a00041900008d5f755438a5923e38360003680f54470001372502540002dd9405ae0000740000009490008bc9db33951d1fc0000f90000000000009914410002892754e40220002730006950004f4000 else 0x3d19a83c422a88b6cb0000004c000031b57172200026625c0009370870005cd32c2d28776120000d40005c63020590001d404941e8b543300000035206a5765e977100095a42600061b37828d45c0008d219000024500056c85700059a8a60003124fb2965220000c24d379b83b5c9000000000454000)) else (if i < 46 then 0x26c50e0000005be5680003c700060d0008990281398bf5e33792170f20b10006dd0004b39290008a168e96a1b900000035b9d00002a163e6908c54ed48f0007ab1d749d00000091e7939789a55da79e1b24276be2a45a96098145574990004390000005679b600000044323d000733000000341000526000 else (if i < 47 then 0x6218f637134c2ba9af80128290f03300022c95f01169e2f20009b532d6b11e800000000046144845728e0009816da3ec20d3c160c71d4495b000093510d0000000000008e442e87f6a52f000044a06f97507f6b91ae0007eb0003346b506b10000000003a10b0001f772813a0000000009606481197321ac else 0x9ca00012b00000000032200000072d4695990665ab1051510006d43671b87170a64d080d3b59c81460007bd0002fd2217e5591000753768))))))
private def loc6 (i : Nat) : Nat := unpack loc6Packed 12 80 i
private def st7Packed (i : Nat) : Nat := (if i < 28 then (if i < 14 then (if i < 7 then (if i < 3 then (if i < 1 then 0xb9758666b86620954ca8518172eb0ccd70cbf12a9950a302e5d6199ae1958a5532a14605cbac3335c326f4aa65428c0b9758666b864aa8d8ca8518172eb0ccd70c955111950a302e5d6199ae192a9df32a14605cbac3335c325535e65428c0b9758666b864aa654bb0518172eb0ccd70c954ca9620a300005cbac3335c325532a125c5cbac3335c325532a14424c000172eb0ccd70c954ca8487172eb0ccd70c954ca85109100005cbac3335c325532a111c5cbac3335c325532a1442240c5572eb0ccd70c954ca81380002e5d6199ae192a995026e317dcbac3335c325532a03a0000b9758666b864aa6540738 else (if i < 2 then 0xc0772eb0ccd70c954ca85180002e5d6199ae192a9950a2e2e5dbcac3335c325532a14605cbb6158666b864aa65428c0b97692b0ccd70c954ca8518172eb9d6199ae192a9950a302e5d61a9d335c325532a14605cbac351666b864aa65428c0b975869b4cd70c954ca8518172eb0d2799ae192a9950a302e5d619bf335c325532a14605cbac33365eb864aa65428c0b9758666caf70c954ca8518172eb0ccd940e192a9950a302e5d6199b155c325532a14605cbac3336173864aa65428c0b9758666be270c954ca8518172eb0ccd740e192a9950a302e5d6199ae19b3a5532a14605cbac3335c33534aa65428c0 else 0x172eb0ccd70c954ca9627172eb0ccd8c6e192a9952c502e5d6199b155c325532a58a05cbac3335f13864aa654b140b9758666b86562954ca9628188ee5d6199ae192a99503500005cbac3335c325532a069c60db9758666b864aa65415c000172eb0ccd70c954ca82b7172eb0ccd70c954ca9200a302e5d6199ae192a99521214605cbac3335c325532a39428c0b9758666b864aa654698518172eb0ccd70c954ca8930a302e5d6199ae192a995192146062fb9758666b864aa65428c0c5572eb0ccd70c954ca8518188ee5d6199ae192a9950a3030bdcbac3335c325532a146060db9758666b864aa65428c0)) else (if i < 5 then (if i < 4 then 0xb9758666b865629551119580002e5d6199ae192aa0532ae2e5d6199b155c325540a6560000b9758666b864aa7d8cab8b9758666b86562954fb19580002e5d6199ae192a9ea32ae2e5d6199b0b9c32553d46560000b9758666b864aa77ccab8b9758666c5570c954ef9958172eb0ccd86ae192a9df32b02e5d6199af89c32553be65605cbac3335c32b14aa77ccac000172eb0ccd70c954eb19570002e5d6199ae192a9bc32ae0005cbac3335c325535e655c000b9758666b864aa654bb38b9758666c5c70c954ca9768172eb0ccd8aae192a9952ed02e5d6199af89c325532a5da05cbac3335c32b14aa654bb40 else 0xb9758666b865caac52a9958172eb0ccd70cb5158a5532b00005cbac3335c32aa4aa655c5cbac3335c32b1554954cac000172eb0ccd70ca992a9957172eb0ccd70cac55325532b00005cbac3335c329b4aa655c5cbac3335c32b1536954cac000172eb0ccd70ca552a99570002e5d6199ae193e25532ae0005cbac3335c326f4aa655c000b9758666b864aa8d8cab8b9758666c5570c9551b1958172eb0ccd7d2e192aa3632b02e5d6199af89c325546c65605cbac3335c32b14aa8d8cac000172eb0ccd70c955111957172eb0ccd8aae192aa2232b02e5d6199afc1c325544465605cbac3335f13864aa888cac0) else (if i < 6 then 0x172eb0ccd70cac52a9957172ede56199ae1958a5532b02e5db0ac3335c32b14aa65605cbb4958666b86562954cac0b975fab0ccd70cac52a9958172eb0d4e99ae1958a5532b02e5d61a8b335c32b14aa65605cbac34da66b86562954cac0b9758693ccd70cac52a9958172eb0cec99ae1958a5532b02e5d6199b2f5c32b14aa65605cbac333657b86562954cac0b9758666ca070cac52a9958172eb0ccd8aae1958a5532b02e5d6199b0b9c32b14aa65605cbac3335f1386562954cac0b9758666b866ceac52a9958172eb0ccd70cd4d58a5532b02e5d6199ae19882b14aa65605cbac3335c32fc562954cac0 else 0xb9758666be270cc412a99580002e5d6199ae198225532ae2e5d6199ae19883044aa6560000b9758666b865f8954cab8b9758666c5570cbf12a9958172eb0ccd7c4e197e25532b02e5d6199ae198e2fc4aa6560000b9758666b865ca954cab800172eb0ccd70cb512a99570002e5d6199ae195fa5532ae2e5d6199ae19a9abf4aa6560000b9758666b86570954cab8b9758666b866ceae12a995818bee5d6199ae1958a5532b03155cbac3335c32b14aa6560623b9758666b86562954cac0c2f72eb0ccd70cac52a99581836e5d6199ae1958a5532b0301dcbac3335c32b14aa65605e6b9758666b86562954cac0))) else (if i < 10 then (if i < 8 then 0x172eb0ccd7aee192a9957172eb0ccd7c4f5dc325532b00005cbac3335e63864aa655c5cbac3335f13cc70c954cac000172eb0ccd78ce192a99570002e5d6199aeb5c325532ae0005cbac3335d03864aa655c000b9758666b866ce954cab8b9758666c5570cd9d2a9958172eb0ccd7c4e19b3a5532b00005cbac3335c33534aa655c5cbac33362ab866a6954cac0b9758666be270cd4d2a99580002e5d6199ae199b25532ae2e5d6199b155c33364aa6560000b9758666b86650954cab8b9758666be270cca12a99580002e5d6199ae198e25532ae0005cbac3335c33104aa655c5cbac33362ab86620954cac0 else (if i < 9 then 0xbdf72eb0ccd7c4e192a99580002e5d6199af89c325532ae2e5dbcac3335f13864aa65605cbb6158666be270c954cac0b97692b0ccd7c4e192a9958172ec4d6199af89c325532b02e5d61a9d335f13864aa65605cbac351666be270c954cac0b975869b4cd7c4e192a9958172eb0d2799af89c325532b02e5d619f5335f13864aa65605cbac33365ebe270c954cac0b9758666caf7c4e192a9958172eb0ccd940f89c325532b02e5d6199b155f13864aa65605cbac3336173e270c954cac0b9758666c177c4e192a9958172eb0ccd80af89c325532b00005cbac3335edb864aa655c5cbac3335f13db70c954cac0 else 0xb9758666c788aae192a99580002e5d6199b139c325532ae2e5d6199b156273864aa6560000b9758666c4a70c954cab8b9758666c55894e192a99580002e5d6199b0f9c325532ae2e5d6199b1561f3864aa6560000b9758666c3570c954cab800172eb0ccd85ce192a9957172eb0ccd8ab0b9c325532b00005cbac33360bb864aa655c000b9758666c0570c954cab800172eb0ccd7e0e192a99570002e5d6199afa5c325532ae317dcbac3335f13864aa656062ab9758666be270c954cac0c4772eb0ccd7c4e192a9958185ee5d6199af89c325532b0306dcbac3335f13864aa6560603b9758666be270c954cac0)) else (if i < 12 then (if i < 11 then 0xc5572eb0ccd8aae192a9958188ee5d6199b155c325532b030bdcbac33362ab864aa656060db9758666c5570c954cac0c0772eb0ccd8aae192a995817e2e5d6199b155c325532b00005cbac33362ab864aa655c5cbb7958666c5570c954cac0b976c2b0ccd8aae192a9958172ed256199b155c325532b02e5d95ac33362ab864aa65605cbac353a66c5570c954cac0b97586a2ccd8aae192a9958172eb0d3699b155c325532b02e5d61a4f3362ab864aa65605cbac343666c5570c954cac0b9758666cbd8aae192a9958172eb0ccd95f155c325532b02e5d6199b2822ab864aa65605cbac333644c5570c954cac0 else 0x172eb0d4599ae192a99570002e5d61a6d335c325532ae0005cbac349e66b864aa655c000b975868cccd70c954cab800172eb0d1399ae192a99570002e5d61a1b335c325532ae0005cbac340266b864aa655c000b975867d4cd70c954cab800172eb0cec99ae192a99570002e5d619bf335c325532ae0005cbac336a66b864aa655c000b9758666cbd70c954cab800172eb0ccd95ee192a99570002e5d6199b29dc325532ae0005cbac3336503864aa655c000b9758666c8970c954cab800172eb0ccd8f0e192a99570002e5d6199b18dc325532ae0005cbac33362e3864aa655c62fb9758666c5570c954cac0) else (if i < 13 then 0x18aae5d6199ae192a9957000311dcbac3335c325532ae000617b9758666b864aa655c000c1b72eb0ccd70c954cab800180ee5d6199ae192a99570002fc5cbac3335c325532ae0005efb9758666b864aa655c000bcd72eb0ccd70c954cab8001776e5d6199ae192a99570002ec5cbac3335c325532ae000000b9758666b864aa6558000b976f2b0ccd70c954cab800172ed856199ae192a99570002e5da4ac3335c325532ae0005cbb2b58666b864aa655c000b97626b0ccd70c954cab800172ebf56199ae192a99570002e5d73ac3335c325532ae0005cbadd58666b864aa655c000b97586a74cd70c954cab8 else 0xb9758666b864aa6542883c8172eb0ccd70c954ca89310100005cbac3335c325532a201c000b9758666b864aa65457b8b975869b4cd70c954ca8af8180ee5d6199ae192a99506700005cbac3335c325532a0cdc5cbac3335c325532a24c3d4000172eb0ccd70c954ca87a7185ee5d6199ae192a99504700005cbac3335c325532a08dc000b9758666b864aa65436b8b97692b0ccd70c954ca86d80002e5d6199ae192a9950b2e2e5dbcac3335c325532a1660000b9758666b864aa6545e38b9758693ccd70c954ca8bc80002e5d6199ae192a995144e2e5d61a8b335c325532a28a0000c5f72eb0ccd70c954cab8)))) else (if i < 21 then (if i < 17 then (if i < 15 then 0xb9758666b864f8954ca8938172eb0ccd70c9551b19512702e5d6199ae192aa2232a24e05cbac3335c32553be65449c0b9758666b864aa6f0ca8938172eb0ccd70c954ca97612702e5d6199ae192a9952c424e05cbac3335c325532a24c45c000172eb0ccd70c954ca88b7172eb0ccd70c954ca89311500005cbac3335c325532a229c5cbac3335c325532a24c42c000172eb0ccd70c954ca8857172eb0ccd70c954ca90919300005cbac3335c325532a325c5cbac346666b864aa65464c0b9758666c5570c954ca8c98172eb0ccd7c4e192a99519302e5d6199ae1958a5532a3260000b9758666b864aa6541e38 else (if i < 16 then 0xb976f2b0ccd70c954ca8938172ed856199ae192a99512702e5da4ac3335c325532a24e05cbac353a66b864aa65449c0b97586a2ccd70c954ca8938172eb0d3699ae192a99512702e5d61a4f335c325532a24e05cbac336a66b864aa65449c0b9758666cbd70c954ca8938172eb0ccd95ee192a99512702e5d6199b281c325532a24e05cbac33362ab864aa65449c0b9758666c2e70c954ca8938172eb0ccd7c4e192a99512702e5d6199aeb5c325532a24e05cbac3335c33674aa65449c0b9758666b866a6954ca8938172eb0ccd70cc412a99512702e5d6199ae197e25532a24e05cbac3335c32b14aa65449c0 else 0x172eb0ccd70c954ca8d37172eb0d1399ae192a9951a702e5d6199b155c325532a34e05cbac3335f13864aa65469c0b9758666b86562954ca8d380002e5d6199ae192a995134e2e5d61a9d335c325532a26a05cbac3335c325532a48049c0b9758666b864aa654848938172eb0ccd70c954ca8e512702e5d6199ae192a9951a624e05cbac3335c325532a32449c0c5f72eb0ccd70c954ca893818aae5d6199ae192a9951270311dcbac3335c325532a24e0617b9758666b864aa65449c0c1b72eb0ccd70c954ca8938180ee5d6199ae192a99512702eedcbac3335c325532a24e0000b9758666b864aa65449b8)) else (if i < 19 then (if i < 18 then 0xb9758666b864aa654b11098172eb0ccd70c954ca90920300005cbac3335c325532a405c5cbac3335c325532a424804000172eb0ccd70c954ca9007172eb0ccd70c954ca9091f100005cbac3335c325532a3e1c5cbac3335c325532a42477c000172eb0ccd70c954ca8ef7172eb0ccd70c954ca9091cb00005cbac3335c325532a395c5cbac340266b864aa65472c0b9758666c5570c954ca8e58172eb0ccd7c4e192a9951cb02e5d6199ae1958a5532a3960000b9758666b864aa65431b8b976c2b0ccd70c954ca8638172eb0ccd70c954ca9091bb00005cbac3335c325532a375c5cbac3335c325532a42469c0 else 0xb975869b4cd70c954ca9098172eb0d2799ae192a99521302e5d6199b2f5c325532a42605cbac333657b864aa65484c0b9758666ca070c954ca9098172eb0ccd8aae192a99521302e5d6199b0b9c325532a42605cbac3335f13864aa65484c0b9758666bc670c954ca9098172eb0ccd70cd9d2a99521302e5d6199ae19a9a5532a42605cbac3335c33104aa65484c0b9758666b865f8954ca9098172eb0ccd70cac52a99521302e5d6199ae194aa5532a42605cbac3335c325546c65484c0b9758666b864aa888ca9098172eb0ccd70c954ef99521302e5d6199ae192a9d632a42605cbac3335c325532a5d884c0) else (if i < 20 then 0xb9758666b86562954ca92080002e5d6199ae192a995232e2e5d6199b2bdc325532a4660000b9758666b864aa6548838b9758666cbd70c954ca9108172eb0ccd70c954ca9202130317dcbac3335c325532a426062ab9758666b864aa65484c0c4772eb0ccd70c954ca9098185ee5d6199ae192a9952130306dcbac3335c325532a4260603b9758666b864aa65484c0bb172eb0ccd70c954ca90980002e5d6199ae192a995212e2e5dbcac3335c325532a42605cbb6158666b864aa65484c0b97692b0ccd70c954ca9098172eb756199ae192a99521302e5d61a9d335c325532a42605cbac351666b864aa65484c0 else 0x172eb0ccd70c954ca84972002b0ccd70c954ca851092e4005cbac3335c325532a121c800ac3335c325532a144243900172eb0ccd70c954ca84472002b0ccd70c954ca851088e4005cbac3335c325532a04dc800b9758666b864aa654073900172eb0ccd70c954ca9457172eb0ccd7c4e192a99528b00005cbac3335c325532a101c5cbac3335c325532a144204000172eb0ccd70c954ca9377172eb0ccd70cac52a99526f00005cbac3335c325532a4adc5cbac3336503864aa65495c000172eb0ccd70c954ca9207172eb0ccd94ee192a99524102e5d6199b155c325532a48205cbac3335f13864aa6549040))) else (if i < 24 then (if i < 22 then 0x158666caf70c954ca85172002b0ccd940e192a9950a2e40056199b155c325532a145c800ac3336173864aa65428b900158666be270c954ca85172002b0ccd740e192a9950a2e40056199ae19b3a5532a145c800ac3335c33534aa65428b900158666b86620954ca85172002b0ccd70cbf12a9950a2e4005cbac333558a5532a145c80000158666ab14aa65428b100158666b86562954ca85172002b0ccd70c9bd2a9950a2e40056199ae192aa3632a145c800ac3335c325544465428b900158666b864aa77cca85172002b0ccd70c954d79950a2e40056199ae192a9952ec145c800ac3335c325532a58828b9 else (if i < 23 then 0x2b0ccd8aae192a85162002e5d6199af89c31950a2e400000ac3335f138632a1458800c5f58666b864aa65428b90018aab0ccd70c954ca8517200311d6199ae192a9950a2e400617ac3335c325532a145c800c1b58666b864aa65428b900180eb0ccd70c954ca85172002e5d6199ae192a9950a2e4005bcac3335c325532a145c800b6158666b864aa65428b9001692b0ccd70c954ca85172002b9d6199ae192a9950a2e400561a9d335c325532a145c800ac351666b864aa65428b90015869b4cd70c954ca85172002b0d2799ae192a9950a2e4005619bf335c325532a145c800ac33365eb864aa65428b9 else 0x172eb0ccd70cbbcca96272002e5d6199b0852a9952c4e4005cbb49335c325532a589c800b9758666ab14aa654b13900172eb0ccd70c954ca96172002e5d6199ae192a9952b8e4005cbac3335c325532a55dc800b9758666b864aa6540d3900172eb0ccd70c954ca82b72002b0ccd70c954ca9200a2e4005cbac2e192a995212145c800001585c325532a42428b100158666b864aa6548485172002b0ccd70c954ca8e50a2e40056199ae192a9951a6145c800b97335c325532a24c28b900158666b864aa6544985172000004cd70c954ca8930a2c40056199ae192a995192145c800b9758666c5570c95428b9)) else (if i < 26 then (if i < 25 then 0x18aae5d6199ae192a98672000005cbac3335c325530cc4005cbac3335c325532a619c800b9758666b864aa654c23900172eb0ccd70c954ca98272002e5d6199ae192a995300e400000c0758666b864aa5d98800c0772eb0ccd70c954bb3900172eb0ccd8aae192a97672002e5d6199af89c31952ece4005cbac3335c32f732a5d9c800b9758666c294aa654bb3900180eb0ccd70c954ca97672002e5d6199aac52a9952ece4005cbac3335c325532a5cdc800b9758666b864aa654b839000002e5da499ae192a96262002e5da4ac3335c32552c4e4005cbac33362ab864aa589c800b9758666be270c654b139 else 0x172eb0ccd562954fb19572002e5d6199ae192a9ea32ae400000b975869b3863be6558800b975869b4cd70c77ccab900172eb0ccd940e18ef99572002e5d6199af89c31df32ae4005cbac3335c32fc3be655c800b975869b3864aa77ccab900172eb0ccd562954ef99572002e5d6199ae191b1df32ae4005cbac3335c32223be655c800b9758666b864aa778cab900172eb0ccd70c954ed19572002e5d6199ae192a9d632ae4005cbac3335c325538c655c800b9758666b864aa6f0cab900172eb0ccd70c954d79957200317dcbac3335c3255314e400000b9758666b864aa6298800b9758666b864aa654c539) else (if i < 27 then 0x172eb0ccd70c95520195720000060dac3335c323632ac40060db9758666b8646c655c800b9758666be270c8d8cab900172eb0ccd9369551b1957200306d6199ae192aa3632ae4005cbac333558a5546c655c800b9758666b864aa8cccab900172eb0ccd70c9551819572000005cbb61335c322232ac4005cbb6158666b86444655c800b9758666be270c888cab900172eb0ccd9269551119572002e5db099ae192aa2232ae4005cbac333558a55444655c800b9758666b864aa884cab900172eb0ccd70c9550e19572002e5d6199ae192aa1632ae4005cbac3335c325540a655c800b9758666b864aa7d8cab9 else 0x172eb0ccd5a8ac52a99572002e5d6199ae195525532ae4005cbac333558aaa4aa655c800b9758666b8654c954cab900172eb0ccd562a992a99572002e5d6199ae194fa5532ae4005cbac3335c329b4aa655c800b9758666ab1536954cab900172eb0ccd70ca552a99572002e5d6199ae1942a5532ae4005cbac3335c327c4aa655c800b9758666b864de954cab90018bee5d6199ae192519572000005cbac3335c324a32ac4005cbac3335c3255494655c800c5572eb0ccd70c918cab9000002e5d6199ae192319562002e5d6199ae192aa4632ae4005cbac3335c3255488655c800b9758666b864aa908cab9))))) else (if i < 42 then (if i < 35 then (if i < 31 then (if i < 29 then 0x172ed856199aac52a99572002e5da4ac333558a5532ae4005cbafd58666ab14aa655c800b97586a74cd562954cab900172eb0d4599aac52a99572002e5d61a6d33558a5532ae4005cbac349e66ab14aa655c800b97586764cd562954cab900172eb0ccd97aac52a99572002e5d6199b2bd58a5532ae4005cbac3336502b14aa655c800b9758666c55562954cab900172eb0ccd85cac52a99572002e5d6199af8958a5532ae4005cbac3335c32b14aa655c800b9758666b67562954cab900172eb0ccd6a6ac52a99572002e5d6199ac4158a5532ae4005cbac33357e2b14aa655c800b9758666ae5562954cab9 else (if i < 30 then 0x172eb0ccd70cbdd2a99572002e5d6199ae197a25532ae4005cbac3335c32f34aa655c800b9758666b865de954cab900172eb0ccd70cba92a99572002e5d6199ae197425532ae4005cbac3335c32e54aa655c800b9758666b865b6954cab900172eb0ccd70cb512a99572002e5d6199ae196525532ae4005cbac3335c32bf4aa655c800b9758666b86570954cab90018bee5d6199aac52a99572003155cbac333558a5532ae400623b9758666ab14aa655c800c2f72eb0ccd562954cab9001836e5d6199aac52a9957200301dcbac333558a5532ae4005e6b9758666ab14aa655c800b976f2b0ccd562954cab9 else 0x172eb0ccd70cd852a99572000005cbb79335a9a5532ac4005cbb7958666b534aa655c800b976f266b866a6954cab900172eb0ccd70cd492a99572002e5d6199ae19a6a5532ae4005cbac3335c33484aa655c800b9758666b8666c954cab900172eb0ccd70cca12a99572002e5d6199ae198e25532ae400000b97586a2b104aa6558800b97586a2ccd620954cab900172eb0ccd940c412a99572002e5d6199b0b98825532ae4005cbac3515c33104aa655c800b9758666b67620954cab900172eb0ccd6a6c412a99572002e5d6199ae1987a5532ae4005cbac3335c330b4aa655c800b9758666b86608954cab9)) else (if i < 33 then (if i < 32 then 0x172eb0ccd7aee192a99572002e5d6199af41c325532ae4005cbac3335e63864aa655c800b9758666bc670c954cab900172eb0ccd76ce192a99572002e5d6199aeb5c325532ae4005cbac3335d03864aa655c800c5f72eb0ccd6f6954cab9000002e5d6199aded2a99562002e5d6199ae19bda5532ae40062ab9758666b774aa655c80000172eb0ccd6ee954cab100172eb0ccd70cddd2a99572002e5d6199ae19baa5532ae4005cbac3335c33734aa655c800b9758666b866e2954cab90000030bd6199ad9d2a995620030bdcbac3335b3a5532ae400617ac3335c33674aa655c800b9758666b866c8954cab9 else 0x172eb0ccd8aae192a99572002e5d6199b139c325532ae4005cbac3336253864aa655c800b9758666c4270c954cab900172eb0ccd87ce192a99572002e5d6199b0d5c325532ae4005cbac333614b864aa655c800b9758666c2670c954cab900172eb0ccd84ae192a99572002e5d6199b085c325532ae4005cbac33360e3864aa655c800b9758666c1a70c954cab900172eb0ccd82ee192a99572002e5d6199b035c325532ae4005cbac333602b864aa655c800b9758666bf970c954cab900172eb0ccd7e0e192a99572002e5d6199afa5c325532ae4005cbac3335f13864aa655c800b9758666bdb70c954cab9) else (if i < 34 then 0x172eb0ccd974e192a995720000062fb972bdc325532ac40062fb9758657b864aa655c800c5f72e66caf70c954cab900187eb0ccd95ee192a99572002e5d4e99b2bdc325532ae4005cbac3336573864aa655c800b9758666ca770c954cab900172eb0ccd936e192a99572002e5d6199b261c325532ae4005cbac33364bb864aa655c800b9758666c9370c954cab900172eb0ccd91ce192a99572002e5d6199b231c325532ae4005cbac333644b864aa655c800b9758666c7f70c954cab900172eb0ccd8f0e192a99572002e5d6199b1b1c325532ae4005cbac333631b864aa655c800b9758666c5c70c954cab9 else 0x172eb0d1e99ae192a99572002e5d61a33335c325532ae4005cbac344e66b864aa655c800b9758686ccd70c954cab900172eb0d0099ae192a99572002e5d619f5335c325532ae4005cbac33b266b864aa655c800b975866fccd70c954cab900172eb0cda99ae192a99572002e5d6199b321c325532ae4005cbac333663b864aa655c800b9758666cc670c954cab900172eb0ccd98ae192a995720000062aac32f5c325532ac40062ab975865eb864aa655c800c4372e66cbd70c954cab90018aab0ccd97ae192a99572002b0d4e99b2f5c325532ae4005cbac33365e3864aa655c800b9758666cbb70c954cab9))) else (if i < 38 then (if i < 36 then 0x172eb0d4399ae192a99572002e5d61a83335c325532ae4005cbac350266b864aa655c800b975869fccd70c954cab900172eb0d3e99ae192a99572002e5d61a7b335c325532ae4005cbac34d666b864aa655c800b975869a4cd70c954cab900172eb0d3299ae192a99572002e5d61a63335c325532ae4005cbac34c266b864aa655c800b9758697ccd70c954cab900172eb0d2e99ae192a99572002e5d61a4d335c325532ae4005cbac349666b864aa655c800b9758691ccd70c954cab900172eb0d2299ae192a99572002e5d61a43335c325532ae4005cbac348266b864aa655c800b975868fccd70c954cab9 else (if i < 37 then 0x172ecf56199ae192a99572002e5d9dac3335c325532ae4005cbb3958666b864aa655c800b97656b0ccd70c954cab900172ec4d6199ae192a99572002e5d7eac3335c325532ae4005cbae758666b864aa655c800b975bab0ccd70c954cab90018aae5d5a99ae192a99572000005cbab5335c325532ac4005cbac356a66b864aa655c800b97586ac4cd70c954cab900172eb0d5799ae192a99572002e5d61aad335c325532ae400000c4753a66b864aa6558800c4772ea74cd70c954cab900188eb0d4e99ae192a99572002e5d61a9b335c325532ae4005cbac353266b864aa655c800b97586a24cd70c954cab9 else 0x1762e5d6199ae192a99572000005cbac3335c325532ac40062fb8958666b864aa655c800b97712b0ccd70c954cab9000002e256199ae192a99562002e5dc2ac3335c325532ae4005cbb8358666b864aa655c800b976eeb0ccd70c954cab900172edcd6199ae192a99572002e5db7ac3335c325532ae4005cbb6d58666b864aa655c800b976d6b0ccd70c954cab900172ed7d6199ae192a99572002e5dadac3335c325532ae4005cbb5758666b864aa655c800b976aab0ccd70c954cab900172ed4d6199ae192a99572002e5da3ac3335c325532ae4005cbb4358666b864aa655c800b9767eb0ccd70c954cab9)) else (if i < 40 then (if i < 39 then 0x18d2e5d6199ae192a9957200314dcbac3335c325532ae400621b9758666b864aa655c800c3f72eb0ccd70c954cab9001876e5d6199ae192a995720030e5cbac3335c325532ae400616b9758666b864aa655c800c2972eb0ccd70c954cab900184ae5d6199ae192a99572003065cbac3335c325532ae40060ab9758666b864aa655c800c1172eb0ccd70c954cab900180ae5d6199ae192a99572003005cbac3335c325532ae4005feb9758666b864aa655c800bfb72eb0ccd70c954cab90017e2e5d6199ae192a99572002f7dcbac3335c325532ae4005e6b9758666b864aa655c800bbb72eb0ccd70c954cab9 else 0x172ede56199b0b92a99572000005cbac333614a5532ac400000b9758666c214aa6558800c5f8aae5d6170c954cab900000314dcbac2e192a9956200314dcbac3539c325532ae40062fc4772e66b864aa655c800001886e5ccd70c954cab10018ab11d6199ae192a995720000061fac3335c325532ac400628b9758666b864aa655c800c7b72eb0ccd70c954cab90018f2e5d6199ae192a995720031ddcbac3335c325532ae40063ab9758666b864aa655c800c7372eb0ccd70c954cab90018e2e5d6199ae192a995720031bdcbac3335c325532ae400636b9758666b864aa655c800c6b72eb0ccd70c954cab9) else (if i < 41 then 0x172eb0ccd7c4f5dc319572002e5d6199af89e638632ae4005cbac33364c3866ce655c800b9758666be270cd9ccab900172eb0ccd91ce19a999572002e5d6199af89c335332ae4005cbac3335f1386650655c800b9758666be270cc40cab9001836e5d6199ae197e19572002e5db0ac3335c32fc32ae4005cbac3335f13865f8655c80000172eb0ccd70cbdccab1000002e5d6199ae197799562000005cbac3335f12b132ac4005cbac3335f1386562655c800c2f72eb0ccd940954cab900172ede56199b2812a99572000005cbac33364da5532ac400000b9758666c934aa6558800c2f72eb0ccd85c954cab9 else 0x1836e5d6199af89c31957200301dcbac3335f138632ae4005efb9758666be270c655c800b976f2b0ccd7c4e18cab900172ed856199af89c319572002e5da4ac3335f138632ae4005cbb1358666be270c655c800b97586a74cd7c4e18cab900172eb0d4599af89c319572002e5d61a6d335f138632ae4005cbac349e66be270c655c800b975867d4cd7c4e18cab900172eb0ccd97af89c319572002e5d6199b2bdf138632ae4005cbac3336503e270c655c800b9758666c557c4e18cab900172eb0ccd85cf89c319572002e5d6199b05df138632ae4005cbac333602be270c655c800b9758666be27b6e18cab9)))) else (if i < 49 then (if i < 45 then (if i < 43 then 0x2e5d6199ae197a25562000005cbac3335c32ea4aac400000b9758666c555629558800b9758666c5570cac52ab900172eb0ccd8aae192aa3672002e5d6199ae197a25546ce4005cbac33362ab864aa889c800b9758666b865d4955113900172eb0ccd8aae192aa0572002e5d6199ae192a995178e4005cbac33362ab864aa77dc800b9758666b864aa6545139001836e5d6199b281c319572002e5db0ac33365038632ae400000b9758666c9870c655880000172eb0ccd91ce18cab10018bee5d6199af89c319572003155cbac3335f138632ae400623b9758666be270c655c800c2f72eb0ccd7c4e18cab9 else (if i < 44 then 0x172eb0ccd913155c325572002e5d6199b1e22ab864aae4005cbac33362ac4e70c955c800b9758666c55894e192ab900172eb0ccd8ab0f9c32557200301dcbac3336173864aae4005cbb4958666c2e70c955c800b9758666c5585ce192ab9000002e5d6199b099c325562000005cbac33360e3864aac4005cbac33362abe270c955c800b9758666c5570cd9d2ab900172eb0ccd84ce19b3a5572002e5d6199b155c33534aae4005cbac33360e3866a6955c800b9758666c5570ccd92ab900172eb0ccd8aae19882557200301dcbac3335c32fc4aae4005cbb4958666b865f8955c800b9758666c5570cbf12ab9 else 0x172eb0ccd70c954ca8597200317dcbac33362ab864aae40062ab9758666c5570c955c800c4772eb0ccd8aae192ab900185ee5d6199b155c32557200306dcbac33362ab864aae400603b9758666c5570c955c800bf172eb0ccd8aae192ab900172ede56199b155c325572002e5db0ac33362ab864aae4005cbb4958666c5570c955c800b97656b0ccd8aae192ab900172eb0d4e99b155c325572002e5d61a8b3362ab864aae4005cbac34da66c5570c955c800b9758693ccd8aae192ab900172eb0d0d99b155c325572002e5d6199b2f62ab864aae4005cbac333657c5570c955c800b9758666ca08aae192ab9)) else (if i < 47 then (if i < 46 then 0x172eb0ccd7c4e18ca8c972002e5d6199ae197e195192e4005cbac333558a5532a325c800b9758666b864aa654643900172eb0ccd70c954ca8c772002e5d6199ae192a99518ae4005cbac3335c325532a0f1c800ac3335c325532a1441e3900172e66b864aa6544988072002e5d6199ae192a995100e4005cbac3335c325532a1f5c800b9758666b864aa65457b9000002e5d6199b155f138662002e5d6199ae192a995066e4005cb99ae192a9951261e9c800b9758666b864aa6543d3900172eb0ccd70c954ca87772002e5d6199ae192a995046e4005cbac3335c325532a1d5c800b9758666b864aa65436b9 else 0x172e66b86562954ca89372002e5ccd70c9f12a995126e4005cb99ae192aa3632a24dc800b97335c325544465449b900172e66b864aa77cca89372002e5ccd70c954de195126e4005cb99ae192a9952ec24dc800b97335c325532a58849b900172e66b864aa6544988b72002e5d6199ae192a995116e4005cb99ae192a995126229c800b9758666b864aa654453900172e66b864aa6544988572002e5d6199ae192a99510ae4005cbac2e192a995212325c80000172eb0ccd70cbf064b100172eb0ccd8aae192a8c972002e5d6199b0b9c3255192e4005cbac3335c32fc4aa325c800b9758666ca070c65464b9) else (if i < 48 then 0x172ed24cd70c954ca89372002e5d6199ae192a995126e4005cba9d335c325532a24dc800b9751666b864aa65449b900172e9b4cd70c954ca89372002e5d2799ae192a995126e4005cb9b5335c325532a24dc800b973365eb864aa65449b900172e66caf70c954ca89372002e5ccd940e192a995126e4005cb99b155c325532a24dc800b97336173864aa65449b900172e66be270c954ca89372002e5ccd75ae192a995126e4005cb99ae19b3a5532a24dc800b97335c33534aa65449b900172e66b86620954ca89372002e5ccd70cbf12a995126e400000b9733558a5532a24d8800b9758666ab14aa65449b9 else 0x172e66b864aa6549009372000005cb70c954ca909126c4005cbac2e192a99521224dc800b97335c325532a42449b900172e66b864aa6547289372002e5ccd70c954ca8d3126e4005cb99ae192a99519224dc80000172e66c5570c95449b100172eb0ccd8aae192a89372000005cb99af89c3195126c4005cbac3335f138632a24dc800c5f72e66b864aa65449b90018aae5ccd70c954ca8937200311dcb99ae192a995126e400617b97335c325532a24dc800c1b72e66b864aa65449b900180ee5ccd70c954ca89372002eedcb99ae192a995126e4005cbb79335c325532a24dc800b976c266b864aa65449b9))) else (if i < 53 then (if i < 51 then (if i < 50 then 0x172eb0ccd85c954ca8e572002e5d6199aac52a9951cae4005cbac3335c325532a391c800b9758666b864aa65471b900172eb0ccd70c954ca86372002e5d6170c954ca9091bae4005cbac3335c325532a375c800b9758666b864aa6546d3900172eb0b864aa654848d372000005cbac3336172551a6c4005cbac33362ab864aa34dc800b9758666c2e70c95469b900172eb0ccd70cbf12a8d372002e5d6199af89c31951a6e4005cbac33365025532a34dc800b9758666c2e4aa65469b900172eb0ccd562954ca8d372002e5d6199ae192a9951a4e4005cbac3335c325532a345c800b9758666b864aa6544d39 else 0x172eb0b864aa758ca90972002e5d6170c954ca976212e4005cbac2e192a9952c4425c800b97585c325532a42480b900172eb0ccd70c954ca90172002e5d6170c954ca909200e4005cbac3335c325532a401c800b97585c325532a4247c3900172eb0ccd70c954ca8f872002e5d6199ae192a9951e8e4005cbac2e192a9952123bdc800b9758666b864aa65477b900172eb0ccd70c954ca8ec72002e5d6170c954ca9091cae4005cbac33362ab864aa395c80000172eb0ccd94065472b100172eb0ccd940e18ca8e572002e5d6199af89c31951cae4005cbac3335c32fc32a395c800b9758666ca04aa65472b9) else (if i < 52 then 0x172eb0d2770c954ca90972002e5d6199ae192a995212e4005cbac32f5c325532a425c800b9758657b864aa65484b900172eb0ca070c954ca90972002e5d618aae192a995212e4005cbac30b9c325532a425c800b97585f13864aa65484b900172eb0bc670c954ca90972002e5d6170cd9d2a995212e4005cbac2e19a9a5532a425c800b97585c33104aa65484b900172eb0b865f8954ca90972000005cbac2ac52a995212c4005cbac333558a5532a425c800b97585c32b14aa65484b900172eb0b8652a954ca90972002e5d6170c9551b195212e4005cbac2e192aa2232a425c800b97585c32553be65484b9 else 0x172eb0ccd70c954ca91072002e5d6170c954ca920212e400000b975862ab864aa4258800b9758666c5570c95484b9000002e5d617c4e18ca90962002e5d6199af89c3195212e40062fb97585c325532a425c800c5572eb0b864aa65484b900188ee5d6170c954ca909720030bdcbac2e192a995212e40060db97585c325532a425c800c0772eb0b864aa65484b9001762e5d6170c954ca90972002e5dbcac2e192a995212e4005cbb61585c325532a425c800b97692b0b864aa65484b900172eb756170c954ca90972002e5d61a9ce192a995212e4005cbac3515c325532a425c800b975869b3864aa65484b9)) else (if i < 55 then (if i < 54 then 0x172eb0ccd7c4e18ca94572002e5d6199ae192a99528ae4005cbac3335c325532a101c800ac3335c325532a144203900172eb0ccd70c954ca93772002e5d6199aac52a99526ee4005cbac3335c325532a4adc80000172eb0d2770c954903100172eb0d2799ae192a92072002e5d6199b155c3255240e4005cbac3336173864aa481c800b9758666b865f8954903900172eb0ccd7c4e18ca92072002e5d61a4ee192a995240e4005cbac333558a5532a481c800b9758666b864aa5d8903900172eb0ccd70c954b112072002e5d6199ae192a99523ee4005cbac3335c325532a46dc800b9758666b864aa6548cb9 else 0x317dcb95ee192a99564000005cbac3335bda5532ac800000b9758666b774aa655900000185eb0ccd6ce954cab2000002e5dbc99ad4d2a99564000005cbac35158825532ac800000b9758666b86494655900000172eb0ccd70c918cab200000306d6199ae191b19564000005cbb61335c322232ac800000b975869b3863be655900000172eb0ccd70c954c532000002e5d6199ae192a9866400000603ac3335c32552ecc800000b9769266b864aa5899000001585c325532a42428b200000266b864aa65449851640000056199b155c32550a2c800000ac3335f138632a145900000158666ab14aa65428b2) else (if i < 56 then 0x2e5d6199ae197a25564000005cbac3335c32ea4aac800000b9758666c55562955900000172eb0ccd930e18cab2000002e5d6199b239c319564000005cbac3335c32f732ac800000b9758666b865de655900000172eb0ccd7c4ac4cab2000002e5d6199b26d2a99564000005cbac333649a5532ac800000b9758666c294aa655900000172eb0ccd842954cab200000314dcbac2e192a9956400000621b97335c325532ac800000c3f58666b864aa655900000172eb0ccd70c954cab2000002e256199ae192a99564000005cbab5335c325532ac800000c4753a66b864aa65590000018aab0cbd70c954cab2 else 0xb9758693b864aa481900000172eb0c5570c95484b2000002e5d617c4e18ca90964000005cbac2ac52a995212c800000b9758666ca032a395900000172eb0ccd85c95469b2000002e5b864aa6548489364000005cb99b155c3255126c800000b97335f138632a24d900000172e66ab14aa65449b2000002e5d6199ae197e0c964000005cbac33362abe270cc800000b9758666c2670c955900000172eb0ccd838e192ab2))))))
private def st7 (i : Nat) : Nat := unpack st7Packed 95 20 i
private def adj7Packed (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0x4ac001a02118024280c101006004e720022191f212ba9214074840302463020c20948730023500290800200025000c500000 else 0x380a05106010c2200df188022084003004102005004680240000021080220004018c0508ac04806500140004214a4a0294a5) else (if i < 3 then 0x2982701402000410900220146130873808709001000c1088041a8812846080000080610080a1006660060388001002149c21 else (if i < 4 then 0x1480008a03042108c023102910c050000300841010000a02400e4801c2008d870000108420198460106602481125830a020 else 0x180320081004201080108a0000c40394e11800008463280411818000045008041888510000)))
private def adj7 (i : Nat) : Nat := unpack adj7Packed 5 80 i
private def loc7Packed (i : Nat) : Nat := (if i < 11 then (if i < 5 then (if i < 2 then (if i < 1 then 0x2c6d88000dc5228605e0000000021817b0003f40008900000126b5814c0000000073ad654f800238fd5610f9000aed4818e0005c17f0000009e80000000089e1b8005aacdca700045a864490000ea001c82205de0000015f0000000035c0000000010b762ac1fcb9c2410e000000 else 0x7da3d0002bd04e0006a800000001382fa0002e40029d86cc85a24436e200000000000150042b2106014100008640000020f4d650c4f00065874c00000000456318405c250800320000001992e7000b4400000536a8cee09a3e2544430005d02b56810e140001b682200001854000) else (if i < 3 then 0x62c060f68b743c0017e0da55e1a0f98006f8001b18040000000040f0002f5b3a52000f9c003f21be00128096000a14c0a354c20080020d2ca000002d200105dff00083c000a91ce77c9fc00000368645e4ae40691acc9b233e41053c15524aab0ec051001044003a009ab2c350e8 else (if i < 4 then 0x24c405c5800000000048000200008c0008a71622498874a00186176884000003a46d4186228a300021c00000000000001d90fc2fd362112b30ea2600045c000004156b4001dd800000f51dd00036d015042f533e7b8a7b070001fde912900000000000000f3528869274a69d10a5 else 0x332002333dc4aa6c0b880067a4cc87b8e00022000447370e7cbd0000000000000000007c9a0ea0ba4fc0012f1eed40000008ce8f4cdbc0000000e9183000e18000004040b5e300000036d4b81d000dda0000000086c0012e000df97b000000d35f8ae90e8994000d9000d09de1db))) else (if i < 8 then (if i < 6 then 0xc60014cb1972c0011100075200000000000001c38004b6e69d7800000c68612797b400cfe0000000001e34b2e4fbd2580019e4c80006b518c44f50006990897b800692db817969000778001c63c282dc4a722bc7122ca10464e980027d000db195800000094899fa896c40161df else (if i < 7 then 0x19e36378000c24000005e9151470001900015300068a334b32260004f40043f0169b94182318eb60000307020000000000095c0026422c45d71ac82ce0a4004291a005c00239812000003ee000aa96705a8480013498d0e6fd8c58003a2dfcc90005e2358001ef4060018a212 else 0x3290edd90004828da3226d04834c1b00086a811a18f62060011db3e51281c003cf68e0001dab32600021745a280001b00c6000000000000010f0be98f3d00015a8004c63949b0000f20000b25f44a001da0008d0f317e8c4654000001f8000000002c97d800082000000dbc95282)) else (if i < 9 then 0x5feef475c44084c2c5d80064a1b08d800000000801a4000000000cc000d505c28f4b0d95a7c200c49dc001e61922500000061a7fc4abd820ae103331733c000001957728e8001410007e5cf24800000000439000824688000000017510245238a1300071ea18000007189292c800 else (if i < 10 then 0xb35712f3000b59e1423000f5c22a2b54a000f2c4d0001c1b59ae066b1d43800098ecc738001210a8000000005b10a90d580000000ae868476250006e81e0003120006f8001f71b038d5580076a002292eb0007f800000000cf15700083411c602db00000000441751041793db else 0x241ed3f175002d20004082c800000044330000000005525d19738d000d54c13180000000007782400017440000001ee84a0000001d305000699f2114000000000000000000da98290001e5a340005ddb329e0220000010a262000000a75f2668098005b8054001864f800207000)))) else (if i < 16 then (if i < 13 then (if i < 12 then 0x4c938c03a1000788c48000b843055a23000a48fd8000aecd40014d0a6ccc000008089a000000132b7a19a0a288124d50000560014021a000e14000002dadc9e21495a8b6a230e4856a1000205710a71538ff0f400000197126f8000000000fa4000001c20020080060c3b01b800 else 0x48000079000232d90c3800000e5d8abbf54200000000000000748653fafdcf4bea0009d96fadd272b640018c000989ea80000012de88000001c5fd8000000019f8001f80000044e0003c0191c50009150341c3c65f80028a0002d000460001084003c80acd85440004868a8ab1d7) else (if i < 14 then 0x11d1a44e00d7fa0001cbb77bc17c000f526ece0ddb1d396700d0aca000e8c6511a5dc0014b154000000002b900000000000000000b412846f0f40000072af4c0000020cafc000006ea1c95a399000000000003641789681c054001d5800626441178b335ae48b9800606001b809b else (if i < 15 then 0x502ca40031c3409d49241f13a8c0003571dce50001c20fa0e0001ab4e2d292600012e0000037d24e000001b70009760d80000067000353001018003ca6142e80035e0000000025339a0015f3b800101e0c18a7ff0c5662a8000c9c5b30038ea4da903e000000ce80056c5699100c else 0x230000004789187d000256705f2a00000b0c000000001b876b248d40005f26f69ca80002c5000a88001a837e2c0f825a1cc30d7000058c0a20cc1434616d7300000035c000006f4cb5d68000000017d800450000001d60000015b8001420009db8300054dd380009e8b1f833b))) else (if i < 19 then (if i < 17 then 0x782a800426f040021f0001f17696e116001bdc655e0f65c89610001d96bbb60000014596a6b6208b59af102000000004e63800000e4ce000000006a2085c98d434ac7c004161f0b94e4beb0000022e37737ada10b356000000b13808be000ae242000610001238c4028003df else (if i < 18 then 0x8050a1071cc22256c00238548c080795d0da0008f0008ac8c40008a0000006ea1d0000fc001f60001bcfa8005745e0003ae000000002d3000001d504e28d14400256000000001dd7e8000671901e200058b7900000130000000000d3aad00000000000000978842246800014ac1d else 0x1907f23e428001d81790002151981a158d7c0040c3d60022f16066c00133000000b04e4000000051b4a5c8a00000045566201c6927b000804b78003864840000026a0016200014885c000007f0fa00000061044851346122f58ac2ec3c8001248a939400227a440c00002345b)) else (if i < 20 then 0x32f41fe0317370945a8000000009c42728f04df18008ba0009100018a0000000081500d239ac000f155c00006b0b0a5000000000401bc296ca10e46d39e000c28003ce000a288d0002c9f11b3154c6c0005261e002069f466800000000374000d12b10010f85791f278c3910bc7 else (if i < 21 then 0x682c042c00079c0022403d000a34cb0000009a8001a93c0a500024f090000bf8c163c1640033a7580013a000704af2058007cc27c000f32f8000000de0006d52a157000fcd978847f441c002f800053000000000754ed00025810c9f000000141aeb267c23bc7da3f85e741cc20c else 0x8f1310b4ea1ec6e6000002cf000000a80cb67200084b040006c4dc800000cc000457714f0e30800)))))
private def loc7 (i : Nat) : Nat := unpack loc7Packed 11 80 i
private def st8Packed (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0xb9758666b866ce954cab9b9758666b866a6954cab9b9758666b86620954cab9b9758666b865f8954cab900172eb0ccd562954cab1b9758666b86562954cab9b9758666b864aa8d8cab9b9758666b864aa888cab9b9758666b864aa77ccab9b9758666b864aa654bb39b9758666b864aa654b139b9758666b864aa65428b900158666b864aa65428b1b9758666b864aa65484b8b9758666b864aa65449b800172eb0ccd70c954cab0b9758666c5570c954cab8b9758666be270c954cab8b9758666b86562954cab8b9758666b864aa65428b8 else 0x172eb0ccd7c4e18cab1c5f72eb0ccd70c954cab9c5572eb0ccd70c954cab9c4772eb0ccd70c954cab9c2f72eb0ccd70c954cab9c1b72eb0ccd70c954cab9c0772eb0ccd70c954cab9b976f2b0ccd70c954cab9b976c2b0ccd70c954cab9b97692b0ccd70c954cab9b97586a74cd70c954cab9b97586a2ccd70c954cab9b975869b4cd70c954cab9b9758693ccd70c954cab9b9758666cbd70c954cab9b9758666caf70c954cab9b9758666ca070c954cab9b9758666c5570c954cab9b9758666c2e70c954cab9b9758666be270c954cab9) else (if i < 3 then 0xb9758666b86620954cabab9758666b865f8954caba00172eb0ccd562954cab2b9758666b86562954cabab9758666b864aa8d8cabab9758666b864aa888cabab9758666b864aa77ccabab9758666b864aa654bb3ab9758666b864aa654b13ab9758666b864aa65428ba00158666b864aa65428b2b9758666b864aa654903900172eb0b864aa65484b1b9758666b864aa65484b9b9758666b864aa65472b9b9758666b864aa65469b900172e66b864aa65449b1b9758666b864aa65449b9b9758666b864aa65464b900172eb0ccd8aae192ab1 else (if i < 4 then 0xc5572eb0ccd70c954cabac4772eb0ccd70c954cabac2f72eb0ccd70c954cabac1b72eb0ccd70c954cabac0772eb0ccd70c954cabab976f2b0ccd70c954cabab976c2b0ccd70c954cabab97692b0ccd70c954cabab97586a74cd70c954cabab97586a2ccd70c954cabab975869b4cd70c954cabab9758693ccd70c954cabab9758666cbd70c954cabab9758666caf70c954cabab9758666ca070c954cabab9758666c5570c954cabab9758666c2e70c954cabab9758666be270c954cabab9758666b866ce954cabab9758666b866a6954caba else 0x172eb0b864aa65484b300172e66b864aa65449b300172eb0ccd8aae192ab300172eb0ccd7c4e18cab300172eb0ccd562954cab300158666b864aa65428b3b9758666b864aa654903a00172eb0b864aa65484b2b9758666b864aa65484bab9758666b864aa65472bab9758666b864aa65469ba00172e66b864aa65449b2b9758666b864aa65449bab9758666b864aa65464ba00172eb0ccd8aae192ab200172eb0ccd7c4e18cab2c5f72eb0ccd70c954caba)))
private def st8 (i : Nat) : Nat := unpack st8Packed 84 20 i
private def adj8Packed (_i : Nat) : Nat := 0x39d000000220130143116b321101004022891
private def adj8 (i : Nat) : Nat := unpack adj8Packed 4 80 i
private def loc8Packed (i : Nat) : Nat := (if i < 1 then 0x553191442c00000004f016a2bb743004e001efb700020935e02b0084a81290000021a89c04300000557cfd180580180e8f2405e3a000171a00038b80001b48002adb2012d0 else 0x1006805700440060135ab6a4240002401e98002e4600680053290000000025cc10ce25d00e5e1f516d91e94d18aea200e008c0159644000000010780)
private def loc8 (i : Nat) : Nat := unpack loc8Packed 7 80 i
private def st9Packed (_i : Nat) : Nat := 0xb9758666b864aa655a5cbac3335c325532acee5d6199ae192a9956572eb0ccd70c954cab1
private def st9 (i : Nat) : Nat := unpack st9Packed 73 20 i
private def adj9Packed (_i : Nat) : Nat := 0x0
private def adj9 (i : Nat) : Nat := unpack adj9Packed 1 80 i
private def loc9Packed (_i : Nat) : Nat := 0xc0002000040
private def loc9 (i : Nat) : Nat := unpack loc9Packed 2 80 i
private def certCount : Nat → Nat
  | 3 => 9
  | 4 => 59
  | 5 => 976
  | 6 => 2531
  | 7 => 1134
  | 8 => 97
  | 9 => 4
  | _ => 0
private def certSizes : Nat → Nat × Nat
  | 3 => (5,67)
  | 4 => (23,89)
  | 5 => (331,1471)
  | 6 => (853,3797)
  | 7 => (379,1709)
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
private lemma cert3_0 : checkCert 3 0 9 = true := by decide +kernel

private lemma certLayer3 : checkCert 3 0 (certCount 3) = true :=
  cert3_0

set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert4_0 : checkCert 4 0 59 = true := by decide +kernel

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
private lemma cert5_576 : checkCert 5 576 96 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_672 : checkCert 5 672 96 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_768 : checkCert 5 768 96 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_864 : checkCert 5 864 96 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert5_960 : checkCert 5 960 16 = true := by decide +kernel

private lemma certLayer5 : checkCert 5 0 (certCount 5) = true :=
  (joinCert 5 0 480 496 (joinCert 5 0 192 288 (joinCert 5 0 96 96 cert5_0 cert5_96) (joinCert 5 192 96 192 cert5_192 (joinCert 5 288 96 96 cert5_288 cert5_384))) (joinCert 5 480 288 208 (joinCert 5 480 96 192 cert5_480 (joinCert 5 576 96 96 cert5_576 cert5_672)) (joinCert 5 768 96 112 cert5_768 (joinCert 5 864 96 16 cert5_864 cert5_960))))

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
private lemma cert6_1824 : checkCert 6 1824 96 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_1920 : checkCert 6 1920 96 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_2016 : checkCert 6 2016 96 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_2112 : checkCert 6 2112 96 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_2208 : checkCert 6 2208 96 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_2304 : checkCert 6 2304 96 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_2400 : checkCert 6 2400 96 = true := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
private lemma cert6_2496 : checkCert 6 2496 35 = true := by decide +kernel

private lemma certLayer6 : checkCert 6 0 (certCount 6) = true :=
  (joinCert 6 0 1248 1283 (joinCert 6 0 576 672 (joinCert 6 0 288 288 (joinCert 6 0 96 192 cert6_0 (joinCert 6 96 96 96 cert6_96 cert6_192)) (joinCert 6 288 96 192 cert6_288 (joinCert 6 384 96 96 cert6_384 cert6_480))) (joinCert 6 576 288 384 (joinCert 6 576 96 192 cert6_576 (joinCert 6 672 96 96 cert6_672 cert6_768)) (joinCert 6 864 192 192 (joinCert 6 864 96 96 cert6_864 cert6_960) (joinCert 6 1056 96 96 cert6_1056 cert6_1152)))) (joinCert 6 1248 672 611 (joinCert 6 1248 288 384 (joinCert 6 1248 96 192 cert6_1248 (joinCert 6 1344 96 96 cert6_1344 cert6_1440)) (joinCert 6 1536 192 192 (joinCert 6 1536 96 96 cert6_1536 cert6_1632) (joinCert 6 1728 96 96 cert6_1728 cert6_1824))) (joinCert 6 1920 288 323 (joinCert 6 1920 96 192 cert6_1920 (joinCert 6 2016 96 96 cert6_2016 cert6_2112)) (joinCert 6 2208 192 131 (joinCert 6 2208 96 96 cert6_2208 cert6_2304) (joinCert 6 2400 96 35 cert6_2400 cert6_2496)))))

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
private lemma cert7_1056 : checkCert 7 1056 78 = true := by decide +kernel

private lemma certLayer7 : checkCert 7 0 (certCount 7) = true :=
  (joinCert 7 0 576 558 (joinCert 7 0 288 288 (joinCert 7 0 96 192 cert7_0 (joinCert 7 96 96 96 cert7_96 cert7_192)) (joinCert 7 288 96 192 cert7_288 (joinCert 7 384 96 96 cert7_384 cert7_480))) (joinCert 7 576 288 270 (joinCert 7 576 96 192 cert7_576 (joinCert 7 672 96 96 cert7_672 cert7_768)) (joinCert 7 864 96 174 cert7_864 (joinCert 7 960 96 78 cert7_960 cert7_1056))))

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

def monotoneCircuit : Circuit :=
  ⟨[⟨.and, [0,1]⟩, ⟨.or, [1,2]⟩, ⟨.or, [0,7]⟩, ⟨.and, [4,5]⟩,
    ⟨.and, [2,6]⟩, ⟨.or, [3,9]⟩, ⟨.or, [4,10]⟩, ⟨.or, [5,12]⟩,
    ⟨.and, [8,11]⟩, ⟨.and, [13,14]⟩], 15⟩

lemma witness_mono : Monotone2 monotoneCircuit := by
  simp [monotoneCircuit, Monotone2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma witness_eval : ∀ x : Fin 6 → Bool, monotoneCircuit.eval (List.ofFn x) = graph x := by
  decide +kernel

end PEqualNP.Outside.L_meta_12349

open PEqualNP.Outside.L_meta_12349 in
theorem PEqualNP.Outside.L_meta_12349 :
∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124032 * 2 ^ 32 + 4261445632) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124032 * 2 ^ 32 + 4261445632) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
