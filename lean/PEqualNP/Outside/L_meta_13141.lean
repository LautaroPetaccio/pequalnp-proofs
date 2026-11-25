import PEqualNP.Defs

-- Circuit signature extraction follows L_meta_8453.
-- The finite search uses the live wire method of L_meta_6159.
namespace PEqualNP.Outside.L_meta_13141.Signed
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 168
def zero : Sig := 0
def one : Sig := BitVec.allOnes 168
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def allowed (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)
def flipOp (d : Nat) := if d=2 then 3 else if d=3 then 2 else d
theorem allowed_four {u d} (h : allowed u d) : d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3) := by
  rcases h with h | ⟨h,j⟩
  · omega
  · have : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
theorem bin_flip {u d} (h : allowed u d) (a b : Sig) : bin d a b = bin (flipOp d) b a := by
  rcases allowed_four h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [bin,flipOp,BitVec.and_comm,BitVec.or_comm]
theorem flip_flip {u d} (h : allowed u d) : allowed u (flipOp d) ∧ flipOp (flipOp d)=d := by
  rcases allowed_four h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  all_goals simp_all [flipOp,allowed]

def Live (u : Bool) (target : Sig) : Nat → Finset Sig → Prop
  | 0,S => S={target} ∧ proper target
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), allowed u d ∧ S=insert a (insert b U) ∧
      proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live u target k (insert (bin d a b) U)
theorem Live.stop {u} {target : Sig} (hp : proper target) : Live u target 0 {target} := ⟨rfl,hp⟩
theorem Live.binary {u} {target : Sig} {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)) :
    Live u target (k+1) (insert a (insert b U)) :=
  ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩
theorem Live.ind {u} {target : Sig} {motive : ∀ (k : Nat) (S : Finset Sig), Live u target k S → Prop}
    (stop : ∀ (hp : proper target), motive 0 {target} (Live.stop hp))
    (binary : ∀ {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)),
      motive k (insert (bin d a b) U) tail →
      motive (k+1) (insert a (insert b U)) (Live.binary hd ha hb hab hfresh tail))
    {k : Nat} {S : Finset Sig} (h : Live u target k S) : motive k S h := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,hf,tail⟩ := h
    exact binary hd ha hb hab hf tail (ih tail)

private lemma live_proper {u target k S} (h : Live u target k S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

def bit (i : Fin 168) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
theorem bit_ext {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩

def nrm (u : Bool) (a : Sig) : Sig := if u && bit 0 a then neg a else a
theorem nrm_false (a : Sig) : nrm false a = a := rfl
theorem nrm_bit (a : Sig) : bit 0 (nrm true a) = false := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg]
theorem nrm_id {u} {a : Sig} (h : bit 0 a = false) : nrm u a = a := by simp [nrm,h]
theorem neg_neg' (a : Sig) : neg (neg a) = a := by simp [neg]
theorem nrm_neg (a : Sig) : nrm true (neg a) = nrm true a := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg,neg_neg']
theorem proper_neg {a : Sig} (h : proper (neg a)) : proper a := by
  refine ⟨?_,?_⟩
  · rintro rfl
    exact h.2 (by simp [neg,zero,one])
  · rintro rfl
    exact h.1 (by simp [neg,zero,one])
theorem proper_nrm {u} {a : Sig} (h : proper (nrm u a)) : proper a := by
  unfold nrm at h
  split at h
  · exact proper_neg h
  · exact h
def prime (d : Bool) (a b : Sig) := if d then a ||| b else a &&& b
theorem bit_prime (i) (d : Bool) (a b : Sig) : bit i (prime d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [prime,bit]
theorem nrm_prime (d : Bool) (a b : Sig) :
    ∃ e, e<4 ∧ nrm true (prime d a b) = bin e (nrm true a) (nrm true b) := by
  refine ⟨if d then (if bit 0 a then (if bit 0 b then 0 else 2) else (if bit 0 b then 3 else 1))
    else (if bit 0 a then (if bit 0 b then 1 else 3) else (if bit 0 b then 2 else 0)),?_,?_⟩
  · split_ifs <;> omega
  · apply bit_ext
    intro i
    cases d <;> cases ha : bit 0 a <;> cases hb : bit 0 b <;>
      simp only [nrm,bit_prime,ha,hb,bit_bin,bit_neg,Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.false_or,
        Bool.or_false,Bool.true_or,Bool.or_true,Bool.false_eq_true,ite_true,ite_false] <;>
      cases hx : bit i a <;> cases hy : bit i b <;> simp [hx,hy,bit_neg,bit_prime]

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (prime false) one
  | .or => xs.foldr (prime true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v
def Repr (u : Bool) (w : List Sig) (v : Sig) : Prop := represented w (nrm u v)

private lemma bin_laws (a : Sig) :
    bin 0 a one = a ∧ bin 1 a zero = a ∧
    bin 0 a zero = zero ∧ bin 1 a one = one ∧
    bin 0 a a = a ∧ bin 1 a a = a ∧ bin 2 a a = zero ∧ bin 3 a a = zero ∧ bin 2 a zero = a ∧
    bin 3 zero a = a ∧ bin 2 zero a = zero ∧ bin 3 a zero = zero ∧ bin 0 zero a = zero ∧ bin 1 zero a = a ∧
    bin 0 one a = a ∧ bin 1 one a = one := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply bit_ext <;> intro i <;>
    simp [bit_bin,bit_zero,bit_one]

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (u : Bool) (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, allowed u d ∧ a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b

private lemma bin_rep {u w a b} (d : Nat) (hd : allowed u d) (ha : represented w a) (hb : represented w b)
    (no : u=true → a ≠ one ∧ b ≠ one) :
    represented w (bin d a b) ∨ witness u w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := bin_laws a
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := bin_laws b
  by_cases he : a=b
  · subst b
    left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact b15.symm ▸ hb
    · exact b16.symm ▸ ro
    · exact absurd rfl (no hu).1
    · exact absurd rfl (no hu).1
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact a1.symm ▸ ha
    · exact a4.symm ▸ ro
    · exact absurd rfl (no hu).2
    · exact absurd rfl (no hu).2
  exact Or.inr ⟨d,a,b,hd,ham,hbm,hap,hbp,he,rfl⟩

theorem norm_ne_one (a : Sig) : nrm true a ≠ one := by
  intro h
  have := nrm_bit a
  rw [h,bit_one] at this
  exact Bool.noConfusion this
theorem prime_rep {u w a b} (d : Bool) (ha : Repr u w a) (hb : Repr u w b) :
    Repr u w (prime d a b) ∨ witness u w (nrm u (prime d a b)) := by
  cases u
  · have e : prime d a b = bin (if d then 1 else 0) a b := by cases d <;> rfl
    have h := bin_rep (u:=false) (if d then 1 else 0) (Or.inl (by split <;> omega)) ha hb (by simp)
    unfold Repr
    simp only [nrm_false] at h ⊢
    rwa [e]
  · obtain ⟨e,he,eq⟩ := nrm_prime d a b
    unfold Repr
    rw [eq]
    exact bin_rep e (Or.inr ⟨rfl,he⟩) ha hb (fun _ => ⟨norm_ne_one a,norm_ne_one b⟩)
theorem repr_const {u w} {v : Sig} (h : v=zero ∨ v=one) : Repr u w v := by
  refine Or.inr fun hp => ?_
  have := proper_nrm hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl
private lemma get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact repr_const (Or.inl rfl)
  | some a => exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))
theorem repr_neg {w a} (h : Repr true w a) : Repr true w (neg a) := by
  unfold Repr
  rwa [nrm_neg]

def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false
private lemma gate_rep (u : Bool) (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → isNot g=false) :
    Repr u (w.map (nrm u)) (gv w g) ∨ (isNot g=false ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have prim (d : Bool) : Repr u (w.map (nrm u)) ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one)) ∨
      witness u (w.map (nrm u)) (nrm u ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one))) := by
    have unit (v : Sig) : prime d v (if d then zero else one) = v := by
      apply bit_ext
      intro i
      cases d <;> simp [bit_prime,bit_zero,bit_one]
    cases l with
    | nil => exact Or.inl (repr_const (by cases d <;> simp))
    | cons i l =>
      cases l with
      | nil =>
        simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
        exact Or.inl (get_rep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (get_rep w i) (get_rep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (get_rep w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
private lemma pull_gate {u target} {w : List Sig} {z : Sig} {k S c} (h : Live u target k S)
    (hz : represented w z ∨ (c=1 ∧ witness u w z)) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+c ∧ Live u target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨rfl,d,a,b,hd,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live u target k (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
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
        exact ⟨_,_,Nat.le_refl _,Live.binary hd pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract {u target} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → ∀ g ∈ gs, isNot g=false)
    (hp : proper target) (hout : target ∈ (execute gs w).map (nrm u)) :
    ∃ k S, k ≤ gs.countP (fun g => !isNot g) ∧ Live u target k S ∧ ∀ a ∈ S, a ∈ w.map (nrm u) := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha]))
      (fun hu a ha => mono hu a (by simp [ha])) hout
    have rep := gate_rep u w g (legal g (by simp)) (fun hu => mono hu g (by simp))
    rw [List.map_append] at hs
    have rep' : represented (w.map (nrm u)) (nrm u (gv w g)) ∨
        ((if isNot g then 0 else 1)=1 ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) :=
      rep.imp id (fun h => ⟨by simp [h.1],h.2⟩)
    obtain ⟨l,T,hl,hu,hT⟩ := pull_gate ht rep' hs
    refine ⟨l,T,?_,hu,hT⟩
    rw [List.countP_cons]
    cases hn : isNot g <;> simp [hn] at hl ⊢ <;> omega

private lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (prime false _ _) = (_ && _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (prime true _ _) = (_ || _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _

private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]

def plainWord (a : Sig) : Bool := !(bit 0 a)
theorem nrm_map {u} {w : List Sig} (h : w.all plainWord=true) : w.map (nrm u)=w := by
  have e : w.map (nrm u) = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact nrm_id (by simpa [plainWord] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]
abbrev Row := Fin 168

theorem live_row_difference {u T k S} (h : Live u T k S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {u T k S} (h : Live u T k S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

def keepChoices (a b : Sig) (r : List Sig) : List (List Sig) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List Sig} {a b : Sig} {needed : Finset Sig}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {target : Sig} {ws : List Sig} (hn : ws.Nodup) (hs : ws.toFinset = {target}) : ws = [target] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def positiveRows : List ℕ := [63, 5, 5, 5, 5, 5, 9, 9, 9, 9, 9, 12, 12, 12, 12, 12, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 38, 38, 38, 38, 38, 42, 42, 42, 42, 42, 5, 5, 7, 7, 9, 9, 11, 11, 12, 12, 14, 14, 17, 17, 18, 18, 19, 21, 22, 22, 25, 26, 26, 28, 28, 37, 37, 38, 38, 39, 41, 41, 42, 42, 43, 44, 44, 49, 49, 50, 50, 51, 53, 54, 57, 58, 60, 60]

def negativeRows : List ℕ := [0, 6, 10, 35, 52, 56, 6, 10, 35, 52, 56, 6, 10, 35, 52, 56, 6, 10, 35, 52, 56, 6, 10, 35, 52, 56, 6, 10, 35, 52, 56, 6, 10, 35, 52, 56, 4, 1, 6, 3, 8, 1, 10, 3, 8, 4, 10, 6, 16, 1, 16, 2, 3, 20, 20, 6, 24, 24, 10, 24, 20, 36, 33, 36, 34, 35, 40, 33, 40, 34, 35, 40, 36, 48, 33, 48, 34, 35, 52, 52, 56, 56, 56, 52]

def inputs : List Sig := [32729065941563849690138583519321275105495629439240, 63616542565950422645735287377014834733520119085518, 298284767116020291366627011932025393331056987949650, 350941696629508717340550912762395566462989084300452, 373961776048090664682685726691400558540641462175280, 374144374555222077928818643071721826234818363189048]

def goal : Sig := (-1 : BitVec 84) ++ (0 : BitVec 84)

def rowInput (r : Fin 168) (i : Fin 6) : Bool :=
  let row := if r.val < 84 then negativeRows.getD r.val 0 else positiveRows.getD (r.val - 84) 0
  row.testBit i.val

def graph (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4277075680 * 2 ^ 32 + 4277074592) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def splitIndex (i : Fin 84) : Fin 168 := ⟨84 + i.val, by omega⟩
def smallIndex (i : Fin 84) : Fin 168 := ⟨i.val, by omega⟩

def separates (u : Bool) (i : Fin 84) (w : Sig) : Prop :=
  if u then bit (splitIndex i) w ≠ bit (smallIndex i) w
  else bit (splitIndex i) w = true ∧ bit (smallIndex i) w = false

def cut (u : Bool) (w : Sig) : BitVec 84 :=
  if u then (((w >>> 84) ^^^ w).setWidth 84)
  else (((w >>> 84) &&& ~~~w).setWidth 84)

def cuts (u : Bool) (ws : List Sig) : BitVec 84 :=
  ws.foldr (fun w c => cut u w ||| c) 0

theorem cut_bit (u : Bool) (i : Fin 84) (w : Sig) :
    (cut u w).getLsbD i.val = true ↔ separates u i w := by
  have hi : i.val < 168 := by omega
  cases u <;>
    simp [cut, separates, bit, splitIndex, smallIndex, i.isLt, hi, Nat.add_comm]

theorem goal_separates (u : Bool) (i : Fin 84) : separates u i goal := by
  have hu : ¬ 84 + i.val < 84 := by omega
  have h1 : bit (splitIndex i) goal = true := by
    change (BitVec.allOnes 84 ++ (0 : BitVec 84)).getLsbD (84 + i.val) = true
    rw [BitVec.getLsbD_append, if_neg hu, BitVec.getLsbD_allOnes]
    exact decide_eq_true (by omega)
  have h0 : bit (smallIndex i) goal = false := by
    change (BitVec.allOnes 84 ++ (0 : BitVec 84)).getLsbD i.val = false
    rw [BitVec.getLsbD_append]
    simp [i.isLt]
  cases u <;> simp [separates, h1, h0]

theorem bin_separates {u d} (hd : allowed u d) (i : Fin 84) (a b : Sig) :
    separates u i (bin d a b) → separates u i a ∨ separates u i b := by
  rcases allowed_four hd with rfl | rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    (try cases u) <;> simp [separates, bit_bin] <;>
    cases bit (splitIndex i) a <;> cases bit (smallIndex i) a <;>
    cases bit (splitIndex i) b <;> cases bit (smallIndex i) b <;> decide

theorem live_covers {u k S} (h : Live u goal k S) (i : Fin 84) : ∃ w ∈ S, separates u i w := by
  induction h using Live.ind with
  | stop _ => exact ⟨goal, by simp, goal_separates u i⟩
  | @binary k U a b d hd ha hb hab fresh tail ih =>
    obtain ⟨v, hv, hsep⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hv
    · rcases bin_separates hd _ _ _ hsep with e | e
      · exact ⟨a, by simp, e⟩
      · exact ⟨b, by simp, e⟩
    · exact ⟨v, by simp [hv], hsep⟩

theorem cuts_bit (u : Bool) (ws : List Sig) (i : Fin 84) :
    (cuts u ws).getLsbD i.val = true ↔ ∃ w ∈ ws, separates u i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a ws h =>
    change (cut u a ||| cuts u ws).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, h, cut_bit]
    simp

theorem cuts_full {u k ws} (h : Live u goal k (List.toFinset ws)) : cuts u ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hsep := live_covers h ⟨j, hj⟩
  have hbit := (cuts_bit u ws ⟨j, hj⟩).mpr (by simpa using hsep)
  change (cuts u ws)[j] = (BitVec.allOnes 84)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

def codes (u : Bool) : List ℕ := if u then [0, 1, 2, 3] else [0, 1]

theorem codes_all {u d} (h : allowed u d) : d ∈ codes u := by
  rcases allowed_four h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> (try cases u) <;> simp [codes]

def branch (u : Bool) (k : ℕ) (step : List Sig → Bool) (ws : List Sig)
    (choice : Sig × Sig × List Sig) : Bool :=
  let (a,b,rest) := choice
  let base := cuts u rest
  (codes u).any fun d =>
    let z := bin d a b
    let covered := cut u z ||| base
    !(ws.contains z) &&
      ((decide (rest.length ≤ k) && covered == -1 && step (z :: rest)) ||
        (decide (rest.length + 1 ≤ k) &&
          (((covered ||| cut u a) == -1 && step (z :: a :: rest)) ||
           ((covered ||| cut u b) == -1 && step (z :: b :: rest)))) ||
        (decide (rest.length + 2 ≤ k) &&
          (covered ||| cut u a ||| cut u b) == -1 && step (z :: a :: b :: rest)))

def search (u : Bool) : ℕ → List Sig → Bool
  | 0, ws => ws == [goal]
  | k + 1, ws => ws == [goal] || (pairs ws).any (branch u k (search u k) ws)

theorem search_of_live {u : Bool} {k : ℕ} {S : Finset Sig} (h : Live u goal k S)
    (ws : List Sig) (hn : ws.Nodup) (equal : ws.toFinset = S)
    (fuel : ℕ) (hFuel : k ≤ fuel) :
    search u fuel ws = true := by
  induction h using Live.ind generalizing ws fuel with
  | stop _ =>
    have e := singleton_list hn equal
    subst ws
    cases fuel <;> simp [search]
  | @binary k U a b d hd ha hb hab fresh tail ih =>
    obtain _ | fuel := fuel
    · omega
    obtain ⟨r, hm, hp⟩ := pick_two
      (ws := ws) (a := a) (b := b)
      (List.mem_toFinset.mp (by simp [equal])) (List.mem_toFinset.mp (by simp [equal])) hab
    let original := bin d a b
    have go {a' b' : Sig} {d' : ℕ} (md : allowed u d') (hdz : bin d' a' b' = original)
        (hmem : (a',b',r) ∈ pairs ws) (perm : ws.Perm (a'::b'::r))
        (heq : ws.toFinset = insert a' (insert b' U)) :
        search u (fuel + 1) ws = true := by
      obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn heq
      let z := bin d' a' b'
      have hz : z ∉ ws := by
        intro e
        have he := List.mem_toFinset.mpr e
        rw [equal, show z = original from hdz] at he
        exact fresh he
      have hz' : z ∉ kept := by
        intro hh
        apply fresh
        change original ∈ insert a (insert b U)
        rw [← hdz]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hh))
      have hnd : (z::kept).Nodup := List.nodup_cons.mpr ⟨hz', hnk⟩
      have next_eq : (z::kept).toFinset = insert original U := by simp [z, hdz, hfin]
      have v := ih (z::kept) hnd next_eq fuel (by omega)
      have hl : Live u goal k (z::kept).toFinset := by simpa only [next_eq] using tail
      have c := cuts_full hl
      have len := live_size hl
      rw [List.toFinset_card_of_nodup hnd, List.length_cons] at len
      simp only [search, branch, Bool.or_eq_true, List.any_eq_true]
      right
      refine ⟨(a',b',r), hmem, d', codes_all md, ?_⟩
      have no : ws.contains z = false := by simpa using hz
      change (!ws.contains z && _) = true
      simp only [no, Bool.not_false, Bool.true_and, Bool.or_eq_true, Bool.and_eq_true,
        decide_eq_true_eq, beq_iff_eq]
      simp [keepChoices] at hk
      rcases hk with rfl | rfl | rfl | rfl <;>
        simp only [cuts, List.foldr_cons] at c <;>
        (try simp only [List.length_cons] at len)
      · exact Or.inl (Or.inl ⟨⟨by omega,c⟩,v⟩)
      · exact Or.inl (Or.inr ⟨by omega,Or.inl ⟨by convert c using 1; simp only [cuts, z]; ac_rfl,v⟩⟩)
      · exact Or.inl (Or.inr ⟨by omega,Or.inr ⟨by convert c using 1; simp only [cuts, z]; ac_rfl,v⟩⟩)
      · exact Or.inr ⟨⟨by omega,by convert c using 1; simp only [cuts, z]; ac_rfl⟩,v⟩
    rcases hm with h | h
    · exact go hd rfl h hp equal
    · exact go (flip_flip hd).1 (bin_flip hd _ _).symm h
        (hp.trans (.swap _ _ _)) (by rw [equal, Finset.insert_comm])



open PEqualNP.MetaComplexity

set_option maxRecDepth 5000 in
theorem sampled : ∀ r : Row, inputs.map (bit r) = List.ofFn (rowInput r) := by
  decide +kernel

set_option maxRecDepth 5000 in
theorem target_rows : ∀ r : Row, bit r goal = graph (rowInput r) := by
  decide +kernel

def idx (i : Fin 6) : Fin 84 := [36, 50, 37, 41, 49, 26].getD i.val 0

theorem inputs_indexed : List.ofFn (fun i : Fin 6 => inputs.getD i.val zero) = inputs := rfl

theorem input_essential :
    ∀ i j : Fin 6, i ≠ j →
      bit (splitIndex (idx i)) (inputs.getD j.val zero) =
        bit (smallIndex (idx i)) (inputs.getD j.val zero) := by
  decide +kernel

theorem roots_equal {u k S} (run : Live u goal k S) (sub : ∀ a ∈ S, a ∈ inputs) :
    S = inputs.toFinset := by
  ext a
  constructor
  · intro ha
    exact List.mem_toFinset.mpr (sub a ha)
  · intro ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (by rwa [inputs_indexed] :
      a ∈ List.ofFn (fun i : Fin 6 => inputs.getD i.val zero))
    have diff : bit (splitIndex (idx i)) goal ≠ bit (smallIndex (idx i)) goal := by
      exact goal_separates true (idx i)
    apply raw_required run inputs (inputs.getD i.val zero) sub
      (splitIndex (idx i)) (smallIndex (idx i)) diff
    intro w hw hne
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp (by rwa [inputs_indexed] :
      w ∈ List.ofFn (fun i : Fin 6 => inputs.getD i.val zero))
    exact input_essential i j (fun h => hne (by rw [h]))

theorem signature_eval (C : Circuit) (legal : FanInTwo C) (r : Row) :
    bit r ((execute C.gates inputs).getD C.output zero) = C.eval (List.ofFn (rowInput r)) := by
  rw [← b_read, execute_bits _ _ _ (fun g hg => (legal g hg).1), sampled]
  rfl

theorem binaryLower (excluded : search true 7 inputs = false) (C : Circuit) (legal : FanInTwo C)
    (computes : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = graph x) :
    8 ≤ C.gates.countP (fun g => !isNot g) := by
  by_contra! small
  have goalEq : (execute C.gates inputs).getD C.output zero = goal :=
    bit_ext fun r => (signature_eval C legal r).trans ((computes _).trans (target_rows r).symm)
  have plain : bit 0 goal = false := by decide
  have proper_goal : proper goal := by unfold proper; decide
  have out := get_rep (u := true) (execute C.gates inputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  rw [nrm_id plain] at out
  obtain ⟨k, S, hk, run, sub⟩ := extract C.gates inputs legal (by simp) proper_goal
    (out.resolve_right (fun h => h proper_goal))
  rw [nrm_map (by decide : inputs.all plainWord = true)] at sub
  have hs := search_of_live run inputs (by decide) (roots_equal run sub).symm 7 (by omega)
  rw [excluded] at hs
  contradiction


set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem excluded : search true 7 inputs = false := by decide +kernel

def upper : Circuit :=
  ⟨[⟨.or, [0,1]⟩, ⟨.or, [0,5]⟩, ⟨.and, [2,3]⟩, ⟨.or, [2,3]⟩, ⟨.and, [7,9]⟩, ⟨.or, [4,10]⟩, ⟨.and, [6,11]⟩, ⟨.or, [8,12]⟩], 13⟩

private lemma upper_monotone : Monotone2 upper := by simp [upper,Monotone2]

private lemma upper_evaluation : ∀ x : Fin 6 → Bool, upper.eval (List.ofFn x) = graph x := by
  decide +kernel

private theorem replacement (s : ℕ) (hs : HasCircuitSize 6 graph s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧
      ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = graph x := by
  obtain ⟨C, ok, len, eval⟩ := hs
  have bound := binaryLower excluded C ok eval
  have cost := List.countP_le_length (p := fun g => !isNot g) (l := C.gates)
  change C.gates.length ≤ s at len
  exact ⟨upper, upper_monotone, by change 8 ≤ s; omega, upper_evaluation⟩

end PEqualNP.Outside.L_meta_13141.Signed

theorem PEqualNP.Outside.L_meta_13141 :
∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075680 * 2 ^ 32 + 4277074592) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075680 * 2 ^ 32 + 4277074592) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := PEqualNP.Outside.L_meta_13141.Signed.replacement
