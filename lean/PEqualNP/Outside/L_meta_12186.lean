import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12186

-- The signed live-wire search and the gate-elimination argument follow L-meta-1449,
-- Apache-2.0. Complemented threshold-two assignments sample the threshold-four function.

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

-- The upper and lower halves represent opposite target labels on 60 pairs of assignments.
abbrev W := BitVec 120
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 60 := ((x >>> 60) ^^^ x).setWidth 60
def cuts (ws : List W) : BitVec 60 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 60) ++ (0 : BitVec 60)
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

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 60) (w : W) : Prop :=
  w.getLsbD (60+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 60) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 60+i.val < 120 := by omega
  have hi' : i.val < 120 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 60) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 60)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
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

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hg hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) ws

theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', optimized_complete hg n ws _ hnd (by omega : n+1-ws.length+ws.length=n+1) hl']⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 120 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 120)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 120) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 120) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 120) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#120)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k (~~~goal)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (~~~goal) := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩
def inputs : List W := [0xc0c33c03030cf00808228020208a, 0x3030ccc0c0c333020208840808221, 0xc0c30f03030c3c080820502020814, 0x30303f00c0c0fc0202015008080540, 0xc03fc00300ff000801540020055000, 0xffc00003ff00000554000015500000]

def complementInputs : List W := inputs.map (fun w => ~~~w)

def targetFun (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (3900735488 * 2 ^ 32 + 2147483648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 8000 in
theorem sample_rows : ∀ j : Fin 120,
    targetFun (fun i => (complementInputs.getD i.val 0)[j.val]) = (~~~goal)[j.val] := by
  decide +kernel

theorem bound_from_impossible (n : ℕ)
    (impossible : ∀ t, t = goal ∨ t = ~~~goal → build basicOps t n inputs.toFinset → False)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = targetFun x) :
    n < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ complementInputs, holds inputs.toFinset u := by
    intro u hu
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hu
    exact .inr (.inr ⟨w, List.mem_toFinset.mpr hw, .inr rfl⟩)
  have evaluate (k : Fin 120) :
      (gs.foldl step (complementInputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (complementInputs.getD i.val 0)
    have width : complementInputs.length = 6 := rfl
    have same : List.ofFn x = complementInputs.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < complementInputs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (complementInputs.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample_rows k
  obtain ⟨t,ht,run⟩ := compile gs o hg complementInputs inputs.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t b inputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact impossible t ht (lift low run)

def SignedBuild (k : ℕ) (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ build basicOps z k av ∨ build basicOps (~~~z) k av

theorem sb_zero {av : Finset W} {z : W} (h : holds av z) : SignedBuild 0 av z := by
  rcases h with h | h | ⟨a,ha,e | e⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · subst z; exact Or.inr (Or.inr (Or.inl ha))
  · subst z; exact Or.inr (Or.inr (Or.inr (by simpa only [BitVec.not_not,build] using ha)))

theorem sb_wait {av : Finset W} {z : W} {k : ℕ} (h : SignedBuild k av z) :
    SignedBuild (k+1) av z := by
  rcases h with h|h|h|h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl (.inl h)))
  · exact .inr (.inr (.inr (.inl h)))

theorem sb_le {av : Finset W} {z : W} {k l : ℕ} (hkl : k ≤ l) (h : SignedBuild k av z) :
    SignedBuild l av z := by
  induction hkl with
  | refl => exact h
  | step _ ih => exact sb_wait ih

theorem sb_step {av : Finset W} {t a b z : W} {k : ℕ} (ha : a ∈ av) (hb : b ∈ av)
    (hne : a ≠ b) (hz : z ∈ basicOps a b) (h : SignedBuild k (insert z av) t) :
    SignedBuild (k+1) av t := by
  rcases h with h|h|h|h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl (.inr ⟨a,ha,b,hb,hne,z,hz,h⟩)))
  · exact .inr (.inr (.inr (.inr ⟨a,ha,b,hb,hne,z,hz,h⟩)))

theorem sb_holds_mono {av av' : Finset W} (sub : av ⊆ av') {x : W} (h : holds av x) :
    holds av' x := by
  rcases h with h|h|⟨a,ha,e⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨a,sub ha,e⟩)

theorem sb_advance {av : Finset W} {z t : W} {k : ℕ} (hz : reachable av z)
    (next : ∀ av' : Finset W, av ⊆ av' → holds av' z → SignedBuild k av' t) :
    SignedBuild (k+1) av t := by
  rcases hz with h | ⟨a,ha,b,hb,hn,w,hw,ok⟩
  · exact sb_wait (next av (fun _ h => h) h)
  · exact sb_step ha hb hn hw (next (insert w av) (fun _ h => Finset.mem_insert_of_mem h) ok)

theorem mem_ops_reach {av : Finset W} {x y z : W} (hx : holds av x) (hy : holds av y)
    (hz : z ∈ basicOps x y) : reachable av z := by
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl
  · exact and_reach hx hy
  · exact or_reach hx hy
  · exact and_reach hx (holds_not hy)
  · exact and_reach hy (holds_not hx)

set_option maxRecDepth 5000 in
theorem mem_ops_zero {av : Finset W} {x y z : W} (hx : holds av x) (hy : holds av y)
    (hzero : x = 0 ∨ y = 0) (hz : z ∈ basicOps x y) : holds av z := by
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hz
  have hc : holds av (0 : W) := .inl rfl
  have absorb (v : W) : v &&& (~~~(0 : W)) = v := by
    exact (congrArg (fun u : W => v &&& u) (BitVec.not_zero (n := 120))).trans BitVec.and_allOnes
  rcases hzero with rfl | rfl <;> rcases hz with rfl|rfl|rfl|rfl <;>
    first | rwa [absorb] | simp_all

theorem ops_map_of {f : W → W} (hAnd : ∀ a b, f (a &&& b) = (f a &&& f b))
    (hOr : ∀ a b, f (a ||| b) = (f a ||| f b)) (hNot : ∀ a, f (~~~a) = ~~~(f a)) :
    ∀ a b z, z ∈ basicOps a b → f z ∈ basicOps (f a) (f b) := by
  intro a b z hz
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hz ⊢
  rcases hz with rfl|rfl|rfl|rfl <;> simp [hAnd,hOr,hNot]

theorem live_transport {f : W → W} (hm : ∀ a b z, z ∈ basicOps a b → f z ∈ basicOps (f a) (f b))
    {g : W} {k : ℕ} {s av : Finset W} (run : live basicOps g k s)
    (hav : ∀ w ∈ s, holds av (f w)) : SignedBuild k av (f g) := by
  induction k generalizing s av with
  | zero =>
      change s = {g} at run
      exact sb_zero (hav g (by simp [run]))
  | succ k ih =>
      rcases run with skip | ⟨a,ha,b,hb,hn,z,hz,hout,r,he,tail⟩
      · exact sb_wait (ih skip hav)
      · apply sb_advance (mem_ops_reach (hav a ha) (hav b hb) (hm a b z hz))
        intro av' sub ok
        apply ih tail
        intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hr
        · exact ok
        · exact sb_holds_mono sub (hav u (by simp [he,hr]))

theorem live_transport_save {f : W → W}
    (hm : ∀ a b z, z ∈ basicOps a b → f z ∈ basicOps (f a) (f b))
    {g p : W} {k : ℕ} {s av : Finset W} (run : live basicOps g k s)
    (hp : p ∈ s) (hpg : p ≠ g) (hzero : f p = 0)
    (hav : ∀ w ∈ s, holds av (f w)) : SignedBuild (k-1) av (f g) := by
  induction k generalizing s av with
  | zero =>
      change s = {g} at run
      exact False.elim (hpg (by simpa [run] using hp))
  | succ k ih =>
      simp only [Nat.add_sub_cancel] at *
      rcases run with skip | ⟨a,ha,b,hb,hn,z,hz,hout,r,he,tail⟩
      · exact sb_le (Nat.sub_le _ _) (ih skip hp hav)
      · have mapped := hm a b z hz
        have inOld : ∀ u ∈ r, holds av (f u) := fun u hu => hav u (by simp [he,hu])
        by_cases touches : p = a ∨ p = b
        · have zz : f a = 0 ∨ f b = 0 := touches.elim (fun h => .inl (h ▸ hzero)) (fun h => .inr (h ▸ hzero))
          have collapsed := mem_ops_zero (hav a ha) (hav b hb) zz mapped
          apply live_transport hm tail
          intro u hu
          rcases Finset.mem_insert.mp hu with rfl | hr
          · exact collapsed
          · exact inOld u hr
        · have pr : p ∈ r := by
            rw [he] at hp
            simpa [Finset.mem_insert, touches, not_or.mp touches |>.1, not_or.mp touches |>.2] using hp
          have pt : p ∈ insert z r := Finset.mem_insert_of_mem pr
          have pos : 0 < k := by
            by_contra! hk
            have eq : k = 0 := by omega
            subst k
            change insert z r = {g} at tail
            exact hpg (by simpa [tail] using pt)
          have cost : (k-1)+1 = k := by omega
          rw [← cost]
          apply sb_advance (mem_ops_reach (hav a ha) (hav b hb) mapped)
          intro av' sub ok
          apply ih tail pt
          intro u hu
          rcases Finset.mem_insert.mp hu with rfl | hr
          · exact ok
          · exact sb_holds_mono sub (inOld u hr)

def fiveInputs : List W := [0x30cf030cf030cf0208a0208a0208a, 0xc3330c3330c333082210822108221, 0x30c3c30c3c30c3c208142081420814, 0xc0fc0c0fc0c0fc0805408054080540, 0xff000ff000ff000550005500055000]


def vinput (i : Fin 6) : W := inputs.getD i.val 0

def pairIx : Fin 6 → List ℕ := ![[4, 5, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 22, 23, 24, 25, 26, 27, 28, 29], [2, 3, 6, 7, 10, 11, 12, 13, 16, 17, 18, 19, 20, 21, 24, 25, 26, 27, 28, 29], [0, 1, 6, 7, 8, 9, 12, 13, 14, 15, 18, 19, 20, 21, 22, 23, 26, 27, 28, 29], [0, 1, 2, 3, 4, 5, 12, 13, 14, 15, 16, 17, 20, 21, 22, 23, 24, 25, 28, 29], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 20, 21, 22, 23, 24, 25, 26, 27], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]

def sourceRow (i : Fin 6) (j : Fin 120) : Fin 120 :=
  ⟨((if j.val < 60 then 0 else 60) + (pairIx i).getD ((j.val % 60) % 20) 0) % 120,
    Nat.mod_lt _ (by decide)⟩

def selectRows (rows : Fin 120 → Fin 120) (w : W) : W :=
  (BitVec.ofBoolListLE (List.ofFn (fun k : Fin 120 => w[(rows k).val]))).cast List.length_ofFn

def restriction (i : Fin 6) : W → W := selectRows (sourceRow i)

theorem selectRows_bit (rows : Fin 120 → Fin 120) (w : W) (j : Fin 120) :
    (selectRows rows w)[j.val] = w[(rows j).val] := by
  rw [← BitVec.getLsbD_eq_getElem j.isLt]
  simp only [selectRows, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, j.isLt, dite_eq_left, Option.getD_some]

theorem selectRows_land (rows : Fin 120 → Fin 120) (u v : W) :
    selectRows rows (u &&& v) = (selectRows rows u &&& selectRows rows v) := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  let k : Fin 120 := ⟨j,hj⟩
  change (selectRows rows (u &&& v))[k.val] = (selectRows rows u &&& selectRows rows v)[k.val]
  simp only [selectRows_bit, BitVec.getElem_and]

theorem selectRows_lor (rows : Fin 120 → Fin 120) (u v : W) :
    selectRows rows (u ||| v) = (selectRows rows u ||| selectRows rows v) := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  let k : Fin 120 := ⟨j,hj⟩
  change (selectRows rows (u ||| v))[k.val] = (selectRows rows u ||| selectRows rows v)[k.val]
  simp only [selectRows_bit, BitVec.getElem_or]

theorem selectRows_neg (rows : Fin 120 → Fin 120) (u : W) : selectRows rows (~~~u) = ~~~selectRows rows u := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  let k : Fin 120 := ⟨j,hj⟩
  change (selectRows rows (~~~u))[k.val] = (~~~selectRows rows u)[k.val]
  simp only [selectRows_bit, BitVec.getElem_not]

def remaining (i : Fin 6) : List W :=
  ((List.finRange 6).filter (· != i)).map fun j => restriction i (vinput j)

set_option maxRecDepth 8000 in
theorem projected_input : ∀ i : Fin 6, restriction i (vinput i) = 0 := by decide +kernel
set_option maxRecDepth 8000 in
theorem projected_goal : ∀ i : Fin 6, restriction i goal = goal := by decide +kernel


set_option maxRecDepth 8000 in
theorem remaining_same : ∀ i : Fin 6, remaining i = fiveInputs := by decide +kernel

set_option maxRecDepth 8000 in
theorem input_index : ∀ w ∈ inputs, ∃ i : Fin 6, vinput i = w := by
  intro w hw
  simp only [inputs, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact ⟨0,rfl⟩ | exact ⟨1,rfl⟩ | exact ⟨2,rfl⟩ | exact ⟨3,rfl⟩ | exact ⟨4,rfl⟩ | exact ⟨5,rfl⟩

theorem restricted_available : ∀ i j : Fin 6, holds (remaining i).toFinset (restriction i (vinput j)) := by
  intro i j
  by_cases h : i = j
  · subst j
    exact Or.inl (projected_input i)
  · right; right
    exact ⟨_, List.mem_toFinset.mpr (List.mem_map.mpr ⟨j, by simp [Ne.symm h],rfl⟩), Or.inl rfl⟩

def changes (w : W) (r : Fin 60) : Bool :=
  w.getLsbD (60+r.val) != w.getLsbD r.val

def rowIndex (i j : Fin 6) (op : Fin 4) : Fin 60 :=
  Fin.ofNat 60 ((#[0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 2, 0, 0, 6, 6, 0, 0, 12, 12, 0, 0, 20, 20, 0, 4, 1, 1, 4, 0, 0, 0, 0, 1, 4, 4, 1, 1, 8, 8, 1, 1, 14, 14, 1, 1, 22, 22, 1, 5, 3, 3, 5, 3, 5, 5, 3, 0, 0, 0, 0, 3, 10, 10, 3, 3, 16, 16, 3, 3, 24, 24, 3, 9, 7, 7, 9, 7, 9, 9, 7, 7, 11, 11, 7, 0, 0, 0, 0, 7, 18, 18, 7, 7, 26, 26, 7, 15, 13, 13, 15, 13, 15, 15, 13, 13, 17, 17, 13, 13, 19, 19, 13, 0, 0, 0, 0, 13, 28, 28, 13, 23, 21, 21, 23, 21, 23, 23, 21, 21, 25, 25, 21, 21, 27, 27, 21, 21, 29, 29, 21, 0, 0, 0, 0])[24 * i.val + 4 * j.val + op.val]!)

set_option maxRecDepth 8000 in
theorem rowIndex_spec : ∀ i j : Fin 6, i ≠ j → ∀ op : Fin 4,
    changes ((ops (vinput i) (vinput j)).getD op.val 0) (rowIndex i j op) = false ∧
    ∀ q : Fin 6, q ≠ i → changes (vinput q) (rowIndex i j op) = false := by decide +kernel

theorem separating_pair (i j : Fin 6) (he : i ≠ j) (op : Fin 4) : ∃ r : Fin 60,
    changes ((ops (vinput i) (vinput j)).getD op.val 0) r = false ∧
    ∀ q : Fin 6, q ≠ i → changes (vinput q) r = false :=
  ⟨rowIndex i j op, rowIndex_spec i j he op⟩

theorem index_of_op (a b z : W) (hz : z ∈ basicOps a b) :
    ∃ o : Fin 4, (ops a b).getD o.val 0 = z := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl
  all_goals first | exact ⟨0,rfl⟩ | exact ⟨1,rfl⟩ | exact ⟨2,rfl⟩ | exact ⟨3,rfl⟩

theorem unchanged (w : W) (r : Fin 60) (h : changes w r = false) : ¬ differs r w := by
  simpa [changes, differs] using h

theorem input_not_goal : ∀ i : Fin 6, vinput i ≠ goal ∧ vinput i ≠ ~~~goal := by decide +kernel

theorem goal_changes : ∀ k : Fin 60, differs k goal ∧ differs k (~~~goal) := by
  unfold differs
  decide +kernel

theorem restricted_new (i j : Fin 6) (z : W) (hz : z ∈ basicOps (vinput i) (vinput j)) :
    holds (remaining i).toFinset (restriction i z) := by
  exact mem_ops_zero (restricted_available i i) (restricted_available i j)
    (Or.inl (projected_input i))
    (ops_map_of (selectRows_land _) (selectRows_lor _) (selectRows_neg _) _ _ _ hz)

theorem raw_present {t : W} (ht : t = goal ∨ t = ~~~goal) (i j : Fin 6) (hij : i ≠ j)
    {z : W} (hz : z ∈ basicOps (vinput i) (vinput j)) (rest : Finset W)
    (hsub : rest ⊆ inputs.toFinset)
    (h : live basicOps t 10 (insert z rest)) : vinput i ∈ rest := by
  obtain ⟨o, ho⟩ := index_of_op _ _ _ hz
  obtain ⟨r, hrz, hrq⟩ := separating_pair i j hij o
  rw [ho] at hrz
  have hd : differs r t := by
    rcases ht with rfl|rfl
    · exact (goal_changes r).1
    · exact (goal_changes r).2
  obtain ⟨w, hw, hdw⟩ := live_separates (differs r) hd (ops_differs r) h
  rcases Finset.mem_insert.mp hw with rfl|hw
  · exact False.elim (unchanged _ _ hrz hdw)
  · obtain ⟨q,rfl⟩ := input_index _ (List.mem_toFinset.mp (hsub hw))
    by_contra hn
    have qi : q ≠ i := by intro eq; exact hn (eq ▸ hw)
    exact unchanged _ _ (hrq q qi) hdw

theorem projected_impossible (hnine : ∀ t, t = goal ∨ t = ~~~goal → build basicOps t 9 fiveInputs.toFinset → False) (i : Fin 6) (t : W) (ht : t = goal ∨ t = ~~~goal)
    (h : SignedBuild 9 (remaining i).toFinset (restriction i t)) : False := by
  rw [remaining_same] at h
  have signs : restriction i t = goal ∨ restriction i t = ~~~goal := by
    rcases ht with rfl|rfl
    · exact .inl (projected_goal i)
    · right
      change selectRows (sourceRow i) (~~~goal) = ~~~goal
      rw [selectRows_neg]
      exact congrArg (fun w : W => ~~~w) (projected_goal i)
  have nt : goal ≠ 0 ∧ goal ≠ ~~~0 ∧ ~~~goal ≠ 0 ∧ ~~~goal ≠ ~~~0 := by decide
  rcases signs with ht' | ht' <;> rw [ht'] at h
  all_goals
    rcases h with h | h | h | h
    · first | exact nt.1 h | exact nt.2.2.1 h
    · first | exact nt.2.1 h | exact nt.2.2.2 h
    · exact hnine _ (by simp) h
    · exact hnine _ (by simp) h

theorem no_eleven_binary (hnine : ∀ t, t = goal ∨ t = ~~~goal → build basicOps t 9 fiveInputs.toFinset → False) (t : W) (ht : t = goal ∨ t = ~~~goal)
    (run : build basicOps t 11 inputs.toFinset) : False := by
  obtain ⟨s, hs, hl⟩ := compress run
  rcases first_live (k := 10) hl with endcase | ⟨a,ha,b,hb,hab,z,hz,_,rest,he,tail⟩
  · have tx : t ∈ s := by simp [endcase]
    obtain ⟨i, hi⟩ := input_index _ (List.mem_toFinset.mp (hs tx))
    rcases ht with rfl|rfl
    · exact (input_not_goal i).1 hi
    · exact (input_not_goal i).2 hi
  · obtain ⟨i, rfl⟩ := input_index _ (List.mem_toFinset.mp (hs ha))
    obtain ⟨j, rfl⟩ := input_index _ (List.mem_toFinset.mp (hs hb))
    have hij : i ≠ j := fun eq => hab (congrArg vinput eq)
    have sub : rest ⊆ inputs.toFinset := by
      intro u hu
      exact hs (he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu))
    have keep := raw_present ht i j hij hz rest sub tail
    have pg : vinput i ≠ t := by rcases ht with rfl|rfl; exact (input_not_goal i).1; exact (input_not_goal i).2
    apply projected_impossible hnine i t ht
    apply live_transport_save (ops_map_of (selectRows_land _) (selectRows_lor _) (selectRows_neg _))
      tail (Finset.mem_insert_of_mem keep) pg (projected_input i)
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl|hw
    · exact restricted_new i j w hz
    · obtain ⟨k,rfl⟩ := input_index _ (List.mem_toFinset.mp (sub hw))
      exact restricted_available i k




private abbrev ShiftPart := ℕ × Bool × W

private def shiftPart (x : ShiftPart) (w : W) : W :=
  if x.2.1 then (w &&& x.2.2) <<< x.1 else (w &&& x.2.2) >>> x.1

private def readPart (x : ShiftPart) (j : ℕ) : Option ℕ :=
  if x.2.1 then
    if j < x.1 then none else
      if x.2.2.getLsbD (j - x.1) then some (j - x.1) else none
  else if x.2.2.getLsbD (j + x.1) then some (j + x.1) else none

private lemma readPart_sound (w : W) (x : ShiftPart) (j : ℕ) (hj : j < 120) :
    (shiftPart x w).getLsbD j = ((readPart x j).map w.getLsbD).getD false := by
  rcases x with ⟨d,b,m⟩
  cases b
  · have c : m.getLsbD (j+d) = false ∨ m.getLsbD (j+d) = true := by
      cases m.getLsbD (j+d) <;> simp
    rcases c with c | c <;>
      simp [shiftPart,readPart,BitVec.getLsbD_ushiftRight,BitVec.getLsbD_and,c,Nat.add_comm]
  · by_cases h : j < d
    · simp [shiftPart,readPart,BitVec.getLsbD_shiftLeft,BitVec.getLsbD_and,h]
    · have hjd : j-d < 120 := by omega
      cases hm : m.getLsbD (j-d) <;>
        have hm' := hm <;>
        rw [BitVec.getLsbD_eq_getElem hjd] at hm' <;>
        simp [shiftPart,readPart,h,hj,hm,hm',BitVec.getLsbD_eq_getElem hjd]


private def runParts (parts : List ShiftPart) (w : W) : W :=
  parts.foldr (fun x z => shiftPart x w ||| z) 0

private lemma runParts_sound (w : W) (parts : List ShiftPart) (j : ℕ) (hj : j < 120) :
    (runParts parts w).getLsbD j = (parts.filterMap (fun x => readPart x j)).any w.getLsbD := by
  induction parts with
  | nil => simp [runParts]
  | cons x parts ih =>
    change (shiftPart x w ||| runParts parts w).getLsbD j = _
    rw [BitVec.getLsbD_or, readPart_sound _ _ _ hj, ih]
    cases h : readPart x j <;> simp [h]

private def rowRename (tbl : Fin 120 → Fin 20 → Fin 20) (p : Fin 120) (j : Fin 120) : Fin 120 :=
  ⟨(j.val / 20)*20 + (tbl p (Fin.ofNat 20 j.val)).val, by
    have h := (tbl p (Fin.ofNat 20 j.val)).isLt
    have h' := j.isLt
    omega⟩

private lemma rowRename_inj (tbl : Fin 120 → Fin 20 → Fin 20) (p : Fin 120)
    (hi : Function.Injective (tbl p)) : Function.Injective (rowRename tbl p) := by
  intro a b h
  have q := congrArg Fin.val h
  have hta := (tbl p (Fin.ofNat 20 a.val)).isLt
  have htb := (tbl p (Fin.ofNat 20 b.val)).isLt
  change (a.val / 20)*20 + (tbl p (Fin.ofNat 20 a.val)).val =
    (b.val / 20)*20 + (tbl p (Fin.ofNat 20 b.val)).val at q
  have hm : (tbl p (Fin.ofNat 20 a.val)).val = (tbl p (Fin.ofNat 20 b.val)).val := by omega
  have hmod := congrArg Fin.val (hi (Fin.ext hm))
  change a.val % 20 = b.val % 20 at hmod
  exact Fin.ext (by omega)

private lemma selectRows_inj {rows : Fin 120 → Fin 120} (h : Function.Injective rows) :
    Function.Injective (selectRows rows) := by
  intro a b he
  apply BitVec.eq_of_getElem_eq
  intro i hi
  obtain ⟨j, hj⟩ := Finite.surjective_of_injective h ⟨i,hi⟩
  have v (w : W) : (selectRows rows w)[j.val] = w[i] := by
    rw [selectRows_bit]
    simpa [hj]
  rw [← v a, ← v b, he]

private lemma rowRename_goal (tbl : Fin 120 → Fin 20 → Fin 20) (p : Fin 120) :
    selectRows (rowRename tbl p) goal = goal := by
  have ranges (j : Fin 120) : 60 ≤ (rowRename tbl p j).val ↔ 60 ≤ j.val := by
    have h := (tbl p (Fin.ofNat 20 j.val)).isLt
    change 60 ≤ (j.val / 20)*20 + (tbl p (Fin.ofNat 20 j.val)).val ↔ _
    omega
  have goal_bit : ∀ j : Fin 120, goal[j.val] = decide (60 ≤ j.val) := by decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro i hi
  let j : Fin 120 := ⟨i,hi⟩
  change (selectRows (rowRename tbl p) goal)[j.val] = goal[j.val]
  rw [selectRows_bit,goal_bit,goal_bit]
  exact decide_eq_decide.mpr (ranges j)

private lemma live_rename {f : W → W} (hinj : Function.Injective f)
    (hm : ∀ a b z, z ∈ basicOps a b → f z ∈ basicOps (f a) (f b))
    {g : W} {k : ℕ} {s : Finset W} (h : live basicOps g k s) :
    live basicOps (f g) k (s.image f) := by
  induction k generalizing s with
  | zero =>
    change s = {g} at h
    simp [live, h]
  | succ k ih =>
    rcases h with hs | ⟨a, ha, b, hb, hne, z, hz, hznot, r, he, tl⟩
    · exact Or.inl (ih hs)
    · refine Or.inr ⟨f a, Finset.mem_image.mpr ⟨a,ha,rfl⟩, f b,
        Finset.mem_image.mpr ⟨b,hb,rfl⟩, fun hb => hne (hinj hb), f z, hm _ _ _ hz,
        ?_, r.image f, by simp [he], by simpa using ih tl⟩
      intro hov
      obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp hov
      exact hznot (hinj heq ▸ hu)

private def quickDispatch (ws : List W) (extra : ℕ) (next : List W → Bool)
    (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    !(ws.contains w) &&
      (((v == -1) && next (w :: r)) ||
      ((extra != 0) && (((v ||| sep a == -1) && next (w :: a :: r)) ||
                         ((v ||| sep b == -1) && next (w :: b :: r)))) ||
      ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (w :: a :: b :: r)))

private lemma quickDispatch_complete {k extra : ℕ} {ws : List W} {a b z : W} {r kept : List W}
    (next : List W → Bool) (hz : z ∈ basicOps a b) (hf : z ∉ ws) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (z :: kept) = true) :
    quickDispatch ws extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  have notFound : ws.contains z = false := Bool.eq_false_iff.mpr (fun h => hf (List.contains_iff_mem.mp h))
  rw [notFound]
  simp only [Bool.not_false, Bool.true_and]
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · exact Or.inl (Or.inl ⟨hc, ht⟩)
  · exact Or.inl (Or.inr ⟨by omega, Or.inl ⟨by convert hc using 1; ac_rfl, ht⟩⟩)
  · exact Or.inl (Or.inr ⟨by omega, Or.inr ⟨by convert hc using 1; ac_rfl, ht⟩⟩)
  · exact Or.inr ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, ht⟩

private def stepPresent (k : ℕ) (ws : List W) (next : List W → Bool) : Bool :=
  (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a,b,r) => quickDispatch ws (k+2-ws.length) next a b r)

private lemma stepPresent_complete {k : ℕ} {g : W} (gt : g=goal ∨ g= ~~~goal)
    (ws : List W) (nd : ws.Nodup) (run : live basicOps g (k+1) ws.toFinset)
    (next : List W → Bool)
    (hyp : ∀ v, v.Nodup → live basicOps g k v.toFinset → next v = true) :
    stepPresent k ws next = true := by
  have l := live_card run
  rw [List.toFinset_card_of_nodup nd] at l
  rcases first_live run with done | ⟨a,ha,b,hb,hab,z,hz,hout,r,he,tail⟩
  · rcases gt with rfl | rfl <;> simp [stepPresent, singleton_list nd done]
  obtain ⟨r',hm,hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
  have haveCandidate {a b : W} (perm : ws.Perm (a :: b :: r'))
      (es : ws.toFinset = insert a (insert b r)) (hz' : z ∈ basicOps a b) :
      quickDispatch ws (k+2-ws.length) next a b r' = true := by
    obtain ⟨kept,hkeep,hnd,hfin⟩ := recover_kept perm nd es
    have zn : z ∉ kept := by
      intro zm
      exact hout (es ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (hfin ▸ List.mem_toFinset.mpr zm)))
    have hnz : (z::kept).Nodup := List.nodup_cons.mpr ⟨zn,hnd⟩
    have hl : live basicOps g k (z::kept).toFinset := by simpa [hfin] using tail
    have hk := live_card hl
    rw [List.toFinset_card_of_nodup hnz,List.length_cons] at hk
    have hlen := perm.length_eq
    simp only [List.length_cons] at hlen
    apply quickDispatch_complete (k := k) next hz' (by simpa using hout) hkeep (by omega) (by omega)
      (cuts_full gt hl) (hyp _ hnz hl)
  simp only [stepPresent,Bool.or_eq_true,List.any_eq_true]
  right
  rcases hm with hd | hs
  · exact ⟨(a,b,r'),hd,haveCandidate hp he hz⟩
  · exact ⟨(b,a,r'),hs,haveCandidate (hp.trans (.swap _ _ _))
      (by rw [he,Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

private def sameWires (a b : List W) : Bool :=
  a.all b.contains && b.all a.contains

private lemma sameWires_sound {a b : List W} (h : sameWires a b = true) : a.toFinset = b.toFinset := by
  obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp h
  ext x
  simp only [List.mem_toFinset]
  exact ⟨fun hm => List.contains_iff_mem.mp (List.all_eq_true.mp ha _ hm),
    fun hm => List.contains_iff_mem.mp (List.all_eq_true.mp hb _ hm)⟩

private def verifyLink (count : Nat → Nat) (states : Nat → Nat → List W)
    (locate : Nat → List W → Nat × Fin 120) (rename : Fin 120 → W → W)
    (k : ℕ) (ws : List W) : Bool :=
  let (j,p) := locate k ws
  decide (j < count k) && sameWires (ws.map (rename p)) (states k j)

private def checkNode (count : Nat → Nat) (states : Nat → Nat → List W)
    (locate : Nat → List W → Nat × Fin 120) (rename : Fin 120 → W → W)
    (k i : ℕ) : Bool :=
  let v := states k i
  decide v.Nodup && (if k=0 then v != [goal] && v != [~~~goal]
    else !(stepPresent (k-1) v (fun w => Bool.not (verifyLink count states locate rename (k-1) w))))

private lemma noLiveTable {count : Nat → Nat} {states : Nat → Nat → List W}
    {locate : Nat → List W → Nat × Fin 120} {rename : Fin 120 → W → W} {cap : ℕ}
    (isInj : ∀ p, Function.Injective (rename p))
    (isHom : ∀ p a b z, z ∈ basicOps a b → rename p z ∈ basicOps (rename p a) (rename p b))
    (fixGoal : ∀ p g, (g=goal ∨ g= ~~~goal) → rename p g=g)
    (checked : ∀ k ≤ cap, ∀ i < count k, checkNode count states locate rename k i = true) :
    ∀ k ≤ cap, ∀ i < count k, ∀ g, g=goal ∨ g= ~~~goal →
      ¬ live basicOps g k (states k i).toFinset := by
  intro k
  induction k with
  | zero =>
    intro hc i hi g hg hp
    have q := checked 0 hc i hi
    simp [checkNode] at q
    have he := singleton_list q.1 hp
    rcases hg with rfl | rfl
    · exact q.2.1 he
    · exact q.2.2 he
  | succ k ih =>
    intro hc i hi g hg hp
    have q := checked (k+1) hc i hi
    simp only [checkNode,Nat.succ_ne_zero,if_false,Nat.add_sub_cancel,Bool.and_eq_true,decide_eq_true_eq] at q
    have hn : ∀ w, w.Nodup → live basicOps g k w.toFinset →
        Bool.not (verifyLink count states locate rename k w) = true := by
      intro w _ hw
      have inv : verifyLink count states locate rename k w = false := Bool.eq_false_iff.mpr (by
        intro ok
        let jp := locate k w
        change (decide (jp.1 < count k) && sameWires (w.map (rename jp.2)) (states k jp.1)) = true at ok
        obtain ⟨hj,hs⟩ := Bool.and_eq_true_iff.mp ok
        have wr := live_rename (isInj jp.2) (isHom jp.2) hw
        have he : (w.map (rename jp.2)).toFinset = w.toFinset.image (rename jp.2) := by
          ext u
          simp
        rw [fixGoal _ _ hg, ← he, sameWires_sound hs] at wr
        exact ih (by omega) _ (of_decide_eq_true hj) _ hg wr)
      simp [inv]
    have yes := stepPresent_complete hg _ q.1 hp _ hn
    rw [yes] at q
    exact Bool.false_ne_true q.2

private def checkGroup (count : Nat → Nat) (states : Nat → Nat → List W)
    (locate : Nat → List W → Nat × Fin 120) (rename : Fin 120 → W → W)
    (k i : ℕ) : Nat → Bool
  | 0 => true
  | n+1 => checkNode count states locate rename k i && checkGroup count states locate rename k (i+1) n

private lemma checkGroup_join {count : Nat → Nat} {states : Nat → Nat → List W}
    {locate : Nat → List W → Nat × Fin 120} {rename : Fin 120 → W → W} (k i n m : ℕ)
    (h : checkGroup count states locate rename k i n = true)
    (h' : checkGroup count states locate rename k (i+n) m = true) :
      checkGroup count states locate rename k i (n+m) = true := by
  induction n generalizing i with
  | zero => simpa using h'
  | succ n ih =>
    rw [show n+1+m=n+m+1 by omega, checkGroup]
    obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp h
    exact Bool.and_eq_true_iff.mpr ⟨a, ih (i+1) b (by convert h' using 2 <;> omega)⟩

private lemma checkGroup_at {count : Nat → Nat} {states : Nat → Nat → List W}
    {locate : Nat → List W → Nat × Fin 120} {rename : Fin 120 → W → W} {k i n : ℕ}
    (h : checkGroup count states locate rename k i n = true) (j : ℕ)
    (hj : i ≤ j) (hj' : j < i+n) : checkNode count states locate rename k j = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp h
    by_cases e : i=j
    · exact e ▸ a
    · exact ih b (by omega) (by omega)

private def unpack (f : ℕ → ℕ) (width chunk i : ℕ) : ℕ :=
  (f (i / chunk) >>> ((i % chunk) * width)) &&& ((1 <<< width) - 1)


private def rowTablePacked (i : ℕ) : ℕ := (if i < 15 then (if i < 7 then (if i < 3 then (if i < 1 then 0x5aa534a0e6844a4189ee6b0208c2727b9ac52ca4189283982094d6a4a0e68c1ee6b0a4188209ca307b9ac5a928398a418820 else (if i < 2 then 0x94d285a8e67ba306b085080629c9ee8c1ac4a16a398850806252e112906294d28399ee6b0208454b290629c9ee6b12839820 else 0x52ca4844624a253399cf081ac844a452c627ba726b109080e65a92894ce629211189cf081ac8c1ee9c9ac2914b18909080e6)) else (if i < 5 then (if i < 4 then 0x4a16a94ce6215cf08211189ac7ba309c9ac215090814b188e64a2535a8e673c85082306b0627ba728c1ac424850816a39862 else 0x425cf2142094d6a39a306b06273d09214209ca306b16a398622914b84462425cf08253399ac2921152c6273d09082726b0e6) else (if i < 6 then 0x2150973c2052e1118a53399ac215cf424208454b18a726b0e64248573c205aa5339a11189ac73c85424208c2726b14b188e6 else 0x5aa533992884462291ac7b8018c2726b1ee52c62290e64a00194d6a399288c1ac7b862290019ca306b1ee5a8e64a06229001))) else (if i < 11 then (if i < 9 then (if i < 8 then 0x94d283996a7b9ac8c020214439c9ee6b2304a0e65a8202144352e11188a494ce64a1ac7b8018454b188a49c9ac7b8e64a001 else 0x52ca418a114a0e694c2073d8d844a41894b7b9ac9c820424c75a92839a53290628442073d8d8c1ee6b2722906252c20424c7) else (if i < 10 then 0x4a16a39a532142073c628458d7ba306b272214204246252cc74a2533996a73c20215ac8c0437ba726b23042420214e65a843 else 0x425cf0808594ce65a9ac8c04373d09080859c9ac8c0e65a8432914b18a114242073ce694d8d292111894b73c20425ac9c8c7)) else (if i < 13 then (if i < 12 then 0x21509081cf52c62844e694d8d215cf081098446252dac9c8c742485081cf5a8e694c628458d73c85081098c1ac9c86252cc7 else 0x5a8e694d2818a112918d005ee8c1ac9c9ee1894b290c70052894ce65a9286b2307b843004a49c9ac8c1ee3996a4a043004a4) else (if i < 14 then 0x94ce64a16a6b1ee8c00110c859c9ac7ba30399285a80110c8552c62844a439a534a18d005ee8446252ca46b2727b8c700528 else 0x52c62292113992894c01635cf844622914b6b1ee9c80131d095a8e64a253188a484401635cf8c1ac7ba72188a452c0131d09)))) else (if i < 22 then (if i < 18 then (if i < 16 then 0x4a0e65aa530808573c43636117b9ac8c272080854244331d4b4a0e694d6a081cf2158d10e307b9ac9ca3008109214c710d6a else (if i < 17 then 0x4242073c8539a535a98d10e3073c20424856b2728c0c710d6a2906252e110810973cc763653290628454b081cf4258d31e72 else 0x21420425cf1894b844c7636532142073d0918a1152d8d31e7242420215cf3996a94c436361173c20215096b2309c84331d4b)) else (if i < 20 then (if i < 19 then 0x3996a94d2810d8d00611291ee6b2309c9ee10cc70054b2912839a535a92863443006307b8a46b2728c1ee31c430056a4a0a4 else 0x39a534a16a6340110dee8c0856b2727ba3031c0110d285a8851894b844a431d8d006534a1ee18a1152ca4634c7006727b928) else (if i < 21 then 0x1894b2921131c016352894dcf18a112914b6340131dee9c9093996a4a25310c01634a4845cf6b2307ba7210c0131ca452d09 else 0x399285aa53004436348573e116b1ee8c2720044331c854254b3992894d6a0058d10dcf216306b1ee9ca30004c710d092156a))) else (if i < 26 then (if i < 24 then (if i < 23 then 0x810973c8531d8d10e535aa30081cf42485634c710e728c16a188a452e11004c76350973e53188a48454b0058d31dcf42672 else 0x8085425cf10cc76354b846530808573d0910d8d31e1152e7208109215cf31c436356a94e11081cf215096344331e309c94b) else (if i < 25 then 0x31c43634015aa534a211291ee6344331c018c2727b94b2912831d8d10c0194d6a4a2307b8a4634c710c019ca307b96a4a0a4 else 0x31d8d0044394d285a9ee8c085634c7004439c9ee8c1285a88510cc76340152e11292534a1ee10d8d31c018454b292727b928)) else (if i < 28 then (if i < 27 then 0x10cc70058d52ca48452894dcf10d8d004c7844a452dee9c90931c430058d5a92894ca4845cf63443004c78c1ee9c8a452d09 else 0x31c0110d8d4a16a94c8573e116340110cc77ba309c8854254b31c01634434a2535a9cf216306340131c437ba728c1092156a) else (if i < 29 then 0x4c763443425cf216535aa300058d31c4373d09216728c16a10c0131d8d2914b8450973e5310c01634c72921152dcf42672 else 0x44331d8d2150973d4b8465300443634c7215cf4261152e72004c710d8d4248573d6a94e110058d10cc773c85426309c94b)))))

private def rowTable (i : ℕ) : ℕ := unpack rowTablePacked 100 4 i

private def backTablePacked (i : ℕ) : ℕ := (if i < 15 then (if i < 7 then (if i < 3 then (if i < 1 then 0x8454b290629c9ee6b128398208c2727b9ac52ca4189283982094d6a4a0e68c1ee6b0a4188209ca307b9ac5a928398a418820 else (if i < 2 then 0x94d285a8e67ba306b085080629c9ee8c1ac4a16a398850806252e112906294d28399ee6b0205aa534a0e6844a4189ee6b020 else 0x425cf2142094d6a39a306b0624a2535a8e673c85082306b06273d09214209ca306b16a398627ba728c1ac424850816a39862)) else (if i < 5 then (if i < 4 then 0x73c85424208c2726b14b188e67ba309c9ac215090814b188e6844a452c627ba726b109080e68c1ee9c9ac2914b18909080e6 else 0x52ca4844624a253399cf081ac5a92894ce629211189cf081ac215cf424208454b18a726b0e62921152c6273d09082726b0e6) else (if i < 6 then 0x2150973c2052e1118a53399ac2914b84462425cf08253399ac4248573c205aa5339a11189ac4a16a94ce6215cf08211189ac else 0x8454b188a49c9ac7b8e64a0018c2726b1ee52c62290e64a00194d6a399288c1ac7b862290019ca306b1ee5a8e64a06229001))) else (if i < 11 then (if i < 9 then (if i < 8 then 0x94ce65a9286b2307b843004a49c9ac8c1ee3996a4a043004a452e11188a494ce64a1ac7b8015aa533992884462291ac7b801 else 0x31d8d10c0194d6a4a2307b8a439a535a92863443006307b8a4634c710c019ca307b96a4a0a46b2728c1ee31c430056a4a0a4) else (if i < 10 then 0x6344331c018c2727b94b291286b2309c9ee10cc70054b291288446252ca46b2727b8c7005288c1ac9c9ee1894b290c700528 else 0x52c62844a439a534a18d005ee5a8e694d2818a112918d005ee10d8d31c018454b292727b92818a1152ca4634c7006727b928)) else (if i < 13 then (if i < 12 then 0x10cc76340152e11292534a1ee1894b844a431d8d006534a1ee31c43634015aa534a211291ee3996a94d2810d8d00611291ee else 0x73d09080859c9ac8c0e65a8437ba726b23042420214e65a84394d283996a7b9ac8c020214439c9ee6b2304a0e65a82021443) else (if i < 14 then 0x94ce64a16a6b1ee8c00110c859c9ac7ba30399285a80110c85425cf0808594ce65a9ac8c0434a2533996a73c20215ac8c043 else 0x31d8d0044394d285a9ee8c08539a534a16a6340110dee8c085634c7004439c9ee8c1285a8856b2727ba3031c0110d285a885)))) else (if i < 22 then (if i < 18 then (if i < 16 then 0x6340131c437ba728c1092156a6b1ee9ca30004c710d092156a73c20424856b2728c0c710d6a7b9ac9ca3008109214c710d6a else (if i < 17 then 0x4242073c8539a535a98d10e304a0e694d6a081cf2158d10e300058d31c4373d09216728c16a081cf42485634c710e728c16a else 0x4c763443425cf216535aa300810973c8531d8d10e535aa3031c01634434a2535a9cf216303992894d6a0058d10dcf21630)) else (if i < 20 then (if i < 19 then 0x73c85081098c1ac9c86252cc77ba306b272214204246252cc7844a41894b7b9ac9c820424c78c1ee6b2722906252c20424c7 else 0x844622914b6b1ee9c80131d098c1ac7ba72188a452c0131d09215cf081098446252dac9c8c7292111894b73c20425ac9c8c7) else (if i < 21 then 0x10d8d004c7844a452dee9c90918a112914b6340131dee9c90963443004c78c1ee9c8a452d096b2307ba7210c0131ca452d09 else 0x6340110cc77ba309c8854254b6b1ee8c2720044331c854254b73c20215096b2309c84331d4b7b9ac8c272080854244331d4b))) else (if i < 26 then (if i < 24 then (if i < 23 then 0x2142073d0918a1152d8d31e72290628454b081cf4258d31e720058d10cc773c85426309c94b081cf215096344331e309c94b else 0x443634c7215cf4261152e720808573d0910d8d31e1152e7210c01634c72921152dcf42672188a48454b0058d31dcf42672) else (if i < 25 then 0x42485081cf5a8e694c628458d4a16a39a532142073c628458d52ca418a114a0e694c2073d8d5a92839a53290628442073d8d else 0x52c62292113992894c01635cf5a8e64a253188a484401635cf21509081cf52c62844e694d8d2914b18a114242073ce694d8d)) else (if i < 28 then (if i < 27 then 0x10cc70058d52ca48452894dcf1894b2921131c016352894dcf31c430058d5a92894ca4845cf3996a4a25310c01634a4845cf else 0x31c0110d8d4a16a94c8573e11399285aa53004436348573e1142420215cf3996a94c43636114a0e65aa530808573c4363611) else (if i < 29 then 0x21420425cf1894b844c7636532906252e110810973cc763653004c710d8d4248573d6a94e1108109215cf31c436356a94e11 else 0x44331d8d2150973d4b8465308085425cf10cc76354b8465310c0131d8d2914b8450973e53188a452e11004c76350973e53)))))

private def backTable (i : ℕ) : ℕ := unpack backTablePacked 100 4 i

private def renSmall (p : Fin 120) (r : Fin 20) : Fin 20 :=
  Fin.ofNat 20 ((rowTable p.val >>> (5*r.val)) &&& 31)

private def renSmallInv (p : Fin 120) (r : Fin 20) : Fin 20 :=
  Fin.ofNat 20 ((backTable p.val >>> (5*r.val)) &&& 31)


private def planDescPacked (i : ℕ) : ℕ := (if i < 5 then (if i < 2 then (if i < 1 then 0xaa584a2c20140dc905a5028140f92058901a48061c008a0001 else 0x1be70d03c62962e8b15e58a5284b1e228c0fe58742c34961809) else (if i < 3 then 0x2924941209c904c872544124188c18434b20458fc1879143b45 else (if i < 4 then 0x3aa79c930df166c8c34871992cc4a05f8b2e4616630ae14548a else 0x4ae724b311f988d0b450621f25089c81ca3f859f228f5107906))) else (if i < 7 then (if i < 6 then 0x5c662d635641caecd55e62a5294c1aa38a5065a773136949948 else 0x6c46b5631a692d109670632d2d9098c58b61462fe317b10bbc7) else (if i < 8 then 0x80283f141f21af5cd7946bc029d91ce94d72c7b8839bd9adbcc else (if i < 9 then 0x9227484363d931c898c8745832249f0e5085c5c22320c930448 else 0xa668523428a9d41ce9f664ee36701d34cd98e64b83e551d27cb))))

private def planDesc (i : ℕ) : ℕ := unpack planDescPacked 17 12 i

private def planDataPacked (i : ℕ) : ℕ := (if i < 56 then (if i < 28 then (if i < 14 then (if i < 7 then (if i < 3 then (if i < 1 then 0x3000030000300003000030000300000a0080000800008000080000800008000c3c00c3c00c3c00c3c00c3c00c3c00c080400004000040000400004000040002c0000c0000c0000c0000c0000c0000080078000780007800078000780007802003f0003f0003f0003f0003f0003f006a00002000020000200002000020000030003f0003f0003f0003f0003f0003f0300001000010000100001000010000008fc000fc000fc000fc000fc000fc00067fffffffffffffffffffffffffffff81 else (if i < 2 then 0xf0000f0000f0000f0000f0000f00019800018000180001800018000180000400300003000030000300003000030008801e0001e0001e0001e0001e0001e00d0003c0003c0003c0003c0003c0003c120000600006000060000600006000060500001000010000100001000010000014000040000400004000040000400000610000100001000010000100001000014400004000040000400004000040000383c0003c0003c0003c0003c0003c000a0001e0001e0001e0001e0001e0001e09 else 0x3c3003c3003c3003c3003c3003c302400004000040000400004000040000090000100001000010000100001000007400004000040000400004000040000120f0000f0000f0000f0000f0000f000280007800078000780007800078000785401000010000100001000010000100078040000400004000040000400004000b1000010000100001000010000100000e4000040000400004000040000400000c0000c0000c0000c0000c0000c0000c0801e0001e0001e0001e0001e0001e008)) else (if i < 5 then (if i < 4 then 0xc0000c0000c0000c0000c0000c0001006000060000600006000060000600030c0000c0000c0000c0000c0000c000080618186181861818618186181861818500010000100001000010000100001007861818618186181861818618186180040008000080000800008000080000801186061860618606186061860618606040003c0003c0003c0003c0003c0003c2a0080000800008000080000800008004c020000200002000020000200002000788000080000800008000080000800003 else 0x4000040000400004000040000400040120001200012000120001200012001b00003000030000300003000030000040010000100001000010000100001000a000c0000c0000c0000c0000c0000c018006000060000600006000060000600440030000300003000030000300003006806000060000600006000060000600090000300003000030000300003000030a8002080020800208002080020800200e000820008200082000820008200080100006000060000600006000060000604) else (if i < 6 then 0xc0000c0000c0000c0000c0000c120000600006000060000600006000061500001000010000100001000010000034000040000400004000040000400000a1000010000100001000010000100001c48000480004800048000480004800048200002000020000200002000020000b018000180001800018000180001800180003000030000300003000030000301a00018000180001800018000180001824f000cf000cf000cf000cf000cf000c281800018000180001800018000180001 else 0xc0000c0000c0000c0000c0000c2a0080000800008000080000800008002c420004200042000420004200042000380001800018000180001800018000185200002000020000200002000020000060020000200002000020000200002001830000300003000030000300003000040010000100001000010000100001000a030c0030c0030c0030c0030c0030c0198000180001800018000180001800005003c0003c0003c0003c0003c0003c0088007800078000780007800078000780d))) else (if i < 10 then (if i < 8 then 0x300003000030000300003000030320001800018000180001800018000185401000010000100001000010000100098040000400004000040000400004000f0030300303003030030300303003030a0018000180001800018000180001800440000400004000040000400004000011000010000100001000010000100000644000440004400044000440004400025100011000110001100011000110000580c0000c0000c0000c0000c0000c000c00018000180001800018000180001819 else (if i < 9 then 0x800008000080000800008000080001406000060000600006000060000600050c0000c0000c0000c0000c0000c0000c0000180001800018000180001800018d000100001000010000100001000010161800018000180001800018000180002400480004800048000480004800048038010000100001000010000100001000303000030000300003000030000300003e0019e0019e0019e0019e0019e00181000300003000030000300003000030040060000600006000060000600006000c else 0xc0000c0000c0000c0000c0000c0000100080000800008000080000800008002800300003000030000300003000030060040000400004000040000400004000e0030000300003000030000300003002a001860018600186001860018600186340004000040000400004000040000405806000060000600006000060000600090002000020000200002000020000200e80000800008000080000800008000008000300003000030000300003000030242000420004200042000420004200006)) else (if i < 12 then (if i < 11 then 0x8400084000840008400084000840001410000100001000010000100001000038400004000040000400004000040000b01800018000180001800018000180018200002000020000200002000020000340002000020000200002000020000203c0000c0000c0000c0000c0000c0000c68001000010000100001000010000100b0c0000c0000c0000c0000c0000c000120020000200002000020000200002000ccc030cc030cc030cc030cc030cc030080100001000010000100001000010002 else 0x202002020020200202002020020200040800008000080000800008000080001820000200002000020000200002000050006000060000600006000060000600c030000300003000030000300003000298000180001800018000180001800007000c0000c0000c0000c0000c0000c00a8000800008000080000800008000080f00cc300cc300cc300cc300cc300cc31a0004000040000400004000040000402c0003000030000300003000030000300a0000200002000020000200002000006) else (if i < 13 then 0xc0000c0000c0000c0000c0000c010080000800008000080000800008000282000020000200002000020000200007018000180001800018000180001800184000040000400004000040000400003500001000010000100001000010000078000c0000c0000c0000c0000c0000c0e800060000600006000060000600006150000300003000030000300003000031a0080000800008000080000800008002c020000200002000020000200002000388080080800808008080080800808003 else 0xc0000c0000c0000c0000c0000c01007800078000780007800078000780033c0003c0003c0003c0003c0003c000080001800018000180001800018000181d0000c0000c0000c0000c0000c0000c2a0080000800008000080000800008003c0000c0000c0000c0000c0000c0000c68040000400004000040000400004000b0010000100001000010000100001000e0040000400004000040000400004000c400004000040000400004000040000110000100001000010000100001000006)))) else (if i < 21 then (if i < 17 then (if i < 15 then 0xc0c00c0c00c0c00c0c00c0c00c0c088000080000800008000080000800003a0000200002000020000200002000009018000180001800018000180001800143000030000300003000030000300003000006000060000600006000060000664000400004000040000400004000040b800900009000090000900009000090130020000200002000020000200002001e0800008000080000800008000080002c200002000020000200002000020000380006000060000600006000060000604 else (if i < 16 then 0x800008000080000800008000080000e0001800018000180001800018000180401000010000100001000010000100051986019860198601986019860198600c0080000800008000080000800008001d800018000180001800018000180000500000c0000c0000c0000c0000c0000cc80088000880008800088000880008817002200022000220002200022000220260800008000080000800008000080001c200002000020000200002000020000180060000600006000060000600006001 else 0x4000040000400004000040000400006019980199801998019980199801998042000020000200002000020000200001200002000020000200002000020000129000090000900009000090000900002c06000060000600006000060000600060800008000080000800008000080000d0000800008000080000800008000081b000030000300003000030000300003320004000040000400004000040000405c00400004000040000400004000040078210002100021000210002100021000b)) else (if i < 19 then (if i < 18 then 0x80000800008000080000800008000060080000800008000080000800008000802000020000200002000020000200030800008000080000800008000080000a000c0000c0000c0000c0000c0000c018400004000040000400004000040000380c0000c0000c0000c0000c0000c000a6000060000600006000060000600001c0001000010000100001000010000103600006000060000600006000060000664004800048000480004800048000480b80100001000010000100001000010013 else 0x1000010000100001000010000100001c400004000040000400004000040000480c0000c0000c0000c0000c0000c000c2000020000200002000020000200001a8000080000800008000080000800003c0002000020000200002000020000207c000800008000080000800008000080d800018000180001800018000180001990010000100001000010000100001001e0040000400004000040000400004002c000300003000030000300003000030482000020000200002000020000200007) else (if i < 20 then 0xf0c00f0c00f0c00f0c00f0c00f0c00020000400004000040000400004000040830cc030cc030cc030cc030cc030cc020000800008000080000800008000081f000200002000020000200002000020360000600006000060000600006000066400400004000040000400004000040098010000100001000010000100001000f0000c0000c0000c0000c0000c0000c120880008800088000880008800088000c220002200022000220002200022000100060000600006000060000600006008 else 0xc0000c0000c0000c0000c0000c0220180001800018000180001800018003400c0000c0000c0000c0000c0000c004800060000600006000060000600006054000140001400014000140001400010700005000050000500005000050000408000c0000c0000c0000c0000c0000c020180001800018000180001800018000830000300003000030000300003000018180001800018000180001800018000400c3300c3300c3300c3300c3300c330280000800008000080000800008000083))) else (if i < 24 then (if i < 22 then 0x400024000240002400024000240002050000100001000010000100001000001840000400004000040000400004000051000010000100001000010000100000e0300003000030000300003000030002018000180001800018000180001800060000300003000030000300003000030699818198181981819818198181981805004010040100401004010040100401060100401004010040100401004010040b30303303033030330303303033030020018000180001800018000180001800c else (if i < 23 then 0x1000010000100001000010000100000e4000240002400024000240002400020c00008000080000800008000080000810006000060000600006000060000600403000030000300003000030000300010006000060000600006000060000600333000330003300033000330003300008006600066000660006600066000660110000c0000c0000c0000c0000c0000c1a00600006000060000600006000060024000c0000c0000c0000c0000c0000c0280000800008000080000800008000083 else 0xc0000c0000c0000c0000c0000c00a2000220002200022000220002200020c8000880008800088000880008800081001800018000180001800018000180044000040000400004000040000400001c060000600006000060000600006000420000200002000020000200002000009060000600006000060000600006000180000c0000c0000c0000c0000c0000c320006000060000600006000060000604401000010000100001000010000100078040000400004000040000400004000b)) else (if i < 26 then (if i < 25 then 0xf0000f0000f0000f0000f0000f00010600006000060000600006000060000500000c0000c0000c0000c0000c0000c4879e0079e0079e0079e0079e0079e005c0000c0000c0000c0000c0000c00000200028000280002800028000280002808000a0000a0000a0000a0000a0000a03186001860018600186001860018600080000c0000c0000c0000c0000c0000c320080000800008000080000800008004c000c0000c0000c0000c0000c0000c088040000400004000040000400004000f else 0x30000300003000030000300003127e0007e0007e0007e0007e0007e000140100001000010000100001000010003004a0004a0004a0004a0004a0004a00ac0000c0000c0000c0000c0000c0000180050000500005000050000500005003800f0000f0000f0000f0000f0000f0088000180001800018000180001800018900c0000c0000c0000c0000c0000c000a8000080000800008000080000800000e000520005200052000520005200050100014000140001400014000140001406) else (if i < 27 then 0x1400014000140001400014000140140050000500005000050000500005003b000030000300003000030000300000c007e0007e0007e0007e0007e0007e0110003c0003c0003c0003c0003c0003c1a0000600006000060000600006000062500001000010000100001000010000054000040000400004000040000400000e100001000010000100001000010000244a0004a0004a0004a0004a0004a00058280002800028000280002800028000d0001e0001e0001e0001e0001e0001e0d else 0x80000800008000080000800008001e0000600006000060000600006000062400f0000f0000f0000f0000f0000f00288000080000800008000080000800006200002000020000200002000020000148a0008a0008a0008a0008a0008a0005a280022800228002280022800228000d0001e0001e0001e0001e0001e0001e19000030000300003000030000300003122080020800208002080020800208001c820008200082000820008200082000187800078000780007800078000780008))))) else (if i < 42 then (if i < 35 then (if i < 31 then (if i < 29 then 0x300003000030000300003000032218000180001800018000180001800024004400044000440004400044000440381800018000180001800018000180005002200022000220002200022000220060000800008000080000800008000080b0030300303003030030300303003002000040000400004000040000400004063000030000300003000030000300001001800018000180001800018000180040000f0000f0000f0000f0000f0000f0c80200002000020000200002000020013 else (if i < 30 then 0x48000480004800048000480004801c0100001000010000100001000010004800c0000c0000c0000c0000c0000c00a800618006180061800618006180061910001000010000100001000010000100e018000180001800018000180001800140008000080000800008000080000801a00022000220002200022000220002028400884008840088400884008840080c100001000010000100001000010000280c0000c0000c0000c0000c0000c00081800018000180001800018000180001c else 0x12000120001200012000120001200034400004000040000400004000040000780000c0000c0000c0000c0000c0000c88000800008000080000800008000080f00020000200002000020000200002016180001800018000180001800018000240c0300c0300c0300c0300c0300c030298000180001800018000180001800001001000010000100001000010000100040040000400004000040000400004001800100001000010000100001000010056000060000600006000060000600000c)) else (if i < 33 then (if i < 32 then 0x30000300003000030000300003000218000180001800018000180001800008000c0000c0000c0000c0000c0000c00a800618006180061800618006180061910001000010000100001000010000101e018000180001800018000180001800340008000080000800008000080000805800060000600006000060000600006054000040000400004000040000400001508001080010800108001080010800038200002000020000200002000020000900800008000080000800008000080016 else 0x20000200002000020000200002000348000080000800008000080000800007a00002000020000200002000020000110001800018000180001800018000181d0000c0000c0000c0000c0000c0000c3200006000060000600006000060000644010000100001000010000100001000388400084000840008400084000840003201002010020100201002010020100040840008400084000840008400084001820100201002010020100201002010050004000040000400004000040000400e) else (if i < 34 then 0xc0000c0000c0000c0000c0000c320000600006000060000600006000064401000010000100001000010000100078040000400004000040000400004000b0010000100001000010000100001000e0040000400004000040000400004000c0030000300003000030000300003002080000800008000080000800008000062000020000200002000020000200001408000080000800008000080000800038200002000020000200002000020000900800008000080000800008000080016 else 0x300003000030000300003000033a0022000220002200022000220002204c00880008800088000880008800088078200002000020000200002000020000b0800008000080000800008000080000e000080000800008000080000800008080030000300003000030000300003002000040000400004000040000400004060300003000030000300003000030001181801818018180181801818018180040c0000c0000c0000c0000c0000c0000a0001800018000180001800018000181d))) else (if i < 38 then (if i < 36 then 0x2100021000210002100021000210260004000040000400004000040000403c10000100001000010000100001000038006000060000600006000060000600508000080000800008000080000800006000080000800008000080000800008080002000020000200002000020000203006000060000600006000060000600084000040000400004000040000400001c0600006000060000600006000060004200002000020000200002000020000091800018000180001800018000180001c else (if i < 37 then 0x2000020000200002000020000202e0820008200082000820008200082002c2080020800208002080020800208003800060000600006000060000600006050300003000030000300003000030001000080000800008000080000800008028c0000c0000c0000c0000c0000c000060024000240002400024000240002400e00800008000080000800008000080025800018000180001800018000180000600000c0000c0000c0000c0000c0000ce80080000800008000080000800008017 else 0x100001000010000100001000010360024000240002400024000240002405c00800008000080000800008000080098006600066000660006600066000660500c0000c0000c0000c0000c0000c00020800008000080000800008000080000820000200002000020000200002000032080020800208002080020800208001692000920009200092000920009200034400004000040000400004000040000780000c0000c0000c0000c0000c0000ce8000800008000080000800008000081b)) else (if i < 40 then (if i < 39 then 0x300003000030000300003000033a0004000040000400004000040000406c00030000300003000030000300003068008000080000800008000080000800b0420004200042000420004200042000e1000010000100001000010000100000c01000010000100001000010000100030842008420084200842008420084200a2008020080200802008020080200801c0600006000060000600006000060004300003000030000300003000030000100000180001800018000180001800019d else 0x20000200002000020000200002001e00018000180001800018000180001834010000100001000010000100001000182400024000240002400024000240002000c0000c0000c0000c0000c0000c00810000100001000010000100001000018400004000040000400004000040000910800108001080010800108001080016020000200002000020000200002000348000080000800008000080000800007a00002000020000200002000020000110000800008000080000800008000081f) else (if i < 41 then 0x30000300003000030000300003010780007800078000780007800078000400c3000c3000c3000c3000c3000c3004800028000280002800028000280002870000a0000a0000a0000a0000a0000a0780001800018000180001800018000004f3c00f3c00f3c00f3c00f3c00f3c002000180001800018000180001800018080001000010000100001000010000103e00006000060000600006000060000674000800008000080000800008000080d80080000800008000080000800008013 else 0x200002000020000200002000020600880008800088000880008800088008300003000030000300003000030000200440004400044000440004400044006c0000c0000c0000c0000c0000c00001000600006000060000600006000060040003000030000300003000030000300a807800078000780007800078000780090000500005000050000500005000050e8001480014800148001480014800140e000020000200002000020000200000101800018000180001800018000180004)))) else (if i < 49 then (if i < 45 then (if i < 43 then 0x100001000010000100001000010e000600006000060000600006000060140000800008000080000800008000081a0000200002000020000200002000006800008000080000800008000080000142200022000220002200022000220003888000880008800088000880008800090600006000060000600006000060001c0000c0000c0000c0000c0000c0000c2206000060000600006000060000600024000040000400004000040000400004398018180181801818018180181801805 else (if i < 44 then 0x300003000030000300003000030220080000800008000080000800008002c4200442004420044200442004420043900011000110001100011000110001030004000040000400004000040000400406000060000600006000060000600010002000020000200002000020000200306180061800618006180061800618010c0000c0000c0000c0000c0000c00002800180001800018000180001800018054030300303003030030300303003030880180001800018000180001800018009 else 0x80000800008000080000800008001e00180001800018000180001800018024000040000400004000040000400004380001000010000100001000010000103100001000010000100001000010000040060000600006000060000600006001080000800008000080000800008000030080000800008000080000800008000e4200042000420004200042000420002500001000010000100001000010000058300003000030000300003000030000e0000600006000060000600006000061d)) else (if i < 47 then (if i < 46 then 0x100001000010000100001000011606180061800618006180061800618024000080000800008000080000800008380002000020000200002000020000203cc300cc300cc300cc300cc300cc30002000100001000010000100001000010080004000040000400004000040000403186001860018600186001860018600080002000020000200002000020000201400018000180001800018000180001874010000100001000010000100001000980018000180001800018000180001811 else 0xc0000c0000c0000c0000c0000c02a0060000600006000060000600006003400004000040000400004000040000458000100001000010000100001000010700c0000c0000c0000c0000c0000c000a8000880008800088000880008800080e0002200022000220002200022000201018000180001800018000180001800040001000010000100001000010000100c00040000400004000040000400004028300003000030000300003000030000618000180001800018000180001800014) else (if i < 48 then 0x800008000080000800008000080003c000180001800018000180001800018440000400004000040000400004000045818180181801818018180181801818090000200002000020000200002000020e600006000060000600006000060000143000030000300003000030000300000802200022000220002200022000220060088000880008800088000880008801580001800018000180001800018000030004000040000400004000040000400700100001000010000100001000010012 else 0xc0000c0000c0000c0000c0000c0000300018000180001800018000180001805403030030300303003030030300303088018000180001800018000180001800d00001000010000100001000010000116000600006000060000600006000060240000800008000080000800008000083a000020000200002000020000200000a8000080000800008000080000800001c22000220002200022000220002200048880008800088000880008800088000b0200002000020000200002000020001a))) else (if i < 52 then (if i < 50 then 0x800008000080000800008000080003c00018000180001800018000180001874000c0000c0000c0000c0000c0000c0a8000080000800008000080000800008b1040210402104021040210402104020e4100041000410004100041000410000c0c0000c0000c0000c0000c0000c0002000200002000020000200002000020060008000080000800008000080000801418000180001800018000180001800030004000040000400004000040000400700100001000010000100001000010012 else (if i < 51 then 0x3000030000300003000030000302a0080000800008000080000800008004c02000020000200002000020000200078000080000800008000080000800008b000c0000c0000c0000c0000c0000c0120000400004000040000400004000041c00c0000c0000c0000c0000c0000c000880000800008000080000800008000062000020000200002000020000200001402000020000200002000020000200049080010800108001080010800108000b4200042000420004200042000420001a else 0x900009000090000900009000090001c04000040000400004000040000400048c0000c0000c0000c0000c0000c00010000018000180001800018000180001950f0000f0000f0000f0000f0000f000120002000020000200002000020000201c0049000490004900049000490004901801240012400124001240012400124020008000080000800008000080000800de0001e0001e0001e0001e0001e000020030000300003000030000300003000a0000600006000060000600006000061d)) else (if i < 54 then (if i < 53 then 0x24000240002400024000240002400c0010000100001000010000100001002b0000300003000030000300003000006002000020000200002000020000200120080000800008000080000800008002c00786007860078600786007860078654000400004000040000400004000040380600006000060000600006000060005000240002400024000240002400024060001000010000100001000010000100900001000010000100001000010000034200042000420004200042000420000a else 0x8400084000840008400084000840001c12000120001200012000120001200048080000800008000080000800008000b0800008000080000800008000080001e20000200002000020000200002000044000060000600006000060000600006540004000040000400004000040000405878000780007800078000780007800090002400024000240002400024000240e0001000010000100001000010000100c004000040000400004000040000400118000180001800018000180001800004) else (if i < 55 then 0x101001010010100101001010010100044048040480404804048040480404801810200102001020010200102001020050480004800048000480004800048000e020000200002000020000200002000258000180001800018000180001800009000f0c00f0c00f0c00f0c00f0c00f0ca8000800008000080000800008000080b00c0000c0000c0000c0000c0000c00120004800048000480004800048000481c0002000020000200002000020000201a000020000200002000020000200000a else 0x2400024000240002400024000240042010020100201002010020100201001880000800008000080000800008000050200002000020000200002000020000e09000090000900009000090000900024040000400004000040000400004000590000100001000010000100001000011400004000040000400004000040000260003c0003c0003c0003c0003c0003c3a00006000060000600006000060000654010000100001000010000100001000380400004000040000400004000040003)))))) else (if i < 84 then (if i < 70 then (if i < 63 then (if i < 59 then (if i < 57 then 0x42000420004200042000420004200161000010000100001000010000100001c000100001000010000100001000010180024000240002400024000240002402030000300003000030000300003000080010000100001000010000100001001bc3003c3003c3003c3003c3003c3000a0001e0001e0001e0001e0001e0001e1d0000300003000030000300003000032a0080000800008000080000800008002c020000200002000020000200002000380080000800008000080000800008003 else (if i < 58 then 0x2000020000200002000020000201e0018000180001800018000180001802410010100101001010010100101001018400404004040040400404004040040200c0000c0000c0000c0000c0000c001002000020000200002000020000200039080010800108001080010800108000940000400004000040000400004000016300003000030000300003000030000400000600006000060000600006000068400040000400004000040000400004098009000090000900009000090000900f else 0x820408204082040820408204082040e0001000010000100001000010000100c0c0000c0000c0000c0000c0000c0002000200002000020000200002000020060008000080000800008000080000801460000600006000060000600006000040010000100001000010000100001000900400004000040000400004000040016c0000c0000c0000c0000c0000c00003000006000060000600006000060000684004000040000400004000040000400b80108001080010800108001080010813)) else (if i < 61 then (if i < 60 then 0x4000040000400004000040000400004018000180001800018000180001800102000020000200002000020000200003008000080000800008000080000800124200042000420004200042000420002d00001000010000100001000010000068400004000040000400004000040000f10000100001000010000100001000022000030000300003000030000300003420002000020000200002000020000205c00080000800008000080000800008098208002080020800208002080020800b else 0x80000800008000080000800008000040088000880008800088000880008801802200022000220002200022000220050880008800088000880008800088000e22000220002200022000220002200025800018000180001800018000180000900000c0000c0000c0000c0000c0000d0800880008800088000880008800088170022000220002200022000220002202600180001800018000180001800018024000100001000010000100001000010380004000040000400004000040000403) else (if i < 62 then 0x888008880088800888008880088800c22000220002200022000220002200048880008800088000880008800088000b200002000020000200002000020000228000080000800008000080000800004c00006000060000600006000060000684000400004000040000400004000040f8001000010000100001000010000101b0000c0000c0000c0000c0000c0000c220020000200002000020000200002002c008000080000800008000080000800382000020000200002000020000200003 else 0x4a0004a0004a0004a0004a0004a160010000100001000010000100001001ff0003f0003f0003f0003f0003f000020001800018000180001800018000180800f0000f0000f0000f0000f0000f001800006000060000600006000060000684000400004000040000400004000040f8001000010000100001000010000101b0000c0000c0000c0000c0000c0000c220020000200002000020000200002003c008000080000800008000080000800582220022200222002220022200222002))) else (if i < 66 then (if i < 64 then 0x80000800008000080000800008001c00600006000060000600006000060040003000030000300003000030000300c8000280002800028000280002800028f0000a0000a0000a0000a0000a0000a1601e0001e0001e0001e0001e0001e0025040010400104001040010400104000141000410004100041000410004100006000300003000030000300003000030107800078000780007800078000780006000014000140001400014000140001478180001800018000180001800018000d else (if i < 65 then 0x200002000020000200002000020000341800018000180001800018000180007000010000100001000010000100001098000480004800048000480004800048f0300003000030000300003000030001a0000400004000040000400004000042c001000010000100001000010000100380040000400004000040000400004003300003000030000300003000030000021806018060180601806018060180601300003000030000300003000030000040020000200002000020000200002000a else 0xc0000c0000c0000c0000c0000c0003180001800018000180001800018000070003000030000300003000030000300c800020000200002000020000200002130000900009000090000900009000091e01800018000180001800018000180034000080000800008000080000800008580180001800018000180001800018009000300003000030000300003000030088200082000820008200082000820001a080020800208002080020800208000508000080000800008000080000800016)) else (if i < 68 then (if i < 67 then 0x4000040000400004000040000400003418000180001800018000180001800072000020000200002000020000200000f00006000060000600006000060000621000300003000030000300003000030220000200002000020000200002000023c0100801008010080100801008010085804200042000420004200042000420071008010080100801008010080100800642000420004200042000420004200008080000800008000080000800008000300180001800018000180001800018010 else 0x3030030300303003030030300303001000040000400004000040000400004028030000300003000030000300003000800006000060000600006000060000621000300003000030000300003000030220080200802008020080200802008023c021080210802108021080210802108580040000400004000040000400004007100001000010000100001000010000044200042000420004200042000420001808000080000800008000080000800050018000180001800018000180001800c) else (if i < 69 then 0x8201082010820108201082010820100c00040000400004000040000400004028300003000030000300003000030000a1800018000180001800018000180001c000010000100001000010000100001260000400004000040000400004000043c0c0000c0000c0000c0000c0000c00068002200022000220002200022000220b0008800088000880008800088000880e18000180001800018000180001800007000030000300003000030000300000200008000080000800008000080000806 else 0x8000080000800008000080000800580001800018000180001800018000030014000140001400014000140001400700500005000050000500005000050012000c0000c0000c0000c0000c0000c0320000200002000020000200002000024c00008000080000800008000080000878018000180001800018000180001800d000040000400004000040000400004160001000010000100001000010000101c0300003000030000300003000030002a0800208002080020800208002080002)))) else (if i < 77 then (if i < 73 then (if i < 71 then 0xa0000a0000a0000a0000a0000a1e01e0001e0001e0001e0001e0001e0034000c0000c0000c0000c0000c0000c00a080020800208002080020800208000a8200082000820008200082000820001c28000280002800028000280002800068a0000a0000a0000a0000a0000a0000f000028000280002800028000280002930000a0000a0000a0000a0000a0000a1e0600006000060000600006000060003400100001000010000100001000010019e0181e0181e0181e0181e0181e01801 else (if i < 72 then 0x10000100001000010000100001260000400004000040000400004000043c01000010000100001000010000100038842008420084200842008420084200321080210802108021080210802108004040000400004000040000400004000180040000400004000040000400004007001000010000100001000010000100120c0000c0000c0000c0000c0000c0002980001800018000180001800018000080003000030000300003000030000300c80002800028000280002800028000293 else 0x40200402004020040200402004021e0108001080010800108001080010802c002000020000200002000020000200388000080000800008000080000800006003000030000300003000030000300104200042000420004200042000420002808000080000800008000080000800070200002000020000200002000020001a4800048000480004800048000480003d00001000010000100001000010000088000300003000030000300003000031080018000180001800018000180001815)) else (if i < 75 then (if i < 74 then 0x40000400004000040000400004160009000090000900009000090000901c300003000030000300003000030000280040000400004000040000400004003000100001000010000100001000010040024000240002400024000240002401bc0003c0003c0003c0003c0003c000040010000100001000010000100001000a00c0000c0000c0000c0000c0000c002800018000180001800018000180001884000c0000c0000c0000c0000c0000c0a80000800008000080000800008000093 else 0x40000400004000040000400004160001000010000100001000010000101c0300003000030000300003000030002800080000800008000080000800008024102041020410204102041020410200d04001040010400104001040010400028100001000010000100001000010000904000040000400004000040000400016300003000030000300003000030000400000200002000020000200002000025c00008000080000800008000080000898180001800018000180001800018000d) else (if i < 76 then 0x5000050000500005000050000500600140001400014000140001400014008c0000c0000c0000c0000c0000c000020008000080000800008000080000800ac0000c0000c0000c0000c0000c00001800400004000040000400004000040038010000100001000010000100001000900400004000040000400004000040016000c0000c0000c0000c0000c0000c0320000200002000020000200002000025c000080000800008000080000800008980180001800018000180001800018011 else 0x4100041000410004100041000410001504001040010400104001040010400038100001000010000100001000010000b0400004000040000400004000040001a1000010000100001000010000100003c40000400004000040000400004000088000040000400004000040000400004b800010000100001000010000100001130000400004000040000400004000041e06000060000600006000060000600034000200002000020000200002000020586000060000600006000060000600005))) else (if i < 80 then (if i < 78 then 0x40000400004000040000400004000241000010000100001000010000100005b0000300003000030000300003000012000600006000060000600006000060190000100001000010000100001000012e0000400004000040000400004000044c00c0000c0000c0000c0000c0000c0088000200002000020000200002000020f0000800008000080000800008000081601800018000180001800018000180024000400004000040000400004000040180010000100001000010000100001002 else (if i < 79 then 0x40000400004000040000400004000045000010000100001000010000100000980003000030000300003000030000310800180001800018000180001800018190000100001000010000100001000012e0000400004000040000400004000044c010000100001000010000100001000380420004200042000420004200042003100801008010080100801008010080044200042000420004200042000420001808400084000840008400084000840050010000100001000010000100001000e else 0xc0000c0000c0000c0000c0000c4200060000600006000060000600006064000040000400004000040000400004b80001000010000100001000010000113004000040000400004000040000400160108001080010800108001080010801c0020000200002000020000200002001880800808008080080800808008080062120021200212002120021200212001404000040000400004000040000400038100001000010000100001000010000b0400004000040000400004000040001a)) else (if i < 82 then (if i < 81 then 0x8000080000800008000080000800003c600006000060000600006000060000800000c0000c0000c0000c0000c0000d2800080000800008000080000800008130012000120001200012000120001201e0040800408004080040800408004082c1012010120101201012010120101203840400404004040040400404004040030100001000010000100001000010000404000040000400004000040000400018030000300003000030000300003000a7800078000780007800078000780001c else 0xc0000c0000c0000c0000c0000c0000400000600006000060000600006000069400440004400044000440004400044098011000110001100011000110001100f000440004400044000440004400044160011000110001100011000110001101c1000010000100001000010000100001840000400004000040000400004000020100001000010000100001000010000c0400004000040000400004000040002803000030000300003000030000300082000020000200002000020000200001a) else (if i < 83 then 0x300003000030000300003000034a0002000020000200002000020000205c00080000800008000080000800008098000200002000020000200002000020f001080010800108001080010800108160840008400084000840008400084001c2010020100201002010020100201001808400084000840008400084000840020200002000020000200002000020000c00800008000080000800008000080048020000200002000020000200002000b18000180001800018000180001800018 else 0x1000010000100001000010000102e0024000240002400024000240002404c00810008100081000810008100081078002400024000240002400024000240b0008000080000800008000080000800e0800008000080000800008000080000820000200002000020000200002000030080000800008000080000800008000a00c0000c0000c0000c0000c0000c001804000040000400004000040000400039400014000140001400014000140000f50000500005000050000500005000022))))) else (if i < 98 then (if i < 91 then (if i < 87 then (if i < 85 then 0x1000010000100001000010000100160040000400004000040000400004001c1010010100101001010010100101001840400404004040040400404004040020100001000010000100001000010000c040000400004000040000400004000280100001000010000100001000010007004000040000400004000040000400121000010000100001000010000100002c4000040000400004000040000400006b0000300003000030000300003000012000018000180001800018000180001a5 else (if i < 86 then 0x800008000080000800008000080000c028000280002800028000280002800280a0000a0000a0000a0000a0000a00070800008000080000800008000080001a2000020000200002000020000200003c8000080000800008000080000800008a0000200002000020000200002000013000018000180001800018000180001a5000100001000010000100001000010360004000040000400004000040000405c00010000100001000010000100001098000400004000040000400004000040f else 0x3000030000300003000030000301001e0001e0001e0001e0001e0001e0033f0003f0003f0003f0003f0003f00008000018000180001800018000180001a5000100001000010000100001000010360004000040000400004000040000405c00010000100001000010000100001098008400084000840008400084000840f002000020000200002000020000200160008000080000800008000080000801c002000020000200002000020000200182000020000200002000020000200002)) else (if i < 89 then (if i < 88 then 0x10000100001000010000100001000160400004000040000400004000040001c03c0003c0003c0003c0003c0003c002000180001800018000180001800018084000040000400004000040000400001d00001000010000100001000010000048f0000f0000f0000f0000f0000f0000c0000280002800028000280002800029b0004a0004a0004a0004a0004a0004a2e0010000100001000010000100001004c04000040000400004000040000400078100001000010000100001000010000b else 0x200002000020000200002000022e0008000080000800008000080000804c04200042000420004200042000420078100001000010000100001000010000b0003000030000300003000030000300800800008000080000800008000080028c0000c0000c0000c0000c0000c000060040000400004000040000400004000e0c3000c3000c3000c3000c3000c3002180001800018000180001800018000050001140011400114001140011400114d80045000450004500045000450004517) else (if i < 90 then 0x490004900049000490004900049360010400104001040010400104001045c04000040000400004000040000400038100001000010000100001000010000300c0000c0000c0000c0000c0000c0002006600066000660006600066000660110000100001000010000100001000009480004800048000480004800048000162000020000200002000020000200003418000180001800018000180001800070000100001000010000100001000010f8000480004800048000480004800049b else 0x8000080000800008000080000801e0200002000020000200002000020002c080000800008000080000800008000380018000180001800018000180001805004000040000400004000040000400040100001000010000100001000010001840000400004000040000400004000051000010000100001000010000100000e0030000300003000030000300003002018000180001800018000180001800063000030000300003000030000300000e0000200002000020000200002000021f))) else (if i < 94 then (if i < 92 then 0x800008000080000800008000080004006000060000600006000060000600304000040000400004000040000400007100001000010000100001000010000124000040000400004000040000400003418000180001800018000180001800072000020000200002000020000200000f000020000200002000020000200002230000800008000080000800008000083e0000200002000020000200002000026c000080000800008000080000800008b80020000200002000020000200002013 else (if i < 93 then 0x2000020000200002000020000201418000180001800018000180001800033030030300303003030030300303000818000180001800018000180001800014000040000400004000040000400004460001000010000100001000010000107c000040000400004000040000400004d80021000210002100021000210002117000800008000080000800008000080260200002000020000200002000020001c000c0000c0000c0000c0000c0000c0281200012000120001200012000120003 else 0x4000040000400004000040000400001d00001000010000100001000010000048300003000030000300003000030000a1800018000180001800018000180001c0000100001000010000100001000013e0000400004000040000400004000046c001100011000110001100011000110b800440004400044000440004400044130100001000010000100001000010001e0400004000040000400004000040002c000400004000040000400004000040300180001800018000180001800018008)) else (if i < 96 then (if i < 95 then 0xa0000a0000a0000a0000a0000a002580001800018000180001800018000060000040000400004000040000400004f8002100021000210002100021000211b0008400084000840008400084000842e0001000010000100001000010000104c040000400004000040000400004000581000010000100001000010000100007003000030000300003000030000300020002000020000200002000020000201803000030000300003000030000300040001000010000100001000010000100a else 0xf3000f3000f3000f3000f3000f300204000040000400004000040000400009000010000100001000010000100000b4a0004a0004a0004a0004a0004a0001a2800028000280002800028000280003c0000a0000a0000a0000a0000a0000a7c000280002800028000280002800028d8082000820008200082000820008200f0208002080020800208002080020801600060000600006000060000600006004f0000f0000f0000f0000f0000f000060028000280002800028000280002800e) else (if i < 97 then 0x300003000030000300003000030120400004000040000400004000040001c01000010000100001000010000100030840008400084000840008400084000a2010020100201002010020100201001c00400004000040000400004000040048300003000030000300003000030000a600006000060000600006000060000200000500005000050000500005000053e0009400094000940009400094000946c002000020000200002000020000200b80800008000080000800008000080003 else 0x280002800028000280002800028000400600006000060000600006000060020400004000040000400004000040000910000100001000010000100001000016040000400004000040000400004000349000090000900009000090000900007a0000200002000020000200002000011000020000200002000020000200002230000900009000090000900009000093e0000400004000040000400004000046c00100001000010000100001000010078084000840008400084000840008400b)))) else (if i < 105 then (if i < 101 then (if i < 99 then 0x100001000010000100001000010040024000240002400024000240002401830000300003000030000300003000040010000100001000010000100001000af0c00f0c00f0c00f0c00f0c00f0c00280000800008000080000800008000088c000240002400024000240002400024f8000100001000010000100001000011b0004000040000400004000040000402e0010000100001000010000100001004c000c0000c0000c0000c0000c0000c0480a0000a0000a0000a0000a0000a0003 else (if i < 100 then 0x10000100001000010000100001004000400004000040000400004000040180300003000030000300003000030004220002200022000220002200022000128800088000880008800088000880002c6000060000600006000060000600008000004000040000400004000040000518000100001000010000100001000011f0000400004000040000400004000042e0009000090000900009000090000904c04200042000420004200042000420078100001000010000100001000010000b else 0x3000030000300003000030000300002000800008000080000800008000080048020000200002000020000200002000b60000600006000060000600006000018000010000100001000010000100001460000400004000040000400004000047c001000010000100001000010000100d80042000420004200042000420004217000080000800008000080000800008260200002000020000200002000020001c00c0000c0000c0000c0000c0000c00281000010000100001000010000100003)) else (if i < 103 then (if i < 102 then 0x200002000020000200002000020000440000200002000020000200002000028c000080000800008000080000800008f8000200002000020000200002000021b0000800008000080000800008000082e0208002080020800208002080020803c082000820008200082000820008200580008000080000800008000080000803000200002000020000200002000020041800018000180001800018000180002000400004000040000400004000040050010000100001000010000100001000e else 0xc0000c0000c0000c0000c0000c0000480000200002000020000200002000028c000080000800008000080000800008f8002200022000220002200022000221b0008800088000880008800088000882e0060000600006000060000600006001404040040400404004040040400404018101001010010100101001010010100200c0000c0000c0000c0000c0000c00088800088000880008800088000880005a200022000220002200022000220000d0800008000080000800008000080001e) else (if i < 104 then 0x50000500005000050000500005460001400014000140001400014000147c00100001000010000100001000010078001800018000180001800018000180d000800008000080000800008000080160200002000020000200002000020001c0800008000080000800008000080001802000020000200002000020000200060090000900009000090000900009001420400204002040020400204002040038900009000090000900009000090000904000040000400004000040000400016 else 0x400004000040000400004000040260010000100001000010000100001003c000c0000c0000c0000c0000c0000c068080000800008000080000800008000302400024000240002400024000240004012000120001200012000120001200180080000800008000080000800008005080000800008000080000800008000122400024000240002400024000240002c10000100001000010000100001000069000010000100001000010000100001140000400004000040000400004000026))) else (if i < 109 then (if i < 107 then (if i < 106 then 0x480004800048000480004800048260010000100001000010000100001003c040000400004000040000400004000581008010080100801008010080100807001200012000120001200012000120060040000400004000040000400004000810000100001000010000100001000030400004000040000400004000040000a00c0000c0000c0000c0000c0000c0029e0001e0001e0001e0001e0001e00007000014000140001400014000140001518000500005000050000500005000051f else 0x880008800088000880008800088260222002220022200222002220022201c08880088800888008880088800888018200002000020000200002000020000a0800008000080000800008000080001c01800018000180001800018000180041000010000100001000010000100000d4000040000400004000040000400001e300003000030000300003000030000400000200002000020000200002000029c000080000800008000080000800009180002000020000200002000020000217) else (if i < 108 then 0x10900109001090010900109001090160404004040040400404004040040401c0040000400004000040000400004001021000210002100021000210002100060800008000080000800008000080001400800008000080000800008000080048020000200002000020000200002000b18000180001800018000180001800018c0000c0000c0000c0000c0000c0000400000200002000020000200002000029c000080000800008000080000800009180022000220002200022000220002217 else 0x12000120001200012000120001200060400004000040000400004000040000803000030000300003000030000300060200002000020000200002000020000e08000080000800008000080000800024a0000a0000a0000a0000a0000a00007a8000280002800028000280002800011000008000080000800008000080000a7000020000200002000020000200002460000800008000080000800008000086c000200002000020000200002000020b8002000020000200002000020000200f)) else (if i < 111 then (if i < 110 then 0x840008400084000840008400084001c01000010000100001000010000100048400004000040000400004000040000b1000010000100001000010000100001ac0000c0000c0000c0000c0000c0000480000200002000020000200002000029c00008000080000800008000080000918000200002000020000200002000021b0004800048000480004800048000482e0010000100001000010000100001004c000400004000040000400004000040580090000900009000090000900009007 else 0x8000080000800008000080000800004c0000200002000020000200002000029c00008000080000800008000080000918000200002000020000200002000021f00008000080000800008000080000836000a0000a0000a0000a0000a0000a03c002800028000280002800028000280580800008000080000800008000080007020000200002000020000200002000060020000200002000020000200002000800800008000080000800008000080030200002000020000200002000020000a) else (if i < 112 then 0x80000800008000080000800008360008000080000800008000080000804c00240002400024000240002400024078001000010000100001000010000100b011000110001100011000110001100060440004400044000440004400044000801000010000100001000010000100050240002400024000240002400024000e0800008000080000800008000080002420000200002000020000200002000068800008000080000800008000080000f20000200002000020000200002000022 else 0x200002000020000200002000029c00008000080000800008000080000918000200002000020000200002000021f)))))))

private def planData (i : ℕ) : ℕ := unpack planDataPacked 127 12 i

private def decodeParts (i : ℕ) : ℕ → List ShiftPart
  | 0 => []
  | n+1 => let s := planData i
    ((s >>> 1) &&& 63, s.testBit 0, BitVec.ofNat 120 (s >>> 7)) :: decodeParts (i+1) n

private def plan (p : Fin 120) : List ShiftPart :=
  let d := planDesc p.val
  decodeParts (d >>> 6) (d &&& 63)


private def sigDataPacked (i : ℕ) : ℕ := (if i < 53 then (if i < 26 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then 0x3f0003f0003f0000000000000000003c0003c0003c0000000000000000003300033000330000000000000000003000030000300000000000000000000f0000f0000f0000000000000000000c0000c0000c000000000000000000030000300003000000000000000000000000000000000000000000000 else (if i < 2 then 0x3000030000300000000000000000000ff000ff000ff000000000000000000f3000f3000f3000000000000000000f0000f0000f0000000000000000000cf000cf000cf000000000000000000cc000cc000cc000000000000000000c3000c3000c3000000000000000000c0000c0000c0000000000000000 else 0xc0300c0300c0300000000000000000c0000c0000c00000000000000000003fc003fc003fc000000000000000003c0003c0003c00000000000000000033f0033f0033f000000000000000003330033300333000000000000000003300033000330000000000000000003030030300303000000000000000)) else (if i < 4 then 0xf3f00f3f00f3f00000000000000000f0000f0000f0000000000000000000cf300cf300cf300000000000000000ccc00ccc00ccc00000000000000000c3f00c3f00c3f00000000000000000c3c00c3c00c3c00000000000000000c0f00c0f00c0f00000000000000000c0c00c0c00c0c000000000000000 else (if i < 5 then 0x30cc030cc030cc000000000000000030c3030c3030c3000000000000000030c0030c0030c00000000000000000303003030030300000000000000000300f0300f0300f00000000000000003003030030300300000000000000003000030000300000000000000000000fc000fc000fc0000000000000000 else 0xc3300c3300c3300000000000000000c3030c3030c3030000000000000000c3000c3000c3000000000000000000c0330c0330c0330000000000000000c0030c0030c0030000000000000000c0000c0000c000000000000000000030f0030f0030f0000000000000000030cf030cf030cf000000000000000))) else (if i < 9 then (if i < 7 then 0xf3ff0f3ff0f3ff0000000000000000f3fc0f3fc0f3fc0000000000000000f3c00f3c00f3c00000000000000000f03c0f03c0f03c0000000000000000f0030f0030f0030000000000000000f0000f0000f0000000000000000000cc000cc000cc000000000000000000c3330c3330c333000000000000000 else (if i < 8 then 0x33cc033cc033cc000000000000000033000330003300000000000000000030c0c30c0c30c0c00000000000000030c0030c0030c000000000000000003003c3003c3003c0000000000000003000c3000c3000c000000000000000300033000330003000000000000000300003000030000000000000000000 else 0xc000fc000fc000f000000000000000c0003c0003c0003000000000000000c0000c0000c00000000000000000003ffc03ffc03ffc00000000000000003f0003f0003f0000000000000000003cf0f3cf0f3cf0f0000000000000003cf003cf003cf000000000000000003c0003c0003c000000000000000000)) else (if i < 11 then (if i < 10 then 0xc0c0cc0c0cc0c0c000000000000000c0c00c0c00c0c00000000000000000c03c0c03c0c03c0000000000000000c0300c0300c0300000000000000000c00f0c00f0c00f0000000000000000c00c3c00c3c00c3000000000000000c00c0c00c0c00c0000000000000000c0030c0030c0030000000000000000 else 0xcc000cc000cc000000000000000000c3f0fc3f0fc3f0f000000000000000c3c0cc3c0cc3c0c000000000000000c3303c3303c3303000000000000000c3300c3300c3300000000000000000c30c0c30c0c30c0000000000000000c3000c3000c3000000000000000000c0fc0c0fc0c0fc0000000000000000) else (if i < 12 then 0xf0c0cf0c0cf0c0c000000000000000f0c00f0c00f0c00000000000000000f00ccf00ccf00cc000000000000000f0000f0000f0000000000000000000cf3c0cf3c0cf3c0000000000000000cf000cf000cf000000000000000000ccc30ccc30ccc30000000000000000cc330cc330cc330000000000000000 else 0x3f0003f0003f0208a0208a0208a0000f0000f0000f0208a0208a0208affc00ffc00ffc00000000000000000ff000ff000ff000000000000000000fc000fc000fc000000000000000000f3000f3000f3000000000000000000f0f30f0f30f0f30000000000000000f0cccf0cccf0ccc000000000000000)))) else (if i < 19 then (if i < 16 then (if i < 14 then 0x300003000030000208a0208a0208a003ff003ff003ff0208a0208a0208a000ff000ff000ff0208a0208a0208a000f3000f3000f30208a0208a0208a000cf000cf000cf0208a0208a0208a000cc000cc000cc0208a0208a0208a000c3000c3000c30208a0208a0208a000c0000c0000c00208a0208a0208a else (if i < 15 then 0x30cf030cf030cf0208a0208a0208a030cc030cc030cc0208a0208a0208a030c3030c3030c30208a0208a0208a030c0030c0030c00208a0208a0208a0303f0303f0303f0208a0208a0208a0300f0300f0300f0208a0208a0208a0300c0300c0300c0208a0208a0208a0300303003030030208a0208a0208a else 0x33f3033f3033f30208a0208a0208a033cf033cf033cf0208a0208a0208a033cc033cc033cc0208a0208a0208a0333f0333f0333f0208a0208a0208a030ff030ff030ff0208a0208a0208a030fc030fc030fc0208a0208a0208a030f3030f3030f30208a0208a0208a030f0030f0030f00208a0208a0208a)) else (if i < 17 then 0x3fff03fff03fff0208a0208a0208a03fcf03fcf03fcf0208a0208a0208a03cff03cff03cff0208a0208a0208a03ccf03ccf03ccf0208a0208a0208a03ccc03ccc03ccc0208a0208a0208a03c0f03c0f03c0f0208a0208a0208a033ff033ff033ff0208a0208a0208a033fc033fc033fc0208a0208a0208a else (if i < 18 then 0xf0ff0f0ff0f0ff0208a0208a0208a0f0cf0f0cf0f0cf0208a0208a0208a0f0cc0f0cc0f0cc0208a0208a0208a0f00f0f00f0f00f0208a0208a0208a0c0ff0c0ff0c0ff0208a0208a0208a0c0cf0c0cf0c0cf0208a0208a0208a0c0cc0c0cc0c0cc0208a0208a0208a0c00f0c00f0c00f0208a0208a0208a else 0x33cff33cff33cff0208a0208a0208a33ccf33ccf33ccf0208a0208a0208a330cf330cf330cf0208a0208a0208a0ffff0ffff0ffff0208a0208a0208a0fcff0fcff0fcff0208a0208a0208a0fccf0fccf0fccf0208a0208a0208a0f3ff0f3ff0f3ff0208a0208a0208a0f3cf0f3cf0f3cf0208a0208a0208a))) else (if i < 22 then (if i < 20 then 0xc03ccc03ccc03cc0208a0208a0208ac030fc030fc030f0208a0208a0208ac00cfc00cfc00cf0208a0208a0208ac000fc000fc000f0208a0208a0208a3ffcf3ffcf3ffcf0208a0208a0208a3f3cf3f3cf3f3cf0208a0208a0208a3f0ff3f0ff3f0ff0208a0208a0208a3c0cf3c0cf3c0cf0208a0208a0208a else (if i < 21 then 0xc3ccfc3ccfc3ccf0208a0208a0208ac33cfc33cfc33cf0208a0208a0208ac33c3c33c3c33c30208a0208a0208ac30ffc30ffc30ff0208a0208a0208ac30cfc30cfc30cf0208a0208a0208ac30ccc30ccc30cc0208a0208a0208ac30c3c30c3c30c30208a0208a0208ac300fc300fc300f0208a0208a0208a else 0xff0cfff0cfff0cf0208a0208a0208af3ffff3ffff3fff0208a0208a0208af3ccff3ccff3ccf0208a0208a0208af30cff30cff30cf0208a0208a0208acfcffcfcffcfcff0208a0208a0208acf3cfcf3cfcf3cf0208a0208a0208ac3fffc3fffc3fff0208a0208a0208ac3fcfc3fcfc3fcf0208a0208a0208a)) else (if i < 24 then (if i < 23 then 0x3333033330333308221082210822100f3300f3300f330822108221082210033f0033f0033f082210822108221003330033300333082210822108221003300033000330082210822108221003030030300303082210822108221000330003300033082210822108221000030000300003082210822108221 else 0xc30f0c30f0c30f0822108221082210c30c0c30c0c30c0822108221082210c3030c3030c3030822108221082210c3000c3000c3000822108221082210c0330c0330c0330822108221082210c0300c0300c0300822108221082210c0030c0030c0030822108221082210c0000c0000c000082210822108221) else (if i < 25 then 0xcc030cc030cc030822108221082210c3ff0c3ff0c3ff0822108221082210c3f30c3f30c3f30822108221082210c3f00c3f00c3f00822108221082210c33f0c33f0c33f0822108221082210c33c0c33c0c33c0822108221082210c3330c3330c3330822108221082210c3300c3300c330082210822108221 else 0xf3330f3330f3330822108221082210f3300f3300f3300822108221082210cfff0cfff0cfff0822108221082210cff30cff30cff30822108221082210cf3f0cf3f0cf3f0822108221082210cf330cf330cf330822108221082210cf300cf300cf300822108221082210cc330cc330cc33082210822108221))))) else (if i < 39 then (if i < 32 then (if i < 29 then (if i < 27 then 0xcc303cc303cc303082210822108221c0333c0333c03330822108221082213fff33fff33fff30822108221082213cf3f3cf3f3cf3f0822108221082213cf333cf333cf330822108221082213c3333c3333c3330822108221082210f3ff0f3ff0f3ff0822108221082210f3f30f3f30f3f3082210822108221 else (if i < 28 then 0xcff3fcff3fcff3f082210822108221cf3f3cf3f3cf3f3082210822108221cf333cf333cf333082210822108221ccf33ccf33ccf33082210822108221cc3f3cc3f3cc3f3082210822108221cc33fcc33fcc33f082210822108221cc333cc333cc333082210822108221cc330cc330cc330082210822108221 else 0x3c0003c0003c0a2ab0a2ab0a2ab0000300003000030a2ab0a2ab0a2abffff3ffff3ffff3082210822108221ff333ff333ff333082210822108221fcf3ffcf3ffcf3f082210822108221fcf33fcf33fcf33082210822108221fc3fffc3fffc3ff082210822108221fc333fc333fc333082210822108221)) else (if i < 30 then 0x30ff030ff030ff0a2ab0a2ab0a2ab030fc030fc030fc0a2ab0a2ab0a2ab0303f0303f0303f0a2ab0a2ab0a2ab00fff00fff00fff0a2ab0a2ab0a2ab003ff003ff003ff0a2ab0a2ab0a2ab003fc003fc003fc0a2ab0a2ab0a2ab003c3003c3003c30a2ab0a2ab0a2ab0003f0003f0003f0a2ab0a2ab0a2ab else (if i < 31 then 0xc33f0c33f0c33f0a2ab0a2ab0a2ab03fff03fff03fff0a2ab0a2ab0a2ab033ff033ff033ff0a2ab0a2ab0a2ab033fc033fc033fc0a2ab0a2ab0a2ab033f3033f3033f30a2ab0a2ab0a2ab033c3033c3033c30a2ab0a2ab0a2ab0333f0333f0333f0a2ab0a2ab0a2ab0333c0333c0333c0a2ab0a2ab0a2ab else 0xf03f0f03f0f03f0a2ab0a2ab0a2ab0f03c0f03c0f03c0a2ab0a2ab0a2ab0f00f0f00f0f00f0a2ab0a2ab0a2ab0f0030f0030f0030a2ab0a2ab0a2ab0c3ff0c3ff0c3ff0a2ab0a2ab0a2ab0c3fc0c3fc0c3fc0a2ab0a2ab0a2ab0c3f30c3f30c3f30a2ab0a2ab0a2ab0c3c30c3c30c3c30a2ab0a2ab0a2ab))) else (if i < 35 then (if i < 33 then 0xf33f0f33f0f33f0a2ab0a2ab0a2ab0f33c0f33c0f33c0a2ab0a2ab0a2ab0f30c0f30c0f30c0a2ab0a2ab0a2ab0f0ff0f0ff0f0ff0a2ab0a2ab0a2ab0f0fc0f0fc0f0fc0a2ab0a2ab0a2ab0f0f00f0f00f0f00a2ab0a2ab0a2ab0f0cf0f0cf0f0cf0a2ab0a2ab0a2ab0f0cc0f0cc0f0cc0a2ab0a2ab0a2ab else (if i < 34 then 0xf3ff0f3ff0f3ff0a2ab0a2ab0a2ab0f3fc0f3fc0f3fc0a2ab0a2ab0a2ab0f3f30f3f30f3f30a2ab0a2ab0a2ab0f3f00f3f00f3f00a2ab0a2ab0a2ab0f3cf0f3cf0f3cf0a2ab0a2ab0a2ab0f3cc0f3cc0f3cc0a2ab0a2ab0a2ab0f3c30f3c30f3c30a2ab0a2ab0a2ab0f3c00f3c00f3c00a2ab0a2ab0a2ab else 0x3f3ff3f3ff3f3ff0a2ab0a2ab0a2ab333ff333ff333ff0a2ab0a2ab0a2ab303ff303ff303ff0a2ab0a2ab0a2ab0ffff0ffff0ffff0a2ab0a2ab0a2ab0fffc0fffc0fffc0a2ab0a2ab0a2ab0fcff0fcff0fcff0a2ab0a2ab0a2ab0fc3f0fc3f0fc3f0a2ab0a2ab0a2ab0fc030fc030fc030a2ab0a2ab0a2ab)) else (if i < 37 then (if i < 36 then 0xfc000fc000fc2081420814208140003c0003c0003c208142081420814000300003000030208142081420814f03fff03fff03ff0a2ab0a2ab0a2abcffffcffffcffff0a2ab0a2ab0a2abcf3ffcf3ffcf3ff0a2ab0a2ab0a2abcf3fccf3fccf3fc0a2ab0a2ab0a2ab3ffff3ffff3ffff0a2ab0a2ab0a2ab else 0x3000c3000c3000c20814208142081430000300003000020814208142081403c3c03c3c03c3c20814208142081400c3f00c3f00c3f20814208142081400c3c00c3c00c3c20814208142081400c0c00c0c00c0c20814208142081400c0300c0300c0320814208142081400c0000c0000c00208142081420814) else (if i < 38 then 0x30c3330c3330c3320814208142081430c3030c3030c3020814208142081430c0f30c0f30c0f20814208142081430c0c30c0c30c0c20814208142081430c0330c0330c0320814208142081430c0030c0030c002081420814208143003c3003c3003c208142081420814300303003030030208142081420814 else 0x30ffc30ffc30ffc20814208142081430f3f30f3f30f3f20814208142081430f3c30f3c30f3c20814208142081430cff30cff30cff20814208142081430cfc30cfc30cfc20814208142081430ccc30ccc30ccc20814208142081430c3f30c3f30c3f20814208142081430c3c30c3c30c3c208142081420814)))) else (if i < 46 then (if i < 42 then (if i < 40 then 0x3cc3f3cc3f3cc3f2081420814208143cc3c3cc3c3cc3c20814208142081433f3f33f3f33f3f20814208142081433cff33cff33cff20814208142081433cfc33cfc33cfc20814208142081433c3f33c3f33c3f20814208142081433c3c33c3c33c3c20814208142081430fff30fff30fff208142081420814 else (if i < 41 then 0xf0c0cf0c0cf0c0c208142081420814c0c3cc0c3cc0c3c208142081420814c003cc003cc003c2081420814208143fffc3fffc3fffc2081420814208143fc3f3fc3f3fc3f2081420814208143fc3c3fc3c3fc3c2081420814208143cf3f3cf3f3cf3f2081420814208143cf3c3cf3c3cf3c208142081420814 else 0xf3cfcf3cfcf3cfc208142081420814f3c3cf3c3cf3c3c208142081420814f0ffcf0ffcf0ffc208142081420814f0f3cf0f3cf0f3c208142081420814f0cfff0cfff0cff208142081420814f0cfcf0cfcf0cfc208142081420814f0c3ff0c3ff0c3f208142081420814f0c3cf0c3cf0c3c208142081420814)) else (if i < 44 then (if i < 43 then 0xccf00ccf00ccf2289e2289e2289e00c3f00c3f00c3f2289e2289e2289e0003f0003f0003f2289e2289e2289efcffcfcffcfcffc208142081420814fccfffccfffccff208142081420814fcc3cfcc3cfcc3c208142081420814f3f3ff3f3ff3f3f208142081420814f3cfff3cfff3cff208142081420814 else 0x33ccc33ccc33ccc2289e2289e2289e33cc033cc033cc02289e2289e2289e33c3f33c3f33c3f2289e2289e2289e330ff330ff330ff2289e2289e2289e30cff30cff30cff2289e2289e2289e30cfc30cfc30cfc2289e2289e2289e03cff03cff03cff2289e2289e2289e00cff00cff00cff2289e2289e2289e) else (if i < 45 then 0xf0000f0000f28a3528a3528a35f3cfff3cfff3cff2289e2289e2289e33fff33fff33fff2289e2289e2289e33cff33cff33cff2289e2289e2289e33cfc33cfc33cfc2289e2289e2289e33cf333cf333cf32289e2289e2289e33cf033cf033cf02289e2289e2289e33ccf33ccf33ccf2289e2289e2289e else 0x30c3f30c3f30c3f28a3528a3528a353030f3030f3030f28a3528a3528a350cf3f0cf3f0cf3f28a3528a3528a350cf0f0cf0f0cf0f28a3528a3528a350c33f0c33f0c33f28a3528a3528a3500f3f00f3f00f3f28a3528a3528a3500f0f00f0f00f0f28a3528a3528a350003f0003f0003f28a3528a3528a35))) else (if i < 49 then (if i < 47 then 0x3cc3f3cc3f3cc3f28a3528a3528a353cc3c3cc3c3cc3c28a3528a3528a353cc0f3cc0f3cc0f28a3528a3528a353cc003cc003cc0028a3528a3528a353c33f3c33f3c33f28a3528a3528a353c03f3c03f3c03f28a3528a3528a353c0303c0303c03028a3528a3528a3530f3f30f3f30f3f28a3528a3528a35 else (if i < 48 then 0x3cf3f3cf3f3cf3f28a3528a3528a353cf3c3cf3c3cf3c28a3528a3528a353cf333cf333cf3328a3528a3528a353cf303cf303cf3028a3528a3528a353cf0f3cf0f3cf0f28a3528a3528a353cf0c3cf0c3cf0c28a3528a3528a353cf033cf033cf0328a3528a3528a353cf003cf003cf0028a3528a3528a35 else 0xfcffffcffffcfff28a3528a3528a35fcf3ffcf3ffcf3f28a3528a3528a35fcf0ffcf0ffcf0f28a3528a3528a353ffff3ffff3ffff28a3528a3528a353ff0f3ff0f3ff0f28a3528a3528a353cffc3cffc3cffc28a3528a3528a353cff33cff33cff328a3528a3528a353cff03cff03cff028a3528a3528a35)) else (if i < 51 then (if i < 50 then 0xfcff0fcff0fcff2aabf2aabf2aabf0f3ff0f3ff0f3ff2aabf2aabf2aabf03fff03fff03fff2aabf2aabf2aabf030ff030ff030ff2aabf2aabf2aabf00fff00fff00fff2aabf2aabf2aabf00ffc00ffc00ffc2aabf2aabf2aabf003ff003ff003ff2aabf2aabf2aabf0003f0003f0003f2aabf2aabf2aabf else 0x3fff03fff03fff02aabf2aabf2aabf3ffcf3ffcf3ffcf2aabf2aabf2aabf3ffc33ffc33ffc32aabf2aabf2aabf3ffc03ffc03ffc02aabf2aabf2aabf3f0ff3f0ff3f0ff2aabf2aabf2aabf3cfff3cfff3cfff2aabf2aabf2aabf30fff30fff30fff2aabf2aabf2aabf0ffff0ffff0ffff2aabf2aabf2aabf) else (if i < 52 then 0xc0000c0000c00805408054080540003c0003c0003c0805408054080540000c0000c0000c0805408054080540ff03fff03fff03f2aabf2aabf2aabfc003fc003fc003f2aabf2aabf2aabf3ffff3ffff3ffff2aabf2aabf2aabf3fffc3fffc3fffc2aabf2aabf2aabf3fff33fff33fff32aabf2aabf2aabf else 0x3ffc03ffc03ffc080540805408054030fc030fc030fc08054080540805400ffc00ffc00ffc080540805408054003fc003fc003fc080540805408054000fc300fc300fc380540805408054000fc000fc000fc080540805408054000f0000f0000f0080540805408054000cc000cc000cc0805408054080540)))))) else (if i < 80 then (if i < 66 then (if i < 59 then (if i < 56 then (if i < 54 then 0xc0c00c0c00c0c00805408054080540c03f0c03f0c03f0805408054080540c03ccc03ccc03cc805408054080540c03c3c03c3c03c3805408054080540c03c0c03c0c03c0805408054080540c0300c0300c0300805408054080540c00f0c00f0c00f0805408054080540c00c0c00c0c00c0805408054080540 else (if i < 55 then 0xc0ff3c0ff3c0ff3805408054080540c0ff0c0ff0c0ff0805408054080540c0fcfc0fcfc0fcf805408054080540c0fccc0fccc0fcc805408054080540c0fc3c0fc3c0fc3805408054080540c0fc0c0fc0c0fc0805408054080540c0f00c0f00c0f00805408054080540c0cc0c0cc0c0cc0805408054080540 else 0xc3fcfc3fcfc3fcf805408054080540c3fccc3fccc3fcc805408054080540c3fc3c3fc3c3fc3805408054080540c3fc0c3fc0c3fc0805408054080540c3f00c3f00c3f00805408054080540c33c0c33c0c33c0805408054080540c0fffc0fffc0fff805408054080540c0ffcc0ffcc0ffc805408054080540)) else (if i < 57 then 0xf03c0f03c0f03c0805408054080540cffc3cffc3cffc3805408054080540cffc0cffc0cffc0805408054080540ccff3ccff3ccff3805408054080540ccfc3ccfc3ccfc3805408054080540ccfc0ccfc0ccfc0805408054080540c3ff3c3ff3c3ff3805408054080540c3ff0c3ff0c3ff0805408054080540 else (if i < 58 then 0x3cf003cf003cf825ca825ca825cafffc0fffc0fffc0805408054080540fcff0fcff0fcff0805408054080540fcfcffcfcffcfcf805408054080540fcfc0fcfc0fcfc0805408054080540f0ff0f0ff0f0ff0805408054080540f0fccf0fccf0fcc805408054080540f0fc0f0fc0f0fc0805408054080540 else 0xc0fcfc0fcfc0fcf825ca825ca825cac0f0fc0f0fc0f0f825ca825ca825ca03fcf03fcf03fcf825ca825ca825ca03f0f03f0f03f0f825ca825ca825ca03ccf03ccf03ccf825ca825ca825ca033cf033cf033cf825ca825ca825ca00fcf00fcf00fcf825ca825ca825ca00fc300fc300fc3825ca825ca825ca))) else (if i < 62 then (if i < 60 then 0xc3fcfc3fcfc3fcf825ca825ca825cac3fccc3fccc3fcc825ca825ca825cac3fc3c3fc3c3fc3825ca825ca825cac3f0fc3f0fc3f0f825ca825ca825cac3ccfc3ccfc3ccf825ca825ca825cac3cccc3cccc3ccc825ca825ca825cac33cfc33cfc33cf825ca825ca825cac33c3c33c3c33c3825ca825ca825ca else (if i < 61 then 0xcc3c3cc3c3cc3c3887618876188761c0ff3c0ff3c0ff3887618876188761c0ff0c0ff0c0ff08876188761887610cff30cff30cff388761887618876100ff300ff300ff3887618876188761003c3003c3003c3887618876188761cffcfcffcfcffcf825ca825ca825cac3fffc3fffc3fff825ca825ca825ca else 0xcf3c3cf3c3cf3c38a7eb8a7eb8a7ebc0ffcc0ffcc0ffc8a7eb8a7eb8a7eb00fff00fff00fff8a7eb8a7eb8a7ebcfff3cfff3cfff3887618876188761ccff3ccff3ccff3887618876188761ccfc3ccfc3ccfc3887618876188761ccf30ccf30ccf30887618876188761cccf3cccf3cccf3887618876188761)) else (if i < 64 then (if i < 63 then 0xfcc00fcc00fcca0d54a0d54a0d5400cfc00cfc00cfca0d54a0d54a0d5400ccc00ccc00ccca0d54a0d54a0d54003fc003fc003fca0d54a0d54a0d54003300033000330a0d54a0d54a0d54cffffcffffcffff8a7eb8a7eb8a7ebcfffccfffccfffc8a7eb8a7eb8a7ebcfc3fcfc3fcfc3f8a7eb8a7eb8a7eb else 0xf003cf003cf003ca0d54a0d54a0d54c0ffcc0ffcc0ffca0d54a0d54a0d54c0cccc0cccc0ccca0d54a0d54a0d5430fff30fff30fffa0d54a0d54a0d5430ffc30ffc30ffca0d54a0d54a0d5430cfc30cfc30cfca0d54a0d54a0d5400fff00fff00fffa0d54a0d54a0d5400ffc00ffc00ffca0d54a0d54a0d54) else (if i < 65 then 0xf0c3cf0c3cf0c3ca0d54a0d54a0d54f0c00f0c00f0c00a0d54a0d54a0d54f03fff03fff03ffa0d54a0d54a0d54f03fcf03fcf03fca0d54a0d54a0d54f03ccf03ccf03cca0d54a0d54a0d54f00fcf00fcf00fca0d54a0d54a0d54f00f0f00f0f00f0a0d54a0d54a0d54f00ccf00ccf00cca0d54a0d54a0d54 else 0xf0fc0f0fc0f0fc0a0d54a0d54a0d54f0f3cf0f3cf0f3ca0d54a0d54a0d54f0f30f0f30f0f30a0d54a0d54a0d54f0cfff0cfff0cffa0d54a0d54a0d54f0cfcf0cfcf0cfca0d54a0d54a0d54f0ccff0ccff0ccfa0d54a0d54a0d54f0cccf0cccf0ccca0d54a0d54a0d54f0c3ff0c3ff0c3fa0d54a0d54a0d54)))) else (if i < 73 then (if i < 69 then (if i < 67 then 0xf3f33f3f33f3f33a2ddea2ddea2ddef33fff33fff33ffa2ddea2ddea2ddef0ffff0ffff0fffa2ddea2ddea2ddefcffcfcffcfcffca0d54a0d54a0d54f3ffcf3ffcf3ffca0d54a0d54a0d54f0ffff0ffff0fffa0d54a0d54a0d54f0ffcf0ffcf0ffca0d54a0d54a0d54f0fccf0fccf0fcca0d54a0d54a0d54 else (if i < 68 then 0xf0ffff0ffff0fffa8f75a8f75a8f75ccfffccfffccfffa8f75a8f75a8f75c0fffc0fffc0fffa8f75a8f75a8f7530fff30fff30fffa8f75a8f75a8f750cfff0cfff0cfffa8f75a8f75a8f7500fff00fff00fffa8f75a8f75a8f75f3ffff3ffff3fffa2ddea2ddea2ddef3ffcf3ffcf3ffca2ddea2ddea2dde else 0xffc00ffc00ffcaafffaafffaaffffcffffcffffcfffa8f75a8f75a8f75fcff3fcff3fcff3a8f75a8f75a8f75fcf30fcf30fcf30a8f75a8f75a8f75fcccffcccffcccfa8f75a8f75a8f75fc3fffc3fffc3ffa8f75a8f75a8f75fc0fffc0fffc0ffa8f75a8f75a8f75fc0cffc0cffc0cfa8f75a8f75a8f75)) else (if i < 71 then (if i < 70 then 0xf0cc0f0cc0f0cc5500055000550000f0c00f0c00f0c05500055000550000f0030f0030f0035500055000550000f0000f0000f000550005500055000000000000000000550005500055000fffffffffffffffaafffaafffaafffc0fffc0fffc0fffaafffaafffaafff00fff00fff00fffaafffaafffaafff else 0x3f00f3f00f3f00f5500055000550003f0033f0033f0035500055000550003f0003f0003f0005500055000550003c0003c0003c00055000550005500033c0033c0033c005500055000550003300033000330005500055000550003000030000300005500055000550000fc000fc000fc00550005500055000) else (if i < 72 then 0x3fcc03fcc03fcc05500055000550003fc0c3fc0c3fc0c5500055000550003fc003fc003fc005500055000550003f3c03f3c03f3c05500055000550003f3003f3003f3005500055000550003f0c33f0c33f0c35500055000550003f0c03f0c03f0c05500055000550003f0303f0303f030550005500055000 else 0xf0000f0000f0000550005500055000cfc00cfc00cfc00550005500055000cf300cf300cf300550005500055000cf003cf003cf003550005500055000cf000cf000cf000550005500055000c3000c3000c3000550005500055000c0000c0000c00005500055000550003ff003ff003ff00550005500055000))) else (if i < 76 then (if i < 74 then 0xf3c00f3c00f3c00550005500055000f3030f3030f3030550005500055000f300cf300cf300c550005500055000f3003f3003f3003550005500055000f3000f3000f3000550005500055000f0c00f0c00f0c00550005500055000f000ff000ff000f550005500055000f0003f0003f0003550005500055000 else (if i < 75 then 0xff000ff000ff000550005500055000fcc00fcc00fcc00550005500055000fc0c0fc0c0fc0c0550005500055000fc030fc030fc030550005500055000fc00ffc00ffc00f550005500055000fc000fc000fc000550005500055000f3c30f3c30f3c30550005500055000f3c0cf3c0cf3c0c550005500055000 else 0xff0c0ff0c0ff0c0550005500055000ff03fff03fff03f550005500055000ff03cff03cff03c550005500055000ff033ff033ff033550005500055000ff030ff030ff030550005500055000ff00fff00fff00f550005500055000ff00cff00cff00c550005500055000ff003ff003ff003550005500055000)) else (if i < 78 then (if i < 77 then 0xff330ff330ff330550005500055000ff303ff303ff303550005500055000ff300ff300ff300550005500055000ff0ffff0ffff0ff550005500055000ff0f0ff0f0ff0f0550005500055000ff0cfff0cfff0cf550005500055000ff0ccff0ccff0cc550005500055000ff0c3ff0c3ff0c3550005500055000 else 0xffc0fffc0fffc0f550005500055000ffc0cffc0cffc0c550005500055000ffc03ffc03ffc03550005500055000ffc00ffc00ffc00550005500055000ff3ffff3ffff3ff550005500055000ff3fcff3fcff3fc550005500055000ff3c3ff3c3ff3c3550005500055000ff3c0ff3c0ff3c0550005500055000) else (if i < 79 then 0xfff30fff30fff30550005500055000fff0ffff0ffff0f550005500055000fff00fff00fff00550005500055000ffcf3ffcf3ffcf3550005500055000ffcccffcccffccc550005500055000ffcc0ffcc0ffcc0550005500055000ffc3cffc3cffc3c550005500055000ffc30ffc30ffc30550005500055000 else 0x3c00f3c00f3c00f5708a5708a5708a330cf330cf330cf5708a5708a5708a0f0cf0f0cf0f0cf5708a5708a5708a0f0030f0030f0035708a5708a5708a0c0cf0c0cf0c0cf5708a5708a5708a030cf030cf030cf5708a5708a5708a0300303003030035708a5708a5708afffc0fffc0fffc0550005500055000))))) else (if i < 93 then (if i < 86 then (if i < 83 then (if i < 81 then 0xcf00fcf00fcf00f5708a5708a5708acf003cf003cf0035708a5708a5708ac30cfc30cfc30cf5708a5708a5708a3f0ff3f0ff3f0ff5708a5708a5708a3f0cf3f0cf3f0cf5708a5708a5708a3f03f3f03f3f03f5708a5708a5708a3f00f3f00f3f00f5708a5708a5708a3c0cf3c0cf3c0cf5708a5708a5708a else (if i < 82 then 0xfc0ccfc0ccfc0cc5708a5708a5708afc00ffc00ffc00f5708a5708a5708af30fcf30fcf30fc5708a5708a5708af30cff30cff30cf5708a5708a5708af30ccf30ccf30cc5708a5708a5708af00cff00cff00cf5708a5708a5708acf0cfcf0cfcf0cf5708a5708a5708acf0c3cf0c3cf0c35708a5708a5708a else 0xff0cfff0cfff0cf5708a5708a5708aff0ccff0ccff0cc5708a5708a5708aff0c3ff0c3ff0c35708a5708a5708aff03fff03fff03f5708a5708a5708aff00fff00fff00f5708a5708a5708aff003ff003ff0035708a5708a5708afc0fffc0fffc0ff5708a5708a5708afc0cffc0cffc0cf5708a5708a5708a)) else (if i < 84 then 0x3f3303f3303f3305d2215d2215d2213f0333f0333f0335d2215d2215d2213c3333c3333c3335d2215d2215d2210f3330f3330f3335d2215d2215d221ffccfffccfffccf5708a5708a5708aff3cfff3cfff3cf5708a5708a5708aff0ffff0ffff0ff5708a5708a5708aff0f3ff0f3ff0f35708a5708a5708a else (if i < 85 then 0xf3f33f3f33f3f335d2215d2215d221f3333f3333f33335d2215d2215d221f3330f3330f33305d2215d2215d221f0333f0333f03335d2215d2215d221f0330f0330f03305d2215d2215d221cf333cf333cf3335d2215d2215d221cf303cf303cf3035d2215d2215d2213f3333f3333f3335d2215d2215d221 else 0xff3f3ff3f3ff3f35d2215d2215d221ff333ff333ff3335d2215d2215d221ff330ff330ff3305d2215d2215d221ff303ff303ff3035d2215d2215d221ff033ff033ff0335d2215d2215d221ff030ff030ff0305d2215d2215d221fc333fc333fc3335d2215d2215d221fc330fc330fc3305d2215d2215d221))) else (if i < 89 then (if i < 87 then 0xf33fff33fff33ff5f2ab5f2ab5f2abf33fcf33fcf33fc5f2ab5f2ab5f2abf03fff03fff03ff5f2ab5f2ab5f2abf003ff003ff003f5f2ab5f2ab5f2abcf3f3cf3f3cf3f35f2ab5f2ab5f2ab3f3fc3f3fc3f3fc5f2ab5f2ab5f2ab3f03f3f03f3f03f5f2ab5f2ab5f2abfff33fff33fff335d2215d2215d221 else (if i < 88 then 0x3f03c3f03c3f03c7581475814758143f00c3f00c3f00c7581475814758143300c3300c3300c758147581475814fffffffffffffff5f2ab5f2ab5f2abff3ffff3ffff3ff5f2ab5f2ab5f2abff3fcff3fcff3fc5f2ab5f2ab5f2abff03fff03fff03f5f2ab5f2ab5f2abff03cff03cff03c5f2ab5f2ab5f2ab else 0xf0c3cf0c3cf0c3c758147581475814cfc3fcfc3fcfc3f758147581475814cfc3ccfc3ccfc3c758147581475814cfc0ccfc0ccfc0c758147581475814cf03ccf03ccf03c7581475814758143fc3f3fc3f3fc3f7581475814758143fc3c3fc3c3fc3c7581475814758143f03f3f03f3f03f758147581475814)) else (if i < 91 then (if i < 90 then 0xff03fff03fff03f758147581475814ff03cff03cff03c758147581475814ff00cff00cff00c758147581475814fcc3cfcc3cfcc3c758147581475814fcc30fcc30fcc30758147581475814fcc00fcc00fcc00758147581475814f3c3cf3c3cf3c3c758147581475814f3c0cf3c0cf3c0c758147581475814 else 0xffc3fffc3fffc3f758147581475814ffc3cffc3cffc3c758147581475814ffc30ffc30ffc30758147581475814ffc0fffc0fffc0f758147581475814ffc0cffc0cffc0c758147581475814ffc03ffc03ffc03758147581475814ffc00ffc00ffc00758147581475814ff0fcff0fcff0fc758147581475814) else (if i < 92 then 0xfcf3ffcf3ffcf3f7da357da357da35cff0fcff0fcff0f7da357da357da35c3f3fc3f3fc3f3f7da357da357da353ff3f3ff3f3ff3f7da357da357da353f03f3f03f3f03f7da357da357da35ffcffffcffffcff7789e7789e7789e3f03f3f03f3f03f7789e7789e7789effcfcffcfcffcfc758147581475814 else 0x333c0333c0333c0d5540d5540d55400ffc00ffc00ffc0d5540d5540d55400f3c00f3c00f3c0d5540d5540d5540033c0033c0033c0d5540d5540d5540fffffffffffffff7fabf7fabf7fabffff3ffff3ffff3f7da357da357da35ff33fff33fff33f7da357da357da35ff03fff03fff03f7da357da357da35)))) else (if i < 100 then (if i < 96 then (if i < 94 then 0x3ffc33ffc33ffc3d5540d5540d55403ffc03ffc03ffc0d5540d5540d55403ff003ff003ff00d5540d5540d55403f3c03f3c03f3c0d5540d5540d55403f0c03f0c03f0c0d5540d5540d55403cfc03cfc03cfc0d5540d5540d554033fc033fc033fc0d5540d5540d554033cc033cc033cc0d5540d5540d5540 else (if i < 95 then 0xc3cc0c3cc0c3cc0d5540d5540d5540c33c0c33c0c33c0d5540d5540d5540c3300c3300c3300d5540d5540d5540c30c0c30c0c30c0d5540d5540d5540c03c0c03c0c03c0d5540d5540d55403fff03fff03fff0d5540d5540d55403ffcf3ffcf3ffcfd5540d5540d55403ffcc3ffcc3ffccd5540d5540d5540 else 0xcfcc0cfcc0cfcc0d5540d5540d5540cf3c0cf3c0cf3c0d5540d5540d5540cf300cf300cf300d5540d5540d5540cf0c0cf0c0cf0c0d5540d5540d5540ccfc0ccfc0ccfc0d5540d5540d5540ccf00ccf00ccf00d5540d5540d5540c3fc0c3fc0c3fc0d5540d5540d5540c3f00c3f00c3f00d5540d5540d5540)) else (if i < 98 then (if i < 97 then 0xf3c00f3c00f3c00d5540d5540d5540f33c0f33c0f33c0d5540d5540d5540f30c0f30c0f30c0d5540d5540d5540f0fc0f0fc0f0fc0d5540d5540d5540f0cc0f0cc0f0cc0d5540d5540d5540f0c00f0c00f0c00d5540d5540d5540cffcccffcccffccd5540d5540d5540cffc0cffc0cffc0d5540d5540d5540 else 0xffc00ffc00ffc00d5540d5540d5540ff3c0ff3c0ff3c0d5540d5540d5540ff0c0ff0c0ff0c0d5540d5540d5540fcfc0fcfc0fcfc0d5540d5540d5540fcf00fcf00fcf00d5540d5540d5540f3fc0f3fc0f3fc0d5540d5540d5540f3f00f3f00f3f00d5540d5540d5540f3cc0f3cc0f3cc0d5540d5540d5540) else (if i < 99 then 0xffff3ffff3ffff3d5540d5540d5540ffff0ffff0ffff0d5540d5540d5540fffcffffcffffcfd5540d5540d5540fffccfffccfffccd5540d5540d5540fffc3fffc3fffc3d5540d5540d5540fffc0fffc0fffc0d5540d5540d5540fff00fff00fff00d5540d5540d5540ffcc0ffcc0ffcc0d5540d5540d5540 else 0xcffcfcffcfcffcfd75cad75cad75cacf3cfcf3cfcf3cfd75cad75cad75cacf3c3cf3c3cf3c3d75cad75cad75caccf0fccf0fccf0fd75cad75cad75ca3ffcf3ffcf3ffcfd75cad75cad75ca3ff0f3ff0f3ff0fd75cad75cad75ca3cfcf3cfcf3cfcfd75cad75cad75ca3cf0f3cf0f3cf0fd75cad75cad75ca))) else (if i < 103 then (if i < 101 then 0xfcf30fcf30fcf30dd761dd761dd761cf3f3cf3f3cf3f3dd761dd761dd7613cf303cf303cf30dd761dd761dd761fffffffffffffffd75cad75cad75cafffcffffcffffcfd75cad75cad75cafffc3fffc3fffc3d75cad75cad75cafcf0ffcf0ffcf0fd75cad75cad75caf3cccf3cccf3cccd75cad75cad75ca else (if i < 102 then 0xfffc0fffc0fffcf5d54f5d54f5d540f3fc0f3fc0f3fcf5d54f5d54f5d54fffffffffffffffdf7ebdf7ebdf7ebcf3c3cf3c3cf3c3df7ebdf7ebdf7eb3ffff3ffff3ffffdf7ebdf7ebdf7ebffff3ffff3ffff3dd761dd761dd761fcff0fcff0fcff0dd761dd761dd761fcf33fcf33fcf33dd761dd761dd761 else 0xf33fcf33fcf33fcf5d54f5d54f5d54f0cfcf0cfcf0cfcf5d54f5d54f5d54f0c0cf0c0cf0c0cf5d54f5d54f5d54f0c00f0c00f0c00f5d54f5d54f5d54cfffccfffccfffcf5d54f5d54f5d54cf3fccf3fccf3fcf5d54f5d54f5d543fffc3fffc3fffcf5d54f5d54f5d543f3fc3f3fc3f3fcf5d54f5d54f5d54)) else (if i < 105 then (if i < 104 then 0xfcffcfcffcfcffcf5d54f5d54f5d54fcf3cfcf3cfcf3cf5d54f5d54f5d54fcf30fcf30fcf30f5d54f5d54f5d54f3ffcf3ffcf3ffcf5d54f5d54f5d54f3fccf3fccf3fccf5d54f5d54f5d54f3cfcf3cfcf3cfcf5d54f5d54f5d54f3cf0f3cf0f3cf0f5d54f5d54f5d54f3cccf3cccf3cccf5d54f5d54f5d54 else 0xffffcffffcffffcf5d54f5d54f5d54fffccfffccfffccf5d54f5d54f5d54fff3cfff3cfff3cf5d54f5d54f5d54fff30fff30fff30f5d54f5d54f5d54ffcfcffcfcffcfcf5d54f5d54f5d54ffcccffcccffcccf5d54f5d54f5d54ff3fcff3fcff3fcf5d54f5d54f5d54ff0fcff0fcff0fcf5d54f5d54f5d54) else (if i < 106 then 0xffffffffffffffffdf75fdf75fdf75fcffffcffffcffffdf75fdf75fdf75fcf3ffcf3ffcf3ffdf75fdf75fdf75fcf33fcf33fcf33fdf75fdf75fdf75fcf30fcf30fcf30fdf75fdf75fdf7503fff03fff03ffffdf75fdf75fdf75f3cccf3cccf3cccf7ddef7ddef7ddeffffffffffffffff5d54f5d54f5d54 else 0xffffffffffffffffffffffffffffff)))))))

private def sigData (i : ℕ) : ℕ := unpack sigDataPacked 120 8 i

private def decodeState (code : ℕ) : ℕ → List W
  | 0 => []
  | n+1 => BitVec.ofNat 120 (sigData (code &&& 1023)) :: decodeState (code >>> 10) n

private def sigHash (w : W) : ℕ :=
  let v := w.toNat
  let h := (v ^^^ ((v >>> 64)*0x517cc1b727220a95)) &&& 0xffffffffffffffff
  let z := ((h ^^^ (h >>> 30))*0xbf58476d1ce4e5b9) &&& 0xffffffffffffffff
  let q := ((z ^^^ (z >>> 27))*0x94d049bb133111eb) &&& 0xffffffffffffffff
  q ^^^ (q >>> 31)

private def stateHash (ws : List W) : ℕ :=
  ws.foldl (fun acc w => acc + sigHash w) (ws.length * 0x94d049bb133111eb)


private def st2Packed (i : ℕ) : ℕ := (if i < 1 then 0xaba11250eae844933d1ce0214f2f3288439b223204f126188139e2261ece778987b39da261ece578807b3c59861ecf126147b3bc97f1eceee5ec7b39de261dce7788477396e211dcf4738c773cc4e21dcf31354773cc4d41dcf2f34c773cbccb1dcf2e304773 else (if i < 2 then 0xc4d30464e5784914395e0c448e6c8490f39b61143ce578150f3c4d4d43cf1352d0f3bc53043ce6e8450e39b611438e578150e395e04438e57805023c49533c0f47328ae3c49702acf125eca83c4986290f175fca33c497b28ced67ac9b3d1cdc258f3134c963 else 0x25c6fd9a3979b9668e5a6e59a396db5668e6b6c99a396db5658e5a6c996395db9650e5a6c9943c4d3046cf125451a3c4950468eee4c51a3))

private def st2 (i : ℕ) : ℕ := unpack st2Packed 34 24 i

private def adj2Packed (i : ℕ) : ℕ := (if i < 1 then 0x4000001c20041260000338c81a14410800040d81404a2a840000040084010200310460008c421075 else 0x408020080430004a01103019084c824084e608142)

private def adj2 (i : ℕ) : ℕ := unpack adj2Packed 5 64 i

private def loc2Packed (i : ℕ) : ℕ := (if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then 0x5d50003080000366000330493024f5c05f622834320000c428168c258f19815800000000000000 else 0x6eeac109380006c051680000000006f6800055aab000030bc0000007581b98ed19400003390000) else (if i < 3 then 0x29e4000000600f624000b212b04c210600005ec123135a7480002f0600062f1283ae495c else 0x4af073f4480007332cc79010000d61cbbce4ab80002bc600000000039ebc00)) else (if i < 6 then (if i < 5 then 0x93034840000000000003921b5d439000321ad832eed37bc3c00090058040019e10000003400460 else 0xec180009473a100000034b4000860eb69fbe4e00003ee4001e5242d1a780000001d12078080000) else (if i < 7 then 0xb8acd000000001cb00000000001948000000e1000054f05128dae6d3a03950000000000198c000 else (if i < 8 then 0xbec0000f01b015026d68000801e8000039c00009ed300ed25bf500000006420003d080000011e0 else 0x157793c00000000c0001d4cac44d80681b18290d988eb4af18c04ac25100002569d812efb1e)))) else (if i < 13 then (if i < 11 then (if i < 10 then 0x22042e15090000002b24000e791058000d00580d411b90f1eb00717b2b465a6816d80001386 else 0xaf05380001531a643801783c023c90b74001c9fdd10adb36194cebac584000000a805900000000) else (if i < 12 then 0x3a60001760d7900000000000000cda5800000000ea80016600000002790f23c04880dd53515 else 0xe7400004bcdda00067271619830006e40000000430424c26c03c14016848919309804000818680)) else (if i < 15 then (if i < 14 then 0x160147a00000069c8000ba162000000000003b259180000006cf00028060004f0096d654ac0 else 0xb380fd45822c0078349c9540b09c000000004126c80000e9895a7d0ec01eb4c843a8c349642000) else (if i < 16 then 0x701b5c391927c3bc0000007574000130b89167bbb40000000000942000274f16b640000 else (if i < 17 then 0x774945c9200034a763f2314c90cc0618000b824b8171000072d00000017804cc6240000492 else 0x42c436c0000002440d217000002576b08eda)))))

private def loc2 (i : ℕ) : ℕ := unpack loc2Packed 13 24 i

private def st3Packed (i : ℕ) : ℕ := (if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then 0x9b2173040a4975b2668094c6530304094969b266807495db266807495db2658074c497f28c054c497f298044c497f29004499db2668034971b2668034969b265803495db26580349d61143c0349a1f24c4014961f04c0014ad5b24c0014c4d3046801495e1146001495e1144c01495e0543c01495e0443c014c4d4843c01495e04438014 else 0x9621143c20495e1143820495e1141c1d495db26641a495e114501949620443c1649b21143816496211438164d1ce02b0164d1ce11dc164d1ce01dc164d04e01dc164961b266815495db26641549a9eb59015495deb59015495e11450124b59eb2541149de261dc11495db26680e495ddf5fc0e495ddf5fc0d498ddf5fc0c495ddf5fc0c4) else (if i < 3 then 0xc597b1dc454cc8d31dc454520c11dc444b59eb1dc424a5e043043e4b5db243c3c4d1cd928c3c4d1cd92583c4d1cd91dc3c4cc4d91dc3c4cb8c11dc3c4969b26683b4b5db243c3a4961b24c037495db24c0374961b2668344a5e04304324aba11210314c49481dc30495ddf5fc294c8d48304274c8d48304264c6530304254975b2668224 else 0x95db260c6b4c31483646b4c494833c6b4844c11dc6546c930438644d1cca1dc614d1cc11dc604d1cc12b45e4d1cca1dc5e4cbcc11dc5e4cb8c11dc5e4c49861dc594b9d7f1dc594c49861dc584c4d3043c464bb93043c464c493c43c454c8d30378454c8d30344454c6130304454c597f28c454c597f1ec454c497f1ec454c597f1dc454)) else (if i < 6 then (if i < 5 then 0x66d30304774d1ce2304774bb92c2f4774a9e112d0774a9a042d0774c497b28c774aba11248774cbcc12107749b22620477495e2220477495e11324764c4948300764bb94830076495db2650754c4962364754c494830c75495db265074499db25f0744971b25f074496db25e074495db25e074498611328724949b25fc6e4949b25ec6d4 else 0xccae53047749b21330477495a133047749d2123047749be123047749b2123047749de003047749e1ff304774c594a304774c514a304774c4d4a304774c4d49304774c4948304774bc148304774bbd48304774c0546304774c0146304774cc945304774b9545304774bbd31304774cb930304774bc530304774bbd30304774bb930304774) else (if i < 7 then 0xc492e368774c497b364774c4962364774c4931360774c494735c774c493e358774b5a11354774b59df354774c494834c774bb94834c774c494534c774bb92334c774b5a04348774c4948340774bb948340774a5e0433c774c4948330774c494832c7749de26328774a9e11328774c4948318774d072f3047740032e304773cb2ee304774 else (if i < 8 then 0xc4948370774c3948370774bb948370774c493e370774c4939370774c4935370774c4933370774c4931370774c4929370774c3929370774bb129370774c0123370774bf923370774c495436c774c495336c774c494836c774c493e36c774c493936c774c493536c774c493336c774c493136c774c392936c774c012336c774c4948368774 else 0x95e043287b4c497f28c7b495db25f0784002778987739de5b898774b5aae8847740025b884773c3611790774b7a57708774b76576d8774971b2660774969b2658774c5a57618774c4986614774c59865fc774c49855fc774c49855ec774bb97f5ec774b66ae5dc774aadea5c0774a99e64d4774c4948394774d1e04380774c492837c774)))) else (if i < 14 then (if i < 11 then (if i < 10 then 0xc49483647e4c49353647e495db26507b495db261c7b495db26107b49d5eb5fc7b495dce5fc7b495dcd5fc7b495dc45fc7b495dc15fc7b495dbf5fc7b495db95fc7b49d9b25fc7b4991b25fc7b48e1a25fc7b495db95ec7b495db25ec7b495db95e07b490db25b47b490db25b07b4c49483647b4c59303647b495e113287b495e103287b4 else 0x95dfe348844a5e1133c84495e1133c84495e0433c84495e0d33484495e1132884495e0432884495e0931c84492e14304844a6e1330484494a13304844cbe1130484499e112e484495e0e32882495e025fc81495deb5fc81495deb5f881495deb5dc81495deb5c081495db25f880495db25d880495db25f47f495db25ec7e495db25d47e4) else (if i < 12 then 0xbf91e364a34ccafe304a34c8530304a34cc91e304a34002d67ac9b3b5a11304974b5a1134c96495e0434895495db25fc944aba5784492495db25bc914c494836490495dc45fc8e492db25ec8e4ac2113048e4949b25fc8b495db25c887495deb5ec86495e0f5fc85495e035fc854d2657844844b5a1134884495e1134884495e04348844 else (if i < 13 then 0xc491e304ad4d1e11328ac495db25fcab495db25b8ab4c4948364aa4c4940304aa495db25fca94c494c304a84c4940304a84b5a11380a74c4948364a64c4948364a44d1f2a5fca34003125eca3395db25eca348d5b25eca34c497f5eca34c597f4c0a34c4931468a34c4d3043ca34c4948364a34bb948364a34c5130364a34c4d30364a34 else 0x961b84c10949d9b24c1044999b24c10449a1b24c1034999b24c10349a1b24c0fe495db2504f54961c34c0f44931b24c0f4492db24c0f44961c54c0eb491db34c0eb4925b24c0eb4961c54c0ea4969b24c0d14a05d0590c14c6eee4ecc14985bd4c0c146c930390af46f130304af4c4948388ad4b5a11304ad4c494a304ad4d1d30304ad4))) else (if i < 16 then (if i < 15 then 0x9d1ab4c10f4c4d484c10f4c49314690f4002578110e395e046c90e495db26510e495db25e90e495db25890e495db25350e495db24e10e4975b84c10e49b9b24c10e49b5b24c10e49a9b24c10e4985b24c10e4975b24c10e4969b24c10e489db24c10e4975b24a90e4c49304690e4969b258d0d4971b25890d4971b74c10b4971b74c10a4 else 0x961c55090f495db24f50f495db24f10f4949b24f10f4961bd4e90f4949bd4e90f495db24e10f48d5a24d10f4931c54c10f49a1bd4c10f4999bd4c10f4981bd4c10f4981b84c10f49d5b54c10f49b9b54c10f49a1b54c10f4999b54c10f4975b54c10f4969b54c10f49b5b24c10f49adb24c10f4969b24c10f489db24c10f49d9b04c10f4) else (if i < 17 then 0x25784914395e116c913495e228650f495e228590f4c4ad78490f40026c8490f3caada8450f40026d8450f39b6588450f49d2578450f4002578150f3b1a446c90f49d2266c90f495e056c90f495db96690f4975b26650f495db26510f49d6265910f49a9eb5910f4bb97f5910f4871b25610f495db252d0f495dc650d0f492db250d0f4 else (if i < 18 then 0x975b36c99a40025a6c9963969b266996495db366995495db266994495db265994495db2655944c5a9777d7f4a42546c97f4c2ed67ad7c495db26517c495db265d7b495db265178495db25e15e4c4ebb7c9304c8eaf7b13049a1e9769304aee58715304ade4b6f5304a968f6c9304a928a6c9304cd2586c9304961b866930496db5669304 else 0x25b6d59a395db86cd9a497a5a6c99a4)))))

private def st3 (i : ℕ) : ℕ := unpack st3Packed 44 24 i

private def adj3Packed (i : ℕ) : ℕ := (if i < 5 then (if i < 2 then (if i < 1 then 0x1000010d50000c104104114c2c10060000000120021091800010424011c00020c01400450c0087041384245001001040 else 0x1430403860000400080402431050400c028214a1010400010450000071400010802000c30032cf005141105140000244) else (if i < 3 then 0x2213800c708c0001010c60800000c05c114008215808b04000000e1c41406c01020802030441481400811ca001042100 else (if i < 4 then 0x1000011821d604600e1c10840820410000111091ce44110108000910004108100004018004104f086080040105180046 else 0x4300044100b04301a0010020400000030011405461c20816800020800c60402c1200002001081000001000040140001))) else (if i < 7 then (if i < 6 then 0x11800042c10c00051080042c00010000800c00010800000410020431070020440880c314140104b045040185043 else 0xc20c304b04e00f04400000400300000900908400508100004100000134000000214d04a1060050c0143100002140) else (if i < 8 then 0x41c128b14600414200130220404538204604000400404000a11218001b0412011010901041442421031c20c2100080 else (if i < 9 then 0x1400410020051041400c00421cb0020500400040013c00430400030c10c0098040100342050008002081545194 else 0x20810402800c30830411050c82020400010820820801832420056830410c30430005c0008043103180))))

private def adj3 (i : ℕ) : ℕ := unpack adj3Packed 6 64 i

private def loc3Packed (i : ℕ) : ℕ := (if i < 59 then (if i < 29 then (if i < 14 then (if i < 7 then (if i < 3 then (if i < 1 then 0x7fbe8146000036bd51a10ec129dd4542075c621866b0b78b3609a31c789000000000265a00000000535a00007c420000 else (if i < 2 then 0x99013085bdc00005b307190b0000000074c423c7e925720959e06860000000038846c9e000000000000190028c00000 else 0xc1d900001d8156107c2136c1000011020000000084c78c7000006a984d54af306b1e00000000000000004c709468)) else (if i < 5 then (if i < 4 then 0x2ac012bf3c0d238084c00000cbe000000000000000000000b6a190555b61bd4018a26e10395d0000811283de2698be9e else 0xa2e06e680000000000005fa1a16100000000053c453186a05c2157a161c61db0000000001f8600006e863fda) else (if i < 6 then 0x6f236e92110000000b4c42c801128bc600006cad0821b50bac801edea30476a100003ddec13cba804a3c1f9aba845f99 else 0xd5da00000000000000000000000055c0000000008b0994015f916d5f47040000456c000069960bbc4700000000000000))) else (if i < 10 then (if i < 8 then 0x7a4182f0cde30000975838045f59d15b47126863000063dd87a1aac00000473d06f40000331053db9add00000000b6b9 else (if i < 9 then 0x314c365a5b98000070dd6aa135b0beb000004348cd920000383e6a9e00000000000028da0000000065f2 else 0x7f3d0000962155616bf18a33b91a0ebd43400000c6840000053827410000000036bc12e2be32d8de764c8652000028de)) else (if i < 12 then (if i < 11 then 0x681600007f696fda0000bc58890b2a272718000084630000000000004e834ac13e8025483268b6700000b504808014e0 else 0x1cc000000000bf30bbe36722000000005f581eda948026db3e5a2bc09a5aa6f60000b7805b3275288aa900005b99aa40) else (if i < 13 then 0x49c05fecc860d4837c1e000000008e90c9da000000006dddc4da6c5e2ef00000b5050000d25a4803ae40 else 0x2930000040806592a272a366430700000000a9a5af401ec0213c000041210000a44136e02c88894e0000a36300004731)))) else (if i < 21 then (if i < 17 then (if i < 15 then 0x94cc6ed300c91c8981600000951e90df46bc476c522941de0000128600009aa90000000000006edb0000a2e11f2998a1 else (if i < 16 then 0x96b3c5701c720000c5003fbc00006ec887a000005bc800004f98a6bc209034b003404e80991e69619c1b000058a80f92 else 0x48c04dc7bc9114002f105d5d6206000000005d219e61000000009c5c62bf5ba900006d5d6fd013c0400425806140)) else (if i < 19 then (if i < 18 then 0x879e0000aa5a345ad7de00005f880000b5095e8357403dc03b40531812e000005fb000000000c4f252a88aa7ca3c0000 else 0x7b42849e4ac01740000032216aa94306cd466eccc642b519d95acb5862eca92500000000a65e75647abd5f606b00) else (if i < 20 then 0x9348b53c0000091e00009ad1245c4dc6c3da721636ed00000000b5260000828800003f5aa69db9066797000000000000 else 0x541100000160b3e704610000000000005bf241910fa101702c80d390bec05146000041cd000021c050220000000021a1))) else (if i < 25 then (if i < 23 then (if i < 22 then 0x418f00004d5b0000b5150d0c64100000000000006d80000000007e7167e7ab80000000007ebbbc00000042000000 else 0x42ab3630c8858edd0000000000003a3c98748e5c8aa143dd5aec58100000129882e30e5c00001570d0d80000a2c07877) else (if i < 24 then 0xa24077820000013ca4673c02433d765a000071dac10307a17daab53d00000000b5410000000000000aa12e000000 else 0x90830000240c0000000000005ade0000000000004c2000006800cd600000348600000c64768026a1000041c000002f9f)) else (if i < 27 then (if i < 26 then 0x74726c600000821800009400b608000056a1000000001dd0a558949e9fdbd8e125109ee00000a246235e6c884504 else 0x2131c56c5104862100000000000000008b2d000077280b27aa030b5b8d8200003e833f840000000000004a3f0000) else (if i < 28 then 0xa78400006fcc3c4800005adc8e1800007a5822c07fad0000d580b54cb921000000007b7403f00000b2c0a261b4c00000 else 0x910af5800002d2122dba00237aa5ff05bec00000000000028c93010d60517da0000085d5c4188e30000000081630000))))) else (if i < 44 then (if i < 36 then (if i < 32 then (if i < 30 then 0x27392a5300001be098f2b546205f341000004570bf0500007e150000d41e000000007c39959ba9a13c8694a199c1 else (if i < 31 then 0x1b085bc90000364039803275415a36a0b5212451000060062a2900000000000000000000a02f00006f900000100401bc else 0x8115bc400000b5020000000000000000000006dc00004e008d3900004a3da4de2890030900000000)) else (if i < 34 then (if i < 33 then 0x54db000000004c2aa58f8b3f863944c1000024a81f5e368900005bc7a68fbd040000241ea4cc0000585100000000bcde else 0x2be97590000000005ed90000b5600590d7001746a6baad8000000000089000000000695d00000000bea7bcf60000) else (if i < 35 then 0xb6300d02245d896e0a1e1680000084866cc53b413a8c00003fc94fc10000892e5670387065e4d0c0664c828978cc else 0x2cf00000c15ece8b00000000b8028fb0be592f960000522100008739780000000000bcb000000000585700007e046621))) else (if i < 40 then (if i < 38 then (if i < 37 then 0x66a3a4da00000000b5664530b9a300000000859500007fbb1fdb00004742b3c60000000015aa61a900003cde02c634a1 else 0x759b0000bf5e43769e5d0000a370bc7000000000577300000000bec17353000000004501d2a117c075128e00) else (if i < 39 then 0xaec01ba19d5b03bc78dd00005a80a33f70f54b5e82a024000000c9b0189f3721000000000f4500003f8100000573 else 0x82929d3f5b5c4c21727200000000a8891a1e6cf76c8667680000007000006f9e420300000000312aa89ea3c0319e)) else (if i < 42 then (if i < 41 then 0xc304b53fd7daa0a100001f5f00000000839ed321a7e032900000885d9c3f00832c410000000042bd00001bc0a2490000 else 0x2601dd400007ebc265d79f200002849000041db12000000000023a182a118e400000c805cc00000508030cc) else (if i < 43 then 0xa5df0000000000003f850000d9750000000001008104146000000000bea122da6e9e4498235f1fa900000000b5c00000 else 0x3269a20136e941da0000176000006e8540c03a6013bc372000002b3c00006d331a102bc157c08c06cec03f8300000000)))) else (if i < 51 then (if i < 47 then (if i < 45 then 0x6da900002fdc62f2724c0000379251807e89d21e0000275a00000000108a069e1fb00000b554ccf04ec1088972cc else (if i < 46 then 0x244800000000334ca32aa25a4f03460c829828838f5a2101000010019aa300009aa8bcb36add3fe14fd40000c3725cdb else 0xac7036950000a2815bda3a2d000043c812aab1006b92000000006cf18b2100000000cb5e4546000077dd7ac27d695fbc)) else (if i < 49 then (if i < 48 then 0x775c00008c0400000000000084a0b646a94600009c1e00003d00951080e300006ed4c80800008721bbc05b7300006a80 else 0x5b800000c20301159f274b20c97000004701443c60220000b4bc00007b4024da8da1000000006769642142da9c5b434a) else (if i < 50 then 0x19187cd70000000000007372a718000000000000000091da5c40000000004fc098230000b5406ecad67600006c12 else 0x9bc04f897ca10000bf31ac461b040000000047da70a10000a9a88b04502d905b0000000000000000cac00000))) else (if i < 55 then (if i < 53 then (if i < 52 then 0xc12d8d86ec234292eef00004ec078bd9f2189d3000046804500a2420bbd4188000000003c0c2fa34f4100005513 else 0x21e855a05fc20000000000000000a5d91fb600000000477000004360000000000000000063a100006e4c000001c059d4) else (if i < 54 then 0x4f40b380adbc1c80bd3e0d06c02e8170000005a90000000024dc00000000d0836f21bb1a876060313adc0000c2002840 else 0x862000006fd1000096a10000545e435a5290304c4d5e00000000000052b6582156dc5e758488490421e90404000049d4)) else (if i < 57 then (if i < 56 then 0x184c0000061e2810472d661e00000000255d74750000c583000000006be0000000004d8800000000000043c09b700000 else 0xb98055da7702249070725fd8000090c000000000d7d8000000003380215e0000000000000000c884000001046184) else (if i < 58 then 0x36e62b4000006eb6b5011284000000000f0a00000000d5006ef000009acc36e3ac4058cc0000000000005d197ee9d85d else 0x275b63105b6095003a80b18394ddc60300002e90af03b6896861b35e44006ca048000000358300000000a6f1)))))) else (if i < 88 then (if i < 73 then (if i < 66 then (if i < 62 then (if i < 60 then 0x514e03c018733c5a20834b4045e494da6d1bb4617c3e00004180c706a7c01c4097f4655ab506920039840000 else (if i < 61 then 0xd75d460200000000725ac4310000000047606fddd180435b761b13129832b63c60e005da45430000cc587f8800000000 else 0x11d80c104e5a00000000890cbd84b5185d4123400000b508863f00000f0902709aa100006c8e00004dc215000000885a)) else (if i < 64 then (if i < 63 then 0x324c00000000a160c7e05a49b1b03521000000000000bce100005439000000003cdaaab144beb547000090de832a else 0x2de0a69331409dc027b090304daaa2f0000051140000aab0911000002780373c000069100d100000a30800005a4836b9) else (if i < 65 then 0xac017a21acc00000000000004d00cf70000001ec4d1804e000003f400000000000005150abc670807d46ca84a33c0000 else 0x365e51103fb1000000001e1ea20412e66a20555a4c8326214130b3304f5ebcc080957c1200000000000061a840da0580))) else (if i < 69 then (if i < 67 then 0x3fe0c9000000000022de841e00000000000083045bd384f14d1ea3bc000000009190ccc0a6a02fe454c9344021e05898 else (if i < 68 then 0x895fb2b0238c00007b3da30900000000ca40a1e088c00240b1c03180c194a6c7000000005a5b0000000000004e5e else 0xd4210000355a4cc074dad6f29e72cf83705a00006eb10000920db15e7c208780ba00000064dac280000000000000)) else (if i < 71 then (if i < 70 then 0x7bc224a1bac9160415920000038041b3789e000000000000b881ae000000a6ce00000000740ca50046b2a320406d else 0x66df06b90000000000000000a1f0000031da9c5a0000000031cc000000004bc070c8000089f33a831db10000000006b8) else (if i < 72 then 0x100017e092dd11c0000000c0a6a77212000062be0000c31e90db000084713b080000814000009b66b8862c40 else 0x720c035e9ee32dc0b51a000006cc15c06c923c0000007827000051293a906ada6e83991800007ca0a8180000)))) else (if i < 80 then (if i < 76 then (if i < 74 then 0x82950000a0b908dd9a2100000000bc83aa80839700de1c5a00001b3f000068a20000000000000000000000000000 else (if i < 75 then 0x1aa89453460430daa5d877a800000000000000005f300ec056405f98b55a2ce000001a860000a24b67b7cc74c25a else 0x62e20000b0df67ea7d0800000000221a25dd000000006d57000000009e6493900000bcbdcf460000a340)) else (if i < 78 then (if i < 77 then 0x1e65364c3fc89a9e5bde00000000369816050baaabbc00000a9f6ce341d8c7f00ae486d20000a9408a400000b7012410 else 0xbbd89bb96a2100006e89d9100000b82114bc5c5a90030000c6e000000000b5131aa9000025c80000aff06f8000003f00) else (if i < 79 then 0x3ff00000000006104189b200000041b0b5390000d583c133ac760000600000004e34d8106a23c58d708c0000bd00b510 else 0x1d800000000000003f801998682a6480c5d9458400005881d71ea321000003bd0000850c2a5e00000000b1805ca10000))) else (if i < 84 then (if i < 82 then (if i < 81 then 0xbe5c3600040178264fde6f000280000000005b89bf330000933959dc0000abc005a17803c4b1 else 0x73f388880000cb5a000000006510b5360000000053c100000ebe833eb66002bc000018a1cd090000474347060de91bad) else (if i < 83 then 0x65e000005fc041c800005984195a57211d606bad33da000000005dc000001f80b348d70169a30000000004c24ba00d9e else 0x7275a70843130de05b5a000037f0000000000000b7212b88b4302740418d000000009aa7539006f29d4111da80080000)) else (if i < 86 then (if i < 85 then 0xc5f24f91715a7d954abd66230000c54900000564000000008109000053a818d129a7165e09805df3910000008948a318 else 0x30a700005840d018ad40000000002224c0036c80beb20000562000000000983b00003f82000041d400008c82) else (if i < 87 then 0x43bd000060235a5cb44718210000565100002eb936aa0fe600001360043100003dda00000000d44838aa000000008d5f else 0x8280d3a33658b0280000000043ca4d4081089cc09ada786600000000a69aa65800005be100000000000044bf00000000))))) else (if i < 103 then (if i < 95 then (if i < 91 then (if i < 89 then 0x2000cc3373d1745aa3000000cf821de00000a41c31dd0000000000000000039506010000be1056c0018000000f02c440 else (if i < 90 then 0x60024dd9ad33c03c0408ab93dbcb260545b5fc60000be830000be16544012c60e92925e000079c0a33e0000645dadc0 else 0x659a19db8502285a3c10706800009206beb30000995c52de148043610e1e4bde5e700000000053da5df000000000ce12)) else (if i < 93 then (if i < 92 then 0x28808ba1b52a709f9833cf4000000c8c995a00000000000083209330cb950000d6dd00000000000000004aa124205e41 else 0x7c180e72000027c16c6b585b2d1c0000c3837929428d000020de72000000c058565b0000bb030000afc0d60300000000) else (if i < 94 then 0x5611beb900006a90c062cfd800000000a46600008015000079a740460000bdc000006ec0006000000000038436c0 else 0xc3debcc934b609000e5a3a3e248c0000325dd4200000000000009bdb0000000000004c084346000039001fa883b0))) else (if i < 99 then (if i < 97 then (if i < 96 then 0xab4042f4a3bd071e000032860000c4b0b900ade049db00000000000059dac0ec309000000000a24800004bdb07900000 else 0xa60fa26c00002fa2b609955d00009d590000ba1a100609da8f910000be919ee2ba957d2d430d0000000000002a5a) else (if i < 98 then 0xb3e03b303c800e1830dd000000002c92000000005000254c0000689687a388217c0aa6df170057f46e905bb0b55e9fda else 0x7448bfc00000214032800000bea941063ada00000000b500c188000000000000cd7000006fc871cc64dd0000)) else (if i < 101 then (if i < 100 then 0x1f396eb092898ac1a4b3989085e09b6000000000000030a172518720c1c0098341bcbb2781000000a502 else 0x8263255ac4300000ad0000001698000059c00000000088923b180000a045a1400000bcd8108000004186c1300000) else (if i < 102 then 0x3e0392da00003c49c9420000aada1a16252153de9b9800005adab0c07fe900005e21c572000000000000081e6c002c39 else 0x280000000000000000006e5e00003fd4bff0000000005573a9a31dd784f71be9383c0000689f2e702fd15f80000023da)))) else (if i < 110 then (if i < 106 then (if i < 104 then 0x6ce03ec0a69e000000008270000000000000059e0000a0101300000000000c0d8cc059286cc175804190af5e07dd else (if i < 105 then 0x79215b88363300000000821500001fa185e300001a6850a70000000084898f5c06da31a181becabe54da00008b41 else 0x7e1c0000cabc00000000000000002be000003c4c84a660c04312bcb2a7698a1bc186000084e302c07c2a5a02)) else (if i < 108 then (if i < 107 then 0x10140000242142c643c604da0000429dc88613e0ced80000cd408d3f8063be30a8c1bc824330c9c036bf00000000cf58 else 0x4e5c000066a1b09e0000cb400000a38800001241931112c1d6da0000248021540302418c499eb686000000003b802030) else (if i < 109 then 0x8802130535fb64039928e9e5ed836a1be743439216000006764000012c09d1a00000000052100000000000029d30000 else 0x93da5a5a000056a00000493c7de0b2da418380840000b6805421369c000000004746000000000000377072f2bcbc))) else (if i < 114 then (if i < 112 then (if i < 111 then 0xb5709c364cdbc8937ab900007f3b79a100009d1800001560c482418232810000c3b05da1c8002bbc9180a31900000ff0 else 0xe001dde52337a5912bd00007bc0b54e58da632160c110600000000048bc5fb99e6038a1000039e0000049d8c4c6) else (if i < 113 then 0x3b2100001be65fde35c0abcc9bc15183000041d50a2300006a127bb9bd803add05831240000082c080f0d0c878dc0000 else 0xd410a3715025760078c0a76800000000000030015980471ca205000095dd9b9b0000ac00c70400007b3b)) else (if i < 116 then (if i < 115 then 0x5f4200003fc693213e400000b5624d0941c9000000002918330046bd0a21000000005fc1ac040000c28a425a00007a75 else 0x81e69d4000001280305a0000c6bc00000000305db53e0000d3a1244cd324000077c100001f106c680000525a16aba898) else (if i < 117 then 0x2edba6d9395a0000cb3000000000453c000081aa00000000115a4740a4bd6821222100003210c96099a12f21a503 else 0x4fa10000c68014405bf688801600000031dc0000)))))))

private def loc3 (i : ℕ) : ℕ := unpack loc3Packed 16 24 i

private def st4Packed (i : ℕ) : ℕ := (if i < 28 then (if i < 14 then (if i < 7 then (if i < 3 then (if i < 1 then 0x95db25890d0056576c92a4240159a1b24c0ff0056b56c9303ac01595db24c0d10056576c961304015ad5b24c07700566c848c11dc015c4930468450056578450f0f001595db24c0360056576c99a06801595e1143c180056578450f05c0159621143c160056576c99a01c015975b2668060056576c99901801595db2654060056586c93043c005961b24c10e0016576c930438005c494836477001712528c11dc005 else (if i < 2 then 0x95db24d10f0096666c93043c025981b24c10f00965c6c93043c025969b24c10f009657845f2668015aeeb56c930005400ad5b24c0014961b24c1170056436c93045c0159b1b24c1140056586c93045001595db24c114005712b5a1143c015002578110f005257811b243c01595db25890f00566e6c93043c0159b5b24c10f0056616c93043c015975b24c10f00565a6c93043c0158d5a24c10f00565d6c930438015 else 0xc497b1dc450116e26d87710004595db25fc2801140095db265803496db26697f00d6576c9965fc035975b25fd0f00d6576c97943c035969b25910f00d6576c96443c035969b54c10f00d65a6c930430035949b24c0fb00d64b6c9303d403595db258cc300d6576c96230c03595db25fc7b00d6576c97c1ec03595db25ec7b00d6576c9781ec03595db25fc7800d6ee4c0c11dc03595db25ec7400d6576c93643c025)) else (if i < 5 then (if i < 4 then 0x95db25fc840156576c97f1f805595db25fc7b0156576c97a1ec05595db25f0740156576a1721ec045b89cb6c8770116576c9971dc045c4aee5fc770116776d97f1dc045995b65fc7701165f6d97f1dc04596db65fc7701165b6cd7f1dc045961b35fc7701165b6d97b1dc045c4948364770116d6720d21dc045b59b6348770116576d17f1d404595db65f4750116576f17f1ac045c497f1dc630117125fc77114045 else 0x95ddf6c97f0316576c97f1ec0c595db25fc7b0256ee4c0c11dc09595ddf6c97b0216576c56430c08595db15fc7b02140095db266807495db25910f01d65d6c93043c07595db24c10901d6576c93042007595db95fc7b01d6576c97f1d007595db25f15f0196576c93443c065981b24c10f01965a6c93043c06595db26690e0196576c99943806595db25910e0196576c93042006595db25e90f0156576c97f28c055) else (if i < 6 then 0x9b2113007605974730477174165002577ad640552577ad6443c15595db24c10e0556576c97f20415595db24e10f0516586c13043c14595db25fc7b0516ee4c0c11dc14595db25fc8104d6576c93040412595db24c1000496576c93023812595db25fca30456576c97f25411595db25fc8e0456576c97f21011595db25fc7e0456576c97f1ec11595db25f0740456576c97f1ec10595db24c10f03940095ddf5fc0c4 else 0x969b24c10f0596576b13043c16595db24c10e059400d1ce01dc164b5a113807705966c844e01dc1658b2113807705966c844d31dc1659b2113187705966c844c11dc1659661130477059658844c11dc1658a2113047705966582cc11dc1659b20430477059659810c11dc165962043047705963d7ecc11dc1658c1f83047705962c7d0c11dc165c49483047705970e520c11dc165bb9483047705964f844b41dc165))) else (if i < 10 then (if i < 8 then 0x9b21330477085678844c11dc20595db25fc7b07d6576c97f1ec1e595db25ec7b0796576c9721ec1e595db24c10f0756576c93041c1d595db24c105075657844ca2101c59ce11304770716576c93043c1b595db25fd640696576c93643c185999b24c10f061657844ca2101859b5b24c10f05d657844ca21017595db24c11305965784a1143c16595e124c50f0596576f53043c16595db54c10f05966d6c93043c165 else (if i < 9 then 0xac211304770a96576c93034428595db24c0c30a16526c93030428595db25fc7b095712520d01dc255c8d48304770956ee4ecc11dc255bb930304770956ea4c0c11dc255c8d30304450956976c930304235ade576c9300896526c93043c225949b24c0fb0896526c9303e822592db24c0f508964b6c9303ac225a6db24c0c10896996c93030422595ddf4e4c508565777d3331421595e1133c84085657844ca210215 else 0xaa68c6c9300c96aea0db24c0325aea576c9300c964b6c930438325a5dc94c0c10c969771530304325a5dc34c0c10c96976e130304325aedb24c0330c9712520c11dc2f5c4948304770b96576c97f1ec2d5caad6844770b56d67ac770f02d5975b24c10f0b165c6c93043c2c5a41b24c0c10a96976c9302dc2a595de84f8770a96577ad351dc2a595de84d4770a9657799351dc2a595e11328770a9657810ca1dc2a5)) else (if i < 12 then (if i < 11 then 0xb5a11304770fd6d677cc11dc3f5c4948304770fd712520c11dc3d5bb930304770f5400d1cd91dc3c4c4a11364770f1712478d91dc3c5c494834c770f1747cc4c11dc3c5d1d48304770f1712518c11dc3c5d1cc128c770f1747304771383c5969b24c10f0e9747304771383a590db24c10f0e574795cdc1dc38590e04304770e1712520c11dc355aee586c9300cd6bb95db24c0335961b24c0ea0cd6aea31b24c0325 else 0xc49b25fc7b1156576c97f1ec4558d5b25fc7b1156576c97b1ec455c497f4c07b115400c597f1dc4548d5b25ec7711571248cd31dc455c493b34077115732c48c11dc455c516430477115712510c11dc455ca940304771157154c0c11dc455c4930304771156ef4c0c11dc455bb930304771155884c0c11dc455c0123304771156e648cc11dc455cc91e304771156ee4b0bd1dc4554c0c11dc5010d65b6c97f1ec405) else (if i < 13 then 0xc4930304771296576c97f1ec495c454a304771257124c0c11dc495c4530304771256ee4c0c11dc495bb530304771257124b0bd1dc49595db25fca31216576c97f1ec485c49303047711d7134c0c11dc465c4930304771196ee4c0c11dc465c49b34c10f1157124c53043c455c8f124ecc11157125892e304455c4930304aa1156576c97b28c455c4948364a31157124c0c1244455c49eb4c07e115400c497f1ec454 else 0xcaa11304771657124c0c11dc565c492e304771557124a4c11dc555c492830477155712544c11dc545c4d30304771517124c0c11dc535c4948304771497124c0c11dc525bb9303047714971177130304515a5dc34c0c11456976f53030451572d3030477145712520c11dc4f5c4948370771397124a4dc1dc4e5ccd23304771396576c97f1ec4c5ca93e304771317124b0bd1dc4c5c49303047712d7134c0c11dc4a5)))) else (if i < 21 then (if i < 17 then (if i < 15 then 0x95db25fc7b19d6586c93043c66595db24c10e1996526c530304665c494836477199712530c11dc665c494a304771996ee520c11dc665a5db24c0c11916246c93030464571530304771915b24c0c11dc645c4948304771897124e4c11dc625c492330477189712520c11dc5f5d1e1130477179712520c11dc5e5bf948304771796ee520c11dc5e5c492330477179657844ca2105c5c49303047716d70a4c0c11dc5a5 else (if i < 16 then 0x961b24c10f1c16616c930304705989b24c0c11bd65777db25fc6d595db25fd0f1b56576c97f1d06d595db26597f1ad6576c9965ec6b595db24c1061ad6576c95f3e06b5a4ddd4c0c11ad693771303046b5c8d30304a01ad697844c12106b5a8e4b6c9301a96586c93043c6a595db24c10e1a96576c9304186a5949b24c0fa1a9712530c11dc6a5975b25fd0f1a5712538c11dc69594db24c0c11a16576d97f1dc685 else 0x95db25fc811dd6576c97520477595db24c0fa1d964b6c9303a876500257844c91d92576c97a30476500312520c01d92576c94830076595db24ccc01d96576c931300765c49304b8d91d56576c979304755a4dd74c0c11d57124b8c128c755971b2668771d56576c9791dc75595db66c97c1d140095db25e0744969b54c0c11d16576c99a1ec74595db25e07b1d16657a5b24c0715961b24c10f1c5657835eb5fc705)) else (if i < 19 then (if i < 18 then 0xa99ab4a4b41dd64b6ad292d0775c494843cb41dd712619302c4775c4948364b11dd712520c02c4775c49482f4b11dd712520c12c077595db25fca41dd712528c128c775c4940304a31dd7124ecc128c775c5930304a31dd7134c0c128c775c492c2f4a31dd7124c0c1284775bb930304a11dd7124c0c127c775c49303049e1dd7124c0c1274775c31303049d1dd6ee4c0c1274775c8d303049c1dd657844ca21c775 else 0xc494a43cc11dd6ee5210f304775b5a1134cc11dd72ab5a11300775c49eb520c01dd7125fd4830077595db257cbe1dd72ab5a112f4775c49eb520bd1dd712bb92c2f4775002ee4b0bd1dd2ae7092c2f4775ab1c24b0bd1dd6976f12c2f4775c494843cbd1dd6576c95e2f0775965b04b8bb1dd6656ad292ec77595e4f844b41dd712c21482d0775c49eb520b41dd7125fd482d0775ab9eb4d4b41dd712549302d0775) else (if i < 20 then 0xb95b248cc11dd6456c123304775919ab48cc11dd62c69923304775bb96448cc11dd7304c123304775b3a10488c11dd71253122304775b5a1147cc11dd6febb91e304775bbae5478c11dd6d68451e304775b5a10478c11dd6d38411e304775b5a04478c11dd6c57f91e3047758b19e478c11dd7125291e304775bb948478c11dd7314c11e304775bb92c478c11dd6ee4c11d3047756c930470c11dd65784510304775 else 0x96db34b0c11dd66c6b92c304775bb9644b0c11dd6d67f929304775b59c74a4c11dd6ce71d29304775a5dba4a4c11dd6596b529304775961ac4a4c11dd6ee67929304775b59fe49cc11dd6d672125304775bba1148cc11dd6d084523304775b5a0448cc11dd6ee7ed23304775b55c948cc11dd66c7212330477597dc848cc11dd65972123304775961c848cc11dd6ce71d233047759b1c748cc11dd6c56f923304775))) else (if i < 24 then (if i < 22 then 0xbbda24c0c11dd6ee68930304775bada24c0c11dd63c689303047758e9a24c0c11dd639689303047758dda24c0c11dd636689303047758d5a24c0c11dd62968930304775739a24c0c11dd65767130304775bb99a4c0c11dd71261930304775c494f4c0c11dd71253530304775bba114b0c11dd6ee7ed2c304775b4dca4b0c11dd66c6d92c304775995b64b0c11dd65f6d92c30477596db64b0c11dd65b6d12c304775 else (if i < 23 then 0x9b1b34c0c11dd65f6cd30304775965b34c0c11dd6586cd30304775d29b24c0c11dd6b56c930304775ad1b24c0c11dd6916c930304775a41b24c0c11dd66a6c93030477598db24c0c11dd65a6c93030477595db24c0c11dd6ee6ad303047759d1ab4c0c11dd66c6ad303047759e1a84c0c11dd5b269d303047758c9a54c0c11dd6ee69130304775a0da44c0c11dd63469130304775bbda34c0c11dd6ee68d30304775 else 0x92dc54c0c11dd69070930304775949c04c0c11dd6666f530304775981bd4c0c11dd6526f530304775bb9bc4c0c11dd6ea6f130304775a5dbc4c0c11dd6956f130304775a4dbc4c0c11dd6906f130304775995bc4c0c11dd65f6f130304775869bc4c0c11dd6936ed30304775a41b64c0c11dd6766d5303047759d5b54c0c11dd6666d530304775969b54c0c11dd6ef6cd30304775bb9b34c0c11dd6906cd30304775)) else (if i < 26 then (if i < 25 then 0xcc6ee4c0c11dd72dbb930304775caeee4c0c11dd6f4bb930304775002ee4c0c11dd347ba530304775d1ee84c0c11dd708b9930304775ba2e54c0c11dd712b9130304775bbae24c0c11dd6eeb7130304775bba314c0c11dd6e087530304775af9f74c0c11dd67877d303047759a5df4c0c11dd66277d30304775b89cc4c0c11dd6d172130304775b35c84c0c11dd6c472130304775b0dc84c0c11dd66871530304775 else 0xa5dbc4ecc11dd6976c53b304775949b14ecc11dd6356893b304775c494f4ecc11dd6586f53a304775949bd4e8c11dd635689373047758d5a24d0c11dd712bb93330477597dc84ccc11dd65b6d933304775965b44ccc11dd712bb931304775965b44c4c11dd66c6cd31304775965b34c4c11dd6586cd31304775cc7124c0c11dd72bc4930304775c4eef4c0c11dd400bbd30304774d1eee4c0c11dd746bb930304775) else (if i < 27 then 0xc4b0a520c11dd712c0148304775c4aee520c11dd71084548304775bba11520c11dd71077d48304775c39df520c11dd6ee77d48304775d1dc8520c11dd71067948304775bb99e520c11dd6ee59148304775d1f1251cc11dd71252147304775bb94851cc11dd400c0146304774b59c8518c11dd71252146304775c4964514c11dd6bb7154230477592dc5508c11dd6976f13f304775c4aee4ecc11dd69777d3b304775 else 0xc49df530c11dd7125914c304775d1f12528c11dd72ac494a304775c4b0b528c11dd712c214a304775c4afe528c11dd712bb54a304775c4abb528c11dd7128454a304775c49df528c11dd6976f14a304775c49b1528c11dd6356c54a304775c49b0528c11dd7126ad4a304775c49a2528c11dd6356894a304775c49a1528c11dd7116854a304775c4964528c11dd747ca948304775cab23520c11dd400c4948304774))))) else (if i < 42 then (if i < 35 then (if i < 31 then (if i < 29 then 0xb59fe570c11dd72a84552304775ca9df548c11dd71277d52304775ca99e548c11dd71277d51304775c4a11538c11dd71277d4e304775c41df538c11dd70e77d4e304775c31df538c11dd6ea77d4e304775c49bc538c11dd6976f14e3047758d1bc538c11dd7126c54e304775c49b0538c11dd7126ad4e304775c49a2538c11dd6976894e3047758d1a2538c11dd7126794e304775cab12530c11dd712b894c304775 else (if i < 30 then 0x95e4b810c11dd6578d60430477595e30810c11dd6978b204304775bface7f8c11dd712b15fe304775bbae57ecc11dd712b05fb304775bbac17ecc11dd63d8d5fb304775bfabf7e0c11dd66c825f83047759b2117d4c11dd6c57f9df304775c4aa1760c11dd6d897dc8304775b5e58720c11dd6d895dc8304775b5e57720c11dd73292db2304775cca436c8c11dd70d845a0304775cc257590c11dd6ce7f964304775 else 0x91a35844c11dd6578ce1130477595e30844c11dd66c8aa11304775c2ed6840c11dd708b5a10304775c4ad5840c11dd712b5a0b304775c2ed682cc11dd712b560b304775c4ad382cc11dd712b320b304775c4ac982cc11dd6579020b304775c4acb824c11dd66c83609304775c4ad6818c11dd66c84606304775c4ad6810c11dd6d6a5e04304775aba97810c11dd66c95e0430477596657810c11dd65895e04304775)) else (if i < 33 then (if i < 32 then 0xc4ad6844c11dd709b5a11304775c22d6844c11dd704b5a11304775ac29b844c11dd6d89ca11304775ac270844c11dd74095e11304775cde57844c11dd73095e113047759b257844c11dd6b095a1130477595e51844c11dd657942113047759c24b844c11dd66e92e1130477595a4b844c11dd65792a1130477595e3f844c11dd6578fa1130477592e3d844c11dd6728d6113047759ba35844c11dd64f8d611304775 else 0x95e4f844ca1dd65292e1132877595e3d844ca1dd6528d61132877592e35844ca1dd6438d61132877595e18844ca1dd65785a1132877595e15844ca1dd65785a0432877595e11674ca1dd712b06a1304775c4ad6a70c11dd730bfa57304775cc2e595cc11dd73095e2c304775c4ad684cc11dd4009b213304774c4ad6848c11dd4009b212304774bfaee844c11dd712bb211304775bbae5844c11dd727b5a11304775) else (if i < 34 then 0xc49304b0db1dd7124c12936c775c493048cdb1dd747c4afe364775c4b0b520d91dd712bf948364775c4aee520d91dd7127ad48364775c49df520d91dd71267948364775c497f520d91dd72dc4930364775c494c4c0d91dd71250130364775c493b4c0d91dd7125210f364775c49304b0d71dd712b065734c77500312520d31dd2578451834c77500312520d01dd347aba11328775d1e97844ca1dd65795a11328775 else 0xc49865212c1dd69e78d3043c775c49864c10f1dd6576c95f42477595db257d081dd6576c95a3e477595db257cf81dd61b6c9303ac775afe114c0e01dd71277d4e374775b5657844dc1dd6d395e11370775b3257844dc1dd6c995e1137077500312520dc1dd312b2d30370775c4ac84c0dc1dd712afd30370775c49304b8dc1dd7124c12c370775003124a4dc1dd3124c129370775c493048cdc1dd7124c12e36c775))) else (if i < 38 then (if i < 36 then 0x95db25f90f1e96576c9303107a595db24c0c21e96576c97f2f07a595db25f8bc1e965777db25fc79595db25fd7c1e56576c97f43c79595db257d0f1e540095db25f078495db25fc7b1e16576c97b1ec78595de06d97f1dd6e2a65b25fc775ca9e26c97f1dd657781ab5fc77595de06897f1dd6576d99d5fc775c49b26897b1dd6576c97f59c77595db25ed571dd7127ad864c0775ab9eb5a1301dd712619474c0775 else (if i < 37 then 0x95db25fd781ed6576c97b5e07b595db26ad731ed6e295db25c87b5002436c96d1ed2576c99a5a87b595db25e16a1ed6576c97f5a47b595db25ed691ed6a692db24c07b592db25c1301ed6436c96d4c07b5975b25fd0f1ed40095e113287b495e116c8ca1ed6576c9273287b595db2590c31ed65d6c93030c7b595db24a8c31ed6576c9303047b592db24c0b21ed7124c0c12907b595db25fca31ed6576c97f1f87b5 else 0xc8e576c97f1ed6e295db25fc7b5b6a576c97f1ed6ca95db25fc7b596e546c97f1ed65b8e1b25fc7b595dc26c97f1ed6576f1b25fc7b595db66c97f1ed6576cdb25fc7b595db26a57f1ed6576c99a5fc7b595db26597f1ed6576c9925fc7b5b8a576c97c1ed6e295db25ec7b5002576c97b1ed2576d9b25ec7b595db26c57b1ed6576c9ab5ec7b595db26897b1ed6576c99a5ec7b595db26597b1ed6e295db25e07b5)) else (if i < 40 then (if i < 39 then 0x95e1143cb92116ae844c12d084595e11304b42116576c930324835002577ad7f2052576c97f5d081595db24c0d22056576c93033c81595db24c0ca2056576c93030c815b5a577ad7f1f96576d9b25fc7e5002576c97b1f92577ad7f5907e595deb6c9381f96667c9b24c07e595e116c8ca1f96576c96430c7e5c4930304a61f96e295e426c87b595e117ad7f1ed40095db95fc7b4d1e576c97f1ed72495db25fc7b5 else 0xa9a4b6c9302116ae95e1143c84595e116c8d921140095e1134884495e116c8d221140095e1133c84495e116c8cf21140095e1132884400257810ca211257845b232884595e0b6c8ca211657811b232884595dfb6c8ca21166e6c9303288459b5b24c0ca2116356893032884595db2590c321169b92e11304845a6e35844c1211657845f330484595e11304c0211657844c12ec845aba57844b9211657846092e4845) else (if i < 41 then 0xa824b6c9302396ae8d5b24c08e5aa6356c9302396a68d5b24c08e5a8a356c93023969e95db04c08e5949c54c0c123964b715303048e592dc34c0c123964f6c9303048e5939b24c0c123964d6c9303048e5931b24c0c12396576c93030487595deb5c5302196578953030486595e1e4c0c12196576c93036485595db24c0d22156576c93033c85595db24c0ca2156576c93031485595db24c0c3215657846095fc845 else 0x95db24c0d92596576c93035096595e116c8d32596576c93032896595db24c0c52596576c93030c96595e1134cc12596a692db24c095595db24c0c124d6576c93032892596db24c0c12456576c93030491592db24c0c124572aa69b24c0905caa576c9302417124c0c128c90595e117ad7f2396576d9b25fc8e5aba526c9302396a6949b24c08e5a82526c9302396ae92db24c08e5aa64b6c9302396a692db24c08e5)))) else (if i < 49 then (if i < 45 then (if i < 43 then 0x8d5a24c0d928d71259930364a35c4930468d928d6576c96430ca35d1f12598c128d71284566304a35c497f598c128d728c4930304a35c9b124c0c128d725c4930304a35c7b124c0c128d716c4930304a35c4f124c0c128d71a95d30304a35c49864c0c128d7125a130304a35c49554c0c128d7125991e304a35c4930304a628d7124c0c1290a35c4930304a22856576c9302c49b5995b24c0c126965b6c930304995 else (if i < 44 then 0xab5c24c10f30566d6c93043cc15971b24c10f30565a6c93043cc15975b24c10e30563568930438c15981b24c1073056666c930410c15981b24c10430565c6c930410c15969b24c10430565c6c9303d4c15969b24c0f53056576dd3043cb85d1db24c0c12bd6356c930304af5002576c97f2ad2576c97f4c0ab595e116c8dc29d7124c0c1298a5595db66c97f28d40095db25eca3400312520d928d2356c948364a35 else 0xa02576c93030567b95db24c0c1598a2a6c930305655745b24c0c15a3a526c530305712751b14c0c15c45d46c530305712749b14c0c15c39d26c53030570c745b14c0c15c45d26ad30305680949a24c0c15a023568930305635771a24c0c15969b265d3030565a6c9934c0c15969b2635303055df6898b4c0c15a5ddf559303056596d1644b8c15965b45912c3056596d16448cc15961b34c50f305723bb93043cc15)) else (if i < 47 then (if i < 46 then 0xc42da77d3030570eb69df4c0c15c2ada77d3030570b95dd64c0c15a2a577153030567e95dc54c0c15b6a526f9303056da92dbe4c0c15b6a356f93030568f95dbd4c0c15a2e576f530305711a5dbc4c0c15c3a976f13030570ca5dbc4c0c15c02976f1303056ada5dbc4c0c15ab2976f1303056aba5dbc4c0c15aa6976f1303056a2a5dbc4c0c15a82976f13030570b969b24c0c15d2e576c93030571c95db24c0c15 else 0x922476c9303ad6586c93043ceb5921b24c10f3ad6586c930438eb595db24c10e3ad64b6c930438eb5961b34c10f3a96976c93043cea595db24c10f3a964b6c93043cea591db24c10f3a96576c930438ea592db24c10e3a96576c9303fcea591db24c0eb3a96576c930438e7595db25f16430d6576c96a590c35d0a5777d6430573a95ddf590c15c8dd16c93b305729a7a974c0c15c4a9a78530305712a65e04c0c15) else (if i < 48 then 0x961b24c10f3fd6586c930438ff5aea576c9303f96aea5db24c0fd5949b25fd5b3ed6576c9644c0fa595db258d303e9657845eb590f5592db25fd643d56b695db24c0f5595db24fd303d564b6c9314c0f5595db24c10e3d569792db24c0f450024b6c9303d12586c93043cf4595db24c10f3d164b6c93043cf4595db24c10e3d164b6c9303d4f4595db24c10f3c16576c93043cee5002476cd303ad25891db24c0eb5 else 0x95db2565304396576c9374c10e595db24c52c4396576c92e4b10e595db24c12a4396576c93148d0e590db24c1234396576c92c48d0e595db24a5234396576c9304890e595db24c11e4396576c9304510e595db24c1134396576c93043d0e595db24c52c42d6576c9304a90a595db24c12b4256586c9304a909595db24c12a42165777d7f59107595e1177d7f411400999b24c1044002666c93040d2ba95db24c0ff5))) else (if i < 52 then (if i < 50 then 0x95e126cd30439400975b24c10e4c22576c93043970495db24c10e5bfa576c9304396b995db24c10e5ae2576c9304396b295db24c10e5ac6576c9304396aa95db24c10e5aa2576c93043969f95db24c10e5a7a576c9304396bb8d5b24c10e595e126c930439657845b24c10e595e0b6c930439657819b24c10e595dfb6c9304396576c98a4c10e595db2591304396576c9634c10e595db2581304396576c95b4c10e5 else (if i < 51 then 0x961f26ad3043d6588d9a24c10f5961f26893043d7136c9a24c10f5961b36693043d6576c98a4c10f5961b25913043d6576c9514c10f5961b34c53043d6586c9314b10f595db24c52c43d6586c9304a90f5961b24c52943d6586c93049d0f595db24e92443d6d76c9314910f5961b24c52343d6576c93148d0f590db24912343d6586c9304890f595db24c12143d6586c9304790f595db24c11343d657845b26650e5 else 0xc56576c93043d6b895db24c10f5962476c93043d6488d5b24c10f5962326c93043d6588b1b24c10f5962116c93043d657831b24c10f59620b6c93043d657829b24c10f5962096c93043d657821b24c10f5962076c93043d6577f1b24c10f5961fb6c93043d6577e5b24c10f5961f86c93043d6587bdb24c10f5961ee6c93043d6587b5b24c10f5961e96c93043d65879db24c10f5961e56c93043d65878db24c10f5)) else (if i < 54 then (if i < 53 then 0xb22576c93143d6c795db24c50f5afe576c93143d6576c9384c50f5a5e4b70d3043d69790dc34c10f5a5e3570d3043d400969b54c10f4aee586cd3043d4009b5b24c10f40025a6c93043d2d6961b24c10f5b52586c93043d6d3961b24c10f5b4a586c93043d6cf961b24c10f5b3a586c93043d6c9961b24c10f5b0a586c93043d6c1961b24c10f5b02586c93043d6b1961b24c10f5a5e586c93043d74895db24c10f5 else 0x95e117ad6443d6577e1eb5910f595e2677d6443d6ae975b25910f5b8a576c96443d6e195db25910f5b7e576c96443d6dc95db25910f5975eb6c96443d6686c97f5910f5969b25fd6443d6356897f5910f590db25a96443d65777db25050f5b5e976c93f43d72a95db24f10f5c4a576c93c43d40095db24f10f4002576c93843d2576cdb24e10f595db24d13243d65792db34c50f595e356cd3143d6d195db24c50f5) else (if i < 55 then 0xaba9792dbd4c1727c82576c9305a929795db24c16a8a36576c9305a928c95db24c169da32576c9305aa28b8d5b24c16aea5e2a6c9305aea577c9b24c16ba95df16c9305c82576c9604c16576c98158130595db25f5604c16576c97f59126595db25fd5c4996d6962446c90f5b8a57865b243d657845b26b10f595e116c99943d65d6c97f5f10f5b6a576c97243d71295e265910f5c4ad67ad6443d74795deb5910f5 else 0x95db26597f5f16576c99a5f17b595db26597c5ed6576c99a5fd78595db26597f5e16576c99a5ed78595db26597b5e1657836097ad64595e26825df591657825df5fd64595db25f15f4c5712c0aae77d305))))))

private def st4 (i : ℕ) : ℕ := unpack st4Packed 54 24 i

private def adj4Packed (i : ℕ) : ℕ := (if i < 15 then (if i < 7 then (if i < 3 then (if i < 1 then 0x1050400c61040460ca0520010830050410060000410441850c30cb1011830420c42850950002801820420020500420c0 else (if i < 2 then 0x3003000000002030c42000400c22430001030410470c000024124c0010c2044001001000002004002040003001040181 else 0x4d04010000108300001200b0000051001010de18100730004125418e08000700004004300600000008b000002040080)) else (if i < 5 then (if i < 4 then 0x81820cb0c604314524100300300215001604a0410122c108214210008b0030850421c10000490422801c8200083000 else 0x800c80020401c01400000804040005410c008004638904008408b1400820081880010400050940431010880070031c9) else (if i < 6 then 0x28304208304304a00330008114008728210100f0010430c00020150802003991001002c40004030012400001500c0041 else 0x21050000090450010000400460850401000840c1240081383008143091141240302103003404002000141102))) else (if i < 11 then (if i < 9 then (if i < 8 then 0x10004100030068600d0410400450d50054560400021090080c304601524328030110c1430c20840000c10024030c8003 else 0x24008010000f00504801c0460000031400c20011870470052014411430800810041840860420061c30840d6005001000) else (if i < 10 then 0x10022400000c40401802020041800cb05c0821850811420411800410c52c004100301b144002040009088041006105 else 0x1c10032850003400c30811411c40031450030030000010400c00c2141348000083004042448000085000012100003141)) else (if i < 13 then (if i < 12 then 0x40000460020010440880010010c62840030011811c01000050c80c50000040820400c214100004500008704218000c else 0x800030801830010810400010410010ca0450010420050c00011010c40131c200938320300204114308c0c100a102181) else (if i < 14 then 0x830410060000000c418c00000a0000000460060c204800b2410070411880d31830010c01400000c4004003000045040 else 0x8200200450300008010800200508404b01804900e0830c32401411406802d910300514018000e100101180008006108)))) else (if i < 23 then (if i < 19 then (if i < 17 then (if i < 16 then 0x10100200a00100104104a0002000890820040c304210c0420400c01010050000411c52c1045043000040043109040000 else 0x4b1c00000000930403421c60420031000400800030470011060c11850c30437440c00c10031012c0000080104180040) else (if i < 18 then 0x54200328104d1442820c20c10040422400800040110000001810030000060c80030451001450430012800011401ca080 else 0x4e1082000040020c20410050810011081000422410801030800041c4082100000003001004080182143082010342045)) else (if i < 21 then (if i < 20 then 0x3410c80060000100830801400000c11450c014010600018008f0810010850c31000ca0000c0002080080340140000101 else 0xc81832000410c00007020c40c00440421011c00400820000002031001020540031c20c1204100347247100002000) else (if i < 22 then 0x842550051c70000040020031004ce04e2c008c00001608208018004000000a2000c11c1b840d5040001105402040241 else 0xc00c20010cf1801c908104000100034f04304a0400080030000c10432c00822411c400b083201000040200082080042))) else (if i < 27 then (if i < 25 then (if i < 24 then 0x8300308014c1c20801862c010208010104400f0c70020c21c00001870000860030810002401421800010410820c2 else 0x400820802c70420401830c70020482c11030000030010c61c9042e000411850070000000420401030000c1083000) else (if i < 26 then 0x1031830440891400400001030020c10c018200204100b04020000000004130008104014400200100201514008b041046 else 0xe10c000500d1883800010010800400010450810423000400000030890450431800c90413010412c0204040209086041)) else (if i < 29 then (if i < 28 then 0x441470030080003403801030001011012030001d20056c52000461132c00052092000801011803822c40021800000d3 else 0x20030011001c73800013c71cc0050000001820410400040433410433400c01424c200610804100000b246280002040) else (if i < 30 then 0x6020440000c304118004538400300a2811411000800081c008b4c100064400400000000104300104b04408010400c240 else 0x3101281080302)))))

private def adj4 (i : ℕ) : ℕ := unpack adj4Packed 6 64 i

private def loc4Packed (i : ℕ) : ℕ := (if i < 181 then (if i < 90 then (if i < 45 then (if i < 22 then (if i < 11 then (if i < 5 then (if i < 2 then (if i < 1 then 0x7bdc8b2003b40c00000bf34000075dc119cc00002862872a840000000006b18138f0ddc45df04160600000000054d80314046a8c0000 else 0x1985809280000090de9037e31f06c80000000000131e25518800006837400001b774455b00001e1c0006f4fe6912780000030969766d) else (if i < 3 then 0x6c79b5db00001e14a0a12162c00000248bc0000000006c86000004d0100000441800000121814948000002eb6324a06c15621800000 else (if i < 4 then 0x77301a6a300000a53c9ba01d53800000d6c10992c0000000006a694303000004468000003a8c15df2760f00000460051d48000014860 else 0x3624000089e1000009fcc97a1c0000086c900000000046209f7288813cf9de9b95000009fac00000a485677c9283912cde97b04bda3))) else (if i < 8 then (if i < 6 then 0x79ef0878088780000000002415f4b3000000198002e8600000805e0e8009a5c4732000004fd08ef81000020c865e11a768000001b84c else (if i < 7 then 0x1a5b700000438c00000c0ea9cac18cc000001de1e9911927746aa79935f42d8130041b8e8000000000000000001054800000f904 else 0xfc7700001cd9e0b70449e12b10400009b618000097b6919c892900000000001afc1000017a840098a304137f01095a52885c6cc)) else (if i < 9 then 0x1f100120b4000010f6a249968f691fcc46e7e868075bb458dc2e101c6b9000010e2245da6475a00001905f31c090d80933000130 else (if i < 10 then 0x4e9b121051ee1081280000000006496c00000000247da5d5c068c1000003910370840000794862d02850409a160000295890f190d7ed else 0x1709d056000000c0e91db0049700cf68035e000018aad21d20251284c6000002976d1e9c268480000000010d540000112cb400f06018)))) else (if i < 16 then (if i < 13 then (if i < 12 then 0x9dfc96440314400000499d00000000011b82000000000751063e8400000f88000001ad10362e260e80000132b4983185660000010448 else 0x8b411326a7856169600000088cc3a0c45faa9bb00000000000453f8242400008df007f3000000000006400c54000000000016635b220) else (if i < 14 then 0x2ce84e3da00000389086e59b2488b8f00000000011a8000000000000002730411378000000000cfa1134e00000000028706 else (if i < 15 then 0x16a10d01e000014b4c6ff3229da71dc8000033d7a394052581f6181b2568b5ea1c002a0c000000000000006bad0000000000000183c2 else 0x137e4000016980000010ee000001dd6300001439500000000070d68000051300f10128169644900000ff5e000028bb3985d80000))) else (if i < 19 then (if i < 17 then 0x7885350490f680000127c0f2e200000000014b1800000000053bc00000000054b899ec168f7800000b4040000198a80f400bf715900 else (if i < 18 then 0x21a19c44c340e6935b43e7a334000001268012c11a1026880e70aa00001ed6d21c0000004c50000002fba5a34e0000159c35c0c00000 else 0xa34040000000024d216fdd611db88eb4000099d8000001bcb40000000010e90694d00000547824fec57968000043841a55e5c16250c0)) else (if i < 20 then 0x20310a29ccb0419d5c000008527e0e1687b2174f032700bddd92d6206de217787fb000000000000000000040e00c7c11b2f80000 else (if i < 21 then 0xbb720a21a2b00000000000000084260bf0873ef4000087520000010f700000082a0526625800000097d08000000000000089121d41c else 0xa48a800000e468caad9370089dca5e845d004252000002e0fe60328309c666479611d0600000243c05a3246cbc6140a1f4f768500000))))) else (if i < 33 then (if i < 27 then (if i < 24 then (if i < 23 then 0x2c06000000000000008037cceda755cc000032b0251a0471d400009896914610000263e093f093d00000000000325690ca66517cdb99 else 0x438127f9b0000265e854169df3f0730000009d6c113e49cb0000000000137645c78244a1000000000000019fbc00000000063b026081) else (if i < 25 then 0x3304903720000000003d8c9295e00000bc900000296da628b4000000001aa8000002421697db11e02a2b7a57e0135c51200000000000 else (if i < 26 then 0x12a000e97400006616944035eaf17176a341e87320000097909a4f1d39c05e2189ad62cb400000000090d5663b2198127564ffde else 0x2c831a7e4812406b2172f3027a9120f0652a58902371c9f178eb9d0b078b93d1dda4fa48122f04c9200000b5a1000004dbc692240000))) else (if i < 30 then (if i < 28 then 0x8968e055000013ab0690c0351e59d5400000000000009b17886841680400009357a0771465692ec00000176f3000015d1383a781346 else (if i < 29 then 0x29c340000000000000665b24d98a5a85704000000e02921a140b1100000fa619364094f05b58400008946800000000112db71a800000 else 0x19c3100000c7cd00000000000001101200802065305901de40381796d683e7600000038008136a45a40000756fc0000000020b23)) else (if i < 31 then 0xa4fa55772531680000577780000000000000294c800001b978000000002594061d98000057c48000047f511d024021a4709000012ab0 else (if i < 32 then 0x8064000000dd0239be5b180b6882dc0400000000270c11bb780000000006f3e59a10ea400d201050121380000000000000000001b2c0 else 0x749009d520000000004435000007f17605f5327040000000019628a3f6250ec00001b990000019fe300001965e0000000005376c0000)))) else (if i < 39 then (if i < 36 then (if i < 34 then 0x6a2ea62e000000b60d0000000000000221e45e8b45cc157b81b24c9023c0000000008d0c00001e18965b6d1f82 else (if i < 35 then 0x2b4c8b4e0579700000863215e3000001b6aa0000000003a609bbda000001f10000017dbc00001cc201d18000002e920f95e489c12582 else 0x19840000092169e7a7000003e8d44f78dc86000000000956c000005cd809a4c00000000000000ff809b248ce223de149383000000000)) else (if i < 37 then 0x24e76000000000000024ec2009b0e65e129c008605fa9cfd1e00001a96800000000005400f98500001edbc5d700ab80a3fc00000 else (if i < 38 then 0x40568e34000000004c00001736660e043f806c640935c6696113670000000004ff012c001a774b34003ea140c88388084807d8040000 else 0x2cb0052400000266467a26538da414010d0000000bff04240482db8ff0000000ba0260e3a5598c4f400420000096ec176e704f00d72c))) else (if i < 42 then (if i < 40 then 0x47230000000001f5215b3680000260310c42000000000425d64d8998210a96300001d63f000000000000016b3c15411c4d3047000bdf else (if i < 41 then 0x9fa0c000000001c0a3277d5949e8a76dd92a78e84000000000bba794bc00000a5c849dc213201135a00001b900896028bbc204c22b86 else 0x9ba4967e65a331a4a9680f802087b4826a421d8b400002686824a10000000009721574b04268588638720072061847c0000)) else (if i < 43 then 0x88a86980000000000000000d9306f918000046eb465700000000004d7680000759c2471c9d9806e077e84121ec83a8dc3dd else (if i < 44 then 0x88c97e418000087a9c0000090620f305518000000061000000000000000000000003b1262ae61c6994b7224b76031b097840000 else 0x22a1665da368068c60f4ec0000180da00001ca4c43e6037837928c0000000020ba70000236c050f095cc2a14417059000000000)))))) else (if i < 67 then (if i < 56 then (if i < 50 then (if i < 47 then (if i < 46 then 0x29c426c4868368135e000000000000000000000007b403ab6827322ed055cec000000000112c22c8043b926ae06c2405a9200000fc62 else 0x8748e21600000157f30000000000e16800005c1820c0f71c49f0de000025e0271a9c4f012e1045b69000000000000018ede550000000) else (if i < 48 then 0x19540945c18b7160c1800000000146c8a166cd9b06d8401ba194f0000000000000000c278000046e8d783c000000000a32bd7770 else (if i < 49 then 0x165713b3c574fc000007c78023189840a2dd000008f006aeda8fc0000013a04000000000000018cbd6ec019ad977e48fadb97a780000 else 0x88391b5f37b04951ea000027d0071d68b41f36ea43e5a000000000132c5505e92b699b294da1a21d1000007ede27345e26279e601381))) else (if i < 53 then (if i < 51 then 0x668a40000000000000000028e913517000000000000003794880de1acfcb8a000001ad161e7028bbd1b9b00000648da5d1a else (if i < 52 then 0x5c18400000000000009da550e1f828ccd4df3a7506fef0000271606957c00009db31e68586fa0275d00001f10150120669e97a180000 else 0xbcf5e3cc000013480000008dde09f6967aa65d6800000000000007b4fdc5e841c05384c8ebdd0040000014411000010a01000000000)) else (if i < 54 then 0x22a0e05d1a34c50c31120240000000004f043dfc80000000000f905017a46da6140e2fbc0000249da3fbbde70081d440000773340000 else (if i < 55 then 0x8678000009180000000000175ec000011fe014a024ab910a84f76c00000000059b006ff100000000076500de8c188840000 else 0x3d6c5da624f60000006219909213c4100000989ca94354643237891bc540d005c40800008b624f839000000000179c95192)))) else (if i < 61 then (if i < 58 then (if i < 57 then 0x941a37782b124247cacd400000000000002803022c013d5c0ec7c4f3c71339434600000fe34008f191da7d68627481549d1d5a else 0x6e168eddb08c4a3e71032f1d5ad1ae5400000000000009b3b000000a37649de000025c5e000008e80000026d92000026f01000000000) else (if i < 59 then 0x6eab1cdbd6a248000000001a54865f6c00000000005c951018b86651a484300a4a100000150f10080000014660000020f3600001cf30 else (if i < 60 then 0x29267000018b408727923611b9619fda1a000000000001e4c20de02938969da153f260378000071484c0f03c3c90c0800001c85d else 0x7bf000001c45a0000000007b4f9dd1832f743a9000000000000000b2216308400000000000002f76d61c0000005d5a000000000))) else (if i < 64 then (if i < 62 then 0x696d909c82e049723c7736c29752aac0abf0a0ea158da1beb400005dbd8db4b00002381c3008000000000025c300000000023c322b9e else (if i < 63 then 0x4744a8a1080ca53d18923817be08bdc2025c2af80000000002873b2fc49eb6600001b3b341f200000000023d216b57400005f9da63f0 else 0x3bd9800005b2111d0400000000000000d5300db00000007a00af802fd05d50a9a7c02f860000000000000000000000216ce00001ffdb)) else (if i < 65 then 0xf7720aa765b3323b6800009b8f01b5d0000265701d49c195d18811796d720840000000000000000010c32114789b8113d80bacc else (if i < 66 then 0x68a19dedc04b0052605c0c400002be8400002f684b9e90000022101058d7ec85290c4c4a26da0000012700ea3c000000000033000000 else 0x192dd00000000093560a8da6a404000041c0000000320800006ca4000004ae026b150000000008388ca67654064bee07ef016758))))) else (if i < 78 then (if i < 72 then (if i < 69 then (if i < 68 then 0x21da10000000000000280331ae253448008c0000032e86076f00000b5723278000007ae20ad42000000000967680000000011460 else 0x16cb57aec00001c510a26780000425a2603c1ea0800005ab8298a1000012c300000000000000000003a150000050f696742a20f00000) else (if i < 70 then 0x28d30000000000000032a019ade2b6f0000070fd400000000147da000006cf159ef8c9065950087da000004e60333226c84275680000 else (if i < 71 then 0x130da63282450900000000058e0d9dc100000000020210777005ed8be21718ec0000588f800006a48800005ff00000000000c691 else 0x167c09def00000399240000000007b85000017ae08fb612c8200000b0db0000092a1000000000a498c98f523e844981000000000))) else (if i < 75 then (if i < 73 then 0x431c271b1000000000581c00000a4c450ca40016c95daa2e18a749000000000000011e8100000de4581774734032f7c0280 else (if i < 74 then 0x276316951400005937a10b31e7c1ec6698d02981e000018340854321aa132e9dbd008e28121ed000000000000022582320404008 else 0x32168d7044387800000baa400009e30400000000000003570505804ecc066802ff980000000000000654a493da000027630000015521)) else (if i < 76 then 0x1a8b443a3172c8000081ca6005f9abc00000435d9889800000999e00001a58994f60a6f63a3808da191b00eeec9bc0176de569ca5a82 else (if i < 77 then 0x59efe232748fc9eb6b1958c006058ec043cc6d10500a97dd704600000000000000000000564366d84496040d3c388a4ddc5000000000 else 0x22aa5e77020679d5aa7384d31863c1842b90000004de042968000010000d5dc00000dc090000000007b0f0c7df000000c00000000000)))) else (if i < 84 then (if i < 81 then (if i < 79 then 0x44dc800000000063ad3d41676e6000019041a167c000034368000088431c7cc00000bf040000000009f320020942e800000000027d3c else (if i < 80 then 0x13c0229b000000130856e0164e06c7c400004769c79e000000000000000374650b20000069b6800009684800000000000004af7a89af else 0x5fd7a12aa22c0c99f24bb7a70899ec04000073c780000a3f190bc81b0840000000010fa1000011b8ca14465b3161ea800000fd347c80)) else (if i < 82 then 0x1b9c0679c02b9e72c3cd65b58af1d5063b17d94906ca00000033e00000053f30ae007998d428012e00000000000000013a100000 else (if i < 83 then 0x29dd52789620400001a29e000000000000021b120ec000000009c0632100000000043e008d51000000000961d800000000289ba else 0x980000048d440000a092000003f67a531970b30000000001fbdf920005e1200000315a00000cca1665682cf22a2c1a1c03bc0c0000))) else (if i < 87 then (if i < 85 then 0x415916f408fd01ebbe000013d300ad815d80672859d4075c5558f643a3271b03a7814f4100000000096b7841a143f80c8b30e3686518 else (if i < 86 then 0x29d20ac8d4540432830000000001f509a48815c0000009892000003cfb22e4600000a35d6a80000004ce100000000000000000010c48 else 0x1d1980000000023b3f6cf6800000000281e08fef206c0108240bb6000006fe9000012cd8271264db39d95000005100281e600000de59)) else (if i < 88 then 0x1b18600000d8730e498000001b01dae20b484b7c127bca31001722063129467400000fd6c000078d78000000000291219701136a else (if i < 89 then 0x10e03000000000310a00000824cdf1517c200b93c0000232f01807000002dc2468db5b701fcda1b51400000000000008f1000000 else 0x5fc16114f273a038e000700fbf5000021b9000001275e7c261eda04620000006a7a02e006ee8400008507c00001d302891a9d0c00000))))))) else (if i < 135 then (if i < 112 then (if i < 101 then (if i < 95 then (if i < 92 then (if i < 91 then 0x6de01030000000000026d323e70000000000000011f188440c742d4312531cc83a4c90d13b5604271000004e70770557b460bb75580c else 0x24e5e00000000000000000000002130075549c6dc0000236402e58d2448a16a67a85a03d80000000000000000005000811c80000) else (if i < 93 then 0x5df25735000007ae800000497cd9fe51ec9000009cec159aa5be00fc5029d3020286de41e12000000fb3d31024000079e12773c else (if i < 94 then 0x1d44887826676969bd000010d480000104630390035210000000005dd81b4c100000f96000000000016069df2a00000510005e193cc1 else 0x59f8149610000000005f518000043999a9d1000003eb00da01da6c000021c983ce4c074600000000081c9c0000308846389))) else (if i < 98 then (if i < 96 then 0x7c8f400000000000004c40c0000372cddcd8000002609000025b04000009a7230e7c000000000bbc10000064008f09a85a1483c80000 else (if i < 97 then 0xda391980e2b0940f6800004e168000000000c7d8890c17ec0000008ad804c106e3d339200000a2e0c64800000250e034884e510 else 0x2260d8dc046bca91bd2c881ce615a701dfe631cc2025a7c610acc98d4a455ec194800000000001980649740000000010e162693815a1)) else (if i < 99 then 0x8cd809d8b50d80c09a84a900000000017b7019470000026591ec692cda449ec55c48c2000000258004260667f06d68677d4000000000 else (if i < 100 then 0x38d7a171f07260679e4c10929da8020dc34c2572400008b660000008d90965a7ed7c9acc00000d2399b20000005a380c85895ac220d1 else 0x9d8f1142335ca9e6398a5c4908326f24d71c684b5e1a159b80000013b2a005e7a9d812635d1b00000283c8000076d6c0000000020c29)))) else (if i < 106 then (if i < 103 then (if i < 102 then 0x4ae0cf2b031d0000000000000006a790000087f3d297400000000042100000061ca8000000f0000000000182f019e6011400000282f2 else 0x8ff8000007de84edb100000e88000002389800000000000001bb5d000025fc952048000049440763c000017ed400001ba10000021829) else (if i < 104 then 0x16c0000009e200000000000000060cc66da1000011dd123e0400000000120490000000008c3c80000474b408706dca800006a531d3bc else (if i < 105 then 0x68884000065d32393d0000155802674ded2d8239949000000000002f3ca1d00325017c563e129f4a1a040c000056ca8158607d7486de else 0x20fc09fb6000002936a30e075455ec3e41539b3c043804b65a0000000000000123c830678e6831b2f40000977c8000000000ed6c))) else (if i < 109 then (if i < 107 then 0x898064989000011d6900000000027969468168b6e87820cb78e5b000001a750154f11b0019671f95f00001ec9c5df000000702780000 else (if i < 108 then 0x83f4dc05d0f41a3484000011c00000029535a404a8cc600001d5409047a944c9bbc0d4390000000007798d99585ed500000127180000 else 0x1d0c08927091307dc940000a6601a9960000000002984000009560c000000000211e0000000dc6656400000000035103f6ae7480)) else (if i < 110 then 0x146da27b60000000001ba2300000103c4bf248cda0000278f030e78e300689680000000000000000000000000011619642a19dc6 else (if i < 111 then 0x1f8c000002d841882a50c067f3366d706c928608cbf3c3cd8128de00000000090564f8d872b4c00001b4711ae94ba0165019b1600000 else 0x74d04000069c7e850d94c724418491d0000087486206823e02995a00001869f000004c0031d699c48000000000000028499123200000))))) else (if i < 123 then (if i < 117 then (if i < 114 then (if i < 113 then 0x76ba20e81000000000324a40133000000000000000000975b000009363c000001a0187988381800000f530cbc084c78b79c464016792 else 0x784311ecc3b61d744671c79b8811ef18f4c00000000000000178c75c17c5a5e00002846078b1c000000000d3214f9780090000000000) else (if i < 115 then 0x6e1c8000000000073c000008f5a6c8a4bf806d168000021a02913365dce13904d0014ada1f6a00000000020901000015872000000000 else (if i < 116 then 0xc65a2f96800008c1c037901819800000000141c801760de630000000009f9615e72000023f5881d1c0000000012fec1c66c0000 else 0x8136851c148f24000000001aadd8307802120000000000000028c95a905f6417ccecfee774800595e359795a74347740000a1775c98c))) else (if i < 120 then (if i < 118 then 0x7bb9853a15df98fd5d00001b210000018ddb000001b9e00001b9cc57c4c0000000016a803f57c000000001933b3a6c0000073ce41570 else (if i < 119 then 0x3d5621b3c0ee40fa540000000007b1c0eade00000000069018da808d1c01e860000000004fe0070002da840000000015b76022611323 else 0x12edb3697800003336800001d2b4e9f2a4384ce720000000000000198de605684cbc95f24000000001f240000023ff200000ea48)) else (if i < 121 then 0x1dac2000020ba90000289f30000160c90e970855a040c00b5b4ec04c08613bb2915300001f34106c400000000000000 else (if i < 122 then 0x32d3124750000290880f705589c98c00cb906c73000008bd8ddb95836858bbf07a84c791000001a9e5fa6a6cf02c368fb98968040000 else 0xbd21000009210267909f7600000000095a0e4aa98ff1a9489766500000000000000673b25289a17d40000344304900000000000)))) else (if i < 129 then (if i < 126 then (if i < 124 then 0x5cf002d1e0000000008c4617a210000049837cd15c74c0000288077b4f0000000000000045da25f725ea48563c88840000014d000000 else (if i < 125 then 0x9f2c12675334012360000005c080cb687dda0e678000033d68000000001f6c6000002564263a06adb83c21b25a40f24000046804cac1 else 0x419c81b216c944000000000649ca18240000000015d8186b801180000000000a376800000000000000faf400000000000008e19a0b09)) else (if i < 127 then 0x94a70d48633930000000000d8bb9f4c12242527c80000173004266098d0000000001d60900000000040b6a2d0157dc000007c1000000 else (if i < 128 then 0x2616800005780e68f26250551c82e18c00001b5742d9e0da0c00000000252e077c70d7950000000007be1839a0996c17048 else 0x3f67612eb0000252f13dc0987213cb5000006d93053809a2f06fc00000000005479059320000117817aeb40000466540000000008ade))) else (if i < 132 then (if i < 130 then 0x2deb4e5df0000177f0268a0000085590a3c0754601f980000000006d34d1a810000000007eb7469a1000010e698c610b59000001732b else (if i < 131 then 0x8c0115ac2927002ec19e40012f05af1a909209d623a4017244000059c0000a164e804580a1284a9de000005c596a10c3798000023695 else 0x6100cf8c0983bcb29b000000000511014242000000000912cd3c4900001d60889a187f400000216600000000001ba68000047c6a7708)) else (if i < 133 then 0x86dbdaca1000003603000003f000371a21480000000004608584c21a80133820000169e059e11c45d8ae864a101fb000000 else (if i < 134 then 0x968613db00000118926fba18f980150109726e0000000368f1c3e93af7c86f20000000004198172601b0fc00006fd314c5b2f6a015cc else 0x27121cd241470146d206240260b000010e48111c800004480dd5e959904000022775e98869e5a8575000007e046f7a07db66c8900000)))))) else (if i < 158 then (if i < 146 then (if i < 140 then (if i < 137 then (if i < 136 then 0x23fe173144b21e154f40000838e1a99e3d77800004d211a1de5c074b0069e084c4a888321155a000000000000003300868580000 else 0x72d4800003fbb9360041e00f6d500001b34672f69db5800000ca2d30c79e6f0000006ce300000000071c8c9b237a4fc000096008652d) else (if i < 138 then 0x5a9603c104b56a5bc23e78400000000000008e66042690000000005cd682551000011eaa0000000002f1c87cb051b6cc7b0000000000 else (if i < 139 then 0x7adb68283000007aec0000000001bc10cba27ba014d5b792ec00002404077007c800000054b80000000001ed7152bc80000 else 0x2709239d68000023f46929c6cf0494b136c65189f87728483d00000c16e8859000002a6000000923500000))) else (if i < 143 then (if i < 141 then 0x646a488809718128760000000003e60e3c2834044000000001261f553c9aa900000000008f3040000000011d507a5b4000079481b690 else (if i < 142 then 0x43a00075ea176a1881434c4000093b0000006ed6a2f8450f80000000000000002d60000043578a24c00001ed6308574ce0c000028919 else 0x27d70ef8308d80000026a000000000022321610c400000a72099960b2014b5a0085400005613000004da307912000011b0c000000000)) else (if i < 144 then 0x10a602667d285a00000f161000000000a2b61585b6e56800000000289526c879d5c101ec289257a820ab5a8c1a40000908280000 else (if i < 145 then 0x24340000000000000000d210bc026bc015000db5900000000073f01bae0000001301000016bc05176d45004e5083e86004f6649a else 0x5d78095c81b4e000006b54c66d196ac10e1980b0215cc000022021523896ff73b40a594966364522a64e8c000006100000000001de47)))) else (if i < 152 then (if i < 149 then (if i < 147 then 0x313acd05000000a804517cdd58892d78000047a00000024a60fe368d0126bf285e1000000000000005437878695c1100000553000000 else (if i < 148 then 0x2733000000000026374d787000000000780a800004674a8a807c6f07b813ca4e139e10221d73f00001057511701d5b84ef5223b0 else 0xd78a000011be086198c0e700001be680000113d403200000000000b9c89926064a000002398000000a5c63670000005db88c6a1)) else (if i < 150 then 0x5823400000000288809c584d18ca15ad94232ac00ef80396008d908486cdc1e000000c8646a88b86900000000093500755a892100000 else (if i < 151 then 0x2ac0c000000000000000000000031c40d6061988000000000000005bfb11d0081d4cf0640000137bd6302060006fa00e130537699129 else 0x3a9506a2300000000029b3244da6a24dce876d13161bc7b2021ee469e800000340d800009d4c1eb76708845b183196d0d705f97a2f41))) else (if i < 155 then (if i < 153 then 0x363983ea98a6c400005496ca160000002c1063e1a50c200001dbe3000000000511217e9b59520fcb64bf691b0422cc25070557800000 else (if i < 154 then 0x262f215a0000007613000000000101104116920ec2970c65e3752fc000000001ca100000028005a801f18928d687009192240000 else 0x9be0000000f369f33f00001a55b25178af00709700000000012cdb0000000003f37c000061bbdb20200000cd8c12901a01800001c5cc)) else (if i < 156 then 0x302fc00003ea00000049b7582e08ee84000038701fba883c8000000000173420000086c80000273460000000001721800002de111f23 else (if i < 157 then 0x4a6000000000059d31dddb86fd40000540046ce000000453800001f31596e0449bc66f2585b294b0000000000285ae620480000 else 0x1469c00006517195a1170180000000015b0c313a800001ad04000000000000079400000000001c6dd000007e005cf61aada00000fcdd))))) else (if i < 169 then (if i < 163 then (if i < 160 then (if i < 159 then 0x5a0f1915f912e40000000023a589979d5b98497d8c85b91c75701b0000000001df81ffdd00001326220f600000439724f6023840f7d8 else 0x4f01400003888501da5851c0000574c5b18914b00fe42796800000581b4000000000c70334084000000000d9863696de102) else (if i < 161 then 0x3e06a0e3c00000000220496e4067531277d000006f57458022080270bc324cd1baf000013a831b18d260c68a406e28151c00000 else (if i < 162 then 0x2097e8db02487a92a07d2e4000000001f95d63d040000000010fa39260a5e58000005fad283a11e483e9b0000031f7462e09823e2924 else 0x1df040000096900000276c01b2b4318040e0e412055bccfd059f6cd2d007abd94a39194561dc83b810000037c61f448000000000))) else (if i < 166 then (if i < 164 then 0x97b7400009941a0ea1a16649b803d161f8eb00002081643529208500000c7d354265679c523825f497a680bcda9780513850995c0000 else (if i < 165 then 0x654a25de031ed9ef750000291e989f3998daa13ac00009fc4467a1000012ec9912a400007016899cc000000000267747ab0 else 0x211d4cd014bb68000055e4a7a3047f48f87300001275b00000005a000018a880000167130000000003181a4c581731886832cb603810)) else (if i < 167 then 0xf19db4d871698940000000000844ac000069c80b83c47f20000004a26101876109702fa0524922187a840000733611b6900001250c else (if i < 168 then 0x33d5c0000424011401000023798338850c05199d5465a5ebc000008c810931e0000000000000000008da840000000010180000000000 else 0x21ca121e0c0000113615eec22b240000000024c9036c50000000000000000000000030a7a8c9777ea8000050b6a4d9113c24f656)))) else (if i < 175 then (if i < 172 then (if i < 170 then 0x5c0000000000003b5a3bc52574600002108052d7d864a80f6c1bda89e051d08426004073485b67a8300000000099b862e40000022749 else (if i < 171 then 0x5760c00004040c00002432c000083a600000a4f600000297d993dc0000057b06677185e81f1680000000002a482eb200000328600000 else 0x3008400001d6a0deda06f7647283e12c00009a9c0000095b01a82c0000026d029170000000000127000001a22997800000058405bb80)) else (if i < 173 then 0x579d1949802c0c62bc134f0000000000b7bf0000252159b7c2219087d99eea01b104a45a000028b5400000268c000000c46000000000 else (if i < 174 then 0x1e83d0000000006a0091b581155c00001b8fc00000a630000026200000000000000000000000000002678000001c3e8a19dd95a9 else 0xf4089b5a00000474059d0000003597c6f8400001134c9010231c01eb69385b0000000008cc10c7119e73c2f9200000000019f700000))) else (if i < 178 then (if i < 176 then 0xba24f33c8a80669488204c8f2100000000068a60000000000000025210781843e800b000680076700000289f2000010a756c649c790 else (if i < 177 then 0xec078dac0000000011d6000001b64000000fa6055700a6c67978c00007771d98588789c000011a180000608027ede45e8d6860 else 0x6407a6f837cc6200dd000012e3046c0800000000000000000232bc06a0000007ac48000000000a0e900000612032f6841701bb12991e)) else (if i < 179 then 0x4b8da000618dc00008b400d0dd7916a99a162905ae180000000008230400006c894000053180662300000c21e0000211cf else (if i < 180 then 0x644a0fcd00000000001b90000000000000007acf99c5c51700000071a04de834680800000000022900000000006fb75d55990d180000 else 0x8e471b2867b855d7c007420000067c40000021800000029ec8000075a54537000000000000000000034e410e12000018b8809d41d32a)))))))) else (if i < 272 then (if i < 226 then (if i < 203 then (if i < 192 then (if i < 186 then (if i < 183 then (if i < 182 then 0x4e044c3248682118f00000780718be03a9781f21925683da100000b83d000004ee05ea2000000724060209488277405d5796430 else 0x1b5129100228d1000013dc05f2b66f047ac81b22803af270c013ef46621512c1236460ec01e4011f000000000025b7626400fbd0) else (if i < 184 then 0x5f6000001b781000000000000015f610000261d4000011fe32112000004f4a65be0000006cba0000000005731050e08f2000000 else (if i < 185 then 0x6f2000002225100001feda8329dbe1200004000053b00254c000006ade0000260923416c00000000000000000000006b0c27699 else 0x78880662d4c7925e890000000001f0049ae12c80985709b900000000001074800000d6002788cacec000005fb2000006540a17ac0000))) else (if i < 189 then (if i < 187 then 0x11c800000149e02bc7800001256800000000212f162cf2948071d45cf3d5e5c00000000000000287a5ad5a8ed04642d5fa8430b3 else (if i < 188 then 0x5ad8000002cd184c4b0000000003ccc400007f6ccca9ca0c24dae0000000000000000000000014106000016795a5536900465ea123c7 else 0x75f340000191c000000000000002e931ee3e837827c0300000000000000057031044000058330000044f94bd5a384a5f05a683709a50)) else (if i < 190 then 0xa300113ec0000000000000133219c2f49a18447a4000050cf25e604321800009043c4784000002e105f6240000000028f581b0826240 else (if i < 191 then 0x3ed80bb00000161848df05892d96d69d2bf9236800009830188e62bb800dc08bf806b9285d21f3a11cd05a45a549680000 else 0x5c3000000965b20e397df7c94309340d168000000bae168770000070b6800000000000009c2f800000000210360471800009b3000000)))) else (if i < 197 then (if i < 194 then (if i < 193 then 0x1581d7f2400000a608400001b6721a1298fc9055a8496c0000000000000606c1a12300001424883a8002329b0f0000055502274e else 0x9907440c060ef001bc8ecf9a55a00000c4a45a98000003d8c0215a3400141de435680000120123d096db31b01055390000000001568c) else (if i < 195 then 0x5a200000089408a31000000000000000000000000000028848e55e8d2148bda0000000009be18000045c7c000000000000063900c55a else (if i < 196 then 0x811f71b6df3000008c1020e0400000000000000f8f26e70a7e5e07624b8044c93c000088c48718052b6d1fc6000000000179767605 else 0x3cdb0000059d24000000000000000000000000001b74c00001f0dd0320c3e885b5b854a1000010cd06a058e383541309a2300001c653))) else (if i < 200 then (if i < 198 then 0x648a0c5db162c9e70800001ca002e88681a9000000000000011bf22c94000003bc9000004287c000032f30000062b980000000000000 else (if i < 199 then 0x32904000000001922900002764814dc9208392c0000009036404409198024dd4388c00003e80400001be20d8bd00001117044b548adb else 0x14b0800002de0000002ea000000000013e307e444bbad8f49d43865ee10000081e8400000000000009eec68c9e52d180000559cc0000)) else (if i < 201 then 0x8368c00002f770460a63cc4e583582405dda00000ecec000028bb200000daf00000000003bbd800000000000002dfc087c806a427670 else (if i < 202 then 0x7ac3400000000117e83b1308f1070dc8be1066f6a70bf29569a7f200000602d8ae4410602acc22451a4afa1eac77b6df2415e7c40000 else 0x9cd00360400008648c7db0000010f01268080000000000000000000000000010c65811680000354e40000786fc4ef2))))) else (if i < 214 then (if i < 208 then (if i < 205 then (if i < 204 then 0x75f70efc89a560000046c18000000000000000001ed696ff74000000000000000000a646838004f7046f300000a357a64b237685fabd else 0x964c0725a980cd2a5a000019b480baa000007db0000000e580000000000000078600000000000ca00100186f8004e12450009e625b05) else (if i < 206 then 0x9aef10cb01b282168d8ae000000a504000007898c6f3f000014ff42678207d100000c0e300000000083a54d19e0000000002fd8cdc30 else (if i < 207 then 0x15f0173e153c3685907260004e014061b340035b40000596086f951ae100000124f0702d000026982927600000705690c5a000006500 else 0x73974e8d400002453c7c654000021b60bdde00000000053f6800009c2008d10000025b8419d751d4a0000086c2000000000467464983))) else (if i < 211 then (if i < 209 then 0x240840000508c000000000207451a500000041431a61000002348149bd4000000000000057fb0000000000b9080121000004318dcc46 else (if i < 210 then 0x3b92000005990138db0fc091ee890c092b005ce04000025644764057e046fe202a080000000000000431500000000000000310e40000 else 0x3a9240000000018d3e45dc800000000141bc43180e9301e049d33f89204000000001adb06ce252eb081f4cf1e0689718055000000000)) else (if i < 212 then 0x6923c00008e5054e5b000000000411811d0994c80000000001440200002180c000012b061b3b2259200002798084078209093304805f else (if i < 213 then 0x1ce8ca345c3d107448400000000161be51949ddc00000133800090a224c0042638c000000ab84750a9b5ee000000000413806e38 else 0x4bbc42885ccde0000276c62d1a46392000022b5c1be840000155264058161a4000000000c0eb2f169fb400000101212cf680000)))) else (if i < 220 then (if i < 217 then (if i < 215 then 0x1a885a88e4de8519512e061c3cc71c0569000ea7a77c269a02651a23c60000028e0c000063ea64b905cfb0b25100001d7e900000edde else (if i < 216 then 0x2037c6780000000000022fc000000000e6405d4c025603568662468c5c171822a1900000000008d5d00000000040e090c72 else 0x8e42610546768f2321b571011e00000000028b68837000000cb9ba080cce122664980407c2a4023d00000f431449500000826840000)) else (if i < 218 then 0x15bc000003ef9dcb28013c0dd2133d662e703059e903367bc000004037800006c924c5800a7440000000008e000000175e678a84f2b2 else (if i < 219 then 0x2ed78ea026946062f162d05bf687b0a80000a32150ac805c1807c07a435932100000000000002835a0000049de42d6a85f4 else 0x3da01787051c18000000001bf5d0000000001dfc22b0600d000000000008c8c48a7c000000001298024574d25a9100c00008da600000))) else (if i < 223 then (if i < 221 then 0x3a9694cc05e51939e65af080000000017280000009a2100000cba9162f17ac643c223c0a5627400004322000000000010bc6a67c0000 else (if i < 222 then 0xd84179322bdc0000000002360181583256c494879f2689000000000000000000005401d0c3d0000200c009b210d491ca185ddd else 0x34030d4b960e10dbea365020d211bda4169a7033189bc8a95d753c00000000000000d8a8146f000004e780b4488ffc00000000024300)) else (if i < 224 then 0x257258807555cd2dc5e2f00000630b50e609690002c0004f0000000001bd8018ba400009b6689a691260143bba2460cb5a000002961 else (if i < 225 then 0x1375b00000d55c000000000a1234ea0309f7400000000000006a5a53981105b4b88988b280000019c00000000009be0000000000 else 0x54c8690e5dcf4134e400000000075190000000005013a1125a2d61e8012a1b0000000001c4480000074d800000000041d680000)))))) else (if i < 249 then (if i < 237 then (if i < 231 then (if i < 228 then (if i < 227 then 0x87d57b315224a6770264328c03000017e80000000000000021b0852d7800003b66e03d40000112cd75479f9900000000008e3c40000 else 0x36704494037f7dc9cc000008f1e49d1c834300001d7d2000027cd43e248000093f001f0036c350cb246830acca00000fa04725686e4a) else (if i < 229 then 0x22368000000000000046a7c00000000061b08c9819bc8855415ac377b61b6287a8ca5a045fb780000000013e0300001a8e856bcd89f1 else (if i < 230 then 0x1fd228460dc8506a1188890097c8000000001a8b70ba865b010000232407f7697c403717d4acc24641736c17db1ee3c224017e98 else 0x79bb400003ff24000000000000026990412da177000000000000002613255c02b3704e921281182c00000049f22a4000000))) else (if i < 234 then (if i < 232 then 0x105e126368000000000000047e3000000000000002c92260eb000000000156f1eca0a296c20ae0000000000000113f2000000000 else (if i < 233 then 0x96a0e96459e6b580544a171a65a89cc4b78900000a75a8057c000039d01afdd2f441509000000e1b03f2ccc880782c1764600001e827 else 0x7566000000000000009a5d3f5a25700366ec6daa9a0f007494f121b3dd00001b3db000020521371712c805f0f69608)) else (if i < 235 then 0x6a220000008f6a33845fa0952f23b602709c0000023a147b8227ef97ad8000073a34000070d4556460438165b0000023af12694d663d else (if i < 236 then 0xdcdc000023c82000000000000000000786828c540000000000000121c200000ce0177102318027f00000074a60000043c128ddb else 0x77454000000001c11e7ba54189e74aaa45802510226d031298756989c10000094aa9f18100000000017600273c0000000005cb800000)))) else (if i < 243 then (if i < 240 then (if i < 238 then 0x18708000088230000000000000014500f6e14e505c1da0000000007c884c9980000084010000227bb7bd44000000002999e180aa0b33 else (if i < 239 then 0x11c5a00000c18084978ee8378c84a11285f38c5c9000008180000014f10000007e8384e80cabf7ba4a21e9000015bd400001eebc else 0xa397000000f802945aa13a0343072f4cea00000015be151668f78000001ea3e35a1a4a00000019b4951579ecbe9c2126089000028806)) else (if i < 241 then 0x11b816550400003af0108810000118e07a3a4af1805e850a4800002594654f88000075e25435a3a108439458db28d6d5433a1772 else (if i < 242 then 0x81e9e8b80000004f6c00000000037748d44100000d0406e201d2c18bc008c5a46801858465f31a821000008ca31eec00000009000000 else 0x72d323e8139ec1eb3071c42911400001ec32a55745b800000000001ccc0865a56048000000000e0df9d7b0000061b0c0000076811068))) else (if i < 246 then (if i < 244 then 0x64c8c761591a0c1d0900001ae5f00000752192024355a51bc815dc00001ed156cacded410b76800005a449b91e000000000 else (if i < 245 then 0x270e01a36800003bb212cda082a5547200000000071adc000080a411b2300001a03c506c16c853def1ea800000241a2024253dc1 else 0x1cfbf0000000008568677308b501b5413f0dc2f0601169d0c51b7123ab70000080290000000000000000006fa05d5c0000000000)) else (if i < 247 then 0xff1919484f40c000000000000000000a40100000612a67d300000000000000300ec135856018935d4ae1870a000002192029b6c0000 else (if i < 248 then 0x9c500000000000a04000000000039d78790491dc9945d0d800000000001f371361da29332c100582d56e1c0000a3625c5a13a6c40000 else 0x65f600000a2404963097ace3ec000000b7040000151496ce4229400c00d2b30000018c669a800000000000000000001b25d000012cb0))))) else (if i < 260 then (if i < 254 then (if i < 251 then (if i < 250 then 0x635000000493240000000025e6c16100000026c400000123c255001cb0458d80000000005d124324000000095e03ec000006fbd5eebe else 0x980f52a1e000011be9294cc000000000e1dc0ed316db05717800000000000003826d35603188586d8072a1e8a1557c87ad87be001c9e) else (if i < 252 then 0x32e7800008c000000000000000000000f48340f3140b4997c0af9e7ac6000009ef7800008ac4583e000000868100000000078b140000 else (if i < 253 then 0x4118558c600001d2b8087a4000030e815f6d54f8179c772285da824b801614842530a38051c4c9a0098578c30097a6cafa000000f1c9 else 0x83f615df62476a724697724c4dc4321e23a31dbc20b8f0c70242230000280415b90270f00f932105a000028b7000001d5bc7b4100000))) else (if i < 257 then (if i < 255 then 0x71aee49800000143bc199a4000000000000044f8d2ada5d60c00000000172ec0000000000000134920000000000000055215fef01f03 else (if i < 256 then 0x3ea0cc28087f9812006c94000003e801db7660b1808aa7d19800003f9dc0000000005e2300002840d0000241a085d304632641700000 else 0x7fb740000198300000a2c0a720400000b25d0000000007579800003a61526f49a5020211000008376000000000000012bb093100c3a1)) else (if i < 258 then 0x360021dd0000230da9ee0e5d463ee7c00008e702011000000000047c05ed6000001333984b110e2885884000036d8a178d14304f7c0 else (if i < 259 then 0x88a9e3aba29e01815e6eb1a42081e30142b0504d19cc10fc220d5a269a0e2550000066da00000e6b09daf2768656c080000363a150dc else 0x5020049c800001b22700001ed1200001e6809638030000ca012a5c00000b9416a2d800000000082da49f68d15c6fb816ac0979000000)))) else (if i < 266 then (if i < 263 then (if i < 261 then 0x8ccf0000000000b24c701c89ada89125603036a84000041540d61e4046c0000a4a568ca79e5c103900000000002220c0000000000000 else (if i < 262 then 0x1471296cc000002cdacb32d6c6a90c04926400000000000000000006fe073a9c000023400000078694000000000000038b063b8d else 0x978f11b0100000238071c8438d166968f26c000009981a4f01e963394d800007a50513d88f9500000a54f00000000000000)) else (if i < 264 then 0x22e00000014b592663016864dc4860aa000003e0869c880000523c860ad64378d05d38570000000000c45d777d40000560414506 else (if i < 265 then 0x3e978d8bf000009f5a0000000002e000c1a188e9c00005d1040000a567deb70000005dcc00000394c0000000002dc2c0000 else 0x3977a38a11a300000069f406edb1660c00001c08d5d5b9d810000050018a848254001630a35351a231d3a5fddc6b97485039adc14205))) else (if i < 269 then (if i < 267 then 0xbf3ea2000d9293946cb7c000000000014461fd645336a07a900001c7da265d5827000001d55c00000000000000000029eacd5df else (if i < 268 then 0x4c99d41482df8dd03d97ac1b8a1000000000a20c8000047530f8e06d4b589c07a131d43f000025c300000142763e9c00b9b000000000 else 0x6f60642c01a678b05e43c020c88467713a9b24e85a9d071580dba800002474000000ca9846f6800008934479700000000008b8106fbf)) else (if i < 270 then 0x888200002030300000af20000010e006cc180000000000000000000000555900000000000000878a800003c92c000000000e240 else (if i < 271 then 0x1ea0cf6e463504ea5825000ff82559c87b23000000000572c62dbc00000000000000000069a851be400000026da500c00009cec62027 else 0x5c1b0000032c61cc7000001a28000001a328a33b80000000004d6a74a24000046e025f5a9326000004749a574000001d1a12b98172f0))))))) else (if i < 317 then (if i < 294 then (if i < 283 then (if i < 277 then (if i < 274 then (if i < 273 then 0x2685194c34b01a54a00000000000000c7c000000000057504067600000000086e8450c05dd007b252b84805c03f7d482de7f9764004 else 0x1020920d40000260993d00268c044c4800000000023720000000003c6c1a91e87b28af2136c1c0a401f10a120358649efc0000015db0) else (if i < 275 then 0xb480a70c0000178f16a7a637a1000020f2117d24000070a7a858d5478a0d2054161011863d024a09552486e2594119d2f040e300000 else (if i < 276 then 0x1ecbc0e0002a5d8b00800005196d70c8a33cd0c7600002454000001c1dd00001965f00001d3bf000000000687768af600000dfbb else 0x31b6999f64ba094fc9000000000a34c0000000002637265f68fade164f000000f835e375000000000000004218925ca09a083b845670))) else (if i < 280 then (if i < 278 then 0x435c800000337800000000145900000127dc18e207d0103a01110405a853b0300001750600001d2a00000150db00001859c73701bc01 else (if i < 279 then 0x9ff6a77da172c124c09b0f5295b3736800006b16a903d44cb4000029ec26cbc997180000000009f6c000015f62694780000900044700 else 0x2f48c00009a1c17ea96dc41e73f755d8000000000a3210000231811272567726ad7400000000020af00001a0860000000007c27996d8)) else (if i < 281 then 0x3456800005f924000012b00000000000000000001f868000000000000000000000010c4066ec497a16f0006509152f2155100000bdb0 else (if i < 282 then 0x8e9000001eb63000009bda356e4000000000dfdc54125040100000bbc651f80000000000000097aa4000056e080000000000000 else 0x577691b1fa17c800002961a361867cb874280000057405116970496f3740a04000009a0c00001f3212e7a05d4c2556800001bf8c0000)))) else (if i < 288 then (if i < 285 then (if i < 284 then 0x59d6a081272241124018a00f6822f17652bd438b60e095834282da7cbc09a8600000000085f315a9c5d31a5d302da24f1d4344780000 else 0x13bd9e8a7000013e060586216230000000009f60cff6c000000000000015a4c189a471184614259e1000001b908e83400009dae40000) else (if i < 286 then 0x60cf40000a418014f068ca4b4500c10065601b2fe3ba8000000ad80000000000e7a0d360000000c4071448000000000b1a100001706e else (if i < 287 then 0x34061dbf019c8e543c84c41bbdd05d0167052d435368000002072128e18325e869440000667b0000000000000000002869f883820989 else 0xc80c86da00001015d0000000009c2b4000000001ecad96dc800000000251c000000000000100578845320de446b0a62fc0000000000))) else (if i < 291 then (if i < 289 then 0x8cd06005d7c2849f67f70000032e94000024a7917643c606768b70878473d0000140ce53d79e620000019d467ac01076025641e35f else (if i < 290 then 0x3aa75cb000000216001c105396864f0757c22c039baf09e0d35370000023285066c83f3c00005851843724b20cf46c564400000 else 0x22e00000090888c0c647e0299da6a218e2270000000004d8304b7000000202900001db409d9b4cd810000000000000025da)) else (if i < 292 then 0x8be01d1b9043c159c200001dedf26e60c16836131ac9000000000007e063f4664a841688188b40000a341a5ede292321218000000000 else (if i < 293 then 0x64764000054990c69b00000000000001905e0000000000a85811f063919f40c05010000097b703f8600001470000001f921725c81084 else 0x2dfc5134672200ab4000001bf90449684ebc8b211da949076000001f58000002900000001e1c23fd8452026fc800000000000001b921))))) else (if i < 305 then (if i < 299 then (if i < 296 then (if i < 295 then 0x68ee5ee9839800000000001ee9c40f200000a438144497d86400005356940bd00000000046f2019dd7c62e38892b63e1c00000000000 else 0x3be15adc03edc821e803bc215230000112023b06405bc26741bb9e00000000000001400087c850f60000000246051c10129000015cee) else (if i < 297 then 0x78600000a0922c000d871000003be888a480000722e613128a80800008ae243d9e135b94bda9cfc0ffdf000000000000016800 else (if i < 298 then 0x6ae1800008ea405d810f2c259020000000000000052f059f04ff0200000000000000000054d19e58005c68000028a023400000022f04 else 0x1bc612472869a400005717c5ed075306148c6e800000082080e9e125d68f748172cc212107e0283df6a31099c800000f348000011faa))) else (if i < 302 then (if i < 300 then 0x16f664eef06906a6484b3006f56971601bfc1184c02b7a8d1100001ecaa00000000000230000069e881c5b3e80d594c00000d941 else (if i < 301 then 0x24bc000001e821000006e457b5c20e018ee2400007568000008f404000055b20000093d0000007b080000000000000089ae66d04 else 0x230a4b680139b27230000000000752a9070295f227ad80000000003e7da97da6fd69441051d2000004f86c000000000f6f2000000000)) else (if i < 303 then 0x941b0000066d5239896bd1e055d3c95000002296800009ef6000004fb7800000d76a95e600000000037480000062f052a86449600000 else (if i < 304 then 0x2400000005b0f030988f640000009084f3ed7eea6478051e488e928f684ef4e8929c00001bd0001c600000c8307d28c00004af6a2821 else 0x2ee8deaf00000000003ba09ed1800000241e782c8000044aba529529322873c00000b0818a4c881b668800000000002280c17d893cc0)))) else (if i < 311 then (if i < 308 then (if i < 306 then 0x2c77000009520622cb688a031899b400fd69a00c800a900001fc101d7a53d3900001acb094a801dbd790862c00173bcfc30000011364 else (if i < 307 then 0x9b674714b9c000ce5102d78000000001ad3069c597e83133818a3c0000000007542000000000000003dad173c600000000000000e954 else 0x63e849d4818cf41e463bd14efc959f8dd29e14d784f120000067dd0000000003c2f0000096d81f910236e4834d00002051e838859e40)) else (if i < 309 then 0x425416ee00000099f547b400000a3b34637157a14fd360e34131c97a7d9733100001cd0c1af806ddc9f016564000001860d000000000 else (if i < 310 then 0x545c89a6600000000017884000059e01351200001823c0000000000fe09943b0c40c00007e400000000001e01068b7c0000 else 0xa066c00003c8c00000000027cbc00001c79e5a9002ac8673000000000010a00799b54f5b000000000a2e089848588480000210306fb9))) else (if i < 314 then (if i < 312 then 0x52f79b4cc2320000002e0200998000005cc41cfc05e0c400f41540000022e805c9c0000098cf1b0dd4780000003cd5018361181983c6 else (if i < 313 then 0x4c980ce0000002550124ee60a0989f407203000026e8400001dc634012000008bbc0d6410000152da00000ce5a001600000000004960 else 0x7d4cdf38100000f5c900374000050d080000a4af400003e925b3a8000017d540000000004a2000000269680000000004ecb0000293a1)) else (if i < 315 then 0x1bef48c0096f68bf008050cd78069878000095410e846000011e928bb81b6b91b824be5114d24dd2200000164600001eab2 else (if i < 316 then 0x74cd14e10000196cca3ae5228c14a05077200000000000001a6923dad9e9a69eb78000067125abb0194208fa3151800000000028468 else 0x995d4318a005d000011b920ae000000000025e464b81870331a01a8d768fdc0000098a12519c08079e1c19fcc10400)))))) else (if i < 340 then (if i < 328 then (if i < 322 then (if i < 319 then (if i < 318 then 0x96fb1c19e62b828db371b6800007aa8000009c3a53ec8000000000000004f080000132c8412000000000003ec000000ef47000001a1e else 0xa178121e6964c400004400155390568c0000972c1a9a04333a5fb02614a30e16c28602830000194214dd69d6b9882843b10000016eb0) else (if i < 320 then 0x920a00000000000000000012f3c0000000001ff0400003bc1841696804878663bc2800004dee5cc1e9da2400002fcfc0000a020dcbd9 else (if i < 321 then 0x12b80ebb15150452ec000010c34000000000000006541a44f40000000004e466c69cba81a267c5e5a79e849a4835ae4c85e00001ec2d else 0x6e2a9b6140000688613c800000000001ae849a5145b41be409450000002687800007341a276f127092170391c27800357740000))) else (if i < 325 then (if i < 323 then 0x37d6800000000000009acf1c6e60000000000000000003e7180000755400000a4d34b82d000004ef0549803bd13b2d11b22000000000 else (if i < 324 then 0x885465bc90000036405700a7685a247c00000000000007a9c00000111c0000000000eb006616dd9c20000000009f20000008acd57029 else 0x99a077cf044461b30400005cdc2065d1de4a2b333bfc081292f6d959492de85cec20000000000000000000e5261225126c1a4a4)) else (if i < 326 then 0x142830000172c202cc0000000000000000001690431c028998132109fc143a04000000000000050ec00000019000000709696ec0 else (if i < 327 then 0x2660001007276800000000000000000096492223000006a5697a8000000000000000b15a5479cd3d18aa04df8680701a820000000000 else 0x3fd7c000050a18000000000000007484885a0000062a16c4860e8b5d101f20973774dcde21b8000001a6425a3100001430091f017fb0)))) else (if i < 334 then (if i < 331 then (if i < 329 then 0x21b848e2184001124983b811580a3d00000035ace764600000000000000000038a9c00004a36ca1d83e8f00000866807fc0000028edb else (if i < 330 then 0x7bbc2900900001e2215caf0bfe97578c1add9521000006ac780000741028ca07c22400009aa01e09b00000000043880971019a840000 else 0x39a014bcc3d360ecb29b100335a000000000000013d5a00000065e2d3a4000082a2400000000215a2157200000001c80000000024f00)) else (if i < 332 then 0x7558c00002a80e184c00000280c00001026071e843006076e000008527a2a0052418000000001fe107aec800002ab6a620070f680000 else (if i < 333 then 0x2114d0000143767541c000069280000000000000000001783266d6a1be911e240000588f06e5d4a60e940d0601a3f84 else 0xa14c61ca03b509c04c0000186d54a2616a5500000000039b7800001e3800000326a9328c00000d3391b91ccfb900000620074c11ba92))) else (if i < 337 then (if i < 335 then 0x18402375486225269d400009b3801b006c80e89cc000010c6c00000056078281d288000024840430c000009d1b22b0042ac591a8 else (if i < 336 then 0x3e4400000000281b368b7a62c60000217810000267848308000007ceb5b560510c0000000000bf712cd9c00000000186682a7823f60 else 0xfa0918a248a8a8b873327800008b51a0eb331840000027fb02e901e968fc9e2be600000968693c0000000f484000015e8455bca70e3)) else (if i < 338 then 0x3a0c000006a142933309330199e6be00000000000000003c015873037d8000097ae52dda7b65413e30be000000057b4a80c66b69b801 else (if i < 339 then 0x10e8400008bfc1d30000000bf15898305e004f425b21a00002198000000000074a540000000000000a11adf5cb000000000000006c60 else 0x1bcda000023d4070f4437da00000a48000001d2c0517d800000000000000000000006900250401ace5454000001b2210000001f0))))) else (if i < 351 then (if i < 345 then (if i < 342 then (if i < 341 then 0x351016f3028c0106a26d36815985536c9b906f649508d34ea4000096c1800001898261da1b871b21b0000062120351a8b3c6c36883c0 else 0xaaac0000a1e1000000a67850bc0098e06d84a370ed83860b40000000026d7000000000000002268c23a04000030c85b04c7ae000000) else (if i < 343 then 0x26ee000001be605801c00006ff69db4200000598100000e51e2a801aec060cb56e300000000009ed60c5da000000000a2ed13606 else (if i < 344 then 0xc144786e56612863402ca100000e2c000000fcd10078014c08d6140000095680000186dc000051f88a53d00000cd21000026b3d else 0x4800a95327e1a5e60070975b20c000025a326f478cda1508f0dcdf53b6a79c19c10000005c7dd10840e2300740392f06e5c00ef00000))) else (if i < 348 then (if i < 346 then 0x24280651158bad876aa608682a8deb6000000cde036104b9121b400000011a0000000cdc8345a0000184ec000011fe697d880000 else (if i < 347 then 0x64840bf071ed04000000000000094560d0a800001fd1686e30997232378978304624e1407c600000044f08000051b3cf2bc97cc80000 else 0xe55fa247808426596c000000001a40309b60348300001188c7394400000000158de1748c000089bbd610c969b0eb30000000000)) else (if i < 349 then 0x243285e0164d79d5707fc4400008493ceb990000166800000167610000000001b30276842e0265e61000000000990180939000000000 else (if i < 350 then 0x3bbc098c8000027be200000000000000500487e9ddf3d0000259f283cfc0000000022260000000000000010c3c else 0x58c11bf9e00000000059980000001d6279d9547c8000000001048118d8c000000000000080f79b0217468000002de600000713680880)))) else (if i < 357 then (if i < 354 then (if i < 352 then 0x99810a86100001872000001975800000000000000000000000000035b000000961793b490000239f10000000007d3700000000000000 else (if i < 353 then 0x310c0790000000cbb8000017cbe31f2c0000000003bcc18af9f99e83e7a85e62b388000090a0e1712000023da5000000000000020ca9 else 0x2625e69880093600000000000000cc60000000000000025b5e00000000018271f21893779ec087e9749a6013e0000003809e2723)) else (if i < 355 then 0x9e018000000001923089b39d8c00500000002df18f6987004000000000000000000035f23d602810d00000000087920000052e05f233 else (if i < 356 then 0x64950041a7693024a4000000000d3da55368000000000d45f2c5727959771c2846600000dcb999b8000009064227b19892637f1 else 0x921c800005ae12975a6a720000063b04000044d6000005193cee6000001b1a855619e03f24350eb5a756f507c03ae600000))) else (if i < 360 then (if i < 358 then 0x9cc1400008daf8000039e00c7da195982af5008d1d2e6000010e0c00000bdda0000015804fd208f2870284895a5afc04e12000000000 else (if i < 359 then 0xa160400006076a60ee976c000004cc0c00009dd8000000350000000000205e495810000052cc094802d865ca232520cee857d88462ad else 0x34d7624b0734d0000017e70000087b3844433ca1d1a8c798e000007750086f6109a02ce400001ae29708011e0ca47c513c0000014846)) else (if i < 361 then 0x500053c00001893c0000000006e040970c8be0689da3413000008e8e400003f7a400000000260030000237be223207718000026a6c else (if i < 362 then 0x18262371800000000025a02560523060000066360e1bb0000256df4212075600000000006c7580b406c09c00000ce08000019f68fb40 else 0x7684)))))))))

private def loc4 (i : ℕ) : ℕ := unpack loc4Packed 18 24 i

private def st5Packed (i : ℕ) : ℕ := (if i < 32 then (if i < 16 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0x95db24c10f05801695db24c10e05801695db24c10f05401695db26693001801695db25910f01801695db24a90f01801695db25fd6443c006002586c93043c00595db24c53043c006002576c930438005a42526c93030400695db24c10e30400692db24c0c123800695db24c0ca21000695db25fd301ec006c4aee4c0c11dc006969b24c0c11dc006961b24c0c11dc00695db24c0c11dc0068d5a24c0c11dc006c493030477114006bb9303047711400695db24c10f00c00695db24c50f004006 else 0x95db24c11421001695db24c1141dc01695db24c0d31dc01695db24c0cb1dc01695db24c0c61dc016961b34c4c11dc016b59c84c0c11dc016a5dbc4c0c11dc0169b9b24c0c11dc0169b5b24c0c11dc016985b24c0c11dc016975b24c0c11dc016969b24c0c11dc0168d5a24c0c11dc016c49484c0c11dc016961b34c0c01dc01695db24c0c01dc01692db24c0b41dc016961b24c0c01d801695db24c0c01d801695db24c50f1d001695db24c0ce1ac016c493030077114016ab9b24c0760a8016) else (if i < 3 then 0x95db2590c101002695db2588c101002695db2580c1010026002576c93045001595e116c99a43c016c4a576c93143c01695e116c93143c01695ddf6c93143c01695db26bd3143c01695db25913143c0160025d6c93043c015ae6576c93043c016002356893043c01595db24dd3043c01695db24b92c43c01695db24c52a43c01695db24b12343c01695db24a52343c01695db24c11443c016002576c92a42401595db26690f42401692db24c10f3ac01695db24c0f430401695db24c0ef304016 else 0x95db25fd3043003695db24c10f43003695db24c10f42403695db25fd303d403695db24c10f3ac036969b24c10f30403695db2590c130003695db2590c12f403695db2590c12d003695db24c0c1218036002576c97f1ec035969b54c0c11dc0369d5b24c0c11dc036969b24c0c11dc03695db24c0c11dc0368d5a24c0c11dc03695db24c10f1d003695db24c10d1d0036969b24c0c11d0036c49303047711403695db24c0c1094036c49484c0c11dc026c49483047711402695db266930014026)) else (if i < 6 then (if i < 5 then 0xc5a5b6c97f1dc046c5a576c97f1dc046bd2576c97f1dc04695e416c97f1dc04695db25fd2e1d404695db25f52e1d404695db26c57f1c8046a5db24c0c1144046c4930304a3114046c49303047b114046003125fc77114045c4a575fc77114046c593030477114046b59b2304950e0046b59b23047b0e0046a5db24c0c10c804695db25fd604c0036002576c96443c035aee576c93043c03695e116c93043c03695db25fd3043c03695db25913043c03695db24c12a43c03695db25fd30434036 else 0x2576c97f1ec055971b24c0c11ec05695db24c0c11ec05695db24c0bc1ec05695db25fd301d805695ddc6c93030404695db24c10e3040468d5b24c0c128c04695db24b0c128c04692db24c0c123804695db25fd3021804695db24b0c121004695db24a4c121004695db24b0c11f804695db25fd7c1ec04695db25fd781ec04695db25fd6a1ec04695db24b0c11ec04695db24b8c11e40460025b6d97f1dc04596e576d97f1dc04695e526d97f1dc04695e436d97f1dc04695e356d97f1dc046) else (if i < 7 then 0xa5dbc4c0c11dc086949bc4c0c11dc086c4930364c11dc086c49303047715c086c493030477144086a5ddf4c0c1084086a5dbc4c0c108408695db24c10f30407695db24c0c11ec07695db24c0c11dc07695db25fd644c006695db24c10f43806695db26695f1dc06695db2654c11dc06695db2644c11dc06695db25fd301d406695db256d3043c05695db25653043c056971b24c10f30405695db24c10b30005695db24c10b2f405695db24c0c128c05695db24c0c121005695db24c0c11f8056 else 0x95db24c0c11c00b6986196c9303040a695db2590c63040a695db2590c13000a695db2590c12f40a695db2590c12ec0a695db2590c12d00a6c4ad6844c11dc0a69b211304770580a6caa576c93043c09695db25fd3043c09695db25913043c09695db24c12a43c09695db24c12743c096961b34c0c11dc0968d5a24c0c11dc096c493030477114096995eb4c0c11dc086995df4c0c11dc08697ddf4c0c11dc08696ddf4c0c11dc086961df4c0c11dc086ab9c24c0c11dc08692dc24c0c11dc086))) else (if i < 12 then (if i < 10 then (if i < 9 then 0x95e116c8c01d81669b21130477178166d1e11304771701669b211304771701669b211304770f016695db24c10f05c16695db24c0c11dc15695db24c0c11c01569a1b04c0c11dc1468d5a24c0c11dc146c49303047711414695e116c93043c12695db25913043c12695db24c0c125411695db24c0c123811695db24c0c121011695e116c97f20411695db24c0c11ec11695db24c0c11ec0d695db24c0c11dc0d695db24c0c11ec0c698db24c0c11dc0c695db24c0c11dc0c695db24c10f3040b6 else 0x95e113047717018695e1130477144186002576c93043816595db24c0d225416695db24c0d221016695db24c0cf21016695db24c0ca21016695db24c0ca1ec166d1e6c844c11dc1660026c844c11dc16500259844c11dc16500258844c11dc1659b24b844c11dc16695e4b844c11dc1669b235844c11dc16695e35844c11dc1669b226844c11dc1660026c810c11dc16595e4b810c11dc16695e35810c11dc16695e357ecc11dc166b59c86c8c11dc16600312520c11dc16595db24c0c91d8166) else (if i < 11 then 0xa59b24c0c11dc226a4db24c0c11dc226971b24c0c11dc226949b24c0c11dc226949b24c0c11a8226a5db24c0c122821695db24c0c1228216a99b24c0c11dc216a5db24c0c11dc216a4db24c0c11dc216a41b24c0c11dc216869b24c0c11dc216a05a24c0c11dc21695dbc4b8c11d4216a5db24c0c11c821697db24c0c11c821695db24c0c11b4216a5db24c0c11ac21696db24c0c11ac216961b24c0c11ac2166c9303047718c216002576c97f1ec1e5002576c93043c1d595db24c10f3041d6 else 0x97dbc4c0c11dc25697db14c0c11dc256949b14c0c11dc2568d5a24c0c11dc256c493030477148256003234c0c1114255c493b30477114256c493030477114256c2d3030477114256bb93030477114256a5db24c0c11dc246949b24c0c11dc246002976c930304235aee576c97f4c0226aee576c93043c226aa2576c93043c226a7a576c93043c226002526c93043c22595e116c93043c226a5e526c930304226a5e4b6c930304226a5e356c930304226949bd4c0c11dc226a5db24c0c11dc226)) else (if i < 14 then (if i < 13 then 0x95db24c0c121031695db24c0b01dc2f695db24c0771d82f6aa29795db24c02b6a42526c9303042b6a41b24c0c11dc2b6002906c9303042a5ab9b24c10f3002a69b1b24c0c12382a696db24c0c12382a6965b24c0c12382a6961b24c0c12382a69b1b24c0c12102a696db24c0c11ec2a6aba577093e1dc2a6002577ad351dc2a500257844ca1dc2a5a5db24c0c10f82a6a5db24c0c10c82a695db24c0c11dc296c8e576c930304266c8e576c930304256c7e576c930304256002ee4c0c11dc255 else 0xb1657720c11dc386b0657720c11dc386b5a4b720c11dc386b5a43720c11dc386b5a35720c11dc386afe57678c11dc38695db24c0c11dc366975b24c0c11dc34692db24c0c11dc3460029771530304325a2a576c930304326a5e526c930304326a5e4b6c930304326a5e356c930304326a5db24c0c11dc326a59b24c0c11dc326a4db24c0c11dc326a31b24c0c11dc3269b1b24c0c11dc326965b24c0c11dc326961b24c0c11dc32692db24c0c11dc32691db24c0c11dc3267e1b24c0c11dc326) else (if i < 15 then 0xc2d3030477198456bb93030477198456c493030477148456c493030477124456c493030477118456a5e576c93030443695db24c0c1238436b8db24c0c11dc43695db24c0c11dc43690db24c0c11dc43695db24c0c126c41695db66c97f1dc406c4930304771143d6c4ad6844c11dc3c69b257844c11dc3c6c4ad677cc11dc3c6d1db2688c11dc3c6c4a57520c11dc3c695e11304771703c6c4923304771143c6aba976c93043c386c4ac195cc11dc38695e11810c11dc386b2657720c11dc386 else 0x90da248cc11dc456c496448cc11dc456d1d30478c11dc456c492c478c11dc456c493043cc11dc456bb93043cc11dc456c493042cc11dc456c49303d4c11dc45695db25ecbd1dc4568d5b24b0bd1dc456c4930304a31dc456bb930304a31dc456c4930304a11dc456c49303049d1dc456c49303049c1dc456c49303047e1dc456c49303047b1dc45695db2520c01d8456c493043c771d8456c4930304771d0456c4930304771a4456c4b0b4c0c1198456c493043cc1198456c493030477198456)))) else (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then 0xc49d54c0c11dc456c49bc4c0c11dc456a5dbc4c0c11dc45695dbc4c0c11dc4568d1bc4c0c11dc456c49b34c0c11dc456961b34c0c11dc45695db34c0c11dc45695db24c0c11dc456c49a84c0c11dc456c499e4c0c11dc456c499a4c0c11dc456c497c4c0c11dc456c496b4c0c11dc456c496a4c0c11dc456d1f124b0c11dc456c4a114b0c11dc456c49644b0c11dc456c3a574a4c11dc45695e044a4c11dc45695d9e4a4c11dc4560030048cc11dc455c025748cc11dc456c4a1148cc11dc456 else 0xc4b004c0c11dc456c4afe4c0c11dc456c22fe4c0c11dc456c4af44c0c11dc456d1eee4c0c11dc456cc6ee4c0c11dc456c4aee4c0c11dc456bfaee4c0c11dc456002ee4c0c11dc455c4ae54c0c11dc456bbae54c0c11dc456c4ae24c0c11dc456c4ac84c0c11dc456c4abf4c0c11dc456c2a434c0c11dc456bba434c0c11dc456c02354c0c11dc456bba354c0c11dc456c49df4c0c11dc456c39df4c0c11dc456bb9df4c0c11dc456c49dd4c0c11dc456c49d94c0c11dc456c49d74c0c11dc456) else (if i < 19 then 0x3124c0c11dc465961b34c0c11dc46695db25fd6443c456c4b0b77d30304456c4a9777d30304456c49df4c10f304456c49644c10f304456c4aee4c0c128c456002576c97f1ec45595db25fd7b1dc45695db2520dc1dc456b16436c8c11dc45695db2520c11dc456c494851cc11dc45695db24ccc11dc45695db24c4c11dc456d1f2a4c0c11dc456d3f124c0c11dc456d1f124c0c11dc456d1b124c0c11dc456ce3124c0c11dc456cc7124c0c11dc456003124c0c11dc455d1f084c0c11dc456 else 0x95dc54c0c11dc5a6c49df4c0c11dc546003124c0c11dc525a5dbc4c0c11dc526c4930304a31dc526c49bc4c0c11dc516c2db24c0c11dc516ba9b24c0c11dc516b5a576c8d21dc4e6c4afeb58c11dc4e6c4ad6520c11dc4e6c4a57520c11dc4e6c4ad64b0c11dc4e6c4ad64a4c11dc4e6b5a1148cc11dc4e68d5b24c0c11dc4d6003124c0c11dc495003114c0c11dc495002ed4c0c11dc49597db14c0c11dc4968d5b14c0c11dc49697da24c0c11dc4968d5a24c0c11dc496a5ddf4c0c1144496)) else (if i < 22 then (if i < 21 then 0x949b14c0c11dc666bb9a24c0c11dc6668d5a24c0c11dc666a55b24c0c11d4666a4db24c0c11d466695db24c0c11d0666a55b24c0c11c8666a4db14c0c11c8666a41b24c0c11ac666949b24c0c11a466695db24c0c11dc6468a9b24c0c11dc646899b24c0c11dc646001b24c0c11dc6456c93043cc11dc64695db24c0c12bc636c4a264c0c11dc63600312520c11dc5e5d1db24c0c11dc5d69b257844c11dc5c6c4a57520c11dc5c6d1dc84c0c11dc5c6d1db04c0c11dc5c6d1da24c0c11dc5c6 else 0xcaa576c93043c666cf6576c930304666c2e526c930304666a5e526c930304666c2e436c930304666002526c53030466595db24c10f304666949b24c10f30466695db24c10d30466695db24c10b30466695db24c0f5304666c4aee4c0c11dc666a5ddf4c0c11dc666a5dd74c0c11dc666a4dd74c0c11dc6669a1b24c0c11dc666995b24c0c11dc66697db24c0c11dc66696db24c0c11dc666961b24c0c11dc66695db24c0c11dc666955b24c0c11dc666949b24c0c11dc666a4db14c0c11dc666) else (if i < 23 then 0x95db24c0c11ec6b6949b24c0c11ec6b695db24c0c11e46b695e117ad7f1dc6b695db66c97f1dc6b6c4aee4c0c11dc6b695db24c0c11dc6b6949ab4a4c11dc6b695db25fc7b1dc6b68d5a24c0c11d46b695db24c0c11cc6b6949b14c0c11c86b68d5a24c0c11c86b6a4db24c0c11c06b6949b24c0c11b46b6002586c93043c6a5002576c9304386a595db24c10e3046a695db24c0ce3046a695db24c0cf3006a695db24c0fa1dc6a695db24c0f71dc6a68d5a24c0c11dc69695db24c0c11dc676 else 0x985b24c0c11dc70696db24c0c11dc706965b24c0c11dc706961b24c0c11dc706a5e576c9303046f695e246c9303046f695db24c0c11dc6e695db24c0c123c6d6a65b24c0c11ec6d6949b24c0c11dc6d695db24c0c11cc6d695db24c0c11dc6c695db25fd6457c6b695e116c97f43c6b695db25fd6443c6b695db24c1092ec6b695db24c0ff2d06b695db24c0c12386b6949b24c0c12386b692db24c0c12386b695db24c0c12346b695db24c0c12306b6949b24c0c12286b696db24c0c11ec6b6))) else (if i < 28 then (if i < 26 then (if i < 25 then 0x95db24c53043c74695db25f0c12f474695db25fd301ec7468d5a24c0c11dc74695db25910f1d474695e116c97f43c726a4a576c530304726a22576c530304726a1e576c530304726a06576c5303047268d5b24c0c128c7268d5b24c0c127472692db24c0c123872692db24c0c1228726995b24c0c11f872696db24c0c11ec72695e117ad7f1dc72695db66c97f1dc72695e116c97f43c706002616c930304705a5e4b6c930304706a5e356c9303047069b1b24c0c11dc70699db24c0c11dc706 else 0x2576c948300765002576c933300765002576c93130076595db24c12c30076695db24c12330076695db24c0f430076695db24c0eb30076695db24c0ea30076695db24c0c02d0766949b24c0fb1dc76692db24c0f51dc76692db24c0eb1dc76692db24c0b31dc76695e116c97f43c75695deb6c96443c75695db25fd6443c75695db25915f43c756a06576c530304756a06576893030475695db66c97f1dc756c4aee4c0c11dc75695db25fc7b1dc7568d5a24c0c11d875695db25fd6443c746) else (if i < 27 then 0xa31b24c0c1228776949b24c0c122877692db24c0c1228776ab9b24c0c122477692db24c0c1224776a5db24c0c122077692db24c0c122077695db25fd3021477695e11450c1210776002576c97f20477595db25fd3020477699db24c0c120477695db24c0b920477695db24c0c120077695db24c0c11f077696db64c0c11ec776995b24c0c11ec77697db24c0c11ec77696db24c0c11ec776961b24c0c11ec77695db24c0c11ec77695db24c0c11e077695db25fd6457c766002576c9303e8765 else 0x92db24c0ed2d077695db24c1092c477695db24c0f72c477695db24c0c12c077695db25fcb42c0776003124c0c1284775003124c0c12747758d5a24c0c127477695db24c0c126c776a5db24c0c126077690db24c0c1260776909b24c0c126077695db24c0c1244776ab9b24c0c1238776ab5b24c0c1238776aadb24c0c1238776a99b24c0c12387769b1b24c0c123877696db24c0c1238776965b24c0c1238776961b24c0c123877692db24c0c123877692db24c0c123477692db24c0c1230776)) else (if i < 30 then (if i < 29 then 0x95db24c0f530477692db24c0f53047768d5a24c0f530477695db2590f330477695db24a8f230477695db24c0ec3047767e1b24c0eb30477695db2590e930477695db24a8e93047769a1b24c0e830477695db24c0e630477695db26597b2f4776c2e576c92c2f4776bfa576c92c2f4776c49b26892c2f4776aadb24c0f52ec77695db24c1142d8776cf2576c9302d0776cea576c9302d0776cf24b6c9302d07760024b6ad292d077595db2669092d0776aadb24c1042d0776a99b24c0f52d0776 else 0x95db24c10e3047768d5a24c10b30477695db25f10930477695db25910930477695db258d0930477695db25810930477695db256d0930477695db24a9093047769b1b24c104304776995b24c10430477697db24c104304776975b24c10430477696db24c104304776965b24c104304776961b24c10430477695db2590f930477695db256cf930477695db256cf830477695db24c0f63047769b1b24c0f5304776975b24c0f530477696db24c0f5304776965b24c0f5304776961b24c0f5304776) else (if i < 31 then 0x90db24c11530477695db24c11430477695db24c11230477695db24c111304776c4aee4c10f304776a5dc54c10f30477692dc54c10f30477691dc54c10f304776975b84c10f3047769c5b24c10f3047769b9b24c10f3047769b1b24c10f3047769a9b24c10f304776985b24c10f304776975b24c10f304776969b24c10f304776965b24c10f304776961b24c10f30477695db24c10f3047768a1b24c10f304776bb9a24c10f3047768d5a24c10f30477695e114510f304776961b24c10e304776 else 0xbe6576c923304776bde576c923304776bda576c923304776bd2576c92330477695e416c92330477690e416c923304776b5a116c12330477690e116c12330477690dfe6c123304776b5a11689233047768d611689233047768b211689233047768d5fb689233047768d5a259123304776b39fe4c123304776c49464c123304776b39fe4a523304776b4db24c120304776002d68451e304775cca576c91e304776b59ab4a51e30477690dab48d1e30477690db24c116304776aedb24c115304776))))) else (if i < 48 then (if i < 40 then (if i < 36 then (if i < 34 then (if i < 33 then 0xc4a578f52930477695e4684529304776002d67f929304775c4ad66c129304776c4ad66ad29304776c4ace6ad29304776c3ace6ad29304776b5a976ad29304776b3a976ad29304776aba976ad293047769b2576ad29304776966576ad29304776962576ad29304776c4a438d523304776c02438d52330477695e4b7212330477695e437212330477695e357212330477695e436f12330477695e436d12330477695e436cd23304776bfe576c923304776bfa576c923304776bf2576c923304776 else 0x95db26553030477695db26413030477695db263d3030477695db26393030477695db26353030477695db263130304776b8db262d303047766c9a262d3030477695db26253030477695db2621303047760031261930304775c49df539303047760025b6d92c30477596e576d92c30477695e526d92c30477695e4b6d92c30477695e436d92c30477695e356d92c304776c5a5b6c92c304776c5a576c92c304776c4ad66c52c304776c4ad66c12c3047768d5a25912c304776c49474c12c304776) else (if i < 35 then 0x949d7689303047768d5d7689303047768d5d568930304776c4db268930304776c49b268930304776c39b268930304776c35b268930304776bb9b268930304776bb1b2689303047768d5a868930304776c49df68530304776c49b267d3030477697db267d30304776c3abf67930304776c4a2c67930304776c49df67930304776c39df67930304776c49d9679303047768d5b0679303047768f5ab67930304776c49a8679303047768d5a2679303047768d5a26693030477695db265930304776 else 0xbba8368930304776aba8368930304776a828368930304776bba4368930304776c4a3968930304776002396893030477596236689303047760023668930304775d1e3568930304776cc63568930304776c4a3568930304776c023568930304776bba3568930304776b8a356893030477695e35689303047760023568930304775bba2c68930304776a0e2c68930304776c45df68930304776c39df68930304776bb9df689303047768d5df689303047768d5dd689303047768d5d968930304776)) else (if i < 38 then (if i < 37 then 0x9b24f6ad30304776c4a4b6ad30304776c324b6ad30304776c024b6ad30304776c4a436ad30304776c2a436ad30304776a5e3d6ad303047769b23d6ad30304776949d76ad303047768d5d56ad30304776bb9b26ad30304776bb1b26ad30304776c4a976a930304776c4a976a130304776c4a426a13030477694a35691303047760023469130304775c49bc69130304776c49b368d30304776961b368d30304776c4aee68930304776002ee68930304775bba9768930304776c4a8368930304776 else 0xc46936c530304776aba936c530304776c4a896c530304776a5e396c530304776d1e526c130304776d1e4b6c130304776c41f86c130304776961b36b130304776c4aee6ad30304776002ee6ad30304775c46976ad30304776c42976ad30304776c2a976ad30304776c02976ad30304776c4a966ad30304776c4a956ad30304776c4a936ad30304776c4a8c6ad30304776c4a896ad303047760026c6ad30304775c52596ad30304776c4e586ad303047769ca576ad303047769ba576ad30304776) else (if i < 39 then 0x8d61a6c930304776a5e136c9303047769b2096c93030477696e096c930304776966096c930304776962096c930304776b59fd6c930304776995fa6c930304776d1df86c930304776cc5f86c9303047769b1f86c930304776965f86c930304776961f86c930304776b59f76c930304776b59f66c930304776995f66c930304776d1df56c930304776d09f56c9303047769b1f46c930304776b89cb6c930304776c3a976c530304776c02976c530304776c4a956c530304776c4a936c530304776 else 0xa42356c930304776a26356c9303047769a2356c930304776982356c93030477696a356c93030477690e356c930304776906356c93030477695e2f6c9303047769622d6c9303047769b22c6c9303047769862c6c9303047769662c6c9303047769622c6c93030477692e2c6c93030477695e2b6c93030477695e2a6c93030477699e266c93030477696e266c93030477696a266c930304776962266c930304776aba1f6c930304776aba1c6c9303047768b21b6c930304776d1e1a6c930304776))) else (if i < 44 then (if i < 42 then (if i < 41 then 0xc26436c930304776c22436c930304776c1e436c930304776c1a436c930304776c16436c930304776c12436c930304776c0e436c930304776c0a436c930304776a5e3b6c930304776a5e396c93030477697e396c93030477695e396c930304776a5e386c93030477696a376c930304776a5e366c930304776962366c93030477695e366c930304776cc6356c930304776bb2356c930304776b9a356c930304776b96356c930304776a5e356c930304776a56356c930304776a4e356c930304776 else 0xbd2576c930304776bce576c930304776b9a576c930304776b96576c9303047769ea576c9303047769e6576c93030477698e576c93030477696a576c930304776002576c930304775d3e526c930304776a42526c930304776d1e4b6c930304776d164b6c930304776d124b6c930304776d0e4b6c930304776d0a4b6c930304776cfe4b6c930304776cfa4b6c930304776cf64b6c930304776d1e476c930304776c52436c930304776c4e436c930304776c3e436c930304776c36436c930304776) else (if i < 43 then 0xa32586c930304776a0e586c9303047769b6586c9303047769b2586c93030477696a586c930304776966586c930304776d42576c930304776d3a576c930304776d36576c930304776d32576c930304776d2e576c930304776d22576c930304776d1e576c930304776ce6576c930304776ce2576c930304776cda576c930304776cd6576c930304776c56576c930304776bfe576c930304776bfa576c930304776be6576c930304776be2576c930304776bda576c930304776bd6576c930304776 else 0x2636c930304775d1e616c930304776c2e5f6c930304776bfa5f6c930304776a5e5c6c930304776a625b6c930304776a5e5b6c930304776a565b6c930304776a525b6c930304776a4e5b6c930304776a265b6c930304776a125b6c930304776a0e5b6c930304776a0a5b6c930304776c565a6c930304776a5e5a6c9303047760025a6c930304775d1e596c930304776d1e586c930304776c22586c930304776bfa586c930304776a5e586c930304776a5a586c930304776a4e586c930304776)) else (if i < 46 then (if i < 45 then 0xc36e26c930304776c2ee26c930304776c4ed76c930304776cced66c930304776ccec56c930304776002b56c930304775d1e976c930304776d16976c930304776d0e976c930304776cf2976c930304776bf6976c930304776bf2976c930304776bda976c930304776d1e966c930304776d1e936c930304776c8e906c930304776002906c930304775d1e8c6c930304776a86816c930304776aba7c6c930304776d1e6c6c930304776af26c6c9303047760026a6c930304775a5e676c930304776 else 0x94a436f13030477692e436f13030477695e356f13030477694a356f13030477690e356f130304776a5dbc6e9303047760025a6d53030477595e526d53030477695e436d53030477695e356d5303047760026c6cd303047750025f6cd30304775002596cd30304775002586cd30304775982576cd3030477695e4b6cd3030477694a4b6cd3030477695e436cd3030477692e436cd3030477695e356cd3030477692e356cd3030477690e356cd30304776c4ae56c930304776c4ae36c930304776) else (if i < 47 then 0x92e477153030477695e437153030477695e3571530304776c4a9770d30304776a5e5870d30304776a5e4b70d30304776a5e4370d30304776a5e3570d30304776a5e3270d30304776aba976f530304776962576f53030477695e526f530304776002526f53030477595e4b6f53030477695e436f53030477695e356f530304776002976f130304775002956f130304775002936f130304775002906f130304775002656f1303047750025f6f13030477595e526f13030477695e436f130304776 else 0xc4a9777d30304776c029777d30304776c4e6677d30304776c5a5777d30304776c4e5777d30304776c4aae77930304776c4aae77530304776c4a9777530304776c4a957753030477695e527713030477695e437713030477695e3577130304776c4aae76d30304776c4aae76530304776c4a9776530304776c4aae75d30304776c4a9775d30304776c4a9375d30304776a5deb75d30304776c49eb75530304776c49df75530304776aba977253030477695e4b715303047760024b71530304775)))) else (if i < 56 then (if i < 52 then (if i < 50 then (if i < 49 then 0x95e356f139304776002586cd3130477595e4b6cd3130477695e356cd31304776c4e576c93130477600331c493030477500347bb93030477500331bb930304775c4afebb93030477600000bb930304774c3ad6afd30304776c2ad6afd30304776c4aceafd30304776c4adbab930304776c4a528e530304776c4a438e530304776c4e578d930304776c4e588d530304776c02578c130304776c02578b930304776c4aee77d30304776c4aae77d30304776c32ae77d30304776c02ae77d30304776 else 0x2578d604304775caad6845eb304776b5ab3a5db2304776d1f3295db2304776ccb1295db2304776ceafe95db2304776ccafe95db2304776b5a117d5b2304776c49fb6ada2304776cfa576c964304776cee576c964304776cea576c9643047760031277d4e30477500000c494830477400312bb948304775c4ad684548304776003125214730477595e416c942304776c2e576c93b304776c22576c93b304776bfa576c93b304776c49b26893b30477695e526f13930477695e4b6f139304776) else (if i < 51 then 0x95db24c10f3d077695db25fd303cc77695db25fd303c477695db25fd303bc77695db25fd303ac77695db25f5303ac77695db25dd303ac77695db25cd303ac77695db25b5303ac77695db24c10e3ac77695db24c10e3a877695db24c11432c776c4ad690e35304776d1f12b5a11304776cab12b5a1130477600312b5a1130477500308b5a11304775b22bd95e113047760026c95e113047759b25793e11304776002578c21130477500312b5a0b3047750026c95e043047750025792e04304775 else 0xaba526c9303047b6aba436c9303047b6a5e436c9303047b6aba356c9303047b6a5e356c9303047b695db25fcc13007b695db25f8c13007b695db25fcc12f47b695db25fd302f07b695db25fcc12d07b695db25c0c12d07b695db25913043c7a695db24c0c13007a695db24c10f2f07a600257781b65fc77595db2669965fc77695deb6c9654d477695db25fd30430776002576c95f42477595db26695f42477695db24c10f3e877695db24c0fb3e877695db25fd303e477695db25fd303dc776)) else (if i < 54 then (if i < 53 then 0x95deb6c93049c7e695db25fd3043c7e695db25fcc12f47e695db25fd302e87e695db25913043c7d6002e295db25fc7b5002576d9b25fc7b5002576c99a5fc7b50000095db25ec7b4002576c97f5e07b5c4a576c97f4c07b695e116c97f4c07b695deb6c97f4c07b695ddf6c97f4c07b695db25fd7b4c07b695db25fd644c07b695db25fd304a87b695db25f5304a87b695db25fd3043c7b695db24c10f30c7b6a66576d9303047b6aba996c9303047b6a66576c9303047b6002576c9303047b5 else 0x95e1132884400257845b232884595e116c93032884695db25913032884695db24c12732884695db24c11432884695db24c10f328846aba9b6c930304846aba526c930304846aba356c93030484695db24c0c930484695db24c0c830484600257844c130084595e116c8c130084695e116c8c12f484695db25fcc12f484600257844c12ec84595e116c8c12ec84695db24c0c12d884600257844c12d084595e116c8c12d084695db24c0c1300836caa577adb24c07e695deb6c9354c07e6) else (if i < 55 then 0x32a95db24c0905aeeae95db24c08e6abaa895db24c08e6abaa395db24c08e6aba9e95db24c08e6002ae949b24c08e5002ae92db24c08e5002ae8d5b24c08e595deb6c97f4c08e6aba526c9303048e6aba4b6c9303048e6a5e4b6c9303048e6a324b6c9303048e692e476c9303048e6aba356c9303048e6a5e356c9303048e691e356c9303048e692e326c9303048e692db25fd303048e692db24c10f3048e692db24c0c12cc8e6002576c93032885595deb6c97f4c084695db25fd3043c846 else 0xa42526c930304b4695db24c10f300b4695db24c10e300b4695db24c104300b4695db24c0f5300b4695db24c0ef300b4695db24c10f304b3692db24c10f304b3695db24c10e304b3695db24c104304b3695db24c0f5304b3695db25fd3043ca3695db259130364a368d5b25fd30304a3695db25fcc12f4a3695deb6c97f4c095695e116c930348956aba526c930304956aba436c930304956a8a436c930304956aba356c93030495690db24c10f304956d1e576c930304916002576c930304915))) else (if i < 60 then (if i < 58 then (if i < 57 then 0x95db2581303d4c1695db2575303d4c1695db2571303d4c1695db256d303d4c1695db2565303d4c16a5e526c93033cc16a5e4b6c93033cc16a5e356c93033cc16aee576c930338c1695db24c10f324c1695db259130308c1695db24c10f308c1695db24c109308c1695db24c10f328c0695db25913030cc0695db24c10f30cc06a42526c930304c0695db259130304bf695db25913030cbd695db25fd7c43cbc6a42526c930304bb695db24c10f2e4b8695db259130304b5695db25913030cb46 else 0xc49d16c93043cc16a5dd16c93043cc168d1d16c93043cc16a06576c53043cc16a06576893043cc1695db26093043cc1695db26013043cc1695db25f93043cc1695db25913043cc1695e116c930438c1695db25fd30438c1695db25f930438c1695db259130438c1695db24c12a438c1695db24c10f438c1695db258930434c1695db25f93042cc1695db25913042cc1695db25813042cc1695db2591303ecc1695db2581303ecc1695db2575303ecc1695db25f9303d4c1695db2591303d4c16) else (if i < 59 then 0xa5dd8745b24c0c16a5ddd741b24c0c16a5dd973db24c0c16c8f12949b14c0c16a06578d1b14c0c16a065777db14c0c16a2e5777dab4c0c16a225777dab4c0c16a225777da24c0c16c45df6c9a24c0c168d1d16c9a14c0c16c8e576c99a4c0c16cf6576c9644c0c160025c6c93043cc150025a6c93043cc15c76576c93043cc16ab6526c93043cc16c8e4b6c93043cc16a5e4b6c93043cc16a064b6c93043cc16c8e436c93043cc16ab6356c93043cc16a5e356c93043cc16a22356c93043cc16 else 0xa427f949b24c0c16aa69792db24c0c16c2e9790db24c0c16bee9790db24c0c16bea9790db24c0c16a1657905b24c0c16c2e978d5b24c0c16aa6978d5b24c0c16a02528d1b24c0c16a5e438d1b24c0c16a5e358d1b24c0c16a5e528b1b24c0c169f6528b1b24c0c16a5e4b865b24c0c16a5e35865b24c0c1698619845b24c0c16c2e4377db24c0c16aba97769b24c0c16c4a97761b24c0c16aba97761b24c0c16aba9774db24c0c16a5e34745b24c0c16c45df745b24c0c16a5ddf745b24c0c16)) else (if i < 62 then (if i < 61 then 0x2576c93043cf4595deb6c9644c0eb695db25fd644c0eb6002586c93043ceb595db24c53043ceb6002576c930438eb5002576c93043cea5002576c930438ea595db24c10f438ea695db24c10f3acea6aa2576c93043ccf6d3f4b95db24c0c160034b95db24c0c15d2f4795db24c0c16cfb2395db24c0c16c7efa95db24c0c160028095db24c0c15aeead949b24c0c16d1e97949b24c0c16bfa97949b24c0c16aba97949b24c0c16ab697949b24c0c16aae97949b24c0c16a8297949b24c0c16 else 0x95e116c9314c10f695ddf6c9314c10f695db36c9314c10f695db26bd314c10f695db2669314c10f695db2591314c10f695db2591304bd0f6002576c9314b10f5002586c9304a90f595db24c5304a90f695db24c12b4a90f6002576c93148d0f500257845b24c10e5002576c9644c10e5002576c9634c10e5002576c9304a90e5aee576c93043d0e6aea576c93043d0e6002576c93043d0e595db24c53043d0e695db25913043d0a695db24c53043d09695db24c53043d086002586c93043cff5) else (if i < 63 then 0x257845eb5910f5002e295db25910f5b5a577adb25910f695e117adb25910f6c4a576c97f5910f695ddf6c97f5910f695db26a17f5910f695db25fd7c5910f695db25fd6a5910f600000969b24c10f4002d6961b24c10f500297961b24c10f5cab2795db24c10f6cab2395db24c10f6caaa895db24c10f6aa28b95db24c10f60025891db24c10f5aba838d5b24c10f600258845b24c10f5caa5777db24c10f6002586c9644c10f5caa576c9644c10f6c4a576c9314c10f6aee576c9314c10f6 else 0x95db25fd7c5915f6aa297a2e576c9306aeea895db25fd306aee577adb2591306aee576c97f591306002576c97d58130595db25fd604b92a695e116c97f5f10f6))))))

private def st5 (i : ℕ) : ℕ := unpack st5Packed 64 24 i

private def adj5Packed (i : ℕ) : ℕ := (if i < 17 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0x8300108015d10108001014000200108500000400e0051070410860821d20c818200000c0830010c27485930032401c4 else 0xa08000c2000132800000c70070400660c00c31c30810801432020020401cf0020400000c01c10403012431000ce040) else (if i < 3 then 0x420410400840c23870003490020811030040400030c50000400811431042801802c3041082100003005040001005095 else 0x2401801431840450c408f4c310040100014806100004100700008000220804110500104000000000708700244114104c)) else (if i < 6 then (if i < 5 then 0x432800830c11000401c40080090401820802840070020410c12c40432c104000014330404114244b08400510325100a else 0x4020060010400000c00401000080c10491c40460420000810cd1013400c00400460c00940c00400891cf001003003045) else (if i < 7 then 0x883410000450040410441400060021800002411430c00810880000030001c00012410871800860810420431c7003101 else 0x1c60050045c000000000c0400441c204510800404414000000404108610054000c10008c0820402460d10800c7002001))) else (if i < 12 then (if i < 10 then (if i < 9 then 0x1800800022871090800437c31877050030410030021130502800c1002080345104041080081113182040040000405101 else 0x20040800820c70030c00430020070870c23400c30020064c43401011430441810010011061000050c004004a20b041) else (if i < 11 then 0x70010010030001000800810c90452c20400010401020011010c33140000820800422041010001421c500000720304b else 0x2401020030401440400431800890030c108004000204d0811072030040400040431040410080400020c1086083000004)) else (if i < 14 then (if i < 13 then 0x810006870000420001830c30022000021c01410010860862c40011010800060c410b0c20d45060071831c50ce10105c else 0xc20420001800c10000462c00c11405900080890000c10000020401401430410920010011400850c3204040301100002) else (if i < 15 then 0xc104000100024100518020008c0400060c04040070010405430010002050000c4005004042006040002204041081041 else (if i < 16 then 0x4014200a08204a0010011c100000400200004120004604200a54414b000040041181105300140000281308002003000 else 0xc62460c40070c10052030040002450c00020410800000440020003c224608000f0001010020401cc080140015244))))) else (if i < 26 then (if i < 21 then (if i < 19 then (if i < 18 then 0x10108000000008200000b04010a00208700510308028004604014910504000600200400109e0ce28b103107283001181 else 0x10c11c000004110b0820032c42831400021040022c13c03490020120400460c00400c1081001101181003006001181) else (if i < 20 then 0x14510138918714e0800d01800000020c10020001400410410070c310304210000000408028c000141304002000405000 else 0xb0002810000013444061c30401c40441850060051870001c00c00010411412410070420010040c40411c0049143083)) else (if i < 23 then (if i < 22 then 0x50820000401810c008a0c10081c21800810cb2080c02cd00350200004500300300000010000300100000a3c0141000 else 0x50410072010810401c140404e0410010824400400033430045100140400430421db04300a0c20410c10840000011c0) else (if i < 24 then 0x120407431010841001c6008a830000803800c12800060ce0400810800000c00c00000001420050411c34810011020c3 else (if i < 25 then 0x10104510200010304104c0003400801043d60802050430050054400c20010800c13070800400460041c3006080080001 else 0x1831c20400831062000030020010000800000810d01c408504958200000d040000301004003083080003440082000)))) else (if i < 30 then (if i < 28 then (if i < 27 then 0x14c20d00800300210154014300a10308928110418100101d085000348002045002000040000105186082500044041001 else 0x100204400a00300310000d0c90051020020441000c10080000c601838704218101e006190040080044002004102000) else (if i < 29 then 0x831832020000000052881c22480040000010030410472010001450801030481c00820011c108710500b002008 else 0x100c13400003830c20c01811c11440030c004b1000c40800020802411023401511841420050c40808001c1040040143)) else (if i < 32 then (if i < 31 then 0x4034130000010a0c01000461010010410000800070c60410030440020010030001401100400011c61462c01800030c3 else 0x410020861070044000010d128504110104510008c04b10308004700118400700a0c400300c100000000041248000040) else (if i < 33 then 0x440012820000052c11021001000cc2c40050000801000001442841c00411070400830c0081000101000044000044003 else (if i < 34 then 0x10204111218700100000400000010200318f24d1432020c50860c20c90c00c100200008018508e080000301300080000 else 0xc73dc1011040c500500254118100530208b147))))))

private def adj5 (i : ℕ) : ℕ := unpack adj5Packed 6 64 i

private def loc5Packed (i : ℕ) : ℕ := (if i < 206 then (if i < 103 then (if i < 51 then (if i < 25 then (if i < 12 then (if i < 6 then (if i < 3 then (if i < 1 then 0x26c024e8644aa52da1000020360a32bea621092dab198680021e60aac8db9bc63c790c80186421bf50000000002ae152e58 else (if i < 2 then 0x228273127800001036aba02555696bed62585223f0000217e072f9ae90900000000015bb1d0f051420000042f000000000014c60 else 0x1f9e427a01909e4d700d1700000135b044284000000000bfc65b2c00000484e0705a70930000033338000081ca0000040e85238c)) else (if i < 4 then 0x19b69503c000029e4000000c400b1e6000005c27220663e1a2d41e4cc21585944e84cbda00000817189a02bfe4000007070339211084 else (if i < 5 then 0x61f9a8e2d00802366615a8c000070fcc000039d80000022a05eb0337924b51e00000a6f2502f800009cb004c33758789d63 else 0x1054881ad35018128882e8400003932000008fe32308f079c205607ba728d712edc8000000000000000000a5f2815a5ebb067a300000))) else (if i < 9 then (if i < 7 then 0x33802b88533b815ba10a630d1c08a248e01e83b21ef418f99000002d7a40000b4a60a44224174000011a780000ae802af3000001ecb1 else (if i < 8 then 0xfa000000000000000d81868529eb4e0000241f5000007ba068d20000080c62b91e00000000000000000011678000033c040000 else 0xa9426258245b82b3a9b4da40000145467b2400000000000001f9da5f2c54e1e4d6114e3310b01368047b5000000fa857cc0635b0193c)) else (if i < 10 then 0x2b8934fc841bda7c82001c800002a4c0000018792ae791e0f216186e7f23fa84774611e400000401216be300000b9da else (if i < 11 then 0x714c2525e00001a1cc0000000006256a138031f21749e0b4840000bc3d0000000001a80216e491400000000000000028ba0000016583 else 0x56c2e2864866c800006bb80ffd000002a8f189f216355bd0bd3a468758000009f7729caa8bf80b880922000000386008440b4b8eaf29)))) else (if i < 18 then (if i < 15 then (if i < 13 then 0xb9969c060000012f9100000030929984000035321a4745f8057b0473382d6a100000000037f68d900b79780000a917000008ae32ba98 else (if i < 14 then 0x16bbf329d4000000002b7750000091109d769dd32a722595dc0000000004a96a6de91568a5f1c228827557513c5d91800002823f else 0x1588cad30200b47ee900000d1b1305686b003afc800000000257e151bd4000049bca4a841ee84000034866c0220000000005c76d4e40)) else (if i < 16 then 0x77421c50000002384d5e35108102ef680000808028d208200076c6283c000005a4180000000000000846c000003caf4b4dd8e836e8c0 else (if i < 17 then 0x8b8112d09a6a617301000020e01000000000a2480af837bfc639e800000000000000468000002b892000000000285a6765a949000000 else 0x8008c0000896000000482f0000000000000000001790622b6a9e7100000e300bbf7400000000000001734ad160b8424000084a49008c))) else (if i < 21 then (if i < 19 then 0x8920133c1000029c9861f86b039000000000236000000000005e1a00001a2810000149048e84af0f2bd904000031d380000000019dd6 else (if i < 20 then 0xb47c6d41049c840000872f0000007fc800001f1d4000037e7896ca00000dc9233720d65a000019e5a00002b861bd2ce26e4000000000 else 0x9260c00000000119c0111c995903a77c061800000084600000000031f24fc6000002356c65c4114800c901b051000000000000000000)) else (if i < 23 then (if i < 22 then 0x24f8098b000000a6f0616f34907ddd001c580cd5a00002580496560000051398000031e097330ade040000a7705c860 else 0xda84fc127ad6985847a33800008f4588718337408200000013ec0877804f000000000002cc6000000920df8e066b25ba60257c40000) else (if i < 24 then 0x285400000102a705c00000000002edb0000017a6c4c42041eb00001a1e478fc8000000218ffa70000000002fac0d4307c862e95d else 0x168c025648d8da00000000087d90f7383f29c0000000000000000003f5a3ee845d5c000006e000000000003e7acca7224a840000))))) else (if i < 38 then (if i < 31 then (if i < 28 then (if i < 26 then 0x40e9c074076580f6000f57456600000000000000253f226e20fda823a780000000020770000015f005c18271a3009243fcc000000000 else (if i < 27 then 0xb2c818e5290320000000002b3a8000000000aec8c00007e64825033293000000000000001747af384000000000164080000 else 0x1cf82701059178a36000002052a0fca251020000000007530400000000024410000000001ec867e405566c3a64000003cc25b2c4ef49)) else (if i < 29 then 0xa78d4fed0000000000000029a063bc02dd983bd32bc8000001884200001d69200000215a00000e4f200001cbbd000000cdc000021d72 else (if i < 30 then 0x8cb8000000000144006c001176030bca956f3c1823b0115805b160b22184b06b67695b2a0000125025227131e64126c00003b68667cd else 0x7a8060d98000000000148b40000881c9d2c032c8000005eec664bb5f80c000000cc400000650000009607175704cfc0000000002449e))) else (if i < 34 then (if i < 32 then 0x1d2bc000024c603ea7800003f3a613635ae0444a9bb902eef017002284ca7249e80290f6800009fd02b459545c8c780 else (if i < 33 then 0x1e06403e85a4810290235d008d06baa107d012a1e154307ea000000cfda5e7b08a9c000026358000021601000023d840000064bc else 0x174a063884000007561df18000000000a9e20036000000000032974fcdab153000008a746204f172624bcc545680340a41c0af30)) else (if i < 36 then (if i < 35 then 0xbb2861bd351506f6bf03cf0dc300000000009e3d45021000000000b5260a4807e22c483fa927811c60000164d98b59a030400001ad75 else 0xab0a6615c0000000000000122cd4fa9c00002e085f400517c1ee0024079223c00000000081ac298de63d7d8a740e9c8000000000d780) else (if i < 37 then 0x15b20000019e816a0003e9eaa5c40000782860caa0000249c9000000000bc459fd803ff388618603da18732e1a9a180 else 0x2de42369600000a0e04cfc6278c0000000000000243c81a6c285c0a6c255bb300000911e18d69d670813800f3277830000063e780000)))) else (if i < 44 then (if i < 41 then (if i < 39 then 0x3b322ec08ab6fc000000000000011ae400007ac1800000000000003b3d4000000002b09882032e14000002bf9400001a40c9e3740000 else (if i < 40 then 0xddb32fd6800000000035d10000000005cdc000000a345905f00002078c8ea058e4fa3ab56ab39ed0400000000000000e6e40000 else 0x4ebd4000000000000044288e000195057ff21fb8078b200002c93caae24000000000c0f2000000000000012113847c07e20)) else (if i < 42 then 0x50d8c4b860000000006448a2be9000003f1e97260000010d5d19d300000000059b722d2a6a9ca43800e48400006af68a5489c002e3c0 else (if i < 43 then 0x17a4618000001fc800000133b5000007e21665c8f16100000000000000000076dc1042600000000056e7ab75d21e600000000022158 else 0x83205d96641084000044fa59c62428b400000000000003d40000000000000000000106260000000000000000002160083e3000013606))) else (if i < 47 then (if i < 45 then 0x5cf517e06bcdc800002e1ae7f5ca5260000000000000074cc0544e870007bd1b4a200000468a4000000000e772000021500bdc82995d else (if i < 46 then 0x1229a984800002d7816ab221f72000000e80000000000536cd2768016fce1008b602832f1a000cc4c3200689ad4236c000066bccb498 else 0x4c104fb18a9026e73277bcab904548cc000021af40000b3079dec86036a89a125e48000000002596c0000000002268c981c012e40000)) else (if i < 49 then (if i < 48 then 0x18834a822535de000024a04b7e100000000007e927f6f4ea6cb304e850869432e940516100000000013f5a90f82510096bb09604 else 0xaf660543171d88a7e4b9d60000008b745ab300000000000000ba1e31060000056800000000001fca17624a41f40c6a4543d91369eb24) else (if i < 50 then 0x335a40000a0135860a000023a01869b0000000002b99e00000000000001eddeaa89d3240478840000000015e3d79f6c0000000000000 else 0x11b80152b4773c0d88c0000ae3300000a12f508810000000005bec2efda00002cf12000020f900000000008db900000a7c000000)))))) else (if i < 77 then (if i < 64 then (if i < 57 then (if i < 54 then (if i < 52 then 0x71981ca7200000000081d8000000000000000b8600000422c6228500001ad5a8c930000006fcaa3a07ccb504c17a8180000000021b75 else (if i < 53 then 0x5616c000000000239b48a0de7980b2617cc244248000037126944021e100000a98028c00510a8cbf20f2300bbd00001ee0100002704c else 0x25a18bb8f66ee100001b5e22ff69ae870000000007ea0453204a6a400006bc64ba9e176780000000000000000017746696600000)) else (if i < 55 then 0x29ce98bb8240da000000000665d9886047af0000010c30816000002ba929ef7aa11c819980000b6401b6800f5220508540c80000 else (if i < 56 then 0x1c2f35c7780f605a56a8aada2a8c000000002396638466c727000014918598c16abd000015801a28fc0000000000000 else 0xb0394b41e0000172b56a2318e5f00001bfe45aec4000073210000095db612213e98400000000000009d9004700bbc01df021c5040000))) else (if i < 60 then (if i < 58 then 0x9eb300000695900000bc8a0000000002882700000000031e3000000000080680416810495996d0c08000000000000023e018f8581740 else (if i < 59 then 0x28f11a1720160261005f800000096dc000008b64924a40000000000a342d1a05b401edf200001f8c79d68d2b210e1688404000008418 else 0x1d80100002952d699200000000000bec000000000bb6cc000005c84000000001e930664f000004a6e40000b7f0032c0000000000)) else (if i < 62 then (if i < 61 then 0x75a7a13001c4fe30096f8157930000028b579df6979b000002150100001e1203038000002adb000000a29c000000000201050c110da0 else 0x969f1c700002f63fb2398000000000000000000000078e0a5000000008d001fc0a8c6b000020e00000018f9d0000000000f1800c83) else (if i < 63 then 0x7a55142840f5823fc800001523d3ff44af72000000000000018f92594019d87aa2b647de20980000000000000017860000030c180000 else 0x1cb2d995400001f2018ba4af30d000000000a06b5919e000003cb460400000039e5a5e890000164026796c00002fc6e2e12)))) else (if i < 70 then (if i < 67 then (if i < 65 then 0x194810000000002f76a1f6c0b6840000a1b0000000000205da8db940000b61c00000020f0000095cadb70e000000000000000000 else (if i < 66 then 0xb9f62f01b0882515a1ac484cecc000023de4000018ad4000000000bb8f26c5a51cb565df000022f2a75006b8908ec8800002cf68ad58 else 0x5dc4eb50332d69068c3f32132889ff02bd9b000025e3d00000000000001b70461524080800002f4296e720000000000000058211fa48)) else (if i < 68 then 0x737c11ba1000000000000002880000000000732067439373700000000000000000009c922a9b0000000001c502a079946096bc5059de else (if i < 69 then 0x1cf0417c11be6c0000128a10000000002859800006f0c80000764c800007c7593389000029dc06c7c9b15a422080000000014884 else 0x1c58c0000277800a800c684000040a8434d48819000005fb6a4ac21584a34664fc9ecdc85e810a40449c88068014f21f7a800001ca51))) else (if i < 73 then (if i < 71 then 0x6ae1ae27259168c78d0000218c600000fcf58e5322060a86e51a1068b680000196cd9931000000000a9504c0da3e788000033982b6cd else (if i < 72 then 0x2f2a80937910801e6843f209b10000003f202bae0000000000000000000331a59ee814480000000000000015b0aee006f2280000 else 0xb27ab780a9900000095095774200001f292000028d6933b3a76dd0000000006098a079214e898fab55b005b80bbac2b259)) else (if i < 75 then (if i < 74 then 0x3ec0000004aecd578300001cb04253050f20b736a16f2393400000000000000863b0b05a684c00000000000000252fd13e047c85f79e else 0x7f2fc00003ee01f2190000000006474400000000000005f4365f18bdf00e78c87120000000001491e99969b08124ba5d72007b001140) else (if i < 76 then 0x2f369a2990000093922a356d9d857002c6d10000113800000068886e1b0000000000491e00002a86986f44000090b812821000013e21 else 0x1aa8066fd0be3000001e8b0000008208514b0788800001675c00000000000000996200002b2c04408c000081460000089449b960))))) else (if i < 90 then (if i < 83 then (if i < 80 then (if i < 78 then 0xb80007b697d08d126084081b45d0a2618cb000000000000000bb22a02fe7ea1000000000372f4000069526148400000462900001515b else (if i < 79 then 0xab988000000002eed400001eff00d4fca5615e5b0e8f20000198800000080a100001f8de000000000000000000000000000aea711906 else 0x3b8d172d8ae04000068e8cb4180e968005867122893f00002384c0000051e88958000000a294ff60000016bec0000228a16d2800000)) else (if i < 81 then 0x736f23968000000000ab81a95440000261d8202feb7c80000000009bc8000002bd825106376198e100000000000000048bf051c026a3 else (if i < 82 then 0x84632d6e5ac01000000000bc49c00000000116a100000fe2110f6c000022940af0097f68000013e869a846acc18354870080000 else 0x29da1950f0000037b01fad2000009d6c4e769b0e0a541a695f75c5a8c605997e59e0629b0000000000a2001d30000000d5a00000))) else (if i < 86 then (if i < 84 then 0xbd82d11dd2a40db2c813702a6c000001e33c0c60000004564800001531000009f854fe922d4000f0800000062140a24000000001d538 else (if i < 85 then 0xa11a692f067006afa112a85e0a616c21bb0162708d5865c20a70a078d2000000000133c0a10b6c5c8b483069040000118805867c973d else 0x1a081000015adc384798f3662968c21300000000081449f8d8970f0000073e11452a6f3509d304d974d0f34067800009370007d8)) else (if i < 88 then (if i < 87 then 0x8d88dd906bcc405b02812125e95a6a850ea378592bd8000000000000000905a6f9c000003d08034bb000005aa716b55d92a7922532e6 else 0x675521a309ae84fe9e00000603911a2582805da0e173c0000086c0a33acdcc871d82b711422dc8e4c4cecc000087e0041db) else (if i < 89 then 0x566000000ace9e3a8700000ffa478f842a0000000000000808782600000000000000000045cf1aada873c84aa3000000000aa4a898bf else 0xb2ba5a884000000000a6a7176d4000000600000028b2c00001995a81d2838d100000000000000000064374bd0026284fc013f2065a92)))) else (if i < 96 then (if i < 93 then (if i < 91 then 0x2ed6800003128586c09cae57104b23ae07301423138403b3a00000000000000b94c003420000000009ec000000bcb491ca1 else (if i < 92 then 0x107b5b9800000261c0ac40910e0000000000000028cad98660000000001cebca788c93bc00000000069a02b9e1000000000 else 0x2c462d7800000247daa6b040000bcd740000bdc86208c0000194840000054985817cb6b9255380000000021e72aa5bc00001f3400000)) else (if i < 94 then 0x41c6cd9838ff3192725ef224bb0000000584000000000b9978de0300000e5722b679a98079970000053684af848e810fe4e000000000 else (if i < 95 then 0x9a704000022022e4b000000000030f69213c00002e5330000077849eed0000010e422648000020a1e545603421000018fe0bcaba8d80 else 0x486e2b32177cc00000ae4140000325680000246d83208ac97e795a03e2400000436800007de60fd9b00001695b0000000006af500000))) else (if i < 99 then (if i < 97 then 0x27ada00001c9e85b8c4000000000fa98a54216b9e6641d8f5d000011e8a000017aec8ea280000000000000934e4000048afc0000 else (if i < 98 then 0x39804000000000c18584e84c03065c1400007844c0d83107707f160000248005eac0000033dc9ba66b1d34000095b540fb300002bc1e else 0xae61d9e0596a0000000000000000000000000000000056cf4000000001bfe519f3800001c4540000445711c2387400395b538f40000)) else (if i < 101 then (if i < 100 then 0x2500e7cc16a262e601ccf0000041230a8d8b4050b200000021a70000019e3c551a03add1c13092bdaea00c1f27e7d482042a57aa040 else 0x5b3c23f905d6c4b248909a2ea0b15518000008778000000000d3800000000000000226dd28048d8ccadc30000028e655b09000000000) else (if i < 102 then 0x27c62c251331699510217a6e7bc1b106becc000012d5d00001d13e560000000a448104c89fa0000007df75d054000000000000000000 else 0x9056d27a157af695c4b4b9800007ad6c000049f3000000000290f170fc9df9621198ff922517400001f08288060ee30000033d81df00))))))) else (if i < 154 then (if i < 128 then (if i < 115 then (if i < 109 then (if i < 106 then (if i < 104 then 0x20c9e536f580807f900cea000002ea090000000000000037900000000004d1c00000000008a6878d299c1200001a05a253880000 else (if i < 105 then 0x7ac16d9049c24af6e937388a5d48a16dfcc06956ad500000002ba8adca400001d678110269a78000048d800000ac7029f410000108f2 else 0x61522325a11aa5959e9f998000000002e95f4b77d2582000021fe003f053dc000002102a00002204049386b22172e0187c29a6448e21)) else (if i < 107 then 0xa680088023079d800b045863668d1806ee65534a74100000290ed00001db4000001d93e0000000007661000002da0c63a1000000000 else (if i < 108 then 0x6d581e4825c01000007e348000000000e492000028cac8cf81109c1d04851e90456a57da39e4a90e3734062048a2b5e7dd2000005dc1 else 0x44e048804000016b6024a11018025acdb0e6314840000a0560009856e2514216f0f139d15ac040000000003864000000000bc3d44cda))) else (if i < 112 then (if i < 110 then 0x9a6600000000002100000000001bf070a240c59e848f80000000026ee917c499de500000000080c000000852fd30405fd68a658 else (if i < 111 then 0x37018000000000794c81048000057af00000000021e8000000215e00001e70ca2fdc00000000000004df7800007d08a39cd5056c0000 else 0x36600d0606fa6000008c6aaf6c1a731c48d08b181974c0000000002347800000000110812314400001fdac531eaacd52c104929d9c60)) else (if i < 113 then 0x756700c60903d4fa8014fa401c9a05480000000019a6c2b38257cc9d02424b0691ca5dc200002cef200000000000002270c596cc0000 else (if i < 114 then 0xa3ef1eace0e6a672908e058163d000029f474c2edfdc0155c0cf4800002a41800001d2bd0000195da7adcea229683455702494fde14c else 0xb93700000000003c0c00002baa03f685168403efc00008630d39a80800cdc942a1900000a6f1c000000001b5880000000001c1b15b60)))) else (if i < 121 then (if i < 118 then (if i < 116 then 0x4ec42096900000dc800000249c00a40464bf0000052695a2100000adb30000000000848448f680000a8062495b000012e0d580c80000 else (if i < 117 then 0xb41990116000021ae0a2486ee41000025cd500000000000002eebc260252a90b51313da11726800002f968a32100001515c else 0x152c66c5c800000946eeb183bc36ef06321cc12c04a418000000002aa83238780000000000f3ea3cb56d802d000000022aa80000)) else (if i < 119 then 0x8a168000000002ca9ea762626f5b0e3433df00000000000000000057602a9187e64e2a8000000000001224d78500000000000002b9a3 else (if i < 120 then 0xff7509535ff92d88100001768200000fc9656e80b5b700000889c72e04000065382605c1b72461001534000005390620494e3757061 else 0x22b9f50a00000022c600000a34b40000000024b3c019040000af6cd3910120290da1410808a697dea40000000019c06000011769))) else (if i < 124 then (if i < 122 then 0x29f9249a847a920df74000000000efe000000c049775b2d884a20840000163218fe9acd0028a1abd68683c0716991df6ed200000 else (if i < 123 then 0x26acc66524000000001098967d4000007a738000032b31a54800001c34a35f680000a3280000052282a1a71105837a1314d80000 else 0x9d8fe14e44a088ff64394487c8c2f4180000000000000ae211b0487e96014f0000000000a40815a580022685bd000017db0b65010ca1)) else (if i < 126 then (if i < 125 then 0x11a840000716107072b0e31294d23219b948000009908000004eb368a31c1f316a3c0000159d400007bf04355591a0cf9e000002a0a3 else 0x82c891eb99f36000003487a1a6d8c660542d0000296e900002d421b9b02414d3c0c0000042420000046241ee3c96e6a78cc3a5d80f33) else (if i < 127 then 0xf1c68125400002300046330000123805f778767000001df1a2d6c58b5a2006186bd711c101c857d78dd8081e01152d95baa4d21 else 0x12504000056f1df401abccc0000000000000000010f219d918a961af460d3daaa8cece9866fca0ee400000000000002bf01019000000))))) else (if i < 141 then (if i < 134 then (if i < 131 then (if i < 129 then 0x4bf6e80db0ef227509ace0a874d00002e5dab90ccca009879800003b53000000000000009862402480000218bd04901669e000017ddb else (if i < 130 then 0x412840000b068486000000000004a60c000051e79a58000000801ea78cde16100002b82024f80da800b019046997201c69e266fc0000 else 0x40430b45a1129eb1806986110a31a21288e0580c0000048b5c848007b1814c636c79cb3db4a00000098706cb619a25ab8e01c1240000)) else (if i < 132 then 0xaf48c000091a040000000000b809513a7510a648c000041e180000754a0888900000000076984785028398b73300001db3c00002a82f else (if i < 133 then 0x2d6aa2a7c000008888ddfa044b0599482a96ae9860000081a100002833e0e76c000000001c96800002caa6543a2ea5f9acb80000 else 0xa90841f09000000000000014e20bcb3c0000b2c4e57858638c9f0024f8ce5d000000c84d8de400000b6b02ecb28611e8c20000000000))) else (if i < 137 then (if i < 135 then 0xb4839211281ea16e300000000000c66c0000007300000ad2596b8618d3220152cc7a4e9032126072e76bc07ca0079197705827a2754c else (if i < 136 then 0x1bae670521442d110409a80382007ce900001b772bbb18000000001f6405d78000000e1469851607840000ab66d2241709340000 else 0x299b1a71900000049005b00e804a70a956808538a45ec20e48fdcc149421e4958a34a672000023e5d00002723300000c8c0)) else (if i < 139 then (if i < 138 then 0xfca001a85115d1098cddde24a24b7ddbd8245b060060121920890258920fe414e06000000000a38a87fe800001d13cbab025002 else 0xa0982f80ef6337df680000474013600b67018cc900000000024574000046c86c96600000000000001e11e2c8040000) else (if i < 140 then 0x74cfc000000002ac3c000009808984600000000000000a3025c260000000000ba96000000000158807504a28e0641a480c1000000000 else 0x16b1774f1860400003032256d86c079b1da00000000000001bcca56f056509263a4704635a600000833a4000060f780000000000000)))) else (if i < 147 then (if i < 144 then (if i < 142 then 0x96d0c0b706bc4ad3e9162640000735800000247740e8163d3c000000002c41060218000000002c7db000000000a9d02250000000aea1 else (if i < 143 then 0x94d6dd91e6ee00489c6181c00000000182820000000009440ed21e0000111925f769dd01000010bc682b9d17122bf680000458a94900 else 0x19610000088c04000000002b1270000001da000006d613a36228030000000007fc61f0d41c4480989924000000000018a5e00001194d)) else (if i < 145 then 0x201a5d81298e54d930000020812a3afc866000001310600000000053a00108300000fa1600002db40a609c86121ca100000347c0ca0c else (if i < 146 then 0x15c000000ba90761815c200000142aa5b211be8028e10e7f58d722bb884918078080fca4000077419f782492994c8c014240000 else 0x18aec8f7c22bcc27380123000001af2109c6cdb8053a6cc3c93837428dd905264180000016ab200000a98d000004698413449510))) else (if i < 150 then (if i < 148 then 0xc980bc435a8da0000163245f40c00002900163bda47c0797227d8dfa5a49a32dc4685fcd0e4800002a48930769d9703e84c0000 else (if i < 149 then 0x4e4001421020000000000016825d4c0143ca0754000025a84a7c54990026c62afc0000000000629c8bd86000018f125e779b6c8 else 0xbd0199e600002e98f00002acd900000000000000000000000000041224e8604b77699db5e726c8e84a48d0ff53ea800000000000000)) else (if i < 152 then (if i < 151 then 0x55199565a000000000000010e805baf0cc92000019e626219972bc00002785d0000000009847ea72154dc00000a8ce512809496e2a00 else 0x4eb81b6caac0fc00008a1c800006eb50cc01000028aac000000000a8b04b4865d4c5e00c0bb01a5758558c00005ec1423df00002415a) else (if i < 153 then 0x12c5c000019150bc3740000ab820000000001eb58ad78000009aa426bb90000000006ee15b8e00d5a6a3809b8817de11c011c5b0 else 0x6ed28000000001262090120000097208000031800000089bc93c503bc41c50627b803dd1000020ee83a0488080000000000)))))) else (if i < 180 then (if i < 167 then (if i < 160 then (if i < 157 then (if i < 155 then 0x54398000066a0400008af69109940138000000000f68000000000000000000000001a78600002cb0cb1d326de0bcdd02200859cc5d9a else (if i < 156 then 0x81411857000001665e8007800005697c31c1258f2d1958a29c41612d48696b891830000060ec80000ae3440000000002f80802026709 else 0x3cf84aa0300000000000000000083928000031c7e206a0000135f00a72000003ba847204b3c82ce0200001f23295379391e00000d580)) else (if i < 158 then 0x23c04d8d939804a2b0000000002609f9fe56ecb300000000090532ad238e33226008d804572300002414a42ab4f04853e39923d else (if i < 159 then 0x9a168c74883a04000000000000000001be3d7853eb0894e2e539a132519be4933fc9a148000005fa10000000004610004c16be62605a else 0x3201400009ecd0ac06af48568040000000000000000000000275a1b843e6ac01fe480cc030cc18be1376400000000016eb0000000000))) else (if i < 163 then (if i < 161 then 0x5002ca8c64a6da6014ec8943800000000004cef69c883ab78000000001c9da00002e8400000293dd000000000067014f586b9b00000 else (if i < 162 then 0x9bee0000046a840000a7cf400006f9817a844e660000000001dabc2f17800001cb280000109708a01000000000adcbc00000000274cc else 0x29f840000871c9cd050000000004dac1365f9b40eb8800000045516be798fdd0000000009fd6df9800000000003680cfcf2a44540000)) else (if i < 165 then (if i < 164 then 0xb90e400000000063a05c584bfc8016a800006967aa2401a0600000000000000000021e98ae608000006cc20521207a400002b1611b00 else 0x3e48400003100c9ac00c662b39b53861a300a3c10e7e805e840000a8684c3b6b18400000174600000000000c3f8b581975a) else (if i < 166 then 0x65c240fc0000022d82000021d8000001f5388b4105abd24f0529100000102a32d8794e36250aa8758255a45dbf51460aade1bd81bc31 else 0x860f40ac0bb872e1f000001ace05e41c2ea900000000016c6021d8a35811e04b42800000000009c8008f769c204b00c7d6404ec80000)))) else (if i < 173 then (if i < 170 then (if i < 168 then 0x10d0471a48000000000000000002702933f8000001fc0635808d9c87d586a1216e0000001e0e96a030000050825cb70b1f200000 else (if i < 169 then 0xb0f20000065c20000000000983c1b0fc000000000000001c25f380775820a9f00002305a00000471800002311c000022d84000019e73 else 0x725c8ec48285aee930000017c930000264dfbdb64a7544096800003f64109064ad7c040036b24000000001a519ae66969b0)) else (if i < 171 then 0x976c00000b7a02ae21ab286f12100001d764a4e6251cc2ef6e879545180d0c847ef0a8d4372f0823c000002add00000cec8 else (if i < 172 then 0x50328a0929b56861d08ae08cbc8000010f2300002b41e4d8c104835020817c000000000043d6c42bda6fc400000000183b020081452d else 0xac1040000a5c4a64a350584000028e013621000000000224840000372ca4cb24d87ad12031e0c00004176c0000000000000000000000))) else (if i < 176 then (if i < 174 then 0x59035e58a0c22ab0cd8e8c000000000511a5745435f22378c8c448000066a11850391e00e5e092f280000a6c10033c7f260dada else (if i < 175 then 0x23a807c5c4290000000000087802700c9421800003772238e800000000000000e5da08efe70810000000003e649b7ca9b8e00000 else 0x66d2400000ac00b380000000306b1120574e000019ec800000000000000415a000000000641a0000082c494402000001dbc5498149c0)) else (if i < 178 then (if i < 177 then 0x86180888854b0000004b4a64fdaa7d020dea00000000001c02704878000000088160868894bb404daac686b4039f0e5d1bc57e0ee8de else 0x5611800006fb9000007ad791f3e04618000020d81d25169289e4000000144844f4000000993660312862640000000022951bdb5e4c32) else (if i < 179 then 0x9ed6092bc0000000000000219b00000000007844a8f12b80080000000020de300002c5122f0ceb64c74e4e50b0214000000000000000 else 0x441af5c089418716648dd48184000001e3c8f24c00007b40904a760f8400001ce01d5298e931e4804d97217db0000039c11c17abc86))))) else (if i < 193 then (if i < 186 then (if i < 183 then (if i < 181 then 0x321204a9ea080145897858000004d9656a86a0dadf9e09807c00007840e668078c1031b9514fe70e900000710445049f0c6000000000 else (if i < 182 then 0x4c39a1af631606a5916b980000000000000216991be00000063bb8fc8411ea0ca9ebd42501641044dd415000016b0456d00d200 else 0x5900ca39c31ac40000789221f0200001b5dc406312290000000000425740000add4cfd8c0000000008fdc800009b8b4000000001b101)) else (if i < 184 then 0x31bc80000022418f607705478867ba013ebd3dc81df2067c4a84088a808000078e3130b9723911f8817371f41200000ff0ca8ee00000 else (if i < 185 then 0x520607a122c1c800004b77800009201905203f89c00006560c0000af0821f58000008b1e6f908000085db49cbc00001ede46ae012710 else 0x2680a0eb40000687c80000b6101f424000029fb9a016000004ccf80000873d80000000004da80000000000000254301ec82611e))) else (if i < 189 then (if i < 187 then 0x86260a87200001f6f60000000008820806a02320143601ee000000a45c045a151cf62c926f810c24900000933d00001da6ca87465af0 else (if i < 188 then 0x6e3b90fa10000184c25556dc2e659c0a0762209a6bb009eca5c2924448400009d304000000000e672000019901b29800c21 else 0x6ed514e001f2000000000000000b048959de000025b8253825a681a7e8400000000269114dd748a2132f3800001548a39e600001399e)) else (if i < 191 then (if i < 190 then 0x59900000068560543c00000000000000000000000000000001da0a3f69af6bd0d190289e0fc0e863f1fe82e932000000000000000000 else 0x1f20a070400000000063b5ccd5144f696107920c000000000000009618000006f21cef820000112af000029d4016a00643f000028369) else (if i < 192 then 0x96f78b9865fc1800004163137db55e0a18809e8867ade41768890858a3000005617a4a422db78000003cf50f729c4b4053d064840000 else 0x51acc0000000012e7589a85a2803fba00000a57a6543600000000028d9af35a3258184da4bc9c000034500fa6488138536942c85a7b1)))) else (if i < 199 then (if i < 196 then (if i < 194 then 0x36ac0000000001e4e600000000021e200000000002dc60000245f01581276df7d0b46cbca98a400001c7010e2157ec04686000026cc0 else (if i < 195 then 0x792a94039000000000b4704afe100000000030931451c000000000a700000003f678000000002ae18000012ddc00002be90b10300000 else 0x5aa255be600000339e000000bbc00000028016422e003a72100000518cc272100002410d2cc0185c2a36a83a489a8620460000000000)) else (if i < 197 then 0x5e4c400008a04c00006a20a58e02a37930881024000000000170803fd448b8000000be8000002cf6900001f9603fd200000000000000 else (if i < 198 then 0x7494252de00000a64236d7524d000001e0b00000007c095e000000377010648a8e18000066a1c000063378347278568000050e20a100 else 0xa71019e5e3c382c88c00000d3c8000003d9272e1169005dac2b41000000000000002cd5c000000000bd6d400000000000001f2855cb3))) else (if i < 202 then (if i < 200 then 0xb9f6800003536a3e7500001945a4427c0000a32a8cd8032f400000297868640971000000adc4250039db68dc840d87893090000090a1 else (if i < 201 then 0x39011e3c9b04000007cb82392c2f6cc000056e10579000000000000001f8f39bcb422b6b75785a0f00000000018792c65016aa4a218 else 0x8f25a621e11c79b5ddbb26400003b5205fbf8de591eca0000000007bef000008ea52236052480000051199d0f1b0a42067239f209871)) else (if i < 204 then (if i < 203 then 0x12cc00000000000003ab680000b88c028483f76a61e8000000000000019ed092968fc908f73c00000e878000000002af001fc4ababf else 0x8f7680000bb9c04f1044568cada00002710022286628b14b96c31017b4867000000000007a002d2860000000008f33186bc) else (if i < 205 then 0x2e6869ec7739c1a7876aec1ec0700002acc11dbc0000000000000000000000062909938107101edec000025ae0a0afc0000000000000 else 0xc418000000002ae833a9c8a9760f830000000001993000000609036a1888217e36ad4a1000026d401da0260c657226079f443a40000)))))))) else (if i < 309 then (if i < 257 then (if i < 231 then (if i < 218 then (if i < 212 then (if i < 209 then (if i < 207 then 0x785a1cb129b368b451a7b053a900e3d400004f882ce0c000000000a926199060000000004b76e20221e091f4800000186425ed029651 else (if i < 208 then 0x81e04000000002810d5dcd000000000066040000117d8a0cb43ff5000019b120c01a4a056b98973330000070768348400000000166da else 0xb9778fada4ba8299df6e0027dcd0000000000000135cd1c3686bdb5aaf000008a80400007c3c03f0039a0100c83f28d795f000025866)) else (if i < 210 then 0x10bf00000134c67b7cc0f184ed3000008304c000008ea400000000052e40182400005ae0096895b8f0d480642d80e8499f6c0000 else (if i < 211 then 0x9018a66465a005c769be81a60a4000070394000000000e2da7cc62012400001f2a14d76a5b9b4ba9debb6b3a304cc0 else 0x64a79a760000003e4851410000000000e9e0000023dceab1a6a82d7b76e9abd9036cd2b000001995e00000164076e00000000002f35c))) else (if i < 215 then (if i < 213 then 0xb189c0000b3c200000000000000bac00445a00002babc00002ce1800000000083cf18d4200002b6210000000000000000003fa7ddd70 else (if i < 214 then 0x1a981e65166f82815c22438738400002a1bf59a61af1f8e92028a8781800000000000000000022f6071c48255b684000000a3c800000 else 0xb4048000031f3054ceac906ee3e05b04279800002c48100000000030582555b00000000015c90000011364000022470748954ac14088)) else (if i < 216 then 0x3de99b55a4a3a1edf6223c2c400afe48b6210f44885697e68ddf1283261982148400c20566079b180000003590709680000b33a00100 else (if i < 217 then 0x66d825a70ab825e3db000029f09000013c5da8a6c00005ddb6973854d19016000000000017a240000b4799032729b90289b00002202c else 0x2bba0000000000000014f8863218dd004c6840000425069ca156a05dcf2000009d3c00000ccc87cc845f92000000000000023d69)))) else (if i < 224 then (if i < 221 then (if i < 219 then 0x83000000bdc259dd0a036000002758228cc0000000000000000009b1300000b71009960443a0aaec00002a54086d20f8e980f8c0000 else (if i < 220 then 0xa3ab07c1200000000026900f9a10000110a02a60c0000000006dec000000000a31a400006d8000000428269fbf275c0db00000009e6a else 0x36c619bc97225a189c6c52290ad9381a90e970bc9f9f278382c464725200000819385da000000f70000002202a000000000000019703)) else (if i < 222 then 0x1b1e0b379af0dcaeba5ac810000142a100000e15d00001aa0100001b8ec98778000000001f1d40000262c7000002580a056e065a else (if i < 223 then 0x8f7206202ae3a40000000029ba1b83621871863096081349322c127b7857e809a600f480000013acc00000ef190b2a1a8c81bc000000 else 0x603caee3f646d8000077dc80000000016201000003de0bc36a75a717c20000080d993123a8ef800002be0575c239f915baaa035c71e0))) else (if i < 227 then (if i < 225 then 0x1d44a4e5a4e6a5082125b2c99a1001000000000022e610000000009604a10800f9742429687685acb880200000a62855b809c00d3446 else (if i < 226 then 0x94100020c00002b1008766000006e751fcb93de81f0bc256f9081e2104ae0402c76a47dba8efc000000002927000000153c5a6180000 else 0x87934c84b4920859bd00002d7846c0649e603796ac9690000241139942400009d42e61daab2f400001096ed74000001bd01000009a3d)) else (if i < 229 then (if i < 228 then 0x17006d10900001970000000fc8c4f6f4000015d411eef81eb5dce19ef0a77904d6440000b0192f63538404711c0cb18000000001a29f else 0xb99c9e0481078800007224800000020000000b20c23c13bf21b7847c8f07f205eb2699219fd340000135014c010000023b9ad17d3691) else (if i < 230 then 0x25df081b1aafdf5fe000000b14400000b0c8c00003afd00000ab002b76b2e8600000162016133b15d40000000000000138080000 else 0x10dc86e5a000000000000020e482858155032b118d680a3421915104918e660000000000110016a007adc8000000000000052991a048))))) else (if i < 244 then (if i < 237 then (if i < 234 then (if i < 232 then 0x4180250834140000003292199587a722e518000006012000000000000000000000000000b90a400000840c00006238000003f2863b68 else (if i < 233 then 0x1fa5e5c47180c099b700000000017b42000029a80164cd9706a8cc2319c9b0852989b0e00000025622e45a1154dba9848f322a81 else 0xa6d1d260c034256430ba9760f7015c9a973e1b6f028a0478f80000b3bcc23b62082400009f356af039f0fdaa4805d05fa5b)) else (if i < 235 then 0x7acc223e0b1b40c5a1000010fdd000000000a7824a3ec96100000058ef135413f6000000000017bf0343b01fdea6801ae600027a1888 else (if i < 236 then 0xcb48458124ce000001d33db33c80000000000000000007ca76fc001d808d606e933000000000b004800008e0b40000000000000 else 0x2df000336a705aa808c0000000000000510120d9e2af68000008e0c8180af879733c0000000000b078000000000ecdaaa198fdc8))) else (if i < 240 then (if i < 238 then 0x6ee107180000012b5d0000000001d470c80400001fdb087cc667bf000004600480fa3b2185d0155400e6a00000b0484b264a68c00000 else (if i < 239 then 0x2b9c8fddd00002619fa41da70805af892f5d00002edb2000000000748f80c1c0000015893c398229e95f026421b286000000c0862586 else 0x7b0057e182e5699012000007de0000027a2d6947dd53e93a01a10158165a6498df31f78300c059c4a000000000a8e861bcc21e25a522)) else (if i < 242 then (if i < 241 then 0x1c8e028080d830b6a00365a1ff9800004c62000007e6045b98756b5e0720000217f0b359000006824a8892000000000000013658 else 0xa550827098ec000000000016b00524840000000017c843fdd40000678f5e1524189c00008e801879300002619eab88037211cdc16a80) else (if i < 243 then 0x295c27440713b0802c319692f3928999f830862f23a499e6680000a9c62a1921f3d5348018746101c18e9e5630 else 0x1606246f63d780fd12b3c54b28000001b372b2a480000000005898000012bb079c01590000000030a49a4218ed469700000000000000)))) else (if i < 250 then (if i < 247 then (if i < 245 then 0x60c0000b95060404a2afd34c0935c9b90014d20000000001f99638278000000000603f49295f48c764c14b64a19640000 else (if i < 246 then 0x1f32081922f01038262073c932c073120d3a4000079a05c81294d79d63e00000000055e0000002243cfce02f37a96c5 else 0x9d545a57297400e021000000f0b9bc78579e00002619992369843c2308553a10297921bc0000000001e13910ad00001bb00)) else (if i < 248 then 0xb305233600000297f0000002058553c800009b67855a39c14003000000093bf0000000006eef145e669e062b0c4923086894c2a4c85a else (if i < 249 then 0x38060171871b9291ed0dd74fddc00001eb4b000000000b46fd4da79c061cef0000019d707472c0000a34000000000000000456100000 else 0x11b021b5d00002b4218a3a675b900000a6547e202c01f482f980b04183000006c048dd890000000000aeb8c26000000000000001a001))) else (if i < 253 then (if i < 251 then 0x6a8025b980e4e66b4c7e80007dab83000000b2a00000000001f1f100000000000002e959885011d6066731a880a8086cd5aa4e79f270 else (if i < 252 then 0x8dc32eb60671c800000000000006216c945c3cc007646899d59fc889180b260000005e8f00000c2042c400005a32c0000008f1300000 else 0x75002185405e26ab806477400005b00442b900001051ea38242ea10000049980d3a0716c81f800000603600000b4399fadb69bd40000)) else (if i < 255 then (if i < 254 then 0x101740000170710660bc76a665c00000bf03ada44e221000000000864109fa03ad7a70244fe84000025ccc000000001b001000001e80 else 0xf1e002f1841d21bc48491006d680000000007e1200001c49277d919610282a800006ff800000000017d601d1808fcc0757a2f61) else (if i < 256 then 0x38940503915d11150253c617f5c67dc8ccda00001b3c8bb4c2f55b9e5cac60d000012e5daeaf53add58d2ce712baaf15e9800002caa0 else 0x2a5df00000000008a0021c08a3d400000000000006a1680000000000000a6778adda8cd8497840000154da2ea612120000000000)))))) else (if i < 283 then (if i < 270 then (if i < 263 then (if i < 260 then (if i < 258 then 0x222d85ef18000060205e580ba1c80000354c000006f0d10d120000113e186f7661d9000000000b4648c8037038931574bb740000 else (if i < 259 then 0x87322997500002ed895ae1c00001380220c9b0e1a61aa9d240acf0af6255fb20000119579890000009a824000000000000060819b0e8 else 0x186695f8202025698100001975ba76f6bb2159578000000002e540032cc6eaa455a5d9080000054e9299800000ba162b5a067b82cb1e)) else (if i < 261 then 0x7778000007c1c14cd1ab086ac098a3c93a103600000000000000000000000005bc0e8e2038f69e1c88d7c800001f1463a920000291e3 else (if i < 262 then 0xb928409c01286c353939404870009e6d795e00002dc709106400000000192a191a10d3306437c9d09000008f1e000010112ab0080000 else 0x4be24361055841d71ea8a8515f169c0400003b3a40000686043f210000045b31bc12b5c93f84891b077f91ac0000000000044630776d))) else (if i < 266 then (if i < 264 then 0xc061628f0000000008d588d9062f6082083486007f804c0cc0000b79000000149387792514482a9000178000000000000000001e2c8 else (if i < 265 then 0xf791a9195a004000000001da06504f99c3100001e3e08819dea00610c28ce900000c25aa12005c19000018af07d182ef406f7b2b8c9 else 0xae640000000001246000000000004c023c4a04216f61d7af29a3440000226b6319a0000130214fd30000030986b323757a55fd9)) else (if i < 268 then (if i < 267 then 0x296445c80000008d38000009cd064cbd000001a401d580000083c06c0b703c25a2480f049364d947cc742a0000000006b200a6d4 else 0x974c0000000001e1d4a72800000b1c4146bd1873000000000273c170d5000006310197301fe8400000000237e8000029e3d1af013089) else (if i < 269 then 0x5f01444da00002dec07b5ca1c6031d6915004a4fe8a2d679512312542aa90f0791814fa1000000000aeaf8d60000001025d418800000 else 0x5f40ac6493500000009720d85422f60c0000000000000546b0000000608b48000000000073f80c2723a968000074e48000000001d7be)))) else (if i < 276 then (if i < 273 then (if i < 271 then 0x20282db02462841cb03620000002aec4f881000018ee8000018ec8034b4000000000b65a79992189237c8467c8000024360045240000 else (if i < 272 then 0x1515e79a42bbaa00000f26000000000000002b7dd000027fdc538e00000000000000026c00000000014e3f000000000 else 0x1a0fc0000000019c7472990c5303601af6c011c0471708518000004c6fe82987f0c1e680a3a822b02b2800300016845828cad4088188)) else (if i < 274 then 0x2874041a79ce4a3a57843da000000000024c2ae3fae0000000b07800000000027aa10000000006be64000080a10000026054723c else (if i < 275 then 0x30525dd8016c0d04dc41018000036e628110716053d154b36ab8dd310c2110000002c6d606779c2e08ea85313d00002f4407d4fa70e0 else 0x277c00000a08f86d541bf823a0c072402b9e20848dce000000000019e05c40100000000074d0000003236a04801f07e98da00001ba4a))) else (if i < 279 then (if i < 277 then 0x5218c03000000000000009d667c81ae7c00000000005db246e9c00000000089b32bca1000001d3029f807ce000002f253000022d61 else (if i < 278 then 0x2a91c70b6800003c321035e5b000000000001826372af00000ac66e11709beb4000086204871578208f7d000001cf80a6c850400 else 0x56c800000000000000000015e000000965023c680000006e900000000000000ff7219a0043dc00000000003d8e40744358a5754)) else (if i < 281 then (if i < 280 then 0x2820125aa0000000001b7c000009ff8e467600000000087c0c0000000000b4056f02d4b95207800009016a18957b122c9086fa651e87 else 0xae2f9a2981c4a8261e00002df8000002f44d30b840000000002300298c6cae80000048805aecd8bf6000000f9e7d07d9273188280000) else (if i < 282 then 0x2c998a2ca800008f9c80000592a044c0a8e2280d9b20f2b690b716000006d1d5364100000273968968000044e4969486424ac21e else 0x60f512e550000000005981800004064099632242400008267d30090000000002bc1a1f050000000000000000001dd0e85c1000000000))))) else (if i < 296 then (if i < 289 then (if i < 286 then (if i < 284 then 0x3e88c0000208600000376c000004c3000000848f00000764d83cc87dcc0000000000000006800dc5a4d80a6eef886b80000b31a5fa33 else (if i < 285 then 0xad106ac60000025a803746dd04a413750dda0000000006d07d6c06000016a880000283922007000005fe191360657d66c29b3e9e5130 else 0x57c1a55036448cbd3000000576e126240000a03068509bbfc8a09c1fe60d883000000000000013bcc000000000a7dc59e4000002a86f)) else (if i < 287 then 0x2c2a200001a3019e5307d81865c0d99800000000000000000045a80b42133bc8000029b98000000e0400007e8089c84000000000 else (if i < 288 then 0x1408000000642a0000000000000000001c300cdce33938000096e0eed006c720000065d250e81210aa19bc8398000007c002a2c0 else 0x23a84785a400009ca186a840064135f634a01a1c87bcc000000000281e3000000000000008112000019603ace62b681))) else (if i < 292 then (if i < 290 then 0x278da9df74000000002312a00000c76000001d2be00000000056b74bc89942000000640d9cf8154020000000001be31 else (if i < 291 then 0x3700deab11f289f1beae9800000505ce576cbd6f400002b9819f74bd2a18dc22f6c0000000000000042280118000000ef8c544a00000 else 0xcc0d3a4000001bb98548f1540b00001c5543084a5f192eb6a441e5e2f0000016e1127901b10099069f32c1633851909395790100000)) else (if i < 294 then (if i < 293 then 0x78e04000068f205c04bccb8000094b6000007d96d04da000000e0900002a1093432971804194099b900000000000002c88e7f40c0000 else 0x270f11b6066f200000a5b11258400000546900e78aff2000008809606020060a19059b847ef0400006f9d8670100001344000000e7e0) else (if i < 295 then 0x262b400004052187123cb0194da6d36a8d3f00001e1250000000000000000000c424549ea73c6764c0000000003fe099c04000023092 else 0x71f8061a400001980378280000099ee680cd00000319eafa04000025128000000000e5c80000245726c0604dc16196aba84000001fd8)))) else (if i < 302 then (if i < 299 then (if i < 297 then 0x79888000000002f6405058000004e730000087d25777000002785aba6246f98785c931a02c214000000db09609bb29ee058 else (if i < 298 then 0x8d39800005ef38000006a00ff9b625180000000000000000006e80000000000344c6bf1000002d3209b0e40000947c80000000000000 else 0x534840000000005ca041f740000000023ce9000012c5d00002148065f000000a5d1424391d78000002e486c6cc000014f0300001a7b0)) else (if i < 300 then 0x6a248000000001a38118d5c8482baef114205426400008f2b40000000000000000000000000000000a6a800000388002428000000000 else (if i < 301 then 0x83201025c000000000ae4a9030900000000000001ed88817caae1498d7c000055768000000000433f24a4ac9e060d68ce72836569d1e else 0x21dc0fd82a5514d70300000888479d69bde281b00866900001729913b0098ef83c1270da8fa303f090ed322ce18c38000005ac25f592))) else (if i < 305 then (if i < 303 then 0x2a4b3b4a1000000000104a0000024cc002f0800000000034279be121461a6cf4928059102805bb8d682789b49c80000000000000 else (if i < 304 then 0x28456640000000000936d8e1100000184000001e6010000161b3a56e076c08ada54ca17d1a47832000006900721900000a791c0000 else 0x33146b129b32797de283b8026108ae00000015722ea5e190721c5a6841000000000195dda8286b0a11df7934f000002a3e05f12166db)) else (if i < 307 then (if i < 306 then 0xb796044a13c39c00006dc3000003b580fda0000006cf0000023ddc0000000008bd99e17568bc8000085396af5b8327c0000b33a40000 else 0x13ea1afd20000000001da950000000000000000004f200fa2128f0880660000000000000064c18a39167c009e0000001612195cc) else (if i < 308 then 0x1876000001d09368c880000911680000000011da327e11768000000000041c01935a5721acb16a1f8e69c01380cda83000000000 else 0x52e8469f0393323d81b8f18000000000000000002ad98b0f25a260b2da5df4220a624c923f342b89f79974000000002ae3900002e1c0))))))) else (if i < 360 then (if i < 334 then (if i < 321 then (if i < 315 then (if i < 312 then (if i < 310 then 0x2294ca9102962755280000077508000076ef28ee9bc3240000784a000000000000007004a64417bd1c000066bd8000065dd8f1ec else (if i < 311 then 0xb4006f92000000000200f9e4615b2160e8c936008f6400000be360ef467a237e82673c000000ce928f5340000000022f92000010ca0 else 0x9ef6296be27402cb6487900000039f6a0d9cbb98ec6d700001269243d6a8e63a7304a7f200000000000001fa03000000000688047a21)) else (if i < 313 then 0xa230205e47afcca013e08800004bc8519b90000041af94f780000000000000000000000345221ee10000000002287000009ca000000 else (if i < 314 then 0x1c1725dd0d19210000022de2c6000000b6fc69c18b193000006455c0f660ed699e49a1760921000000633f4ce02b886000019690 else 0x9e440a54600000000000001fea100001ed5a7b81090da1bb8104c976400000008cfc3c4c3296a5dbc0000173005cb0e71e8000000000))) else (if i < 318 then (if i < 316 then 0x2da3c00001632599284000000001e1488ff69fb0000001f9ea4e6420660000000000000009333b756a3802000009cf0000003189 else (if i < 317 then 0x95d98000055e140000b4081462e08ce5fdbc0000000000000000000000074925b420000000000000024dbc0000200a800002750266da else 0x6b7d479a01b38070c8000000000000000000000019685000018a840000211bc5e0f1b9c917836369344262ae1a95bd18fe833b680000)) else (if i < 319 then 0x4732bae6b2d82cec8ab18800000000292951e019be92b8f61c699a0efae908000000000238000000b4fd400006f9000304000004a98 else (if i < 320 then 0x2fc194798a00e506690000251906ba057b31000000000000018e5d8d0080000000017c4eabc240000a7cf81f0300000000000001f204 else 0x87920a32700002c401000000000648ce57c9951094e0800000000081db2bc213c580000000000000000000000000000608c00000ee80)))) else (if i < 327 then (if i < 324 then (if i < 322 then 0x14405617c323d03e6000000000083842a1500000ba168d5b000000000000000000066369b6d470d22c4160a321a600af8840003 else (if i < 323 then 0x846100000000000000044c00000291b0000000002ee092386177d42ce78000091434000000002c4c80000290bf18842937073f000000 else 0x45d8c7a3c861786880610723c16128787b00000000000ba7000000000000000a60eeb4404ca8400007e20405a0742c4fe01)) else (if i < 325 then 0x28221725e545d00000b2b80000000001916800001374d0000117007c8000000a5bbedf810000021f66a5217c6c0000000000000207a2 else (if i < 326 then 0x25ef50598000016b8400000000056c0000009f4868e003c2c287c042a85d93cadc04000003802286c00000ae12226310c09535748785 else 0x18dee70f20c6da62d08000000c4858c99d105368300001ed611727a284d19491ad0093b680000b1fa06a800ca82200b83e00c790))) else (if i < 330 then (if i < 328 then 0x37834421500000000085e4a7d41b05309820610c8369e7a0c56eb289c000000a0fa42d06000000000a9a84cf8103ef40000447800000 else (if i < 329 then 0x37e851a2f00002e34070580434f00000000048c30829ea948400005fb8a82a100001f6e06524800007e3026ba90000000008d4500000 else 0x1da7011824558c12ec1a968a07a668e4341888560b47a6d9f2b5885dd62b16419b6600000000029006f7405f0c40000000019d46)) else (if i < 332 then (if i < 331 then 0xc6180000120d1b7747a61c00004683000002e802a51818084000000000000078599bf1400002a3b900000000000002d8bc000000000 else 0xd77566030000000004aa2400006af2000000000027863a0f0000089e08024c0000000000000235e0ae2e6df04000000000773685432) else (if i < 333 then 0x1a8e000001b2609043000001230628516061478302c5d4000078084e3c946422c500b0e480000acaa5ebb7476480000 else 0x11685c18bd04036720000271a29d6ec0000641800000274a86bd89d7300000bca96df01b21a4a26300000000060cc0249e3f73878b0))))) else (if i < 347 then (if i < 340 then (if i < 337 then (if i < 335 then 0x6878000008324a906329db2ea0800000000000001b2467de8400000000113212c96abca3998a0b698151400000bbe6c0000782181766 else (if i < 336 then 0x2238100001753000000000067a00499b0f7ca7cde000000000aed90cf5a4ea4800000000018a1000017cf418a9de50000002af83 else 0xee0000000846000001528683a02b8e62d68547a0aec08000000000000044399b51200001d9f0574cc00005e00c00008ba103621)) else (if i < 338 then 0x90440c1c600001e35400000000096001141eaccb5ee987ff74255e7096c000061d08730000001e79e0000132120c301e0200000074e0 else (if i < 339 then 0x45c816930643a5dce0978cd6c81ae8fa701e0000000003f69daf800a20e64391788000000000000002c47800000000028da000000000 else 0x2b6493c5b0000027e4a77cc417ce051c0fd6c000000002368c00000000057c3c000000e02bd1e6be7dfa30a614ef6a01c2000000))) else (if i < 343 then (if i < 341 then 0x3cf825583bc440000000000000021bc29d8000002798b8fb22225800000000035c18000019104000023040000024dc57de4458000000 else (if i < 342 then 0x120e40000bbfd6ebf02400122086d481adf2000023a10000000000ac6689121afe7c00003f6a46ae0000021884a727039295f7b28939 else 0xa331c372a06a80000000018ed1a38200000000000000480600000000000000888b40000000021e5a170ce775a00002da40b0248d8c8)) else (if i < 345 then (if i < 344 then 0x8b012741e440f01f1021f9894ec4484a7d400000167800000000000000000005cc20000075255bb49157c9450000000000000002d901 else 0x9c330000002d1800006a72000004849800007c8716e3d3541a070100000000012339680000001d4041cc10fe48689c8000000001339e) else (if i < 346 then 0x1df13000000000000000000a39a6659500000d61e454123f5a16820ab83000018f520000000009db00f2e070598baa1256262d12 else 0xa87800000000000000000020732615c80000ba368000046440030879e90000016204000097a2c813f5c210000047c7ecae4000000000)))) else (if i < 353 then (if i < 350 then (if i < 348 then 0x33b45a8f2050180000130840000045229c800ad205e100000233e129b829f2144800e960000017e5c423680000613c800007ec41f118 else (if i < 349 then 0x12b36000022ee1a768000006d920000000000000000001ba0004d8130d921782b383ad000000077231fe3c000028b3f else 0xa7caa1e4bbdd980000a1826729ea72faa01e53a6201a80000000008a2807fe92f168a664aca85e4e900002b140000012868b298e72a1)) else (if i < 351 then 0x6ef50000003da4000049344000015920856b0000133180000104b900001509ca2800a1e93487d4a8c8ec4a81400000000001f6805a06 else (if i < 352 then 0x2d17400004410403300000000c03fc4a3b040000120bfb20b67ebe69b200000a7380e9debbf700f682eca00000000000000 else 0xb1240000000000a2e986100956f9b87814de731580000000000000000006c186a2040000799a000000c4cc0000a4282ef4679679f886))) else (if i < 356 then (if i < 354 then 0xb7a13b5c807b0839900000263c67f52774f005404d978c1f6ad6e15509863000000a0e100000472000000000000000 else (if i < 355 then 0x6a96a5f09a5f1800000000000004134e875b0000166003cf900000ace84000000002579322280000000000000034a19eb26 else 0x1a29e10d20a38166f6ae73500000bbccb9cccba8003b82cba100000b98000002a4a17078000004108cc7da04f01ab00)) else (if i < 358 then (if i < 357 then 0x2fc1466a0000000002b6d936391fc02ca1278f02a31100001b51e1ed8205c8282113bc52064a2ae992f215b6696db400009127cd0e2 else 0x1ba107c81000009b401cd802b0c158323b2c7b9c1bd6000001cbbc0000045b90000125926be04000025530000000000000064a0e88b9) else (if i < 359 then 0x769880000955693fe90000000004c00000007c98000000000000009f1600000a30a8000000000050000001dfe0 else 0x24d5ab81780000b2c4910ac8e885adda0000067483586082209116e7dd80000000000a07a07a33723281c000000c1c9000000000)))))) else (if i < 386 then (if i < 373 then (if i < 366 then (if i < 363 then (if i < 361 then 0x49000000076200d3060000037008c1300000000000c4100001eb0822c0133c30000007897eb2852a4bcdd4000000002bf1e90232b7cd else (if i < 362 then 0x5f7ca4700ae685855a000007aa1a875c2dc0594600000000000000a68a4a0bc0000000000000000006b432e1c6757a00000 else 0x2dac601ecc00000000000008328999e04d6169ef1783921c04bda84a7612d776ae1b0eb68087046258c6ca77e4a7c5f3841822c1)) else (if i < 364 then 0x7f30506da000017961aa886a74100000d1b700002b4399ec2965284c904000000001f3696de8c00007d04000005207189c600001d79c else (if i < 365 then 0xa7a00d6da0697848a411b6a153f00000b40c0836000000000050a0a18f400007780800005ed68000000000e775262110e200000052a6 else 0x694040000ae68238131caf09b21000000000aca9ea983000000000262e47e809ec9e545503d029b239aca11a1e06ea29cc0b3ba27e2a))) else (if i < 369 then (if i < 367 then 0xafdd5e10000000000050a22cc12000007f817c3286e4ca830183bc78384000066725262174cc8683e77f841ac0a183c0000494e24510 else (if i < 368 then 0x4ef0aae0b526e9cad22060239e0000000004da08a9f6000029b408d00000000000000000000000007ba65df1600000115b0000225f2 else 0x980228614671820c64dd2d079800000000000000000000001de6135cc00000645b8000000000324669e009f20570240000)) else (if i < 371 then (if i < 370 then 0x1065000008159a98b9000023df200000000000001765e00000000066b3800000b0e5065154ef483e0000000000372cd16206640121bf else 0xb4781d804000000000925680000ad848000084cf986c200000000000000000072e6000000000038e0000000000000019f4c000006351) else (if i < 372 then 0xa7c608c9000000d500ace7800000000000000000131bc0000130869c41800008e38000003232120bdb02e86e92ab00d2ac0227a5f280 else 0x861c80000256fee2c0000026b1038775788245c100000000000000611508b9e5a526e25a3af92310f30ec00000b6301da3c3740c0000)))) else (if i < 379 then (if i < 376 then (if i < 374 then 0x8b210000000002b8a66c16800003a20400005d408e19e220700000000002c18000024f614d96eeff44a830fcd1000029c95a17640000 else (if i < 375 then 0x24170ff16000007d6151260000000000000035f607060000007f2200000000037b06ae00a8d00000003640000002c010b2d41532906d else 0x3a7c80000000028bf1adf32d25a000011c2d38a00d3002124ad1660000000000000000000c025c0940b905bb2c63da2543d000000000)) else (if i < 377 then 0x71e480000000013d8830d6a7dc03016a701a000001fda00002d1a100000b65d39132495e00001c1c86ac18000000002c7da else (if i < 378 then 0xb68056a0136406ea00000000000ed5a02f008ae850c84000000002bb3800001f78000002056375c98000021000663d26eaa7021 else 0xa47da14814b28617de6f8f00000bc54628da41202865800000cb80000023f0cad8e591d087985f3232c24c00007ca800000b357648de))) else (if i < 382 then (if i < 380 then 0x228d10000044c178f6953433a5c99df31f24c0000ae2613fad000000f2a00000000019a05a8e400002c8bc7658c000000001d3e0 else (if i < 381 then 0x957400003e60400009e3445edc3fe74a9317b350000049402150401f7acd0000001f8db15e610486 else 0x856008a2ab323139d067bd670a100001a449a9e100000000000000aa39939a400000fb9e00000d06c00000000085f180000000017340)) else (if i < 384 then (if i < 383 then 0x7cd811f3900002d69c4188590e0b2c98000093e60c6e04ca00034600001dd3066b2046214d718000087d8533c61ddc00000 else 0x2630980e12b18237009eb481157400003ad85608900001c400016b40000b354272c156fc4fc9e167610a1c81fa615f34c20d33ad) else (if i < 385 then 0x7872a2a0c00002d0099726c0000000025454000000000a38fc0000adbad1f8904d007c920000000000000000001337ac7e9b7a240000 else 0x44c000000147203cddb108dd7aa8d3840d0089b80c8724126000000000198201e300974f39fca26da0000000009ec85a2005e30a1c01))))) else (if i < 399 then (if i < 392 then (if i < 389 then (if i < 387 then 0xb6118000027460bf300000270a34d76000004979ab1034cd012121aae0ddf93709ce4c1200d8c000068b200000ac60c104846165733d else (if i < 388 then 0x49d7400005c581bf929ba78000049601e40189004000000002d1b90000227800000000000000000007e9025f9e00000000031b500000 else 0x941c0000080e3000004780abc855e3cb42266b401fe10f20000000000062dc87fe09be80abb054d012fb95f526a0b315315c064)) else (if i < 390 then 0x2f6027fd232fa55b33000000000601c800000000000004133d7e0744e800000484e400009236deb072164ac8e900000ff10000000000 else (if i < 391 then 0x848808518000000000000013586aea200000a3aa89a2a756f99f48727c9041a0000211e03e04a6718000000000000000000000006589 else 0x1bf6500000fc9200001840400001b1810000227862b0c40000435800000693220ce83f74c000000002c75000002d5a1a960042a1))) else (if i < 395 then (if i < 393 then 0xb25a1b01f1dcf5dc1c7fea53189baf0206f0768c1cd04af66800000000000000000000000000218b29f1640000000000000000007f60 else (if i < 394 then 0x1c70400000c30397268291e000021cf300002310900002c58d00002e6c63c3848c1820c486c60aa5a4000000002ca14289825fdc else 0x6000400003a9000000000400000000027c5542c8d05f219e100000ace680000b9d78000038e4045646041c0000)) else (if i < 397 then (if i < 396 then 0xba965a0720000000002f025e10c986f43c5d6a47c033400000469000000000053322514000000000053c6c00007b78844df00001d396 else 0x960a800004bae02d2344278000037001829300000cce90000000001f57400001b5d8000035d68000057478fb1e16418000083c00fd83) else (if i < 398 then 0xbc93e366800000775b77c9014b000000000020c100fb087811b3d014bc11a4305160000037c8131219d3696ac03200218e2000024a9c else 0x71e677c9a828033b4293150000220c800000000009a84000065e00cfc8000000000821801bb006060000032400249b)))) else (if i < 405 then (if i < 402 then (if i < 400 then 0x92f687c22a790df65e0128423de7840a1f48559316ab05cc24dcb0b2c50000000001610900000a1e0574f47d928d68800004b7683c5a else (if i < 401 then 0x5b9c07ad1000000000ba9decfa100001e3893c186b390b837987e0000015805000000000b0520000000001b5e094d04b8101c5180000 else 0x1754800004778241f281426be20000023df40000000001d81dc3f62878c30b3000019ad400000713c31b20000000000910019dc80000)) else (if i < 403 then 0x14040ba419578100000acec00001e8300000176da000000000ba7188e8c87049e4985f3c800000000000007ae7aa65c000029523 else (if i < 404 then 0x6df2106f200001a707000000000110840000500f5985a4e3021fe176db1585800000000071750000062b86cfd1846c40000aecd80000 else 0x110000001794987584000001330000000000dc8640b7856227d96910aa2d76800004598d3006000019cc8534e622c0000003310))) else (if i < 408 then (if i < 406 then 0x9e66c0000000003b1000000ac4700000bf803f744df1e8d9cd8205679b000009621000000000020168484800000000147690000289bf else (if i < 407 then 0xa28a80000bcb669e463f66232671ec480000ab8a400000000023db000000f4190fc83872ab8e00000929269645a2048000082ba92c5a else 0x2ee40000000000080069004d7001607ae6582ad08000028fb80000000029b711b9252b1e1fda5193f90d20000003e000000000019a60)) else (if i < 410 then (if i < 409 then 0x45f015b98a3e8c00000000142e05a600782700001bb2a2dd79da640000000003276a9a894e669403f822000000758f2b920 else 0x1501d286e8a654270000000000000002b3807acc4000000000000000001d8e0452b6238704701b10094ef0000032a01b2e0000000000) else (if i < 411 then 0x2b0807db68000073ef23b90bd718105c00000795a35f82caa10000103df52449aa60000021df3271c00000b62000000000000000 else 0x2e11100001ae5a7845a1f423f8000000373499e7600002f36b85000000096e0030800000236c83e68ee6bc00000703c900314188)))))))))

private def loc5 (i : ℕ) : ℕ := unpack loc5Packed 18 24 i

private def st6Packed (i : ℕ) : ℕ := (if i < 12 then (if i < 6 then (if i < 3 then (if i < 1 then 0x95db24c0c11dc66005c0095db24c10f05801695db24c0c11dc16005e576c9644c10f304007002586c93030477001b4795db24c0c11dc007c02576c93030477001efe95db24c0c11dc007002576c93030477001a978d5b24c0c11dc00795e356c93030477001c008d5a24c0c11dc00695db24c10f30477001e576c9303047b1dc00795db24c0c130076001e576c93043c771d800795db24c0c11c86b001e576c93030477198007003124c0c11dc45001b1295d303047711400795db24c0c11dc03001e586c9303047700400795db24c0c11dc01001e576c93030077004007 else (if i < 2 then 0x95db24c12a30477005e576c930490c11dc01795db24c52330477005e576c930488c11dc01795db24c11e30477005e586c93043cc11dc01795db24c10f30477005e576c930438c11dc01795db24c0f530477005e576c9303acc11dc017002576c93030077005a57845b24c0c01dc01795db25fd3030077005e576c97e4c0c01dc01795db25913030077005e576c9314c0c01dc01795db24c10f30077005c0092db24c0b41dc01695db25fd302d077005e576c93043cb41dc01795db24c0c02cc77005c0095db24c0c01d8016961b24c0c11dc6a005e576c930304771a8017 else 0x95db24c0c11d47400de576c930304771ac03795db24c0c11dc4500dc0095db2590c1010026b5a586c93030477005e97961b24c0c11dc017b5a4b6c93030477005e9792db24c0c11dc017b5a356c93030477005e978d5b24c0c11dc017962116c93030477005e57845b24c0c11dc01795e0b6c93030477005e577edb24c0c11dc017002356893030477005b126c9a24c0c11dc017961b25913030477005e576c9644c0c11dc01795db258d3030477005e576c9604c0c11dc01795db256d3030477005e576c9594c0c11dc01795db24c12d30477005e576c9314b0c11dc017)) else (if i < 4 then 0x95db24b0c11dc76011e576c92e304771d404795db24b0c11dc75011e576c930304761d4047949b24c0c11dc6b011e576c92c304771ac04795db24c0c11d46b011e576c930304721ac04795db24c0c11ec45011e576c97f4c07711404795db24c0d91dc45011e356c9303047711404795db24c0c11ec05011c0095db25fd3043c03695db25fd3043cc100dc00969b24c0c11dc03696a576c9303047700dc0095db24c0c11dc036969b25fd303047700de576c97f4c0c11dc03795db24c10f3047700de576c930304771d403795db25fd303047400de576c930304771d0037 else (if i < 5 then 0x95db24c10f30477029e576c930304b91dc0a795db24c0c11dc11029e576c97f4c0c11dc09795db24c0c11dc45025f1295e354c0c11dc0870025f77d3030477021a57949df4c0c11dc08795e4377d3030477021e578d5df4c0c11dc087c49b26893030477021e576c9303d4c11dc06795ddf6c9644c0c1015e576c9644c10f304057002576c9303047b015a576c9303047b1dc05795db24c0c11dc76015e576c930304771d405795db24c0c11dc6b015e576d9b24c0c11ec047002576c92c3047b011a57781b64c0c11dc04795db257d3030477011e576c9584c0c11dc047 else 0x95db24c0c130084059e576c930304bb21016795db24c0c12d084059c000026c844c11dc1650025792e113047705980095e35844c11dc1669b2576c93030477059e5995db24c0c11dc167962576c93030477059e576c9303fcc11dc16795db24c0eb30477059e57845b23047711416795db2520c11dc45059e436c930304770e016795db248cc11dc38059c0095db24c0c11dc15695db24c10f30477055e576c9303047711414795db24c0c11dc76045e576c930304771c811795db24c0c11dc6b045e576c935304770a80f7002576c93030477031b4795db24c0c11dc0a7))) else (if i < 9 then (if i < 7 then 0xc2e576c93030477095efe95db24c0c11dc25795db25fd3030477095c00c49303047711425695db24c0c11dc45095c00a5db24c0c11dc226aba586c93030477089c00949b24c0c11dc226c8e976c93030477085c00a5db24c0c11dc216002936c93030477085800a41b24c0c11dc216a5e816c93030477085e528d5b24c0c11dc21790e356c93030477085e578d5a24c0c11dc217a5db24c0cf30477085c00a5db24c0c11c8216002976c9303046b085a57949b24c0c11ac21795e356c9303046b085e976c930304770ac21795db24c0c11dc2a085c0095db24c0ca210166 else (if i < 8 then 0x95db26693030477115e576c9864c0c11dc45795db24c12c30477115e576c93048cc11dc457003124c10f30477115b1295d3043cc11dc457003124c0c128c77115800c493030477198456c4a574c0c11dc66115e576c9303047712445795db24c0c11dc46115c0095db24c0c11dc43695db24c10f3047710ded66c93030477114387002976c930304770c980092db24c0c11dc326002476c930304770c9a4b6c93043cc11dc32795e526c9303048e0a9e5792db24c0c12382a795e356c9303048e0a9f4795db24c0c11dc2770032395db24c0c1095b2395db24c0c11dc257 else 0x2576c9333047711580095db24c4c11dc45600347c493030477115800003124c0c11dc45500312bf93030477115800c4aee4c0c11dc45600000bb93030477115712bba574c0c11dc457c4a9795d3030477115c00c49df4c0c11dc456c4a5777d3030477115e577addf4c0c11dc457002576f1303047711580095db34c0c11dc456d1e576c93030477115ee295db24c0c11dc457002576c93030477115a576f1b24c0c11dc45795db36c93030477115f126c9ab4c0c11dc457c39b26ad3030477115e576c9ab4c0c11dc457c49b26893030477115e576c9a24c0c11dc457)) else (if i < 10 then 0xd1e576c93030477199c0095db24c0c11dc66695e526c93030477199c00949b24c0c11dc66695e436c93030477199e578d5b24c0c11dc66795db24c0fb30477199e576c9303dcc11dc66795db24c0c12c477199e526c930304771c8667949b24c0c11dc6b199e576c930304751ac66795db24c0c11c86b199e576c930304771a4667d1e116c93030477171e57845304a4c11dc5c795ddf6ad3030477145e5777da24c0c11dc51700000c4930304771256d695e116c8c11dc45795e116c96430477115e576c97f590c11dc457002576c94830477115a576c94851cc11dc457 else (if i < 11 then 0x95db24c0ce304771ade576c930328c11dc6b795db24c0c3304771ade576c9303048a1dc6b795db24c10f304761ade576c9303ecc11d86b795db25fd30304751ade576c97f4c0c11c86b795db24c10f304721ade576c9303ecc11c86b795db24c0c11dc6d1adeaea5db24c0c11dc6a7aba966c930304771a9eae949b24c0c11dc6a7aba356c930304771a9e576c9303ecc11dc6a795db24c0eb304771a9e576c93043c771d86a795db24c0fb1dc761a9e576c93043c771ac6a795db24c0fb1dc6b1a9ed6ab9b24c0c11dc697002576c93043cc119980097db24c0c11dc666 else 0x95e266c930304771bde576c930304771c86f795db24c0c11ec771b5f2395ddf6c9303046b7002576c9303048e1ad80095db24c0c11ec6b695deb6c97f4c0771ade576c97f4c10f1dc6b795db25fd303ec771adf4795db24c0c11dc6b7c8e576c930304771adc0095db24c0c11dc6b6aba526c930304771adea9949b24c0c11dc6b7a5e526c930304771ade90949b24c0c11dc6b7aba356c930304771ade978d5b24c0c11dc6b794a346c930304771ade526c97f4c0c11dc6b7949b24c10f304771ade526c9303ecc11dc6b795db24c0d2304771ade576c93033cc11dc6b7)))) else (if i < 18 then (if i < 15 then (if i < 13 then 0x95db24c0ca304771d9e576c93030cc11dc767c8f1295db24c0c11d5f2395ddf6c93030475795db25fd3043c771d5e576c97f4c10d1dc757c8e576c930304771d5f2295db24c0c11dc75795db2590c1300771d5e576c964304bd1dc75795db2590c12d0771d5e576c97f4c0c11d875795deb6c97f4c0771c9e8695db24c0c11dc727aba526c930304771c9eae90db24c0c11dc727a5e436c930304771c9e9390db24c0c11dc727aba356c930304771c9e978d5b24c0c11dc727a4e356c930304771c9e57949b24c0c11dc70795e4b6c930304771c1e578d5b24c0c11dc707 else (if i < 14 then 0x95db25fd30304861dde576c93043cc121077795db24c0ca304841dde576c97f4c0c11f87770025b6c9303047b1dd80095db24c0c11ec77695db25fd303047b1dde576c93043cc11ec77795db24c0c12f07b1dde576c93043cc11e8777002576c9304b0c01d980095db24c123300766002576c930300b41d9a577adb25fd301dc767aee576c93043c771d9e57845b24c10f1dc76795db25fd3043c771d9e576c9644c10f1dc76795db258d3043c771d9e576c9304a90f1dc76795db24c10f3ac771d9f4795db24c0c11dc767aba526c930304771d9eae8d5b24c0c11dc767 else 0x95e116c930404c11dde57845b24c0ff30477795e116c9303f0c11dde576c95b4c0fb304777aee576c9303d4c11ddc0095db24c0f530477695e526c9303d4c11dde5792db24c0f53047770024b6c9303d4c11dda578d5b24c0f530477795db24c12a3d4c11dde57845b24c0eb30477795db2591303acc11dde576c9304a8eb30477795db24c10f3acc11dde576c9303fceb30477795db24c0f53acc11dde576c93043ce830477795db24c0eb3a0c11ddc0095db24c0c12c077695db25fd30304a31ddc00ab9b24c0c12387760024b6c9303048e1dd80092db24c0c1228776)) else (if i < 16 then 0xa5e4b6c93043cc11dde5792db24c10f304777b5a476c93043cc11dde5791db24c10f30477795e416c93043cc11dded68d5b24c10f304777a5e356c93043cc11dde578d5b24c10f30477791e356c93043cc11dde578c9b24c10f30477795e2c6c93043cc11dde578a9b24c10f30477795e116c93043cc11ddc008d5a24c10f30477695db25913043cc11ddc0095db24c10e304776002576c964424c11dda576c9644c109304777002576c92a424c11dda576c9304a90930477795e526c930410c11dde5792db24c10430477795e436c930410c11dde578d5b24c104304777 else (if i < 17 then 0x8d5b26ada24c0c11ddc008d5a267930304776002576c9904c0c11dd80095db263530304776d1e576c9644c0c11ddf12bfa576c923304777002fe95db248cc11dda5790db26c12330477795e436c9ab48cc11dde5790db268923304777d1e576c930478c11ddc0095db24c114304776c4ad66c93043cc11dded6a5db24c10f304777aba976c93043cc11ddc009b1b24c10f3047760025d6c93043cc11dd800965b24c10f304776002586c93043cc11ddb4795db24c10f304777c2a576c93043cc11ddf0095db24c10f304777002576c93043cc11ddad692db24c10f304777 else 0x9b1ab4c0c11dd400c4a4b6ad303047760031290dab4c0c11ddb1295e3d6ad3030477795e4b6c9ab4c0c11dde5292db26ad3030477795e436c9ab4c0c11dde4b90db26ad3030477792e356c9ab4c0c11dde438d5b26ad3030477700000bb9a24c0c11dd400c4a3568930304776002ee8d5a24c0c11dd80095e3568930304776000008d5a24c0c11dd4008d5df6893030477600235755a24c0c11dd800c49b2689303047760030e6c9a24c0c11dd800bb9b26893030477695e436c9a24c0c11dde4b90db26893030477795e356c9a24c0c11dde438d5b268930304777))) else (if i < 21 then (if i < 19 then 0xa5e358d1b24c0c11dde9795e2c6c93030477795e4b8b1b24c0c11ddc0092e2c6c930304776a5e358b1b24c0c11dde578d62c6c930304777002578a9b24c0c11ddb4795e116c930304777d0a57845b24c0c11ddf3c95e116c930304777ce257845b24c0c11ddf4395e0b6c93030477795e52825b24c0c11dde5792e096c93030477795e35825b24c0c11ddc00d1df86c93030477695e4b7e1b24c0c11dde578d5f86c930304777b5a117e1b24c0c11dde2c845f86c930304777c465777db24c0c11ddf0e95ddf6c930304777c325777db24c0c11ddf0095ddf6c930304777 else (if i < 20 then 0xbe65790db24c0c11dde5790a416c930304777002578e5b24c0c11dd800962366c930304776002578d9b24c0c11ddaaea5e356c930304777002978d5b24c0c11dd800a56356c930304776002938d5b24c0c11dd800a26356c930304776aba838d5b24c0c11dde97a0e356c930304777bfa578d5b24c0c11dde9795e356c930304777a56578d5b24c0c11dde9395e356c930304777a26578d5b24c0c11dde8395e356c93030477797e578d5b24c0c11dde5895e356c93030477795e438d5b24c0c11dde4b90e356c930304777002438d5b24c0c11dda9795e346c930304777 else 0x2ff95db24c0c11ddb47bfa576c930304777002fe95db24c0c11dd800be6576c930304776c2af695db24c0c11ddc00bda576c930304776002f495db24c0c11ddb12bba576c930304777a665b95db24c0c11ddc0096a576c9303047760000095db24c0c11dd400a42526c930304776a5e57949b24c0c11dde9395e526c930304777a4257949b24c0c11dde8395e526c9303047770034792db24c0c11ddaaea5e4b6c930304777c4b0890db24c0c11ddc00c22436c930304776c4afe90db24c0c11ddf0895e436c930304777bfe5790db24c0c11ddefe95e436c930304777)) else (if i < 22 then 0x312a5ddf4c0c11dd800002976f13030477500257949bc4c0c11dd80095e436f130304776002578d5bc4c0c11dd800002586cd303047750025792db34c0c11dd80095e436cd30304776002578d5b34c0c11dd800d1e976c930304776b5aaea5db24c0c11ddc00002906c9303047750029796db24c0c11dd8000025a6c93030477500297961b24c0c11ddb4fd1e576c9303047770034795db24c0c11ddb47ce2576c9303047770033895db24c0c11ddb47caa576c930304777c4f1295db24c0c11ddf47c22576c930304777ceb0895db24c0c11ddf12c02576c930304777 else (if i < 23 then 0x29792db24c10f305800a5e356c93043cc16c8e5777db24c10f305c0095db25f93043cc16002576c9644c10f30580095db24c10f438c16002576c9644c10b30580095db2591303ecc16002576c9644c0f530580095db24c10f308c16002576c93043cc02d180095db24c0f5300b4695db24c0f5304c02d1c0095db24c10f304b36002576c9303d4c12cd800a66576c9303047b60000095db24c0c11ed6576c9644c10f3047b7002576c97f4c0eb1dd80000312b5a11304775000009b257844c11dd40000000c494830477400000002ee4c0c11dd000c4aae77d30304776 else 0x95db24c10f439723c4b0b95db24c0c17002aea5e526c930305a9795e528d5b24c0c17a5e8195e346c930305c00a5e358d1b24c0c16c8f0b95ddf6c930305f23a5e5777db24c0c170029777dd16c930305b23c4a576c93043cc17a5e8b95db24c10f305e97a06576c93043cc17)))))

private def st6 (i : ℕ) : ℕ := unpack st6Packed 74 24 i

private def adj6Packed (i : ℕ) : ℕ := (if i < 7 then (if i < 3 then (if i < 1 then 0x10001280c1984417808100020088011802108426304ca388290c420280c13006213480890060042d else (if i < 2 then 0xca713c0209c01190012800738060108007200202040008c01140d29000780a376c21081a009c0a else 0x50c043000000980098a201800000621a122198230a820584000882028881094a0084100840710001)) else (if i < 5 then (if i < 4 then 0x88662042218c36218003802000003200004808150482000071012320ca000c213a0491984350001 else 0x2000000800424852080100c000040018ea500803084a000c05400621140000020298000204120c01) else (if i < 6 then 0x38060098401142001c0000c21008048a420100011080711d85304ad09043320090002010440000c2 else 0x108c4038840190601380d0904311c2408801000023006050c022000319440000e23002a48461))) else (if i < 10 then (if i < 8 then 0x10020304a60044f3806100c82199ae088005148700400180400080220000000082002f0800011420 else (if i < 9 then 0xb8e10044108c05e00030d14600c001000201c251958000024095a100420108000082000004028c6 else 0x180002886313c3d3844088c6021121491001c5a0008c310c66004000080130463108612304000025)) else (if i < 12 then (if i < 11 then 0x41023000030342210c6640c8e01520308a0004020002313445004200040308c8328ca00046508c00 else 0x10006108c2300405024610392102880108400a44260001000000052111922280200208301027) else (if i < 13 then 0x8920084ac908038982c0002600104000200100000c2010805048010880118061284000102748100 else 0x118008180000bc20108820894100400704000044218801228212002f))))

private def adj6 (i : ℕ) : ℕ := unpack adj6Packed 5 64 i

private def loc6Packed (i : ℕ) : ℕ := (if i < 81 then (if i < 40 then (if i < 20 then (if i < 10 then (if i < 5 then (if i < 2 then (if i < 1 then 0x80f480000000000000f8028e02230000008bf03141000009f9800001dc9c0000000000001784d9d02e4006a418000000000000 else 0x215e000020f20bf6d00002d6f4d5603d7600000000000000440500c28b78c300000076700000000007521764000001d0400000) else (if i < 3 then 0x3c6e266a54a9800000000388217c0000002121081000000d4823f90a1da40000be8460ef0000000001ac0856c34a01c60d0e40 else (if i < 4 then 0x2d6d2a2b17ee0223f5f1e44ae12d12000015ed05200188077df000000001900c052073b42980df13000000000000009dd22241 else 0x125092a00f68c00000000342099860000000002edb02fbc84202da6391814380000027c031f2054200000000000000bd720000))) else (if i < 7 then (if i < 6 then 0x16d09b77c0000e96889c900000d7240000512d04800034200004c5c1b201b0180000000038b9800000000059e00001b4784f9f else 0x36000000000009f407d418000169026750324180000724400005460aac0c0000a03e116eb7010bcecbc040000023200000dc3c) else (if i < 8 then 0xf3800002099000001ead80000c50a00001d8480000000000007c2d000000000d38020760000000000d80380900000eaa0956f else (if i < 9 then 0x11ee800000000dd3c44dc8ad017f24000071c04608033606d5e00001dc85e090b3bd00003d64838600000000037384b1080000 else 0xbe80220065480000000022f2400001f132dc192dd4e76600000b36859e427210000185b18f02674886a080000a0400000)))) else (if i < 15 then (if i < 12 then (if i < 11 then 0x60c10ba8400000000352d00001437a7253624200000a3bacd0084080000036b0f23103408000000000000000039e68741a12c0 else 0xdc0842000982cde15e1e334322c200000000029cf80000c98948423a5c9da0c0000000016399c6c70a9f49f480000c7908c1f) else (if i < 13 then 0x54490000166e0e92000000de29c73c000079ce0aa25a9b47bc000000ba780000d7856541bc4c53a30b2210ea313da5c680e162 else (if i < 14 then 0x34ec976c691e9000018581f5b492203b403a7697804000023f03cc21095a00005cc038a19d9260c704c298597c00001218 else 0x64d981a0d850200005160a7d7800001f8155ad3480136305e8c31a43c768257a0000000000000a9200000588f0e0489112b906))) else (if i < 17 then (if i < 16 then 0xd842f60000003036880c19125b924c5f07390000015c80f1f2767924dbc0000440d00000000000000e005c400c0dcb1c09327 else 0x1f3000000000124180000a7090000345204308832a7924000005fba0000000011d9c0000000000001d405fd011412) else (if i < 18 then 0x45c00f7820ae00000396c11ed200004950c1b693f4e778322361204975786c180000315b400000000000000001d626c2e0 else (if i < 19 then 0x766d00001a81c3b080000000015b829a381ac418b24000031640ac1aac01d2cc00005d9203e24b90029068690993692b42370c else 0x4251277c000005f1b1eb18000000002a5d00001092400007d2d481000d70000000005e19b74485b9800002e508771800000000))))) else (if i < 30 then (if i < 25 then (if i < 22 then (if i < 21 then 0x19e02722118ed11670c0085ec9000000000bc080000036400001d530000043508470000010ef11fa4195c922420000 else 0x20e1000000001084910de00001763000000000000000000cbb1000000001ebd200006dde2fca99602108372103403000003a27) else (if i < 23 then 0x4f60000001c8247aa832880001b9c000003b8826c79d23c725142519f980000000006a00800000000519069241de6d2b4e0000 else (if i < 24 then 0x2ced111313dbce8e17489b2368f6809f001a0f2e100000104c00040000006f460000000035551668c000000000000000000000 else 0x3720281c0000000002aea1b7cd200a00000000204858a2506cc00000a9d4000000006edf183c9887800001f5080000b4e40000))) else (if i < 27 then (if i < 26 then 0x6c200000000000005090800017d02c51925b49940c000000001fa4bf60c653e31a13098bdfa0000000003bae800000000e5ec else 0xd4027660afc0223618cf00001bbc00000255040688cdb47a21000019fc891788f923c320000064c059463a0041c08000013c1) else (if i < 28 then 0x35738566605b20000000000000000000000000115d60760505e00000000031db000000000729cbdf200004220006babe04 else (if i < 29 then 0x1b90cc920000079e2be24c82061304ad033dc81736000027b00e2100000560955c0446a40000c84e15d0a26b400001b33 else 0x5c00000000000000000031f24911076506c2427718000000004baf000017e3800003b8026b7430b82141005e3e578bc0032bf)))) else (if i < 35 then (if i < 32 then (if i < 31 then 0x99721dbd22f300000000062f2156e800022e3d125f81e000001d2000000204200000fdb4c15a00000000115ba0000 else 0x12cf352357308d5c91f1f80001e00090386ae614049600000007c40180055e6400006c89402702a807a3f00001a18000005ea1) else (if i < 33 then 0x21263f86c00001240000039b909b0461490000336c40000a040000007901137c000000001d6040000359f85600000000008141 else (if i < 34 then 0x7c210e2300000000000003a90004f0000026208cae938021b1200000000036062c400000747234e180000a91e else 0x81b1800020b4200001bd114a4000000000000027c186730c36c0000000013d82d7bc320608500820acc010000090000000f107))) else (if i < 37 then (if i < 36 then 0x34bc000050230f5cc000000005ac0a1100000085390000380056b6497d256ecb700484d806851cc137cf1b6783053 else 0x6cf41f02114cc89b864cd0040418383500000000001590000003a5c800008f5aa60200000da010b7e8c181ac72f00d1e460000) else (if i < 38 then 0x2df000000f6e0ce84194c9a8006630bc000000361680180c54200001fc9d93bce161481f1c4e5418c00002d2d427c0b7ea4660 else (if i < 39 then 0x6a00000000004c20540430108000000000000000000000d1017a5000000000000000e601d29ca2cc6b033cb400001a502394c else 0x1d61c2cec00004a1201e0000010700000012a48ea9c8a1200002df780000c8806aee009c88a786dbc0000228007ac4ad86)))))) else (if i < 60 then (if i < 50 then (if i < 45 then (if i < 42 then (if i < 41 then 0xde02df6c0600abc0000045050890800000000388196ebebf843c432ea004f02000000001c1c00000ca100000000000000d001 else 0x48130acf514447b411ba639200011038010000230859336d5aa00000d018b6c105cc02d800001c0782adf000001a404102a2d9) else (if i < 43 then 0x6cc0a89183a790a9e21b83f1680000000033f43375000000000640d22a880000000074b08286cc89800004d1b000000000eb00 else (if i < 44 then 0xbf19000000001015237482495000022482000022781f6b56100d53c715906cc8000000006400918487680ffc0 else 0x31a0d7e7e3698323a98f680000025a2950af218680055890000000010b42a49e570044a0813c0000040108d66000000000))) else (if i < 47 then (if i < 46 then 0x3c8180001129e0900b57500000000000000f880000075a00d6086b78ed40c032000012b80000085b96ac6c540c94410d04 else 0x16cd0f70bf0004c09bf940000000026901db4000000000709e2ec016f009ba10000132619862000000000000177045976) else (if i < 48 then 0x34c09909012045a1992f00000000001400800008a080000000040405ed00c3625db6bb5800001128c00002c6000000e95a else (if i < 49 then 0xc2fb9a8895d2941a0f822fc542a02261e00001aecd087a000001ad13084216632b967c081a316500913e4974800020ab00000 else 0x159ca4da5fa36000045341444800000000624914800f28a37814b7a3e56cf8122fdc5d36000000000000000000c8489e000000)))) else (if i < 55 then (if i < 52 then (if i < 51 then 0x65441b2c1c2002e5d0000156f00000138971b001a48000000002d4180000000060da2f4c250b5b9267fb942150657d7e7c0000 else 0x1ed036410000000001766b3d6952240400000017d7400002720238900000000000007d6d80000000000003f348d6242206f230) else (if i < 53 then 0x3b688aa8400000000000043284e54273db0000000000000035149f780000a2080000000033200000066f27c6e81d91ab0a0cc0 else (if i < 54 then 0x32c1a1d8e100056408000000000000539e0000133424172376603806256c0000000026a84000096dc02c33158c11b44d27 else 0x2cb6a89d80000325a3b40a24fd3330be80000000000111860e069809f3ac000046040000000013b00000000003d5818760085a))) else (if i < 57 then (if i < 56 then 0xeb18000006d64bd6041430b2f3574800000c3e6d6322c60000000005e02816f4a842c8243b8105875e20c1bd9 else 0x46281c080e26053e8338043612e10c46c200001e59c5ec0000042a60000040820000000000000000000000000111400000) else (if i < 58 then 0x388c986c63a0276130216c0000597000001a20139d30301797980001700000000000000006930378700000387144800000 else (if i < 59 then 0x2f018be8481901b3900000700dab18ec921a400ca610f3c19b96a0c440e57bb402c879b328b7c0000000016ed00001b1185b12 else 0x388c00000e416768024a80000104d881a032204000063c90000000018a3800004ad485d68ad7a00000000000011ab41140))))) else (if i < 70 then (if i < 65 then (if i < 62 then (if i < 61 then 0x86a02f4c1a9a8e092891cbb98541803bbe000000000000000000000000010142213e2e4c3b2800000c1026a83800017400c982 else 0x3fd0a6d700000e5e0326f000015f00ccc80a00006805db8000000cf000022ab915900e02800018e0a9fa11e4600001480c0000) else (if i < 63 then 0x1bc900001c9c400008a71800000001033d2ca1800019b0400000000000000000f5e03ad30000000000000000000000000049e1 else (if i < 64 then 0x1795151550d476a0cab00000002f280000000017d84c50569d80d808020022396bfb000020892e080000022c709b000e98 else 0x20705e83cd7f0000008264000103048a0295afd78b4b48831a600001316c341800000000000003d154ba080001a3011827))) else (if i < 67 then (if i < 66 then 0x80f435c01e7325d62000014d70000000005f7633631bc7aea9e7a090000000000eb33cd081b240000b1180d8c00001d50c0000 else 0x3000b168a622f5a00000000002c66c58123f30000000010b9e832d03700cab40000000001b3000000000391c87ec20e189c39) else (if i < 68 then 0x17ed9da985a44c544000024801e290af001e04a1e80000037103ba41d88d087094b95e312ec696a020000767206b610d4e5edd else (if i < 69 then 0x2770219452740b1418a422f1c899420000000000000000048bd000000001d6348b471cee92c8000004de028492f60823bedcbe else 0x33e60000043543c391f4810eea5d72000005d78ca0a2b5d45dc92e0157823a0c0cd900001c07ae16c842d8b29c00006900)))) else (if i < 75 then (if i < 72 then (if i < 71 then 0x204fe062a0000000000000000000000000000000000000072c0800000000000016d3b1824000104480000000019b24658c else 0x81b686cc0000057f0000000000f2ded160805500001e49c000005dc8000044369a5384a0424187810e33d1443432f50d400000) else (if i < 73 then 0x6d46e71e000000000bc90775a411e284ec0000f5a11140213380000c0c00000000008ecc0000548c0000000000000 else (if i < 74 then 0x318615c00c4909fa98264800000000c80c0760aa41000001f06194f41f68d490db842c330000200306bbc22d50000212608e20 else 0x35d92424926402d5a8a9c8000071460000898980000d7c07c9e0000245a4000061043b5380000f1b4ac02005e824f40000e0e0))) else (if i < 78 then (if i < 76 then 0x748b1eb05764b036c832690cf00000a5f5000043e0a2336cd857e2400001a6006dde414f8a27990040000000003c24d3003848 else (if i < 77 then 0x571e45180000025215e8202e180b8028982c3000001f9610d124b2e9df742602163d2dee9d720e45208002c9e00000523c6b94 else 0x884484a240000d3816289930022330004000003858066731300516dc5720000000005d210000000002eda054901c0000000000)) else (if i < 79 then 0x3c00400008a6900000000000002bdd4b9f8000000004b885bef81bc8c00061124f20000011632e821000042e6000000000 else (if i < 80 then 0xe4343b010550000000002c0218e08be015a8aab4000000c7000000244e537cceea256ec0fdc98e18000000003904859a2ece8 else 0x2e20c23b200003aba800000000c6da00000000000009c3e4502419300000b2bc3a03000001508d48c74e400001cf300000))))))) else (if i < 122 then (if i < 101 then (if i < 91 then (if i < 86 then (if i < 83 then (if i < 82 then 0x201cc9709290f0000105a400003ca38000033b0fade000000000000000006ae4000000000c9bc1ca805870dab60000 else 0x316406d7d18320000000046285c20400001c4940210000066f4061e0d80000005b725313bcef04208bae0892029a556c06d5cf) else (if i < 84 then 0x2f401d8c8ec9e186eb0011803906d137f99acc1af0809bc000040d881434c06c00002becc0000f31e1fde165b0c22881bf else (if i < 85 then 0x24843a58077780000000040f240000000032a4b1e0d93b6dfbd207918a0d24d23a894d1006d70000000006a800000000008a20 else 0x7f4c226800000000003891f7a48b241772000016c851e5afd5e45d380000ad82e5861a83000006e920a1800003811800005160))) else (if i < 88 then (if i < 87 then 0x56c000000e008000017ad353216780b882727600000f95a09840000082f000002d206ba500001d84200001dc429284484209c0 else 0x2581000003e0a000048090700000000000485f91611d9cc1dc00000000000000000000000000000000000168f80001225a0000) else (if i < 89 then 0x64c180000370098dd7243158f000000000304003e01bac00a002f5b000022924000000000000205c0000063c10000000000000 else (if i < 90 then 0x73890b57400010b000000432800000163c66e529830ac6600000000000000000cb8435ad3a298c20243467fde800016b0867e6 else 0x1059404005ba2796e898329f45644e000000000f6fc000114132f6f8ee24f10706a7429f92c300000770c0cdf91189dcc01b41)))) else (if i < 96 then (if i < 93 then (if i < 92 then 0x380100000e41000001cc8d3db0d8dd00000bd7400009e1b54c82f211f702b78600000000000000000000000000064e5e86 else 0x7d825b2333f004b040d2c00000000000000000100316a924ab5c9603b98332d80000c718f9db134040b842680bf88) else (if i < 94 then 0x43b580000d50cbf63556c29898f1420000000000001014e042175d0adc015b02472b74892cc017604000004c000000c706e103 else (if i < 95 then 0x21a0000008946b30180000e000038c04661607a1f4070cc13c48ac7a583c000000000af00892056420000021047060 else 0xa3b8d44a26c906d7829130458000020a7800010f89610031e31b978000083e600001606400004190800000000bc92))) else (if i < 98 then (if i < 97 then 0x1b660c1490e4087af494f0f684000014c000003cb7a2b2c0000000000000bc64c2800000000000000fb03000033e7889c00000 else 0x23648ee986480000000000000000008684bbf200000d01f19cf00001a89000001cc693200c20000000000000018f1a2cdb) else (if i < 99 then 0x17b3c000000008c0f18120000025801e0c2d23c6e1a985d5306b01b800003a263b0080000731800003e1f8000131420000 else (if i < 100 then 0x63040fa800000d7c0057180000cdbade987b8080000000000000ad824010000000862f061727800010bcc44909c68400000000 else 0x66c080000000000007234800001c1281ad52400000033800000207800000bd06000061d880001154600000000300652da4f360))))) else (if i < 111 then (if i < 106 then (if i < 103 then (if i < 102 then 0x252b40000922131c107019458000000000000000082d0192e0c000019b90000000000000000010e8900004196c00000ba1 else 0x551e800018ad9125905e03ec0000002203516e03d005e5200000000000016908cd8e3f330000000002edb481c98f30bd120000) else (if i < 104 then 0x210b4071e00000000000000000000042b05fab60000601e044081600cd488a8d80410da60ec61 else (if i < 105 then 0x74c86418000000000000000000000000048d0aa862250697390000430060d4062000000000000742000020ad000009a3c0c09 else 0x1e70890bc00c013e091142dfc0000019d690172772062809bc04000000005681800000000de4046802a80055720000))) else (if i < 108 then (if i < 107 then 0x1920978c0c980458033e6525720000565e2f24c011246aa72c005e005eb6d08000001781c000000007430150400000a1f0 else 0x5a04000000000400079c08f905d3e400008350800000000b12014ed36b5122240000000035d520600000000002a77561780000) else (if i < 109 then 0x798c3e77800000b703840271a559808a9e715e2309c000000000000226fde9425e0105ec00000bc6060c81b4f000002542472a else (if i < 110 then 0x5442002c00000000085c0000000e2c17c0480980000074e775c83139976830b5161e1d1000000000000001748800019f3ea5dd else 0x3541a148544bc000037f92f201b2e475ce414c8f89c000020087133000000000e40c000006824e1e0000025302f2610e000000)))) else (if i < 116 then (if i < 113 then (if i < 112 then 0x45508000184790c8036d9063793cbc00000000084f1f1422b21212f34400dec87627840680000ce9cfd0309823b784a7babc85 else 0x84264261226080000000006d01d3a827805f4139e08828cc972000007b01d14287ad00000000000000000) else (if i < 114 then 0x72408000023820f3d494c424010b3000005f80b204c91670b90302d00000f931155a000000002207eca865981000006b328320 else (if i < 115 then 0x425633e0000005210036d17580000000003b00363215a8045e000003ce000000b3540000000023172000089c00000123401bc1 else 0x5a99ae8f0960103193953800004d028fe000002ab014622862700000f885c60038230000000000000000068b90000000000000))) else (if i < 119 then (if i < 117 then 0x52501da8c4e988ca16dce000012fbe96de2790a956891640000513804168000094e980cf9850a224319c000000000000002586 else (if i < 118 then 0x49c61401188e00000852016f980000ebe05b419dc600000adc064cc0000000005ebd3913b8619294c000062c20577800011083 else 0x2ec32728000008c39000000001f50000000000290c000001e3d509ca80004a0d0c0026a897b21680255b34ad1ae26867830f29)) else (if i < 120 then 0x262813b8000005a82000001c09138400003cb200000f4200a8201b84000000004310c3ecd7c2400007d41000022624bd6c else (if i < 121 then 0x7f80178c4000000006d823f80da732b930130003cc8000043e0000032c012942ab025f85800020638378474c00000000000000 else 0x1d10c4a8162540000578123945980ecc000000240f08924000000002c260b2a8000000002e26c7700000017a9800018b848298)))))) else (if i < 142 then (if i < 132 then (if i < 127 then (if i < 124 then (if i < 123 then 0x343680500000066f922c1231c00000000000002317e000060ed800000000c4e006042fc6088da000079d908300dbec0684 else 0x256ec0b002d5b0000175b0aecd1495600000001780200004c90970014082e46800001d74000000000151080000b7d0be60) else (if i < 125 then 0x2f598000115d22f5c4ad3000011d00bd0124f01af8837b000004474af1b000005c1e6a6608c061c7a3272574138d980000cb81 else (if i < 126 then 0x65981fe9c616c45bc000000001d62cc0021d9eb99860bb4000033a6000017e12230088cd42a65127200000000000000000068d else 0xc0a4000000000000128840000334100000000078000000186e14e4010bc3a882f468000000007f2300000000074060000))) else (if i < 129 then (if i < 128 then 0x2a480c81a0000284200000000000000000000006b3c000000000000007a2e2b000000a001d3020000313044c60c4a8fa64 else 0x6609bb69470cae800000000015a0a75868a02408859364000000000000000006f9200001540000000000000008604c8905d03) else (if i < 130 then 0x4a50000017e7a2ab30000000000000c1802dad1d94400006ddb000020345b0b800008c28800020790ed616b30016f134ba0000 else (if i < 131 then 0xfc2000020eb400000000014000000d40c2ead04c000000d6804f0198418000000000000228840000a5cc0000016250f304549 else 0x243000001343d158c07e09bbc80000a59000002f509ddd000004a34800016280a8bf6a6495d819bc873de00004133a1d7a0000)))) else (if i < 137 then (if i < 134 then (if i < 133 then 0x32e400001a7100f0831ad1b6f58088001825c31d6008ab44c180623000018002190804411878088c696210000290793f720000 else 0x4a1000001d92c195e0bc113e880000bf8077c60b48c000031a0509011b9985089427664125d7c0000372200001f8b40000f14e) else (if i < 135 then 0x512c0000231cc00001310b978919401fc07170000004a00afbd2ec1800000ec2f7e94e0c00001d9980000000001b80d980d407 else (if i < 136 then 0x1e2000b10a8ad5a1919bd40000000037720a2017e0841854f2c00000c20e00001ac781484000029180000000005a3c5e02 else 0x3890a29800000db053e0c1f3a4ab7a000005a33fef000000000631e2e60400000000789800000000000000dad2ccf06f90051e))) else (if i < 139 then (if i < 138 then 0x67a4082121c121b1e6f402b61c000000001208000017200000000003d4840000000000001760198043794000021880a942e180 else 0x23404c720000023b0096600000f2db000040000000000005804c64840000271e269084e00934200002c00000001280fc86) else (if i < 140 then 0x40c6000002cd30a8023079a2043d142f0680001abb4e9ca73c980000000058921c408000000010c8900001856800000000 else (if i < 141 then 0xb790000043a800004fac00000a600380400002068c4008a2d8000017c0c00002a5c41d09112400008aa030a600000390096a8 else 0x130315ba2166989e298813a821ae2000089c42208481182710000000000983c2f9e00002750545ba8af5868c1aa0073b80000))))) else (if i < 152 then (if i < 147 then (if i < 144 then (if i < 143 then 0x33f2000014a000000421f078f00000209c640234320000016da4b571e29d76c455d550e3058c9167e3f801bc60000049005518 else 0x652600000f37e00007dad2740230004142720130c19ca30e780000024ae00000e6f234ed002c8000000003ad38a76c0d040000) else (if i < 145 then 0x6d6001300cc9064db2f1e00000f95e09000190b700000000000290c000003567169e68821973213c00000000005e0c0000755d else (if i < 146 then 0x7a08f578000116a0000033bc9383ce13082a0000000000cdc239908ad7d168a2d2182678a9680000e4e03cb49b9781406331e else 0x212d0000103420000000003ccd333c0b404fcf0aa19ff0000005a84b5ef400002a2302ae86c19937afac0000000000ea009929))) else (if i < 149 then (if i < 148 then 0x4d5c9be10000020d888c112470ea90000078431fce4690c6c862f0280001217069860f4011fa40000000048820000000009cbf else 0x4b6c80000bbb46bbd65988000000010d20436880000b8ba1df0000000000bc0c00006cfaaec6dd2c86fe406800000000009c6b) else (if i < 150 then 0x7d8131d20187e00000000000012fb800002fed3021800008ad121de3b384d3608e818c10a90019a304bbd00000d4795a048e1e else (if i < 151 then 0x1e40e0a0244d0be9c9e640000000001c1d8b3e48a18000032c1c4abaa6e3000016509ccc000000000290d893c862da else 0x1dee40713000031e009f18185e30b110b0116020000000000000fad241ec8a9080000c8ba000045d0bd5a400000000)))) else (if i < 157 then (if i < 154 then (if i < 153 then 0x8100436f40000333f000041d3186da000062b114d6a20340000420e3d88581120ebd5a048aac073061cb085ed3f1c8ccb4d584 else 0x21c01b6cc5cb4000023490c458000000003c4d800014a20cd8422081d8858100ea00022086cfc934079710000002cc0001084d) else (if i < 155 then 0x2ca9034035b21db8098d300000000000003028876080000c4941f417f8c2ee003c8c000000002028c1c30ad58 else (if i < 156 then 0x26c628935970e0e19336e00000920000000000282f80000000000000bd49b2e8000087c00000000000000454fac0cc00000b83 else 0x86e0000018f0a8cb9784097924000010026183b17b06a30902122a636af0c700000084c9191d01db25e9e00000000127046072))) else (if i < 160 then (if i < 158 then 0x279032568464300e053842c0f1dec800003a5080000152a000000003a5313172000071443ac080000000000001857812789ba0 else (if i < 159 then 0x79cc0fd68fe7600006cc200000a630c7020b6f0417005b40c41000027d040000d4000000000008306fc7000002288c00000000 else 0x39e580001146275d02034c000000005baf0000215b2e760000000000693cb898501e3aa00bb6000001ca42d42d2d660000)) else (if i < 161 then 0x17a000000a5185a0225ea1b324be7000002b3805d4004184bd9bdc00000040da00002dd6c000093a7528f4460c0000f1c8 else (if i < 162 then 0x711e34e1d41e0e315000044c152ad2000000000b0840d265d053b5080501dbc0e6402076800000000aa1e6ec91cb4452006f72 else 0x2bc204e30b8a91c5100000cd980000000039400a5ba000000002c4851b780000425214769e5ec8880))))))))

private def loc6 (i : ℕ) : ℕ := unpack loc6Packed 17 24 i

private def st7Packed (i : ℕ) : ℕ := (if i < 1 then 0x2576c9303047b1dd80095db24c0c11dc6b6002576c9303047719980095db2520c11dc45600000c49303047711540095db24c0c11dc45695db26ad3030477115e576c9a24c0c11dc45795db24c12c30477115e576c93048cc11dc457002976c93030477085a576c930304770a82179b2576c93030477059c0095db24c0c11dc03695db25fd303047700de57845b24c0c11dc01795db25913030477005e576c93043cc11dc017002576c93030077005a576c93030477058017002576c93030477001a578d5b24c0c11dc00795db24c10f30477001e576c93030477004007 else (if i < 2 then 0x2fe95db24c0c11dda9795e526c930304777002978d5b24c0c11dda9795e356c930304777a0e578d5b24c0c11dde5790e356c930304777002438d5b24c0c11dda578d62c6c930304777d1e57845b24c0c11dde5792db26ad3030477795e436c9ab4c0c11ddc0095e3568930304776000008d5a24c0c11dd400c49b26893030477695e436c9a24c0c11dde578d5b268930304777002576c93043cc11dda5792db24c10f30477795e476c93043cc11dde578d5b24c10f30477795e116c93043cc11dde576c9644c10f304777002576c9303d4c11dda576c93043ceb304777 else 0x95db25913043cc160000095db24c0c11ed400d1e576c930304776))

private def st7 (i : ℕ) : ℕ := unpack st7Packed 74 24 i

private def adj7Packed (i : ℕ) : ℕ := (if i < 1 then 0x784811088101084000a01004128c0c20c02314202d0b019c4419044794050016141c0d60c2300c01 else 0x200000a1)

private def adj7 (i : ℕ) : ℕ := unpack adj7Packed 5 64 i

private def loc7Packed (i : ℕ) : ℕ := (if i < 7 then (if i < 3 then (if i < 1 then 0x1e0079ebed9a80f01349b49b002ec156c46600000011c800000000000001801118000000 else (if i < 2 then 0x56ec5c87be8c9b330001e32a829a78f651000000001c003000007c4cb240017691c300000017de else 0x3a040000000003261cd8e849e0084adc8e801a0000000000068d55880000007821e60408730)) else (if i < 5 then (if i < 4 then 0xb304d696407b30000001a00000c8c2d9808000000025211600008650002dcca0600010f15b8000 else 0x5a58764e6000043530806e00000000f7a5210002c48f60f6d39e1c1db02a0000049207678cc) else (if i < 6 then 0x681b281cc5048879456a9c00009a92c84000b9000000021c20003043d8d2b43c1350a530000b60 else 0x70200031210c8a363409162f18b493c70e036e10005580c7a0000002da1c0444000026028c534c))) else (if i < 10 then (if i < 8 then 0x4245f6b0787b668dd9853b4000a3000011035e829000011b400038300031b4ada0000003204000 else (if i < 9 then 0x3193816e24000a713462cd15e000016492920005184b30f807320005ba1c036e05462000582000 else 0x4ef44c0d84b0b4b6800191ab090200000a801ec00032362a139892807120008720000000000)) else (if i < 12 then (if i < 11 then 0x38000000009300ec0000f0100059917b42c0c81cd729d80001ef0000b08609c800002290000 else 0x43d238221c00063c40080000000000000001c060007b836000013bc64f2f3307a692) else (if i < 13 then 0xaf3058110c4a10001478bc000024f18cc0000003c300007800000000001808000 else 0xe21803613))))

private def loc7 (i : ℕ) : ℕ := unpack loc7Packed 13 24 i

private def st8Packed (i : ℕ) : ℕ := 0x95db24c10f30477695db24c0c11dc6b695db24c0c11dc456

private def st8 (i : ℕ) : ℕ := unpack st8Packed 64 24 i

private def adj8Packed (i : ℕ) : ℕ := 0x10041000150122a2

private def adj8 (i : ℕ) : ℕ := unpack adj8Packed 4 64 i

private def loc8Packed (i : ℕ) : ℕ := (if i < 1 then 0x99a7d425a002709292804195aa0003a532104080098009800c040c else (if i < 2 then 0x842aa133c00210013d51a88000000380000d0039a8000000009132 else 0x4c2013c005600000000000000e8))

private def loc8 (i : ℕ) : ℕ := unpack loc8Packed 9 24 i

private def st9Packed (i : ℕ) : ℕ := 0x2576c930304775

private def st9 (i : ℕ) : ℕ := unpack st9Packed 54 24 i

private def certCount : ℕ → ℕ
  | 2 => 61
  | 3 => 435
  | 4 => 1332
  | 5 => 1520
  | 6 => 564
  | 7 => 51
  | 8 => 3
  | 9 => 1
  | _ => 0

private def certDims : ℕ → ℕ × ℕ
  | 2 => (97,419)
  | 3 => (631,2819)
  | 4 => (1931,8689)
  | 5 => (2203,9887)
  | 6 => (877,3907)
  | 7 => (71,317)
  | 8 => (17,61)
  | _ => (1,2)

private def stData : ℕ → ℕ → ℕ
  | 2 => st2
  | 3 => st3
  | 4 => st4
  | 5 => st5
  | 6 => st6
  | 7 => st7
  | 8 => st8
  | 9 => st9
  | _ => fun _ => 0

private def adjData : ℕ → ℕ → ℕ
  | 2 => adj2
  | 3 => adj3
  | 4 => adj4
  | 5 => adj5
  | 6 => adj6
  | 7 => adj7
  | 8 => adj8
  | _ => fun _ => 0

private def locData : ℕ → ℕ → ℕ
  | 2 => loc2
  | 3 => loc3
  | 4 => loc4
  | 5 => loc5
  | 6 => loc6
  | 7 => loc7
  | 8 => loc8
  | _ => fun _ => 0

private def certState (k i : ℕ) : List W :=
  let s := stData k i
  decodeState (s >>> 4) (s &&& 15)

private def certLocate (k : ℕ) (v : List W) : ℕ × Fin 120 :=
  let (b,n) := certDims k
  let h := stateHash v
  let slot := (h / b + adjData k (h % b) * (1 + (h / 1031) % (n - 1))) % n
  let s := locData k slot
  (s >>> 7, Fin.ofNat 120 (s &&& 127))

private def renameFast (p : Fin 120) (w : W) : W := runParts (plan p) w

private abbrev certGroup := checkGroup certCount certState certLocate renameFast



set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma inverseSmall : ∀ p : Fin 120, ∀ i : Fin 20, renSmallInv p (renSmall p i) = i := by
  decide +kernel

private lemma rename_inj (p : Fin 120) : Function.Injective (rowRename renSmall p) :=
  rowRename_inj _ _ (Function.LeftInverse.injective (inverseSmall p))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma maps_0 : ∀ j : Fin 10, ∀ i : Fin 120,
    ((plan ((Fin.ofNat 120 (0+j.val)) : Fin 120)).filterMap
      (fun x => readPart x i.val)) = [(rowRename renSmall (Fin.ofNat 120 (0+j.val)) i).val] := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma maps_10 : ∀ j : Fin 10, ∀ i : Fin 120,
    ((plan ((Fin.ofNat 120 (10+j.val)) : Fin 120)).filterMap
      (fun x => readPart x i.val)) = [(rowRename renSmall (Fin.ofNat 120 (10+j.val)) i).val] := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma maps_20 : ∀ j : Fin 10, ∀ i : Fin 120,
    ((plan ((Fin.ofNat 120 (20+j.val)) : Fin 120)).filterMap
      (fun x => readPart x i.val)) = [(rowRename renSmall (Fin.ofNat 120 (20+j.val)) i).val] := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma maps_30 : ∀ j : Fin 10, ∀ i : Fin 120,
    ((plan ((Fin.ofNat 120 (30+j.val)) : Fin 120)).filterMap
      (fun x => readPart x i.val)) = [(rowRename renSmall (Fin.ofNat 120 (30+j.val)) i).val] := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma maps_40 : ∀ j : Fin 10, ∀ i : Fin 120,
    ((plan ((Fin.ofNat 120 (40+j.val)) : Fin 120)).filterMap
      (fun x => readPart x i.val)) = [(rowRename renSmall (Fin.ofNat 120 (40+j.val)) i).val] := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma maps_50 : ∀ j : Fin 10, ∀ i : Fin 120,
    ((plan ((Fin.ofNat 120 (50+j.val)) : Fin 120)).filterMap
      (fun x => readPart x i.val)) = [(rowRename renSmall (Fin.ofNat 120 (50+j.val)) i).val] := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma maps_60 : ∀ j : Fin 10, ∀ i : Fin 120,
    ((plan ((Fin.ofNat 120 (60+j.val)) : Fin 120)).filterMap
      (fun x => readPart x i.val)) = [(rowRename renSmall (Fin.ofNat 120 (60+j.val)) i).val] := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma maps_70 : ∀ j : Fin 10, ∀ i : Fin 120,
    ((plan ((Fin.ofNat 120 (70+j.val)) : Fin 120)).filterMap
      (fun x => readPart x i.val)) = [(rowRename renSmall (Fin.ofNat 120 (70+j.val)) i).val] := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma maps_80 : ∀ j : Fin 10, ∀ i : Fin 120,
    ((plan ((Fin.ofNat 120 (80+j.val)) : Fin 120)).filterMap
      (fun x => readPart x i.val)) = [(rowRename renSmall (Fin.ofNat 120 (80+j.val)) i).val] := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma maps_90 : ∀ j : Fin 10, ∀ i : Fin 120,
    ((plan ((Fin.ofNat 120 (90+j.val)) : Fin 120)).filterMap
      (fun x => readPart x i.val)) = [(rowRename renSmall (Fin.ofNat 120 (90+j.val)) i).val] := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma maps_100 : ∀ j : Fin 10, ∀ i : Fin 120,
    ((plan ((Fin.ofNat 120 (100+j.val)) : Fin 120)).filterMap
      (fun x => readPart x i.val)) = [(rowRename renSmall (Fin.ofNat 120 (100+j.val)) i).val] := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma maps_110 : ∀ j : Fin 10, ∀ i : Fin 120,
    ((plan ((Fin.ofNat 120 (110+j.val)) : Fin 120)).filterMap
      (fun x => readPart x i.val)) = [(rowRename renSmall (Fin.ofNat 120 (110+j.val)) i).val] := by
  decide +kernel

private lemma mapping (p : Fin 120) (i : Fin 120) :
    (plan p).filterMap (fun x => readPart x i.val) = [(rowRename renSmall p i).val] := by
  have hb : p.val / 10 ≤ 11 := by have := p.isLt; omega
  let j : Fin 10 := Fin.ofNat 10 p.val
  have ee : (Fin.ofNat 120 ((p.val / 10)*10 + j.val)) = p := by
    apply Fin.ext
    change (((p.val / 10)*10 + p.val % 10) % 120) = p.val
    rw [show (p.val / 10)*10 + p.val % 10 = p.val by omega, Nat.mod_eq_of_lt p.isLt]
  generalize hq : p.val / 10 = q at hb ee
  interval_cases q
  · simpa only [ee] using maps_0 j i
  · simpa only [ee] using maps_10 j i
  · simpa only [ee] using maps_20 j i
  · simpa only [ee] using maps_30 j i
  · simpa only [ee] using maps_40 j i
  · simpa only [ee] using maps_50 j i
  · simpa only [ee] using maps_60 j i
  · simpa only [ee] using maps_70 j i
  · simpa only [ee] using maps_80 j i
  · simpa only [ee] using maps_90 j i
  · simpa only [ee] using maps_100 j i
  · simpa only [ee] using maps_110 j i


private lemma renameFast_eq (p : Fin 120) (w : W) :
    renameFast p w = selectRows (rowRename renSmall p) w := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  let j : Fin 120 := ⟨i,hi⟩
  change (renameFast p w)[j.val] = (selectRows (rowRename renSmall p) w)[j.val]
  rw [selectRows_bit, ← BitVec.getLsbD_eq_getElem j.isLt,
    ← BitVec.getLsbD_eq_getElem (rowRename renSmall p j).isLt]
  rw [renameFast, runParts_sound _ _ _ j.isLt, mapping p j]
  simp

private lemma renameFast_inj (p : Fin 120) : Function.Injective (renameFast p) := by
  intro x y h
  rw [renameFast_eq,renameFast_eq] at h
  exact selectRows_inj (rename_inj p) h

private lemma renameFast_op (p : Fin 120) (a b z : W) (h : z ∈ basicOps a b) :
    renameFast p z ∈ basicOps (renameFast p a) (renameFast p b) := by
  simp only [renameFast_eq]
  exact ops_map_of (selectRows_land _) (selectRows_lor _) (selectRows_neg _) a b z h

private lemma renameFast_goal (p : Fin 120) (g : W) (h : g=goal ∨ g= ~~~goal) : renameFast p g = g := by
  rw [renameFast_eq]
  rcases h with rfl | rfl
  · exact rowRename_goal renSmall p
  · rw [selectRows_neg,rowRename_goal]

private lemma layer_0 : certGroup 0 0 (certCount 0) = true :=
  by rfl


private lemma layer_1 : certGroup 1 0 (certCount 1) = true :=
  by rfl

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_2_0 : certGroup 2 0 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_2_60 : certGroup 2 60 1 = true := by decide +kernel

private lemma layer_2 : certGroup 2 0 (certCount 2) = true :=
  (checkGroup_join 2 0 60 1
    group_2_0 group_2_60)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_3_0 : certGroup 3 0 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_3_60 : certGroup 3 60 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_3_120 : certGroup 3 120 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_3_180 : certGroup 3 180 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_3_240 : certGroup 3 240 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_3_300 : certGroup 3 300 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_3_360 : certGroup 3 360 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_3_420 : certGroup 3 420 15 = true := by decide +kernel

private lemma layer_3 : certGroup 3 0 (certCount 3) = true :=
  (checkGroup_join 3 0 240 195
    (checkGroup_join 3 0 120 120
    (checkGroup_join 3 0 60 60
    group_3_0 group_3_60) (checkGroup_join 3 120 60 60
    group_3_120 group_3_180)) (checkGroup_join 3 240 120 75
    (checkGroup_join 3 240 60 60
    group_3_240 group_3_300) (checkGroup_join 3 360 60 15
    group_3_360 group_3_420)))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_4_0 : certGroup 4 0 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_4_60 : certGroup 4 60 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_4_120 : certGroup 4 120 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_4_180 : certGroup 4 180 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_4_240 : certGroup 4 240 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_4_300 : certGroup 4 300 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_4_360 : certGroup 4 360 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_4_420 : certGroup 4 420 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_4_480 : certGroup 4 480 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_4_540 : certGroup 4 540 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_4_600 : certGroup 4 600 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_4_660 : certGroup 4 660 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_4_720 : certGroup 4 720 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_4_780 : certGroup 4 780 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_4_840 : certGroup 4 840 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_4_900 : certGroup 4 900 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_4_960 : certGroup 4 960 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_4_1020 : certGroup 4 1020 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_4_1080 : certGroup 4 1080 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_4_1140 : certGroup 4 1140 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_4_1200 : certGroup 4 1200 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_4_1260 : certGroup 4 1260 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_4_1320 : certGroup 4 1320 12 = true := by decide +kernel

private lemma layer_4 : certGroup 4 0 (certCount 4) = true :=
  (checkGroup_join 4 0 660 672
    (checkGroup_join 4 0 300 360
    (checkGroup_join 4 0 120 180
    (checkGroup_join 4 0 60 60
    group_4_0 group_4_60) (checkGroup_join 4 120 60 120
    group_4_120 (checkGroup_join 4 180 60 60
    group_4_180 group_4_240))) (checkGroup_join 4 300 180 180
    (checkGroup_join 4 300 60 120
    group_4_300 (checkGroup_join 4 360 60 60
    group_4_360 group_4_420)) (checkGroup_join 4 480 60 120
    group_4_480 (checkGroup_join 4 540 60 60
    group_4_540 group_4_600)))) (checkGroup_join 4 660 360 312
    (checkGroup_join 4 660 180 180
    (checkGroup_join 4 660 60 120
    group_4_660 (checkGroup_join 4 720 60 60
    group_4_720 group_4_780)) (checkGroup_join 4 840 60 120
    group_4_840 (checkGroup_join 4 900 60 60
    group_4_900 group_4_960))) (checkGroup_join 4 1020 180 132
    (checkGroup_join 4 1020 60 120
    group_4_1020 (checkGroup_join 4 1080 60 60
    group_4_1080 group_4_1140)) (checkGroup_join 4 1200 60 72
    group_4_1200 (checkGroup_join 4 1260 60 12
    group_4_1260 group_4_1320)))))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_5_0 : certGroup 5 0 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_5_60 : certGroup 5 60 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_5_120 : certGroup 5 120 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_5_180 : certGroup 5 180 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_5_240 : certGroup 5 240 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_5_300 : certGroup 5 300 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_5_360 : certGroup 5 360 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_5_420 : certGroup 5 420 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_5_480 : certGroup 5 480 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_5_540 : certGroup 5 540 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_5_600 : certGroup 5 600 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_5_660 : certGroup 5 660 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_5_720 : certGroup 5 720 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_5_780 : certGroup 5 780 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_5_840 : certGroup 5 840 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_5_900 : certGroup 5 900 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_5_960 : certGroup 5 960 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_5_1020 : certGroup 5 1020 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_5_1080 : certGroup 5 1080 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_5_1140 : certGroup 5 1140 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_5_1200 : certGroup 5 1200 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_5_1260 : certGroup 5 1260 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_5_1320 : certGroup 5 1320 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_5_1380 : certGroup 5 1380 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_5_1440 : certGroup 5 1440 60 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_5_1500 : certGroup 5 1500 20 = true := by decide +kernel

private lemma layer_5 : certGroup 5 0 (certCount 5) = true :=
  (checkGroup_join 5 0 780 740
    (checkGroup_join 5 0 360 420
    (checkGroup_join 5 0 180 180
    (checkGroup_join 5 0 60 120
    group_5_0 (checkGroup_join 5 60 60 60
    group_5_60 group_5_120)) (checkGroup_join 5 180 60 120
    group_5_180 (checkGroup_join 5 240 60 60
    group_5_240 group_5_300))) (checkGroup_join 5 360 180 240
    (checkGroup_join 5 360 60 120
    group_5_360 (checkGroup_join 5 420 60 60
    group_5_420 group_5_480)) (checkGroup_join 5 540 120 120
    (checkGroup_join 5 540 60 60
    group_5_540 group_5_600) (checkGroup_join 5 660 60 60
    group_5_660 group_5_720)))) (checkGroup_join 5 780 360 380
    (checkGroup_join 5 780 180 180
    (checkGroup_join 5 780 60 120
    group_5_780 (checkGroup_join 5 840 60 60
    group_5_840 group_5_900)) (checkGroup_join 5 960 60 120
    group_5_960 (checkGroup_join 5 1020 60 60
    group_5_1020 group_5_1080))) (checkGroup_join 5 1140 180 200
    (checkGroup_join 5 1140 60 120
    group_5_1140 (checkGroup_join 5 1200 60 60
    group_5_1200 group_5_1260)) (checkGroup_join 5 1320 120 80
    (checkGroup_join 5 1320 60 60
    group_5_1320 group_5_1380) (checkGroup_join 5 1440 60 20
    group_5_1440 group_5_1500)))))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_0 : certGroup 6 0 21 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_21 : certGroup 6 21 11 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_32 : certGroup 6 32 13 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_45 : certGroup 6 45 13 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_58 : certGroup 6 58 13 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_71 : certGroup 6 71 9 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_80 : certGroup 6 80 9 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_89 : certGroup 6 89 13 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_102 : certGroup 6 102 11 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_113 : certGroup 6 113 9 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_122 : certGroup 6 122 10 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_132 : certGroup 6 132 8 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_140 : certGroup 6 140 9 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_149 : certGroup 6 149 8 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_157 : certGroup 6 157 7 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_164 : certGroup 6 164 10 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_174 : certGroup 6 174 7 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_181 : certGroup 6 181 7 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_188 : certGroup 6 188 13 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_201 : certGroup 6 201 8 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_209 : certGroup 6 209 4 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_213 : certGroup 6 213 8 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_221 : certGroup 6 221 11 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_232 : certGroup 6 232 10 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_242 : certGroup 6 242 14 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_256 : certGroup 6 256 12 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_268 : certGroup 6 268 12 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_280 : certGroup 6 280 10 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_290 : certGroup 6 290 13 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_303 : certGroup 6 303 14 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_317 : certGroup 6 317 9 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_326 : certGroup 6 326 8 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_334 : certGroup 6 334 7 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_341 : certGroup 6 341 11 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_352 : certGroup 6 352 11 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_363 : certGroup 6 363 7 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_370 : certGroup 6 370 11 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_381 : certGroup 6 381 8 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_389 : certGroup 6 389 5 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_394 : certGroup 6 394 10 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_404 : certGroup 6 404 9 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_413 : certGroup 6 413 6 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_419 : certGroup 6 419 8 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_427 : certGroup 6 427 9 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_436 : certGroup 6 436 13 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_449 : certGroup 6 449 10 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_459 : certGroup 6 459 12 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_471 : certGroup 6 471 6 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_477 : certGroup 6 477 10 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_487 : certGroup 6 487 7 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_494 : certGroup 6 494 7 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_501 : certGroup 6 501 10 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_511 : certGroup 6 511 5 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_516 : certGroup 6 516 5 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_521 : certGroup 6 521 5 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_526 : certGroup 6 526 5 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_531 : certGroup 6 531 4 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_535 : certGroup 6 535 7 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_542 : certGroup 6 542 5 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_547 : certGroup 6 547 7 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_554 : certGroup 6 554 9 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_6_563 : certGroup 6 563 1 = true := by decide +kernel

private lemma layer_6 : certGroup 6 0 (certCount 6) = true :=
  (checkGroup_join 6 0 326 238
    (checkGroup_join 6 0 164 162
    (checkGroup_join 6 0 89 75
    (checkGroup_join 6 0 45 44
    (checkGroup_join 6 0 21 24
    group_6_0 (checkGroup_join 6 21 11 13
    group_6_21 group_6_32)) (checkGroup_join 6 45 26 18
    (checkGroup_join 6 45 13 13
    group_6_45 group_6_58) (checkGroup_join 6 71 9 9
    group_6_71 group_6_80))) (checkGroup_join 6 89 43 32
    (checkGroup_join 6 89 24 19
    (checkGroup_join 6 89 13 11
    group_6_89 group_6_102) (checkGroup_join 6 113 9 10
    group_6_113 group_6_122)) (checkGroup_join 6 132 17 15
    (checkGroup_join 6 132 8 9
    group_6_132 group_6_140) (checkGroup_join 6 149 8 7
    group_6_149 group_6_157)))) (checkGroup_join 6 164 68 94
    (checkGroup_join 6 164 37 31
    (checkGroup_join 6 164 17 20
    (checkGroup_join 6 164 10 7
    group_6_164 group_6_174) (checkGroup_join 6 181 7 13
    group_6_181 group_6_188)) (checkGroup_join 6 201 12 19
    (checkGroup_join 6 201 8 4
    group_6_201 group_6_209) (checkGroup_join 6 213 8 11
    group_6_213 group_6_221))) (checkGroup_join 6 232 48 46
    (checkGroup_join 6 232 24 24
    (checkGroup_join 6 232 10 14
    group_6_232 group_6_242) (checkGroup_join 6 256 12 12
    group_6_256 group_6_268)) (checkGroup_join 6 280 23 23
    (checkGroup_join 6 280 10 13
    group_6_280 group_6_290) (checkGroup_join 6 303 14 9
    group_6_303 group_6_317))))) (checkGroup_join 6 326 133 105
    (checkGroup_join 6 326 63 70
    (checkGroup_join 6 326 26 37
    (checkGroup_join 6 326 8 18
    group_6_326 (checkGroup_join 6 334 7 11
    group_6_334 group_6_341)) (checkGroup_join 6 352 18 19
    (checkGroup_join 6 352 11 7
    group_6_352 group_6_363) (checkGroup_join 6 370 11 8
    group_6_370 group_6_381))) (checkGroup_join 6 389 30 40
    (checkGroup_join 6 389 15 15
    (checkGroup_join 6 389 5 10
    group_6_389 group_6_394) (checkGroup_join 6 404 9 6
    group_6_404 group_6_413)) (checkGroup_join 6 419 17 23
    (checkGroup_join 6 419 8 9
    group_6_419 group_6_427) (checkGroup_join 6 436 13 10
    group_6_436 group_6_449)))) (checkGroup_join 6 459 62 43
    (checkGroup_join 6 459 35 27
    (checkGroup_join 6 459 18 17
    (checkGroup_join 6 459 12 6
    group_6_459 group_6_471) (checkGroup_join 6 477 10 7
    group_6_477 group_6_487)) (checkGroup_join 6 494 17 10
    (checkGroup_join 6 494 7 10
    group_6_494 group_6_501) (checkGroup_join 6 511 5 5
    group_6_511 group_6_516))) (checkGroup_join 6 521 21 22
    (checkGroup_join 6 521 10 11
    (checkGroup_join 6 521 5 5
    group_6_521 group_6_526) (checkGroup_join 6 531 4 7
    group_6_531 group_6_535)) (checkGroup_join 6 542 12 10
    (checkGroup_join 6 542 5 7
    group_6_542 group_6_547) (checkGroup_join 6 554 9 1
    group_6_554 group_6_563))))))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_7_0 : certGroup 7 0 5 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_7_5 : certGroup 7 5 3 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_7_8 : certGroup 7 8 2 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_7_10 : certGroup 7 10 3 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_7_13 : certGroup 7 13 3 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_7_16 : certGroup 7 16 3 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_7_19 : certGroup 7 19 3 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_7_22 : certGroup 7 22 2 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_7_24 : certGroup 7 24 2 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_7_26 : certGroup 7 26 2 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_7_28 : certGroup 7 28 2 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_7_30 : certGroup 7 30 2 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_7_32 : certGroup 7 32 2 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_7_34 : certGroup 7 34 3 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_7_37 : certGroup 7 37 2 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_7_39 : certGroup 7 39 3 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_7_42 : certGroup 7 42 2 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_7_44 : certGroup 7 44 2 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_7_46 : certGroup 7 46 2 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_7_48 : certGroup 7 48 2 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_7_50 : certGroup 7 50 1 = true := by decide +kernel

private lemma layer_7 : certGroup 7 0 (certCount 7) = true :=
  (checkGroup_join 7 0 28 23
    (checkGroup_join 7 0 16 12
    (checkGroup_join 7 0 8 8
    (checkGroup_join 7 0 5 3
    group_7_0 group_7_5) (checkGroup_join 7 8 2 6
    group_7_8 (checkGroup_join 7 10 3 3
    group_7_10 group_7_13))) (checkGroup_join 7 16 6 6
    (checkGroup_join 7 16 3 3
    group_7_16 group_7_19) (checkGroup_join 7 22 2 4
    group_7_22 (checkGroup_join 7 24 2 2
    group_7_24 group_7_26)))) (checkGroup_join 7 28 11 12
    (checkGroup_join 7 28 4 7
    (checkGroup_join 7 28 2 2
    group_7_28 group_7_30) (checkGroup_join 7 32 2 5
    group_7_32 (checkGroup_join 7 34 3 2
    group_7_34 group_7_37))) (checkGroup_join 7 39 7 5
    (checkGroup_join 7 39 3 4
    group_7_39 (checkGroup_join 7 42 2 2
    group_7_42 group_7_44)) (checkGroup_join 7 46 2 3
    group_7_46 (checkGroup_join 7 48 2 1
    group_7_48 group_7_50)))))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_8_0 : certGroup 8 0 2 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_8_2 : certGroup 8 2 1 = true := by decide +kernel

private lemma layer_8 : certGroup 8 0 (certCount 8) = true :=
  (checkGroup_join 8 0 2 1
    group_8_0 group_8_2)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma group_9_0 : certGroup 9 0 1 = true := by decide +kernel

private lemma layer_9 : certGroup 9 0 (certCount 9) = true :=
  group_9_0

private lemma allChecked (k : ℕ) (hk : k ≤ 9) (i : ℕ) (hi : i < certCount k) :
    checkNode certCount certState certLocate renameFast k i = true := by
  have h : certGroup k 0 (certCount k) = true := by
    interval_cases k
    · exact layer_0
    · exact layer_1
    · exact layer_2
    · exact layer_3
    · exact layer_4
    · exact layer_5
    · exact layer_6
    · exact layer_7
    · exact layer_8
    · exact layer_9
  exact checkGroup_at h i (Nat.zero_le i) (by simpa using hi)

private lemma rootState : (certState 9 0).toFinset = fiveInputs.toFinset := by decide +kernel

private lemma noNine (t : W) (ht : t=goal ∨ t= ~~~goal)
    (h : build basicOps t 9 fiveInputs.toFinset) : False := by
  obtain ⟨S,hsub,hS⟩ := compress h
  have hAll : S = fiveInputs.toFinset := by
    apply Finset.eq_of_subset_of_card_le hsub
    have here : ∀ w ∈ fiveInputs, w ∈ S := by
      intro w hw
      have witness : ∃ i : Fin 60, differs i w ∧ ∀ v ∈ fiveInputs, v ≠ w → ¬differs i v := by
        have index : ∀ q ∈ fiveInputs, ∃ j : Fin 5, fiveInputs[j.val]! = q := by
          intro q hq
          simp only [fiveInputs, List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl|rfl|rfl|rfl|rfl
          all_goals first | exact ⟨0,rfl⟩ | exact ⟨1,rfl⟩ | exact ⟨2,rfl⟩ |
            exact ⟨3,rfl⟩ | exact ⟨4,rfl⟩
        have fact : ∀ j : Fin 5, ∃ i : Fin 60, differs i fiveInputs[j.val]! ∧
            ∀ l : Fin 5, fiveInputs[l.val]! ≠ fiveInputs[j.val]! →
              ¬differs i fiveInputs[l.val]! := by
          unfold differs
          decide +kernel
        obtain ⟨j,rfl⟩ := index w hw
        obtain ⟨i,hi,hrest⟩ := fact j
        refine ⟨i,hi,?_⟩
        intro v hv hvw
        obtain ⟨l,rfl⟩ := index v hv
        exact hrest l hvw
      obtain ⟨i,_,hu⟩ := witness
      have hd : differs i t := by
        rcases ht with rfl | rfl
        · exact (goal_changes i).1
        · exact (goal_changes i).2
      obtain ⟨u,hus,h⟩ := live_separates (differs i) hd (ops_differs i) hS
      by_cases e : u=w
      · exact e ▸ hus
      · exact False.elim (hu u (List.mem_toFinset.mp (hsub hus)) e h)
    exact Finset.card_le_card (fun _ h => here _ (List.mem_toFinset.mp h))
  rw [hAll, ← rootState] at hS
  exact noLiveTable renameFast_inj renameFast_op renameFast_goal allChecked 9 (by omega) 0
    (by decide +kernel) t ht hS

def witness : Circuit :=
  ⟨[⟨.and,[0,1]⟩,⟨.or,[0,1]⟩,⟨.or,[2,6]⟩,⟨.and,[7,8]⟩,⟨.and,[6,2]⟩,⟨.or,[3,10]⟩,
    ⟨.and,[9,11]⟩,⟨.and,[10,3]⟩,⟨.or,[4,13]⟩,⟨.and,[12,14]⟩,⟨.and,[13,4]⟩,
    ⟨.or,[5,16]⟩,⟨.and,[15,17]⟩],18⟩

private lemma witness_mono : Monotone2 witness := by simp [Monotone2,witness]

private lemma witness_eval : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = targetFun x := by
  decide +kernel

end PEqualNP.Outside.L_meta_12186

open PEqualNP.Outside.L_meta_12186 in
theorem PEqualNP.Outside.L_meta_12186 :
∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3900735488 * 2 ^ 32 + 2147483648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3900735488 * 2 ^ 32 + 2147483648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hs
  obtain ⟨C,fits,size,computes⟩ := hs
  by_cases hasNot : ∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · obtain ⟨g,mem,op⟩ := hasNot
    have short : binaryCost C.gates < C.size :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨g,mem,by simp [isBinary,op]⟩
    have bound := bound_from_impossible 11 (no_eleven_binary noNine) C.gates C.output fits computes
    refine ⟨witness,witness_mono,?_,witness_eval⟩
    change 13 ≤ s
    omega
  · refine ⟨C,?_,size,computes⟩
    intro g mem
    obtain ⟨op,cap⟩ := fits g mem
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun eq => (hasNot ⟨g,mem,eq⟩).elim)),cap⟩
