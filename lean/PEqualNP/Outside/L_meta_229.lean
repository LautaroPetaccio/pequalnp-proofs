import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_229

open PEqualNP.MetaComplexity

private def someTrue {n : ℕ} (x : Fin n → Bool) : Bool :=
  decide (∃ i : Fin n, x i = true)

private theorem false_iff_zero {n : ℕ} (x : Fin n → Bool) :
    someTrue x = false ↔ x = fun _ => false := by
  constructor
  · intro h
    funext i
    cases hi : x i
    · rfl
    · have ht : someTrue x = true := decide_eq_true ⟨i,hi⟩
      simp [h] at ht
  · rintro rfl
    simp [someTrue]

private theorem rank_positive_of_entry {α β : Type*} [Fintype α] [Fintype β]
    (M : Matrix α β ℚ) (x : α) (y : β) (h : M x y ≠ 0) : 1 ≤ M.rank := by
  rw [Matrix.rank_eq_finrank_span_cols]
  have hcol : M.col y ≠ 0 := by
    intro he
    exact h (congrFun he x)
  let p := Submodule.span ℚ {M.col y}
  have hp : p ≤ Submodule.span ℚ (Set.range M.col) :=
    Submodule.span_mono (Set.singleton_subset_iff.mpr ⟨y,rfl⟩)
  have hdim : Module.finrank ℚ p = 1 := finrank_span_singleton hcol
  rw [← hdim]
  exact Submodule.finrank_mono hp

private theorem lower (n : ℕ) (τ : (Fin n → Bool) → (Fin n → Bool) → ℕ)
    (ht : IsTyping n someTrue τ) :
    n ≤ ∑ i : Fin n, ∑ b : Bool, (typedMatrix n someTrue τ i b).rank := by
  classical
  have each (i : Fin n) : 1 ≤ (typedMatrix n someTrue τ i true).rank := by
    let x : Fin n → Bool := fun j => decide (j = i)
    let z : Fin n → Bool := fun _ => false
    have hx : someTrue x = true := decide_eq_true ⟨i, by simp [x]⟩
    have hz : someTrue z = false := (false_iff_zero z).mpr rfl
    obtain ⟨j,hj,hne⟩ := ht x z hx hz
    have hji : j = i := by simpa [x,z] using hne
    subst j
    apply rank_positive_of_entry _ x z
    simp [typedMatrix,hx,hz,hj,x]
  calc
    n = ∑ _i : Fin n, 1 := by simp
    _ ≤ _ := Finset.sum_le_sum (fun i _ => by
      rw [Fintype.sum_bool]
      have h := each i
      omega)

private theorem upper (n : ℕ) : HasTypedRank n someTrue n := by
  classical
  let τ : (Fin n → Bool) → (Fin n → Bool) → ℕ :=
    fun x _ => if h : ∃ i : Fin n, x i = true then h.choose.val else 0
  have chosen (x y : Fin n → Bool) (hx : someTrue x = true) (i : Fin n)
      (hτ : τ x y = i.val) : x i = true := by
    have he : ∃ j : Fin n, x j = true := of_decide_eq_true hx
    have hv : he.choose.val = i.val := by simpa [τ, he] using hτ
    have hi : he.choose = i := Fin.ext hv
    exact hi ▸ he.choose_spec
  refine ⟨τ, ?_, ?_⟩
  · intro x y hx hy
    have he : ∃ j : Fin n, x j = true := of_decide_eq_true hx
    have hz := (false_iff_zero y).mp hy
    exact ⟨he.choose, by simp [τ, he], by simp [hz, he.choose_spec]⟩
  · let z : Fin n → Bool := fun _ => false
    have hzero (i : Fin n) : typedMatrix n someTrue τ i false = 0 := by
      ext x y
      simp only [typedMatrix, Matrix.zero_apply]
      split
      next h =>
        have ht := chosen x y h.1 i h.2.2.1
        simp [ht] at h
      next _ => rfl
    have hone (i : Fin n) : (typedMatrix n someTrue τ i true).rank ≤ 1 := by
      let M := typedMatrix n someTrue τ i true
      have he : M = Matrix.vecMulVec (fun x => M x z)
          (fun y => if y = z then 1 else 0) := by
        ext x y
        by_cases hy : y = z
        · subst y
          simp [Matrix.vecMulVec]
        · have hnot : someTrue y ≠ false := fun h => hy ((false_iff_zero y).mp h)
          simp [M, typedMatrix, Matrix.vecMulVec, hy, hnot]
      change M.rank ≤ 1
      rw [he]
      exact Matrix.rank_vecMulVec_le _ _
    calc
      _ ≤ ∑ _i : Fin n, 1 := Finset.sum_le_sum (fun i _ => by
        rw [Fintype.sum_bool, hzero, Matrix.rank_zero]
        simpa using hone i)
      _ = n := by simp

end PEqualNP.Outside.L_meta_229

theorem PEqualNP.Outside.L_meta_229 :
    ∀ n : ℕ, 1 ≤ n → PEqualNP.MetaComplexity.HasTypedRank n (fun x => decide (∃ i : Fin n, x i = true)) n ∧
    ¬ PEqualNP.MetaComplexity.HasTypedRank n (fun x => decide (∃ i : Fin n, x i = true)) (n - 1) := by
  intro n hn
  refine ⟨PEqualNP.Outside.L_meta_229.upper n, ?_⟩
  rintro ⟨τ,hτ,hs⟩
  have hl := PEqualNP.Outside.L_meta_229.lower n τ hτ
  unfold PEqualNP.Outside.L_meta_229.someTrue at hl
  omega
