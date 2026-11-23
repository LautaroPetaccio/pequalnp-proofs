import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_752

private def pairs : List (Fin 4 × Fin 4) := [(0, 1), (1, 0), (2, 3), (3, 2)]

private def graph : SimpleGraph (Fin 4) where
  Adj a b := (a, b) ∈ pairs
  symm := by
    have h : ∀ a b : Fin 4, (a, b) ∈ pairs → (b, a) ∈ pairs := by decide +kernel
    exact ⟨fun {_ _} => h _ _⟩
  loopless := by
    have h : ∀ a : Fin 4, (a, a) ∉ pairs := by decide +kernel
    exact ⟨h⟩

private def adjDecidable : DecidableRel graph.Adj := fun a b =>
  inferInstanceAs (Decidable ((a, b) ∈ pairs))

private theorem acyclic : graph.IsAcyclic := by
  have unique : ∀ a b c : Fin 4, (a, b) ∈ pairs → (a, c) ∈ pairs → b = c := by
    decide +kernel
  intro v p hp
  have hl := hp.three_le_length
  have h₀ := p.adj_getVert_succ (i := 0) (by omega)
  have h₁ := p.adj_getVert_succ (i := 1) (by omega)
  exact (hp.getVert_sub_one_ne_getVert_add_one (i := 1) (by omega))
    (unique _ _ _ h₀.symm h₁)

private theorem coverLower (T : Finset (Fin 4))
    (h : ∀ a b : Fin 4, graph.Adj a b → a ∈ T ∨ b ∈ T) : 2 ≤ T.card := by
  have e₀ : graph.Adj 0 1 := @of_decide_eq_true _ (adjDecidable 0 1) rfl
  have e₁ : graph.Adj 2 3 := @of_decide_eq_true _ (adjDecidable 2 3) rfl
  rcases h 0 1 e₀ with h₀ | h₁ <;> rcases h 2 3 e₁ with h₂ | h₃
  · exact Finset.one_lt_card.mpr ⟨0, h₀, 2, h₂, by decide⟩
  · exact Finset.one_lt_card.mpr ⟨0, h₀, 3, h₃, by decide⟩
  · exact Finset.one_lt_card.mpr ⟨1, h₁, 2, h₂, by decide⟩
  · exact Finset.one_lt_card.mpr ⟨1, h₁, 3, h₃, by decide⟩

end PEqualNP.Outside.L_meta_752

theorem PEqualNP.Outside.L_meta_752 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 4
      (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) s ↔ 3 ≤ s := by
  open PEqualNP.Outside.L_meta_752 in
  intro s
  letI := adjDecidable
  have functionEq :
      (fun x : Fin 4 → Bool => decide (∃ i j : Fin 4, graph.Adj i j ∧ x i = true ∧ x j = true)) =
      (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) := by
    funext x
    exact (by
      have h : ∀ x : Fin 4 → Bool,
          decide (∃ i j : Fin 4, graph.Adj i j ∧ x i = true ∧ x j = true) =
            ((x 0 && x 1) || (x 2 && x 3)) := by decide +kernel
      exact h x)
  have edges : graph.edgeFinset.card = 2 := by decide +kernel
  have nonempty : ∃ a b : Fin 4, graph.Adj a b := ⟨0, 1, of_decide_eq_true rfl⟩
  rw [← functionEq]
  constructor
  · intro h
    have lower := PEqualNP.MetaComplexity.L104 4 2 s graph acyclic nonempty coverLower h
    omega
  · intro hs
    let T : Finset (Fin 4) := {0, 2}
    have cover : ∀ a b : Fin 4, graph.Adj a b → a ∈ T ∨ b ∈ T := by
      dsimp [T]
      decide
    have size : graph.edgeFinset.card + T.card - 1 = 3 := by decide +kernel
    obtain ⟨C, hC, hsize, heval⟩ := PEqualNP.MetaComplexity.L105 4 graph T nonempty cover
    exact ⟨C, hC, by omega, heval⟩
