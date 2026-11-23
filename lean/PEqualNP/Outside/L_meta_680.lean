import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_680 :
    ∀ (n : ℕ) [NeZero n] (D : Finset (ZMod n)),
    (∀ d : ZMod n, d ≠ 0 → ((D ×ˢ D).filter (fun q : ZMod n × ZMod n => q.1 - q.2 = d)).card = 1) →
    (∀ s t : ZMod n, s ≠ t →
        (D.image (fun a : ZMod n => a + s) ∩ D.image (fun a : ZMod n => a + t)).card = 1) ∧
    (∀ x : ZMod n,
        (Finset.univ.filter (fun w : ZMod n => x ∈ D.image (fun a : ZMod n => a + w))).card = D.card) := by
  classical
  intro n _ D h
  constructor
  · intro s t hst
    rw [← h (t - s) (sub_ne_zero.mpr hst.symm)]
    apply Finset.card_nbij' (fun x => (x - s, x - t)) (fun q => q.1 + s)
    · intro x hx
      obtain ⟨hs, ht⟩ := Finset.mem_inter.mp hx
      obtain ⟨a, ha, has⟩ := Finset.mem_image.mp hs
      obtain ⟨b, hb, hbt⟩ := Finset.mem_image.mp ht
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_product.mpr
        exact ⟨by simpa [← has] using ha, by simpa [← hbt] using hb⟩
      · dsimp
        ring
    · rintro ⟨a, b⟩ hq
      obtain ⟨hab, hd⟩ := Finset.mem_filter.mp hq
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
      change a - b = t - s at hd
      apply Finset.mem_inter.mpr
      exact ⟨Finset.mem_image.mpr ⟨a, ha, rfl⟩,
        Finset.mem_image.mpr ⟨b, hb, by dsimp; linear_combination -hd⟩⟩
    · intro x _
      exact sub_add_cancel x s
    · rintro ⟨a, b⟩ hq
      have hd := (Finset.mem_filter.mp hq).2
      change a - b = t - s at hd
      apply Prod.ext
      · exact add_sub_cancel_right a s
      · dsimp
        linear_combination hd
  · intro x
    apply Finset.card_nbij' (fun w => x - w) (fun a => x - a)
    · intro w hw
      obtain ⟨a, ha, haw⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hw).2
      simpa [← haw] using ha
    · intro a ha
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, Finset.mem_image.mpr ⟨a, ha, by dsimp; ring⟩⟩
    · intro w _
      dsimp
      ring
    · intro a _
      dsimp
      ring
