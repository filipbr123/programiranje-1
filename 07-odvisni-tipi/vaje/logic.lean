-- Izomorfizmi

theorem eq1 {A B : Prop} : (A ∧ B) ↔ (B ∧ A) := by
  apply Iff.intro
  . intro h
    apply And.intro
    . exact h.right
    . exact h.left
  . intro h
    apply And.intro
    . exact h.right
    . exact h.left



theorem eq2 {A B : Prop} : (A ∨ B) ↔ (B ∨ A) := by
  apply Iff.intro
  . intro h
    apply Or.elim h
    . exact Or.inr
    . exact Or.inl
  . intro h
    apply Or.elim h
    . exact Or.inr
    . exact Or.inl



theorem eq3 {A B C : Prop} : (A ∧ (B ∧ C)) ↔ (B ∧ (A ∧ C)) := by
  apply Iff.intro
  . intro h
    apply And.intro
    . exact h.right.left
    . apply And.intro
      . exact h.left
      . exact h.right.right
  . intro h
    apply And.intro
    . exact h.right.left
    . apply And.intro
      . exact h.left
      . exact h.right.right



theorem eq4 {A B C : Prop} : (A ∨ (B ∨ C)) ↔ (B ∨ (A ∨ C)) := by
  apply Iff.intro
  . intro h
    apply Or.elim h
    . intro hA
      . exact Or.inr (Or.inl hA)
    . intro hBC
      apply Or.elim hBC
      . intro hB
        . exact Or.inl hB
      . intro hC
        .exact Or.inr (Or.inr hC)
  . intro h
    apply Or.elim h
    . intro hB
      . exact Or.inr (Or.inl hB)
    . intro hAC
      apply Or.elim hAC
      . intro hA
        . exact Or.inl hA
      . intro hC
        .exact Or.inr (Or.inr hC)



theorem eq5 {A B C : Prop} : A ∧ (B ∨ C) ↔ (A ∧ B) ∨ (A ∧ C) := by
  apply Iff.intro
  intro h
  cases h with
  | intro hA hBC =>
     cases hBC with
     | inl hB => exact Or.inl (And.intro hA hB)
     | inr hC => exact Or.inr (And.intro hA hC)
  intro h
  cases h with
  | inl hAB =>
      cases hAB with
      | intro hA hB =>
        exact And.intro hA (Or.inl hB)
  | inr hAC =>
      cases hAC with
      | intro hA hC =>
        exact And.intro hA (Or.inr hC)



theorem eq6 {A B C : Prop} : (B ∨ C) → A ↔ (B → A) ∧ (C → A) := by
  apply Iff.intro
  . intro h
    apply And.intro
    . intro hb
      . exact h (Or.inl hb)
    . intro hc
      . exact h (Or.inr hc)
  . intro h
    . intro hBC
      cases hBC with
      | inl hB => exact h.left hB
      | inr hC => exact h.right hC



theorem eq7 {A B C : Prop} : C → (A ∧ B) ↔ (C → A) ∧ (C → B) := by
  apply Iff.intro
  . intro h
    apply And.intro
    . intro hc1
      exact (h hc1).left
    . intro hc2
      exact (h hc2).right
  . intro h hc3
    exact And.intro (h.left hc3) (h.right hc3)
