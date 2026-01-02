
variable (α : Type) (p q : α → Prop) (r : Prop)
variable (r : Prop)

-- Izjave napišite na list papirja, nato pa jih dokažite v datoteki.

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  apply Iff.intro
  . intro h x hp
    apply h
    exact Exists.intro x hp
  . intro h hp
    cases hp with
    | intro x hx => exact (h x) hx



example : (r → ∀ x, p x) ↔ (∀ x, r → p x) := by
  apply Iff.intro
  . intro h x hr
    exact (h hr) x
  . intro h hr x
    exact (h x) hr



example : r ∧ (∃ x, p x) ↔ (∃ x, r ∧ p x) := by
  apply Iff.intro
  . intro h
    cases h with
    | intro hr hex =>
      cases hex with
      | intro x px =>
         apply Exists.intro x
         exact And.intro hr px
  . intro h
    cases h with
    | intro x hrpx =>
      cases hrpx with
      | intro r px =>
        apply And.intro
        . exact r
        . apply Exists.intro x
          exact px



example : r ∨ (∀ x, p x) → (∀ x, r ∨ p x) := by
  intro h x
  cases h with
  | inl r => exact Or.inl r
  | inr px => exact Or.inr (px x)



-- Tu pa nam bo v pomoč klasična logika
-- namig: `Classical.byContradiction` in `Classical.em` sta lahko v pomoč
open Classical

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by
  apply Iff.intro
  . intro h
    apply Classical.byContradiction
    . intro nepx
      apply h
      . intro x
        apply Classical.byContradiction
        . intro npx
          apply nepx
          exact Exists.intro x npx
  . intro h npx
    cases h with
    | intro x nx => exact nx (npx x)



example : r ∨ (∀ x, p x) ↔ (∀ x, r ∨ p x) := by
  apply Iff.intro
  . intro h x
    cases h with
    | inl r => exact Or.inl r
    | inr px => exact Or.inr (px x)
  . intro h
    have x := Classical.em r
    cases x with
    | inl hr => exact Or.inl hr
    | inr nhr =>
        right
        intro x
        have hx := h x
        cases hx
        case inl hr => contradiction
        case inr px => exact px
