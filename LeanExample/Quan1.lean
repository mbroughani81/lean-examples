example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ x : α, p x :=
  fun h : (∀ x : α, p x ∧ q x) =>
  fun x : α =>
  And.left (h x)
