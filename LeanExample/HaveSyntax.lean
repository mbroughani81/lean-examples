variable (p q : Prop)


example (h : p ∧ q) : q ∧ p :=
  (fun hp : p =>
    (fun hq : q =>
      show q ∧ p from And.intro hq hp)
      h.right)
    h.left

example (h : p ∧ q) : q ∧ p :=
  let hp : p := h.left
  let hq : q := h.right
  show q ∧ p from And.intro hq hp

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  have hq : q := h.right
  show q ∧ p from And.intro hq hp

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  suffices hq : q from And.intro hq hp
  show q from And.right h
