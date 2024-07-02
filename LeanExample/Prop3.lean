variable (p q r : Prop)

#check p → q → p ∧ q
#check ¬p → p ↔ False

example (hp : p) (hq : q) : p ∧ q := And.intro hp hq
example (h : p ∧ q) : p := And.left h
example (h : p ∧ q) : q := And.right h
example (hp : p) : p ∨ q := Or.intro_left q hp
example (hq : q) : p ∨ q := Or.intro_right p hq

example (h : p ∧ q) : q ∧ p :=
  And.intro (And.right h) (And.left h)

example (h : p ∨ q) : q ∨ p :=
  Or.elim h
    (fun hp : p =>
      show q ∨ p from Or.intro_right q hp)
    (fun hq : q =>
      show q ∨ p from Or.intro_left p hq)

example (h : p ∨ q) : q ∨ p :=
  Or.elim h
    (fun hp : p => Or.inr hp)
    (fun hq : q => Or.inl hq)

example (h : p ∨ q) : q ∨ p :=
  h.elim (fun hp => Or.inr hp) (fun hq => Or.inl hq)

