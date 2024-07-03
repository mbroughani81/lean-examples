-- p ∧ q ↔ q ∧ p
variable (p q : Prop)
-- proof 1
theorem tt {p q : Prop}(h : p ∧ q) : q ∧ p :=
  And.intro (And.right h) (And.left h)
theorem and_swap : p ∧ q ↔ q ∧ p :=
  let h₁ : p ∧ q → q ∧ p := fun(hp : p ∧ q) => tt hp;
  let h₂ : q ∧ p → p ∧ q := fun(hp : q ∧ p) => tt hp;
  Iff.intro h₁ h₂
#print and_swap
#check and_swap
section gg
  variable (x₁ x₂ x₃ x₄ : Prop)
  #check and_swap (x₁ ∧ x₂) (x₃ ∨ x₄)
end gg

-- proof 2
theorem and_swap_2 : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q =>
     show q ∧ p from And.intro (And.right h) (And.left h))
    (fun h : q ∧ p =>
     show p ∧ q from And.intro (And.right h) (And.left h))
#check and_swap_2 p q
#check and_swap_2
variable (h : p ∧ q)
theorem thr1 : q ∧ p := Iff.mp (and_swap_2 p q) h
#check thr1
