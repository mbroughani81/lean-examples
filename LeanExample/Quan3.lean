variable (α : Type) (r : α → α → Prop)

variable (refl_r : ∀ x, r x x)
variable (symm_r : ∀ {x y}, r x y → r y x)
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) : r a d :=
  trans_r hab (trans_r (symm_r hcb) hcd)

#check α
#check r
variable (β₀: Sort 0) (β₁ : Sort 1) (β₂ : Sort 2)
#check β₀
#check β₁
#check β₂
#check Nat
#check Sort 0
#check Type
#check Type 0
#check Sort 1
#check Type 1
#check Sort 2
