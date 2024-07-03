variable (α : Type) (r : α → α → Prop)
variable (trans_r : ∀ x y z, r x y → r y z → r x z)

variable (a b c : α)
variable (hab : r a b) (hbc : r b c)

#check trans_r
#check trans_r a b c
#check trans_r a b c hab
#check trans_r a b c hab hbc

variable (trans_r' : ∀ {x y z}, r x y → r y z → r x z)

#check trans_r'
#check trans_r' hab
#check trans_r' hab hbc
