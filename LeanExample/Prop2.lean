theorem t1 (p q : Prop) (hp : p) (hq : q) : p := hp
variable (p q r s : Prop)

#check t1 p q
-- p → q → p
#check t1 r s
-- r → s → r
#check t1 (r → s) (s → r)
-- (r → s) → (s → r) → r → s
variable (h : r → s)
#check t1 (r → s) (s → r)
#check t1 (r → s) (s → r) h

theorem g1 (h₁ : p → q) (h₂ : p) : q :=
  h₁ h₂

theorem t2 (h₁ : q → r) (h₂ : p → q) : p → r :=
  fun h₃ : p =>
  h₁ (h₂ h₃)

#print t2
