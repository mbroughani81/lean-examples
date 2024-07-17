universe u
def Lst (α : Type u) : Type u := List α

def Lst.cons {α : Type u} (a : α) (as : Lst α) : Lst α := List.cons a as
def Lst.cons' (a : α) (as : Lst α) : Lst α := List.cons a as
def Lst.cons'' (α : Type u) (a : α) (as : Lst α) : Lst α := List.cons a as
def Lst.nil {α : Type u} : Lst α := List.nil
def Lst.nil' : Lst α := List.nil
def Lst.nil'' (α : Type u) : Lst α := List.nil
-- def Lst.append {α : Type u} (as bs : Lst α) : Lst α := List.append as bs

#check Lst.cons
#check Lst.cons'
#check Lst.nil
#check Lst.nil'
#check Lst.cons 0 Lst.nil
#check Lst.cons' 0 Lst.nil'
#check Lst.nil''
def x := Lst.cons'' Nat 1 (Lst.nil'' Nat)
