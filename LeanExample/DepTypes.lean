def cons (α : Type) (a : α) (as : List α) : List α :=
  List.cons a as

#check cons Nat
#check @List.cons
#check List.cons

universe u v

def f (α : Type u) (β : α → Type v) (a : α) (b : β a) : (a : α) × β a :=
  ⟨a, b⟩

def g (α : Type u) (β : α → Type v) (a : α) (b : β a) : Σ a : α, β a :=
  Sigma.mk a b

def h1 (x : Nat) : Nat :=
  (f Type (fun α => α) Nat x).2

def hh1 (x : Nat) : Type :=
  (f Type (fun α => α) Nat x).1

#check hh1 5
#check h1 5

#check (List.nil : List Nat)
#check @id
#check @id Nat 1
#check @id Int 1
#check id 1
