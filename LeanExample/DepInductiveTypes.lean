inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons (a : α) {n : Nat} (v : Vec α n) : Vec α (n + 1)

-- #check Vec
def x := Vec.cons 3 (Vec.cons 2 (Vec.cons 1 Vec.nil))
-- #check x

def listOfVec {β : Type} {n : Nat} : Vec β n → List β
  | Vec.nil      => []
  | Vec.cons x v => x :: listOfVec v
def listOfVec' : Vec α n → List α
  | Vec.nil      => []
  | Vec.cons x v => x :: listOfVec v

#check listOfVec
#check listOfVec'
#eval listOfVec x
#eval List.length (listOfVec x)



-- theorem length_listOfVec {α : Type} {n : Nat} {v : Vec α n} :
--   List.length (listOfVec v) = n := sorry


theorem length_listOfVec {α : Type} :
  ∀(n : Nat) (v : Vec α n), List.length (listOfVec v) = n
    | _, Vec.nil => by rfl
    | _, Vec.cons a v =>
      by
        simp [listOfVec]
        simp[length_listOfVec _ v]
