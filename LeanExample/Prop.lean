variable (p q r : Prop)
#check p    -- p is Prop
#check Prop -- Prop is Type
variable (term1 : p)
#check term1   -- t1 is p

variable (x : Nat)
#check x
#check Nat
-- variable (x1 : x) ERROR


variable {p : Prop}
variable {q : Prop}

-- theorem t1 : p → q → p := fun hp : p => fun hq : q => hp
-- theorem t1 : p → q → p :=
--   fun hp : p =>
--   fun _  =>
--   hp
theorem t1 (hp : p) (hq : q) : p := hp
-- theorem t1 {p q : Prop} (hp : p) (hq : q) : p := hp

theorem t3 : p → (p → q) → q  :=
  fun hp : p =>
  fun hq : (p -> q) =>
  hq hp

theorem t3' (hp : p) : (p → q) → q  :=
  fun hq : (p -> q) =>
  hq hp

axiom hp : p
theorem t2 {p q : Prop} : q → p := t1 hp

-- #eval And False True
#check And False True
axiom unsound : False
#check 1 = 0
theorem ex : 1 = 0 :=
  False.elim unsound
