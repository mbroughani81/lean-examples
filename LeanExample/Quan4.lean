example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  Exists.intro 1 h

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  Exists.intro 0 h

def ggg (x : Nat) : (x > 0) → ∃ y, y < x :=
  fun h => Exists.intro 0 h

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  have h := (And.intro hxy hyz)
  Exists.intro y h

variable (g : Nat → Nat → Nat)
variable (hg : g 0 0 = 0)

def p1 (x: Nat) : Prop := g x x = x
def p2 (x: Nat) : Prop := g x 0 = x
def p3 (x: Nat) : Prop := g 0 0 = x
def p4 (x: Nat) : Prop := g x x = 0
theorem gex1 : ∃ x, g x x = x := ⟨0, hg⟩
theorem gex2 : ∃ x, g x 0 = x := ⟨0, hg⟩
theorem gex3 : ∃ x, g 0 0 = x := ⟨0, hg⟩
theorem gex4 : ∃ x, g x x = 0 := ⟨0, hg⟩
