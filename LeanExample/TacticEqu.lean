#check Eq.refl
#check Eq.symm
#check Eq.trans
#check Eq.subst

theorem Eq_trans_symm {α : Type} (a b c : α) (hab : a = b) (hcb : c = b) :
  a = c :=
  by
    apply Eq.trans
    { exact hab }
    { apply Eq.symm
      exact hcb }

theorem example1 (a b c : Nat) (h : a = b) (h2 : b = c) : a = c :=
  by
    rw [h]
    rw [h2]

-- opaque a₁ : Nat
-- opaque b₁ : Nat
variable (a₁ b₁ : Nat)
-- def xxxxx := a₁ = b₁
def xxxxx := Eq a₁ b₁
#check xxxxx
#print xxxxx

opaque f : Nat → Nat
opaque g : Nat → Nat
opaque h : Nat → Nat → Nat → Prop
theorem g1 (hg : ∀x : Nat, g x = f x) : h (f a) (g b) (g c) :=
  by
    rw [hg] -- g b replaced by f b
    rw [hg] -- g c replaced by f c
    sorry
theorem g2 (hg : ∀x : Nat, g x = f x) : h (f a) (g b) (g c) :=
  by
    rw [←hg] -- f a replaced by g a
    sorry

example (a b : Nat) (h : a = b) : a + 0 = b :=
  by
    simp
    exact h

example (a b : Nat) (h : a = b) : a + a = b + a :=
  by
    simp [h]

def add : Nat → Nat → Nat
  | m, Nat.zero   => m
  | m, Nat.succ n => Nat.succ (add m n)

theorem add_zero (n : Nat) :
  add 0 n = n :=
  by
    induction n with
    | zero       => rfl
    | succ n' ih => simp [add, ih] -- WTF??? [add, ih]

theorem add_succ (m n : Nat) :
  add (Nat.succ m ) n = Nat.succ (add m n) :=
  by
    induction n with
    | zero       => rfl
    | succ n' ih => simp [add, ih]


theorem add_comm (m n : Nat) : add m n = add n m :=
  by
    induction n with
    | zero       => simp [add, add_zero]
    | succ n' ih => simp [add, add_succ, ih]
