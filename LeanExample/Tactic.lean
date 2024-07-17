theorem fst : ∀ a b : Prop, a → b → a :=
  by
    -- intro a₁ b₁
    -- intro ha hb
    intro a₁ b₁ ha hb
    assumption
    -- exact ha

theorem fst_of_two_props_params (a b : Prop) (ha : a) (hb : b) :
  a :=
  by
    assumption
    -- exact ha

theorem prop_comp (a b c : Prop) (hab : a → b) (hbc : b → c) :
  a → c :=
  by
    intro ha
    apply hbc
    apply hab
    assumption
    -- exact ha

theorem And_swap (a b : Prop) :
  a ∧ b → b ∧ a :=
  by
    intro hab
    apply And.intro
    apply And.right -- Goal here????
    exact hab
    -- assumption
    apply And.left
    exact hab
    -- assumption

theorem Nat.succ_neq_self (n : Nat) :
  Nat.succ n ≠ n :=
by
  induction n with
  | zero => simp
  | succ n' ih => simp [ih]

#check And.intro

theorem And_swap_braces :
  ∀ a b : Prop, a ∧ b → b ∧ a :=
  by
    intro a b hab
    apply And.intro
    -- { apply And.right
    --   exact hab }
    { exact And.right hab }
    -- { apply And.left
    --   exact hab }
    { exact And.left hab }

opaque f : Nat → Nat

theorem f5_if (h : ∀n : Nat, f n = n) : f 5 = 5 :=
  by exact h 5

#check Or.inl

def double (n : Nat) : Nat :=
  n + n

theorem Exists_double_iden :
  ∃n : Nat, double n = n :=
  by
    apply Exists.intro 0
    rfl
