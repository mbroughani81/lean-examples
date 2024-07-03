open Classical

variable (p q: Prop)
#check em p
-- em -> dne
theorem dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (em p)
    (fun hp : p => hp)
    (fun hnp : ¬p => absurd hnp h)
-- dne -> em
-- 1. dne -> raa
theorem tri1 {p : Prop} (hh : ¬p → False) : ¬¬p := hh
theorem raa {p : Prop} : (¬p → False) → p :=
  (fun hnp : ¬p → False =>
    have nnp : ¬¬p := tri1 hnp
    show p from dne nnp)
-- tri1 can be removed (because ¬p → False equals ¬¬p)
theorem raa' {p : Prop} : (¬p → False) → p :=
  (fun hnp : ¬p → False =>
    show p from dne hnp)
-- 2. raa -> em
theorem emm {p : Prop} : p ∨ ¬p :=
  let h : ¬(p ∨ ¬p) → False := (fun h₁ : ¬(p ∨ ¬p) =>
    let hnp : p -> False := (fun hp : p =>
      let xx : p ∨ ¬p := Or.intro_left (¬p) hp
      absurd xx h₁
    );
    let hnp' : ¬p := hnp;
    let xx : p ∨ ¬p := Or.intro_right p hnp'
    absurd xx h₁
  )
  raa h
-- 3. dne -> em (dne -> raa -> em) is proved
--
example (h : ¬¬p) : p :=
  byCases
    (fun h1 : p => h1)
    (fun h1 : ¬p => absurd h1 h)

example (h : ¬¬p) : p :=
  byContradiction
    (fun h1 : ¬p =>
     show False from h h1)

example (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
  Or.elim (em p)
    (fun hp : p =>
      -- ¬q *is* q -> false *is* function from q to False
      have hnq : ¬q := (show ¬q from
        (fun hq : q => h ⟨hp, hq⟩))
      Or.inr hnq)
    (fun hnp : ¬p =>
      Or.inl hnp)
