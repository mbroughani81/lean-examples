inductive Score : Type where
  | vs       : Nat → Nat → Score
  | advServ  : Score
  | advRecv  : Score
  | gameServ : Score
  | gameRecv : Score
infixr:50 " – " => Score.vs

def x : Score := (0–40)

inductive Step : Score → Score → Prop where
  | serv_0_15     : ∀n, Step (0–n) (15–n)
  | serv_15_30    : ∀n, Step (15–n) (30–n)
  | serv_30_40    : ∀n, Step (30–n) (40–n)
  | serv_40_game  : ∀n, n < 40 → Step (40–n) Score.gameServ
  | serv_40_adv   : Step (40–40) Score.advServ
  | serv_adv_40   : Step Score.advServ (40–40)
  | serv_adv_game : Step Score.advServ Score.gameServ
  | recv_0_15     : ∀n, Step (n–0) (n–15)
  | recv_15_30    : ∀n, Step (n–15) (n–30)
  | recv_30_40    : ∀n, Step (n–30) (n–40)
  | recv_40_game  : ∀n, n < 40 → Step (n–40) Score.gameRecv
  | recv_40_adv   : Step (40–40) Score.advRecv
  | recv_adv_40   : Step Score.advRecv (40–40)
  | recv_adv_game : Step Score.advRecv Score.gameRecv
infixr:45 " ⤳ " => Step

theorem nat_example (n : Nat) : n = 0 ∨ ∃ m, n = Nat.succ m :=
  by
    cases n
    { sorry }
    { sorry }

theorem no_Step_to_0_0 (s : Score) :
  ¬ s ⤳ 0–0 :=
  by
    intro h
    cases h

inductive Or' : Prop → Prop → Prop where
  | inl : a → Or' a b

-- inductive Or' (a b : Prop) : Prop where
--   | inl : a → Or' a b

opaque p : Prop
opaque q : Prop

axiom hp : p
axiom hq : q

def hpq : Prop := p ∨ q
def hpq' : Prop := Or p q
def hpq'' : Prop := Or' p q
#check hpq
#check hpq'
#check hpq''
def pq : p ∨ q := Or.inl hp
def pq' : Or p q := Or.inl hp
def pq'' : Or' p q  := Or'.inl hp
#check pq
#check pq'
#check pq''
