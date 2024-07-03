def cmps {α β γ : Type} (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

def double (x : Nat) := 2*x
def triple (x : Nat) := 3*x

#eval cmps double triple 2

variable {α β γ : Type}
variable (g : β → γ) (f : α → β) (h : α → α)
variable (x : α)

def compose := g (f x)
def doTwice := h (h x)
def doThrice := h (h (h x))

#print compose
#print doTwice
#print doThrice
#eval compose double triple 2
#eval cmps double triple 2
