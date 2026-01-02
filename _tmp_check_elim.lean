universe u
variable {α : Sort u} {p : α → Prop}

def choose' : (∃ a, p a) → α
  | ⟨a, _ha⟩ => a

#check choose'
