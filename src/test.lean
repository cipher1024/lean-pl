
import spec

open separation separation.hProp

variables {value : Type}

example {p q a b : hProp value}
  (h₀ : p =*> a)
  (h₁ : b =*> q)
  (h₂ : p =*> b)
  (h₃ : p =*> q)
  (h₄ : a =*> q)
  (h₅ : a =*> b)
  (h₆ : a =*> b ⊛ q)
  (h₇ : p =*> emp) :
  p ⊛ a =*> q ⊛ b :=
begin
  duplicate_goal 9,
  { s_apply h₀, admit },
  { s_apply h₁, admit },
  { s_apply h₂, admit },
  { s_apply h₃, admit },
  { s_apply h₄, admit },
  { s_apply h₅, admit },
  { s_apply h₆, s_apply h₇ },
  { s_assumptions, admit },
  { s_assumption, admit },
  s_show p =*> b,
  { assumption, },
  { assumption, },
end
