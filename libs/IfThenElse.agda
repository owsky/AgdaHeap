module libs.IfThenElse where
  open import libs.Bool
  
  if_then_else_ : {A : Set} → Bool → A → A → A
  if true then x else y = x
  if false then x else y = y
  