module libs.Exp where
  data ⊥ : Set where
  
  ⊥-elim : ∀ {n} {x : Set n} → ⊥ → x
  ⊥-elim ()