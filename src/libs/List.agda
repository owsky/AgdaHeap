module libs.List (A : Set) where
  data List : Set where
    [] : List
    _∷_ : A -> List -> List
  infixr 5 _∷_