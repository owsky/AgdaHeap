module libs.List (A : Set) where
  data List : Set where
    [] : List
    _∷_ : A -> List -> List
  infixr 5 _∷_

  _++_ : List -> List -> List
  [] ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)
  infixr 5 _++_