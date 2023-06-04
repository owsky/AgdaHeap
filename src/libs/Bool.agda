module libs.Bool where
  data Bool : Set where
    true  : Bool
    false : Bool

  _&&_ : Bool -> Bool -> Bool
  true  && b = b
  false && b = false

  _||_ : Bool -> Bool -> Bool
  true  || b = true
  false || b = b

  ! : Bool -> Bool
  ! true = false
  ! false = true