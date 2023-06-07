module libs.Sets where
  data _⊎_ (A B : Set) : Set where
    left  : A → A ⊎ B
    right : B → A ⊎ B

  data _×_ (A B : Set) : Set where
    _,_ : A → B → A × B

  fst : {A B : Set} → A × B → A
  fst (a , b) = a

  snd : {A B : Set} → A × B → B
  snd (a , b) = b
  