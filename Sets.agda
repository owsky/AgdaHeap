module Sets where
  data _⊎_ (A B : Set) : Set where
    left  : A → A ⊎ B
    right : B → A ⊎ B