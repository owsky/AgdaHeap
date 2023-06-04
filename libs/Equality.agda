module libs.Equality {X : Set} where
  data _≡_ : X → X → Set where
    refl : {a : X} → a ≡ a