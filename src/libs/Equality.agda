open import Agda.Primitive

module libs.Equality where
  data _≡_ {n : Level} {A : Set n} (x : A) : A → Set n where
    refl : x ≡ x
    
  infixl 5 _≡_

  {-# BUILTIN EQUALITY _≡_ #-} 

  cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
  cong f refl = refl

  symm : {A : Set} {x y : A} → x ≡ y → y ≡ x
  symm refl = refl

  trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans refl refl = refl