module libs.Nat where
  open import libs.Bool
  open import libs.Equality
  open import libs.Sets

  data ℕ : Set where
      zero  : ℕ
      succ  : ℕ → ℕ

  {-# BUILTIN NATURAL ℕ #-}

  data _<_ : ℕ → ℕ → Set where
    base  : {n : ℕ}     → n < succ n
    step  : {a b : ℕ}   → a < b → a < succ b

  data _≤_ : ℕ → ℕ → Set where
    base-≤ : (n : ℕ) -> n ≤ n
    step-≤ : (n m : ℕ) -> n ≤ m -> n ≤ succ m

  _<?_ : ℕ → ℕ → Bool
  zero     <? zero     = false
  zero     <? (succ b) = true
  (succ a) <? zero     = false
  (succ a) <? (succ b) = a <? b

  _≤?_ : ℕ → ℕ → Bool
  zero     ≤? zero     = true
  zero     ≤? (succ b) = true
  (succ a) ≤? zero     = false
  (succ a) ≤? (succ b) = a ≤? b
  
  lemma-<-zero : {n : ℕ} → zero < succ n
  lemma-<-zero {zero} = base
  lemma-<-zero {succ n} = step lemma-<-zero

  lemma-<-pred : {m n : ℕ} → succ m < n → m < n
  lemma-<-pred {m} {n} (base) = step base
  lemma-<-pred {m} {n} (step p) = step (lemma-<-pred p)

  lemma-<-succ : {n : ℕ} → n < succ n
  lemma-<-succ = base
      
  data Positive : ℕ -> Set where
    base-positive : Positive (succ zero)
    step-positive : {n : ℕ} -> Positive n -> Positive (succ n)
  
  pred-positive : {n : ℕ} → Positive (succ (succ n)) → Positive (succ n)
  pred-positive (step-positive p) = p
  
  _+_ : ℕ → ℕ → ℕ
  zero  + m = m
  succ n + m = succ (n + m)

  _-_ : ℕ → ℕ → ℕ
  zero - _ = zero
  succ a - zero = succ a
  succ a - succ b = a - b

  _∙_ : ℕ → ℕ → ℕ
  zero   ∙ b = zero
  succ a ∙ b = b + (a ∙ b)
  
  infixl 6 _+_
  infixl 7 _∙_

  half : ℕ → ℕ
  half zero            = zero
  half (succ zero)     = zero
  half (succ (succ n)) = succ (half n)

  lemma-+-zero : (a : ℕ) → (a + zero) ≡ a
  lemma-+-zero zero     = refl
  lemma-+-zero (succ a) = cong succ (lemma-+-zero a)

  lemma-+-succ : (a b : ℕ) → (a + succ b) ≡ succ (a + b)
  lemma-+-succ zero     b = refl
  lemma-+-succ (succ a) b = cong succ (lemma-+-succ a b)