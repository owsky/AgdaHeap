module Nat where
  open import Bool

  data ℕ : Set where
      zero  : ℕ
      succ  : ℕ → ℕ

  _+_ : ℕ → ℕ → ℕ
  zero  + m = m
  succ n + m = succ (n + m)

  data Positive : ℕ -> Set where
    one : Positive (succ zero)
    succ : (n : ℕ) -> Positive n -> Positive (succ n)

  data _≤_ : ℕ → ℕ → Set where
    base : (n : ℕ) -> n ≤ n
    step : (n m : ℕ) -> n ≤ m -> n ≤ succ m