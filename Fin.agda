module Fin where
  open import Nat
  open import Bool

  data Fin : ℕ → Set where
    zer : {n : ℕ} → Fin (succ n)
    suc : {n : ℕ} (i : Fin n) → Fin (succ n)

  _=?_ : {n : ℕ} → Fin n → Fin n → Bool
  zer =? zer = true
  zer =? suc b = false
  suc a =? zer = false
  suc a =? suc b = a =? b