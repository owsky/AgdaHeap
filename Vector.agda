open import Nat
open import Fin
open import IfThenElse
open import Bool
module Vector where
  
  data Vector (A : Set) : ℕ → Set where
    []  : Vector A zero
    _∷_ : {n : ℕ} → A → Vector A n → Vector A (succ n)

  infixr 5 _∷_

  _++_ : {n m : ℕ} {A : Set} → Vector A n → Vector A m → Vector A (n + m)
  [] ++ v2 = v2
  (x ∷ xs) ++ v2 = x ∷ (xs ++ v2)

  infixr 5 _++_

  _[_] : {n : ℕ} {A : Set} → Vector A n → Fin n → A
  (v ∷ vs) [ zer ] = v
  (v ∷ vs) [ suc n ] = vs [ n ]

  mapi : {n : ℕ} {A B : Set} → Vector A n → (Fin n → A → B) → Vector B n
  mapi [] f = []
  mapi (x ∷ xs) f = (f zer x) ∷ mapi xs λ i → f (suc i)

  swap : {n : ℕ} {A : Set} → Vector A n → Fin n → Fin n → Vector A n
  swap (x ∷ xs) i j = mapi (x ∷ xs) λ curr → if curr =? i then (λ el → (x ∷ xs) [ j ]) else (if curr =? j then (λ el → (x ∷ xs) [ i ]) else λ el → el)
