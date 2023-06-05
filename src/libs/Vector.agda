open import libs.Nat
open import libs.Fin
open import libs.IfThenElse
open import libs.Bool
module libs.Vector where
  
  data Vector (A : Set) : ℕ → Set where
    []  : Vector A zero
    _∷_ : {n : ℕ} → A → Vector A n → Vector A (succ n)

  infixr 5 _∷_

  snoc : {n : ℕ} {A : Set} → A → Vector A n → Vector A (succ n)
  snoc x [] = x ∷ []
  snoc x (y ∷ ys) = y ∷ (snoc x ys)

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
