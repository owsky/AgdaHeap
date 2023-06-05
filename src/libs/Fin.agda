module libs.Fin where
  open import libs.Nat
  open import libs.Bool
  open import libs.Equality

  data Fin : ℕ → Set where
    zer : {n : ℕ} → Fin (succ n)
    suc : {n : ℕ} → Fin n → Fin (succ n)

  _=?_ : {n : ℕ} → Fin n → Fin n → Bool
  zer =? zer = true
  zer =? suc b = false
  suc a =? zer = false
  suc a =? suc b = a =? b

  _≠?_ : {n : ℕ} → Fin n → Fin n → Bool
  a ≠? b = ! (a =? b)

  from-ℕ : {n : ℕ} → (m : ℕ) → m < n → Fin n
  from-ℕ {zero} zero ()
  from-ℕ {zero} (succ m) ()
  from-ℕ {succ .zero} zero base = zer
  from-ℕ {succ n} zero (step m<n) = zer
  from-ℕ {succ .(succ m)} (succ m) base = zer
  from-ℕ {succ n} (succ m) (step m<n) = suc (from-ℕ m (lemma-<-pred m<n))

  to-ℕ : {n : ℕ} → Fin n → ℕ
  to-ℕ zer = zero
  to-ℕ (suc i) = succ (to-ℕ i)

  lemma-suc-zero : (n : ℕ) → Fin (n + succ zero) ≡ Fin (succ n)
  lemma-suc-zero zero = refl
  lemma-suc-zero (succ n) rewrite lemma-succ-zero n = refl
