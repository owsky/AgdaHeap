open import Vector
open import Nat
open import Fin

vec : Vector ℕ zero
vec = []

vec2 : Vector ℕ (succ (succ (succ (succ zero))))
vec2 = zero ∷ (succ zero) ∷ (succ (succ zero)) ∷ (succ (succ (succ zero))) ∷ []

vec2_sw : Vector ℕ (succ (succ (succ (succ zero))))
vec2_sw = swap vec2 zer (suc (suc (suc zer)))