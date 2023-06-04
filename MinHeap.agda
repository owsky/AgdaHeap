open import Sets
open import Nat
open import Vector

module MinHeap
  (A : Set)
  (_≤_ : A → A → Set)
  (cmp : (x y : A) → (x ≤ y) ⊎ (y ≤ x)) where

  data Min-Heap (A : Set) : Set where
    []  : Min-Heap A
    insert : A → Min-Heap A → Min-Heap A
    delete : A → Min-Heap A → Min-Heap A

  heapify : {n : ℕ} → Vector A n → Vector A n
  heapify = {!   !}

  heap-insert : {n : ℕ} → A → Vector A n → Vector A (succ n)
  heap-insert x xs = heapify (x ∷ xs)
