open import libs.Bool
open import libs.List

module MinHeap
  (A : Set)
  (_<?_ : A → A → Bool)
  (_≤?_ : A → A → Bool)
  where

  private
    data Heap′ : Set where
      empty : Heap′
      node : A → Heap′ → Heap′ → Heap′

  record Heap : Set where
    constructor heap
    field value : Heap′

  new-heap : Heap
  new-heap = heap empty

  insert : A → Heap → Heap
  insert x (heap empty) = heap (node x empty empty)
  insert x (heap (node y l r)) with x ≤? y
  ... | true = heap (node x (Heap.value (insert y (heap r))) l)
  ... | false = heap (node y (Heap.value (insert x (heap r))) l)

  fromList : List A → Heap
  fromList [] = new-heap
  fromList (x ∷ xs) = insert x (fromList xs)