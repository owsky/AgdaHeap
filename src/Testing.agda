{-# OPTIONS --allow-unsolved-metas #-}
module Testing where
  open import libs.Nat
  open import libs.List
  open import MinHeap ℕ _<?_ _≤?_ _≤_
  open import libs.Maybe

  one : ℕ
  one = succ zero

  two : ℕ
  two = succ one

  three : ℕ
  three = succ two

  four : ℕ
  four = succ three

  l : List ℕ
  l = three ∷ zero ∷ four ∷ one ∷ two ∷ []
  h : Heap
  h = from-list l

  h-min : Maybe ℕ
  h-min = peek-min h

  h-popped : Heap
  h-popped = remove-min h

  h2 : Heap
  h2 = new-heap

  h3 : Heap
  h3 = insert three h2
