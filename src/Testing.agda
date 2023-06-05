module Testing where
  open import libs.Nat
  open import libs.List
  open import MinHeap ℕ _<?_ _≤?_

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
  h = fromList l

  h2 : Heap
  h2 = new-heap

  h3 : Heap
  h3 = insert three h2

  -- h2 : Heap
  -- h2 = node three (node (succ three) empty empty) (node zero empty empty)