open import libs.Bool
open import libs.List
open import libs.Maybe

module MinHeap
  (A : Set)
  (_<?_ : A → A → Bool)
  (_≤?_ : A → A → Bool)
  (_≤_ : A → A → Set)
  where

  private
    data Heap' : Set where
      empty : Heap'
      node : A → Heap' → Heap' → Heap'

    to-list' : Heap' → List A
    to-list' empty = []
    to-list' (node x left right) = x ∷ (to-list' left) ++ (to-list' right) 

    peek-min' : Heap' → Maybe A
    peek-min' empty = nothing
    peek-min' (node x left right) = just x

  record Heap : Set where
    constructor heap
    field value : Heap'

  new-heap : Heap
  new-heap = heap empty

  insert : A → Heap → Heap
  insert x (heap empty) = heap (node x empty empty)
  insert x (heap (node y l r)) with x ≤? y
  ... | true = heap (node x (Heap.value (insert y (heap r))) l)
  ... | false = heap (node y (Heap.value (insert x (heap r))) l)

  from-list : List A → Heap
  from-list [] = new-heap
  from-list (x ∷ xs) = insert x (from-list xs)

  peek-min : Heap → Maybe A
  peek-min (heap empty) = nothing
  peek-min (heap (node x left right)) = just x

  to-list : Heap → List A
  to-list (heap h) = to-list' h

  remove-min : Heap → Heap
  remove-min (heap empty) = heap empty
  remove-min (heap (node x left right)) = from-list (to-list' left ++ to-list' right) 

  module Correctness where
    data MaybeComp : A → Maybe A → Set where
      none : (x : A) → MaybeComp x nothing
      some : (x : A) → (y : A) → x ≤ y → MaybeComp x (just y)

    data IsMin : A → Maybe A → Maybe A → Set where
      is-min : (x : A) → (y z : Maybe A) → MaybeComp x y → MaybeComp x z → IsMin x y z

    data IsHeap' : Heap' → Set where
      empty-heap : IsHeap' empty
      children-heap : (x : A) → (l r : Heap') → IsMin x (peek-min' l) (peek-min' r) → IsHeap' l → IsHeap' r → IsHeap' (node x l r)

    data IsHeap : Heap → Set where
      is-heap : (x : A) → (l r : Heap') → IsHeap' (node x l r) → IsHeap (heap (node x l r))

    -- data IsHeap : Heap → Set where
    --   empty-heap : IsHeap (heap empty)
    --   children-heap : (x : A) → (l r : Heap') → IsMin x (peek-min' l) (peek-min' r) → {! IsHeap l  !} → {! IsHeap r  !} → IsHeap (heap (node x l r))