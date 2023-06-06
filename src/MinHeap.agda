open import libs.Bool
open import libs.List
open import libs.Maybe
open import libs.Equality

module MinHeap
  (A : Set)
  (_<?_ : A → A → Bool)
  (_≤?_ : A → A → Bool)
  (_≤_ : A → A → Set)
  (≤-from-≤? : {a b : A} → (a ≤? b ≡ true) → a ≤ b)
  (trans≤ : {x y z : A} → x ≤ y → y ≤ z → x ≤ z)
  -- (cmp : (x y : A) → (x ≤ y) ⊎ (y ≤ x))
  where

  record Heap : Set

  private
    data Heap' : Set where
      empty : Heap'
      node : A → Heap' → Heap' → Heap'

    to-heap' : Heap → Heap'

  record Heap where
    constructor heap
    pattern
    field value : Heap'

  to-heap' (heap empty) = empty
  to-heap' (heap (node x l r)) = node x l r

  new-heap : Heap
  new-heap = heap empty

  insert : A → Heap → Heap
  insert x (heap empty) = heap (node x empty empty)
  insert x (heap (node y left right)) with x ≤? y
  ... | true = heap (node x left ((Heap.value (insert y (heap right)))))
  ... | false = heap (node y (Heap.value (insert x (heap left))) right)

  from-list : List A → Heap
  from-list [] = new-heap
  from-list (x ∷ xs) = insert x (from-list xs)

  peek-min : Heap → Maybe A
  peek-min (heap empty) = nothing
  peek-min (heap (node x l r)) = just x

  to-list : Heap → List A
  to-list (heap empty) = []
  to-list (heap (node x l r)) = x ∷ (to-list (heap l)) ++ (to-list (heap r))

  remove-min : Heap → Heap
  remove-min (heap empty) = heap empty
  remove-min (heap (node x l r)) = from-list (to-list (heap l) ++ to-list (heap r)) 

  module Correctness where
    data _≤-maybe_ : Maybe A → Maybe A → Set where
      ≤-maybe-one : (x : A) → (just x) ≤-maybe nothing
      ≤-maybe-both : (x : A) → (y : A) → x ≤ y → just x ≤-maybe (just y)

    trans≤-maybe : {x y z : Maybe A} → x ≤-maybe y → y ≤-maybe z → x ≤-maybe z
    trans≤-maybe (≤-maybe-one x) ()
    trans≤-maybe (≤-maybe-both x y x₁) (≤-maybe-one .y) = ≤-maybe-one x
    trans≤-maybe (≤-maybe-both x y x≤y) (≤-maybe-both y z y≤z) = ≤-maybe-both x z (trans≤ x≤y y≤z)

    data IsHeap : Heap → Set where
      is-heap-empty : IsHeap (heap empty) 
      is-heap-node : (x : A) → (l r : Heap') → IsHeap (heap l) → IsHeap (heap r) → just x ≤-maybe (peek-min (heap l)) → just x ≤-maybe (peek-min (heap r)) → IsHeap (heap (node x l r))
    
    data IsMin : Maybe A → Heap → Set where
      is-min-empty : IsMin nothing new-heap
      is-min-nodel : (x y : A) → (l : Heap') → (r : Heap') → x ≤ y → IsMin (just x) (heap l) → IsMin (just x) (heap (node y l r))
      is-min-noder : (x y : A) → (l : Heap') → (r : Heap') → x ≤ y → IsMin (just x) (heap r) → IsMin (just x) (heap (node y l r))

    new-heap-proof : IsHeap new-heap
    new-heap-proof = is-heap-empty

    insert-proof-lemma∅ : {x root : A} → x ≤? root ≡ true → just x ≤-maybe just root
    insert-proof-lemma∅ {x} {root} p = ≤-maybe-both x root (≤-from-≤? p)

    insert-proof-lemma₁ : {x root : A} {left : Heap'} → just root ≤-maybe peek-min (heap left) → x ≤? root ≡ true → just x ≤-maybe peek-min (heap left)
    insert-proof-lemma₁ p1 p2 = trans≤-maybe (insert-proof-lemma∅ p2) p1

    insert-proof-lemma₂ : {root : A} {right : Heap} → just root ≤-maybe peek-min right → just root ≤-maybe peek-min (insert root right)
    insert-proof-lemma₂ {root} {right} p with peek-min (insert root right) in eq
    ... | nothing = ≤-maybe-one root
    ... | just x = ≤-maybe-both root x {!   !}

    insert-proof-lemma₃ : {x y : A} → (x ≤? y) ≡ true → just x ≤-maybe just y
    insert-proof-lemma₃ {x} {y} p = ≤-maybe-both x y (≤-from-≤? p)

    insert-proof-lemma₄ : {x y : A} {left : Heap} → just y ≤-maybe peek-min left → just y ≤-maybe peek-min (insert x left)
    insert-proof-lemma₄ {x} {y} {left} p = {!   !}

    insert-proof : (x : A) → (h : Heap) → IsHeap h → IsHeap (insert x h)
    insert-proof x (heap empty) h-is-heap = is-heap-node x empty empty h-is-heap h-is-heap (≤-maybe-one x) (≤-maybe-one x)
    insert-proof x (heap (node y left right)) (is-heap-node .y .left .right h-is-heap h-is-heap₁ x₁ x₂) with x ≤? y in eq
    ... | true = is-heap-node x left (Heap.value (insert y (heap right))) h-is-heap (insert-proof y (heap right) h-is-heap₁) (insert-proof-lemma₁ x₁ eq) (trans≤-maybe (insert-proof-lemma₃ eq) (insert-proof-lemma₂ x₂)) -- (insert-proof-lemma₂ pz eq)
    ... | false = is-heap-node y (Heap.value (insert x (heap left))) right (insert-proof x (heap left) h-is-heap) h-is-heap₁ (insert-proof-lemma₄ x₁) x₂

    from-list-proof : (xs : List A) → IsHeap (from-list xs)
    from-list-proof [] = {!   !}
    from-list-proof (x ∷ xs) = {!   !}

    peek-min-proof : {x : A} → (h : Heap) → IsHeap h → IsMin (peek-min h) h
    peek-min-proof = {!   !}

    remove-min-proof : (h : Heap) → IsHeap h → IsHeap  (remove-min h)
    remove-min-proof = {!   !}   