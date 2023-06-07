open import libs.Bool
open import libs.List
open import libs.Maybe
open import libs.Equality
open import libs.Sets

module MinHeap
  (A : Set)
  (_≤_ : A → A → Set)
  (trans≤ : {x y z : A} → x ≤ y → y ≤ z → x ≤ z)
  (refl≤ : {x : A} → x ≤ x)
  (cmp : (x y : A) → (x ≤ y) ⊎ (y ≤ x))
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
  insert x (heap (node y l r)) with cmp x y
  ... | left  x≤y = heap (node x l ((Heap.value (insert y (heap r)))))
  ... | right y≤x = heap (node y (Heap.value (insert x (heap l))) r)

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
      ≤-maybe-one : (x : A) → just x ≤-maybe nothing
      ≤-maybe-both : (x : A) → (y : A) → x ≤ y → just x ≤-maybe just y

    trans≤-maybe : {x y z : Maybe A} → x ≤-maybe y → y ≤-maybe z → x ≤-maybe z
    trans≤-maybe (≤-maybe-one x) ()
    trans≤-maybe (≤-maybe-both x y x₁) (≤-maybe-one .y) = ≤-maybe-one x
    trans≤-maybe (≤-maybe-both x y x≤y) (≤-maybe-both y z y≤z) = ≤-maybe-both x z (trans≤ x≤y y≤z)

    data IsHeap : Heap → Set where
      is-heap-empty : IsHeap new-heap
      is-heap-node : (x : A) → (l r : Heap') → IsHeap (heap l) → IsHeap (heap r) → just x ≤-maybe (peek-min (heap l)) → just x ≤-maybe (peek-min (heap r)) → IsHeap (heap (node x l r))

    insert-lemma₀ : {x y : A} {h : Heap} → x ≤ y → just y ≤-maybe peek-min h → just x ≤-maybe peek-min h
    insert-lemma₀ {x} {y} {h} x≤y y≤-maybe with peek-min h
    ... | nothing = ≤-maybe-one x
    insert-lemma₀ {x} {y} {h} x≤y (≤-maybe-both .y .z x₁) | just z = ≤-maybe-both x z (trans≤ x≤y x₁)
    
    -- insert-result-lemma : (x : A) → (h : Heap) → IsHeap h → (peek-min (insert x h) ≡ just x) ⊎ (peek-min (insert x h) ≡ peek-min h)
    -- insert-result-lemma x h h-is-heap with peek-min h
    -- ... | nothing = {!   !}
    -- ... | just root with cmp x root
    -- ... | comp with peek-min (insert x h)
    -- insert-result-lemma x h h-is-heap | just root | left x₁ | nothing = {!   !}
    -- insert-result-lemma x h h-is-heap | just root | left x₁ | just x₂ = {!   !}
    -- insert-result-lemma x h h-is-heap | just root | right x₁ | nothing = {!   !}
    -- insert-result-lemma x h h-is-heap | just root | right x₁ | just x₂ = {!   !}

    insert-lemma₁ : {y : A} {h : Heap} → just y ≤-maybe peek-min h → just y ≤-maybe peek-min (insert y h)
    insert-lemma₁ {y} {h} y-≤-maybe with peek-min h
    ... | nothing = {!   !}
    ... | just root with cmp y root
    ... | comp with insert y h
    ... | ins with peek-min ins
    insert-lemma₁ {y} {h} y-≤-maybe | just root | left y≤root | heap value | nothing = ≤-maybe-one y
    insert-lemma₁ {y} {h} y-≤-maybe | just root | left y≤root | heap empty | just pm-ins = {!   !}
    insert-lemma₁ {y} {h} y-≤-maybe | just root | left y≤root | heap (node x value value₁) | just pm-ins = {!   !}
    insert-lemma₁ {y} {h} y-≤-maybe | just root | right root≤y | heap value | nothing = {!   !}
    insert-lemma₁ {y} {h} y-≤-maybe | just root | right root≤y | heap value | just pm-ins = {!   !}
    -- ... | left y≤root = insert-lemma₀ y≤root {!  y-≤-maybe !}
    -- ... | right root≤y = insert-lemma₀ (refl≤ {y}) {!   !}

    insert-lemma₂ : {x y : A} {h : Heap} → y ≤ x → just y ≤-maybe peek-min h → just y ≤-maybe peek-min (insert x h)
    insert-lemma₂ {x} {y} {h} y≤x just-y-≤-maybe-peek-min-h = {!   !}

    insert-proof : (x : A) → (h : Heap) → IsHeap h → IsHeap (insert x h)
    insert-proof x (heap empty) is-heap-empty = is-heap-node x empty empty is-heap-empty is-heap-empty (≤-maybe-one x) (≤-maybe-one x)
    insert-proof x (heap (node y l r)) (is-heap-node y l r l-is-heap r-is-heap y≤min-l y≤min-r) with cmp x y
    ... | left x≤y = is-heap-node x l (Heap.value ( insert y (heap r))) l-is-heap (insert-proof y (heap r) r-is-heap) (insert-lemma₀ x≤y y≤min-l) (insert-lemma₀ x≤y (insert-lemma₁ y≤min-r))
    ... | right y≤x = is-heap-node y (Heap.value (insert x (heap l))) r (insert-proof x (heap l) l-is-heap) r-is-heap (insert-lemma₂ y≤x y≤min-l) y≤min-r
    





-- EXPERIMENT

    -- insert-proof : (x : A) → (h : Heap) → IsHeap h → IsHeap (fst (insert x h))
    -- insert-proof x (heap empty) h-is-heap = is-heap-node x empty empty h-is-heap h-is-heap (≤-maybe-one x) (≤-maybe-one x)
    -- insert-proof x (heap (node root l r)) h-is-heap with cmp x root | insert x (heap (node root l r))
    -- ... | left x≤root | heap empty , x = is-heap-empty
    -- ... | left x≤root | heap (node x₁ value value₁) , x = {!   !}
    -- ... | right root≤x | nh , root = {!   !}





















    -- data IsMin : A → Heap → Set where
    --   is-min-empty : (x : A) → IsMin x new-heap
    --   is-min-node : (x y : A) → (l : Heap') → (r : Heap') → x ≤ y → IsMin x (heap l) → IsMin x (heap (node y l r))

    -- insert-lemma₃ : {x y : A} {h : Heap} → x ≤ y → IsMin y h → IsMin x h
    -- insert-lemma₃ {x} {y} {.new-heap} x≤y (is-min-empty .y) = is-min-empty x
    -- insert-lemma₃ {x} {y} {.(heap (node y₁ l r))} x≤y (is-min-node .y y₁ l r x₁ is-min-y-h) =
    --   let insert-lemma₃-helper : {h' : Heap} → IsMin y h' → IsMin x h'
    --       insert-lemma₃-helper is-min-y-h' = insert-lemma₃ x≤y is-min-y-h'
    --   in is-min-node x y₁ l r (trans≤ x≤y x₁) (insert-lemma₃-helper is-min-y-h)
    
    -- is-min-trans : {x y : A} {h : Heap} → x ≤ y → IsMin y h → IsMin x h
    -- is-min-trans {x} {y} {heap empty} x≤y is-min-y-h = is-min-empty x
    -- is-min-trans {x} {y} {heap (node x₁ value value₁)} x≤y (is-min-node .y .x₁ .value .value₁ x₂ is-min-y-h) = is-min-node x x₁ value value₁ (trans≤ x≤y x₂) (insert-lemma₃ x≤y is-min-y-h)

    -- data IsHeap : Heap → Set where
    --   is-heap-empty : IsHeap (heap empty)
    --   is-heap-node : (x : A) → (l r : Heap') → IsHeap (heap l) → IsHeap (heap r) → IsMin x (heap l) → IsMin x (heap r) → IsHeap (heap (node x l r))

    -- is-min-insert-refl : {x : A} {h : Heap} → IsMin x h → x ≤ x → IsMin x (insert x h)
    -- is-min-insert-refl {x} {heap empty} is-min-x-h x≤x = is-min-node x x empty empty x≤x is-min-x-h
    -- is-min-insert-refl {x} {heap (node root l r)} (is-min-node .x .root .l .r x₁ is-min-x-h) x≤x with insert x (heap (node root l r))
    -- ... | heap empty = is-min-empty x
    -- ... | heap (node x₂ value value₁) = is-min-node x x₂ value value₁ {!   !} {!   !}

    -- insert-lemma₁ : {x y : A} {h : Heap} → x ≤ y → IsMin y h → IsMin x (insert y h)
    -- insert-lemma₁ x≤y is-min-y-h = {!   !}

    -- insert-lemma₂ : {x y : A} {h : Heap} → y ≤ x → IsMin y h → IsMin y (insert x h)
    -- insert-lemma₂ {x} {y} {h} y≤x is-min-y-h with insert x h
    -- ... | heap empty = is-min-empty y
    -- ... | heap (node root l r) with cmp x root
    -- ... | left x≤root = is-min-node y root l r (trans≤ y≤x x≤root) {!   !}
    -- ... | right root≤x = is-min-node y root l r {!   !} {!   !}

    -- insert-preserves-min-heap : (x : A) → (h : Heap) → IsHeap h → IsHeap (insert x h)
    -- insert-preserves-min-heap x (heap empty) is-heap-empty = is-heap-node x empty empty is-heap-empty is-heap-empty (is-min-empty x) (is-min-empty x)
    -- insert-preserves-min-heap x (heap (node y l r)) (is-heap-node y l r is-heap-l is-heap-r is-min-l is-min-r) with cmp x y
    -- ... | left x≤y = is-heap-node x l (Heap.value (insert y (heap r))) is-heap-l (insert-preserves-min-heap y (heap r) is-heap-r) (is-min-trans x≤y is-min-l) (insert-lemma₁ x≤y is-min-r)
    -- ... | right y≤x = is-heap-node y (Heap.value (insert x (heap l))) r (insert-preserves-min-heap x (heap l) is-heap-l) is-heap-r (insert-lemma₂ y≤x is-min-l) is-min-r