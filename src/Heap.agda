open import libs.List
open import libs.Maybe
open import libs.Sets
open import libs.Equality

module Heap
  (A : Set)
  (_≤_ : A → A → Set)
  (trans≤ : {x y z : A} → x ≤ y → y ≤ z → x ≤ z)
  (refl≤ : {x : A} → x ≤ x)
  (cmp : (x y : A) → (x ≤ y) ⊎ (y ≤ x))
  where

  data Heap : Set where
    empty : Heap
    node : A → Heap → Heap → Heap

  insert : A → Heap → Heap
  insert x empty = node x empty empty
  insert x (node y l r) with cmp x y
  ... | left  x≤y = node x l (insert y r)
  ... | right y≤x = node y (insert x l) r

  from-list : List A → Heap
  from-list [] = empty
  from-list (x ∷ xs) = insert x (from-list xs)

  peek-min : Heap → Maybe A
  peek-min empty = nothing
  peek-min (node x l r) = just x

  to-list : Heap → List A
  to-list empty = []
  to-list (node x l r) = x ∷ (to-list l) ++ (to-list r)

  remove-min : Heap → Heap
  remove-min empty = empty
  remove-min (node x l r) = from-list (to-list l ++ to-list r) 

  module Correctness where
    data _≤-maybe_ : Maybe A → Maybe A → Set where
      ≤-maybe-nothing : nothing ≤-maybe nothing
      ≤-maybe-one : {x : A} → just x ≤-maybe nothing
      ≤-maybe-both : {x y : A} → x ≤ y → just x ≤-maybe just y

    trans≤-maybe : {x y z : Maybe A} → x ≤-maybe y → y ≤-maybe z → x ≤-maybe z
    trans≤-maybe ≤-maybe-nothing ≤-maybe-nothing = ≤-maybe-nothing
    trans≤-maybe ≤-maybe-one ≤-maybe-nothing = ≤-maybe-one
    trans≤-maybe (≤-maybe-both x) ≤-maybe-one = ≤-maybe-one
    trans≤-maybe (≤-maybe-both x) (≤-maybe-both x₁) = ≤-maybe-both (trans≤ x x₁)

    refl≤-maybe : {x : Maybe A} → x ≤-maybe x
    refl≤-maybe {nothing} = ≤-maybe-nothing
    refl≤-maybe {just x} = ≤-maybe-both refl≤

    data IsHeap : Heap → Set where
      is-heap-empty : IsHeap empty
      is-heap-node : (x : A) → (l r : Heap) → IsHeap l → IsHeap r → just x ≤-maybe (peek-min l) → just x ≤-maybe (peek-min r) → IsHeap (node x l r)

    insert-lemma₀ : {x y : A} {h : Heap} → x ≤ y → just y ≤-maybe peek-min h → just x ≤-maybe peek-min h
    insert-lemma₀ {x} {y} {h} x≤y y≤-maybe with peek-min h
    ... | nothing = ≤-maybe-one
    insert-lemma₀ {x} {y} {h} x≤y (≤-maybe-both x₁) | just z = ≤-maybe-both (trans≤ x≤y x₁)

    insert-lemma₁ : {y : A} {h : Heap} → just y ≤-maybe peek-min h → just y ≤-maybe peek-min (insert y h)
    insert-lemma₁ {y} {empty} y≤min-empty = ≤-maybe-both refl≤
    insert-lemma₁ {y} {node root l r} y≤min-node with cmp y root
    ... | left y≤root = ≤-maybe-both refl≤
    ... | right root≤y = y≤min-node

    insert-lemma₂ : {x y : A} {h : Heap} → y ≤ x → just y ≤-maybe peek-min h → just y ≤-maybe peek-min (insert x h)
    insert-lemma₂ {x} {y} {empty} y≤x just-y-≤-maybe-peek-min-h = ≤-maybe-both y≤x
    insert-lemma₂ {x} {y} {node root l r} y≤x (≤-maybe-both x₁) with cmp x root
    ... | left x≤root = ≤-maybe-both y≤x
    ... | right root≤x = ≤-maybe-both x₁

    insert-proof : (x : A) → (h : Heap) → IsHeap h → IsHeap(insert x h)
    insert-proof x empty h-is-heap = is-heap-node x empty empty h-is-heap h-is-heap (≤-maybe-one) (≤-maybe-one)
    insert-proof x (node root l r) (is-heap-node .root .l .r h-is-heap h-is-heap₁ root-≤-min-l root-≤-min-r) with cmp x root
    ... | left x≤root = is-heap-node x l (insert root r) h-is-heap (insert-proof root r h-is-heap₁) (insert-lemma₀ x≤root root-≤-min-l) ((insert-lemma₀ x≤root (insert-lemma₁ root-≤-min-r)))
    ... | right root≤x = is-heap-node root (insert x l) r (insert-proof x l h-is-heap) h-is-heap₁ (insert-lemma₂ root≤x root-≤-min-l) root-≤-min-r

    from-list-proof : (xs : List A) → IsHeap (from-list xs)
    from-list-proof [] = is-heap-empty
    from-list-proof (x ∷ xs) = insert-proof x (from-list xs) (from-list-proof xs)

    peek-min-proof : (h : Heap) → IsHeap h →  {!   !}
    peek-min-proof = {!   !}
