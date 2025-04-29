open import libs.Maybe
open import libs.Sets
open import libs.Equality
open import libs.Bool
open import libs.Nat
open import libs.Exp

-- the module requires that the data type carries a total order
module Heap
  (A : Set)
  (_≤_ : A → A → Set)
  (cmp : (x y : A) → (x ≤ y) ⊎ (y ≤ x))
  (trans≤ : {x y z : A} → x ≤ y → y ≤ z → x ≤ z)
  (refl≤ : {x : A} → x ≤ x)
  (antisym≤ : {x y : A} → x ≤ y → y ≤ x → x ≡ y)
  where
  open import libs.List A

  record Heap : Set

  -- encapsulated data constructors so the data structure can only be
  -- interacted with through the exposed API, which was verified for
  -- correctness
  private
    data Heap' : Set where
      empty : Heap'
      node : A → Heap' → Heap' → Heap'

  record Heap where
    constructor heap
    pattern
    field value : Heap'

  new-heap : Heap
  new-heap = heap empty

  -- inserts the item into the given heap
  insert : A → Heap → Heap
  insert x (heap empty) = heap empty
  insert x (heap (node root l r)) with cmp x root
  ... | left  _ = heap (node x l (Heap.value (insert root (heap r))))
  ... | right _ = heap (node root (Heap.value (insert x (heap l))) r)

  -- constructs a new heap from the given list
  from-list : List → Heap
  from-list []       = heap empty
  from-list (x ∷ xs) = insert x (from-list xs)

  -- returns the smallest item in the heap
  peek-first : Heap → Maybe A
  peek-first (heap empty)           = nothing
  peek-first (heap (node root _ _)) = just root

  -- converts the heap into a list
  to-list : Heap → List
  to-list (heap empty)           = []
  to-list (heap (node root l r)) = root ∷ (to-list (heap l)) ++ (to-list (heap r))

  -- removes the smallest item in the heap
  -- inefficient implementation but correct implementation
  remove-first : Heap → Heap
  remove-first (heap empty)           = heap empty
  remove-first (heap (node root l r)) = from-list (to-list (heap l) ++ to-list (heap r))

  -- correctness by verification module
  module Correctness where
    -- data type which allows comparing Maybe types
    data _≤-maybe_ : Maybe A → Maybe A → Set where
      ≤-maybe-nothing  : nothing ≤-maybe nothing
      ≤-maybe-one      : {x : A} → just x ≤-maybe nothing
      ≤-maybe-both     : {x y : A} → x ≤ y → just x ≤-maybe just y

    -- witness of maybe comparisons being transitive
    trans≤-maybe : {x y z : Maybe A} → x ≤-maybe y → y ≤-maybe z → x ≤-maybe z
    trans≤-maybe ≤-maybe-nothing   ≤-maybe-nothing      = ≤-maybe-nothing
    trans≤-maybe ≤-maybe-one       ≤-maybe-nothing      = ≤-maybe-one
    trans≤-maybe (≤-maybe-both x≤y)  ≤-maybe-one        = ≤-maybe-one
    trans≤-maybe (≤-maybe-both x≤y) (≤-maybe-both y≤z)  = ≤-maybe-both (trans≤ x≤y y≤z)

    -- witness of maybe comparison being reflexive
    refl≤-maybe : {x : Maybe A} → x ≤-maybe x
    refl≤-maybe {nothing} = ≤-maybe-nothing
    refl≤-maybe {just _}  = ≤-maybe-both refl≤

    -- data type which verifies the correct heap structure, i.e., for each node x, its key is smaller
    -- than its childrens'
    data IsHeap : Heap' → Set where
      is-heap-empty : IsHeap empty
      is-heap-node  : 
        (x : A) → 
        (l r : Heap') → 
        IsHeap l → 
        IsHeap r → 
        just x ≤-maybe (peek-first (heap l)) → 
        just x ≤-maybe (peek-first (heap r)) → 
        IsHeap (node x l r)

    -- witness that a heap created through new-heap is a proper heap
    new-heap-proof : IsHeap (Heap.value new-heap)
    new-heap-proof = is-heap-empty

    -- auxiliary lemmas for insertion witness

    insert-lemma₀ : {x y : A} {h : Heap} → x ≤ y → just y ≤-maybe peek-first h → just x ≤-maybe peek-first h
    insert-lemma₀ {h = h} x≤y y≤-maybe with peek-first h
    insert-lemma₀ {h = h} x≤y y≤-maybe           | nothing = ≤-maybe-one
    insert-lemma₀ {h = h} x≤y (≤-maybe-both y≤z) | just z  = ≤-maybe-both (trans≤ x≤y y≤z)

    insert-lemma₁ : {y : A} {h : Heap} → just y ≤-maybe peek-first h → just y ≤-maybe peek-first (insert y h)
    insert-lemma₁ {y} {heap empty} y≤first-empty = y≤first-empty
    insert-lemma₁ {y} {heap (node root _ _)} y≤first-node with cmp y root
    ... | left  y≤root  = ≤-maybe-both refl≤
    ... | right root≤y  = y≤first-node

    insert-lemma₂ : {x y : A} {h : Heap} → y ≤ x → just y ≤-maybe peek-first h → just y ≤-maybe peek-first (insert x h)
    insert-lemma₂ {x} {h = heap empty} y≤x just-y-≤-maybe-peek-first-h = just-y-≤-maybe-peek-first-h
    insert-lemma₂ {x} {h = heap (node root l r)} y≤x (≤-maybe-both y≤root) with cmp x root
    ... | left  x≤root = ≤-maybe-both y≤x
    ... | right root≤x = ≤-maybe-both y≤root

    -- witness that the heap resulting from inserting a value into a heap is still a proper heap
    insert-proof : (x : A) → (h : Heap) → IsHeap (Heap.value h) → IsHeap(Heap.value (insert x h))
    insert-proof x (heap empty) h-is-heap = h-is-heap
    insert-proof x (heap (node root l r)) (is-heap-node root l r l-h-is-heap r-h-is-heap root-≤-first-l root-≤-first-r) with cmp x root
    ... | left  x≤root = is-heap-node x l (Heap.value (insert root (heap r))) l-h-is-heap (insert-proof root (heap r) r-h-is-heap) (insert-lemma₀ x≤root root-≤-first-l) ((insert-lemma₀ x≤root (insert-lemma₁ root-≤-first-r)))
    ... | right root≤x = is-heap-node root (Heap.value (insert x (heap l))) r (insert-proof x (heap l) l-h-is-heap) r-h-is-heap (insert-lemma₂ root≤x root-≤-first-l) root-≤-first-r

    -- witness that creating a heap using the from-list constructor is a proper heap
    from-list-proof : (xs : List) → IsHeap (Heap.value (from-list xs))
    from-list-proof []       = is-heap-empty
    from-list-proof (x ∷ xs) = insert-proof x (from-list xs) (from-list-proof xs)

    ins-first-lemma : (x root : A) → (l r : Heap) → x ≤ root → peek-first (insert x (heap (node root (Heap.value l) (Heap.value r)))) ≡ just x
    ins-first-lemma x root _ _ x≤root with cmp x root
    ... | left  x≤root = refl
    ... | right root≤x = symm (cong just (antisym≤ x≤root root≤x))

    -- witness that if an item is inserted into a heap, and the item is smaller than all the other heap items, then peek-first returns
    -- the same item
    peek-first-proof : {x root : A} → (l r : Heap) → x ≤ root → peek-first (insert x (heap (node root (Heap.value l) (Heap.value r)))) ≡ just x
    peek-first-proof {x} {root} l r x≤root with ins-first-lemma x root l r
    ... | ins = ins x≤root

    -- witness that removing the smallest item from a heap produces a valid heap
    remove-first-proof : (h : Heap) → IsHeap (Heap.value h) → IsHeap (Heap.value (remove-first h))
    remove-first-proof (heap empty) is-heap = is-heap
    remove-first-proof (heap (node root l r)) _ with (to-list (heap l) ++ to-list (heap r))
    ... | tl = from-list-proof tl

    -- type which defines membership to lists
    _∈_ : A → List → Set
    x ∈ []       = ⊥
    x ∈ (y ∷ xs) = (x ≡ y) ⊎ (x ∈ xs)

    -- data type which defines that a heap and its flattened list representation have the same elements
    data SameElements : Heap → Set where
      same-empty    : SameElements (heap empty)
      same-elements : 
        (root : A) → 
        (l r : Heap) → 
        (root ∈ to-list (heap (node root (Heap.value l) (Heap.value r)))) → 
        SameElements l → 
        SameElements r → 
        SameElements (heap (node root (Heap.value l) (Heap.value r)))

    -- witness that the list produced by the to-list method contains the same items as the input heap
    to-list-proof : (root : A) → (l r : Heap) → IsHeap (node root (Heap.value l) (Heap.value r))  → SameElements (heap (node root (Heap.value l) (Heap.value r)))
    to-list-proof root (heap empty)                 (heap empty)                        _                                                                                              = same-elements root (heap empty) (heap empty) (left refl) same-empty same-empty
    to-list-proof root (heap empty)                 (heap (node r-root r-l r-r))        (is-heap-node root empty (node r-root r-l r-r) _ r-is-heap _ _)                                = same-elements root (heap empty) (heap (node r-root r-l r-r)) (left refl) same-empty (to-list-proof r-root (heap r-l) (heap r-r) r-is-heap)
    to-list-proof root (heap (node l-root l-l l-r)) (heap empty)                        (is-heap-node root (node l-root l-l l-r) empty l-is-heap _ _ _)                                = same-elements root (heap (node l-root l-l l-r)) (heap empty) (left refl) (to-list-proof l-root (heap l-l) (heap l-r) l-is-heap) same-empty
    to-list-proof root (heap (node l-root l-l l-r)) (heap (node r-root r-left r-right)) (is-heap-node root (node l-root l-l l-r) (node r-root r-left r-right) l-is-heap r-is-heap _ _) = same-elements root (heap (node l-root l-l l-r)) (heap (node r-root r-left r-right)) (left refl) (to-list-proof l-root (heap l-l) (heap l-r) l-is-heap) (to-list-proof r-root (heap r-left) (heap r-right) r-is-heap)