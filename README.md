# AgdaHeap
AgdaHeap was a project that I worked on for the [Type Theory](https://en.didattica.unipd.it/off/2022/LM/SC/SC2598/000ZZ/SCQ1098250/N0) course at the University of Padua.  

## API
As the name suggests it is an implementation of the Heap data structure with methods:
  - new-heap : Heap
  - insert : A → Heap → Heap
  - peek-first : Heap → Maybe A
  - remove-first : Heap → Heap
  - from-list : List → Heap
  - to-list : Heap → List

## Correctness

The implementation is admittedly inefficient because the purpose of the project was not to create an actual module to be used in a production environment, but rather to implement a minimilastic API for heaps and subsequently proving its correctness.  

Within the Heap module, there's an embedded submodule called Correctness which contains proofs of correctness for each of the methods exposed by the API. Internally it's totally possible to use the data constructors of Heap' to create a non-valid Heap, which is why the Heap data type is declared as private only and inaccessible from outside the module. This has been achieved through a dummy Heap record type which contains the actual Heap' data structure as a field.

## Module Parameters

The Heap module requires the following parameters:
  - (A : Set)  
     Type that will be contained within the Heap  
     
  - (_≤_ : A → A → Set)  
      Ordering function  
      
  - (cmp : (x y : A) → (x ≤ y) ⊎ (y ≤ x))  
      Comparing function  
      
  - (trans≤ : {x y z : A} → x ≤ y → y ≤ z → x ≤ z)  
      Transitivity proof of the ordering function  
      
  - (refl≤ : {x : A} → x ≤ x)  
      Reflexivity proof of the ordering function  
      
  - (antisym≤ : {x y : A} → x ≤ y → y ≤ x → x ≡ y)  
      Antisymmetry proof of the ordering function  
  
## Internal definitions
Within the src directory there is a libs directory which contains all the functions and types that I needed to complete the project. All of them can be replaced by the [Agda Standard Library](https://github.com/agda/agda-stdlib) with very minor adjustments. For the sake of the project I didn't want to rely on the stdlib.
  
  
  
