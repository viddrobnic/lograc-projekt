{-# OPTIONS --allow-unsolved-metas #-}

open import OrderedSet using (OrderedSet; orderedInfinity; [_]; _<∞_)
open import Data.Nat using (ℕ; suc)
open import Data.Bool.Base using (if_then_else_; false; true; Bool)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import 23Tree using (2-3Tree; 2Node; 3Node; Empty)
open import Search 

data InsertWitness {A : OrderedSet} {min max : (OrderedSet.S (orderedInfinity A))} : {h : ℕ} → (b : Bool) → 2-3Tree A h min max → Set where
  -- w-Empty : {b : Bool} {p : min <∞ max} → InsertWitness b (Empty min max p)
  w-2Node : {h : ℕ} {a : OrderedSet.S A} {l : 2-3Tree A h min [ a ]} {r : 2-3Tree A h [ a ] max} 
    {p : min <∞ [ a ]} {q : [ a ] <∞ max} {b : Bool}
    → InsertWitness b (2Node a p q l r)
  w-3Node : {h : ℕ} {a b : OrderedSet.S A} {l : 2-3Tree A h min [ a ]} {m : 2-3Tree A h [ a ] [ b ]} {r : 2-3Tree A h [ b ] max}
    {p : min <∞ [ a ]} {q : [ a ] <∞ [ b ]} {s : [ b ] <∞ max}
    → InsertWitness false (3Node a b p q s l m r)

-- Insert element into a tree
insert : {A : OrderedSet} {h : ℕ} {min max : (OrderedSet.S (orderedInfinity A))}
  → 2-3Tree A h min max → (a : OrderedSet.S A)
  → {p : (OrderedSet._<_ (orderedInfinity A)) min [ a ]} {q : (OrderedSet._<_ (orderedInfinity A)) [ a ] max}
  → ∃ λ z -- bit if height increased
  → Σ[ t ∈ (2-3Tree A (if z then (suc h) else h) min max) ] InsertWitness z t

-- Empty tree -> height increased
insert (Empty min max x) a {p} {q} = true ,
  (2Node a p q
    (Empty min [ a ] p)
    (Empty [ a ] max q) , w-2Node)

-- -- Insert into 2Node
insert {A} (2Node b p' q' l r) a {p} {q}
  with IsStrictTotalOrder.compare (OrderedSet.strictTotalOrder (orderedInfinity A)) [ a ] [ b ]
-- In node -> height unchanged
insert {A} (2Node b p' q' l r) a {p} {q} | tri≈ ¬x y ¬z = false , 2Node b p' q' l r , w-2Node
-- Insert in left tree
insert {A} {h} {min} (2Node {h'} b p' q' l r) a {p} {q} | tri< x ¬y ¬z with insert l a {p} {x}
... | false , (l' , w) =  false , 2Node b p' q' l' r , w-2Node 
-- Returned 2Node -> merge
... | true , (2Node c p'' q'' l' r' , w) = false , 3Node c b p'' q'' q' l' r' r , w-3Node
-- Returned 3Node -> agda should know that this is impossible
... | true , 3Node c d p'' q'' s'' l' m' r' , ()
insert {A} (2Node b p' q' l r) a {p} {q} | tri> ¬x ¬y z with insert r a {z} {q}
... | false , (r' , w) =  false , 2Node b p' q' l r' ,  w-2Node 
-- Returned 2Node -> merge
... | true , (2Node c p'' q'' l' r' , w) = false , 3Node b c p' p'' q'' l l' r' , w-3Node
-- Returned 3Node -> agda should know that this is impossible
... | true , 3Node c d p'' q'' s'' l' m' r' , ()

-- Insert into 3Node
insert {A} (3Node b c p' q' s' l m r) a {p} {q}
  with IsStrictTotalOrder.compare (OrderedSet.strictTotalOrder (orderedInfinity A)) [ a ] [ b ]
-- Node in tree (a ≡ b)
insert {A} (3Node b c p' q' s' l m r) a {p} {q} | tri≈ ¬x y ¬z = false , 3Node b c p' q' s' l m r , w-3Node
-- a < b -> insert in left tree
insert {A} (3Node b c p' q' s' l m r) a {p} {q} | tri< x ¬y ¬z with insert l a {p} {x}
... | false , (l' , w) = false , 3Node b c p' q' s' l' m r , w-3Node
-- Returned 2Node -> break 3Node
... | true , (2Node d p'' q'' l' r' , w) = true , 2Node b
  p'
  (IsStrictTotalOrder.trans (OrderedSet.strictTotalOrder (orderedInfinity A)) q' s')
  (2Node d p'' q'' l' r')
  (2Node c q' s' m r) , w-2Node 
... | true , 3Node a₁ b₁ x₁ x₂ x₃ t t₁ t₂ , ()
-- a > b -> check if a < c
insert {A} (3Node b c p' q' s' l m r) a {p} {q} | tri> ¬x ¬y z 
  with IsStrictTotalOrder.compare (OrderedSet.strictTotalOrder (orderedInfinity A)) [ a ] [ c ]
-- a ≡ c -> already inserted
insert {A} (3Node b c p' q' s' l m r) a {p} {q} | tri> ¬x ¬y z | tri≈ ¬x' y' ¬z' = false , 3Node b c p' q' s' l m r , w-3Node 
-- a < c -> insert in middle tree
insert {A} (3Node b c p' q' s' l m r) a {p} {q} | tri> ¬x ¬y z | tri< x' ¬y' ¬z' with insert m a {z} {x'}
... | false , (m' , w) = false , 3Node b c p' q' s' l m' r , w-3Node
... | true , (2Node d p'' q'' l' r' , w) = true , (2Node d
  (IsStrictTotalOrder.trans (OrderedSet.strictTotalOrder (orderedInfinity A)) p' p'')
  (IsStrictTotalOrder.trans (OrderedSet.strictTotalOrder (orderedInfinity A)) q'' s')
  (2Node b p' p'' l l')
  (2Node c q'' s' r' r)) , w-2Node 
... | true , 3Node d e p'' q'' s'' l' r' m' , ()
-- a > c -> insert in right tree
insert {A} (3Node b c p' q' s' l m r) a {p} {q} | tri> ¬x ¬y z | tri> ¬x' ¬y' z' with insert r a {z'} {q}
... | false , (r' , w) = false , 3Node b c p' q' s' l m r' , w-3Node 
... | true , (2Node d p'' q'' l' r' , w) = true , 2Node c
  (IsStrictTotalOrder.trans (OrderedSet.strictTotalOrder (orderedInfinity A)) p' q')
  s'
  (2Node b p' q' l m)
  (2Node d p'' q'' l' r'), w-2Node
... | true , 3Node d e p'' q'' s'' l' m' r' , ()

-- No element is an element of an empty tree.
a∉Empty : {A : OrderedSet}
  {min max : (OrderedSet.S (orderedInfinity A))} {p : OrderedSet._<_ (orderedInfinity A) min max}
  {a : OrderedSet.S A}
  → _∈_ {A = A} a (Empty min max p)  → ⊥

a∉Empty {a = a} ()

-- lemma after insertion of a a should be in tree.
after-insert-a∈t : {A : OrderedSet} {h : ℕ} {min max : (OrderedSet.S (orderedInfinity A))}
  → (t : 2-3Tree A h min max)
  → (a : OrderedSet.S A)
  → {p : (OrderedSet._<_ (orderedInfinity A)) min [ a ]} {q : (OrderedSet._<_ (orderedInfinity A)) [ a ] max}
  → a ∈ (proj₁ (proj₂ (insert t a {p} {q})))

after-insert-a∈t {A} t a {p} {q} with insert t a {p} {q}
after-insert-a∈t {A} t a {p} {q} | false , t' , w with search t' a
after-insert-a∈t {A} t a {p} {q} | false , 2Node b p' q' l r , w | yes u = u
after-insert-a∈t {A} t a {p} {q} | false , 2Node b p' q' l r , w | no u with search l a | search r a
... | yes u | _ = left₂ u
... | no u | yes u' = right₂ u'
... | no u | no u' with IsStrictTotalOrder.compare (OrderedSet.strictTotalOrder (orderedInfinity A)) [ a ] [ b ]
... | tri< x ¬y ¬z = ⊥-elim (u {! !})
... | tri≈ ¬x refl ¬z = here₂ {a = b} {l = l} {r = r} {p = p'} {q = q'}
... | tri> ¬x ¬y z = {!   !}
after-insert-a∈t {A} t a {p} {q} | false , 3Node b c p' q' s' l r m , w | yes u = u
after-insert-a∈t {A} t a {p} {q} | false , 3Node b c p' q' s' l r m , w | no u = {!   !}
after-insert-a∈t {A} t a {p} {q} | true , 2Node b p' q' l r , w with search (2Node b p' q' l r) a
after-insert-a∈t {A} t a {p} {q} | true , 2Node b p' q' l r , w | yes u = u
after-insert-a∈t {A} t a {p} {q} | true , 2Node b p' q' l r , w | no u = {!   !}
