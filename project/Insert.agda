open import OrderedSet using (OrderedSet)

module Insert (A : OrderedSet) where

open import OrderedSet using (orderedInfinity; [_])
open import Data.Nat using (ℕ; suc)
open import Data.Bool.Base using (if_then_else_; false; true; Bool)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import 23Tree A using (2-3Tree; 2Node; 3Node; Empty)
open import Search A using (_∈_; here₂; here₃-l; here₃-r; left₂; right₂; left₃; middle₃; right₃)

open OrderedSet.OrderedSet A using (S)

A∞ = orderedInfinity A

open OrderedSet.OrderedSet A∞ renaming (S to S∞; _<_ to _<∞_; strictTotalOrder to strictTotalOrder∞)
open IsStrictTotalOrder strictTotalOrder∞ renaming (trans to <∞-trans; compare to <∞-compare)

data InsertWitness {min max : S∞} : {h : ℕ} → (b : Bool) → 2-3Tree h min max → Set where
  w-Empty : {b : Bool} {p : min <∞ max}
    → InsertWitness b (Empty min max p)
  w-2Node : {h : ℕ} {a : S}
    {l : 2-3Tree h min [ a ]} {r : 2-3Tree h [ a ] max} 
    {p : min <∞ [ a ]} {q : [ a ] <∞ max} {b : Bool}
    → InsertWitness b (2Node a p q l r)
  w-3Node : {h : ℕ} {a b : S}
    {l : 2-3Tree h min [ a ]} {m : 2-3Tree h [ a ] [ b ]} {r : 2-3Tree h [ b ] max}
    {p : min <∞ [ a ]} {q : [ a ] <∞ [ b ]} {s : [ b ] <∞ max}
    → InsertWitness false (3Node a b p q s l m r)

-- Insert element into a tree
insert : {h : ℕ} {min max : S∞}
  → 2-3Tree h min max → (a : S)
  → {p : min <∞ [ a ]} {q : [ a ] <∞ max}
  → ∃ λ z -- bit if height increased
  → Σ[ t ∈ (2-3Tree (if z then (suc h) else h) min max) ] (InsertWitness z t × a ∈ t)

-- Empty tree -> height increased
insert (Empty min max x) a {p} {q} = true ,
  (2Node a p q
    (Empty min [ a ] p)
    (Empty [ a ] max q) , w-2Node , here₂)

-- Insert into 2Node
insert (2Node b p' q' l r) a {p} {q}
  with <∞-compare [ a ] [ b ]

-- In node -> height unchanged
insert (2Node b p' q' l r) .b {p} {q} | tri≈ ¬x refl ¬z = false , 2Node b p' q' l r , w-2Node , here₂

-- Insert in left tree
insert {h} {min} (2Node {h'} b p' q' l r) a {p} {q} | tri< x ¬y ¬z with insert l a {p} {x}
insert {h} {min} (2Node {h'} b p' q' l r) a {p} {q} | tri< x ¬y ¬z | false , (l' , w , a∈l) =  false , 2Node b p' q' l' r , w-2Node , left₂ a∈l
-- Returned 2Node -> merge
insert {h} {min} (2Node {h'} b p' q' l r) a {p} {q} | tri< x ¬y ¬z | true , (2Node c p'' q'' l' r' , w , a∈l) with a∈l
... | here₂ = false , (3Node c b p'' q'' q' l' r' r) , w-3Node , here₃-l
... | left₂ a∈l' = false , (3Node c b p'' q'' q' l' r' r) , w-3Node , left₃ a∈l'
... | right₂ a∈r' = false , (3Node c b p'' q'' q' l' r' r) , w-3Node , middle₃ a∈r'
-- Returned 3Node -> agda should know that this is impossible
insert {h} {min} (2Node {h'} b p' q' l r) a {p} {q} | tri< x ¬y ¬z | true , 3Node c d p'' q'' s'' l' m' r' , () , a∈t

-- Insert in right tree
insert (2Node b p' q' l r) a {p} {q} | tri> ¬x ¬y z with insert r a {z} {q}
insert (2Node b p' q' l r) a {p} {q} | tri> ¬x ¬y z | false , (r' , w , a∈r) =  false , 2Node b p' q' l r' , w-2Node , (right₂ a∈r)
-- Returned 2Node -> merge
insert (2Node b p' q' l r) a {p} {q} | tri> ¬x ¬y z | true , (2Node c p'' q'' l' r' , w , a∈r) with a∈r
... | here₂ = false , 3Node b c p' p'' q'' l l' r' , w-3Node , here₃-r
... | left₂ a∈l' = false , 3Node b c p' p'' q'' l l' r' , w-3Node , middle₃ a∈l' 
... | right₂ a∈r' = false , 3Node b c p' p'' q'' l l' r' , w-3Node , right₃ a∈r'
-- Returned 3Node -> agda should know that this is impossible
insert (2Node b p' q' l r) a {p} {q} | tri> ¬x ¬y z | true , 3Node c d p'' q'' s'' l' m' r' , () , a∈t

-- -- Insert into 3Node
insert {A} (3Node b c p' q' s' l m r) a {p} {q}
  with <∞-compare [ a ] [ b ]

-- Node in tree (a ≡ b)
insert (3Node b c p' q' s' l m r) .b {p} {q} | tri≈ ¬x refl ¬z = false , 3Node b c p' q' s' l m r , w-3Node , here₃-l

-- a < b -> insert in left tree
insert (3Node b c p' q' s' l m r) a {p} {q} | tri< x ¬y ¬z with insert l a {p} {x}
insert (3Node b c p' q' s' l m r) a {p} {q} | tri< x ¬y ¬z | false , (l' , w , a∈l) = false , 3Node b c p' q' s' l' m r , w-3Node , left₃ a∈l

-- Returned 2Node -> break 3Node
insert (3Node b c p' q' s' l m r) a {p} {q} | tri< x ¬y ¬z | true , (2Node d p'' q'' l' r' , w , a∈l) with a∈l
... | here₂ = true , 2Node b
  p'
  (<∞-trans q' s')
  (2Node d p'' q'' l' r')
  (2Node c q' s' m r) , w-2Node , left₂ here₂
... | left₂ a∈l' = true , 2Node b
  p'
  (<∞-trans q' s')
  (2Node d p'' q'' l' r')
  (2Node c q' s' m r) , w-2Node , left₂ (left₂ a∈l')
... | right₂ a∈r' = true , 2Node b
  p'
  (<∞-trans q' s')
  (2Node d p'' q'' l' r')
  (2Node c q' s' m r) , w-2Node , left₂ (right₂ a∈r')

insert (3Node b c p' q' s' l m r) a {p} {q} | tri< x ¬y ¬z | true , 3Node a₁ b₁ x₁ x₂ x₃ t t₁ t₂ , () , a∈t

-- a > b -> check if a < c
insert (3Node b c p' q' s' l m r) a {p} {q} | tri> ¬x ¬y z 
  with <∞-compare [ a ] [ c ]

-- a ≡ c -> already inserted
insert (3Node b .a p' q' s' l m r) a {p} {q} | tri> ¬x ¬y z | tri≈ ¬x' refl ¬z' = false , 3Node b a p' q' s' l m r , w-3Node , here₃-r 

-- a < c -> insert in middle tree
insert (3Node b c p' q' s' l m r) a {p} {q} | tri> ¬x ¬y z | tri< x' ¬y' ¬z' with insert m a {z} {x'}

insert (3Node b c p' q' s' l m r) a {p} {q} | tri> ¬x ¬y z | tri< x' ¬y' ¬z' | false , (m' , w , a∈m) = false , 3Node b c p' q' s' l m' r , w-3Node , middle₃ a∈m

insert (3Node b c p' q' s' l m r) a {p} {q} | tri> ¬x ¬y z | tri< x' ¬y' ¬z' | true , (2Node d p'' q'' l' r' , w , a∈m) with a∈m
... | here₂ = true , (2Node d
  (<∞-trans p' p'')
  (<∞-trans q'' s')
  (2Node b p' p'' l l')
  (2Node c q'' s' r' r)) , w-2Node , here₂
... | left₂ a∈l' = true , (2Node d
  (<∞-trans p' p'')
  (<∞-trans q'' s')
  (2Node b p' p'' l l')
  (2Node c q'' s' r' r)) , w-2Node , left₂ (right₂ a∈l')
... | right₂ a∈r' = true , (2Node d
  (<∞-trans p' p'')
  (<∞-trans q'' s')
  (2Node b p' p'' l l')
  (2Node c q'' s' r' r)) , w-2Node , right₂ (left₂ a∈r')

insert (3Node b c p' q' s' l m r) a {p} {q} | tri> ¬x ¬y z | tri< x' ¬y' ¬z' | true , 3Node d e p'' q'' s'' l' r' m' , () , a∈t

-- a > c -> insert in right tree
insert (3Node b c p' q' s' l m r) a {p} {q} | tri> ¬x ¬y z | tri> ¬x' ¬y' z' with insert r a {z'} {q}

insert (3Node b c p' q' s' l m r) a {p} {q} | tri> ¬x ¬y z | tri> ¬x' ¬y' z' | false , (r' , w , a∈r) = false , 3Node b c p' q' s' l m r' , w-3Node , right₃ a∈r

insert (3Node b c p' q' s' l m r) a {p} {q} | tri> ¬x ¬y z | tri> ¬x' ¬y' z' | true , (2Node d p'' q'' l' r' , w , a∈r) with a∈r
... | here₂ = true , 2Node c
  (<∞-trans p' q')
  s'
  (2Node b p' q' l m)
  (2Node d p'' q'' l' r'), w-2Node , right₂ here₂
... | left₂ a∈l' = true , 2Node c
  (<∞-trans p' q')
  s'
  (2Node b p' q' l m)
  (2Node d p'' q'' l' r'), w-2Node , right₂ (left₂ a∈l')
... | right₂ a∈r' = true , 2Node c
  (<∞-trans p' q')
  s'
  (2Node b p' q' l m)
  (2Node d p'' q'' l' r'), w-2Node , right₂ (right₂ a∈r')

insert (3Node b c p' q' s' l m r) a {p} {q} | tri> ¬x ¬y z | tri> ¬x' ¬y' z' | true , 3Node d e p'' q'' s'' l' m' r' , () , a∈t


-- No element is an element of an empty tree.
a∉Empty : {min max : S∞} {p : min <∞ max} {a : S}
  → _∈_  a (Empty min max p)  → ⊥

a∉Empty {a = a} ()

-- lemma after insertion of a a should be in tree.
after-insert-a∈t : {h : ℕ} {min max : S∞}
  → (t : 2-3Tree h min max)
  → (a : S)
  → {p : min <∞ [ a ]} {q : [ a ] <∞ max}
  → a ∈ (proj₁ (proj₂ (insert t a {p} {q})))

after-insert-a∈t t a {p} {q} with insert t a {p} {q}
... | _ , _ , _ , a∈t = a∈t
