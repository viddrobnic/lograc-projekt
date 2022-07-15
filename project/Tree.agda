open import OrderedSet using (OrderedSet)

module Tree (A : OrderedSet) where

open import Data.Nat using (ℕ; suc)
open import OrderedSet using (OrderedSet; Set∞; orderedInfinity; _<∞_; [_])
open _<∞_
open Set∞ using (+∞; -∞)
open import 23Tree A
open OrderedSet.OrderedSet A using (S)
open import Insert A renaming (insert to insert-aux)
open import Search A using (_∈_; Dec) renaming (search to search-aux)

open import Data.Product
open import Data.Bool.Base using (if_then_else_; false; true; Bool)

record Tree : Set where
    field
        h : ℕ
        tree : 2-3Tree h -∞ +∞

empty : Tree
empty = record { h = 0 ; tree = Empty -∞ +∞ -∞<+∞ }

singleton : S → Tree
singleton a = record { h = 1 ; tree = 2Node a -∞<n n<+∞ (Empty -∞ [ a ] -∞<n) (Empty [ a ] +∞ n<+∞) }

insert : Tree → S → Tree
insert record { h = h ; tree = t } a with insert-aux t a {p = -∞<n} {q = n<+∞}
... | false , t' , _ = record { h = h ; tree = t' }
... | true , t' , _ = record { h = suc h ; tree = t' }

search : (t : Tree) → (a : S) → Dec (a ∈ (Tree.tree t))
search record { h = h ; tree = t } a = search-aux t a 
