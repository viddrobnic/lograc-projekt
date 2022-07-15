module Examples where

open import Data.Nat using (ℕ; zero; suc; _⊔_; s≤s; z≤n) renaming (_<_ to _<ℕ_)
open import Data.Nat.Properties using () renaming (<-isStrictTotalOrder to <ℕ-isStrictTotalOrder)
open import OrderedSet
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; resp)

-- Natural numbers as ordered set
orderedℕ : OrderedSet
orderedℕ = record { 
  S = ℕ ; 
  _<_ = _<ℕ_ ; 
  strictTotalOrder = <ℕ-isStrictTotalOrder 
  }

open import Search orderedℕ using (_∈_; Dec)
open _∈_
open import Tree orderedℕ

-- Empty tree
emptyTree = empty

-- Singleton tree with 5
singletonTree = singleton 5

-- Insert 5 into empty tree
insert-5 : insert emptyTree 5 ≡ singletonTree
insert-5 = refl 

-- Tree with 4 elements.
tree : Tree
tree = insert (insert (insert (insert empty 42) 69) 3) 1

-- Check that 1 is in tree
1-in-tree : search tree 1 ≡ Dec.yes (left₂ here₃-l)
1-in-tree = refl

-- Check that 42 is in tree
42-in-tree : search tree 42 ≡ Dec.yes here₂
42-in-tree = refl

-- Check that 2 is not in tree
2-not-in-tree : search tree 2 ≡ (Dec.no λ { (left₂ (left₃ ()))
                                          ; (left₂ (middle₃ ()))
                                          ; (left₂ (right₃ ())) 
                                          ; (right₂ (left₂ ()))                        
                                          ; (right₂ (right₂ ())) })
2-not-in-tree = refl
