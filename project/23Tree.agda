open import OrderedSet using (OrderedSet)

module 23Tree (A : OrderedSet) where

open import OrderedSet using (OrderedSet; orderedInfinity; [_])
open import Data.Nat using (ℕ; suc)

open OrderedSet.OrderedSet A using (S)
open OrderedSet.OrderedSet (orderedInfinity A) renaming (S to S∞; _<_ to _<∞_)

-- Define type for 2-3 trees.
data 2-3Tree : ℕ → S∞ → S∞ → Set where
  -- Empty node
  Empty : (min max : S∞)
        → min <∞ max
        → 2-3Tree 0 min max
  -- 2Node: Node with a single value and two children.
  2Node : {h : ℕ} {min max : S∞}
        → (a : S)
        → min <∞ [ a ]
        → [ a ] <∞ max
        → 2-3Tree h min [ a ] → 2-3Tree h [ a ] max
        → 2-3Tree (suc h) min max
  -- 3Node: Node with two values and three children.
  3Node : {h : ℕ} {min max : S∞} 
        → (a b : S)
        → min <∞ [ a ]
        → [ a ] <∞ [ b ]
        → [ b ] <∞ max
        → 2-3Tree h min [ a ] → 2-3Tree h [ a ] [ b ] → 2-3Tree h [ b ] max
        → 2-3Tree (suc h) min max
 