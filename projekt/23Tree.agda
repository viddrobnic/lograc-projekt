open import OrderedSet using (OrderedSet; orderedInfinity; [_]; _<∞_)
open import Data.Nat using (ℕ; suc)

-- Define type for 2-3 trees.
data 2-3Tree (A : OrderedSet) : ℕ → (OrderedSet.S (orderedInfinity A)) → (OrderedSet.S (orderedInfinity A)) → Set where
  -- Empty node
  Empty : (min max : (OrderedSet.S (orderedInfinity A)))
        → (OrderedSet._<_ (orderedInfinity A)) min max
        → 2-3Tree A 0 min max
  -- 2Node: Node with a single value and two children.
  2Node : {h : ℕ} {min max : (OrderedSet.S (orderedInfinity A))}
        → (a : OrderedSet.S A)
        → (OrderedSet._<_ (orderedInfinity A)) min [ a ]
        → (OrderedSet._<_ (orderedInfinity A)) [ a ] max
        → 2-3Tree A h min [ a ] → 2-3Tree A h [ a ] max
        → 2-3Tree A (suc h) min max
  -- 3Node: Node with two values and three children.
  3Node : {h : ℕ} {min max : (OrderedSet.S (orderedInfinity A))} 
        → (a b : OrderedSet.S A)
        → (OrderedSet._<_ (orderedInfinity A)) min [ a ]
        → (OrderedSet._<_ (orderedInfinity A)) [ a ] [ b ]
        → (OrderedSet._<_ (orderedInfinity A)) [ b ] max
        → 2-3Tree A h min [ a ] → 2-3Tree A h [ a ] [ b ] → 2-3Tree A h [ b ] max
        → 2-3Tree A (suc h) min max
