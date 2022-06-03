open import Data.Nat using (ℕ; zero; suc; _⊔_) renaming (_<_ to _<ℕ_)
open import Data.Nat.Properties using () renaming (<-isStrictTotalOrder to <ℕ-isStrictTotalOrder)
open import Data.Product
open import OrderedSet
open import 23Tree
open import Search
open import Insert

-- EXAMPLE:
-- Natural number are ordered set
orderedℕ : OrderedSet
orderedℕ = record { 
  S = ℕ ; 
  _<_ = _<ℕ_ ; 
  strictTotalOrder = <ℕ-isStrictTotalOrder 
  }

orderedℕ∞ = OrderedSet.S (orderedInfinity orderedℕ)

-- Empty
emptyTree1 : 2-3Tree orderedℕ 0 -∞ +∞
emptyTree1 = Empty -∞ +∞ -∞<+∞

-- Example 2-3 tree.
sampleTree : 2-3Tree orderedℕ 1 -∞ +∞
sampleTree = 2Node 1 -∞<n n<+∞ (Empty -∞ [ 1 ] -∞<n) (Empty [ 1 ] +∞ n<+∞)

sampleTree2 : 2-3Tree orderedℕ 1 -∞ +∞
sampleTree2 = 3Node 1 2 -∞<n (m<n (Data.Nat.s≤s (Data.Nat.s≤s Data.Nat.z≤n))) n<+∞ (Empty -∞ [ 1 ] -∞<n) (Empty [ 1 ] [ 2 ] (m<n (Data.Nat.s≤s (Data.Nat.s≤s Data.Nat.z≤n)))) (Empty [ 2 ] +∞ n<+∞)

sampleTree3 : 2-3Tree orderedℕ 2 -∞ +∞
sampleTree3 = 2Node 3 -∞<n n<+∞ 
  (3Node 1 2 -∞<n 
    (m<n (Data.Nat.s≤s (Data.Nat.s≤s Data.Nat.z≤n))) 
    (m<n (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s Data.Nat.z≤n)))) 
    (Empty -∞ [ 1 ] -∞<n) 
    (Empty [ 1 ] [ 2 ] (m<n (Data.Nat.s≤s (Data.Nat.s≤s Data.Nat.z≤n)))) 
    (Empty [ 2 ] [ 3 ] (m<n (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s Data.Nat.z≤n)))))) 
  (2Node 4 
    (m<n (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s Data.Nat.z≤n))))) 
    n<+∞ 
    (Empty [ 3 ] [ 4 ] (m<n (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s Data.Nat.z≤n)))))) 
    (Empty [ 4 ] +∞ n<+∞))

sampleTree4 : 2-3Tree orderedℕ 2 -∞ +∞
sampleTree4 = 3Node 2 4 -∞<n 
  (m<n (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s Data.Nat.z≤n)))) 
  n<+∞ 
  (2Node 1 -∞<n 
    (m<n (Data.Nat.s≤s (Data.Nat.s≤s Data.Nat.z≤n))) 
    (Empty -∞ [ 1 ] -∞<n) 
    (Empty [ 1 ] [ 2 ] (m<n (Data.Nat.s≤s (Data.Nat.s≤s Data.Nat.z≤n))))) 
  (2Node 3 
    (m<n (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s Data.Nat.z≤n)))) 
    (m<n (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s Data.Nat.z≤n))))) 
    (Empty [ 2 ] [ 3 ] (m<n (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s Data.Nat.z≤n))))) 
    (Empty [ 3 ] [ 4 ] (m<n (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s Data.Nat.z≤n))))))) 
  (2Node 5 
    (m<n (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s Data.Nat.z≤n)))))) 
    n<+∞ 
    (Empty [ 4 ] [ 5 ] (m<n (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s Data.Nat.z≤n))))))) 
    (Empty [ 5 ] +∞ n<+∞))

1-in-sampleTree : 1 ∈ sampleTree
1-in-sampleTree = here₂

1-in-sampleTree2 : 1 ∈ sampleTree2
1-in-sampleTree2 = here₃-l

2-in-sampleTree2 : 2 ∈ sampleTree2
2-in-sampleTree2 = here₃-r

1-in-sampleTree3 : 1 ∈ sampleTree3
1-in-sampleTree3 = left₂ here₃-l

4-in-sampleTree3 : 4 ∈ sampleTree3
4-in-sampleTree3 = right₂ here₂

1-in-sampleTree4 : 1 ∈ sampleTree4
1-in-sampleTree4 = left₃ here₂

3-in-sampleTree4 : 3 ∈ sampleTree4
3-in-sampleTree4 = middle₃ here₂

5-in-sampleTree4 : 5 ∈ sampleTree4
5-in-sampleTree4 = right₃ here₂

-- Insertion example
tree0 : 2-3Tree orderedℕ 0 -∞ +∞
tree0 = Empty -∞ +∞ -∞<+∞

tree1 = proj₁ (proj₂ (insert tree0 5 {p = -∞<n} {q = n<+∞}))
tree2 = proj₁ (proj₂ (insert tree1 10 {p = -∞<n} {q = n<+∞}))
tree3 = proj₁ (proj₂ (insert tree2 5 {p = -∞<n} {q = n<+∞}))
tree4 = proj₁ (proj₂ (insert tree3 1 {p = -∞<n} {q = n<+∞}))
tree5 = proj₁ (proj₂ (insert tree4 2 {p = -∞<n} {q = n<+∞}))
tree6 = proj₁ (proj₂ (insert tree5 3 {p = -∞<n} {q = n<+∞}))
        