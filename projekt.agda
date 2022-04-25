open import Relation.Binary
open import Data.Nat using (ℕ; zero; suc) renaming (_<_ to _<ℕ_)
open import Data.Nat.Properties using () renaming (<-isStrictTotalOrder to <ℕ-isStrictTotalOrder)
open import Relation.Binary.PropositionalEquality
open import Level using (0ℓ)

-- Add -∞ and ∞ to the set.
-- Example: add -∞ and ∞ to ℕ.
data Set∞ (A : Set) : Set where
  -∞  :            Set∞ A
  [_] :  (a : A) → Set∞ A
  +∞  :            Set∞ A

-- Set with linear order.
record OrderedSet : Set₁ where
  field
    S : Set₀
    _<_ : Rel S 0ℓ
    strictTotalOrder : IsStrictTotalOrder _≡_ _<_

-- New operator < on Set∞
data _<∞_ {S₀ : Set} {_<₀_ : Rel S₀ 0ℓ} : Rel (Set∞ S₀) 0ℓ where
    -∞<n : {n : S₀} → -∞ <∞ [ n ]
    n<+∞ : {n : S₀} → [ n ] <∞ +∞
    -∞<+∞ : -∞ <∞ +∞
    m<n  : {m n : S₀} → m <₀ n → [ m ] <∞ [ n ]

-- Convert ordered set to ordered set with added -∞ and ∞.
-- This function defines how < works on Set∞ A.
orderedInfinity : OrderedSet → OrderedSet
orderedInfinity record { S = S₀ ; _<_ = _<₀_ ; strictTotalOrder = strictTotalOrder₀ } = record { 
  S = Set∞ S₀ ; 
  _<_ = _<∞_ ; 
  strictTotalOrder = record { 
    isEquivalence = isEquivalenceAux ;
    trans = transAux ;
    compare = compareAux } }
  where
    isEquivalenceAux = record { 
      refl = refl ;
      sym = λ x → sym x ; 
      trans = λ x y → trans x y }
    
    transAux : Transitive _<∞_
    transAux -∞<n n<+∞ = -∞<+∞
    transAux -∞<n (m<n x) = -∞<n
    transAux (m<n x) n<+∞ = n<+∞
    transAux (m<n x) (m<n y) = m<n (IsStrictTotalOrder.trans strictTotalOrder₀ x y)

    -- helper lemma: inserting in Set∞ preserves <
    set∞-< : {n m : S₀} → [ n ] <∞ [ m ] → n <₀ m
    set∞-< (m<n x) = x

    -- helper lemma: inserting in Set∞ preserves equality
    set∞-≡ : {n m : S₀} → [ n ] ≡ [ m ] → n ≡ m
    set∞-≡ refl = refl

    compareAux : Trichotomous _≡_ _<∞_
    compareAux -∞ -∞ = tri≈ (λ {()}) refl λ {()}
    compareAux -∞ [ a ] = tri< -∞<n (λ {()}) λ {()}
    compareAux -∞ +∞ = tri< -∞<+∞ (λ {()}) λ {()}
    compareAux [ a ] -∞ = tri> (λ {()}) ((λ {()})) -∞<n
    compareAux [ a ] +∞ = tri< n<+∞ ((λ {()})) (λ {()})
    compareAux +∞ -∞ = tri> (λ {()}) ((λ {()})) -∞<+∞
    compareAux +∞ [ a ] = tri> (λ {()}) ((λ {()})) n<+∞
    compareAux +∞ +∞ = tri≈ (λ {()}) refl λ {()}
    compareAux [ m ] [ n ] with IsStrictTotalOrder.compare strictTotalOrder₀ m n
    ... | tri< a ¬b ¬c = tri< (m<n a) (λ x → ¬b (set∞-≡ x)) λ {x → ¬c (set∞-< x)}
    ... | tri≈ ¬a b ¬c = tri≈ (λ x → ¬a (set∞-< x)) (cong (λ x → [ x ]) b) λ x → ¬c (set∞-< x)
    ... | tri> ¬a ¬b c = tri> (λ x → ¬a (set∞-< x)) (λ x → ¬b (set∞-≡ x)) (m<n c)
  
-- Define type for 2-3 trees.
data 2-3Tree (A : OrderedSet) : ℕ → (OrderedSet.S (orderedInfinity A)) → (OrderedSet.S (orderedInfinity A)) → Set where
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

data _∈_ {A : OrderedSet} {min max : (OrderedSet.S (orderedInfinity A))} : {h : ℕ} → OrderedSet.S A → 2-3Tree A h min max → Set where
  here₂ : {h : ℕ} {a : OrderedSet.S A} {l : 2-3Tree A h min [ a ]} {r : 2-3Tree A h [ a ] max} 
    {p : min <∞ [ a ]} {q : [ a ] <∞ max} 
    → a ∈ 2Node a p q l r
  here₃-l : {h : ℕ} {a b : OrderedSet.S A} {l : 2-3Tree A h min [ a ]} {m : 2-3Tree A h [ a ] [ b ]} {r : 2-3Tree A h [ b ] max}
    {p : min <∞ [ a ]} {q : [ a ] <∞ [ b ]} {s : [ b ] <∞ max}
    → a ∈ 3Node a b p q s l m r
  here₃-r : {h : ℕ} {a b : OrderedSet.S A} {l : 2-3Tree A h min [ a ]} {m : 2-3Tree A h [ a ] [ b ]} {r : 2-3Tree A h [ b ] max}
    {p : min <∞ [ a ]} {q : [ a ] <∞ [ b ]} {s : [ b ] <∞ max}
    → b ∈ 3Node a b p q s l m r
  
  left₂ : {h : ℕ} {a b : OrderedSet.S A} {l : 2-3Tree A h min [ b ]} {r : 2-3Tree A h [ b ] max} 
    {p : min <∞ [ b ]} {q : [ b ] <∞ max} 
    → a ∈ l
    → a ∈ 2Node b p q l r
  right₂ : {h : ℕ} {a b : OrderedSet.S A} {l : 2-3Tree A h min [ b ]} {r : 2-3Tree A h [ b ] max} 
    {p : min <∞ [ b ]} {q : [ b ] <∞ max} 
    → a ∈ r
    → a ∈ 2Node b p q l r

  left₃ : {h : ℕ} {a b c : OrderedSet.S A} {l : 2-3Tree A h min [ b ]} {m : 2-3Tree A h [ b ] [ c ]} {r : 2-3Tree A h [ c ] max}
    {p : min <∞ [ b ]} {q : [ b ] <∞ [ c ]} {s : [ c ] <∞ max}
    → a ∈ l
    → a ∈ 3Node b c p q s l m r
  middle₃ : {h : ℕ} {a b c : OrderedSet.S A} {l : 2-3Tree A h min [ b ]} {m : 2-3Tree A h [ b ] [ c ]} {r : 2-3Tree A h [ c ] max}
    {p : min <∞ [ b ]} {q : [ b ] <∞ [ c ]} {s : [ c ] <∞ max}
    → a ∈ m
    → a ∈ 3Node b c p q s l m r
  right₃ : {h : ℕ} {a b c : OrderedSet.S A} {l : 2-3Tree A h min [ b ]} {m : 2-3Tree A h [ b ] [ c ]} {r : 2-3Tree A h [ c ] max}
    {p : min <∞ [ b ]} {q : [ b ] <∞ [ c ]} {s : [ c ] <∞ max}
    → a ∈ r
    → a ∈ 3Node b c p q s l m r

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
