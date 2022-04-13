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
  -- Empty tree has two constructors:
  -- - Empty tree with different left and right values.
  -- - Empty tree with same value for left and right boundary.
  Empty≡ : (min max : (OrderedSet.S (orderedInfinity A)))
        → min ≡ max
        → 2-3Tree A 0 min max
  Empty< : (min max : (OrderedSet.S (orderedInfinity A)))
        → (OrderedSet._<_ (orderedInfinity A)) min max
        → 2-3Tree A 0 min max
  -- 2Node: Node with a single value and two children.
  2Node : {h : ℕ} {minₗ maxₗ minᵣ maxᵣ : (OrderedSet.S (orderedInfinity A))} 
        → (a : OrderedSet.S A)
        → 2-3Tree A h minₗ maxₗ → 2-3Tree A h minᵣ maxᵣ
        → (OrderedSet._<_ (orderedInfinity A)) maxₗ [ a ]
        → (OrderedSet._<_ (orderedInfinity A)) [ a ] minᵣ
        → 2-3Tree A (suc h) minₗ maxᵣ
  -- 3Node: Node with two values and three children.
  3Node : {h : ℕ} {minₗ maxₗ minₘ maxₘ minᵣ maxᵣ : (OrderedSet.S (orderedInfinity A))} 
        → (a b : OrderedSet.S A)
        → 2-3Tree A h minₗ maxₗ → 2-3Tree A h minₘ maxₘ → 2-3Tree A h minᵣ maxᵣ
        → (OrderedSet._<_ (orderedInfinity A)) maxₗ [ a ]
        → (OrderedSet._<_ (orderedInfinity A)) [ a ] minₘ
        → (OrderedSet._<_ (orderedInfinity A)) maxₘ [ b ]
        → (OrderedSet._<_ (orderedInfinity A)) [ b ] minᵣ
        → 2-3Tree A (suc h) minₗ maxᵣ

data _∈_ {A : OrderedSet} {h : ℕ} {min max : (OrderedSet.S (orderedInfinity A))} : 2-3Tree A h min max → Set where
  -- here₂ : {l r : 2-3Tree A h} → a ∈ (?) 
  here₃-l : {!  {a b : A} → a ∈  !}
  here₃-r : {!  {a b : A} → b ∈  !}
  left₂ : {!   !}
  right₂ : {!   !}
  left₃ : {!   !}
  middle₃ : {!   !}
  right₃ : {!   !}


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
emptyTree1 = Empty< -∞ +∞ -∞<+∞

emptyTree2 : 2-3Tree orderedℕ 0 [ 5 ] [ 5 ]
emptyTree2 = Empty≡ [ 5 ] [ 5 ] refl 

-- Example 2-3 tree.
sampleTree : 2-3Tree orderedℕ 1  -∞ +∞
sampleTree = 2Node 3
              (Empty< -∞ [ 2 ] -∞<n )
              ((Empty< [ 4 ] +∞ n<+∞ ))
              (m<n (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s Data.Nat.z≤n))))
              (m<n (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s Data.Nat.z≤n)))))

-- TODO:
-- - not all trees can be defined because of strict inequality
-- - are there better lemmas for proving 10 < 23 ?