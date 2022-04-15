open import Relation.Binary
open import Data.Nat using (ℕ; zero; suc) renaming (_≤_ to _≤ℕ_)
open import Data.Sum
open import Data.Nat.Properties using () renaming (≤-isTotalOrder to ≤ℕ-isTotalOrder)
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
    _≤_ : Rel S 0ℓ
    totalOrder : IsTotalOrder _≡_ _≤_

-- New operator ≤ on Set∞
data _≤∞_ {S₀ : Set} {_≤₀_ : Rel S₀ 0ℓ} : Rel (Set∞ S₀) 0ℓ where
    -∞≤n : {n : Set∞ S₀} → -∞ ≤∞ n
    n≤+∞ : {n : Set∞ S₀} → n ≤∞ +∞
    m≤n  : {m n : S₀} → m ≤₀ n → [ m ] ≤∞ [ n ]

-- Convert ordered set to ordered set with added -∞ and ∞.
-- This function defines how ≤ works on Set∞ A.
orderedInfinity : OrderedSet → OrderedSet
orderedInfinity record { S = S₀ ; _≤_ = _≤₀_ ; totalOrder = totalOrder₀ } = record { 
  S = Set∞ S₀ ; 
  _≤_ = _≤∞_ ; 
  totalOrder = record { 
    isPartialOrder = isPartialOrderAux ;
    total = totalAux }  }
  where
    isPartialOrder₀ : IsPartialOrder _≡_ _≤₀_
    isPartialOrder₀ = IsTotalOrder.isPartialOrder totalOrder₀

    isPreorder₀ : IsPreorder _≡_ _≤₀_
    isPreorder₀ = IsPartialOrder.isPreorder isPartialOrder₀

    reflexive₀ :  _≡_ ⇒ _≤₀_
    reflexive₀ = IsPreorder.reflexive isPreorder₀

    totalAux : Total _≤∞_
    totalAux -∞ -∞ = inj₁ -∞≤n
    totalAux -∞ [ a ] = inj₁ -∞≤n
    totalAux -∞ +∞ = inj₁ -∞≤n
    totalAux [ a ] -∞ = inj₂ -∞≤n
    totalAux [ a ] [ b ] with (IsTotalOrder.total totalOrder₀) a b
    ... | inj₁ x = inj₁ (m≤n x)
    ... | inj₂ y = inj₂ (m≤n y)
    totalAux [ a ] +∞ = inj₁ n≤+∞
    totalAux +∞ y = inj₂ n≤+∞

    reflAux : _≡_ ⇒ _≤∞_
    reflAux { -∞} refl = -∞≤n
    reflAux {[ a ]} refl = m≤n (reflexive₀ refl)
    reflAux {+∞} refl = n≤+∞
    
    transAux : Transitive _≤∞_
    transAux -∞≤n q = -∞≤n
    transAux n≤+∞ n≤+∞ = n≤+∞
    transAux (m≤n x) n≤+∞ = n≤+∞
    transAux (m≤n x) (m≤n y) = m≤n (IsPreorder.trans
      (IsPartialOrder.isPreorder
        (IsTotalOrder.isPartialOrder totalOrder₀)) x y)

    antisymAux : Antisymmetric _≡_ (λ z z₁ → z ≤∞ z₁)
    antisymAux -∞≤n -∞≤n = refl
    antisymAux n≤+∞ n≤+∞ = refl
    antisymAux (m≤n x) (m≤n y) = cong
      (λ u → [ u ])
      (IsPartialOrder.antisym (IsTotalOrder.isPartialOrder totalOrder₀) x y)

    isPartialOrderAux = record {
      isPreorder = record {
        isEquivalence = isEquivalence ;
        reflexive = reflAux ;
        trans = transAux } ;
      antisym = antisymAux }
    
    -- -- helper lemma: inserting in Set∞ preserves <
    -- set∞-< : {n m : S₀} → [ n ] ≤∞ [ m ] → n ≤₀ m
    -- set∞-< (m≤n x) = x

    -- -- helper lemma: inserting in Set∞ preserves equality
    -- set∞-≡ : {n m : S₀} → [ n ] ≡ [ m ] → n ≡ m
    -- set∞-≡ refl = refl

    -- compareAux : Trichotomous _≡_ _≤∞_
    -- compareAux -∞ -∞ = tri≈ (λ {()}) refl λ {()}
    -- compareAux -∞ [ a ] = tri< -∞≤n (λ {()}) λ {()}
    -- compareAux -∞ +∞ = tri< -∞≤+∞ (λ {()}) λ {()}
    -- compareAux [ a ] -∞ = tri> (λ {()}) ((λ {()})) -∞≤n
    -- compareAux [ a ] +∞ = tri< n≤+∞ ((λ {()})) (λ {()})
    -- compareAux +∞ -∞ = tri> (λ {()}) ((λ {()})) -∞≤+∞
    -- compareAux +∞ [ a ] = tri> (λ {()}) ((λ {()})) n≤+∞
    -- compareAux +∞ +∞ = tri≈ (λ {()}) refl λ {()}
    -- compareAux [ m ] [ n ] with IsStrictTotalOrder.compare strictTotalOrder₀ m n
    -- ... | tri< a ¬b ¬c = tri< (m≤n a) (λ x → ¬b (set∞-≡ x)) λ {x → ¬c (set∞-< x)}
    -- ... | tri≈ ¬a b ¬c = tri≈ (λ x → ¬a (set∞-< x)) (cong (λ x → [ x ]) b) λ x → ¬c (set∞-< x)
    -- ... | tri> ¬a ¬b c = tri> (λ x → ¬a (set∞-< x)) (λ x → ¬b (set∞-≡ x)) (m≤n c)
  
-- Define type for 2-3 trees.
data 2-3Tree (A : OrderedSet) : ℕ → (OrderedSet.S (orderedInfinity A)) → (OrderedSet.S (orderedInfinity A)) → Set where
  Empty : (min max : (OrderedSet.S (orderedInfinity A)))
        → (OrderedSet._≤_ (orderedInfinity A)) min max
        → 2-3Tree A 0 min max
  -- 2Node: Node with a single value and two children.
  2Node : {h : ℕ} {minₗ maxₗ minᵣ maxᵣ : (OrderedSet.S (orderedInfinity A))} 
        → (a : OrderedSet.S A)
        → 2-3Tree A h minₗ maxₗ → 2-3Tree A h minᵣ maxᵣ
        → (OrderedSet._≤_ (orderedInfinity A)) maxₗ [ a ]
        → (OrderedSet._≤_ (orderedInfinity A)) [ a ] minᵣ
        → 2-3Tree A (suc h) minₗ maxᵣ
  -- 3Node: Node with two values and three children.
  3Node : {h : ℕ} {minₗ maxₗ minₘ maxₘ minᵣ maxᵣ : (OrderedSet.S (orderedInfinity A))} 
        → (a b : OrderedSet.S A)
        → 2-3Tree A h minₗ maxₗ → 2-3Tree A h minₘ maxₘ → 2-3Tree A h minᵣ maxᵣ
        → (OrderedSet._≤_ (orderedInfinity A)) maxₗ [ a ]
        → (OrderedSet._≤_ (orderedInfinity A)) [ a ] minₘ
        → (OrderedSet._≤_ (orderedInfinity A)) maxₘ [ b ]
        → (OrderedSet._≤_ (orderedInfinity A)) [ b ] minᵣ
        → 2-3Tree A (suc h) minₗ maxᵣ

-- data _∈_ {A : OrderedSet} {h : ℕ} {min max : (OrderedSet.S (orderedInfinity A))} : 2-3Tree A h min max → Set where
--   -- here₂ : {l r : 2-3Tree A h} → a ∈ (?) 
--   here₃-l : {!  {a b : A} → a ∈  !}
--   here₃-r : {!  {a b : A} → b ∈  !}
--   left₂ : {!   !}
--   right₂ : {!   !}
--   left₃ : {!   !}
--   middle₃ : {!   !}
--   right₃ : {!   !}


-- EXAMPLE:
-- Natural number are ordered set
orderedℕ : OrderedSet
orderedℕ = record { 
  S = ℕ ; 
  _≤_ = _≤ℕ_ ; 
  totalOrder = ≤ℕ-isTotalOrder }

orderedℕ∞ = OrderedSet.S (orderedInfinity orderedℕ)

-- Empty
emptyTree : 2-3Tree orderedℕ 0 -∞ +∞
emptyTree = Empty -∞ +∞ -∞≤n

-- Example 2-3 tree.
sampleTree : 2-3Tree orderedℕ 1  -∞ +∞
sampleTree = 2Node
  3
  (Empty -∞ [ 3 ] -∞≤n)
  (Empty [ 3 ] +∞ n≤+∞)
  (m≤n (_≤ℕ_.s≤s (_≤ℕ_.s≤s (_≤ℕ_.s≤s _≤ℕ_.z≤n))))
  (m≤n (_≤ℕ_.s≤s (_≤ℕ_.s≤s (_≤ℕ_.s≤s _≤ℕ_.z≤n))))

-- -- TODO:
-- -- - not all trees can be defined because of strict inequality
-- -- - are there better lemmas for proving 10 < 23 ?  