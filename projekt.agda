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

-- Convert ordered set to ordered set with added -∞ and ∞.
-- This function defines how < works on Set∞ A.
orderedInfinity : OrderedSet → OrderedSet
orderedInfinity record { S = S₀ ; _<_ = _<₀_ ; strictTotalOrder = strictTotalOrder₀ } = record { 
  S = Set∞ S₀ ; 
  _<_ = _<aux_ ; 
  strictTotalOrder = record { 
    isEquivalence = isEquivalenceAux ;
    trans = transAux ;
    compare = compareAux } }
  where
    data _<aux_ : Rel (Set∞ S₀) 0ℓ where
      -∞<n : {n : S₀} → -∞ <aux [ n ]
      n<+∞ : {n : S₀} → [ n ] <aux +∞
      -∞<+∞ : -∞ <aux +∞
      m<n  : {m n : S₀} → m <₀ n → [ m ] <aux [ n ]
    
    isEquivalenceAux = record { 
      refl = refl ;
      sym = λ x → sym x ; 
      trans = λ x y → trans x y }
    
    transAux : Transitive _<aux_
    transAux -∞<n n<+∞ = -∞<+∞
    transAux -∞<n (m<n x) = -∞<n
    transAux (m<n x) n<+∞ = n<+∞
    transAux (m<n x) (m<n y) = m<n (IsStrictTotalOrder.trans strictTotalOrder₀ x y)

    -- helper lemma: inserting in Set∞ preserves <
    set∞-< : {n m : S₀} → [ n ] <aux [ m ] → n <₀ m
    set∞-< (m<n x) = x

    -- helper lemma: inserting in Set∞ preserves equality
    set∞-≡ : {n m : S₀} → [ n ] ≡ [ m ] → n ≡ m
    set∞-≡ refl = refl

    compareAux : Trichotomous _≡_ _<aux_
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
  Empty : (min max : (OrderedSet.S (orderedInfinity A))) → 2-3Tree A 0 min max
  -- TODO we need proof that maxl < a and a < minr
  2Node : {h : ℕ} {minₗ maxₗ minᵣ maxᵣ : (OrderedSet.S (orderedInfinity A))} 
        → (a : OrderedSet.S A)
        → 2-3Tree A h minₗ maxₗ → 2-3Tree A h minᵣ maxᵣ → 2-3Tree A (suc h) minₗ maxᵣ
  -- TODO proofs maxl < a < min
  3Node : {h : ℕ} {minₗ maxₗ minₘ maxₘ minᵣ maxᵣ : (OrderedSet.S (orderedInfinity A))} 
        → (a b : OrderedSet.S A)
        → 2-3Tree A h minₗ maxₗ → 2-3Tree A h minₘ maxₘ → 2-3Tree A h minᵣ maxᵣ → 2-3Tree A (suc h) minₗ maxᵣ

-- EXAMPLE:
-- Natural number are ordered set
orderedℕ : OrderedSet
orderedℕ = record { 
  S = ℕ ; 
  _<_ = _<ℕ_ ; 
  strictTotalOrder = <ℕ-isStrictTotalOrder 
  }

orderedℕ∞ = OrderedSet.S (orderedInfinity orderedℕ)

-- Example 2-3 tree.
sampleTree : 2-3Tree orderedℕ 2  -∞ +∞
sampleTree = 2Node 5 
                (2Node 3
                  (Empty -∞ [ 3 ])
                  (Empty [ 3 ] [ 5 ]))
                (3Node 7 10
                  (Empty [ 5 ] [ 7 ])
                  (Empty [ 7 ] [ 10 ])
                  (Empty [ 10 ] +∞))