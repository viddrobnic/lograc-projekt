module OrderedSet where

open import Relation.Binary
open import Level using (0ℓ; Level)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)

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

-- Simple lemma
-- if [ a ] < [ b ], then [ a ] !≡ [ b ]
<∞-not-equal : {A : OrderedSet} {[a] [b] : (OrderedSet.S (orderedInfinity A))} → (OrderedSet._<_ (orderedInfinity A)) [a] [b] → ¬ ([a] ≡ [b])
<∞-not-equal {A} {[a]} {[b]} [a]<[b] with IsStrictTotalOrder.compare (OrderedSet.strictTotalOrder (orderedInfinity A)) [a] [b]
... | tri< a ¬b ¬c = λ x → ¬b x
... | tri≈ ¬a b ¬c = λ x → ¬a [a]<[b]
... | tri> ¬a ¬b c = λ x → ¬b x
