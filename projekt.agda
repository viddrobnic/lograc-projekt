open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Level using (0ℓ)
-- open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s; _<_)


data Set∞ (A : Set) : Set where
  -∞  :            Set∞ A
  [_] :  (a : A) → Set∞ A
  +∞  :            Set∞ A


record OrderedSet : Set₁ where
  field
    S : Set₀
    _<_ : Rel S 0ℓ
    strictTotalOrder : IsStrictTotalOrder _≡_ _<_

orderedInfinity : OrderedSet → OrderedSet
orderedInfinity record { S = S₀ ; _<_ = _<₀_ ; strictTotalOrder = strictTotalOrder₀ } = record { 
  S = Set∞ S₀ ; 
  _<_ = _<aux_ ; 
  strictTotalOrder = record { isEquivalence = isEquivalenceAux ; trans = transAux ; compare = compareAux } }
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
    ... | tri< a ¬b ¬c = tri< (m<n a) (λ x → ¬b {!   !}) {!   !} -- TODO: Rabimo dokaz za injektivnost [ _ ]
    ... | tri≈ ¬a b ¬c = {!   !}
    ... | tri> ¬a ¬b c = {!   !}
  
-- data _≤_ : Rel ℕ 0ℓ where
--   z≤n : ∀ {n}                 → zero  ≤ n
--   s≤s : ∀ {m n} (m≤n : m ≤ n) → suc m ≤ suc n


-- data _<∞_ : {A : Set} → Set∞ A → Set∞ A → Set₂ where
--   -∞<n : {A : Set} {n : Set∞ A} → -∞ <∞ n  
--   -- []<[] :  {A : Set} {n m : A} → n < m → [ n ] <∞ [ m ]
--   n<+∞ : {A : Set} {n : Set∞ A} → n <∞ +∞