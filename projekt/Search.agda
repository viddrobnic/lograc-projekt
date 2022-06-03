open import OrderedSet using (OrderedSet; orderedInfinity; [_]; _<∞_)
open import Data.Nat using (ℕ)
open import Relation.Binary
open import 23Tree using (2-3Tree; 2Node; 3Node; Empty)
open import Level using (Level)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality
open import OrderedSet using (<∞-not-equal)

-- Is element in tree?
data _∈_ {A : OrderedSet} {min max : (OrderedSet.S (orderedInfinity A))} : {h : ℕ} → OrderedSet.S A → 2-3Tree A h min max → Set where
  -- Element is in this node
  here₂ : {h : ℕ} {a : OrderedSet.S A} {l : 2-3Tree A h min [ a ]} {r : 2-3Tree A h [ a ] max} 
    {p : min <∞ [ a ]} {q : [ a ] <∞ max} 
    → a ∈ 2Node a p q l r
  here₃-l : {h : ℕ} {a b : OrderedSet.S A} {l : 2-3Tree A h min [ a ]} {m : 2-3Tree A h [ a ] [ b ]} {r : 2-3Tree A h [ b ] max}
    {p : min <∞ [ a ]} {q : [ a ] <∞ [ b ]} {s : [ b ] <∞ max}
    → a ∈ 3Node a b p q s l m r
  here₃-r : {h : ℕ} {a b : OrderedSet.S A} {l : 2-3Tree A h min [ a ]} {m : 2-3Tree A h [ a ] [ b ]} {r : 2-3Tree A h [ b ] max}
    {p : min <∞ [ a ]} {q : [ a ] <∞ [ b ]} {s : [ b ] <∞ max}
    → b ∈ 3Node a b p q s l m r
  
  -- Element is in left/right subtree
  left₂ : {h : ℕ} {a b : OrderedSet.S A} {l : 2-3Tree A h min [ b ]} {r : 2-3Tree A h [ b ] max} 
    {p : min <∞ [ b ]} {q : [ b ] <∞ max}
    → a ∈ l
    → a ∈ 2Node b p q l r
  right₂ : {h : ℕ} {a b : OrderedSet.S A} {l : 2-3Tree A h min [ b ]} {r : 2-3Tree A h [ b ] max} 
    {p : min <∞ [ b ]} {q : [ b ] <∞ max} 
    → a ∈ r
    → a ∈ 2Node b p q l r

  -- Element is in left/middle/right subtree
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

-- Lemmas about _∈_
if-in-less-than-max : {A : OrderedSet} {min max : (OrderedSet.S (orderedInfinity A))} {h : ℕ} {a : OrderedSet.S A} {t : 2-3Tree A h min max}
  → a ∈ t → OrderedSet._<_ (orderedInfinity A) [ a ] max
if-in-less-than-max (here₂ {q = q}) = q
if-in-less-than-max {A} (here₃-l {q = q} {s = s}) = IsStrictTotalOrder.trans (OrderedSet.strictTotalOrder (orderedInfinity A)) q s
if-in-less-than-max {A} (here₃-r {s = s}) = s
if-in-less-than-max {A} (left₂ {q = q} a∈t) = IsStrictTotalOrder.trans (OrderedSet.strictTotalOrder (orderedInfinity A)) (if-in-less-than-max a∈t) q 
if-in-less-than-max {A} (right₂ a∈t) = if-in-less-than-max a∈t
if-in-less-than-max {A} (left₃ {q = q} {s = s} a∈t) = IsStrictTotalOrder.trans (OrderedSet.strictTotalOrder (orderedInfinity A)) (if-in-less-than-max a∈t) (IsStrictTotalOrder.trans (OrderedSet.strictTotalOrder (orderedInfinity A)) q s)
if-in-less-than-max {A} (middle₃ {s = s} a∈t) = IsStrictTotalOrder.trans (OrderedSet.strictTotalOrder (orderedInfinity A)) (if-in-less-than-max a∈t) s
if-in-less-than-max {A} (right₃ a∈t) = if-in-less-than-max a∈t

if-in-more-than-min : {A : OrderedSet} {min max : (OrderedSet.S (orderedInfinity A))} {h : ℕ} {a : OrderedSet.S A} {t : 2-3Tree A h min max}
  → a ∈ t → OrderedSet._<_ (orderedInfinity A) min [ a ]
if-in-more-than-min (here₂ {p = p}) = p
if-in-more-than-min {A} (here₃-l {p = p}) = p
if-in-more-than-min {A} (here₃-r {p = p} {q = q}) = IsStrictTotalOrder.trans (OrderedSet.strictTotalOrder (orderedInfinity A)) p q
if-in-more-than-min {A} (left₂ a∈t) = if-in-more-than-min a∈t
if-in-more-than-min {A} (right₂ {p = p} a∈t) = IsStrictTotalOrder.trans (OrderedSet.strictTotalOrder (orderedInfinity A)) p (if-in-more-than-min a∈t)
if-in-more-than-min {A} (left₃ a∈t) = if-in-more-than-min a∈t
if-in-more-than-min {A} (middle₃ {p = p} a∈t) = IsStrictTotalOrder.trans (OrderedSet.strictTotalOrder (orderedInfinity A)) p (if-in-more-than-min a∈t)
if-in-more-than-min {A} (right₃ {p = p} {q = q} a∈t) = IsStrictTotalOrder.trans (OrderedSet.strictTotalOrder (orderedInfinity A)) ((IsStrictTotalOrder.trans (OrderedSet.strictTotalOrder (orderedInfinity A)) p q)) (if-in-more-than-min a∈t)

-- Search result - is element in a set or not
data Dec {l : Level} (A : Set l) : Set l where
  yes : A → Dec A
  no  : (A → ⊥) → Dec A


-- Lemmas for search
not-in-if-not-in-left₂ : {A : OrderedSet} {min max : (OrderedSet.S (orderedInfinity A))} {h : ℕ} {a b : OrderedSet.S A} {l : 2-3Tree A h min [ b ]} {r : 2-3Tree A h [ b ] max} {p : min <∞ [ b ]} {q : [ b ] <∞ max}
  → (OrderedSet._<_ (orderedInfinity A)) [ a ] [ b ]
  → (a ∈ l → ⊥)
  → (a ∈ 2Node b p q l r → ⊥)
not-in-if-not-in-left₂ {A} [a]<[b] a∉l here₂ = <∞-not-equal {A = A} [a]<[b] refl
not-in-if-not-in-left₂ {A} [a]<[b] a∉l (left₂ a∈l) = a∉l a∈l
not-in-if-not-in-left₂ {A} {a = a} {b = b} [a]<[b] a∉l (right₂ a∈r) with IsStrictTotalOrder.compare (OrderedSet.strictTotalOrder (orderedInfinity A)) [ a ] [ b ]
... | tri< x ¬y ¬z = ¬z (if-in-more-than-min a∈r)
... | tri≈ ¬x y ¬z = ¬z (if-in-more-than-min a∈r)
... | tri> ¬x ¬y z = ¬x [a]<[b]

not-in-if-not-in-right₂ : {A : OrderedSet} {min max : (OrderedSet.S (orderedInfinity A))} {h : ℕ} {a b : OrderedSet.S A} {l : 2-3Tree A h min [ b ]} {r : 2-3Tree A h [ b ] max} {p : min <∞ [ b ]} {q : [ b ] <∞ max}
  → (OrderedSet._<_ (orderedInfinity A)) [ b ] [ a ]
  → (a ∈ r → ⊥)
  → (a ∈ 2Node b p q l r → ⊥)
not-in-if-not-in-right₂ {A} [b]<[a] a∉r here₂ = <∞-not-equal {A = A} [b]<[a] refl
not-in-if-not-in-right₂ {A} {a = a} {b = b} [b]<[a] a∉r (left₂ a∈l) with IsStrictTotalOrder.compare (OrderedSet.strictTotalOrder (orderedInfinity A)) [ a ] [ b ]
... | tri< x ¬y ¬z = ¬z [b]<[a]
... | tri≈ ¬x y ¬z = ¬x (if-in-less-than-max a∈l)
... | tri> ¬x ¬y z = ¬x (if-in-less-than-max a∈l)
not-in-if-not-in-right₂ {A} [b]<[a] a∉r (right₂ a∈r) = a∉r a∈r

not-in-if-not-in-left₃ : {A : OrderedSet} {min max : (OrderedSet.S (orderedInfinity A))} {h : ℕ} {a b c : OrderedSet.S A} {l : 2-3Tree A h min [ b ]} {m : 2-3Tree A h [ b ] [ c ]} {r : 2-3Tree A h [ c ] max}
    {p : min <∞ [ b ]} {q : [ b ] <∞ [ c ]} {s : [ c ] <∞ max}
  → (OrderedSet._<_ (orderedInfinity A)) [ a ] [ b ]
  → (a ∈ l → ⊥)
  → (a ∈ 3Node b c p q s l m r → ⊥)
not-in-if-not-in-left₃ {A} [a]<[b] a∉l here₃-l = <∞-not-equal {A = A} [a]<[b] refl
not-in-if-not-in-left₃ {A} {a = a} {b = b} [a]<[b] a∉l (here₃-r {q = q}) with IsStrictTotalOrder.compare (OrderedSet.strictTotalOrder (orderedInfinity A)) [ a ] [ b ]
... | tri< x ¬y ¬z = ¬z q
... | tri≈ ¬x y ¬z = ¬z q
... | tri> ¬x ¬y z = ¬x [a]<[b]
not-in-if-not-in-left₃ {A} [a]<[b] a∉l (left₃ a∈l) = a∉l a∈l
not-in-if-not-in-left₃ {A} {a = a} {b = b} [a]<[b] a∉l (middle₃ a∈m) with IsStrictTotalOrder.compare (OrderedSet.strictTotalOrder (orderedInfinity A)) [ a ] [ b ]
... | tri< x ¬y ¬z = ¬z (if-in-more-than-min a∈m)
... | tri≈ ¬x y ¬z = ¬x [a]<[b]
... | tri> ¬x ¬y z = ¬x [a]<[b]
not-in-if-not-in-left₃ {A} {a = a} {b = b} [a]<[b] a∉l (right₃ {r = r} {q = q} a∈r) with IsStrictTotalOrder.compare (OrderedSet.strictTotalOrder (orderedInfinity A)) [ a ] [ b ] 
... | tri< x ¬y ¬z = ¬z (IsStrictTotalOrder.trans (OrderedSet.strictTotalOrder (orderedInfinity A)) q (if-in-more-than-min a∈r))
... | tri≈ ¬x y ¬z = ¬x [a]<[b]
... | tri> ¬x ¬y z = ¬x [a]<[b]

not-in-if-not-in-right₃ : {A : OrderedSet} {min max : (OrderedSet.S (orderedInfinity A))} {h : ℕ} {a b c : OrderedSet.S A} {l : 2-3Tree A h min [ b ]} {m : 2-3Tree A h [ b ] [ c ]} {r : 2-3Tree A h [ c ] max}
    {p : min <∞ [ b ]} {q : [ b ] <∞ [ c ]} {s : [ c ] <∞ max}
  → (OrderedSet._<_ (orderedInfinity A)) [ c ] [ a ]
  → (a ∈ r → ⊥)
  → (a ∈ 3Node b c p q s l m r → ⊥)
not-in-if-not-in-right₃ {A} {a = a} {c = c} [c]<[a] a∉r (here₃-l {q = q}) with IsStrictTotalOrder.compare (OrderedSet.strictTotalOrder (orderedInfinity A)) [ a ] [ c ]
... | tri< x ¬y ¬z = ¬z [c]<[a]
... | tri≈ ¬x y ¬z = ¬z [c]<[a]
... | tri> ¬x ¬y z = ¬x q
not-in-if-not-in-right₃ {A} [c]<[a] a∉r here₃-r = <∞-not-equal {A = A} [c]<[a] refl
not-in-if-not-in-right₃ {A} {a = a} {c = c} [c]<[a] a∉r (left₃ {q = q} a∈l) with IsStrictTotalOrder.compare (OrderedSet.strictTotalOrder (orderedInfinity A)) [ a ] [ c ] 
... | tri< x ¬y ¬z = ¬z [c]<[a]
... | tri≈ ¬x y ¬z = ¬z [c]<[a]
... | tri> ¬x ¬y z = ¬x ((IsStrictTotalOrder.trans (OrderedSet.strictTotalOrder (orderedInfinity A)) (if-in-less-than-max a∈l) q))
not-in-if-not-in-right₃ {A} {a = a} {c = c} [c]<[a] a∉r (middle₃ a∈m) with IsStrictTotalOrder.compare (OrderedSet.strictTotalOrder (orderedInfinity A)) [ a ] [ c ]
... | tri< x ¬y ¬z = ¬z [c]<[a]
... | tri≈ ¬x y ¬z = ¬z [c]<[a]
... | tri> ¬x ¬y z = ¬x (if-in-less-than-max a∈m)
not-in-if-not-in-right₃ {A} [c]<[a] a∉r (right₃ a∈r) = a∉r a∈r

not-in-if-not-in-middle₃ : {A : OrderedSet} {min max : (OrderedSet.S (orderedInfinity A))} {h : ℕ} {a b c : OrderedSet.S A} {l : 2-3Tree A h min [ b ]} {m : 2-3Tree A h [ b ] [ c ]} {r : 2-3Tree A h [ c ] max}
    {p : min <∞ [ b ]} {q : [ b ] <∞ [ c ]} {s : [ c ] <∞ max}
  → (OrderedSet._<_ (orderedInfinity A)) [ b ] [ a ]
  → (OrderedSet._<_ (orderedInfinity A)) [ a ] [ c ]
  → (a ∈ m → ⊥)
  → (a ∈ 3Node b c p q s l m r → ⊥)
not-in-if-not-in-middle₃ {A} [b]<[a] [a]<[c] a∉m here₃-l = <∞-not-equal {A = A} [b]<[a] refl
not-in-if-not-in-middle₃ {A} {a = a} {c = c} [b]<[a] [a]<[c] a∉r (here₃-r {q = q}) = <∞-not-equal {A = A} [a]<[c] refl
not-in-if-not-in-middle₃ {A} {a = a} {b = b} {c = c} [b]<[a] [a]<[c] a∉m (left₃ a∈l) with IsStrictTotalOrder.compare (OrderedSet.strictTotalOrder (orderedInfinity A)) [ a ] [ b ]
... | tri< x ¬y ¬z = ¬z [b]<[a]
... | tri≈ ¬x y ¬z = ¬z [b]<[a]
... | tri> ¬x ¬y z = ¬x (if-in-less-than-max a∈l)
not-in-if-not-in-middle₃ {A} {a = a} {b = b} {c = c} [b]<[a] [a]<[c] a∉m (middle₃ a∈m) = a∉m a∈m
not-in-if-not-in-middle₃ {A} {a = a} {b = b} {c = c} [b]<[a] [a]<[c] a∉m (right₃ a∈r) with IsStrictTotalOrder.compare (OrderedSet.strictTotalOrder (orderedInfinity A)) [ a ] [ c ]
... | tri< x ¬y ¬z = ¬z (if-in-more-than-min a∈r)
... | tri≈ ¬x y ¬z = ¬x [a]<[c]
... | tri> ¬x ¬y z = ¬x [a]<[c]

-- Search for element
-- Returns yes if element is in tree, no otherwise.
search : {A : OrderedSet} {min max : (OrderedSet.S (orderedInfinity A))} {h : ℕ} → (t : 2-3Tree A h min max) → (a : OrderedSet.S A) → Dec (a ∈ t)

-- Search in empty tree
search (Empty _ _ x) a = no (λ ())

-- Search in 2Node
search {A} (2Node b p q l r) a with IsStrictTotalOrder.compare (OrderedSet.strictTotalOrder (orderedInfinity A)) [ a ] [ b ]
search {A} (2Node b p q l r) .b | tri≈ ¬x refl ¬z = yes here₂
search {A} (2Node b p q l r) a | tri< x ¬y ¬z with search l a
... | yes u = yes (left₂ u)
... | no u = no (not-in-if-not-in-left₂ x u)
search {A} (2Node b p q l r) a | tri> ¬x ¬y z with search r a
... | yes u = yes (right₂ u)
... | no u = no (not-in-if-not-in-right₂ z u)

-- Search in 3Node
search {A} (3Node b c p q s l m r) a with IsStrictTotalOrder.compare (OrderedSet.strictTotalOrder (orderedInfinity A)) [ a ] [ b ]
search {A} (3Node b c p q s l m r) .b | tri≈ ¬x refl ¬z = yes here₃-l
search {A} (3Node b c p q s l m r) a | tri< x ¬y ¬z with search l a 
... | yes u = yes (left₃ u)
... | no u = no (not-in-if-not-in-left₃ x u)
search {A} (3Node b c p q s l m r) a | tri> ¬x ¬y z with IsStrictTotalOrder.compare (OrderedSet.strictTotalOrder (orderedInfinity A)) [ a ] [ c ]
search {A} (3Node b .a p q s l m r) a | tri> ¬x ¬y z | tri≈ ¬x' refl ¬z' = yes here₃-r
search {A} (3Node b c p q s l m r) a | tri> ¬x ¬y z | tri< x' ¬y' ¬z' with search m a
... | yes u = yes (middle₃ u)
... | no u = no (not-in-if-not-in-middle₃ z x' u)
search {A} (3Node b c p q s l m r) a | tri> ¬x ¬y z | tri> ¬x' ¬y' z' with search r a
... | yes u = yes (right₃ u)
... | no u = no (not-in-if-not-in-right₃ z' u)