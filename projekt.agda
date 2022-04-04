data Set∞ (A : Set) : Set where
  -∞  :           Set∞ A
  [_] : (a : A) → Set∞ A
  +∞  :           Set∞ A

data _<∞_ : {A : Set} → Set∞ A → Set∞ A → Set where
  -∞<n : {A : Set} {n : Set∞ A} → -∞ <∞ n  
----   []<[] : {n m : ℕ} → n < m → [ n ] <∞ [ m ]
  n<+∞ : {A : Set} {n : Set∞ A} → n <∞ +∞