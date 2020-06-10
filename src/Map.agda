{-# OPTIONS --cubical --safe #-}

open import Cubical.Data.Bool

module Map {K : Set} (_==_ : K → K → Bool) where
  open import List
  open import Cubical.Data.Maybe
  open import Cubical.Data.Prod

  Map : ∀ {ℓ} → Set ℓ → Set ℓ
  Map A = List (K × A)

  module _ {ℓ} {A : Set ℓ} where

    empty : Map A
    empty = []

    lookup : K → Map A → Maybe A
    lookup k [] = nothing
    lookup k ((i , x) ∷ m) with i == k
    lookup k ((i , x) ∷ m) | false = lookup k m
    lookup k ((i , x) ∷ m) | true = just x

    findWithDefault : A → K → Map A → A
    findWithDefault a k m with lookup k m
    findWithDefault a k m | nothing = a
    findWithDefault a k m | just x = x

    delete : K → Map A → Map A
    delete k [] = []
    delete k ((i , n) ∷ m) with i == k
    delete k (x ∷ m) | false = x ∷ delete k m
    delete k (x ∷ m) | true = m

    insert : K → A → Map A → Map A
    insert k a m = (k , a) ∷ delete k m

    insertWith : ((new : A) → (old : A) → A) → K → A → Map A → Map A
    insertWith f k a m with lookup k m
    insertWith f k a m | nothing = insert k a m
    insertWith f k a m | just x = insert k (f a x) m

    adjust : (A → A) → K → Map A → Map A
    adjust f k m with lookup k m
    adjust f k m | nothing = m
    adjust f k m | just x = insert k (f x) m

    union : Map A → Map A → Map A
    union [] n = n
    union ((k , a) ∷ m) n = insert k a (union m n)

    mapElems : ∀ {ℓ'} {B : Set ℓ'} → (A → B) → Map A → Map B
    mapElems f [] = []
    mapElems f ((k , x) ∷ m) = (k , f x) ∷ mapElems f m

    toList : Map A → List (K × A)
    toList x = x

    elems : Map A → List A
    elems m = mapList proj₂ m
